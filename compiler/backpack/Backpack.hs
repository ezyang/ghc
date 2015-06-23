{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE CPP #-}
module Backpack (doBackpack) where

#include "HsVersions.h"

import GHC hiding (Failed, Succeeded)

import GhcMonad

import BackpackSyn
import ShUnify

import Packages

import Parser
import Lexer
import Shaping

import TcIface
import DynFlags
import OccName
import Avail
import NameEnv
import TcRnDriver
import TcRnMonad
import Module
import LoadIface
import HscTypes
import StringBuffer
import FastString
import ErrUtils
import SrcLoc
import HscMain
import DriverPipeline hiding (unP)
import Finder
import Util
import UniqFM
import Outputable
import Maybes
import Panic
import HeaderInfo
import Bag

import IfaceSyn

import Data.Either
import GHC.Fingerprint
import Data.IORef
import Control.Monad
import qualified Data.Map as Map
import System.FilePath
import qualified Data.Traversable as T
import Control.Exception

-- ----------------------------------------------------------------------------
-- Run --backpack mode

-- | Summary of a bkp file, analogous to 'ModSummary'.
data BkpSummary
    = BkpSummary {
        bs_pkg_name :: PackageName,
          -- ^ Identity of a package
        bs_internal_shape :: Shape,
        bs_path :: FilePath,
          -- ^ Location of the Backpack file
        bs_decls :: Int
          -- ^ Cache of the number of declarations in the package.
        }

-- | Apply a function on 'DynFlags' on an 'HscEnv'
overHscDynFlags :: (DynFlags -> DynFlags) -> HscEnv -> HscEnv
overHscDynFlags f hsc_env = hsc_env { hsc_dflags = f (hsc_dflags hsc_env) }

-- | Entry point to compile a Backpack file.
-- NB: inside of this is in the Ghc monad because we want to update
-- HscEnv as we go, and this is the common state that can be threaded
-- through the typechecker.
doBackpack :: FilePath -> Ghc ()
doBackpack src_filename = do
    -- flag gyrations
    dflags0 <- getDynFlags
    src_opts <- liftIO $ getOptionsFromFile dflags0 src_filename
    (dflags, unhandled_flags, warns) <- liftIO $ parseDynamicFilePragma dflags0 src_opts
    -- setDynFlags dflags
    modifySession (\hsc_env -> hsc_env {hsc_dflags = dflags})
    liftIO $ checkProcessArgsResult dflags unhandled_flags
    liftIO $ handleFlagWarnings dflags warns
    -- TODO: something mumble preprocessing.  Maybe just right
    -- to move this into the DriverPipeline chain

    hsc_env <- getSession
    buf <- liftIO $ hGetStringBuffer src_filename
    let loc = mkRealSrcLoc (mkFastString src_filename) 1 1
    case unP parseBackpack (mkPState dflags buf loc) of
        PFailed span err -> do
            liftIO $ throwOneError (mkPlainErrMsg dflags span err)
        POk _ bkp -> do
            forM_ bkp $ \pkg -> do
                let pkg_name = let PackageName fs_pn = unLoc (hspkgName (unLoc pkg))
                               in unpackFS fs_pn
                liftIO . compilationProgressMsg dflags
                       $ "==== Package " ++ pkg_name ++ " ===="
                -- Shape the package
                -- TODO: when export specification is implemented for
                -- packages, need to return both the unfiltered and
                -- the filtered provisions.
                (pk, sh) <- liftIO
                          . runHsc hsc_env
                          . ioMsgMaybe
                          . initShM hsc_env (realSrcLocSpan loc)
                          $ shPackage pkg
                -- Record the shape in the EPS
                sh_subst <- liftIO $ computeShapeSubst hsc_env sh
                updateEpsGhc_ (\eps -> eps { eps_shape = sh_subst } )
                eps <- getEpsGhc
                -- Figure out if we should generate code or not.
                -- If there are holes, we can't generate code.
                let (target, set_write_interface)
                           | hscTarget dflags == HscNothing = (HscNothing, False)
                           -- NB: if we set the target to HscNothing because
                           -- we can't compile indefinite packages, we should
                           -- still write the interface files
                           | not (Map.null (sh_requires sh)) = (HscNothing, True)
                           | otherwise = (hscTarget dflags, False)
                -- Figure out where to put the build products.  This is a
                -- little subtle, since there are two choices for where
                -- to put things:
                --
                --      1. Inline with the hs files / organized by package
                --         name;
                --      2. In a separate directory per package key.
                --
                -- (1) is acceptable when we are typechecking an indefinite
                -- package, or compiling a definite package with no holes.
                -- However, when compiling a definite package with holes,
                -- we might instantiate it multiple times, so we must do (2)
                -- to disambiguate between the cases.
                --
                -- To keep things predictable, if we're compiling we always
                -- organize by pk.
                let pkg_key = unpackFS (packageKeyFS pk)
                    name_outdir p | Just f <- p dflags = Just (f </> pkg_name)
                                  | otherwise = Nothing -- inline ok!
                    key_outdir p | Just f <- p dflags = Just (f </> pkg_key)
                                 | otherwise = Just ("out" </> pkg_key)
                    outdir | target == HscNothing = name_outdir
                           | otherwise = key_outdir
                -- Setup the dflags for the package, and type-check/compile it!
                withTempSession (overHscDynFlags (\dflags ->
                  (if set_write_interface
                    then flip gopt_set Opt_WriteInterface
                    else id) $
                  dflags {
                    hscTarget   = target,
                    thisPackage = pk,
                    objectDir   = outdir objectDir,
                    hiDir       = outdir hiDir,
                    stubDir     = outdir stubDir
                  } )) $ do
                    let bs = BkpSummary {
                            bs_pkg_name = unLoc (hspkgName (unLoc pkg)),
                            bs_internal_shape = sh, -- TODO watch out with exportspcs!
                            bs_decls = length (hspkgBody (unLoc pkg)),
                            bs_path = src_filename
                        }
                    compilePackage bs pkg
                -- Clear the EPS, because everything was loaded modulo a shape
                -- and it might be out-of-date the next time we shape.
                -- TODO: only eliminate things which depend on holes.
                updateEpsGhc_ (\eps -> initExternalPackageState {
                        eps_IIT = eps_IIT eps,
                        eps_EST = eps_EST eps
                    } )

-- | Compiles a Backpack package.
compilePackage :: BkpSummary -> LHsPackage -> Ghc ()
compilePackage bs (L _loc HsPackage { hspkgBody = decls })
    = mapM_ (compilePkgDecl bs) (zip [1..] decls)

-- | Compiles a (located) Backpack package declaration
compilePkgDecl :: BkpSummary -> (Int, LHsPkgDecl) -> Ghc ()
compilePkgDecl bs (i, (L (RealSrcSpan loc) decl)) = compilePkgDecl' bs i loc decl

-- TODO: move this to PackageName
packageNameFS :: PackageName -> FastString
packageNameFS (PackageName fs) = fs

-- | Up until now, GHC has assumed a single compilation target per source file.
-- Backpack files with inline modules break this model, since a single file
-- may generate multiple output files.  How do we decide to name these files?
-- Should there only be one output file? This function our current heuristic,
-- which is we make a "fake" module and use that.
hsModuleToModSummary :: DynFlags
                     -> HscSource
                     -> BkpSummary
                     -> Located (HsModule RdrName)
                     -> IO ModSummary
hsModuleToModSummary dflags hsc_src bs
                     hsmod@(L _ HsModule { hsmodName = Just (L _ modname) }) = do
    -- Sort of the same deal as in DriverPipeline's getLocation
    location <- mkHomeModLocation2 dflags modname
                             (unpackFS (packageNameFS (bs_pkg_name bs)) </>
                              moduleNameSlashes modname)
                             (case hsc_src of
                                  HsSrcFile -> "hs"
                                  HsBootFile -> "hs-boot"
                                  HsigFile -> "hsig")
    -- This duplicates a pile of logic in GhcMake
    time <- getModificationUTCTime (bs_path bs) -- TODO cache me
    let this_package | HsigFile <- hsc_src = holePackageKey
                     | otherwise = thisPackage dflags
        this_mod = mkModule this_package modname
    hi_timestamp <- modificationTimeIfExists (ml_hi_file location)
    return ModSummary {
            ms_mod = this_mod,
            ms_hsc_src = hsc_src,
            ms_location = location,
            ms_hspp_file = "(inline file)",
            -- VERY IMPORTANT, because tc will ignore ModSummary this_mod
            ms_hspp_opts = dflags { thisPackage = this_package },
            ms_hspp_buf = Nothing,
            -- TODO: These have to be filled in to do recompilation checking
            ms_srcimps = error "hsModuleToModSummary: no ms_srcimps",
            ms_textual_imps = error "hsModuleToModSummary: no ms_textual_imps",
            -- This is our hack to get the parse tree to the right spot
            ms_parsed_mod = Just (HsParsedModule {
                    hpm_module = hsmod,
                    hpm_src_files = [], -- TODO if we preprocessed it
                    hpm_annotations = error "hsModuleToModsummary: no apiAnns (FIXME)" -- BOGUS
                }),
            ms_hs_date = time,
            ms_obj_date = Nothing, -- TODO do this
            ms_iface_date = hi_timestamp
        }
hsModuleToModSummary _ _ _ _ = panic "hsModuleToModSummary: no module name"

-- | Update the EPS from the Ghc monad. TODO move to appropriate library spot.
updateEpsGhc_ :: GhcMonad m => (ExternalPackageState -> ExternalPackageState) -> m ()
updateEpsGhc_ f = do
    hsc_env <- getSession
    liftIO $ atomicModifyIORef' (hsc_EPS hsc_env) (\x -> (f x, ()))

updateEpsGhc :: GhcMonad m => (ExternalPackageState -> (ExternalPackageState, a)) -> m a
updateEpsGhc f = do
    hsc_env <- getSession
    liftIO $ atomicModifyIORef' (hsc_EPS hsc_env) f

getEpsGhc :: GhcMonad m => m ExternalPackageState
getEpsGhc = do
    hsc_env <- getSession
    liftIO $ readIORef (hsc_EPS hsc_env)

-- | Compile a (non-located) package declaration.  Updates the session.
compilePkgDecl' :: BkpSummary -> Int -> RealSrcSpan -> HsPkgDecl -> Ghc ()
compilePkgDecl' bs i _ (ModuleD hsmod@(L _ HsModule { hsmodName = Just (L _ modname) })) = do
    hsc_env <- getSession
    dflags <- getDynFlags
    -- This is an inline module, fake up a ModSummary
    mod_summary <- liftIO $ hsModuleToModSummary dflags HsSrcFile bs hsmod
    let this_mod = ms_mod mod_summary
    -- XXX recompilation checking doesn't work
    let modified = SourceModified
    -- Do the compilation!
    hmi <- liftIO $ compileOne hsc_env mod_summary i (bs_decls bs) Nothing Nothing modified
    -- Add the module to the HPT and put it into scope
    let hpt1 = addToUFM (hsc_HPT hsc_env) modname hmi
        ifaces1 = addToUFM_C mergeModIfaceForImport (hsc_ifaces hsc_env) modname (hm_iface hmi)
        hsc_env1 = hsc_env { hsc_HPT = hpt1
                           , hsc_ifaces = ifaces1 }
    setSession hsc_env1
    -- Cache the interface if we were JUST typechecking (which means
    -- that this must be the most generalized version of the module)
    -- TODO: A bad user of the GHC API could trample this invariant.
    -- We must be sure NOT to redundantly type check an hsmod with a
    -- bad shape.
    when (hscTarget dflags == HscNothing) $
        updateEpsGhc_ (\eps -> eps {
            eps_IIT = extendModuleEnv (eps_IIT eps) this_mod (hm_iface hmi)
            })

compilePkgDecl' bs i loc (SignatureD hsmod@(L _ HsModule { hsmodName = Just (L _ modname) })) = do
    dflags <- getDynFlags
    mod_summary <- liftIO $ hsModuleToModSummary dflags HsigFile bs hsmod
    let this_mod = ms_mod mod_summary
    -- XXX recompilation checking doesn't work
    let modified = SourceModified
    -- Do the compilation!
    hsc_env <- getSession
    hmi <- liftIO $ compileOne hsc_env mod_summary i (bs_decls bs) Nothing Nothing modified
    -- Program the IIT...
    let specific_mod = mkModule (thisPackage dflags) (moduleName this_mod)
    updateEpsGhc_ $ \eps ->
        eps { eps_IIT = extendModuleEnv (eps_IIT eps) specific_mod (hm_iface hmi) }
    -- ... and load the RENAMED THING into the HIT
    iface <- liftIO $ rnModIface hsc_env (thisPackage dflags) (hm_iface hmi)
    {-pprTrace "tc'd hole" (ppr (mi_exports iface)) $-}
    addIfaceToHIT dflags loc iface
    -- Update what's in scope
    hsc_env <- getSession
    let ifaces1 = addToUFM_C mergeModIfaceForImport (hsc_ifaces hsc_env) modname iface
        hsc_env1 = hsc_env { hsc_ifaces = ifaces1 }
    setSession hsc_env1

-- These should have already been caught by shaping
compilePkgDecl' _ _ _ (ModuleD _) = panic "compilePkgDecl': ModuleD missing modname"
compilePkgDecl' _ _ _ (SignatureD _) = panic "compilePkgDecl': SignatureD missing modname"

compilePkgDecl' bs i loc (IncludeD IncludeDecl{ idPackageName = L _ name@(PackageName fs_name), idInclSpec = ispec }) = do
    hsc_env <- getSession
    dflags <- getDynFlags
    liftIO . compilationProgressMsg dflags $
        (showModuleIndex (i, bs_decls bs) ++ "Including " ++ unpackFS fs_name)
    -- Typecheck it
    new_ifaces <- tcInclude loc (bs_internal_shape bs) name ispec
    -- TODO: need to COMPILE the includes if we instantiate them
    -- Put the includes into scope
    let ifaces1 = addListToUFM_C mergeModIfaceForImport (hsc_ifaces hsc_env) new_ifaces
        hsc_env1 = hsc_env { hsc_ifaces = ifaces1 }
    setSession hsc_env1

tcInclude :: RealSrcSpan -> Shape -> PackageName -> Maybe LInclSpec -> Ghc [(ModuleName, ModIface)]
tcInclude loc sh n ispec = do
    hsc_env <- getSession
    dflags <- getDynFlags
    eps <- liftIO $ readIORef (hsc_EPS hsc_env)
    case Map.lookup n (eps_EST eps) of
        Nothing -> panic "tcInclude: no package"
        Just incl_sh -> do
            Shape{ sh_provides = provs
                 , sh_requires = reqs } <- liftIO $ renameShape hsc_env ispec incl_sh
            -- A little hack: use the /internal/ final shape context
            -- from the package to re-derive what the hole substitution here
            -- was.
            hsubst <- liftIO $ computeHoleSubst dflags (sh_provides sh) reqs
            let ifExc m = do r <- liftIO $ initIfaceCheck hsc_env m
                             case r of
                                Failed err -> pprPanic "oops" err -- liftIO $ throwGhcExceptionIO (ProgramError (showSDoc dflags err))
                                Succeeded (x, _) -> return x
            -- NB: no fixpointing is necessary
            prov_ifaces <- forM (Map.toList provs) $ \(modname, (m, _)) -> do
                                m' <- fmap fst . liftIO $ renameHoleModule dflags hsubst m
                                iface <- ifExc $ computeInterface (text "prov_iface") False m'
                                return (modname, iface)
            req_ifaces <- forM (Map.toList reqs) $ \(modname, (ms, _)) -> do
                                ms' <- mapM (fmap fst . liftIO . renameHoleModule dflags hsubst) ms
                                ifaces <- mapM (ifExc . computeInterface (text "req_iface") False) ms'
                                mapM_ (addIfaceToHIT dflags loc) ifaces
                                return [(modname, iface) | iface <- ifaces]
            return (prov_ifaces ++ concat req_ifaces)

-- throwErrors :: ErrorMessages -> Hsc a
-- throwErrors = liftIO . throwIO . mkSrcErr


addIfaceToHIT dflags loc iface = do
    hsc_env <- getSession
    let mod = mi_module iface
        addToHIT eps iface = eps { eps_HIT = addToUFM (eps_HIT eps)
                                                      (moduleName mod)
                                                      (iface, False) }
    case isHoleModule mod of
      True -> do
        mb_err <- updateEpsGhc $ \eps ->
            case lookupUFM (eps_HIT eps) (moduleName mod) of
                Nothing        -> (addToHIT eps iface, Nothing)
                Just (_, True) -> (eps, Just stale_msg)
                Just (iface', False) -> case mergeModIface iface' iface of
                    Failed err -> (eps, Just (format_msgs err))
                    Succeeded iface'' -> pprTrace "merge ok" (ppr (mi_exports iface') $$ ppr (mi_exports iface) $$ ppr (mi_exports iface'')) $ (addToHIT eps iface'', Nothing)
        case mb_err of
            Just err -> liftIO . throwIO $ mkSrcErr err
            Nothing -> return ()
      False ->
        -- We *know* what this is, so instead we do the boot check
        -- ala TcRnDriver
        let ifExc (Failed err) = liftIO $ throwGhcExceptionIO (ProgramError (showSDoc dflags err))
            ifExc (Succeeded (iface,_)) = return iface
        in liftIO . runHsc hsc_env . ioMsgMaybe . initTc hsc_env HsSrcFile False mod loc $ do
                    boot_details <- typecheckIface iface
                    local_details <- typecheckIface =<< ifExc =<< initIfaceTcRn (computeInterface (text "boot check") False mod)
                    _ <- checkHiBootIface' (md_insts local_details)
                                           (md_types local_details)
                                           (md_exports local_details)
                                           boot_details
                    return ()
  where
    format_msgs errs = listToBag
                            [ mkLongErrMsg dflags (RealSrcSpan loc) alwaysQualify
                                           msg
                                           (ppr d1 $$ ppr d2)
                                           -- TODO: make this prettier
                            | (d1, d2, msg) <- errs ]
    stale_msg = unitBag $ mkPlainErrMsg dflags (RealSrcSpan loc) (text "Stale")
