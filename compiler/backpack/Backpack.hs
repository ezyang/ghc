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

import DynFlags
import OccName
import Avail
import NameEnv
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

import IfaceSyn

import GHC.Fingerprint
import Data.IORef
import Control.Monad
import qualified Data.Map as Map
import System.FilePath
import qualified Data.Traversable as T

-- ----------------------------------------------------------------------------
-- Run --backpack mode

-- | Summary of a bkp file, analogous to 'ModSummary'.
data BkpSummary = BkpSummary {
    bs_pkg_name :: PackageName,
    bs_internal_shape :: Shape,
    bs_path :: FilePath,
    bs_decls :: Int
    }

-- | Apply a function on 'DynFlags' on an 'HscEnv'
overHscDynFlags :: (DynFlags -> DynFlags) -> HscEnv -> HscEnv
overHscDynFlags f hsc_env = hsc_env { hsc_dflags = f (hsc_dflags hsc_env) }

-- | Entry point to compile a Backpack file.
doBackpack :: FilePath -> Ghc ()
doBackpack src_filename = do
    hsc_env <- getSession
    buf <- liftIO $ hGetStringBuffer src_filename
    let dflags = hsc_dflags hsc_env
        loc = mkRealSrcLoc (mkFastString src_filename) 1 1
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
                -- Merge the ModIfaces for the requirements
                {-
                merged_ifaces <- T.forM (sh_requires sh) $ \(mods, _) -> do
                    ifaces <- forM mods $ \mod -> do
                        imod <- liftIO $ generalizeHoleModule dflags mod
                        case lookupModuleEnv (eps_IIT eps) imod of
                            Nothing -> panic "where'd it go"
                            Just iface ->
                              initIfaceLcl (mi_module iface) (modulePackageKey mod)
                                           (text "(from the IIT)") $ undefined
                    case foldM mergeModIface (head ifaces) (tail ifaces) of
                        Failed sdoc -> panic "failed"
                        Succeeded iface -> return iface
                        -}
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
compilePkgDecl bs (i, (L _ decl)) = compilePkgDecl' bs i decl

-- TODO: move this to PackageName
packageNameFS :: PackageName -> FastString
packageNameFS (PackageName fs) = fs

-- | Up until now, GHC has assumed a single compilation target per source file.
-- Backpack files with inline modules break this model, since a single file
-- may generate multiple output files.  How do we decide to name these files?
-- Should there only be one output file? This function our current heuristic,
-- which is we make a "fake" module and use that.
hsModuleToModSummary :: HscSource
                     -> BkpSummary
                     -> Located (HsModule RdrName)
                     -> Ghc ModSummary
hsModuleToModSummary hsc_src bs
                     hsmod@(L _ HsModule { hsmodName = Just (L _ modname) }) = do
    dflags <- getDynFlags
    -- Sort of the same deal as in DriverPipeline's getLocation
    location <- liftIO $ mkHomeModLocation2 dflags modname
                             (unpackFS (packageNameFS (bs_pkg_name bs)) </>
                              moduleNameSlashes modname)
                             (case hsc_src of
                                  HsSrcFile -> "hs"
                                  HsBootFile -> "hs-boot"
                                  HsigFile -> "hsig")
    -- This duplicates a pile of logic in GhcMake
    time <- liftIO $ getModificationUTCTime (bs_path bs) -- TODO cache me
    let this_package | HsigFile <- hsc_src = holePackageKey
                     | otherwise = thisPackage dflags
        this_mod = mkModule this_package modname
    hi_timestamp <- liftIO $ modificationTimeIfExists (ml_hi_file location)
    return ModSummary {
            ms_mod = this_mod,
            ms_hsc_src = hsc_src,
            ms_location = location,
            ms_hspp_file = error "hsModuleToModSummary: no ms_hspp_file",
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
hsModuleToModSummary _ _ _ = panic "hsModuleToModSummary: no module name"

-- | Update the EPS from the Ghc monad. TODO move to appropriate library spot.
updateEpsGhc_ :: GhcMonad m => (ExternalPackageState -> ExternalPackageState) -> m ()
updateEpsGhc_ f = do
    hsc_env <- getSession
    liftIO $ atomicModifyIORef' (hsc_EPS hsc_env) (\x -> (f x, ()))

getEpsGhc :: GhcMonad m => m ExternalPackageState
getEpsGhc = do
    hsc_env <- getSession
    liftIO $ readIORef (hsc_EPS hsc_env)

-- | Compile a (non-located) package declaration.  Updates the session.
compilePkgDecl' :: BkpSummary -> Int -> HsPkgDecl -> Ghc ()
compilePkgDecl' bs i (ModuleD hsmod@(L _ HsModule { hsmodName = Just (L _ modname) })) = do
    hsc_env <- getSession
    dflags <- getDynFlags
    -- This is an inline module, fake up a ModSummary
    mod_summary <- hsModuleToModSummary HsSrcFile bs hsmod
    let this_mod = ms_mod mod_summary
    -- XXX recompilation checking doesn't work
    let modified = SourceModified
    -- Do the compilation!
    hmi <- liftIO $ compileOne hsc_env mod_summary i (bs_decls bs) Nothing Nothing modified
    -- Add the module to the HPT and put it into scope
    let hpt1 = addToUFM (hsc_HPT hsc_env) modname hmi
        ifaces1 = addToUFM_C (++) (hsc_ifaces hsc_env) modname [hm_iface hmi]
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

compilePkgDecl' bs i (SignatureD hsmod@(L _ HsModule { hsmodName = Just (L _ modname) })) = do
    hsc_env <- getSession
    dflags <- getDynFlags
    mod_summary <- hsModuleToModSummary HsigFile bs hsmod
    let this_mod = ms_mod mod_summary
    -- XXX recompilation checking doesn't work
    let modified = SourceModified
    -- Do the compilation!
    hmi <- liftIO $ compileOne hsc_env mod_summary i (bs_decls bs) Nothing Nothing modified
    -- Program the IIT...
    let specific_mod = mkModule (thisPackage dflags) (moduleName this_mod)
    updateEpsGhc_ $ \eps ->
        eps { eps_IIT = extendModuleEnv (eps_IIT eps) specific_mod (hm_iface hmi) }
    -- ... and load it into the EPS
    -- (this is a little wasteful, since we do have the type-checked ModGuts,
    -- but it's the easiest way to reuse the logic here.)
    liftIO . initIfaceCheck hsc_env $ loadSysInterface (text "signature") specific_mod
    -- Update what's in scope
    hsc_env <- getSession
    let ifaces1 = addToUFM_C (++) (hsc_ifaces hsc_env) modname [hm_iface hmi]
        hsc_env1 = hsc_env { hsc_ifaces = ifaces1 }
    setSession hsc_env1

-- These should have already been caught by shaping
compilePkgDecl' _ _ (ModuleD _) = panic "compilePkgDecl': ModuleD missing modname"
compilePkgDecl' _ _ (SignatureD _) = panic "compilePkgDecl': SignatureD missing modname"

compilePkgDecl' bs i (IncludeD IncludeDecl{ idPackageName = L _ name@(PackageName fs_name), idInclSpec = Nothing }) = do
    hsc_env <- getSession
    dflags <- getDynFlags
    liftIO . compilationProgressMsg dflags $
        (showModuleIndex (i, bs_decls bs) ++ "Including " ++ unpackFS fs_name)
    -- Typecheck it
    new_ifaces <- tcInclude (bs_internal_shape bs) name
    -- TODO: need to COMPILE the includes if we instantiate them
    -- Put the includes into scope
    let ifaces1 = addListToUFM_C (++) (hsc_ifaces hsc_env) new_ifaces
        hsc_env1 = hsc_env { hsc_ifaces = ifaces1 }
    setSession hsc_env1

tcInclude :: Shape -> PackageName -> Ghc [(ModuleName, [ModIface])]
tcInclude sh n = do
    hsc_env <- getSession
    dflags <- getDynFlags
    let ifaces = hsc_ifaces hsc_env
    eps <- liftIO $ readIORef (hsc_EPS hsc_env)
    case Map.lookup n (eps_EST eps) of
        Nothing -> panic "tcInclude: no package"
        -- TODO implement renaming
        Just Shape { sh_provides = provs, sh_requires = reqs } -> do
            -- A little hack: use the /internal/ final shape context
            -- from the package to re-derive what the hole substitution here
            -- was.
            hsubst <- liftIO $ computeHoleSubst dflags (sh_provides sh) reqs
            -- NB: no fixpointing is necessary
            prov_ifaces <- liftIO . forM (Map.toList provs) $ \(modname, (m, _)) -> do
                                m' <- fmap fst $ renameHoleModule dflags hsubst m
                                iface <- initIfaceCheck hsc_env $ loadSysInterface (text "prov_iface") m'
                                return (modname, [iface])
            req_ifaces <- liftIO . forM (Map.toList reqs) $ \(modname, (ms, _)) -> do
                                ms' <- mapM (fmap fst . renameHoleModule dflags hsubst) ms
                                ifaces <- mapM (initIfaceCheck hsc_env . loadSysInterface (text "req_iface")) ms'
                                return (modname, ifaces)
            return (prov_ifaces ++ req_ifaces)

-- MaybeErr is a bad warning because we want to report as
-- many errors as possible
-- TODO totally unclear what fingerprints should be, so omitted for now
mergeIfaceDecls :: [IfaceDecl]
           -> [IfaceDecl]
           -> MaybeErr SDoc [IfaceDecl]
mergeIfaceDecls ds1 ds2 =
    let mkE ds = mkOccEnv [ (ifName d, return d) | d <- ds ]
    in sequence (occEnvElts (plusOccEnv_C (\mx my -> mx >>= \x -> my >>= \y -> mergeIfaceDecl x y) (mkE ds1) (mkE ds2)))

mergeModIface :: ModIface -> ModIface -> MaybeErr SDoc ModIface
mergeModIface iface1 iface2 = do
    MASSERT( mi_module iface1 == mi_module iface2 )
    merged_decls <- fmap (map ((,) fingerprint0))
                  $ mergeIfaceDecls (map snd (mi_decls iface1))
                               (map snd (mi_decls iface2))
    let fixities = mergeFixities (mi_fixities iface1) (mi_fixities iface2)
        warns = mergeWarnings (mi_warns iface1) (mi_warns iface2)
    -- Actually, I think a lot of these fields won't be used
    return (emptyModIface (mi_module iface1)) {
        -- Fake in-memory interfaces always have empty sig-of
        mi_sig_of = Nothing,
        mi_decls = merged_decls,
        -- Some harmless things which are easy to compute
        mi_orphan = mi_orphan iface1 || mi_orphan iface2,
        mi_finsts = mi_finsts iface1 || mi_finsts iface2,
        mi_used_th = mi_used_th iface1 || mi_used_th iface2,
        -- The key things
        mi_fixities = fixities,
        mi_warns = warns,
        mi_fix_fn = mkIfaceFixCache fixities,
        mi_warn_fn = mkIfaceWarnCache warns,
        mi_hash_fn = \n -> case mi_hash_fn iface1 n of
                            Nothing -> mi_hash_fn iface2 n
                            Just r -> Just r,
        -- Stuff we can stub out so we fail fast (had to be non-strict)
        mi_deps      = noDependencies, -- BOGUS
        mi_usages    = panic "No mi_usages in HOLE",
        mi_anns      = panic "No mi_anns in HOLE",
        mi_insts     = panic "No mi_insts in HOLE",
        mi_fam_insts = panic "No mi_fam_insts in HOLE",
        mi_rules     = panic "No mi_rules in HOLE"
    }

mergeFixities :: [(OccName, Fixity)] -> [(OccName, Fixity)] -> [(OccName, Fixity)]
mergeFixities fix1 fix2 =
    let forceEqual x y | x == y = x
                       | otherwise = panic "mergeFixities"
    in mergeOccList forceEqual fix1 fix2

mergeOccList :: ((OccName, a) -> (OccName, a) -> (OccName, a))
             -> [(OccName, a)] -> [(OccName, a)] -> [(OccName, a)]
mergeOccList f xs1 xs2 =
    let oe1 = mkOccEnv [ (fst x, x) | x <- xs1 ]
        oe2 = mkOccEnv [ (fst x, x) | x <- xs2 ]
    in occEnvElts (plusOccEnv_C f oe1 oe2)

-- TODO: better merging
mergeWarnings :: Warnings -> Warnings -> Warnings
mergeWarnings w@WarnAll{} _ = w
mergeWarnings _ w@WarnAll{} = w
mergeWarnings (WarnSome ws1) (WarnSome ws2) = WarnSome (mergeOccList const ws1 ws2)
mergeWarnings w@WarnSome{} _ = w
mergeWarnings _ w@WarnSome{} = w
mergeWarnings NoWarnings NoWarnings = NoWarnings
