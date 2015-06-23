{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
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
import MkIface
import Exception
import Bag
import ShPackageKey
import Shape

import UniqSet

import System.Exit
import Data.IORef
import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import System.FilePath

-- TODO: move this to PackageName
packageNameFS :: PackageName -> FastString
packageNameFS (PackageName fs) = fs

-- ----------------------------------------------------------------------------
-- Backpack monad

-- | When doing Backpack compilation, we compile multiple package keys
-- as the "home package"; this type records all of them.
type HptCache = Map PackageKey HomePackageTable

-- | Backpack environment
data BkpEnv
    = BkpEnv {
        -- | The session
        bkp_session :: Session,
        -- | Table of Backpack things (fix me soon)
        bkp_table :: IORef (Map PackageName LHsPackage),
        -- | The filename of the bkp file we're compiling
        bkp_filename :: FilePath,
        -- | Mapping of each package key to HPT we have COMPILED. We
        -- grovel in this when linking to find all of the local objects
        -- we may have compiled but don't exist in the installed package
        -- database.
        bkp_hpt_cache :: IORef HptCache,
        -- | When a package we are compiling includes another package
        -- which has not been compiled, we bump the level and compile
        -- that.
        bkp_level :: Int,
        -- | The "base" 'DynFlags'; the 'DynFlags' in the 'HscEnv'
        -- may be temporarily modified, so we want to base any modifications
        -- on the ORIGINAL 'DynFlags'.  See @-outputdir@ flags for an
        -- example.
        bkp_dflags :: DynFlags
    }

type BkpM = IOEnv BkpEnv

-- Blah, to get rid of the default instance for IOEnv
instance {-# OVERLAPPING #-} HasDynFlags BkpM where
    getDynFlags = fmap hsc_dflags getSession

instance GhcMonad BkpM where
    getSession = do
        Session s <- fmap bkp_session getEnv
        readMutVar s
    setSession hsc_env = do
        Session s <- fmap bkp_session getEnv
        writeMutVar s hsc_env

-- | Get the current 'BkpEnv'.
getBkpEnv :: BkpM BkpEnv
getBkpEnv = getEnv

getBkpLevel :: BkpM Int
getBkpLevel = bkp_level `fmap` getBkpEnv

-- | Skip @do_this@ if @pk@ is already recorded in the HPT cache;
-- otherwise run @do_this@ and place the result in the HPT cache.
hptCache :: PackageKey -> BkpM () -> BkpM ()
hptCache pk do_this = do
    hpt_cache <- getHptCache
    when (Map.notMember pk hpt_cache) $ do
        do_this
        hsc_env <- getSession
        env <- getBkpEnv
        liftIO $ modifyIORef' (bkp_hpt_cache env) (Map.insert pk (hsc_HPT hsc_env))

-- | Get the current HPT cache
getHptCache :: BkpM HptCache
getHptCache = do
    env <- getBkpEnv
    liftIO (readIORef (bkp_hpt_cache env))

-- | Apply a function on 'DynFlags' on an 'HscEnv'
overHscDynFlags :: (DynFlags -> DynFlags) -> HscEnv -> HscEnv
overHscDynFlags f hsc_env = hsc_env { hsc_dflags = f (hsc_dflags hsc_env) }

-- | Lookup the source of a package (to instantiate it.)
lookupBackpack :: PackageName -> BkpM LHsPackage
lookupBackpack pn = do
    ref <- fmap bkp_table getBkpEnv
    tbl <- readMutVar ref
    case Map.lookup pn tbl of
        Nothing -> panic "nothing"
        Just p -> return p

-- | Run 'ShM' in any 'GhcMonad'.
runShM :: GhcMonad m => FilePath -> PackageName -> ShM a -> m a
runShM f name m = do
    hsc_env <- getSession
    liftIO (runHsc hsc_env (ioMsgMaybe (initShM hsc_env f name m)))

innerBkpM :: BkpM a -> BkpM a
innerBkpM do_this = do
    init_dflags <- fmap bkp_dflags getBkpEnv
    updEnv (\env -> env { bkp_level = bkp_level env + 1 }) .
        -- NB: withTempSession mutates, so we don't have to worry
        -- about bkp_session being stale.
        withTempSession (\hsc_env -> hsc_env {hsc_dflags = init_dflags}) $
            do_this

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

-- | Run 'BkpM' in 'Ghc'.
initBkpM :: DynFlags -> FilePath -> BkpM a -> Ghc a
initBkpM dflags file m =
    reifyGhc $ \session -> do
    hpt_cache_var <- newIORef Map.empty
    table_var <- newIORef Map.empty
    let env = BkpEnv {
                    bkp_session = session,
                    bkp_table = table_var,
                    bkp_filename = file,
                    bkp_hpt_cache = hpt_cache_var,
                    bkp_level = 0,
                    bkp_dflags = dflags
                }
    runIOEnv env m

-- ----------------------------------------------------------------------------
-- Messaging

backpackProgressMsg :: Int -> DynFlags -> String -> IO ()
backpackProgressMsg level dflags msg =
    compilationProgressMsg dflags $ replicate (level * 2) ' ' ++ msg

mkBackpackMsg :: BkpM Messager
mkBackpackMsg = do
    level <- getBkpLevel
    return $ \hsc_env mod_index recomp mod_summary ->
      let dflags = hsc_dflags hsc_env
          showMsg msg reason =
            backpackProgressMsg level dflags $
                showModuleIndex mod_index ++
                msg ++ showModMsg dflags (hscTarget dflags)
                                  (recompileRequired recomp) mod_summary
                    ++ reason
      in case recomp of
            MustCompile -> showMsg "Compiling " ""
            UpToDate
                | verbosity (hsc_dflags hsc_env) >= 2 -> showMsg "Skipping  " ""
                | otherwise -> return ()
            RecompBecause reason -> showMsg "Compiling " (" [" ++ reason ++ "]")

msgTopPackage :: (Int,Int) -> PackageName -> BkpM ()
msgTopPackage (i,n) (PackageName fs_pn) = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags
        $ showModuleIndex (i, n) ++ "Processing " ++ unpackFS fs_pn

msgPackageKey :: Maybe a -> PackageKey -> BkpM ()
msgPackageKey Nothing _ = return ()
msgPackageKey (Just _) pk = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags
        $ "Instantiating " ++ renderWithStyle dflags (ppr pk) (mkUserStyle (QueryQualify neverQualifyNames alwaysQualifyModules neverQualifyPackages) AllTheWay)

msgInclude :: (Int,Int) -> PackageName -> BkpM ()
msgInclude (i,n) (PackageName fs_name) = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags $
        (showModuleIndex (i, n) ++ "Including " ++ unpackFS fs_name)

compileBackpack :: HscEnv
           -> ModSummary      -- ^ summary for module being compiled
           -> Int             -- ^ module N ...
           -> Int             -- ^ ... of M
           -> Maybe ModIface  -- ^ old interface, if we have one
           -> Maybe Linkable  -- ^ old linkable, if we have one
           -> SourceModified
           -> BkpM HomeModInfo   -- ^ the complete HomeModInfo, if successful
compileBackpack a b c d e f g = do
    msg <- mkBackpackMsg
    liftIO $ compileOne' Nothing (Just msg) a b c d e f g

-- ----------------------------------------------------------------------------
-- Run --backpack mode

-- | Summary of a Backpack package, analogous to 'ModSummary'.
data BkpSummary
    = BkpSummary {
        bs_pkg_name :: PackageName,
          -- ^ Identity of a package
        bs_decls :: Int
          -- ^ Cache of the number of declarations in the package.
        }

-- | Entry point to compile a Backpack file.
-- NB: inside of this is in the Ghc monad because we want to update
-- HscEnv as we go, and this is the common state that can be threaded
-- through the typechecker.
doBackpack :: FilePath -> Ghc ()
doBackpack src_filename = do
    -- Apply options from file to dflags
    -- TODO: When we reference other bkp files, these flags SHOULD NOT apply
    dflags0 <- getDynFlags
    src_opts <- liftIO $ getOptionsFromFile dflags0 src_filename
    (dflags, unhandled_flags, warns) <- liftIO $ parseDynamicFilePragma dflags0 src_opts
    modifySession (\hsc_env -> hsc_env {hsc_dflags = dflags})
    -- Cribbed from: preprocessFile / DriverPipeline
    liftIO $ checkProcessArgsResult dflags unhandled_flags
    liftIO $ handleFlagWarnings dflags warns
    -- TODO: something mumble preprocessing.  Maybe just right
    -- to move this into the DriverPipeline chain

    buf <- liftIO $ hGetStringBuffer src_filename
    let loc = mkRealSrcLoc (mkFastString src_filename) 1 1
    case unP parseBackpack (mkPState dflags buf loc) of
        PFailed span err -> do
            liftIO $ throwOneError (mkPlainErrMsg dflags span err)
        POk _ bkp -> do
            initBkpM dflags src_filename $
                forM_ (zip [1..] bkp) $ \(i,pkg) -> do
                    let pkg_name = unLoc (hspkgName (unLoc pkg))
                    msgTopPackage (i,length bkp) pkg_name
                    innerBkpM $ processPackage Nothing pkg

processPackage :: Maybe PackageKey -> LHsPackage -> BkpM ()
processPackage mb_pk pkg = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
    let pkg_name = unLoc (hspkgName (unLoc pkg))
        is_exe = pkg_name == PackageName (fsLit "main")
    bkp_table_ref <- fmap bkp_table getBkpEnv
    env <- getBkpEnv
    updMutVar bkp_table_ref (Map.insert pkg_name pkg)
    -- Shape the package
    -- TODO: when export specification is implemented for
    -- packages, need to return both the unfiltered and
    -- the filtered provisions.
    pk <- case mb_pk of
            Just pk -> return pk
            Nothing -> runShM (bkp_filename env) pkg_name $
                            shComputePackageKey is_exe pkg
    msgPackageKey mb_pk pk
    shpk <- liftIO $ lookupPackageKey dflags pk

    -- Figure out if we should generate code or not.
    -- If there are holes, we can't generate code.
    let (target, set_write_interface)
               | hscTarget dflags == HscNothing = (HscNothing, False)
               -- NB: if we set the target to HscNothing because
               -- we can't compile indefinite packages, we should
               -- still write the interface files
               | ShPackageKey { shPackageKeyFreeHoles = fh } <- shpk
               , not (isEmptyUniqSet fh) = (HscNothing, True)
               | otherwise = (hscTarget dflags, False)
    let pkg_key = unpackFS (packageKeyFS pk)
        key_base p | Just f <- p dflags = f
                   | otherwise          = "out"
        outdir p = key_base p </> pkg_key
    -- Setup the dflags for the package, and type-check/compile it!
    withTempSession (\hsc_env -> overHscDynFlags (\dflags ->
      (if set_write_interface
        then flip gopt_set Opt_WriteInterface
        else id) $
      dflags {
        hscTarget   = target,
        thisPackage = pk,
        objectDir   = Just (outdir objectDir),
        hiDir       = Just (outdir hiDir),
        stubDir     = Just (outdir stubDir),
        -- Add key_base so we can find the interface files we write out
        -- (technically should only be necessary when COMPILING; or
        -- maybe not at all if we properly cache everything)
        importPaths  = importPaths dflags ++ [key_base hiDir]
      -- NB: reset hsc_ifaces since this dictates visibility
      } ) hsc_env { hsc_ifaces = emptyUFM } ) . hptCache pk $ do

        (decls, Shape _ avail_sh) <- runShM (bkp_filename env) pkg_name $
                        shPackage pk pkg
        -- Record the shape in the EPS
        sh_subst <- liftIO $ computeShapeSubst hsc_env avail_sh
        updateEpsGhc_ (\eps -> eps { eps_shape = sh_subst } )

        let bs = BkpSummary {
                bs_pkg_name = unLoc (hspkgName (unLoc pkg)),
                bs_decls = length decls
            }

        mapM_ (compilePkgDecl bs) (zip [1..] decls)
    when is_exe $ do
        -- Link it (cribbed from GhcMake)
        let no_hs_main = gopt Opt_NoHsMain dflags
            a_root_is_Main = True -- TODO: test properly
            do_linking = a_root_is_Main || no_hs_main ||
                         ghcLink dflags == LinkDynLib ||
                         ghcLink dflags == LinkStaticLib
        hpt_cache <- getHptCache
        -- DynFlags link
        ok_flag <- liftIO $ linkMany (ghcLink dflags) dflags do_linking hpt_cache
        when (failed ok_flag) (liftIO $ exitWith (ExitFailure 1))
    -- Clear the EPS, because everything was loaded modulo a shape
    -- and it might be out-of-date the next time we shape.
    -- TODO: only eliminate things which depend on holes.
    when (target == HscNothing) $
        updateEpsGhc_ (\eps -> initExternalPackageState {
                eps_IIT = eps_IIT eps,
                eps_EST = eps_EST eps
            } )

-- | Compile a shaped package declaration.  Updates the session.
compilePkgDecl :: BkpSummary -> (Int, LShPkgDecl) -> BkpM ()
compilePkgDecl bs (i, L (RealSrcSpan loc) (ShDecl mod_summary)) = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
        this_mod = ms_mod mod_summary
        modname = moduleName this_mod
        is_sig = ms_hsc_src mod_summary == HsigFile
    -- XXX recompilation checking doesn't work
    let modified = SourceModified
    -- Do the compilation!
    hmi <- compileBackpack hsc_env mod_summary i (bs_decls bs) Nothing Nothing modified
    eps <- getEpsGhc
    -- Some extra business when it's a signature: we have to RENAME it because
    -- the normal typechecking process will put all new identifiers in HOLE:A
    -- rather than the REAL location
    -- See Note [Applying shaping to a signature ModIface]
    iface <- if is_sig
                then do iface <- liftIO $ rnModIface hsc_env (thisPackage dflags) (hm_iface hmi)
                        -- If compiling, check for compatibility
                        -- If typechecking, add to the iface we are merging prior to
                        -- typechecking
                        -- TODO: this is a terrible hack, because the WRITTEN
                        -- iface is WRONG WRONG WRONG
                        addIfaceToHIT dflags loc iface
                        return iface
                else return (hm_iface hmi)
    -- Add the module to the HPT and put it into scope
    let hpt1 = if is_sig
                then hsc_HPT hsc_env
                else addToUFM (hsc_HPT hsc_env) modname (hmi { hm_iface = iface })
        ifaces1 = addToUFM_C mergeModIfaceForImport (hsc_ifaces hsc_env) modname iface
        hsc_env1 = hsc_env { hsc_HPT = hpt1
                           , hsc_ifaces = ifaces1 }
    setSession hsc_env1
    -- Cache the interface if we were JUST typechecking (which means
    -- that this must be the most generalized version of the module)
    -- TODO: A bad user of the GHC API could trample this invariant.
    -- We must be sure NOT to redundantly type check an hsmod with a
    -- bad shape.
    when (hscTarget dflags == HscNothing) $
        let specific_mod = mkModule (thisPackage dflags) (moduleName this_mod)
        -- TODO assert specific_mod == this_mod for non-holes
        in updateEpsGhc_ $ \eps ->
            eps { eps_IIT = extendModuleEnv (eps_IIT eps) specific_mod (hm_iface hmi) }

compilePkgDecl bs (i, L (RealSrcSpan loc) (ShInclude pk (ModShape provs reqs))) = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
    shpk <- liftIO $ lookupPackageKey dflags pk
    -- TODO: test if it's DEFINITE
    let name = shPackageKeyPackageName shpk
    msgInclude (i, bs_decls bs) name
    -- Compile it, if necessary
    when (hscTarget dflags /= HscNothing) $ do
        pkg <- lookupBackpack name
        innerBkpM $ processPackage (Just pk) pkg
    let ifExc m = do r <- liftIO $ initIfaceCheck hsc_env m
                     case r of
                        Failed err -> pprPanic "oops" err -- liftIO $ throwGhcExceptionIO (ProgramError (showSDoc dflags err))
                        Succeeded (x, _) -> return x
    -- Collect up the interfaces (TODO: do this lazily?)
    prov_ifaces <- forM (Map.toList provs) $ \(modname, m) -> do
                        iface <- ifExc $ computeInterface (text "prov_iface") False m
                        return (modname, iface)
    req_ifaces <- forM (Map.toList reqs) $ \(modname, ms) -> do
                        ifaces <- mapM (ifExc . computeInterface (text "req_iface") False) ms
                        mapM_ (addIfaceToHIT dflags loc) ifaces
                        return [(modname, iface) | iface <- ifaces]
    let new_ifaces = prov_ifaces ++ concat req_ifaces
    -- Put the ifaces into scope
    let ifaces1 = addListToUFM_C mergeModIfaceForImport (hsc_ifaces hsc_env) new_ifaces
        hsc_env1 = hsc_env { hsc_ifaces = ifaces1 }
    setSession hsc_env1

-- Note [Applying shaping to a signature ModIface]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Consider the following signature:
--
--  signature H where
--      data A = A
--      f :: A -> A
--
-- Ordinarily, we would typecheck this into the following ModIface:
--
--  signature HOLE:H(HOLE:H.A, HOLE:H.f) where
--      data A = A
--      f :: HOLE:H -> HOLE:H
--
-- Note that the top-level declarations A and f are not qualified with
-- a module: we implicitly know that they come from HOLE:H and if we
-- want to refer to them we say HOLE:H.A / HOLE:H.f.  Additionally,
-- this ModIface comes with some useful information about the type A,
-- which we will cross-check against the implementation when it comes along.
--
-- What happens, then, if we discover via shaping that A is in fact q():Types.A
-- (but we still don't know what HOLE:A is.) Now our ModIface is wrong on
-- multiple counts:
--
--      1. Its export of HOLE:H.A is wrong (this can be fixed.)
--
--      2. Its self-references to HOLE:H.A are wrong (this can be fixed.)
--
--      3. It claims to define a data type A with one constructor
--      (implicitly) named HOLE:A.T; but no such type exists anymore.
--      (this cannot easily be fixed.)
--
-- (3) puts us in quite a pickle: it would be inaccurate to keep the
-- declaration, but it would also be wrong to drop it, since we do need
-- to check that q():Types.A really has got one constructor named A with
-- no arguments.  (NB: This check is actually delayed all the way to
-- when we find a module to fill HOLE:H, see bkpfail05.)
--
-- The solution is to just not bother trying to make sure our ModIfaces
-- are perfectly accurate: they may mention HOLEs but we can fix these
-- when we READ the ModIface (since we will also have a shape in that case.)
-- Of course, ModIfaces for definite packages will be accurate, since
-- (absent mutual recursion) they're just a pile of exports; but they
-- too will contain declarations for types and values so we can check
-- for compatibility after type-checking.

-- Note [Merging hole interfaces]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Consider the following Backpack file:
--
--  signature A where
--      data A
--  signature B where
--      import A
--      data B = B A
--  signature A where
--      import B
--      data A = A B
--  module M where
--      import A
--      import B
--      ...
--
-- When we typecheck M, we want to see that the 'TyThing's for
-- A and B are mutually recursive.  Ordinarily, this would be
-- achieved by making the inner TyThing (unsafely) lazy on
-- a lookup into the EPT for the other entity; the idea is
-- the thunk will only be pulled on after we've safely typechecked
-- everything into the EPT.
--
-- Unfortunately, disaster strikes for *signature merging*; namely,
-- we can't know if it's safe to load a signature unless we look
-- at the actual definition, tugging on the lazy definitions and
-- sending GHC into an infinite loop.
--
-- To work around this, we have to keep around the *original*, un-typechecked
-- ModIfaces to merge and check for compatibility: this is what goes in
-- the HIT.  When we load another signature into scope, we merge it into
-- the HIT *without* type-checking.  Eventually, when we typecheck M,
-- we finally need the TyThings for A and B; so we now finally type-check
-- the interfaces from the HIT.
--
-- Here's one troublesome case:
--
--  signature A where
--      data A
--  module M where
--      import A
--      data S = S A
--  signature A where
--      data A = A
--  module M2 where
--      f (S A) = ...
--
-- When we type-check M, A gets type-checked and M ends up with a
-- bunch of reference to a TyThing which describes A as an
-- abstract type.  But then, when we typecheck the second signature
-- for A, we now know a better TyThing for A, even though S's TyThing
-- is out of date.
--
-- In fact, this situation is exactly analogous hs-boot retypecheck
-- loops.  So eventually, we could support this by re-typechecking M
-- after we find more information about A.  But for now, we just
-- panic.  Let us know if it's a problem.


-- | Given a 'ModIface', add it to the HIT.
addIfaceToHIT :: GhcMonad m => DynFlags -> RealSrcSpan -> ModIface -> m ()
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
                    Succeeded iface'' -> (addToHIT eps iface'', Nothing)
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
                    -- NB: directly typecheck the interface because we need the
                    -- ModDetails.
                    local_details <-
                        if modulePackageKey mod == thisPackage dflags
                            -- Pull it out from the HPT if it's local
                            then let hpt = hsc_HPT hsc_env
                                 in case lookupHptByModule hpt mod of
                                        Just hm -> return (hm_details hm)
                                        Nothing -> panic "can't find it"
                            -- TODO: It MIGHT be in the cached HPT. But this
                            -- will always work. (NB: but not for HOME modules;
                            -- we don't know how to find the hi files in not
                            -- one-shot mode)
                            else typecheckIface =<< ifExc =<< initIfaceTcRn (computeInterface (text "boot check") False mod)
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
