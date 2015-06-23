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

import DynFlags
import TcRnMonad
import Module
import HscTypes
import StringBuffer
import FastString
import ErrUtils
import SrcLoc
import HscMain
import UniqFM
import Outputable
import Maybes
import HeaderInfo
import MkIface
import ShUnitKey
import GhcMake

import UniqSet

import GHC.PackageDb
import System.Exit
import Data.IORef
import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import System.FilePath
import Data.Version

-- ----------------------------------------------------------------------------
-- Backpack monad

-- Backpack monad is a 'GhcMonad' which also maintains a little extra state
-- beyond the 'Session', c.f. 'BkpEnv'.
type BkpM = IOEnv BkpEnv

-- | Backpack environment.  NB: this has a 'Session' and not an 'HscEnv',
-- because we are going to update the 'HscEnv' as we go.
data BkpEnv
    = BkpEnv {
        -- | The session
        bkp_session :: Session,
        -- | Table of Backpack things (fix me soon)
        bkp_table :: IORef (Map IndefUnitId LHsUnit),
        -- | The filename of the bkp file we're compiling
        bkp_filename :: FilePath,
        -- | When a package we are compiling includes another package
        -- which has not been compiled, we bump the level and compile
        -- that.
        bkp_level :: Int
    }

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

-- | Get the nesting level, when recursively compiling modules.
getBkpLevel :: BkpM Int
getBkpLevel = bkp_level `fmap` getBkpEnv

-- | Apply a function on 'DynFlags' on an 'HscEnv'
overHscDynFlags :: (DynFlags -> DynFlags) -> HscEnv -> HscEnv
overHscDynFlags f hsc_env = hsc_env { hsc_dflags = f (hsc_dflags hsc_env) }

-- | Lookup the source of a package (to instantiate it.)
lookupBackpack :: IndefUnitId -> BkpM LHsUnit
lookupBackpack uid = do
    ref <- fmap bkp_table getBkpEnv
    tbl <- readMutVar ref
    -- TODO: local units only currently
    case Map.lookup uid tbl of
        Nothing -> panic "nothing"
        Just p -> return p

-- | Run 'ShM' in a 'BkpM'.
runShM :: ShM a -> BkpM a
runShM m = do
    hsc_env <- getSession
    env <- getBkpEnv
    liftIO (runHsc hsc_env (ioMsgMaybe (initShM hsc_env (bkp_filename env) m)))

-- | Run a 'BkpM' computation, with the nesting level bumped one.
innerBkpM :: BkpM a -> BkpM a
innerBkpM do_this = do
    -- NB: withTempSession mutates, so we don't have to worry
    -- about bkp_session being stale.
    updEnv (\env -> env { bkp_level = bkp_level env + 1 }) do_this

-- | Update the EPS from a 'GhcMonad'. TODO move to appropriate library spot.
updateEpsGhc_ :: GhcMonad m => (ExternalPackageState -> ExternalPackageState) -> m ()
updateEpsGhc_ f = do
    hsc_env <- getSession
    liftIO $ atomicModifyIORef' (hsc_EPS hsc_env) (\x -> (f x, ()))

-- | Get the EPS from a 'GhcMonad'.
getEpsGhc :: GhcMonad m => m ExternalPackageState
getEpsGhc = do
    hsc_env <- getSession
    liftIO $ readIORef (hsc_EPS hsc_env)

-- | Run 'BkpM' in 'Ghc'.
initBkpM :: FilePath -> BkpM a -> Ghc a
initBkpM file m =
    reifyGhc $ \session -> do
    table_var <- newIORef Map.empty
    let env = BkpEnv {
                    bkp_session = session,
                    bkp_table = table_var,
                    bkp_filename = file,
                    bkp_level = 0
                }
    runIOEnv env m

-- ----------------------------------------------------------------------------
-- Messaging

-- | Print a compilation progress message, but with indentation according
-- to @level@ (for nested compilation).
backpackProgressMsg :: Int -> DynFlags -> String -> IO ()
backpackProgressMsg level dflags msg =
    compilationProgressMsg dflags $ replicate (level * 2) ' ' ++ msg

-- | Creates a 'Messager' for Backpack compilation; this is basically
-- a carbon copy of 'batchMsg' but calling 'backpackProgressMsg', which
-- handles indentation.
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

-- | 'PprStyle' for Backpack messages; here we usually want the module to
-- be qualified (so we can tell how it was instantiated.) But we try not
-- to qualify packages so we can use simple names for them.
backpackStyle :: PprStyle
backpackStyle =
    mkUserStyle
        (QueryQualify neverQualifyNames
                      alwaysQualifyModules
                      neverQualifyPackages) AllTheWay

-- | Message when we initially process a Backpack unit.
msgTopPackage :: (Int,Int) -> UnitName -> BkpM ()
msgTopPackage (i,n) (UnitName fs_pn) = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags
        $ showModuleIndex (i, n) ++ "Processing " ++ unpackFS fs_pn

-- | Message when we instantiate a Backpack unit.
msgUnitKey :: UnitKey -> BkpM ()
msgUnitKey pk = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags
        $ "Instantiating " ++ renderWithStyle dflags (ppr pk) backpackStyle

-- | Message when we include a Backpack unit.
msgInclude :: (Int,Int) -> IndefUnitId -> BkpM ()
msgInclude (i,n) uid = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags
        $ showModuleIndex (i, n) ++ "Including " ++
          renderWithStyle dflags (ppr uid) backpackStyle

-- ----------------------------------------------------------------------------
-- Run --backpack mode

-- | Entry point to compile a Backpack file.
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
            initBkpM src_filename $
                forM_ (zip [1..] bkp) $ \(i,pkg) -> do
                    let unit_name = unLoc (hsunitName (unLoc pkg))
                    msgTopPackage (i,length bkp) unit_name
                    -- Cache the package
                    bkp_table_ref <- fmap bkp_table getBkpEnv
                    let uid = IndefiniteUnitId (thisIPID dflags)
                                               (Just unit_name)
                    updMutVar bkp_table_ref (Map.insert uid pkg)
                    -- Typecheck (and compile) the package
                    innerBkpM $ do
                        mb_pk <- typecheckUnit pkg
                        case mb_pk of
                            Just pk -> compileUnit pk pkg
                            Nothing -> return ()

-- | Create a temporary Session to do some sort of type checking or
-- compilation.  This function is responsible for managing a few things,
-- including (1) deciding where the output files of the process go,
-- (2) configuring the module map, so we know what modules are in scope,
-- based on the 'IncludeGraph', and (3) setting up 'sigOf' properly.
withBkpSession :: UnitKey -> IncludeGraph -> Bool -> BkpM a -> BkpM a
withBkpSession pk include_graph tc_only do_this = do
    dflags <- getDynFlags
    uid <- liftIO $ unitKeyUnitId dflags pk
    let pkg_key = unpackFS (unitKeyFS pk)
        unit_name = case indefUnitName uid of
                     Just (UnitName fs) -> unpackFS fs
                     Nothing -> pkg_key -- TODO shouldn't happen
        key_base p | Just f <- p dflags = f
                   | otherwise          = "out"
        outdir p | tc_only   = key_base p </> unit_name
                 | otherwise = key_base p </> unit_name </> pkg_key
        -- TODO: handle collisions properly
        mod_map = Map.unions (map is_provides include_graph)
    insts <- liftIO $ unitKeyInsts dflags pk
    withTempSession (overHscDynFlags (\dflags ->
      -- If we're type-checking an indefinite package, we want to
      -- turn on interface writing.  However, if the user also
      -- explicitly passed in `-fno-code`, we DON'T want to write
      -- interfaces unless the user also asked for `-fwrite-interface`.
      (if tc_only && hscTarget dflags /= HscNothing
        then flip gopt_set Opt_WriteInterface
        else id) $
      dflags {
        hscTarget   = if tc_only then HscNothing
                                 else hscTarget dflags,
        thisPackage = pk,
        objectDir   = Just (outdir objectDir),
        hiDir       = Just (outdir hiDir),
        stubDir     = Just (outdir stubDir),
        sigOf       = Map.fromList insts,
        packageModuleMap = mod_map
      } )) $ do_this

-- | Create a temporary session for type-checking.
withBkpTcSession :: UnitKey -> IncludeGraph -> BkpM a -> BkpM a
withBkpTcSession pk include_graph do_this = do
    old_eps <- getEpsGhc
    r <- withBkpSession pk include_graph True do_this
    -- Restore the old EPS from prior to typechecking.  This is because
    -- any indefinite TyThings we stored in the EPS may become invalid
    -- on future runs, if shaping changes.
    --
    -- Resetting the entire EPS to prior to the compilation is a pretty big
    -- hammer, but better than totally clearing the EPS.
    updateEpsGhc_ (\eps -> old_eps {
            eps_EST = eps_EST eps
        })
    return r

-- | Create a temporary session for compilation.
withBkpCompSession :: UnitKey -> IncludeGraph -> BkpM a -> BkpM a
withBkpCompSession pk include_graph do_this =
    withBkpSession pk include_graph False do_this

-- | Type checks a unit and adds it to the indefinite unit database. Returns
-- 'Just pk' if it's definite (which means we can compile it eagerly).
typecheckUnit :: LHsUnit -> BkpM (Maybe UnitKey)
typecheckUnit pkg = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
        unit_name = unLoc (hsunitName (unLoc pkg))
        is_exe = unit_name == UnitName (fsLit "main")
    shpk <- runShM $ shComputeUnitKey pkg
    pk <- liftIO $ newUnitKey' dflags shpk
    when (not is_exe) $ do
        -- Desugar into the include and module graphs we need
        include_graph <- runShM $ shIncludeGraph pk pkg
        ipkg <- withBkpTcSession pk include_graph $ do
            dflags <- getDynFlags
            mod_graph <- runShM $ shModGraph pk include_graph pkg

            -- Record the shape in the EPS, so that type-checking
            -- can see it.
            sh <- runShM $ shPackage pk pkg
            sh_subst <- liftIO $ computeShapeSubst hsc_env sh
            updateEpsGhc_ (\eps -> eps { eps_shape = sh_subst } )

            msg <- mkBackpackMsg
            ok <- load' LoadAllTargets (Just msg) mod_graph
            when (failed ok) (liftIO $ exitWith (ExitFailure 1))

            -- TODO: exports
            let prov_mods = Map.fromList [ (ms_mod_name ms, ms_mod ms)
                                         | ms <- mod_graph
                                         , ms_hsc_src ms == HsSrcFile ]

            -- TODO assert that the holes are right...
            let hi_dir = expectJust (panic "Backpack hiDir") $ hiDir dflags
            let serializeProvision (modname, m) = do
                    m' <- serializeModule dflags m
                    return (modname, m')
            provs <- liftIO $ mapM serializeProvision (Map.toList prov_mods)
            return IndefiniteUnitInfo {
                    indefUnitId = shUnitKeyUnitId shpk,
                    indefProvides = provs,
                    indefRequires = uniqSetToList (shUnitKeyFreeHoles shpk),
                    indefImportDirs = [hi_dir]
                }
        -- NB: This is outside 'withBkpTcSession' so the update to 'Session'
        -- sticks.
        addIndefiniteUnit ipkg
    return $ case () of
            _ | is_exe -> Just mainUnitKey
              -- This means we can compile immediately!
              | isEmptyUniqSet (shUnitKeyFreeHoles shpk) -> Just pk
              | otherwise -> Nothing

serializeModule :: DynFlags -> Module -> IO IndefModule
serializeModule dflags m = do
    uk <- serializeUnitKey dflags (moduleUnitKey m)
    return (IndefiniteModule uk (moduleName m))

serializeUnitKey :: DynFlags -> UnitKey -> IO IndefUnitKey
serializeUnitKey dflags pk = do
    shpk <- lookupUnitKey dflags pk
    insts <- serializeHoleMap dflags (shUnitKeyInsts shpk)
    return (IndefiniteUnitKey (shUnitKeyUnitId shpk) insts)

serializeHoleMap :: DynFlags -> [(ModuleName, Module)] -> IO [(ModuleName, IndefModule)]
serializeHoleMap dflags hmap =
    let ser (modname, mod) = do
            mod' <- serializeModule dflags mod
            return (modname, mod')
    in mapM ser hmap

-- | Compile a unit into code, adding it to the in-memory package database
-- if it is not an executable.
compileUnit :: UnitKey -> LHsUnit -> BkpM ()
compileUnit pk pkg = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
    let unit_name@(UnitName fs_unit_name) = unLoc (hsunitName (unLoc pkg))
        is_exe = unit_name == UnitName (fsLit "main") -- DUPE
    msgUnitKey pk
    include_graph <- runShM $ shIncludeGraph pk pkg
    insts <- liftIO $ unitKeyInsts dflags pk
    -- Compile the includes (outside so additions are added to package
    -- environment)
    forM_ (zip [1..] include_graph) $
        compileInclude (length include_graph)
    (exposed, hi_dir, obj_files) <- withBkpCompSession pk include_graph $ do
        dflags <- getDynFlags
        mod_graph <- runShM $ shModGraph pk include_graph pkg
        msg <- mkBackpackMsg
        ok <- load' LoadAllTargets (Just msg) mod_graph
        when (failed ok) (liftIO $ exitWith (ExitFailure 1))

        -- Generate info to register in database
        hsc_env <- getSession
        let home_mod_infos = eltsUFM (hsc_HPT hsc_env)
            linkables = map (expectJust "link".hm_linkable) home_mod_infos
            getOfiles (LM _ _ us) = map nameOfObject (filter isObject us)
            obj_files = concatMap getOfiles linkables

        let export_sig (modname, m) =
                ExposedModule modname Nothing
                              (Just (OriginalModule (moduleUnitKey m) (moduleName m)))
            export_mod ms = ExposedModule (ms_mod_name ms) Nothing Nothing

            sigs = map export_sig insts
            mods = [ export_mod ms | ms <- mod_graph, ms_hsc_src ms == HsSrcFile ]
            exposed = mods ++ sigs

            hi_dir = expectJust (panic "Backpack hiDir") $ hiDir dflags

        return (exposed, hi_dir, obj_files)
    let pkg = InstalledPackageInfo {
            installedPackageId = thisIPID dflags,
            abiHash = "",
            -- TODO this is all wrong
            sourcePackageId = SourcePackageId fs_unit_name,
            packageName = PackageName fs_unit_name,
            packageVersion = makeVersion [0],
            unitName = Just unit_name,
            unitKey = pk,
            exposedModules = exposed,
            hiddenModules = [], -- TODO: doc only
            instantiatedWith = [], -- TODO (not used by anything right now)
            -- 'depends' is important if we end up linking into a real
            -- executable
            depends = [ is_pkg_key is | is <- include_graph ]
                       ++ [ moduleUnitKey mod | (_, mod) <- insts],
            -- We didn't bother making an 'ar' archive which would be specified
            -- in 'hsLibraries', so instead we just add the object files to
            -- the linker options so they get linked in.  This is not such a
            -- good idea for -dynamic compilation; we should probably make
            -- the libraries in that case.
            ldOptions = obj_files,
            importDirs = [ hi_dir ],
            exposed = False,
            -- nope
            hsLibraries = [],
            extraLibraries = [],
            extraGHCiLibraries = [],
            libraryDirs = [],
            frameworks = [],
            frameworkDirs = [],
            ccOptions = [],
            includes = [],
            includeDirs = [],
            haddockInterfaces = [],
            haddockHTMLs = [],
            trusted = False
        }
    when (not is_exe) $ addPackage pkg

addIndefiniteUnit :: GhcMonad m => IndefiniteUnitConfig -> m ()
addIndefiniteUnit pkg = do
    dflags0 <- GHC.getSessionDynFlags
    case indefPkgDatabase dflags0 of
        Nothing -> panic "addIndefiniteUnit: called too early"
        Just pkgs -> do let dflags = dflags0 { indefPkgDatabase = Just (pkg : pkgs) }
                        _ <- GHC.setSessionDynFlags dflags
                        -- By this time, the global ref has probably already
                        -- been forced, in which case doing this isn't actually
                        -- going to do you any good.
                        -- dflags <- GHC.getSessionDynFlags
                        -- liftIO $ setUnsafeGlobalDynFlags dflags
                        return ()

addPackage :: GhcMonad m => PackageConfig -> m ()
addPackage pkg = do
    dflags0 <- GHC.getSessionDynFlags
    case pkgDatabase dflags0 of
        Nothing -> panic "addPackage: called too early"
        Just pkgs -> do let dflags = dflags0 { pkgDatabase = Just (pkg : pkgs) }
                        _ <- GHC.setSessionDynFlags dflags
                        -- By this time, the global ref has probably already
                        -- been forced, in which case doing this isn't actually
                        -- going to do you any good.
                        -- dflags <- GHC.getSessionDynFlags
                        -- liftIO $ setUnsafeGlobalDynFlags dflags
                        return ()

compileInclude :: Int -> (Int, IncludeSummary) -> BkpM ()
compileInclude n (i, is) = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
        pk = is_pkg_key is
    shpk <- liftIO $ lookupUnitKey dflags pk
    -- TODO: test if it's DEFINITE
    let can_compile = isJust (indefUnitName (shUnitKeyUnitId shpk))
        uid = shUnitKeyUnitId shpk
    msgInclude (i, n) uid
    -- Compile it, if necessary
    when can_compile $ do
        pkg <- lookupBackpack uid
        innerBkpM $ compileUnit pk pkg
