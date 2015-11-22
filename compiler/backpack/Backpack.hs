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
import ShUnitId
import GhcMake

import UniqSet

import System.Exit
import Data.IORef
import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import System.FilePath
import Data.Version
import qualified Data.Traversable as T

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
        -- | The filename of the bkp file we're compiling
        bkp_filename :: FilePath,
        -- | Table of source units which we know how to compile
        bkp_table :: Map ComponentId LHsUnit,
        -- | When a package we are compiling includes another package
        -- which has not been compiled, we bump the level and compile
        -- that.
        bkp_level :: Int
    }

-- Blah, to get rid of the default instance for IOEnv
-- TODO: just make a proper new monad for BkpM, rather than use IOEnv
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
initBkpM :: FilePath -> [(ComponentId, LHsUnit)] -> BkpM a -> Ghc a
initBkpM file bkp m = do
    reifyGhc $ \session -> do
    let env = BkpEnv {
                    bkp_session = session,
                    bkp_table = Map.fromList bkp,
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
msgTopPackage :: (Int,Int) -> ComponentName -> BkpM ()
msgTopPackage (i,n) (ComponentName fs_pn) = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags
        $ showModuleIndex (i, n) ++ "Processing " ++ unpackFS fs_pn

-- | Message when we instantiate a Backpack unit.
msgUnitId :: UnitId -> BkpM ()
msgUnitId pk = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags
        $ "Instantiating " ++ renderWithStyle dflags (ppr pk) backpackStyle

-- | Message when we include a Backpack unit.
-- How to user-friendly print ComponentId?  Use ComponentName -> ComponentId
-- mapping.
msgInclude :: (Int,Int) -> ComponentId -> BkpM ()
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
    let dflags1 = dflags0 { thisComponentId =
                                if thisComponentId dflags0 == ComponentId (fsLit "")
                                then ComponentId (fsLit "main")
                                else thisComponentId dflags0
                                }
    src_opts <- liftIO $ getOptionsFromFile dflags1 src_filename
    (dflags, unhandled_flags, warns) <- liftIO $ parseDynamicFilePragma dflags1 src_opts
    modifySession (\hsc_env -> hsc_env {hsc_dflags = dflags})
    -- Cribbed from: preprocessFile / DriverPipeline
    liftIO $ checkProcessArgsResult dflags unhandled_flags
    liftIO $ handleFlagWarnings dflags warns
    -- TODO: something mumble preprocessing.  Call out to preprocess probably
    {-
    c <- liftIO $ readIORef (unitIdCache dflags)
    pprTrace "cache" (ppr c) $ return ()
    -}

    buf <- liftIO $ hGetStringBuffer src_filename
    let loc = mkRealSrcLoc (mkFastString src_filename) 1 1
        primary_name = ComponentName (fsLit (dropExtension src_filename))
    case unP parseBackpack (mkPState dflags buf loc) of
        PFailed span err -> do
            liftIO $ throwOneError (mkPlainErrMsg dflags span err)
        POk _ bkp -> do
            let computeComponentId pkg =
                    let comp_name = unLoc (hsunitName (unLoc pkg))
                        cid | comp_name == primary_name
                            = thisComponentId dflags
                            | otherwise
                            = addComponentName (thisComponentId dflags) comp_name
                    in cid
                comps = [ (computeComponentId u, u) | u <- bkp ]
            initBkpM src_filename comps $
                forM_ (zip [1..] comps) $ \(i, (cid, pkg)) -> do
                    let comp_name = unLoc (hsunitName (unLoc pkg))
                        is_primary = comp_name == primary_name
                    msgTopPackage (i,length bkp) comp_name
                    innerBkpM $ do
                        -- Figure out if we should type-check or
                        -- compile
                        sh_uid <- runShM $ shComputeUnitId cid pkg
                        -- This test is necessary to see if we're
                        -- compiling the primary for a specific instantiation
                        -- (See test bkpcabal01)
                        let insts = if not (Map.null (sigOf dflags))
                                            && is_primary
                                        then Map.toList (sigOf dflags)
                                        else shUnitIdInsts sh_uid
                        uid <- liftIO $ newUnitId dflags cid insts
                        case lookupPackage dflags uid of
                            -- Nothing to do
                            -- TODO: this could be wrong, if Cabal is
                            -- registering inplace and not unregister
                            -- before we attempt a recompile.  How can
                            -- we tell? Hmm...
                            Just _ -> return ()
                            -- Let's go!
                            Nothing -> do
                                fh <- liftIO $ unitIdFreeHoles dflags uid
                                if isEmptyUniqSet fh
                                    then if comp_name == ComponentName (fsLit "main")
                                            then compileExe pkg
                                            else compileUnit is_primary uid
                                    else typecheckUnit is_primary cid pkg

-- | Tiny enum for all types of Backpack operations we may do.
data SessionType = ExeSession | TcSession | CompSession
    deriving (Eq)

-- | Create a temporary Session to do some sort of type checking or
-- compilation.  This function is responsible for managing a few things,
-- including (1) deciding where the output files of the process go,
-- (2) configuring the module map, so we know what modules are in scope,
-- based on the 'IncludeGraph', and (3) setting up 'sigOf' properly.
withBkpSession :: UnitId        -- unit ID that we are going to tc/compile
               -> Map ModuleName Module
                                -- module mapping saying what is in scope
               -> Map ModuleName [Module]
                                -- module mapping for requirements
               -> SessionType   -- what kind of session are we doing
               -> BkpM a        -- actual action to run
               -> BkpM a
withBkpSession uid mod_map req_map session_type do_this = do
    dflags <- getDynFlags
    ComponentId cid_fs <- liftIO $ unitIdComponentId dflags uid
    insts <- liftIO $ unitIdInsts dflags uid
    let uid_str = unpackFS (unitIdFS uid)
        cid_str = unpackFS cid_fs
        -- There are multiple units in a single Backpack file, so we
        -- need to separate out the results in those cases.  Right now,
        -- we follow this hierarchy:
        --      $outputdir/$compid          --> typecheck results
        --      $outputdir/$compid/$unitid  --> compile results
        key_base p | Just f <- p dflags = f
                   | otherwise          = "out"
        -- We might want to detect if it's the "primary component" and
        -- then reduce the filepaths but for now...
        sub_comp p = p </> cid_str
        outdir p | CompSession <- session_type = sub_comp (key_base p) </> uid_str
                 | otherwise = sub_comp (key_base p)
    withTempSession (overHscDynFlags (\dflags ->
      -- If we're type-checking an indefinite package, we want to
      -- turn on interface writing.  However, if the user also
      -- explicitly passed in `-fno-code`, we DON'T want to write
      -- interfaces unless the user also asked for `-fwrite-interface`.
      (case session_type of
        -- Make sure to write interfaces when we are type-checking
        -- indefinite packages.
        TcSession | hscTarget dflags /= HscNothing
                  -> flip gopt_set Opt_WriteInterface
                  | otherwise -> id
        CompSession -> id
        ExeSession -> id) $
      dflags {
        hscTarget   = case session_type of
                        TcSession -> HscNothing
                        _ -> hscTarget dflags,
        thisPackage = uid,
        -- Setup all of the output directories according to our hierarchy
        objectDir   = Just (outdir objectDir),
        hiDir       = Just (outdir hiDir),
        stubDir     = Just (outdir stubDir),
        -- sigOf is sometimes used to trigger some alternate codepaths, so it's
        -- important to have this be something accurate.
        sigOf       = Map.fromList insts,
        -- Unset output-file for non exe builds
        outputFile  = if session_type == ExeSession
                        then outputFile dflags
                        else Nothing,
        -- Manually configure the module map, because it's too much of
        -- a pain to synthesize a series of package flags to do this
        packageModuleMap = mod_map,
        requirementsMap = req_map
      } )) $ do_this

withBkpExeSession :: IncludeGraph -> BkpM a -> BkpM a
withBkpExeSession include_graph do_this = do
    let mod_map = Map.unions (map is_inst_provides include_graph)
    withBkpSession mainUnitId mod_map Map.empty ExeSession do_this

-- | Create a temporary session for type-checking.
withBkpTcSession :: UnitId -> IncludeGraph -> BkpM a -> BkpM a
withBkpTcSession pk include_graph do_this = do
    old_eps <- getEpsGhc
    let mod_map = Map.unions (map is_inst_provides include_graph)
        req_map = Map.unionsWith (++) (map (Map.map return . is_inst_requires) include_graph)
    r <- withBkpSession pk mod_map req_map TcSession do_this
    -- Restore the old EPS from prior to typechecking.  This is because
    -- any indefinite TyThings we stored in the EPS may become invalid
    -- on future runs, if shaping changes.
    --
    -- Resetting the entire EPS to prior to the compilation is a pretty big
    -- hammer, but better than totally clearing the EPS.
    updateEpsGhc_ (const old_eps)
    return r

withBkpCompSession :: UnitId -> Map ModuleName Module -> Map ModuleName [Module] -> BkpM a -> BkpM a
withBkpCompSession uid mod_map req_map do_this =
    withBkpSession uid mod_map req_map CompSession do_this
    -- No setTargets nuttery

-- | Type checks a unit and adds it to the indefinite unit database.
typecheckUnit :: Bool {- is primary -} -> ComponentId -> LHsUnit -> BkpM ()
typecheckUnit is_primary cid pkg = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
        comp_name = unLoc (hsunitName (unLoc pkg))
    --  is_exe = comp_name == ComponentName (fsLit "main")
    shpk <- runShM $ shComputeUnitId cid pkg
    pk <- liftIO $ newUnitId' dflags shpk
    -- TODO skip this when there are no holes
    -- when (not is_exe) $ do
    -- Desugar into the include and module graphs we need
    include_graph <- runShM $ shIncludeGraph pk pkg
    ipkg <- withBkpTcSession pk include_graph $ do
        dflags <- getDynFlags
        mod_graph <- runShM $ shModGraph pk include_graph pkg

        -- Record the shape in the EPS, so that type-checking
        -- can see it.
        sh <- runShM $ shPackage pk include_graph mod_graph pkg
        sh_subst <- liftIO $ computeShapeSubst hsc_env sh
        updateEpsGhc_ (\eps -> eps { eps_shape = sh_subst } )

        msg <- mkBackpackMsg
        ok <- load' LoadAllTargets (Just msg) mod_graph
        when (failed ok) (liftIO $ exitWith (ExitFailure 1))
        let hi_dir = expectJust (panic "hiDir Backpack") $ hiDir dflags

        -- TODO duplicate
        let export_mod ms = (ms_mod_name ms, ms_mod ms)
            mods = [ export_mod ms | ms <- mod_graph, ms_hsc_src ms == HsSrcFile ]

        -- TODO: THIS IS WRONG
        -- The actual problem is that wired in packages like ghc-prim
        -- need to be "unwired" so that the resolution mechanism can handle
        -- them properly
        indef_deps <- liftIO  . mapM (generalizeHoleUnitId dflags . is_pkg_key) . filter (not . Map.null . is_requires) $ include_graph

        return InstalledPackageInfo {
            componentId = cid,
            -- Stub data
            abiHash = "",
            sourcePackageId = SourcePackageId (fsLit ""),
            packageName = PackageName (fsLit ""),
            packageVersion = makeVersion [0],
            componentName = comp_name,
            unitId = pk,
            exposedModules = mods,
            hiddenModules = [], -- TODO: doc only
            -- this is NOT the build plan
            depends = indef_deps,
            instantiatedDepends = map is_pkg_key include_graph,
            ldOptions = [],
            importDirs = [ hi_dir ],
            exposed = False,
            indefinite = True,
            -- not necessary for in-memory
            unitIdMap = [],
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

    -- NB: This is outside 'withBkpTcSession' so the update to 'Session'
    -- sticks.
    addPackage ipkg

compileUnit :: Bool {- is primary -} -> UnitId -> BkpM ()
compileUnit is_primary uid = do
    dflags <- getDynFlags
    cid <- liftIO $ unitIdComponentId dflags uid
    bkp_env <- getBkpEnv
    lunit <- case Map.lookup cid (bkp_table bkp_env) of
                -- TODO: exception throw
                Nothing -> panic "missing needed dependency, please compile me manually"
                Just lunit -> return lunit
    let comp_name = unLoc (hsunitName (unLoc lunit))
    msgUnitId uid
    include_graph <- runShM $ shIncludeGraph uid lunit
    let raw_deps = map is_pkg_key include_graph
    insts <- liftIO $ unitIdInsts dflags uid
    hsubst <- liftIO $ mkShHoleSubst dflags (listToUFM insts)
    deps <- liftIO $ mapM (renameHoleUnitId dflags hsubst) raw_deps
    let raw_provs = map is_inst_provides include_graph
        raw_reqs  = map is_inst_requires include_graph
    provs <- liftIO $ mapM (T.mapM (renameHoleModule dflags hsubst)) raw_provs
    reqs <- liftIO $ mapM (T.mapM (fmap (:[]) . renameHoleModule dflags hsubst)) raw_reqs
    let mod_map = Map.unions provs
        req_map = Map.unionsWith (++) reqs
    forM_ (zip [1..] deps) $
        compileInclude (length deps)
    (exposed, hi_dir, obj_files) <- withBkpCompSession uid mod_map req_map $ do
        mod_graph <- runShM $ shModGraph uid include_graph lunit
        msg <- mkBackpackMsg
        ok <- load' LoadAllTargets (Just msg) mod_graph
        when (failed ok) (liftIO $ exitWith (ExitFailure 1))

        hsc_env <- getSession
        let home_mod_infos = eltsUFM (hsc_HPT hsc_env)
            linkables = map (expectJust "bkp link".hm_linkable) $ filter ((==HsSrcFile) . mi_hsc_src . hm_iface) home_mod_infos
            getOfiles (LM _ _ us) = map nameOfObject (filter isObject us)
            obj_files = concatMap getOfiles linkables

        let export_mod ms = (ms_mod_name ms, ms_mod ms)
            mods = [ export_mod ms | ms <- mod_graph, ms_hsc_src ms == HsSrcFile ]
            exposed = mods

            hi_dir = expectJust (panic "Backpack hiDir") $ hiDir dflags

        return (exposed, hi_dir, obj_files)
    let pkginfo = InstalledPackageInfo {
            componentId = cid,
            abiHash = "",
            -- Stub data
            sourcePackageId = SourcePackageId (fsLit ""),
            packageName = PackageName (fsLit ""),
            packageVersion = makeVersion [0],
            componentName = comp_name,
            unitId = uid,
            exposedModules = exposed,
            hiddenModules = [], -- TODO: doc only
            -- 'depends' is important if we end up linking into a real
            -- executable
            instantiatedDepends = [],
            depends = deps
                       ++ [ moduleUnitId mod | (_, mod) <- insts],
            -- We didn't bother making an 'ar' archive which would be specified
            -- in 'hsLibraries', so instead we just add the object files to
            -- the linker options so they get linked in.  This is not such a
            -- good idea for -dynamic compilation; we should probably make
            -- the libraries in that case.
            ldOptions = obj_files,
            importDirs = [ hi_dir ],
            exposed = False,
            indefinite = False,
            -- not necessary for in-memory
            unitIdMap = [],
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
    addPackage pkginfo

{-
buildUnit :: SessionType -> UnitId -> LHsUnit -> BkpM ()
buildUnit session uid lunit = do
    dflags <- getDynFlags
    cid <- liftIO $ unitIdComponentId d
    return ()
    -}

compileExe :: LHsUnit -> BkpM ()
compileExe pkg = do
    msgUnitId mainUnitId
    include_graph <- runShM $ shIncludeGraph mainUnitId pkg
    forM_ (zip [1..] (map is_pkg_key include_graph)) $
        compileInclude (length include_graph)
    withBkpExeSession include_graph $ do
        mod_graph <- runShM $ shModGraph mainUnitId include_graph pkg
        msg <- mkBackpackMsg
        ok <- load' LoadAllTargets (Just msg) mod_graph
        when (failed ok) (liftIO $ exitWith (ExitFailure 1))

addPackage :: GhcMonad m => PackageConfig -> m ()
addPackage pkg = do
    dflags0 <- GHC.getSessionDynFlags
    case pkgDatabase dflags0 of
        Nothing -> panic "addPackage: called too early"
        -- TODO: give a more in-depth in-memory filename
        Just pkgs -> do let dflags = dflags0 { pkgDatabase = Just (pkgs ++ [("(in memory)", [pkg])]) }
                        _ <- GHC.setSessionDynFlags dflags
                        -- By this time, the global ref has probably already
                        -- been forced, in which case doing this isn't actually
                        -- going to do you any good.
                        -- dflags <- GHC.getSessionDynFlags
                        -- liftIO $ setUnsafeGlobalDynFlags dflags
                        return ()

compileInclude :: Int -> (Int, UnitId) -> BkpM ()
compileInclude n (i, pk) = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
    -- Check if we've compiled it already
    shpk <- liftIO $ lookupUnitId dflags pk
    let cid = shUnitIdComponentId shpk
    msgInclude (i, n) cid
    case lookupPackage dflags pk of
        Nothing -> do
            -- Nope, compile it
            innerBkpM $ compileUnit False pk
        Just _ -> return ()
