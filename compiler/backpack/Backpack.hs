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
        bkp_table :: Map ComponentId (LHsUnit HsComponentId),
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
initBkpM :: FilePath -> [LHsUnit HsComponentId] -> BkpM a -> Ghc a
initBkpM file bkp m = do
    reifyGhc $ \session -> do
    let env = BkpEnv {
                    bkp_session = session,
                    bkp_table = Map.fromList [(hsComponentId (unLoc (hsunitName (unLoc u))), u) | u <- bkp],
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
msgTopPackage :: (Int,Int) -> HsComponentId -> BkpM ()
msgTopPackage (i,n) (HsComponentId (PackageName fs_pn) _) = do
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
-- How to user-friendly print ComponentId?
msgInclude :: (Int,Int) -> ComponentId -> BkpM ()
msgInclude (i,n) cid = do
    dflags <- getDynFlags
    level <- getBkpLevel
    liftIO . backpackProgressMsg level dflags
        $ showModuleIndex (i, n) ++ "Including " ++
          renderWithStyle dflags (ppr cid) backpackStyle

-- ----------------------------------------------------------------------------
-- Run --backpack mode

type PackageNameMap a = Map PackageName a

-- For now, something really simple, since we're not actually going
-- to use this for anything
unitDefines :: LHsUnit PackageName -> (PackageName, HsComponentId)
unitDefines (L _ HsUnit{ hsunitName = L _ pn@(PackageName fs) })
    = (pn, HsComponentId pn (ComponentId fs))

packageNameMap :: [LHsUnit PackageName] -> PackageNameMap HsComponentId
packageNameMap units = Map.fromList (map unitDefines units)

renameHsUnits :: DynFlags -> PackageNameMap HsComponentId -> [LHsUnit PackageName] -> [LHsUnit HsComponentId]
renameHsUnits dflags m units = map renameHsUnit units
  where

    renamePackageName :: PackageName -> HsComponentId
    renamePackageName pn =
        case Map.lookup pn m of
            Nothing ->
                case lookupPackageName dflags pn of
                    Nothing -> error "no package name"
                    Just cid -> HsComponentId pn cid
            Just hscid -> hscid

    renameHsUnit :: LHsUnit PackageName -> LHsUnit HsComponentId
    renameHsUnit (L loc u) =
        L loc HsUnit {
            hsunitName = fmap renamePackageName (hsunitName u),
            hsunitExports = hsunitExports u,
            hsunitBody = map renameHsUnitDecl (hsunitBody u)
        }

    renameHsUnitDecl :: LHsUnitDecl PackageName -> LHsUnitDecl HsComponentId
    renameHsUnitDecl (L loc (DeclD a b c)) = L loc (DeclD a b c)
    renameHsUnitDecl (L loc (IncludeD idecl)) =
        L loc (IncludeD IncludeDecl {
            idInclude = fmap renamePackageName (idInclude idecl),
            idInclSpec = idInclSpec idecl
        })

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

    buf <- liftIO $ hGetStringBuffer src_filename
    let loc = mkRealSrcLoc (mkFastString src_filename) 1 1
        -- LOL this is terrible
        primary_name = ComponentId (fsLit (dropExtension src_filename))
    case unP parseBackpack (mkPState dflags buf loc) of
        PFailed span err -> do
            liftIO $ throwOneError (mkPlainErrMsg dflags span err)
        POk _ pkgname_bkp -> do
            -- OK, so we have an LHsUnit PackageName, but we want an
            -- LHsUnit ComponentId.  So let's rename it.
            --
            -- NB: If we top-sort here you can put these in whatever order
            -- you want, but includes have to be acyclic!
            let bkp = renameHsUnits dflags (packageNameMap pkgname_bkp) pkgname_bkp
            initBkpM src_filename bkp $
                forM_ (zip [1..] bkp) $ \(i, lunit) -> do
                    let comp_name = unLoc (hsunitName (unLoc lunit))
                        is_primary = hsComponentId comp_name == primary_name
                    msgTopPackage (i,length bkp) comp_name
                    innerBkpM $ do
                        -- Figure out if we should type-check or
                        -- compile.  This is the "pre-shaping" pass
                        -- described in the paper.
                        uid0 <- runShM $ shComputeUnitId lunit
                        -- This test is necessary to see if we're
                        -- compiling the primary for a specific instantiation
                        -- (See test bkpcabal01)
                        let insts = if not (Map.null (sigOf dflags))
                                            && is_primary
                                        then Map.toList (sigOf dflags)
                                        else unitIdInsts uid0
                            uid = unsafeNewUnitId (unitIdComponentId uid0) insts
                        if isEmptyUniqSet (unitIdFreeHoles uid)
                            then if hsComponentId comp_name == ComponentId (fsLit "main")
                                    then compileExe lunit
                                    else compileUnit uid
                            else typecheckUnit (hsComponentId comp_name)

-- | Tiny enum for all types of Backpack operations we may do.
data SessionType = ExeSession | TcSession | CompSession
    deriving (Eq)

-- | Create a temporary Session to do some sort of type checking or
-- compilation.  This function is responsible for managing a few things,
-- including (1) deciding where the output files of the process go,
-- (2) configuring the module map, so we know what modules are in scope,
-- based on the 'IncludeGraph', and (3) setting up 'sigOf' properly.
withBkpSession :: UnitId        -- unit ID that we are going to tc/compile
               -> IncludeGraph
               -> Map ModuleName Module
                                -- module mapping saying what is in scope
               -> Map ModuleName [Module]
                                -- module mapping for requirements
               -> SessionType   -- what kind of session are we doing
               -> BkpM a        -- actual action to run
               -> BkpM a
withBkpSession uid include_graph mod_map req_map session_type do_this = do
    dflags <- getDynFlags
    let cid@(ComponentId cid_fs) = unitIdComponentId uid
        is_primary = cid == thisComponentId dflags
        insts = unitIdInsts uid
        uid_str = unpackFS (unitIdFS uid)
        cid_str = unpackFS cid_fs
        -- There are multiple units in a single Backpack file, so we
        -- need to separate out the results in those cases.  Right now,
        -- we follow this hierarchy:
        --      $outputdir/$compid          --> typecheck results
        --      $outputdir/$compid/$unitid  --> compile results
        key_base p | Just f <- p dflags = f
                   | otherwise          = "."
        sub_comp p | is_primary = p
                   | otherwise = p </> cid_str
        outdir p | CompSession <- session_type
                 -- Special case when package is definite
                 , not (null insts) = sub_comp (key_base p) </> uid_str
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
        -- Synthesized the flags
        packageFlags = packageFlags dflags ++ map (\is ->
            ExposePackage
                (showSDoc dflags (text "-unit-id" <+> ppr (unwireUnitId dflags (is_uid is)) <+> ppr (is_renaming is)))
                (UnitIdArg (unwireUnitId dflags (is_uid is))) (is_renaming is)) include_graph,
        -- Manually configure the module map, because it's too much of
        -- a pain to synthesize a series of package flags to do this
        -- packageModuleMap = mod_map,
        requirementsMap = req_map
      } )) $ do
        dflags <- getSessionDynFlags
        setSessionDynFlags dflags
        do_this

withBkpExeSession :: IncludeGraph -> BkpM a -> BkpM a
withBkpExeSession include_graph do_this = do
    let mod_map = Map.unions (map is_inst_provides include_graph)
    withBkpSession mainUnitId include_graph mod_map Map.empty ExeSession do_this

getSource :: ComponentId -> BkpM (LHsUnit HsComponentId)
getSource cid = do
    bkp_env <- getBkpEnv
    case Map.lookup cid (bkp_table bkp_env) of
        -- TODO: exception throw
        Nothing -> panic "missing needed dependency, please compile me manually"
        Just lunit -> return lunit

typecheckUnit :: ComponentId -> BkpM ()
typecheckUnit cid = do
    lunit <- getSource cid
    -- TODO: Computing this twice is a little goofy
    uid <- runShM $ shComputeUnitId lunit
    buildUnit TcSession uid lunit

compileUnit :: UnitId -> BkpM ()
compileUnit uid = do
    -- Let everyone know we're building this unit ID
    msgUnitId uid
    lunit <- getSource (unitIdComponentId uid)
    buildUnit CompSession uid lunit

buildUnit :: SessionType -> UnitId -> LHsUnit HsComponentId -> BkpM ()
buildUnit session uid lunit = do
    -- Analyze the dependency structure
    include_graph <- runShM $ shIncludeGraph uid lunit

    -- Determine the dependencies of this unit.
    let raw_deps = map is_uid include_graph

    -- The compilation dependencies are just the appropriately filled
    -- in unit IDs which must be compiled before we can compile.
    --
    -- TODO: it seems better if we preemptively do this, and use
    -- this as the "shadow set" of unit IDs we're going to do.
    let insts = unitIdInsts uid
        hsubst = listToUFM insts
        deps = map (renameHoleUnitId hsubst) raw_deps

    -- Build dependencies
    case session of
        TcSession -> return ()
        _ -> forM_ (zip [1..] deps) $ \(i, dep) ->
                compileInclude (length deps) (i, dep)

    -- Compute the in-scope provisions and requirements
    let raw_provs = map is_inst_provides include_graph
        raw_reqs  = map is_inst_requires include_graph
        provs = map (fmap (renameHoleModule hsubst)) raw_provs
        reqs  = map (fmap ((:[]) . renameHoleModule hsubst)) raw_reqs
        mod_map = Map.unions provs
        req_map = Map.unionsWith (++) reqs

    mb_old_eps <- case session of
                    TcSession -> fmap Just getEpsGhc
                    _ -> return Nothing

    conf <- withBkpSession uid include_graph mod_map req_map session $ do
        dflags <- getDynFlags
        mod_graph <- runShM $ shModGraph uid lunit
        -- pprTrace "mod_graph" (ppr mod_graph) $ return ()

        {-
        hsc_env <- getSession
        case session of
            TcSession -> do
                -- TODO: do this lazily as we process modules
                sh <- runShM $ shPackage uid include_graph mod_graph lunit
                sh_subst <- liftIO $ computeShapeSubst hsc_env sh
                updateEpsGhc_ (\eps -> eps { eps_shape = sh_subst } )
            _ -> return ()
            -}

        msg <- mkBackpackMsg
        ok <- load' LoadAllTargets (Just msg) mod_graph
        when (failed ok) (liftIO $ exitWith (ExitFailure 1))

        let hi_dir = expectJust (panic "hiDir Backpack") $ hiDir dflags
            -- TODO: doesn't handle export renaming
            export_mod ms = (ms_mod_name ms, ms_mod ms)
            mods = [ export_mod ms | ms <- mod_graph, ms_hsc_src ms == HsSrcFile ]

        -- Compile relevant only
        hsc_env <- getSession
        let home_mod_infos = eltsUFM (hsc_HPT hsc_env)
            linkables = map (expectJust "bkp link" . hm_linkable)
                      . filter ((==HsSrcFile) . mi_hsc_src . hm_iface)
                      $ home_mod_infos
            getOfiles (LM _ _ us) = map nameOfObject (filter isObject us)
            obj_files = concatMap getOfiles linkables

        let indef_deps =
                      map (unwireUnitId dflags . generalizeHoleUnitId . is_uid)
                    -- TODO: THIS IS WRONG
                    -- The actual problem is that wired in packages like
                    -- ghc-prim need to be "unwired" so that the resolution
                    -- mechanism can handle them properly
                    $ include_graph
            cand_compat_pn = PackageName (case unitIdComponentId uid of
                                                    ComponentId fs -> fs)
            compat_pn = case session of
                            TcSession -> cand_compat_pn
                            _ | [] <- unitIdInsts uid -> cand_compat_pn
                            -- Cabal would munge this but there's no need to
                            -- access these
                              | otherwise -> PackageName (fsLit "")

        return InstalledPackageInfo {
            -- Stub data
            abiHash = "",
            sourcePackageId = SourcePackageId (fsLit ""),
            packageName = compat_pn,
            packageVersion = makeVersion [0],
            unitId = uid,
            -- Slight inefficiency here haha
            exposedModules = map (\(m,n) -> (m,Just n)) mods,
            hiddenModules = [], -- TODO: doc only
            -- this is NOT the build plan
            depends = case session of
                        TcSession -> indef_deps
                        _ -> map (unwireUnitId dflags)
                                $ deps ++ [ moduleUnitId mod
                                          | (_, mod) <- insts
                                          , not (isHoleModule mod) ],
            -- instantiatedDepends = deps,
            ldOptions = case session of
                            TcSession -> []
                            _ -> obj_files,
            importDirs = [ hi_dir ],
            exposed = False,
            {-
            indefinite = case session of
                            TcSession -> True
                            _ -> False,
                            -}
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


    addPackage conf
    case mb_old_eps of
        Just old_eps -> updateEpsGhc_ (const old_eps)
        _ -> return ()

compileExe :: LHsUnit HsComponentId -> BkpM ()
compileExe pkg = do
    msgUnitId mainUnitId
    include_graph <- runShM $ shIncludeGraph mainUnitId pkg
    forM_ (zip [1..] (map is_uid include_graph)) $
        compileInclude (length include_graph)
    withBkpExeSession include_graph $ do
        mod_graph <- runShM $ shModGraph mainUnitId pkg
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
compileInclude n (i, uid) = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
    -- Check if we've compiled it already
    let cid = unitIdComponentId uid
    msgInclude (i, n) cid
    -- TODO: this recompilation avoidance should distinguish between
    -- local in-memory entries (OK to avoid recompile) and entries
    -- from the database (MUST recompile).
    --
    -- This is a bit tricky to tickle because you need
    -- (1) a local unit, and (2) to have installed it to the database.
    -- But bkpcabal01's got it!
    --
    -- This is also a bit annoying because technically these should
    -- SHADOW the database.  Waaaay bad juju if you compile depending
    -- on an older version of something.
    case lookupPackage dflags uid of
        Nothing -> do
            -- Nope, compile it
            innerBkpM $ compileUnit uid
        Just _ -> return ()

{-
-- | Given a 'ComponentId', create a new 'ComponentId' for a private
-- subcomponent named 'ComponentName' contained within it.
addComponentName :: ComponentId -> ComponentName -> ComponentId
addComponentName (ComponentId cid) (ComponentName n) =
    ComponentId (concatFS [cid, fsLit "-", n])
    -}
