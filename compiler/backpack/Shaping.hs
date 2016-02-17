{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE CPP #-}
module Shaping (
    -- * Shaping monad
    initShM,
    ShM,
    -- * Shaping
    shPackage,
    shComputeUnitId,
    shIncludeGraph,
    shModGraph,
    -- * IR bits
    IncludeSummary(..), IncludeGraph,
) where

#include "HsVersions.h"

import HscMain
import BackpackSyn
import ShUnify
import Shape

import GhcMonad
import SrcLoc
import Outputable
import HscTypes
import Module
import PackageConfig
import DynFlags
import UniqFM
import ErrUtils
import Maybes
import Avail
import RnSource
import TcRnDriver
import Name
import PrelNames

import BasicTypes hiding (SuccessFlag(..))
import Digraph
import HsSyn
import IOEnv
import RdrName
import Packages
import Finder
import HeaderInfo
import RnNames
import NameEnv
import TcRnMonad
import Bag
import MkIface
import UniqSet
import Util
import FastString
import LoadIface
import GhcMake
import MergeIface

import qualified GHC.LanguageExtensions as LangExt

import System.FilePath
import Data.List
import Data.IORef
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Traversable as T
import qualified Data.Foldable as F

{-
************************************************************************
*                                                                      *
                        IR
*                                                                      *
************************************************************************
-}

-- | An include declaration which can be topologically sorted.
data IncludeSummary = IncludeSummary {
        is_loc :: SrcSpan,
        -- The INSTANTIATED package key for this include.
        -- So if we "include p requires (H)" and we happen to
        -- know that H is q:H, then is_uid is p(q:H).
        is_uid :: UnitId,
        -- is_provides and is_requires record the RENAMED but
        -- UN-INSTANTIATED names for modules.  So with
        -- "include p requires (H)", the recorded requirement
        -- is always H -> p(HOLE:H):H and not H -> p(q:H):H
        -- (even if we know it was instantiated that way.)
        -- The point is that this lets us know how to read
        -- in interfaces, and then we can instantiate with
        -- the actual implementation ourselves.
        is_provides :: Map ModuleName Module,
        is_requires :: Map ModuleName Module,
        -- When actually compiling, we want the real RENAMED
        -- and INSTANTIATED provides/requires.  So they're saved here.
        is_inst_provides :: Map ModuleName Module,
        is_inst_requires :: Map ModuleName Module
    }

-- Note [is_provides versus is_inst_provides]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Suppose we are compiling the unit:
--
--      include m-impl (M)
--      include p requires (H as M)
--
-- Through pre-shaping, we know that we will need modules from
-- p(H -> m-impl:M).  However, prior to shaping, we do not actually
-- know that this substitution is VALID: if m-impl:M doesn't implement
-- all the requirements of p, we need to give an error.  Furthermore,
-- unification may occur when we do this (say M reexports something from
-- signature A), so the process of checking that the substitution is
-- valid has side-effects.
--
-- We do have one codepath which can check this: computeInterface (rnInterface),
-- which is ordinary used to implement lazy interface loading during type
-- checking.  But: (1) rnInterface does too much work; we just want to look at
-- mi_exports and not the entire interface, and (2) if something is missing,
-- computeInterface has no good way of reporting an error.  So, for
-- computeInterface on a module assumes that the instantiation is *good*,
-- and we need a different strategy.
--
-- A different strategy is cunningly use computeInterface ONLY to handle
-- renaming due to requirements, and then merge the names ourselves after
-- the fact.  Thus, is_provides and is_requires have the UNINSTANTIATED
-- (according to the source unit) modules which ARE renamed according to
-- the specification.  We can load these interfaces, which is guaranteed
-- to work, and then check for everything being good.  Once this check
-- is complete, we are allowed to actually load the interfaces referred
-- to by is_inst_provides, which we otherwise would not have known about.

instance Outputable IncludeSummary where
    ppr IncludeSummary{ is_uid = pk, is_inst_provides = provs, is_inst_requires = reqs }
        = text "include" <+> ppr pk <+> ppr provs <+> text "requires" <+> ppr reqs

type IncludeGraph = [IncludeSummary]

{-
************************************************************************
*                                                                      *
                        Include planning
*                                                                      *
************************************************************************
-}

-- The strategy is staged: we first compute the include graph, then
-- we compute the module graph.

-- | This function takes a 'UnitId' and an source 'LHsUnit' and computes the
-- list of 'IncludeSummary's specifying what external specific instantiated
-- units are depended upon by this unit.
shIncludeGraph :: UnitId -> LHsUnit HsComponentId -> ShM [IncludeSummary]
shIncludeGraph uid lpkg = setPackageSh lpkg . setUnitIdSh uid $ do
    -- Extract out all the includes from the package description,
    -- processing any renamings so we have an up-to-date picture
    -- about what an include provides and requires.  However, we
    -- DON'T yet know how the includes are going to be instantiated.
    let decls = hsunitBody (unLoc lpkg)
        get_include (L loc (IncludeD decl)) = Just (L loc decl)
        get_include _ = Nothing
        incls = mapMaybe get_include decls
    graph0 <- mapM summariseInclude incls
    -- Let's set up the unification process.  (TODO: maybe do this
    -- during summariseInclude)
    fs <- liftIO $ newIORef 0
    hmap <- liftIO $ newIORef Map.empty
    unifs <- liftIO . forM graph0 $ \is0 -> do
        provs_u <- T.mapM (convertModule' fs hmap emptyMuEnv) (is_provides is0)
        reqs_u  <- T.mapM (convertModule' fs hmap emptyMuEnv) (is_requires is0)
        uid_u <- convertUnitId' fs hmap emptyMuEnv (is_uid is0)
        return (provs_u, reqs_u, uid_u, is0)
    -- OK, now successively unify everything.
    -- (We'll do the trick of using intersectionWith to unify, and then
    -- just do a plain old union)
    holeMap <- liftIO $ readIORef hmap
    let go provs_all (provs_u, _, uid_u, _) = do
            u0 <- convertUnitIdU uid_u
            F.sequenceA_ (Map.intersectionWith unifyModule provs_u holeMap)
            F.sequenceA_ (Map.intersectionWith unifyModule provs_u provs_all)
            a <- T.mapM convertModuleU provs_all
            c <- T.mapM convertModuleU provs_u
            h <- T.mapM convertModuleU holeMap
            u <- convertUnitIdU uid_u
            -- pprTrace "go" (ppr a $$ ppr c $$ ppr h $$ ppr u0 $$ ppr u) $ return ()
            return (Map.union provs_all provs_u)
    _ <- liftIO $ foldM go Map.empty unifs

    -- OK, feed it back into the graph
    graph1 <- liftIO . forM unifs $ \(provs_u, reqs_u, uid_u, is0) -> do
        provs <- T.mapM convertModuleU provs_u
        reqs <- T.mapM convertModuleU reqs_u
        uid <- convertUnitIdU uid_u
        return is0 { is_inst_provides = provs
                   , is_inst_requires = reqs
                   , is_uid = uid
                   }
    --shDump (ppr graph1)

    -- Now top-sort
    let top_graph = topSortIncludeGraph graph1
    -- TODO: Compute loop-breakers to get rid of cycles
        unroll (AcyclicSCC is) = return is
        unroll _ = error "cycles not supported"
    graph <- mapM unroll top_graph

    {-
    -- This was the old algorithm
    {-
    -- If we want includes to be instantiatable by locally defined
    -- modules, we need to also consider local module definitions in
    -- our substitution.
    let get_decl (L _ (DeclD ModuleD (L _ modname) _mb_hsmod)) = do
          Just (modname, mkModule uid modname)
        get_decl _ = Nothing
        mods = catMaybes (map get_decl decls)
    -}
    -- Based on the 'UnitId', compute an initial substitution to apply
    -- to the includes.  If we're just type-checking, this will start
    -- off as the identity substitution.
    let hsubst0 = unitIdHoleSubst uid
    -- Processing the include graph in topological order, "fill" requirements
    -- by using the substitution, updating the summary, and then add
    -- provisions as things that can be used by later includes in the topsort.
    let go (gr, hsubst) (AcyclicSCC is0) = -- loc?
          -- Substitute the provisions and unit ID
          let rn_provs = fmap (renameHoleModule hsubst) (is_provides is0)
              rn_reqs  = fmap (renameHoleModule hsubst) (is_requires is0)
              uid = renameHoleUnitId hsubst (is_uid is0)
              is = is0 { is_inst_provides = rn_provs
                       , is_inst_requires = rn_reqs
                       , is_uid = uid }
              -- Update the substitution with the provisions
              hsubst' = addListToHoleSubst hsubst (Map.toList rn_provs)
              -- TODO: assert fixpoint not necessary
          in return (is:gr, hsubst')
        go (gr, hsubst) (CyclicSCC iss) = error "cycles not supported"
    let top_graph = topSortIncludeGraph graph0
    (rev_graph, _) <- foldM go ([], hsubst0) top_graph
    let graph = reverse rev_graph
    -}
    -- shDump (ppr graph)
    return graph

-- | Convert an 'IncludeDecl' into an 'IncludeSummary', applying any
-- renaming to update the provided and required modules.  This does
-- NOT substitute holes; that is done later in 'shIncludeGraph'.
summariseInclude :: Located (IncludeDecl HsComponentId) -> ShM IncludeSummary
summariseInclude (L loc IncludeDecl { idInclude = L _ name
                                          , idInclSpec = mb_inclspec }) = do
    ipkg <- lookupUnit (hsComponentId name)
    let hsubst = mkInclSpecSubst mb_inclspec
        provs0 = fmap (renameHoleModule hsubst) (shcProvides ipkg)
        renameProvides Nothing
            = return provs0
        renameProvides (Just (L _ InclSpec { isProvides = Nothing }))
            = return provs0
        renameProvides (Just (L _ InclSpec { isProvides = Just rns }))
            = foldM go Map.empty rns
          where go new (L _ rn)
                    | Just m <- Map.lookup (renameFrom rn) provs0
                    = return (Map.insert (renameTo rn) m new)
                    | otherwise = panic "PROPER ERROR HERE"
    provs <- renameProvides mb_inclspec

    let uid = renameHoleUnitId hsubst (shcUnitId ipkg)
    return IncludeSummary {
        is_loc = loc,
        -- Not substituted yet, we will do this shortly
        is_uid = uid,
        is_provides = provs,
        -- These get filled in later
        is_inst_provides = panic "unknown is_inst_provides",
        is_inst_requires = panic "unknown is_inst_requires",
        is_requires = Map.fromList [(moduleName new, mkModule uid orig) | (orig, new) <- unitIdInsts uid, isHoleModule new ]
        }

mkInclSpecSubst :: Maybe (Located InclSpec) -> ShHoleSubst
mkInclSpecSubst Nothing = emptyUFM
mkInclSpecSubst (Just (L _ InclSpec { isRequires = rns })) =
    foldl' (\m (L _ rn) ->
           addToUFM m
               (renameFrom rn)
               (mkModule holeUnitId
                         (renameTo rn)))
       emptyUFM rns

type IncludeNode = (IncludeSummary, Int, [Int])
includeNodeKey :: IncludeNode -> Int
includeNodeKey (_, k, _) = k
includeNodeSummary :: IncludeNode -> IncludeSummary
includeNodeSummary (s, _, _) = s

topSortIncludeGraph :: IncludeGraph -> [SCC IncludeSummary]
topSortIncludeGraph include_graph
    = map (fmap includeNodeSummary) $ stronglyConnCompG graph
    where
      graph = includeGraphNodes include_graph

includeGraphNodes :: IncludeGraph -> Graph IncludeNode
includeGraphNodes summaries = graphFromEdgedVertices nodes
  where
    numbered_summaries = zip summaries [1..]

    node_map :: Map ModuleName IncludeNode
    node_map = Map.fromList [ (n, node)
                            | node@(s, _, _) <- nodes
                            , n <- Map.keys (is_provides s) ]

    lookup_key mod = fmap includeNodeKey (Map.lookup mod node_map)

    -- TODO: This doesn't work quite right when multiple packages provide the same thing
    nodes = [ (s, key, out_keys)
            | (s, key) <- numbered_summaries
            , let out_keys = mapMaybe lookup_key (Map.keys (is_requires s)) ]


{-
************************************************************************
*                                                                      *
                        Module planning
*                                                                      *
************************************************************************
-}

-- | This is our version of GhcMake.downsweep, but with a few modifications:
--
--  1. Every module is required to be mentioned, so we don't do any funny
--     business with targets or recursively grabbing dependencies.  (We
--     could support this in principle).
--  2. We support inline modules, whose summary we have to synthesize ourself.
--
-- We don't bother trying to support GhcMake for now, it's more trouble
-- than it's worth for inline modules.
shModGraph :: UnitId -> LHsUnit HsComponentId -> ShM [ModSummary]
shModGraph uid lpkg = setPackageSh lpkg . setUnitIdSh uid $ do
    let decls = hsunitBody (unLoc lpkg)
    dflags <- getDynFlags

    --  1. Create a HsSrcFile/HsigFile summary for every
    --  explicitly mentioned module/signature.
    --  TODO: chase deps, so that we don't have to assume all
    --  modules/signatures are mentioned.
    let get_decl (L _ (DeclD dt lmodname mb_hsmod)) = do
          let hsc_src = case dt of
                          ModuleD    -> HsSrcFile
                          SignatureD -> HsigFile
          Just `fmap` summariseDecl dflags hsc_src lmodname mb_hsmod
        get_decl _ = return Nothing
    nodes <- catMaybes `fmap` mapM get_decl decls

    --  2. For each hole which does not already have an hsig file,
    --  create an "empty" hsig file to induce compilation for the
    --  requirement.
    let node_map = Map.fromList [ ((ms_mod_name n, ms_hsc_src n == HsigFile), n)
                                | n <- nodes ]
    req_nodes <- fmap catMaybes . forM (unitIdInsts uid) $ \(mod_name, _) ->
        let has_local = Map.member (mod_name, True) node_map
        in if has_local
            then return Nothing
            else fmap Just $ summariseRequirement dflags mod_name

    -- 3. Return the kaboodle
    return (nodes ++ req_nodes)

summariseRequirement :: DynFlags -> ModuleName -> ShM ModSummary
summariseRequirement dflags mod_name = do
    hsc_env <- getTopEnv
    -- TODO: don't base this lookup on ComponentId
    PackageName pn_fs <- fmap (hsPackageName . shg_name) getGblEnv
    location <- liftIO $ mkHomeModLocation2 dflags mod_name
                 (unpackFS pn_fs </> moduleNameSlashes mod_name) "hsig"

    env <- getGblEnv
    time <- liftIO $ getModificationUTCTime (shg_filename env)
    hi_timestamp <- liftIO $ modificationTimeIfExists (ml_hi_file location)

    mod <- liftIO $ addHomeModuleToFinder hsc_env mod_name location

    loc <- getSrcSpanSh
    extra_sig_imports <- liftIO $ findExtraSigImports hsc_env HsigFile mod_name

    return ModSummary {
        ms_mod = mod,
        ms_hsc_src = HsigFile,
        ms_location = location,
        ms_hs_date = time,
        ms_obj_date = Nothing,
        ms_iface_date = hi_timestamp,
        ms_srcimps = [],
        ms_textual_imps = extra_sig_imports,
        ms_parsed_mod = Just (HsParsedModule {
                hpm_module = L loc (HsModule {
                        hsmodName = Just (L loc mod_name),
                        hsmodExports = Nothing,
                        hsmodImports = [],
                        hsmodDecls = [],
                        hsmodDeprecMessage = Nothing,
                        hsmodHaddockModHeader = Nothing
                    }),
                hpm_src_files = [],
                hpm_annotations = (Map.empty, Map.empty)
            }),
        ms_hspp_file = "", -- none, it came inline
        ms_hspp_opts = dflags,
        ms_hspp_buf = Nothing
        }

summariseDecl :: DynFlags
              -> HscSource
              -> Located ModuleName
              -> Maybe (Located (HsModule RdrName))
              -> ShM ModSummary
summariseDecl dflags hsc_src (L _ modname) (Just hsmod) = hsModuleToModSummary dflags hsc_src modname hsmod
summariseDecl _dflags hsc_src lmodname@(L _ modname) Nothing
    = do hsc_env <- getTopEnv
         -- TODO: this looks for modules in the wrong place
         r <- liftIO $ summariseModule hsc_env
                         Map.empty -- GHC API recomp not supported
                         (hscSourceToIsBoot hsc_src)
                         lmodname
                         True -- Target lets you disallow, but not here
                         Nothing -- GHC API buffer support not supported
                         [] -- No exclusions
         case r of
            Nothing -> failSh (text "module" <+> ppr modname <+> text "is a package module")
            Just (Left err) -> reportErrorSh err >> failM
            Just (Right summary) -> return summary

-- | Up until now, GHC has assumed a single compilation target per source file.
-- Backpack files with inline modules break this model, since a single file
-- may generate multiple output files.  How do we decide to name these files?
-- Should there only be one output file? This function our current heuristic,
-- which is we make a "fake" module and use that.
hsModuleToModSummary :: DynFlags
                     -> HscSource
                     -> ModuleName
                     -> Located (HsModule RdrName)
                     -> ShM ModSummary
hsModuleToModSummary dflags hsc_src modname
                     hsmod@(L loc (HsModule _ _ imps _ _ _)) = do
    -- Sort of the same deal as in DriverPipeline's getLocation
    -- Use the PACKAGE NAME to find the location
    PackageName unit_fs <- fmap (hsPackageName . shg_name) getGblEnv
    hsc_env <- getTopEnv
    -- Unfortunately, we have to define a "fake" location in
    -- order to appease the various code which uses the file
    -- name to figure out where to put, e.g. object files.
    -- To add insult to injury, we don't even actually use
    -- these filenames to figure out where the hi files go.
    -- A travesty!  Fix this some day...
    location0 <- liftIO $ mkHomeModLocation2 dflags modname
                             (unpackFS unit_fs </>
                              moduleNameSlashes modname)
                              (case hsc_src of
                                HsigFile -> "hsig"
                                HsBootFile -> "hs-boot"
                                HsSrcFile -> "hs")
    -- DANGEROUS: bootifying can POISON the module finder cache
    let location = case hsc_src of
                        HsBootFile -> addBootSuffixLocn location0
                        _ -> location0
    -- This duplicates a pile of logic in GhcMake
    env <- getGblEnv
    time <- liftIO $ getModificationUTCTime (shg_filename env)
    hi_timestamp <- liftIO $ modificationTimeIfExists (ml_hi_file location)

    -- Also copied from 'getImports'
    let (src_idecls, ord_idecls) = partition (ideclSource.unLoc) imps

             -- GHC.Prim doesn't exist physically, so don't go looking for it.
        ordinary_imps = filter ((/= moduleName gHC_PRIM) . unLoc . ideclName . unLoc)
                               ord_idecls

        implicit_prelude = xopt LangExt.ImplicitPrelude dflags
        implicit_imports = mkPrelImports modname loc
                                         implicit_prelude imps
        convImport (L _ i) = (fmap sl_fs (ideclPkgQual i), ideclName i)

    extra_sig_imports <- liftIO $ findExtraSigImports hsc_env hsc_src modname

    -- So that Finder can find it, even though it doesn't exist...
    this_mod <- liftIO $ addHomeModuleToFinder hsc_env modname location
    return ModSummary {
            ms_mod = this_mod,
            ms_hsc_src = hsc_src,
            ms_location = location,
            ms_hspp_file = (case hiDir dflags of
                            Nothing -> ""
                            Just d -> d) </> ".." </> moduleNameSlashes modname <.> "hi",
            -- VERY IMPORTANT, because tc will ignore ModSummary this_mod
            ms_hspp_opts = dflags {
                thisPackage = moduleUnitId this_mod
                },
            ms_hspp_buf = Nothing,
            ms_srcimps = map convImport src_idecls,
            ms_textual_imps = map convImport (implicit_imports ++ ordinary_imps)
                           -- We have to do something special here:
                           -- due to merging, requirements may end up with
                           -- extra imports
                           ++ extra_sig_imports,
            -- This is our hack to get the parse tree to the right spot
            ms_parsed_mod = Just (HsParsedModule {
                    hpm_module = hsmod,
                    hpm_src_files = [], -- TODO if we preprocessed it
                    hpm_annotations = (Map.empty, Map.empty) -- BOGUS
                }),
            ms_hs_date = time,
            ms_obj_date = Nothing, -- TODO do this, but problem: hi_timestamp is BOGUS
            ms_iface_date = hi_timestamp
        }

findExtraSigImports hsc_env hsc_src modname = do
    -- Gotta work hard.
    -- TODO: but only when I'm type-checking
    let dflags = hsc_dflags hsc_env
        reqmap = requirementsMap dflags
    extra_requirements <-
      case hsc_src of
        HsigFile | Just reqs <- Map.lookup modname reqmap -> do
            all_deps <- forM reqs $ \(req :: Module) -> do
                -- NB: we NEED the transitive closure of local imports!!!
                (deps, _) <- initIfaceCheck hsc_env . withException $
                            (computeDependencies (text "requirement deps" <+> ppr modname)
                            False req)
                -- Now we must reflect upon the substitution in req
                -- in order to determine the meaning of the dependencies.
                let hmap = Map.fromList (unitIdInsts (moduleUnitId req))
                -- m -> M
                --  means that if we see an m in the dep list, it is a hole.
                --  Consequently, we have a dependency on M
                let go (_, True) = [] -- ignore boots
                    go (mod_name, False)
                        | Just mod <- Map.lookup mod_name hmap
                        = uniqSetToList (moduleFreeHoles mod)
                        | otherwise
                        = [] -- not a requirement
                return (concatMap go (dep_mods deps))
            return (concat all_deps)
        _ -> return []

    return [ (Nothing, noLoc mod_name) | mod_name <- extra_requirements ]

-- resolveImport :: ModuleName -> 

-- To get truly accurate dependency information, we need to
-- determine what the requirements of every external import are.
importRequirements hsc_env mod_name = do
    let dflags = hsc_dflags hsc_env
    found <- findImportedModule hsc_env mod_name Nothing
    case found of
        Found _ mod -> do
            -- OK, this is pretty good, now we just consult the
            -- free hole variables to find out what it requires, assuming
            -- that it's an external one (if it's internal one
            -- the natural import graph will handle it)
            if thisPackage dflags == moduleUnitId mod
                then return []
                else return (uniqSetToList (unitIdFreeHoles (moduleUnitId mod)))
        _ -> return []

{-
************************************************************************
*                                                                      *
                        External shapes
*                                                                      *
************************************************************************
-}

-- Just a summary of shape information, not quite the shape but you
-- can calculate it based on the 'Module's that are available.
data ShapeConfig
    = ShapeConfig {
        shcUnitId :: UnitId,
        shcProvides :: Map ModuleName Module,
        shcRequires :: Map ModuleName Module
    }

-- summariseInclude (provides and shpackagekey)
-- lookupPackageShape (shape, package key)
-- preshape (preshape)
lookupIndefUnitId :: ComponentId -> ShM (Maybe ShapeConfig)
lookupIndefUnitId cid = do
    dflags <- getDynFlags
    case lookupComponentId dflags cid of
        Just cfg -> do
            return $ Just
            -- TODO: This would be bad if the UnitId is not serialized correctly
                ShapeConfig { shcUnitId = packageConfigId cfg
                            , shcProvides = Map.fromList
                                                [ (mod_name, fromMaybe (mkModule (packageConfigId cfg) mod_name) mb_mod)
                                                | (mod_name, mb_mod) <- exposedModules cfg ]
                            -- TODO: is this right?  Should be OK
                            , shcRequires = Map.fromList (unitIdInsts (packageConfigId cfg))
                            }
        Nothing -> return Nothing

lookupUnit :: ComponentId -> ShM ShapeConfig
lookupUnit n = do
    mb_shc <- lookupIndefUnitId n
    case mb_shc of
        Just shc -> return shc
        Nothing ->
            failSh (text "Cannot find package" <+> ppr n)


{-
************************************************************************
*                                                                      *
                        Shaping monads
*                                                                      *
************************************************************************
-}

-- | Register 'LHsUnit' as the unit we are shaping.
setPackageSh :: LHsUnit HsComponentId -> ShM a -> ShM a
setPackageSh (L loc HsUnit { hsunitName = L _ name } ) do_this
    = setSrcSpanSh loc
    . setHsComponentId name
    $ do_this

-- | Register 'UnitId' as the unit ID we are shaping.
setUnitIdSh :: UnitId -> ShM a -> ShM a
setUnitIdSh uid do_this
    = updGblEnv (\shg -> shg { shg_uid = uid }) $
      setThisPackageM uid do_this

data ShGblEnv = ShGblEnv {
    shg_uid :: UnitId,
    shg_name :: HsComponentId,
    shg_filename :: FilePath
    }
data ShLclEnv = ShLclEnv {
    shl_loc :: RealSrcSpan, -- Source span
    shl_errs :: TcRef Messages
    }

{-
getRealSrcSpanSh :: ShM RealSrcSpan
getRealSrcSpanSh = do
    env <- getLclEnv
    return (shl_loc env)
    -}

getSrcSpanSh :: ShM SrcSpan
getSrcSpanSh = do
    env <- getLclEnv
    return (RealSrcSpan (shl_loc env))

-- setSrcSpan
setSrcSpanSh :: SrcSpan -> ShM a -> ShM a
setSrcSpanSh (RealSrcSpan real_loc) thing_inside
    = updLclEnv (\env -> env { shl_loc = real_loc }) thing_inside
setSrcSpanSh (UnhelpfulSpan _) thing_inside = thing_inside

setHsComponentId :: HsComponentId -> ShM a -> ShM a
setHsComponentId name thing_inside
    = updGblEnv (\env -> env { shg_name = name } ) thing_inside

type ShM a = TcRnIf ShGblEnv ShLclEnv a

-- getErrsVar
getErrsVarSh :: ShM (IORef Messages)
getErrsVarSh = fmap shl_errs getLclEnv

-- addMessages
addMessagesSh :: Messages -> ShM ()
addMessagesSh (m_warns, m_errs) = do
    errs_var <- getErrsVarSh
    (warns, errs) <- readTcRef errs_var
    writeTcRef errs_var (warns `unionBags` m_warns,
                         errs  `unionBags` m_errs)

-- failWith
failSh :: SDoc -> ShM a
failSh msg = addErrSh msg >> failM

-- failIfErrsM
failIfErrsSh :: ShM ()
failIfErrsSh = ifErrsSh failM (return ())

-- ifErrsM
ifErrsSh :: ShM r -> ShM r -> ShM r
ifErrsSh bale_out normal
    = do errs_var <- getErrsVarSh
         msgs <- readTcRef errs_var
         dflags <- getDynFlags
         if errorsFound dflags msgs
            then bale_out
            else normal

-- reportError
reportErrorSh :: ErrMsg -> ShM ()
reportErrorSh err = do
    errs_var <- getErrsVarSh
    (warns, errs) <- readTcRef errs_var
    writeTcRef errs_var (warns,
                         errs  `snocBag` err)

-- addErr
addErrSh :: MsgDoc -> ShM ()
addErrSh msg = do loc <- getSrcSpanSh
                  dflags <- getDynFlags
                  -- TODO augment with context
                  reportErrorSh (mkPlainErrMsg dflags loc msg)

-- XXX eliminate me in favor of proper error messages
maybeErrSh :: SDoc -> Maybe a -> ShM a
maybeErrSh msg Nothing = failSh msg
maybeErrSh _   (Just x) = return x

liftTcToSh :: HscSource -> Module -> SrcSpan -> TcM r -> ShM r
liftTcToSh _ mod UnhelpfulSpan{} _ =
    failSh (text "Module does not have a RealSrcSpan:" <+> ppr mod)
liftTcToSh hsc_src mod (RealSrcSpan loc) do_this = do
    hsc_env <- getTopEnv
    (msgs, r) <- liftIO $ initTc hsc_env hsc_src False mod loc do_this
    addMessagesSh msgs
    case r of
        Nothing -> failM
        Just x -> return x

initShM :: HscEnv -> FilePath -> ShM a -> IO (Messages, Maybe a)
initShM hsc_env filename do_this = do
    errs_var <- newIORef emptyMessages
    let gbl_env = ShGblEnv {
                -- Will get filled in soon
                shg_uid = panic "shg_uid: not initialized",
                shg_name = panic "shg_name: not initialized",
                shg_filename = filename
            }
        lcl_env = ShLclEnv {
                shl_loc = panic "initShM sh_loc", -- Should be overridden soon
                shl_errs = errs_var -- tcl_errs
            }
        hsc_env' = hsc_env {
                -- this pokes iface files and WE DON'T WANT THAT
                -- (we don't have real iface files at this point)
                hsc_dflags = wopt_unset (hsc_dflags hsc_env) Opt_WarnWarningsDeprecations
            }
    maybe_res <- initTcRnIf 's' hsc_env' gbl_env lcl_env $ do
        r <- tryM do_this
        case r of
            Right res -> return (Just res)
            Left _ -> return Nothing
    msgs <- readIORef errs_var ;
    return (msgs, maybe_res)

type ShModM a = TcRn a

shDump :: SDoc -> ShM ()
shDump doc = do
    dflags <- getDynFlags
    when (dopt Opt_D_dump_shape dflags) (traceSh Opt_D_dump_shape doc)

traceSh :: DumpFlag -> SDoc -> ShM ()
traceSh flag doc = do
    dflags <- getDynFlags
    liftIO $ dumpSDoc dflags reallyAlwaysQualify flag "" doc

{-
************************************************************************
*                                                                      *
                        Merging
*                                                                      *
************************************************************************
-}

-- There are two parts to the substitution: the hole subst and the name subst
mergeShapes :: Shape
            -> Shape
            -> ShM Shape
mergeShapes sh1 sh2 = do
    hsc_env <- getTopEnv
    -- Step 1: Fill every requirement of 2 with provided modules from 1,
    -- and vice versa.
    -- TODO ASSERT provides/requires are disjoint
    -- TODO ASSERT lhs/rhs are disjoint
    let hsubst0_lhs = computeHoleSubst (sh_provides sh1) (sh_requires sh2)
        hsubst0_rhs = computeHoleSubst (sh_provides sh2) (sh_requires sh1)
        hsubst0 = plusUFM hsubst0_lhs hsubst0_rhs
    -- TODO This is pretty dodgy, because you might have to calculate a fixpoint
    -- Add an ASSERT that you don't, because the include summarizer dealt with
    -- SCCs for you

    -- Step 1: Fill every requirement of 2 with the provided modules from 1
    -- (as well as any implicitly filled in modules from the outer package key)
    -- ... and unify the names
    let nsubst0 = emptyNameEnv
    nsubst0 <- maybeErrSh
                -- TODO: make this error message better
                -- by reporting the specific AvailInfos that failed merging
                (vcat [ text "Failed to unify when filling requirements:"
                      , hang (text "Context:") 2 (ppr sh1)
                      , hang (text "Merging shape:") 2  (ppr sh2)])
            $ foldM (\subst ((_, as1), as2) ->
                        uAvailInfos subst as1 as2) nsubst0
                    (Map.intersectionWith (,) (sh_provides sh1) (sh_requires sh2))

    -- and vice versa
    nsubst0 <- maybeErrSh
                -- TODO: make this error message better
                -- by reporting the specific AvailInfos that failed merging
                (vcat [ text "Failed to unify when filling requirements:"
                      , hang (text "Context:") 2 (ppr sh2)
                      , hang (text "Merging shape:") 2  (ppr sh1)])
            $ foldM (\subst ((_, as1), as2) ->
                        uAvailInfos subst as1 as2) nsubst0
                    (Map.intersectionWith (,) (sh_provides sh2) (sh_requires sh1))

    -- Step 2: Check that, for any requirement we filled, that it is provided
    -- (NB: we can test based on OccNames)
    forM_ (Map.toList (Map.intersectionWith (,) (sh_provides sh1) (sh_requires sh2))) $
        \(modname, ((m, prov_as), req_as)) ->
            let mkOS as = mkUniqSet $ do a <- as
                                         n <- availNames a
                                         return (nameOccName n)
                missing = minusUniqSet (mkOS req_as) (mkOS prov_as)
            in if isEmptyUniqSet missing
                then return ()
                -- TODO this error message is pretty terrible
                else failSh $ vcat [ text "Cannot use module" <+> ppr m
                                     <+> text "to instantiate hole at" <+> ppr modname
                                   , hang (text "Missing implementations of:") 2
                                          (hsep (punctuate comma
                                                    (map ppr (uniqSetToList missing)))) ]

    -- and vice versa
    forM_ (Map.toList (Map.intersectionWith (,) (sh_provides sh2) (sh_requires sh1))) $
        \(modname, ((m, prov_as), req_as)) ->
            let mkOS as = mkUniqSet $ do a <- as
                                         n <- availNames a
                                         return (nameOccName n)
                missing = minusUniqSet (mkOS req_as) (mkOS prov_as)
            in if isEmptyUniqSet missing
                then return ()
                -- TODO this error message is pretty terrible
                else failSh $ vcat [ text "Cannot use module" <+> ppr m
                                     <+> text "to instantiate hole at" <+> ppr modname
                                   , hang (text "Missing implementations of:") 2
                                          (hsep (punctuate comma
                                                    (map ppr (uniqSetToList missing)))) ]

    -- Step 3: Unify leftover requirements
    nsubst0 <- maybeErrSh
                -- TODO: make this error message better
                -- by reporting the specific AvailInfos that failed merging
                -- (DUPLICATE)
                (vcat [ text "Failed to unify when merging requirements:"
                      , hang (text "Context:") 2 (ppr sh1)
                      , hang (text "Merging shape:") 2  (ppr sh2)])
            $ foldM (\subst (as1, as2) -> uAvailInfos subst as1 as2) nsubst0
              (Map.intersectionWith (,) (sh_requires sh1) (sh_requires sh2))
    -- This gives us a substitution
    subst@(ShSubst hsubst _nsubst) <- liftIO $ mkShSubst hsc_env hsubst0 nsubst0
    -- Step 4: Merge everything together, substituting along the way
    let provs0 = Map.union (sh_provides sh1) (sh_provides sh2)
        doSubst = liftIO . substAvailInfo hsc_env subst
    provs <- T.mapM (\(m,  as) -> do let m' = renameHoleModule hsubst m
                                     as' <- mapM doSubst as
                                     return (m', as')) provs0
    let doReqSubst as = do as' <- mapM doSubst as
                           return as'
    reqs1 <- T.mapM doReqSubst (sh_requires sh1)
    reqs2 <- T.mapM doReqSubst (Map.difference (sh_requires sh2) (sh_provides sh1))
    let reqs = Map.unionWith mergeRequirements reqs1 reqs2
    return Shape {
                sh_provides = provs,
                sh_requires = reqs
            }

mergeRequirements :: [AvailInfo]
                  -> [AvailInfo]
                  -> [AvailInfo]
mergeRequirements as1 as2 = mergeAvails as1 as2

{-
************************************************************************
*                                                                      *
                        Pre-shaping
*                                                                      *
************************************************************************
-}

data PreShape = PreShape {
    psh_provides :: UniqSet ModuleName,
    psh_requires :: UniqSet ModuleName
    }

mkModulePreShape :: ModuleName -> PreShape
mkModulePreShape modname =
    emptyPreShape { psh_provides = unitUniqSet modname }

mkSignaturePreShape :: ModuleName -> PreShape
mkSignaturePreShape modname =
    emptyPreShape { psh_requires = unitUniqSet modname }

emptyPreShape :: PreShape
emptyPreShape = PreShape { psh_provides = emptyUniqSet, psh_requires = emptyUniqSet }

preshape :: PreShape -> LHsUnitDecl HsComponentId -> ShM PreShape
preshape psh (L _ decl) = preshape' psh decl

preshape' :: PreShape -> HsUnitDecl HsComponentId -> ShM PreShape
preshape' psh (DeclD ModuleD (L _ modname) _) =
    return (mergePreShapes psh (mkModulePreShape modname))
preshape' psh (DeclD SignatureD (L _ modname) _) =
    return (mergePreShapes psh (mkSignaturePreShape modname))
preshape' psh (IncludeD (IncludeDecl{
                idInclude = L _ name,
                idInclSpec = ispec
              })) = do
    ipkg <- lookupUnit (hsComponentId name)
    fmap (mergePreShapes psh) (renamePreShape ispec (indefPackageToPreShape ipkg))

renamePreShape :: Maybe LInclSpec -> PreShape -> ShM PreShape
renamePreShape Nothing psh = return psh
renamePreShape (Just (L _ InclSpec{ isProvides = rn_provs, isRequires = rn_reqs }))
               PreShape{ psh_provides = provs, psh_requires = reqs }
    = do provs' <- renamePreProvides rn_provs provs
         reqs' <- renamePreRequires rn_reqs reqs
         failIfErrsSh
         return PreShape{ psh_provides = provs', psh_requires = reqs' }
  where renamePreProvides Nothing orig = return orig
        renamePreProvides (Just rns) orig = do
            -- nonlinear, non-mentioned are dropped
            let go new (L _ rn)
                    | renameTo rn `elementOfUniqSet` new = do
                        addErrSh (text "Duplicate dest" <+> ppr (renameTo rn))
                        -- TODO: say previous rename
                        return new
                    | not (renameFrom rn `elementOfUniqSet` orig) = do
                        addErrSh (text "Unknown module" <+> ppr (renameFrom rn))
                        return new
                    | otherwise =
                        return (addOneToUniqSet new (renameTo rn))
            foldM go emptyUniqSet rns
        renamePreRequires rns orig = do
            -- linear, non-mentioned passed through
            let go (new, orig) (L _ rn)
                    | renameTo rn `elementOfUniqSet` new = do
                        addErrSh (text "Duplicate dest (tell us if you need this to be supported)" <+> ppr (renameTo rn))
                        -- TODO: actually, this COULD be supported, but we
                        -- don't right now.
                        return (new, orig)
                    | not (renameFrom rn `elementOfUniqSet` orig) = do
                        -- TODO improve error message
                        addErrSh (text "Could not rename" <+> ppr (renameFrom rn))
                        return (new, orig)
                    | otherwise = do
                        return (addOneToUniqSet new (renameTo rn), delOneFromUniqSet orig (renameFrom rn))
            (new, left) <- foldM go (emptyUniqSet, orig) rns
            return (unionUniqSets left new)

indefPackageToPreShape :: ShapeConfig -> PreShape
indefPackageToPreShape ipkg =
    PreShape {
        psh_provides = mkUniqSet (Map.keys (shcProvides ipkg)),
        psh_requires = unitIdFreeHoles (shcUnitId ipkg)
        }

mergePreShapes :: PreShape -> PreShape -> PreShape
mergePreShapes psh1 psh2 =
    PreShape {
        psh_provides = unionUniqSets (psh_provides psh1) (psh_provides psh2),
        psh_requires = unionUniqSets
                                 (minusUniqSet (psh_requires psh1) (psh_provides psh2))
                                 (minusUniqSet (psh_requires psh2) (psh_provides psh1))
    }


{-
************************************************************************
*                                                                      *
                        Shaping proper
*                                                                      *
************************************************************************
-}

-- | Compute package key of a 'HsUnit'
shComputeUnitId :: LHsUnit HsComponentId -> ShM UnitId
shComputeUnitId
    (L loc HsUnit { hsunitName = L _ hscid
                  , hsunitExports = Nothing -- XXX incomplete
                  , hsunitBody = decls })
    = setSrcSpanSh loc
    . setHsComponentId hscid $
      do -- Pre-pass, to calculate the requirements
         psh <- foldM preshape emptyPreShape decls
         let insts = map (\modname -> (modname, mkModule holeUnitId modname))
                         (uniqSetToList (psh_requires psh))
         return (unsafeNewUnitId (hsComponentId hscid) insts)
shComputeUnitId
    (L _ HsUnit { hsunitName = _
                  , hsunitExports = Just _
                  , hsunitBody = _ }) = panic "Exports not implemented"

-- | Shape a 'HsUnit'.
shPackage :: UnitId -> IncludeGraph -> [ModSummary] -> LHsUnit HsComponentId -> ShM Shape
shPackage uid
    include_graph
    mod_graph
    lunit@(L _loc HsUnit { hsunitName = L _ hscid
                         , hsunitExports = Nothing })
    = setPackageSh lunit .
      setUnitIdSh uid $ do
         -- Shape includes and modules
         sh0 <- foldM shIncludeSummary emptyShape include_graph
         sh <- foldM shModSummary sh0 mod_graph
         -- Dump the shape if we're asked to
         shDump (vcat [ text "/--- Shape for" <+> ppr (hsPackageName hscid)
                      , ppr sh
                      , text "\\---"
                      ])

         return sh
shPackage _ _ _
    (L _ HsUnit { hsunitName = _
                , hsunitExports = Just _
                , hsunitBody = _ }) = panic "exports not implemented"

shIncludeSummary :: Shape -> IncludeSummary -> ShM Shape
shIncludeSummary sh IncludeSummary{ is_loc = loc
                                  , is_provides = provs
                                  , is_requires = reqs } = setSrcSpanSh loc $ do
    hsc_env <- getTopEnv
    -- Soooooooooo.... we're shaping an include and we know it's UID
    -- is p(H -> q:H).  What we'd like to do is slurp up the H requirements
    -- of p and see if they are fulfilled by q:H.  But we can't use
    -- computeInterface p(H -> q:H):H to get the requirements, because
    -- computeInterface assumes that this renaming is VALID (that is,
    -- q:H truly fulfills all of the mi_exports of p:H.)  Which remains
    -- to be seen: the whole point of shaping is to figure out if this
    -- is true or not.
    --
    -- In fact, computeInterface is TOOO cunning, it is going to rename all
    -- of the interface and we really didn't care about that, just the
    -- mi_exports.  So we need a version of computeInterface which
    -- "does" less.
    reqs <- T.forM reqs $ \mod -> do
                (exports, _) <- liftIO $ initIfaceCheck hsc_env (withException (computeExports (text "shaping requires" <+> ppr mod) False mod))
                return exports
    provs <- T.forM provs $ \mod -> do
                (exports, _) <- liftIO $ initIfaceCheck hsc_env (withException (computeExports (text "shaping provides" <+> ppr mod) False mod))
                return (mod, exports)
    mergeShapes sh (Shape provs reqs)

shModSummary :: Shape -> ModSummary -> ShM Shape
{-
shModSummary sh summary
    | ms_hsc_src summary == HsBootMerge = return sh
    -}
shModSummary sh summary = do -- TODO would like location here
    let outer_m = ms_mod summary
        modname = ms_mod_name summary
        hsc_src = ms_hsc_src summary
    -- Usually will become HOLE:H for holes, but not necessarily!
    hsc_env <- getTopEnv
    parsed_mod <- liftIO $ hscParse hsc_env summary
    let hsmod@(L inner_loc _) = hpm_module parsed_mod
    avails <- liftTcToSh hsc_src outer_m inner_loc $
        updGblEnv (\tcg_env -> tcg_env { tcg_ifaces = mkShIfaces sh
                                       , tcg_shaping = True } ) $
        shModule hsmod
    mergeShapes sh (mkDeclShape hsc_src modname outer_m avails)

mkDeclShape :: HscSource -> ModuleName -> Module -> [AvailInfo] -> Shape
mkDeclShape HsSrcFile = mkModuleShape
mkDeclShape HsigFile = mkSignatureShape
mkDeclShape _ = panic "merge"

mkModuleShape :: ModuleName -> Module -> [AvailInfo] -> Shape
mkModuleShape modname this_mod exports =
    emptyShape { sh_provides = Map.singleton modname (this_mod, exports) }

mkSignatureShape :: ModuleName -> Module -> [AvailInfo] -> Shape
mkSignatureShape modname _this_mod exports =
    emptyShape { sh_requires = Map.singleton modname exports }

-- Based off of tcRnModuleTcRnM
shModule :: Located (HsModule RdrName) -> ShModM [AvailInfo]
shModule (L loc (HsModule maybe_mod export_ies
                          import_decls local_decls _mod_deprec
                          _maybe_doc_hdr)) = do
    -- NB: repeated setGblEnv seems goofy but it's necessary!
    tcg_env <- getGblEnv

    let prel_imp_loc = loc -- TODO type-checker gets this from prel_imp_loc
        this_mod = tcg_mod tcg_env

    -- TODO: not necessary???? Why did we use this......
    -- tcg_env <- tcRnSignature (tcg_src tcg_env)
    -- setGblEnv tcg_env $ do

    -- TODO factor this out to a function and reuse in tcRnModuleTcRnM
    implicit_prelude <- xoptM LangExt.ImplicitPrelude;
    let { prel_imports = mkPrelImports (moduleName this_mod) prel_imp_loc
                                     implicit_prelude import_decls }

    -- Shape imports
    tcg_env <- shImports (prel_imports ++ import_decls)
    setGblEnv tcg_env $ do

    -- Shape declarations
    tcg_env <- shSrcDecls local_decls
    setGblEnv tcg_env $ do

    -- Calculate the exports
    (_rn_exports, tcg_env) <- rnExports (isJust maybe_mod) export_ies tcg_env ;
    -- TODO: I think it's OK if we don't typecheck rn_exports

    failIfErrsM
    return (tcg_exports tcg_env)

-- Based off of tcRnImports
shImports :: [LImportDecl RdrName] -> ShModM TcGblEnv
shImports import_decls = do
    (rn_imports, rdr_env, imports, hpc_info) <- rnImports import_decls
    failIfErrsM
    gbl <- getGblEnv
    return gbl {
          tcg_rdr_env = tcg_rdr_env gbl `plusGlobalRdrEnv` rdr_env,
          tcg_imports = tcg_imports gbl `plusImportAvails` imports,
          tcg_rn_imports = rn_imports,
          tcg_hpc     = hpc_info
        }

-- Based off of tcRnSrcDecls
shSrcDecls :: [LHsDecl RdrName] -> ShModM TcGblEnv
shSrcDecls decls = do
    (first_group, group_tail) <- findSplice decls
    -- TODO This renames the entire source, but technically we
    -- only need the top level to do our work.
    -- TODO Do we need to calculate extra_deps?
    (tcg_env, _rn_decls) <- rnTopSrcDecls first_group
    case group_tail of
        Just _ -> failWithTc (text "Can't do a top-level splice in shaping")
        Nothing -> return tcg_env

{-
************************************************************************
*                                                                      *
                        Shaping stub ModIfaces
*                                                                      *
************************************************************************
-}

-- Note [Stub ModIface for shaping]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- We want to reuse the existing implementation of the renamer, but
-- the renamer assumes that when a module is imported, we can get
-- the ModIface for the source level import; however, we don't have
-- enough information for a full interface, just enough to give an
-- accurate set of exports.  So 'mkShIfaces' and 'mkShIface' make
-- stub interfaces which can be then fed into the renamer to give
-- it enough information to proceed.

-- | Create a map of fake 'ModIface's corresponding to the exports of
-- a 'Shape'.
mkShIfaces :: Shape -> ModuleNameEnv ModIface
mkShIfaces sh = listToUFM_C mergeModIfaceForImport (provs ++ reqs)
    where provs = do (modname, (m, avails)) <- Map.toList (sh_provides sh)
                     return (modname, mkShIface m avails)
          -- For now, all requirements are visible.
          -- NB: This works slightly differently from how type-checking
          -- programs the interfaces.
          reqs  = do (modname, avails) <- Map.toList (sh_requires sh)
                     return (modname, mkShIface (mkModule holeUnitId modname) avails)

-- | Create a fake 'ModIface' representing a 'Module' and its exports.
mkShIface :: Module -> [AvailInfo] -> ModIface
mkShIface this_mod exports =
    (emptyModIface this_mod) {
        mi_exports  = mkIfaceExports exports
        -- NB: mi_fixities not recorded here, so it's not possible
        -- to do full renaming since we won't reassociate infix ops
    }

mergeModIfaceForImport :: ModIface -> ModIface -> ModIface
mergeModIfaceForImport = mergeModIface' (error "mergeModIfaceForImport")
