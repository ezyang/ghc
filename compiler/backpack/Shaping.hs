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
) where

#include "HsVersions.h"

import MergeIface
import HscMain
import BackpackSyn
import ShUnitId
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

import System.FilePath
import Data.List
import Data.IORef
import Data.Time
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Traversable as T

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
shIncludeGraph :: UnitId -> LHsUnit -> ShM [IncludeSummary]
shIncludeGraph pk lpkg = setPackageSh lpkg . setUnitIdSh pk $ do
    let decls = hsunitBody (unLoc lpkg)
    dflags <- getDynFlags
    -- Extract out all the includes from the package description,
    -- processing any renamings so we have an up-to-date picture
    -- about what an include provides and requires.  However, we
    -- DON'T yet know how the includes are going to be instantiated.
    let get_include (L loc (IncludeD decl)) = Just (L loc decl)
        get_include _ = Nothing
        incls = mapMaybe get_include decls
    graph0 <- mapM summariseInclude incls
    {-
    -- If we want includes to be instantiatable by locally defined
    -- modules, we need to also consider local module definitions in
    -- our substitution.
    let get_decl (L _ (DeclD ModuleD (L _ modname) _mb_hsmod)) = do
          Just (modname, mkModule pk modname)
        get_decl _ = Nothing
        mods = catMaybes (map get_decl decls)
    -}
    -- Based on the 'UnitId', compute an initial substitution to apply
    -- to the includes.  If we're just type-checking, this will start
    -- off as the identity substitution.
    insts <- liftIO $ unitIdInsts dflags pk
    hsubst0 <- liftIO $ mkShHoleSubst dflags (listToUFM insts)
    -- Processing the include graph in topological order, "fill" requirements
    -- by using the substitution, updating the summary, and then add
    -- provisions as things that can be used by later includes in the topsort.
    let go (gr, hsubst) (AcyclicSCC is0) = do -- TODO set loc
          -- Substitute the provisions and unit ID
          rn_provs <- T.mapM (liftIO . renameHoleModule dflags hsubst) (is_provides is0)
          -- NB: DO NOT substitute the requirements.  A bit finely balanced
          pk <- liftIO $ renameHoleUnitId dflags hsubst (is_pkg_key is0)
          let is = is0 { is_inst_provides = rn_provs
                       , is_pkg_key = pk }
          -- Update the substitution with the provisions
          hsubst' <- liftIO $ addListToHoleSubst dflags hsubst (Map.toList rn_provs)
              -- TODO: assert fixpoint not necessary
          return (is:gr, hsubst')
        go _ (CyclicSCC iss) = failSh (text "Include cycle:" $$ ppr iss)
    let top_graph = topSortIncludeGraph graph0
    (rev_graph, _) <- foldM go ([], hsubst0) top_graph
    let graph = reverse rev_graph
    -- shDump (ppr graph)
    return graph

-- | Convert an 'IncludeDecl' into an 'IncludeSummary', applying any
-- renaming to update the provided and required modules.  This does
-- NOT substitute holes; that is done later in 'shIncludeGraph'.
summariseInclude :: Located IncludeDecl -> ShM IncludeSummary
summariseInclude ldecl@(L _ IncludeDecl { idComponentName = L _ name
                                        , idInclSpec = mb_inclspec }) = do
    dflags <- getDynFlags
    ipkg <- lookupUnit name
    hsubst <- liftIO $ mkInclSpecSubst dflags mb_inclspec

    provs0 <- T.mapM (liftIO . renameHoleModule dflags hsubst) (shcProvides ipkg)
    let renameProvides Nothing
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

    -- TODO: more utility functions here... stop UnitId<->ShUnitId
    -- bouncing
    pk0 <- liftIO $ newUnitId' dflags (shcShUnitId ipkg)
    pk <- liftIO $ renameHoleUnitId dflags hsubst pk0
    insts <- liftIO $ unitIdInsts dflags pk

    return IncludeSummary {
        is_ldecl = ldecl,
        -- Not substituted yet, we will do this shortly
        is_pkg_key = pk,
        is_inst_provides = panic "unknown",
        is_provides = provs,
        is_requires = Map.fromList [(moduleName new, mkModule pk orig) | (orig, new) <- insts, isHoleModule new ]
        }

mkInclSpecSubst :: DynFlags -> Maybe (Located InclSpec) -> IO ShHoleSubst
mkInclSpecSubst _ Nothing = return emptyUFM
mkInclSpecSubst dflags (Just (L _ InclSpec { isRequires = rns })) =
    mkShHoleSubst dflags (foldl' (\m (L _ rn) ->
                               addToUFM m
                                   (renameFrom rn)
                                   (mkModule holeUnitId
                                             (renameTo rn)))
                           emptyUFM rns)

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
shModGraph :: UnitId -> IncludeGraph -> LHsUnit -> ShM [ModSummary]
shModGraph pk include_graph lpkg = setPackageSh lpkg . setUnitIdSh pk $ do
    let decls = hsunitBody (unLoc lpkg)
    dflags <- getDynFlags
    pk <- shUnitId
    insts <- liftIO $ unitIdInsts dflags pk

    --  1. Create a HsSrcFile/HsBootFile summary for every
    --  explicitly mentioned module/signature.
    --  TODO: chase deps, so that we don't have to assume all
    --  modules/signatures are mentioned.
    let get_decl (L _ (DeclD dt lmodname mb_hsmod)) = do
          let hsc_src = case dt of
                          ModuleD    -> HsSrcFile
                          SignatureD -> HsBootFile
          Just `fmap` summariseDecl dflags hsc_src lmodname mb_hsmod
        get_decl _ = return Nothing
    nodes <- catMaybes `fmap` mapM get_decl decls

    --  2. For every hole, create an HsBootMerge summary.
    --  TODO: this logic would work for GhcMake too.
    --  NB: We don't have to worry about there being an HsSrcFile, because
    --  that would be filled in.
    -- The node_map tells us if there is a local boot file a merge should
    -- depend on
    let node_map = Map.fromList [ ((ms_mod_name n, ms_hsc_src n == HsBootFile), n)
                                | n <- nodes ]
    -- TODO: included packages
    merge_nodes <- forM insts $ \(mod_name, _) ->
        let has_local = Map.member (mod_name, True) node_map
        in summariseMerge dflags include_graph has_local mod_name

    -- 3. Return the kaboodle
    return (nodes ++ merge_nodes)

summariseMerge :: DynFlags -> IncludeGraph -> Bool -> ModuleName -> ShM ModSummary
summariseMerge dflags include_graph has_local mod_name = do
    -- SUPER duplicate with makeMergeRequirementSummary
    hsc_env <- getTopEnv
    ComponentName unit_fs <- fmap shg_name getGblEnv
    location <- liftIO $ mkHomeModLocation2 dflags mod_name
                 (unpackFS unit_fs </> moduleNameSlashes mod_name) "hs-boot-merge"
    obj_timestamp <-
         if isObjectTarget (hscTarget dflags)
             then liftIO $ modificationTimeIfExists (ml_obj_file location)
             else return Nothing
    src_timestamp <- case obj_timestamp of
                        Just date -> return date
                        Nothing -> liftIO getCurrentTime -- something fake
    mod <- liftIO $ addHomeModuleToFinder hsc_env mod_name location
    canon_mod <- liftIO $ canonicalizeModule dflags mod
    included_reqs <- fmap concat . forM include_graph $ \is -> do
        incl_insts <- liftIO $ unitIdInsts dflags (is_pkg_key is)
        return $ case find ((==canon_mod).snd) incl_insts of
                    Nothing -> []
                    Just (n, _) -> [mkModule (is_pkg_key is) n]
    return ModSummary {
        ms_mod = mod,
        ms_hsc_src = HsBootMerge,
        ms_location = location,
        ms_hs_date = src_timestamp,
        ms_obj_date = obj_timestamp,
        ms_iface_date = Nothing,
        ms_srcimps = [],
        ms_textual_imps = [],
        ms_merge_imps = (has_local, included_reqs),
        ms_parsed_mod = Nothing,
        ms_fat_iface = Nothing,
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
    ComponentName unit_fs <- fmap shg_name getGblEnv
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
                                -- HsBootFile -> "hs-boot"
                                _ -> "hs")
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

        implicit_prelude = xopt Opt_ImplicitPrelude dflags
        implicit_imports = mkPrelImports modname loc
                                         implicit_prelude imps
        convImport (L _ i) = (fmap sl_fs (ideclPkgQual i), ideclName i)

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
            ms_fat_iface = Nothing,
            ms_srcimps = map convImport src_idecls,
            ms_textual_imps = map convImport (implicit_imports ++ ordinary_imps),
            ms_merge_imps = (False, []),
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
        shcShUnitId :: ShUnitId,
        shcProvides :: Map ModuleName Module,
        shcRequires :: Map ModuleName Module
    }

-- summariseInclude (provides and shpackagekey)
-- lookupPackageShape (shape, package key)
-- preshape (preshape)
lookupIndefUnitId :: ComponentId -> ShM (Maybe ShapeConfig)
lookupIndefUnitId iud = do
    dflags <- getDynFlags
    case lookupIndefiniteUnit dflags iud of
        {-
        IndefFoundIndefinite cfg -> do
            -- got to do more work...
            let sh_uid = ShUnitId {
                                 shUnitIdComponentId = indefComponentId cfg,
                                 shUnitIdInsts = [ (m, mkModule holeUnitId m)
                                                     | m <- indefRequires cfg],
                                 shUnitIdFreeHoles = mkUniqSet (indefRequires cfg)
                              }
            uid <- liftIO $ newUnitId' dflags sh_uid
            provs <- liftIO $ convertIndefiniteHoleMap dflags (indefProvides cfg)
            return $ Just
                ShapeConfig { shcProvides = Map.fromList provs
                            , shcRequires = Map.fromList [(m, mkModule uid m) | m <- indefRequires cfg]
                            , shcShUnitId = sh_uid}
                            -}
        Just cfg -> do
            sh_uid <- liftIO $ lookupUnitId dflags (packageConfigId cfg)
            return $ Just
                ShapeConfig { shcShUnitId = sh_uid
                            , shcProvides = Map.fromList (exposedModules cfg)
                            -- TODO: is this right?  Should be OK
                            , shcRequires = Map.fromList (shUnitIdInsts sh_uid)
                            }
        Nothing -> return Nothing

lookupUnit :: ComponentName -> ShM ShapeConfig
lookupUnit n = do
    -- First, create a "local" unit id and see if we already have dealt
    -- with it.
    dflags <- getDynFlags
    let local_uid = addComponentName (thisComponentId dflags) n
    mb_shc <- lookupIndefUnitId local_uid
    case mb_shc of
        Just shc -> return shc
        Nothing -> do
            uid <- case lookupComponentName dflags n of
                    Just uid -> return uid
                    Nothing -> failSh (text "Cannot find unit" <+> ppr n)
            mb_shc <- lookupIndefUnitId uid
            case mb_shc of
                Just shc -> return shc
                Nothing -> failSh (text "Cannot find unit" <+> ppr n <+>
                                parens (text "despite having a mapping to" <+> ppr uid))


{-
************************************************************************
*                                                                      *
                        Shaping monads
*                                                                      *
************************************************************************
-}

-- | Register 'LHsUnit' as the unit we are shaping.
setPackageSh :: LHsUnit -> ShM a -> ShM a
setPackageSh (L loc HsUnit { hsunitName = L _ name } ) do_this
    = setSrcSpanSh loc
    . setComponentName name
    $ do_this

-- | Register 'UnitId' as the unit ID we are shaping.
setUnitIdSh :: UnitId -> ShM a -> ShM a
setUnitIdSh pk do_this
    = updGblEnv (\shg -> shg { shg_pk = pk }) $
      setThisPackageM pk do_this

data ShGblEnv = ShGblEnv {
    shg_pk :: UnitId,
    shg_name :: ComponentName,
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

setComponentName :: ComponentName -> ShM a -> ShM a
setComponentName name thing_inside
    = updGblEnv (\env -> env { shg_name = name } ) thing_inside

type ShM a = TcRnIf ShGblEnv ShLclEnv a

-- getErrsVar
getErrsVarSh :: ShM (IORef Messages)
getErrsVarSh = fmap shl_errs getLclEnv

shUnitId :: ShM UnitId
shUnitId = fmap shg_pk getGblEnv

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

liftTcToSh :: HscSource -> TopModule -> SrcSpan -> TcM r -> ShM r
liftTcToSh _ top_mod UnhelpfulSpan{} _ =
    failSh (text "Module does not have a RealSrcSpan:" <+> ppr top_mod)
liftTcToSh hsc_src top_mod (RealSrcSpan loc) do_this = do
    hsc_env <- getTopEnv
    (msgs, r) <- liftIO $ initTc hsc_env hsc_src False top_mod loc do_this
    addMessagesSh msgs
    case r of
        Nothing -> failM
        Just x -> return x

initShM :: HscEnv -> FilePath -> ShM a -> IO (Messages, Maybe a)
initShM hsc_env filename do_this = do
    errs_var <- newIORef emptyMessages
    let gbl_env = ShGblEnv {
                -- Will get filled in soon
                shg_pk = panic "shg_pk: not initialized",
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

addShapeToEnv :: ComponentName -> (Shape, UnitId) -> ShM ()
addShapeToEnv name (sh, pk) =
    updateEps_ (\eps -> eps { eps_EST = Map.insert name (sh, pk) (eps_EST eps) })

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
    dflags <- getDynFlags
    -- Step 1: Fill every requirement of 2 with provided modules from 1,
    -- and vice versa.
    -- TODO ASSERT provides/requires are disjoint
    -- TODO ASSERT lhs/rhs are disjoint
    hsubst0_lhs <- liftIO $ computeHoleSubst dflags (sh_provides sh1) (sh_requires sh2)
    hsubst0_rhs <- liftIO $ computeHoleSubst dflags (sh_provides sh2) (sh_requires sh1)
    let hsubst0 = plusUFM hsubst0_lhs hsubst0_rhs
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
    provs <- T.mapM (\(m,  as) -> do m' <- liftIO $ renameHoleModule dflags hsubst m
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

preshape :: PreShape -> LHsUnitDecl -> ShM PreShape
preshape psh (L _ decl) = preshape' psh decl

preshape' :: PreShape -> HsUnitDecl -> ShM PreShape
preshape' psh (DeclD ModuleD (L _ modname) _) =
    return (mergePreShapes psh (mkModulePreShape modname))
preshape' psh (DeclD SignatureD (L _ modname) _) =
    return (mergePreShapes psh (mkSignaturePreShape modname))
preshape' psh (IncludeD (IncludeDecl{
                idComponentName = L _ name,
                idInclSpec = ispec
              })) = do
    ipkg <- lookupUnit name
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
        psh_requires = shUnitIdFreeHoles (shcShUnitId ipkg)
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
shComputeUnitId :: ComponentId -> LHsUnit -> ShM ShUnitId
shComputeUnitId cid
    (L loc HsUnit { hsunitName = L _ name
                  , hsunitExports = Nothing -- XXX incomplete
                  , hsunitBody = decls })
    = setSrcSpanSh loc
    . setComponentName name $
      do dflags <- getDynFlags
         -- Pre-pass, to calculate the requirements
         psh <- foldM preshape emptyPreShape decls
         insts <- forM (uniqSetToList (psh_requires psh)) $ \modname -> do
                        -- TODO: unnecessarily monadic
                        let mod = mkModule holeUnitId modname
                        return (modname, mod)
         liftIO $ newShUnitId dflags cid insts
shComputeUnitId _cid
    (L _ HsUnit { hsunitName = _
                  , hsunitExports = Just _
                  , hsunitBody = _ }) = panic "Exports not implemented"

-- | Shape a 'HsUnit'.
shPackage :: UnitId -> IncludeGraph -> [ModSummary] -> LHsUnit -> ShM Shape
shPackage pk
    include_graph
    mod_graph
    lunit@(L _loc HsUnit { hsunitName = L _ name
                         , hsunitExports = Nothing })
    = setPackageSh lunit .
      setUnitIdSh pk $ do
         -- Shape includes and modules
         sh0 <- foldM shIncludeSummary emptyShape include_graph
         sh <- foldM shModSummary sh0 mod_graph
         -- Dump the shape if we're asked to
         shDump (vcat [ text "/--- Shape for" <+> ppr name
                      , ppr sh
                      , text "\\---"
                      ])
         -- Store the shape in the EPS
         addShapeToEnv name (sh, pk)

         return sh
shPackage _ _ _
    (L _ HsUnit { hsunitName = _
                , hsunitExports = Just _
                , hsunitBody = _ }) = panic "exports not implemented"

shIncludeSummary :: Shape -> IncludeSummary -> ShM Shape
shIncludeSummary sh IncludeSummary{ is_ldecl = L loc _
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
shModSummary sh summary
    | ms_hsc_src summary == HsBootMerge = return sh
shModSummary sh summary = do -- TODO would like location here
    let outer_m = ms_mod summary
        modname = ms_mod_name summary
        hsc_src = ms_hsc_src summary
    dflags <- getDynFlags
    -- Usually will become HOLE:H for holes, but not necessarily!
    inner_m <- liftIO $ canonicalizeModule dflags outer_m
    hsc_env <- getTopEnv
    parsed_mod <- liftIO $ hscParse hsc_env summary
    let hsmod@(L inner_loc _) = hpm_module parsed_mod
    avails <- liftTcToSh hsc_src (TopModule { topModSemantic = inner_m
                                            , topModIdentity = outer_m }) inner_loc $
        updGblEnv (\tcg_env -> tcg_env { tcg_ifaces = mkShIfaces sh
                                       , tcg_shaping = True } ) $
        shModule hsmod
    mergeShapes sh (mkDeclShape hsc_src modname outer_m avails)

mkDeclShape :: HscSource -> ModuleName -> Module -> [AvailInfo] -> Shape
mkDeclShape HsSrcFile = mkModuleShape
mkDeclShape HsBootFile = mkSignatureShape
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
        this_mod = topModIdentity (tcg_top_mod tcg_env)

    -- TODO: not necessary???? Why did we use this......
    -- tcg_env <- tcRnSignature (tcg_src tcg_env)
    -- setGblEnv tcg_env $ do

    -- TODO factor this out to a function and reuse in tcRnModuleTcRnM
    implicit_prelude <- xoptM Opt_ImplicitPrelude;
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
    (emptyModIface (hsTopModule this_mod)) {
        mi_exports  = mkIfaceExports exports
        -- NB: mi_fixities not recorded here, so it's not possible
        -- to do full renaming since we won't reassociate infix ops
    }

mergeModIfaceForImport :: ModIface -> ModIface -> ModIface
mergeModIfaceForImport = mergeModIface' (error "mergeModIfaceForImport")
