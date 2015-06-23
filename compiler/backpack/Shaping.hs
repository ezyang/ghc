{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE CPP #-}
module Shaping (
    -- * Shaping monad
    initShM,
    ShM,
    -- * Shaping
    shPackage,
    shComputeUnitKey,
    shIncludeGraph,
    shModGraph,
) where

#include "HsVersions.h"

import MergeIface
import HscMain
import BackpackSyn
import ShUnitKey
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
import GHC.PackageDb

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
                        Shaping VERSION TWO
*                                                                      *
************************************************************************
-}

-- Plan:
--      UnitNode ::= Include [ModuleName] [ModuleName]
--                 | Merge ModuleName
--                      Imports {-# BOOT #-} ModuleName
--                      Imports Included ModuleName
--                 | Signature {-# BOOT #-} ModuleName
--                      Imports ModuleName
--                 | Module ModuleName
--                      Imports ModuleName
--
-- Extremist: Module = Unit
-- Should the Unit modularity be what GhcMake can conveniently compile?
-- Let's get something that works.
--      Do we want to force through GhcMake? (SPJ commented once that better to
--      not.  But we get some facilities)
--      **Let's force it through GhcMake**
--
-- This means that all includes need to be done BEFORE HAND
--
--      * Preshape sort just includes (this is the order we compile them)
--      * Compute PKs for includes
--      * (Shape if indefinite)
--      * Compute and compile module graph, with the PK provs brought into scope
--        (requirements are just merge nodes; loaded ifaces will look right due
--        to shaping)
--
-- Generalization?  With GhcMake or without?
--
--      * Without GhcMake, Decls form a graph.  Just compile.  (Expanded graph
--      is just for big compilation...)  So would have to reimplement GhcMake
--      but without the home package restriction. BLEH.  OK, plan on
--      reimplementing if you get this far.

shIncludeGraph :: UnitKey -> LHsUnit -> ShM [IncludeSummary]
shIncludeGraph pk lpkg = setPackageSh lpkg . setUnitKeySh pk $ do
    let decls = hsunitBody (unLoc lpkg)
    dflags <- getDynFlags
    let get_include (L loc (IncludeD decl)) = Just (L loc decl)
        get_include _ = Nothing
        incls = mapMaybe get_include decls
    graph0 <- mapM summariseInclude incls
    -- With the top-sorted include graph, fill in implementations of
    -- modules.
    pk <- shPkgKey
    insts <- liftIO $ unitKeyInsts dflags pk
    -- HACK: augment with any local modules
    -- This doesn't really help
    let get_decl (L _ (DeclD ModuleD (L _ modname) _mb_hsmod)) = do
          Just (modname, mkModule pk modname)
        get_decl _ = Nothing
        mods = catMaybes (map get_decl decls)
    hsubst0 <- liftIO $ mkShHoleSubst dflags (listToUFM (insts ++ mods))
    let go (gr, hsubst) (AcyclicSCC is0) = do -- TODO set loc
          provs <- T.mapM (liftIO . renameHoleModule dflags hsubst) (is_provides is0)
          pk <- liftIO $ renameHoleUnitKey dflags hsubst (is_pkg_key is0)
          let is = is0 { is_provides = provs
                       , is_pkg_key = pk }
              -- TODO: assert fixpoint not necessary
          hsubst' <- liftIO $ addListToHoleSubst dflags hsubst (Map.toList provs)
          return (is:gr, hsubst')
        go _ (CyclicSCC iss) = failSh (text "Include cycle:" $$ ppr iss)
    (rev_graph, _) <- foldM go ([], hsubst0) (topSortIncludeGraph graph0)
    let graph = reverse rev_graph
    -- shDump (ppr graph)
    return graph

setPackageSh :: LHsUnit -> ShM a -> ShM a
setPackageSh (L loc HsUnit { hsunitName = L _ name } ) do_this
    = setSrcSpanSh loc
    . setUnitName name
    $ do_this

setUnitKeySh :: UnitKey -> ShM a -> ShM a
setUnitKeySh pk do_this
    = updGblEnv (\shg -> shg { shg_pk = pk }) $
      setThisPackageM pk do_this

-- This is our version of GhcMake.downsweep, but with a few modifications:
--
--  1. Every module is required to be mentioned, so we don't do any funny
--     business with targets or recursively grabbing dependencies.  (We
--     could support this in principle).
--  2. We support inline modules, whose summary we have to synthesize ourself.
--
-- We don't bother trying to support GhcMake for now, it's more trouble
-- than it's worth for inline modules.
shModGraph :: UnitKey -> IncludeGraph -> LHsUnit -> ShM [ModSummary]
shModGraph pk include_graph lpkg = setPackageSh lpkg . setUnitKeySh pk $ do
    let decls = hsunitBody (unLoc lpkg)
    dflags <- getDynFlags
    pk <- shPkgKey
    insts <- liftIO $ unitKeyInsts dflags pk
    hsc_env <- getTopEnv
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
    let node_map = Map.fromList [ ((ms_mod n, ms_hsc_src n == HsBootFile), n)
                                | n <- nodes ]
    -- TODO: included packages
    merge_nodes <- forM insts $ \(mod_name, _) -> do
        -- SUPER duplicate with makeMergeRequirementSummary
        UnitName unit_fs <- fmap shg_name getGblEnv
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
        let has_local = Map.member (mod, True) node_map
        included_reqs <- fmap concat . forM include_graph $ \is -> do
            incl_insts <- liftIO $ unitKeyInsts dflags (is_pkg_key is)
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
            ms_hspp_file = "FAKE",
            ms_hspp_opts = dflags,
            ms_hspp_buf = Nothing
            }

    -- 3. Return the kaboodle
    return (nodes ++ merge_nodes)

mkInclSpecSubst :: DynFlags -> Maybe (Located InclSpec) -> IO ShHoleSubst
mkInclSpecSubst _ Nothing = return emptyUFM
mkInclSpecSubst dflags (Just (L _ InclSpec { isRequires = rns })) =
    mkShHoleSubst dflags (foldl' (\m (L _ rn) ->
                               addToUFM m
                                   (renameFrom rn)
                                   (mkModule holeUnitKey
                                             (renameTo rn)))
                           emptyUFM rns)

-- Just a summary of shape information, not quite the shape but you
-- can calculate it based on the 'Module's that are available.
data ShapeConfig
    = ShapeConfig {
        shcShUnitKey :: ShUnitKey,
        shcProvides :: Map ModuleName Module,
        shcRequires :: [ModuleName]
    }

convertIndefiniteModule
    :: DynFlags
    -> IndefModule
    -> IO Module
convertIndefiniteModule dflags (IndefiniteModule uk name) = do
    pk <- convertIndefiniteUnitKey dflags uk
    return (mkModule pk name)

convertIndefiniteUnitKey
    :: DynFlags
    -> IndefiniteUnitKey InstalledPackageId UnitName ModuleName
    -> IO UnitKey
convertIndefiniteUnitKey dflags (IndefiniteUnitKey uid iinsts) = do
    insts <- convertIndefiniteHoleMap dflags iinsts
    newUnitKey dflags uid insts

convertIndefiniteHoleMap
    :: DynFlags
    -> [(ModuleName, IndefModule)]
    -> IO [(ModuleName, Module)]
convertIndefiniteHoleMap dflags hmap =
    let conv (modname, imod) = do
            mod <- convertIndefiniteModule dflags imod
            return (modname, mod)
    in mapM conv hmap

-- summariseInclude (provides and shpackagekey)
-- lookupPackageShape (shape, package key)
-- preshape (preshape)
lookupIndefUnitId :: IndefUnitId -> ShM (Maybe ShapeConfig)
lookupIndefUnitId iud = do
    dflags <- getDynFlags
    case lookupIndefiniteUnit dflags iud of
        IndefFoundIndefinite cfg -> do
            -- got to do more work...
            provs <- liftIO $ convertIndefiniteHoleMap dflags (indefProvides cfg)
            return $ Just
                ShapeConfig { shcProvides = Map.fromList provs
                            , shcRequires = indefRequires cfg
                            , shcShUnitKey
                            = ShUnitKey {
                                 shUnitKeyUnitId = indefUnitId cfg,
                                 shUnitKeyInsts = [ (m, mkModule holeUnitKey m)
                                                     | m <- indefRequires cfg],
                                 shUnitKeyFreeHoles = mkUniqSet (indefRequires cfg)
                              }
                            }
        IndefFoundDefinite cfg ->
            let conv (ExposedModule m reex sig) =
                      ASSERT ( isNothing sig ) -- legitimate error
                      ASSERT ( isNothing reex ) -- TODO
                      (m, mkModule (unitKey cfg) m)
            in return $ Just
                ShapeConfig { shcShUnitKey
                            -- TODO: ShUnitKey should return always,
                            -- use the unit name == Nothing convention!!!
                            = ShUnitKey {
                                 shUnitKeyUnitId = packageUnitId cfg,
                                 shUnitKeyInsts = [],
                                 shUnitKeyFreeHoles = emptyUniqSet
                              }
                            , shcProvides = Map.fromList (map conv (exposedModules cfg))
                            , shcRequires = []
                            }
        IndefNotFound -> return Nothing

lookupUnit :: UnitName -> ShM ShapeConfig
lookupUnit n = do
    -- First, create a "local" unit id and see if we already ahve dealt
    -- with it.
    dflags <- getDynFlags
    let local_uid = IndefiniteUnitId (thisIPID dflags) (Just n)
    mb_shc <- lookupIndefUnitId local_uid
    case mb_shc of
        Just shc -> return shc
        Nothing -> do
            uid <- case lookupUnitName dflags n of
                    Just uid -> return uid
                    Nothing -> failSh (text "Cannot find unit" <+> ppr n)
            mb_shc <- lookupIndefUnitId uid
            case mb_shc of
                Just shc -> return shc
                Nothing -> failSh (text "Cannot find unit" <+> ppr n <+>
                                parens (text "despite having a mapping to" <+> ppr uid))

summariseInclude :: Located IncludeDecl -> ShM IncludeSummary
summariseInclude ldecl@(L _ IncludeDecl { idUnitName = L _ name
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

    -- TODO: more utility functions here... stop UnitKey<->ShUnitKey
    -- bouncing
    pk0 <- liftIO $ newUnitKey' dflags (shcShUnitKey ipkg)
    pk <- liftIO $ renameHoleUnitKey dflags hsubst pk0
    -- NB: Rely on invariant that indefShUnitKey is FULLY indefinite
    fh <- liftIO $ unitKeyFreeHoles dflags pk

    return IncludeSummary {
        is_ldecl = ldecl,
        -- Not substituted yet, we will do this shortly
        is_pkg_key = pk,
        is_provides = provs,
        is_requires = fh
        }

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
            , let out_keys = mapMaybe lookup_key (uniqSetToList (is_requires s)) ]



{-
************************************************************************
*                                                                      *
                        Shaping monads
*                                                                      *
************************************************************************
-}

data ShGblEnv = ShGblEnv {
    shg_pk :: UnitKey,
    shg_name :: UnitName,
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

setUnitName :: UnitName -> ShM a -> ShM a
setUnitName name thing_inside
    = updGblEnv (\env -> env { shg_name = name } ) thing_inside

type ShM a = TcRnIf ShGblEnv ShLclEnv a

-- getErrsVar
getErrsVarSh :: ShM (IORef Messages)
getErrsVarSh = fmap shl_errs getLclEnv

shPkgKey :: ShM UnitKey
shPkgKey = fmap shg_pk getGblEnv

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

addShapeToEnv :: UnitName -> (Shape, UnitKey) -> ShM ()
addShapeToEnv name (sh, pk) =
    updateEps_ (\eps -> eps { eps_EST = Map.insert name (sh, pk) (eps_EST eps) })

lookupPackageShape :: UnitName -> ShM (Shape, UnitKey)
lookupPackageShape unit_name = do
    {-
    eps <- getEps
    dflags <- getDynFlags
    case Map.lookup unit_name (eps_EST eps) of
    -}
    unit <- lookupUnit unit_name
    convertIndefiniteUnitConfig unit

convertIndefiniteUnitConfig :: ShapeConfig -> ShM (Shape, UnitKey)
convertIndefiniteUnitConfig unit = do
    hsc_env <- getTopEnv
    dflags <- getDynFlags
    let shpk = shcShUnitKey unit
    pk <- liftIO $ newUnitKey' dflags shpk
    provs <- T.forM (shcProvides unit) $ \mod -> do
                -- TODO: don't TYPECHECK the entire interface. Just
                -- read out the mi_exports
                mb_iface <- liftIO $ initIfaceCheck hsc_env (computeInterface (text "pkgconfig") False mod)
                case mb_iface of
                    Succeeded (iface, _) -> return (mod, mi_exports iface)
                    Failed err -> failSh err
    reqs <- fmap Map.fromList . forM (shcRequires unit) $ \modname -> do
                mb_iface <- liftIO $ initIfaceCheck hsc_env (computeInterface (text "pkgconfig") False (mkModule pk modname))
                case mb_iface of
                    Succeeded (iface, _) -> return (modname, mi_exports iface)
                    Failed err -> failSh err
    return (Shape provs reqs, pk)

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
    -- Step 1: Fill every requirement of 2 with the provided modules from 1
    -- (as well as any implicitly filled in modules from the outer package key)
    pk <- shPkgKey
    hsubst0 <- liftIO $ computeHoleSubst dflags pk (sh_provides sh1) (sh_requires sh2)
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
                idUnitName = L _ name,
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
        psh_requires = shUnitKeyFreeHoles (shcShUnitKey ipkg)
        }

mergePreShapes :: PreShape -> PreShape -> PreShape
mergePreShapes psh1 psh2 =
    PreShape {
        psh_provides = unionUniqSets (psh_provides psh1) (psh_provides psh2),
        psh_requires = unionUniqSets (psh_requires psh1)
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
shComputeUnitKey :: LHsUnit -> ShM ShUnitKey
shComputeUnitKey
    (L loc HsUnit { hsunitName = L _ name
                  , hsunitExports = Nothing -- XXX incomplete
                  , hsunitBody = decls })
    = setSrcSpanSh loc
    . setUnitName name $
      do dflags <- getDynFlags
         -- Pre-pass, to calculate the requirements
         psh <- foldM preshape emptyPreShape decls
         insts <- forM (uniqSetToList (psh_requires psh)) $ \modname -> do
                        -- TODO: unnecessarily monadic
                        let mod = mkModule holeUnitKey modname
                        return (modname, mod)
         let uid = IndefiniteUnitId (thisIPID dflags) (Just name)
         liftIO $ newShUnitKey dflags uid insts
shComputeUnitKey
    (L _ HsUnit { hsunitName = _
                  , hsunitExports = Just _
                  , hsunitBody = _ }) = panic "Exports not implemented"

-- | Shape a 'HsUnit'.
shPackage :: UnitKey -> LHsUnit -> ShM Shape
shPackage pk
    lunit@(L _loc HsUnit { hsunitName = L _ name
                        , hsunitExports = Nothing -- XXX incomplete
                        , hsunitBody = decls })
    = setPackageSh lunit .
      setUnitKeySh pk $ do
         -- Shape each declaration, building the shape
         sh <- foldM shPkgDecl emptyShape decls
         -- Calculate holes and the package key, and substitute THIS
         -- Dump the shape if we're asked to
         shDump (vcat [ text "/--- Shape for" <+> ppr name
                      , ppr sh
                      , text "\\---"
                      ])
         -- Store the shape in the EPS
         addShapeToEnv name (sh, pk)
         -- TODO Write the shape in a package interface file
         return sh
shPackage _
    (L _ HsUnit { hsunitName = _
                  , hsunitExports = Just _
                  , hsunitBody = _ }) = panic "exports not implemented"

shPkgDecl :: Shape -> LHsUnitDecl -> ShM Shape
shPkgDecl sh (L loc (DeclD dt lmodname@(L _ modname) mb_hsmod)) =
    setSrcSpanSh loc $ do
    pk <- shPkgKey
    let outer_m = mkModule pk modname
        hsc_src = case dt of
                    ModuleD    -> HsSrcFile
                    SignatureD -> HsBootFile
    dflags <- getDynFlags
    -- Usually will become HOLE:H for holes, but not necessarily!
    inner_m <- liftIO $ canonicalizeModule dflags outer_m
    summary <- summariseDecl dflags hsc_src lmodname mb_hsmod
    hsc_env <- getTopEnv
    parsed_mod <- liftIO $ hscParse hsc_env summary
    let hsmod@(L inner_loc _) = hpm_module parsed_mod
    avails <- liftTcToSh hsc_src (TopModule { topModSemantic = inner_m
                                            , topModIdentity = outer_m }) inner_loc $
        updGblEnv (\tcg_env -> tcg_env { tcg_ifaces = mkShIfaces sh
                                       , tcg_shaping = True } ) $
        shModule hsmod
    mergeShapes sh (mkDeclShape dt modname outer_m avails)
shPkgDecl sh (L loc (IncludeD IncludeDecl{
                idUnitName = L _ name,
                idInclSpec = ispec
              })) =
    setSrcSpanSh loc $ do
    (sh', pk') <- lookupPackageShape name
    hsc_env <- getTopEnv
    (incl_sh, _) <- liftIO $ renameShape hsc_env ispec (sh', pk')
    mergeShapes sh incl_sh

-- First, compute a ShHoleSubst based on the requirement renaming;
-- e.g. 'include p requires (A as B)' results in a ShHoleSubst from
-- A to HOLE:B.  (NB: the ShFreeHoles is degenerate.)
-- NB: We assume that the incl spec is valid and linear, which
-- is checked during pre-shaping
renameShape :: HscEnv -> Maybe LInclSpec -> (Shape, UnitKey) -> IO (Shape, UnitKey)
renameShape _ Nothing sh_pk = return sh_pk
renameShape hsc_env
            (Just (L _ InclSpec{ isProvides = rn_provs, isRequires = rn_reqs }))
            (Shape{ sh_provides = provs, sh_requires = reqs }, pk)
    = do let dflags = hsc_dflags hsc_env
         hsubst <- mkShHoleSubst dflags
                   (foldl' (\m (L _ rn) ->
                               addToUFM m
                                   (renameFrom rn)
                                   (mkModule holeUnitKey
                                             (renameTo rn)))
                           emptyUFM rn_reqs)
         let renameProvides Nothing orig = return orig
             -- ^-- this is wrong, we need to rename here too
             renameProvides (Just rns) orig =
                let go new (L _ rn)
                        | Just (m, avails) <- Map.lookup (renameFrom rn) orig
                        = do m' <- renameHoleModule dflags hsubst m
                             avails' <- mapM (renameHoleAvailInfo hsc_env hsubst) avails
                             return $ Map.insert (renameTo rn) (m', avails') new
                        | otherwise = panic "renameProvides"
                in foldM go Map.empty rns
         provs' <- renameProvides rn_provs provs
         let renameRequires rns orig0 = do
                orig <- T.forM orig0 $ mapM (renameHoleAvailInfo hsc_env hsubst)
                let go orig (L _ rn)
                        | Just e <- Map.lookup (renameFrom rn) orig
                        = Map.insert (renameTo rn) e (Map.delete (renameFrom rn) orig)
                        | otherwise = panic "renameRequires"
                return (foldl' go orig rns)
         reqs' <- renameRequires rn_reqs reqs
         pk' <- liftIO $ renameHoleUnitKey dflags hsubst pk
         return (Shape{ sh_provides = provs', sh_requires = reqs' }, pk')

mkDeclShape :: HsDeclType -> ModuleName -> Module -> [AvailInfo] -> Shape
mkDeclShape ModuleD = mkModuleShape
mkDeclShape SignatureD = mkSignatureShape

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
    tcg_env <- rnExports (isJust maybe_mod) export_ies tcg_env ;

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
                     return (modname, mkShIface (mkModule holeUnitKey modname) avails)

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

{-
************************************************************************
*                                                                      *
                        Build planning
*                                                                      *
************************************************************************
-}

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
    UnitName unit_fs <- fmap shg_name getGblEnv
    hsc_env <- getTopEnv
    -- Unfortunately, we have to define a "fake" location in
    -- order to appease the various code which uses the file
    -- name to figure out where to put, e.g. object files.
    -- To add insult to injury, we don't even actually use
    -- these filenames to figure out where the hi files go.
    -- A travesty!  Fix this some day...
    location <- liftIO $ mkHomeModLocation2 dflags modname
                             (unpackFS unit_fs </>
                              moduleNameSlashes modname)
                             (case hsc_src of
                                  HsSrcFile -> "hs"
                                  HsBootFile -> "hs-boot"
                                  HsBootMerge -> panic "hsModuleToModSummary panic")
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

    -- So that Finder can find it, even though it doesn't exist...
    this_mod <- liftIO $ addHomeModuleToFinder hsc_env modname location
    return ModSummary {
            ms_mod = this_mod,
            ms_hsc_src = hsc_src,
            ms_location = location,
            ms_hspp_file = "(inline file)",
            -- VERY IMPORTANT, because tc will ignore ModSummary this_mod
            ms_hspp_opts = dflags {
                thisPackage = {- if hsc_src == HsigFile
                                then holeUnitKey
                                else -} moduleUnitKey this_mod
                },
            ms_hspp_buf = Nothing,
            ms_srcimps = src_idecls,
            ms_textual_imps = implicit_imports ++ ordinary_imps,
            ms_merge_imps = (False, []),
            -- This is our hack to get the parse tree to the right spot
            ms_parsed_mod = Just (HsParsedModule {
                    hpm_module = hsmod,
                    hpm_src_files = [], -- TODO if we preprocessed it
                    hpm_annotations = (Map.empty, Map.empty) -- error "hsModuleToModsummary: no apiAnns (FIXME)" -- BOGUS
                }),
            ms_hs_date = time,
            ms_obj_date = Nothing, -- TODO do this, but problem: hi_timestamp is BOGUS
            ms_iface_date = hi_timestamp
        }
