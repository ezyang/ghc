{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE CPP #-}
module Shaping (
    -- * Shaping monad
    initShM,
    ShM,
    -- * Shaping
    shPackage,
    shComputePackageKey,
    -- * Other stuff
    mergeAvails,
    mergeModIfaceForImport,
    mergeModIface,
    mergeModIface',
) where

#include "HsVersions.h"

import BackpackSyn
import ShPackageKey
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
import IfaceSyn

import HscMain
import HsSyn
import IOEnv
import RdrName
import Finder
import HeaderInfo
import RnNames
import NameEnv
import TcRnMonad
import Bag
import MkIface
import UniqSet
import Util
import Fingerprint
import FastString
import GhcMake

import System.FilePath
import Data.List
import Data.Either
import Data.IORef
import Control.Monad
import qualified Data.Map as Map
import qualified Data.Traversable as T

{-
************************************************************************
*                                                                      *
                        Shaping monads
*                                                                      *
************************************************************************
-}

data ShGblEnv = ShGblEnv {
    shg_pk :: PackageKey,
    shg_name :: PackageName,
    shg_filename :: FilePath
    }
data ShLclEnv = ShLclEnv {
    shl_loc :: RealSrcSpan, -- Source span
    shl_errs :: TcRef Messages
    }

getSrcSpanSh :: ShM SrcSpan
getSrcSpanSh = do
    env <- getLclEnv
    return (RealSrcSpan (shl_loc env))

-- setSrcSpan
setSrcSpanSh :: SrcSpan -> ShM a -> ShM a
setSrcSpanSh (RealSrcSpan real_loc) thing_inside
    = updLclEnv (\env -> env { shl_loc = real_loc }) thing_inside
setSrcSpanSh (UnhelpfulSpan _) thing_inside = thing_inside

type ShM a = TcRnIf ShGblEnv ShLclEnv a

-- getErrsVar
getErrsVarSh :: ShM (IORef Messages)
getErrsVarSh = fmap shl_errs getLclEnv

shPkgKey :: ShM PackageKey
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

initShM :: HscEnv -> FilePath -> PackageName -> ShM a -> IO (Messages, Maybe a)
initShM hsc_env filename name do_this = do
    errs_var <- newIORef emptyMessages
    let gbl_env = ShGblEnv {
                -- Will get filled in soon
                shg_pk = panic "shg_pk: not initialized",
                shg_name = name,
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

addShapeToEnv :: PackageName -> (Shape, PackageKey) -> ShM ()
addShapeToEnv name (sh, pk) =
    updateEps_ (\eps -> eps { eps_EST = Map.insert name (sh, pk) (eps_EST eps) })

lookupPackageShape :: PackageName -> ShM (Maybe (Shape, PackageKey))
lookupPackageShape name = do
    eps <- getEps
    return (Map.lookup name (eps_EST eps))

{-
************************************************************************
*                                                                      *
                        Merging
*                                                                      *
************************************************************************
-}

-- There are two parts to the substitution: the hole subst and the name subst
mergeShapes :: ([LShPkgDecl], Shape) -> Shape -> ShM ([LShPkgDecl], Shape)
mergeShapes (decls, sh1@(Shape mod_sh1 avail_sh1)) sh2@(Shape mod_sh2 avail_sh2) = do
    hsc_env <- getTopEnv
    let avail_provs1 = sh_avail_provides avail_sh1
        avail_provs2 = sh_avail_provides avail_sh2
        avail_reqs1  = sh_avail_requires avail_sh1
        avail_reqs2  = sh_avail_requires avail_sh2
    -- 1. Do the module substitution (but not on names)
    ((decls', mod_sh), hsubst) <- mergeModShapes' (decls, mod_sh1) mod_sh2
    -- ... Unify the names
    let nsubst0 = emptyNameEnv
    nsubst0 <- maybeErrSh
                -- TODO: make this error message better
                -- by reporting the specific AvailInfos that failed merging
                (vcat [ text "Failed to unify when filling requirements:"
                      , hang (text "Context:") 2 (ppr sh1)
                      , hang (text "Merging shape:") 2  (ppr sh2)])
            $ foldM (\subst (as1, as2) ->
                        uAvailInfos subst as1 as2) nsubst0
                    (Map.intersectionWith (,) avail_provs1 avail_reqs2)
    -- Step 2: Check that, for any requirement we filled, that it is provided
    -- (NB: we can test based on OccNames)
    forM_ (Map.toList (Map.intersectionWith (,) avail_provs1 avail_reqs2)) $
        \(modname, (prov_as, req_as)) ->
            let mkOS as = mkUniqSet $ do a <- as
                                         n <- availNames a
                                         return (nameOccName n)
                missing = minusUniqSet (mkOS req_as) (mkOS prov_as)
            in if isEmptyUniqSet missing
                then return ()
                -- TODO this error message is pretty terrible
                -- (want to at least report want the provision at modname is)
                else failSh $ vcat [ text "Cannot use instantiate hole at" <+> ppr modname
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
              (Map.intersectionWith (,) avail_reqs1 avail_reqs2)
    -- This gives us a substitution
    subst <- liftIO $ mkShSubst hsc_env hsubst nsubst0
    -- Step 4: Merge everything together, substituting along the way
    let doSubst = liftIO . substAvailInfo hsc_env subst
    new_avail_provs <- T.mapM (mapM doSubst) (Map.union avail_provs1 avail_provs2)
    new_avail_reqs1 <- T.mapM (mapM doSubst) avail_reqs1
    new_avail_reqs2 <- T.mapM (mapM doSubst) (Map.difference avail_reqs2 avail_provs1)
    let new_avail_reqs = Map.unionWith mergeAvails new_avail_reqs1 new_avail_reqs2
    return (decls', Shape mod_sh (AvailShape new_avail_provs new_avail_reqs))

-- Assumes the AvailInfos have already been unified
mergeAvails :: [AvailInfo] -> [AvailInfo] -> [AvailInfo]
mergeAvails as1 as2 =
    let mkNE as = mkNameEnv [(availName a, a) | a <- as]
    in nameEnvElts (plusNameEnv_C plusAvail (mkNE as1) (mkNE as2))

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

preshape :: PreShape -> LHsPkgDecl -> ShM PreShape
preshape psh (L _ decl) = preshape' psh decl

preshape' :: PreShape -> HsPkgDecl -> ShM PreShape
preshape' psh (DeclD ModuleD (L _ modname) _) = -- HSigfile
    return (mergePreShapes psh (mkModulePreShape modname))
preshape' psh (DeclD SignatureD (L _ modname) _) =
    return (mergePreShapes psh (mkSignaturePreShape modname))
preshape' psh (IncludeD (IncludeDecl{
                idPackageName = L _ name,
                idInclSpec = ispec
              })) = do
    mb_shape <- lookupPackageShape name
    case mb_shape of
        Nothing -> failSh (text "Could not find package" <+> ppr name)
        Just (Shape sh' _, _) -> fmap (mergePreShapes psh) (renamePreShape ispec (shapeToPreShape sh'))

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

shapeToPreShape :: ModShape -> PreShape
shapeToPreShape ModShape { sh_mod_provides = provs, sh_mod_requires = reqs } =
    PreShape {
        psh_provides = mkUniqSet (Map.keys provs),
        psh_requires = mkUniqSet (Map.keys reqs)
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

-- | Compute package key of a 'HsPackage'
shComputePackageKey :: Bool -> LHsPackage -> ShM PackageKey
shComputePackageKey
    is_exe
    (L loc HsPackage { hspkgName = L _ name
                     , hspkgExports = Nothing -- XXX incomplete
                     , hspkgBody = decls })
    = setSrcSpanSh loc $
      do dflags <- getDynFlags
         -- Pre-pass, to calculate the requirements
         psh <- foldM preshape emptyPreShape decls
         insts <- forM (uniqSetToList (psh_requires psh)) $ \modname -> do
                        -- TODO: unnecessarily monadic
                        let mod = mkModule holePackageKey modname
                        return (modname, mod)
         when (not (null insts) && is_exe) $
            failSh (text "Main package cannot have holes" <+> ppr (map fst insts))
         if is_exe
            then return mainPackageKey
            else liftIO $ newPackageKey dflags name (thisLibraryName dflags) insts

-- | Shape a 'HsPackage'.
shPackage :: PackageKey -> LHsPackage -> ShM ([LShPkgDecl], Shape)
shPackage pk
    (L loc HsPackage { hspkgName = L _ name
                     , hspkgExports = Nothing -- XXX incomplete
                     , hspkgBody = decls })
    = setSrcSpanSh loc .
      updGblEnv (\shg -> shg { shg_pk = pk }) $ do
         setThisPackageM pk $ do
         -- Shape each declaration, building the shape
         (rev_decls, sh) <- foldM shPkgDecl ([], emptyShape) decls
         let decls = reverse rev_decls
         -- Calculate holes and the package key, and substitute THIS
         -- Dump the shape if we're asked to
         shDump (vcat [ text "/--- Shape for" <+> ppr name
                      , ppr sh
                      , vcat (map ppr decls)
                      , text "\\---"
                      ])
         -- Store the shape in the EPS
         addShapeToEnv name (sh, pk)
         -- TODO Write the shape in a package interface file
         return (decls, sh)

shPkgDecl :: ([LShPkgDecl], Shape) -> LHsPkgDecl -> ShM ([LShPkgDecl], Shape)
shPkgDecl (decls, sh) (L loc (DeclD dt lmodname@(L _ modname) mb_hsmod)) =
    setSrcSpanSh loc $ do
    pk <- shPkgKey
    -- canonicalizeModule
    let outer_m = mkModule pk modname
        hsc_src = case dt of
                    ModuleD    -> HsSrcFile
                    SignatureD -> HsigFile
    dflags <- getDynFlags
    -- Usually will become HOLE:H for holes, but not necessarily!
    m <- liftIO $ canonicalizeModule dflags outer_m
    {-
    let m = case dt of
                ModuleD -> outer_m
                SignatureD -> mkModule holePackageKey modname
                -}
    summary <- summariseDecl dflags hsc_src m lmodname mb_hsmod
    hsc_env <- getTopEnv
    parsed_mod <- liftIO $ hscParse hsc_env summary
    let hsmod@(L inner_loc _) = hpm_module parsed_mod
    avails <- liftTcToSh hsc_src m inner_loc $
        updGblEnv (\tcg_env -> tcg_env { tcg_ifaces = mkShIfaces sh
                                       , tcg_shaping = True } ) $
        shModule hsmod
    mergeShapes (L loc (ShDecl summary) : decls, sh)
                (mkDeclShape dt modname outer_m avails)
shPkgDecl (decls, sh) (L loc (IncludeD IncludeDecl{
                idPackageName = L _ name,
                idInclSpec = ispec
              })) =
    setSrcSpanSh loc $ do
    mb_shape <- lookupPackageShape name
    case mb_shape of
        Nothing -> failSh (text "Could not find package" <+> ppr name)
        Just (sh', pk') -> do
            hsc_env <- getTopEnv
            (incl_sh@(Shape mod_sh _), incl_pk)
                <- liftIO $ renameShape hsc_env ispec (sh', pk')
            mergeShapes (L loc (shInclude incl_pk mod_sh) : decls, sh) incl_sh

-- First, compute a ShHoleSubst based on the requirement renaming;
-- e.g. 'include p requires (A as B)' results in a ShHoleSubst from
-- A to HOLE:B.  (NB: the ShFreeHoles is degenerate.)
-- NB: We assume that the incl spec is valid and linear, which
-- is checked during pre-shaping
renameShape :: HscEnv -> Maybe LInclSpec -> (Shape, PackageKey) -> IO (Shape, PackageKey)
renameShape _ Nothing sh_pk = return sh_pk -- short circuit
renameShape hsc_env
            ispec@(Just (L _ InclSpec{ isProvides = rn_provs, isRequires = rn_reqs }))
            (Shape mod_shape avail_shape, pk)
    = do -- Rename ModShape
         (mod_shape', hsubst) <- renameModShape' hsc_env ispec mod_shape
         -- Rename AvailShape
         let renameProvides Nothing orig = return orig
             renameProvides (Just rns) orig =
                let go new (L _ rn)
                        | Just avails <- Map.lookup (renameFrom rn) orig
                        = do avails' <- mapM (renameHoleAvailInfo hsc_env hsubst) avails
                             return $ Map.insert (renameTo rn) avails' new
                        | otherwise = panic "renameProvides2"
                in foldM go Map.empty rns
         provs' <- renameProvides rn_provs (sh_avail_provides avail_shape)
         let renameRequires rns orig0 = do
                orig <- T.forM orig0 $ mapM (renameHoleAvailInfo hsc_env hsubst)
                let go orig (L _ rn)
                        | Just e <- Map.lookup (renameFrom rn) orig
                        = Map.insert (renameTo rn) e (Map.delete (renameFrom rn) orig)
                        | otherwise = panic "renameRequires2"
                return (foldl' go orig rns)
         reqs' <- renameRequires rn_reqs (sh_avail_requires avail_shape)
         -- Rename the package key
         let dflags = hsc_dflags hsc_env
         (pk', _) <- liftIO $ renameHolePackageKey dflags hsubst pk
         -- Roll it up
         return (Shape mod_shape' (AvailShape provs' reqs'), pk')

-- Based off of tcRnModuleTcRnM
shModule :: Located (HsModule RdrName) -> ShModM [AvailInfo]
shModule (L loc (HsModule maybe_mod export_ies
                          import_decls local_decls _mod_deprec
                          _maybe_doc_hdr)) = do
    -- NB: repeated setGblEnv seems goofy but it's necessary!
    tcg_env <- getGblEnv

    let prel_imp_loc = loc -- TODO type-checker gets this from prel_imp_loc
        this_mod = tcg_mod tcg_env

    setGblEnv tcg_env { tcg_mod_name = maybe_mod } $ do

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
    (tcg_env, _rn_decls) <- rnTopSrcDecls Nothing first_group
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
mkShIfaces sh = listToUFM (provs ++ reqs)
    where provs = do (modname, (m, avails)) <- Map.toList (shapeProvides sh)
                     return (modname, mkShIface m avails)
          -- For now, all requirements are visible.
          -- NB: This works slightly differently from how type-checking
          -- programs the interfaces.
          reqs  = do (modname, (_, avails)) <- Map.toList (shapeRequires sh)
                     return (modname, mkShIface (mkModule holePackageKey modname) avails)

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

mkDeclShape :: HsDeclType -> ModuleName -> Module -> [AvailInfo] -> Shape
mkDeclShape t modname mod as = Shape (mkDeclModShape t modname mod) (mkDeclAvailShape t modname as)

mkDeclModShape :: HsDeclType -> ModuleName -> Module -> ModShape
mkDeclModShape ModuleD modname mod = emptyModShape { sh_mod_provides = Map.singleton modname mod }
mkDeclModShape SignatureD modname mod = emptyModShape { sh_mod_requires = Map.singleton modname [mod] }

mkDeclAvailShape :: HsDeclType -> ModuleName -> [AvailInfo] -> AvailShape
mkDeclAvailShape ModuleD modname as = emptyAvailShape { sh_avail_provides = Map.singleton modname as }
mkDeclAvailShape SignatureD modname as = emptyAvailShape { sh_avail_requires = Map.singleton modname as }

{-
************************************************************************
*                                                                      *
                        Merging ModIfaces
*                                                                      *
************************************************************************
-}

mergeModIface' :: [(Fingerprint, IfaceDecl)] -> ModIface -> ModIface -> ModIface
mergeModIface' merged_decls iface1 iface2 =
    let fixities = mergeFixities (mi_fixities iface1) (mi_fixities iface2)
        warns = mergeWarnings (mi_warns iface1) (mi_warns iface2)
    in ASSERT2( mi_module iface1 == mi_module iface2, ppr (mi_module iface1) <+> ppr (mi_module iface2) )
       (emptyModIface (mi_module iface1)) {
        -- Fake in-memory interfaces always have empty sig-of
        mi_sig_of = Nothing,

        -- The merge proper
        mi_decls     = merged_decls,
        mi_anns      = mi_anns iface1 ++ mi_anns iface2,
        -- TODO filter out duplicates
        mi_exports   = mergeAvails (mi_exports iface1) (mi_exports iface2),
        mi_insts     = mi_insts iface1 ++ mi_insts iface2,
        mi_fam_insts = mi_fam_insts iface1 ++ mi_fam_insts iface2,
        mi_rules     = mi_rules iface1 ++ mi_rules iface2,

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
        mi_usages    = panic "No mi_usages in HOLE"
    }

-- MaybeErr is a bad warning because we want to report as
-- many errors as possible
-- TODO totally unclear what fingerprints should be, so omitted for now
mergeIfaceDecls :: [IfaceDecl]
                -> [IfaceDecl]
                -> MaybeErr
                    -- on error, we want to report the two IfaceDecls
                    -- for pretty printing, as well as a little description
                    -- why they were different.
                    [(IfaceDecl, IfaceDecl, SDoc)]
                    [IfaceDecl]
mergeIfaceDecls ds1 ds2 =
    let mkE ds = listToUFM [ (ifName d, d) | d <- ds ]
        (bad, ok) = partitionEithers
                  . map (\(d1,d2) -> case mergeIfaceDecl d1 d2 of
                                        Succeeded d -> Right d
                                        Failed err -> Left (d1, d2, err))
                  . eltsUFM
                  $ intersectUFM_C (,) (mkE ds1) (mkE ds2)
    in case bad of
              -- HACK using right bias
        [] -> Succeeded (eltsUFM (plusUFM (mkE ds1) (plusUFM (mkE ds2) (mkE ok))))
        _ -> Failed bad

mergeModIface :: ModIface -> ModIface -> MaybeErr [(IfaceDecl, IfaceDecl, SDoc)] ModIface
mergeModIface iface1 iface2 = {-pprTrace "mergeModIface" (ppr (mi_module iface1)) $ -} do
    merged_decls <- fmap (map ((,) fingerprint0))
                  $ mergeIfaceDecls (map snd (mi_decls iface1))
                               (map snd (mi_decls iface2))
    return (mergeModIface' merged_decls iface1 iface2)

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

{-
************************************************************************
*                                                                      *
                        Build planning
*                                                                      *
************************************************************************
-}

summariseDecl :: DynFlags
              -> HscSource
              -> Module
              -> Located ModuleName
              -> Maybe (Located (HsModule RdrName))
              -> ShM ModSummary
summariseDecl dflags hsc_src mod _ (Just hsmod) = hsModuleToModSummary dflags hsc_src mod hsmod
summariseDecl _ hsc_src mod lmodname Nothing
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
            Nothing -> failSh (text "module" <+> ppr mod <+> text "is a package module")
            Just (Left err) -> reportErrorSh err >> failM
            Just (Right summary) -> return summary

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
                     -> Module
                     -> Located (HsModule RdrName)
                     -> ShM ModSummary
hsModuleToModSummary dflags hsc_src this_mod
                     hsmod = do
    -- Sort of the same deal as in DriverPipeline's getLocation
    pn <- fmap shg_name getGblEnv
    let modname = moduleName this_mod
    -- Unfortunately, we have to define a "fake" location in
    -- order to appease the various code which uses the file
    -- name to figure out where to put, e.g. object files.
    -- To add insult to injury, we don't even actually use
    -- these filenames to figure out where the hi files go.
    -- A travesty!  Fix this some day...
    location <- liftIO $ mkHomeModLocation2 dflags modname
                             (unpackFS (packageNameFS pn) </>
                              moduleNameSlashes modname)
                             (case hsc_src of
                                  HsSrcFile -> "hs"
                                  HsBootFile -> "hs-boot"
                                  HsigFile -> "hsig")
    -- This duplicates a pile of logic in GhcMake
    env <- getGblEnv
    time <- liftIO $ getModificationUTCTime (shg_filename env)
    hi_timestamp <- liftIO $ modificationTimeIfExists (ml_hi_file location)
    return ModSummary {
            ms_mod = this_mod,
            ms_hsc_src = hsc_src,
            ms_location = location,
            ms_hspp_file = "(inline file)",
            -- VERY IMPORTANT, because tc will ignore ModSummary this_mod
            ms_hspp_opts = dflags {
                thisPackage = {- if hsc_src == HsigFile
                                then holePackageKey
                                else -} modulePackageKey this_mod
                },
            ms_hspp_buf = Nothing,
            -- TODO: These have to be filled in to do recompilation checking
            ms_srcimps = [], -- error "hsModuleToModSummary: no ms_srcimps",
            ms_textual_imps = [], -- error "hsModuleToModSummary: no ms_textual_imps",
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

{-
************************************************************************
*                                                                      *
                        Planner
*                                                                      *
************************************************************************
-}

mergeModShapes' :: ([LShPkgDecl], ModShape)
               -> ModShape
               -> ShM (([LShPkgDecl], ModShape), ShHoleSubst)
mergeModShapes' (decls, sh1) sh2 = do
    dflags <- getDynFlags
    -- Fill every requirement of 2 with the provided modules from 1
    hsubst0 <- liftIO $ computeHoleSubst dflags (sh_mod_provides sh1) (sh_mod_requires sh2)
    hsubst <- liftIO $ fixShHoleSubst dflags hsubst0
    -- Do the substitution
    let provs0 = Map.union (sh_mod_provides sh1) (sh_mod_provides sh2)
        doHoleSubst = liftIO . renameHoleModule dflags hsubst
    provs <- T.mapM doHoleSubst provs0
    let doReqSubst = mapM doHoleSubst
    reqs1 <- T.mapM doReqSubst (sh_mod_requires sh1)
    reqs2 <- T.mapM doReqSubst (Map.difference (sh_mod_requires sh2) (sh_mod_provides sh1))
    let reqs = Map.unionWith (++) reqs1 reqs2
    -- Substitute the decls
    let doDeclSubst (L loc (ShDecl ms)) = do
            mod' <- liftIO $ renameHoleModule dflags hsubst (ms_mod ms)
            return (L loc (ShDecl ms { ms_mod = mod' }))
        doDeclSubst (L loc (ShInclude pk (ModShape provs reqs))) = do
            (pk', _) <- liftIO $ renameHolePackageKey dflags hsubst pk
            provs' <- T.mapM doHoleSubst provs
            reqs' <- T.mapM doReqSubst reqs
            return (L loc (ShInclude pk' (ModShape provs' reqs')))
    decls' <- mapM doDeclSubst decls
    return ((decls', ModShape provs reqs), hsubst)

shInclude :: PackageKey -> ModShape -> ShPkgDecl
shInclude pk mod_sh = ShInclude pk mod_sh

renameModShape' :: HscEnv
               -> Maybe LInclSpec
               -> ModShape
               -> IO (ModShape, ShHoleSubst)
renameModShape' _ Nothing mod_sh = return (mod_sh, emptyUFM)
renameModShape' hsc_env
               (Just (L _ InclSpec{ isProvides = rn_provs, isRequires = rn_reqs }))
               (ModShape provs reqs) = do
    let dflags = hsc_dflags hsc_env
    hsubst <- mkShHoleSubst dflags
              (foldl' (\m (L _ rn) ->
                          addToUFM m
                              (renameFrom rn)
                              (mkModule holePackageKey
                                        (renameTo rn)))
                      emptyUFM rn_reqs)
    let renameProvides Nothing orig = return orig
        renameProvides (Just rns) orig =
           let go new (L _ rn)
                   | Just m <- Map.lookup (renameFrom rn) orig
                   = do m' <- renameHoleModule dflags hsubst m
                        return $ Map.insert (renameTo rn) m' new
                   | otherwise = panic "renameProvides"
           in foldM go Map.empty rns
    provs' <- renameProvides rn_provs provs
    let renameRequires rns orig0 = do
           orig <- T.forM orig0 $ mapM (renameHoleModule dflags hsubst)
           let go orig (L _ rn)
                   | Just e <- Map.lookup (renameFrom rn) orig
                   = Map.insert (renameTo rn) e (Map.delete (renameFrom rn) orig)
                   | otherwise = panic "renameRequires"
           return (foldl' go orig rns)
    reqs' <- renameRequires rn_reqs reqs
    return (ModShape{ sh_mod_provides = provs', sh_mod_requires = reqs' }, hsubst)
