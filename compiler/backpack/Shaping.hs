{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE CPP #-}
module Shaping (
    -- * Shaping monad
    initShM,
    -- * Shaping
    shPackage,
) where

#include "HsVersions.h"

import BackpackSyn
import ShPackageKey
import ShUnify

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

import HsSyn
import IOEnv
import RdrName
import HeaderInfo
import RnNames
import NameEnv
import TcRnMonad
import Bag
import MkIface
import UniqSet

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
    shg_pk :: PackageKey
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

liftTcToSh :: HscSource -> Module -> RealSrcSpan -> TcM r -> ShM r
liftTcToSh hsc_src mod loc do_this = do
    hsc_env <- getTopEnv
    (msgs, r) <- liftIO $ initTc hsc_env hsc_src False mod loc do_this
    addMessagesSh msgs
    case r of
        Nothing -> failM
        Just x -> return x

initShM :: HscEnv -> RealSrcSpan -> ShM a -> IO (Messages, Maybe a)
initShM hsc_env loc do_this = do
    errs_var <- newIORef emptyMessages
    let gbl_env = ShGblEnv {
                -- Will get filled in soon
                shg_pk = panic "shg_pk: not initialized"
            }
        lcl_env = ShLclEnv {
                shl_loc = loc, -- Should be overridden soon
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
mergeShapes :: Shape -> Shape -> ShM Shape
mergeShapes sh1 sh2 = do
    hsc_env <- getTopEnv
    dflags <- getDynFlags
    -- Step 1: Fill every requirement of 2 with the provided modules from 1
    hsubst <- liftIO $ computeHoleSubst dflags (sh_provides sh1) (sh_requires sh2)
    -- ... and unify the names
    let nsubst0 = emptyNameEnv
    nsubst0 <- maybeErrSh
                -- TODO: make this error message better
                -- by reporting the specific AvailInfos that failed merging
                (vcat [ text "Failed to unify when filling requirements:"
                      , hang (text "Context:") 2 (ppr sh1)
                      , hang (text "Merging shape:") 2  (ppr sh2)])
            $ foldM (\subst ((_, as1), (_, as2)) ->
                        uAvailInfos subst as1 as2) nsubst0
                    (Map.intersectionWith (,) (sh_provides sh1) (sh_requires sh2))
    -- Step 2: Check that, for any requirement we filled, that it is provided
    -- (NB: we can test based on OccNames)
    forM_ (Map.toList (Map.intersectionWith (,) (sh_provides sh1) (sh_requires sh2))) $
        \(modname, ((m, prov_as), (_, req_as))) ->
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
            $ foldM (\subst ((_, as1), (_, as2)) -> uAvailInfos subst as1 as2) nsubst0
              (Map.intersectionWith (,) (sh_requires sh1) (sh_requires sh2))
    -- This gives us a substitution
    subst@(ShSubst hsubst _nsubst) <- liftIO $ mkShSubst hsc_env hsubst nsubst0
    -- Step 4: Merge everything together, substituting along the way
    let provs0 = Map.union (sh_provides sh1) (sh_provides sh2)
        doSubst = liftIO . substAvailInfo hsc_env subst
    provs <- T.mapM (\(m,  as) -> do (m', _) <- liftIO $ renameHoleModule dflags hsubst m
                                     as' <- mapM doSubst as
                                     return (m', as')) provs0
    let doReqSubst (ms, as) = do ms' <- liftIO $ mapM (fmap fst
                                                     . renameHoleModule dflags hsubst) ms
                                 as' <- mapM doSubst as
                                 return (ms', as')
    reqs1 <- T.mapM doReqSubst (sh_requires sh1)
    reqs2 <- T.mapM doReqSubst (Map.difference (sh_requires sh2) (sh_provides sh1))
    let reqs = Map.unionWith mergeRequirements reqs1 reqs2
    return Shape {
                sh_provides = provs,
                sh_requires = reqs
            }

mergeRequirements :: ([Module], [AvailInfo])
                  -> ([Module], [AvailInfo])
                  -> ([Module], [AvailInfo])
mergeRequirements (ms1, as1) (ms2, as2) =
    (ms1 ++ ms2, -- todo: dedupe
     mergeAvails as1 as2)

-- Assumes the AvailInfos have already been unified
mergeAvails :: [AvailInfo] -> [AvailInfo] -> [AvailInfo]
mergeAvails as1 as2 =
    let mkNE as = mkNameEnv [(availName a, a) | a <- as]
    in nameEnvElts (plusNameEnv_C plusAvail (mkNE as1) (mkNE as2))

{-
************************************************************************
*                                                                      *
                        Shaping environment
*                                                                      *
************************************************************************
-}

addShapeToEnv :: PackageName -> Shape -> ShM ()
addShapeToEnv name sh =
    updateEps_ (\eps -> eps { eps_EST = Map.insert name sh (eps_EST eps) })

lookupPackageShape :: PackageName -> ShM (Maybe Shape)
lookupPackageShape name = do
    eps <- getEps
    return (Map.lookup name (eps_EST eps))

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
preshape' psh (ModuleD (L _ HsModule { hsmodName = Just (L _ modname) })) =
    return (mergePreShapes psh (mkModulePreShape modname))
preshape' psh (ModuleD (L _ HsModule { hsmodName = Nothing })) =
    return psh
preshape' psh (SignatureD (L _ HsModule { hsmodName = Just (L _ modname) })) =
    return (mergePreShapes psh (mkSignaturePreShape modname))
preshape' psh (SignatureD (L _ HsModule { hsmodName = Nothing })) =
    return psh
preshape' psh (IncludeD (IncludeDecl{
                idPackageName = L _ name,
                idInclSpec = Nothing -- XXX
              })) = do
    mb_shape <- lookupPackageShape name
    case mb_shape of
        Nothing -> failSh (text "Could not find package" <+> ppr name)
        -- XXX renaming
        Just sh' -> return (mergePreShapes psh (shapeToPreShape sh'))

shapeToPreShape :: Shape -> PreShape
shapeToPreShape Shape { sh_provides = provs, sh_requires = reqs } =
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

-- | Shape a 'HsPackage'.
shPackage :: LHsPackage -> ShM (PackageKey, Shape)
shPackage
    -- TODO record location
    (L loc HsPackage { hspkgName = L _ name@(PackageName fs_name)
                      , hspkgExports = Nothing -- XXX incomplete
                      , hspkgBody = decls })
    = setSrcSpanSh loc $
      do dflags <- getDynFlags
         -- Pre-pass, to calculate the requirements
         psh <- foldM preshape emptyPreShape decls
         let insts = do m <- uniqSetToList (psh_requires psh)
                        return (m, mkModule holePackageKey m)
             spid = SourcePackageId fs_name -- XXX this is wrong
         pk <- liftIO $ newPackageKey dflags name spid insts
         updGblEnv (\shg -> shg { shg_pk = pk }) $ do
         setThisPackageM pk $ do
         -- Shape each declaration, building the shape
         sh <- foldM shPkgDecl emptyShape decls
         -- Calculate holes and the package key, and substitute THIS
         -- Dump the shape if we're asked to
         shDump (text "Shape for" <+> ppr name $$ ppr sh)
         -- Store the shape in the EPS
         addShapeToEnv name sh
         -- TODO Write the shape in a package interface file
         return (pk, sh)

shPkgDecl :: Shape -> LHsPkgDecl -> ShM Shape
shPkgDecl sh (L loc decl) = setSrcSpanSh loc $ shPkgDecl' sh decl

shPkgDecl' :: Shape -> HsPkgDecl -> ShM Shape

shPkgDecl' sh (ModuleD hsmod@(L (RealSrcSpan loc)
            HsModule { hsmodName = Just (L _ modname) })) = do
    pk <- shPkgKey
    let m = mkModule pk modname
    avails <- liftTcToSh HsSrcFile m loc $
        updGblEnv (\tcg_env -> tcg_env { tcg_ifaces = mkShIfaces sh } ) $
        shModule hsmod
    mergeShapes sh (mkModuleShape modname m avails)

shPkgDecl' _ (ModuleD (L _ HsModule { hsmodName = Nothing })) =
    failSh (text "Module declaration must have a name")
shPkgDecl' _ (ModuleD (L UnhelpfulSpan{} HsModule { hsmodName = Just (L _ modname)})) =
    failSh (text "Module declaration" <+> ppr modname <+> text "missing RealSrcSpan")

shPkgDecl' sh (SignatureD hsmod@(L (RealSrcSpan loc)
            HsModule { hsmodName = Just (L _ modname) })) = do
    pk <- shPkgKey
    avails <- liftTcToSh HsigFile (mkModule holePackageKey modname) loc $
        updGblEnv (\tcg_env -> tcg_env { tcg_ifaces = mkShIfaces sh } ) $
        shModule hsmod
    mergeShapes sh (mkSignatureShape modname (mkModule pk modname) avails)

shPkgDecl' _ (SignatureD (L _ HsModule { hsmodName = Nothing })) =
    failSh (text "Signature declaration must have a name")
shPkgDecl' _ (SignatureD (L UnhelpfulSpan{} HsModule { hsmodName = Just (L _ modname)})) =
    failSh (text "Signature declaration" <+> ppr modname <+> text "missing RealSrcSpan")

shPkgDecl' sh (IncludeD IncludeDecl{
                idPackageName = L _ name,
                idInclSpec = Nothing -- XXX
              }) = do
    mb_shape <- lookupPackageShape name
    case mb_shape of
        Nothing -> failSh (text "Could not find package" <+> ppr name)
        -- XXX renaming
        Just sh' -> mergeShapes sh sh'

mkModuleShape :: ModuleName -> Module -> [AvailInfo] -> Shape
mkModuleShape modname this_mod exports =
    emptyShape { sh_provides = Map.singleton modname (this_mod, exports) }

mkSignatureShape :: ModuleName -> Module -> [AvailInfo] -> Shape
mkSignatureShape modname this_mod exports =
    emptyShape { sh_requires = Map.singleton modname ([this_mod], exports) }

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
mkShIfaces :: Shape -> ModuleNameEnv [ModIface]
mkShIfaces sh = listToUFM (provs ++ reqs)
    where provs = do (modname, (m, avails)) <- Map.toList (sh_provides sh)
                     return (modname, [mkShIface m avails])
          -- For now, all requirements are visible.
          -- NB: This works slightly differently from how type-checking
          -- programs the interfaces.
          reqs  = do (modname, (_, avails)) <- Map.toList (sh_requires sh)
                     return (modname, [mkShIface (mkModule holePackageKey modname) avails])

-- | Create a fake 'ModIface' representing a 'Module' and its exports.
mkShIface :: Module -> [AvailInfo] -> ModIface
mkShIface this_mod exports =
    (emptyModIface this_mod) {
        mi_exports  = mkIfaceExports exports
        -- NB: mi_fixities not recorded here, so it's not possible
        -- to do full renaming since we won't reassociate infix ops
    }
