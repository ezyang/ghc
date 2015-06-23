{-# LANGUAGE CPP #-}

module ShUnify(
    -- * Overall substitution
    ShSubst(..),
    mkShSubst,
    substAvailInfo,

    -- * Hole substitutions
    ShHoleSubst,
    mkShHoleSubst,
    fixShHoleSubst,
    computeHoleSubst,
    substHoleAvailInfo,
    substHoleName,
    -- NOT exporting substHoleModule

    -- * Name substitutions
    ShNameSubst,
    substName,
    substNameAvailInfo,
    computeShapeSubst,
    setNameModule,

    -- * HOLE renaming
    renameHolePackageKey,
    renameHoleModule,
    renameHoleModule',
    renameHoleAvailInfo,

    -- * Unification
    uAvailInfos,

    -- * ModIface substitution
    rnModIface,
    ) where

#include "HsVersions.h"

import Shape
import ShPackageKey

import Outputable
import HscTypes
import Module
import UniqFM
import UniqSet
import Avail
import IfaceSyn

import DynFlags
import Name
import NameEnv
import TcRnMonad
import Util
import Fingerprint
import Unique

-- really, the global binder code should live in a different module
import {-# SOURCE #-} IfaceEnv

-- a bit vexing
import {-# SOURCE #-} LoadIface

import Data.List
import Control.Monad
import qualified Data.Map as Map
import qualified Data.Traversable as T

-- NB: substitution functions need 'HscEnv' since they need the name cache
-- to allocate new names if we change the 'Module' of a 'Name'

{-
************************************************************************
*                                                                      *
                        Shaping substitutions
*                                                                      *
************************************************************************
-}

-- Substitutions on 'Shape's. Similar to 'TvSubst' in Unify.
-- 'ShHoleSubst' could apply to range of 'ShNameSubst', but not
-- the *domain* (because the source always has form @HOLE:A.T@,
-- and the hole substitution does NOT apply here.)  A 'ShSubst'
-- is always idempotent.
data ShSubst
  = ShSubst ShHoleSubst -- substitutions on HOLE:A
            ShNameSubst -- substitutions on HOLE:A.T

-- Given non-idempotent hole and name substitutions, calculates
-- an idempotent hole+name substitution
mkShSubst :: HscEnv -> ShHoleSubst -> ShNameSubst -> IO ShSubst
mkShSubst hsc_env hsubst0 nsubst0 = do
    let dflags = hsc_dflags hsc_env
    hsubst <- fixShHoleSubst dflags hsubst0
    -- TODO: which order of applying the substitution is best?
    nsubst1 <- T.mapM (substHoleName hsc_env hsubst) nsubst0
    let nsubst = fixShNameSubst nsubst1
    return (ShSubst hsubst nsubst)

-- | Applies an idempotent 'ShSubst' to an 'AvailInfo'.
substAvailInfo :: HscEnv -> ShSubst -> AvailInfo -> IO AvailInfo
substAvailInfo hsc_env (ShSubst hsubst nsubst) a
    = substHoleAvailInfo hsc_env hsubst a >>=
      substNameAvailInfo hsc_env nsubst

{-
************************************************************************
*                                                                      *
                        Hole substitutions
*                                                                      *
************************************************************************
-}

-- | Substitution on @HOLE:A@.  'ShFreeHoles' says what the free
-- holes of the range of the substitution are.
type ShHoleSubst = ModuleNameEnv (Module, ShFreeHoles)

-- | Calculate a NON-IDEMPOTENT substitution from an arbitrary mapping.
mkShHoleSubst :: DynFlags -> ModuleNameEnv Module -> IO ShHoleSubst
mkShHoleSubst dflags subst = T.mapM addShFreeHoles subst
    where addShFreeHoles m = do
            free_holes <- calcModuleFreeHoles dflags m
            return (m, free_holes)

-- | Compute the NON-IDEMPOTENT substitution for filling some requirements
-- with some provisions.
computeHoleSubst :: DynFlags -> PackageKey -> ShProvides -> ShRequires -> IO ShHoleSubst
computeHoleSubst dflags pk provs reqs = do
    shpk <- lookupPackageKey dflags pk
    let shpk_map = case shpk of
                    ShPackageKey { shPackageKeyInsts = insts } -> Map.fromList insts
                    _ -> Map.empty
        proto_hsubst =
            foldl' (\m modname ->
            -- TODO Does order matter? Shouldn't...
                case Map.lookup modname provs of
                    Just (mod, _) -> addToUFM m modname mod
                    Nothing -> case Map.lookup modname shpk_map of
                                Just mod -> addToUFM m modname mod
                                Nothing -> m)
               emptyUFM (Map.keys reqs)
    mkShHoleSubst dflags proto_hsubst

-- | Find the idempotent fixed point of a non-idempotent substitution on
-- 'Module's.
fixShHoleSubst :: DynFlags -> ShHoleSubst -> IO ShHoleSubst
fixShHoleSubst dflags env0 = f env0 where
    f env | not fixpoint = f =<< T.mapM (renameHoleModule' dflags env . fst) (removeCycles env)
          | otherwise    = return env
        where fixpoint = isNullUFM (intersectUFM_C const in_scope env)
              in_scope = unionManyUniqSets (map snd (eltsUFM env))
              removeCycles m = filterUFM_Directly notCycle m
              notCycle u (m, _) = not (isHoleModule m && getUnique (moduleName m) == u)

-- | Substitutes holes in an 'AvailInfo'.  NOT suitable for renaming
-- when an include occurs (see 'renameHoleAvailInfo' instead).
-- See 'substHoleName' for more details.
substHoleAvailInfo :: HscEnv -> ShHoleSubst -> AvailInfo -> IO AvailInfo
substHoleAvailInfo hsc_env env (Avail n) = Avail `fmap` substHoleName hsc_env env n
substHoleAvailInfo hsc_env env (AvailTC n ns) = do
    n' <- substHoleName hsc_env env n
    ns' <- mapM (substHoleName hsc_env env) ns
    return (AvailTC n' ns')

-- | Substitutes holes in a 'Name'. NOT suitable for renaming when
-- an include occurs.
--
-- @p(A -> HOLE:A).T@ maps to @p(A -> q():A).T@ with @A -> q():A@;
-- this substitution has no effect on @HOLE:A.T@ (we expect this
-- to be substituted via a name substitution).
substHoleName :: HscEnv -> ShHoleSubst -> Name -> IO Name
substHoleName hsc_env env n = do
    let m = nameModule n
    m' <- substHoleModule (hsc_dflags hsc_env) env m
    if m == m'
        then return n
        else setNameModule hsc_env (Just m') n

-- | Substitutes holes in a 'Module', but not at the top level;
-- this is the behavior you want when substituting the 'nameModule' of a 'Name'.
-- @p(A -> HOLE:A):B@ maps to @p(A -> q():A):B@ with @A -> q():A@;
-- this substitution has no effect on @HOLE:A@.
substHoleModule :: DynFlags -> ShHoleSubst -> Module -> IO Module
substHoleModule dflags env m = fmap fst (substHoleModule' dflags env m)

-- | Like 'substHoleModule', but also returns the 'ShFreeHoles' of the resulting
-- 'Module'.
substHoleModule' :: DynFlags -> ShHoleSubst -> Module -> IO (Module, ShFreeHoles)
substHoleModule' dflags env m
  | not (isHoleModule m) = renameHoleModule' dflags env m
  | otherwise = return (m, unitUniqSet (moduleName m))

-- | Substitutes holes in a 'Module'.  NOT suitable for being called
-- directly on a 'nameModule'.
-- @p(A -> HOLE:A):B@ maps to @p(A -> q():A):B@ with @A -> q():A@;
-- similarly, @HOLE:A@ maps to @q():A@.
renameHoleModule :: DynFlags -> ShHoleSubst -> Module -> IO Module
renameHoleModule dflags env m = fmap fst (renameHoleModule' dflags env m)

renameHoleTopModule :: DynFlags -> ShHoleSubst -> TopModule -> IO TopModule
renameHoleTopModule dflags env (TopModule sem idm) = do
    sem' <- renameHoleModule dflags env sem
    idm' <- renameHoleModule dflags env idm
    return (TopModule sem' idm')

-- | Like 'renameHoleModule', but returns the 'ShFreeHoles' of the substituted
-- 'Module'.
renameHoleModule' :: DynFlags -> ShHoleSubst -> Module -> IO (Module, ShFreeHoles)
renameHoleModule' dflags env m
  | not (isHoleModule m) = do
        (pk, in_scope) <- renameHolePackageKey' dflags env (modulePackageKey m)
        return (mkModule pk (moduleName m), in_scope)
  | Just (m', in_scope') <- lookupUFM env (moduleName m) = return (m', in_scope')
  -- NB m = HOLE:Blah, that's what's in scope.
  | otherwise = return (m, unitUniqSet (moduleName m))

-- | Substitutes holes in a 'PackageKey', suitable for renaming when
-- an include occurs.
--
-- @p(A -> HOLE:A)@ maps to @p(A -> HOLE:B)@ with @A -> HOLE:B@.
renameHolePackageKey :: DynFlags -> ShHoleSubst -> PackageKey -> IO PackageKey
renameHolePackageKey dflags env pk = fmap fst (renameHolePackageKey' dflags env pk)

-- | Like 'renameHolePackageKey', but returns the 'ShFreeHoles' of
-- the resulting 'PackageKey'.
renameHolePackageKey' :: DynFlags
                      -> ShHoleSubst
                      -> PackageKey
                      -> IO (PackageKey, ShFreeHoles)
renameHolePackageKey' dflags env pk = do
    shpk <- lookupPackageKey dflags pk
    case shpk of
        ShPackageKey { shPackageKeyUnitName = pn,
                       shPackageKeyLibraryName = vh,
                       shPackageKeyInsts = insts,
                       shPackageKeyFreeHoles = in_scope }
            | isNullUFM (intersectUFM_C const in_scope env) -> return (pk, in_scope)
            | otherwise -> do
                insts' <- mapM (\(modname, mod) -> do
                            -- XXX todo use renameHoleModule'
                            mod' <- renameHoleModule dflags env mod
                            return (modname, mod')) insts
                newPackageKeyWithScope dflags pn vh insts'
        ShDefinitePackageKey _ -> return (pk, emptyUniqSet)

{-
************************************************************************
*                                                                      *
                        Name substitutions
*                                                                      *
************************************************************************
-}

-- | Substitution on @HOLE:A.T@.  We enforce the invariant that the
-- 'nameModule' of keys of this map have 'modulePackageKey' @HOLE@
-- (meaning that if we have a hole substitution, the keys of the map
-- are never affected.)  Alternately, this is ismorphic to
-- @Map ('ModuleName', 'OccName') 'Name'@.
type ShNameSubst = NameEnv Name

-- | Find the idempotent fixed point of a non-idempotent substitution on
-- 'Name's.  Similar to 'niFixTvSubst'.
fixShNameSubst :: ShNameSubst -> ShNameSubst
fixShNameSubst env = f env where
    f env | not_fixpoint = f (mapNameEnv (substName env) env)
          | otherwise    = env
        where not_fixpoint = anyNameEnv (\n -> elemNameEnv n env) env
-- INVARIANT: don't give it HOLE:A.T -> HOLE:B.T; HOLE:B.T -> HOLE:A.T,
-- you'l infinite loop... ToDo ASSERT this

-- | Substitute names in a 'Name'.
substName :: ShNameSubst -> Name -> Name
substName env n | Just n' <- lookupNameEnv env n = n'
                | otherwise                      = n

-- | Substitute names in an 'AvailInfo'.  This has special behavior
-- for type constructors, where it is sufficient to substitute the 'availName'
-- to induce a substitution on 'availNames'.
substNameAvailInfo :: HscEnv -> ShNameSubst -> AvailInfo -> IO AvailInfo
substNameAvailInfo _ env (Avail n) = return (Avail (substName env n))
substNameAvailInfo hsc_env env (AvailTC n ns) =
    AvailTC (substName env n) `fmap`
        mapM (setNameModule hsc_env (fmap nameModule (lookupNameEnv env n))) ns

-- | Set the 'Module' of a 'Name'.
setNameModule :: HscEnv -> Maybe Module -> Name -> IO Name
setNameModule _ Nothing n = return n
setNameModule hsc_env (Just m) n =
    initIfaceCheck hsc_env $ newGlobalBinder m (nameOccName n) (nameSrcSpan n)

-- | rn a name substitution based on the shape of the requirements
-- of a package.  E.g. anywhere we have @HOLE:A.T@ we can substitute
-- @p().T@, if in our requirements we know that the hole named @A@
-- specifically requires @p().T@.
computeShapeSubst :: HscEnv -> Shape -> IO ShNameSubst
computeShapeSubst hsc_env sh = do
    let subst = do (modname, (_, as)) <- Map.toList (sh_requires sh)
                   a <- as
                   n <- availName a : availNames a
                   return (modname, n)
    fmap mkNameEnv $ mapM (\(modname, n) ->
        do n0 <- initIfaceCheck hsc_env $
                   newGlobalBinder (mkModule holePackageKey modname)
                                   (nameOccName n) (nameSrcSpan n)
           return (n0, n)
        ) subst

{-
************************************************************************
*                                                                      *
                        Renaming
*                                                                      *
************************************************************************
-}

-- | Substitutes holes in an 'AvailInfo', suitable for renaming when
-- an include occurs.
renameHoleAvailInfo :: HscEnv -> ShHoleSubst -> AvailInfo -> IO AvailInfo
renameHoleAvailInfo hsc_env env (Avail n) = Avail `fmap` renameHoleName hsc_env env n
renameHoleAvailInfo hsc_env env (AvailTC n ns) = do
    n' <- renameHoleName hsc_env env n
    ns' <- mapM (renameHoleName hsc_env env) ns
    return (AvailTC n' ns')

-- | Substitutes holes in a 'Name', suitable for renaming when
-- an include occurs.
--
-- @p(A -> HOLE:A).T@ maps to @p(A -> HOLE:B).T@ with @A -> HOLE:B@;
-- similarly, @HOLE:A.T@ maps to @HOLE:B.T@.
renameHoleName :: HscEnv -> ShHoleSubst -> Name -> IO Name
renameHoleName hsc_env env n = do
    let m = nameModule n
        dflags = hsc_dflags hsc_env
    -- This line distinguishes this from 'substHoleName'.
    m' <- renameHoleModule dflags env m
    if m == m'
        then return n
        else initIfaceCheck hsc_env $
                 newGlobalBinder m' (nameOccName n) (nameSrcSpan n)

{-
************************************************************************
*                                                                      *
                        Shaping unification
*                                                                      *
************************************************************************
-}

-- | Unify two lists of 'AvailInfo's, given an existing substitution @subst@.
uAvailInfos :: ShNameSubst -> [AvailInfo] -> [AvailInfo] -> Maybe ShNameSubst
uAvailInfos subst as1 as2 =
    let mkOE as = listToUFM $ do a <- as
                                 n <- availNames a
                                 return (nameOccName n, a)
    in foldM (\subst (a1, a2) -> uAvailInfo subst a1 a2) subst
             (eltsUFM (intersectUFM_C (,) (mkOE as1) (mkOE as2)))
             -- Edward: I have to say, this is pretty clever.

-- | Unify two 'AvailInfo's, given an existing substitution @subst@.
uAvailInfo :: ShNameSubst -> AvailInfo -> AvailInfo -> Maybe ShNameSubst
uAvailInfo subst (Avail n1) (Avail n2) = uName subst n1 n2
uAvailInfo subst (AvailTC n1 _) (AvailTC n2 _) = uName subst n1 n2
uAvailInfo _ _ _ = Nothing

-- | Unify two 'Name's, given an existing substitution @subst@.
uName :: ShNameSubst -> Name -> Name -> Maybe ShNameSubst
uName subst n1 n2
    | n1 == n2      = Just subst
    | isHoleName n1 = uHoleName subst n1 n2
    | isHoleName n2 = uHoleName subst n2 n1
    | otherwise     = Nothing

-- | Unify a name @h@ which 'isHoleName' with another name, given an existing
-- substitution @subst@.
uHoleName :: ShNameSubst -> Name {- hole name -} -> Name -> Maybe ShNameSubst
uHoleName subst h n =
    ASSERT( isHoleName h )
    case lookupNameEnv subst h of
        Just n' -> uName subst n' n
                -- Do a quick check if the other name is substituted.
        Nothing | Just n' <- lookupNameEnv subst n ->
                    ASSERT( isHoleName n ) uName subst h n'
                | otherwise ->
                    Just (extendNameEnv subst h n)

{-
************************************************************************
*                                                                      *
                        ModIface substitution
*                                                                      *
************************************************************************
-}

-- | This is UNLIKE the other substitutions, which occur during
-- the course of unification.  Called 'rn' because it is BOTH
-- hole renaming and name substitution.
--
-- What we have a generalized ModIface, which corresponds to
-- a module that looks like p(A -> HOLE:A):B (or maybe even HOLE:A).
-- We need a *specific* ModIface, e.g. p(A -> q():A):B which we can merge,
-- typecheck and load up.
--
-- Here are all of the relevant cases:
--
--  p(A -> HOLE:A):M  ==>  p(A -> HOLE:B):M
--
--      Substitute all occurrences of HOLE:A with HOLE:B (renameHole).
--      Then, for any Name of form HOLE:B.T, replace the Name with
--      the Name according to the B provision in the shape (substName).
--
--  p(A -> HOLE:A):M  ==>  p(A -> q():A):M
--
--      Substitute all occurrences of HOLE:A with q():A (renameHole).
--      Then, for any Name of form q():A.T, replace the Name with
--      the Name according to the renamed ModIface for that module.
rnModIface :: HscEnv -> PackageKey -> ModIface -> IO ModIface
rnModIface hsc_env pk iface = do
    MASSERT( pk /= holePackageKey )
    let dflags = hsc_dflags hsc_env
    shpk <- lookupPackageKey dflags pk
    hmap <- mkShHoleSubst dflags (listToUFM
                (case shpk of
                    ShPackageKey { shPackageKeyInsts = insts } -> insts
                    ShDefinitePackageKey{} -> []))
    if (not (isNullUFM hmap))
      then do
        topmod <- renameHoleTopModule dflags hmap (mi_top_module iface)
        initTcRnIf 'c' hsc_env () hmap $ do
            exports <- mapM rnAvailInfo (mi_exports iface)
            decls <- mapM rnIfaceDecl' (mi_decls iface)
            -- TODO:
            -- mi_insts
            -- mi_fam_insts
            -- mi_rules
            -- mi_vect_info (LOW PRIORITY)
            {-pprTrace "rnModIface" (ppr mod <+> ppr exports) $ -}
            return iface { mi_top_module = topmod
                         , mi_exports = exports
                         , mi_decls = decls }
      else {- pprTrace "rnModIface" (ppr shpk) $ -} return iface

type ShIfM = TcRnIf () ShHoleSubst
type Rename a = a -> ShIfM a

rnAvailInfo :: Rename AvailInfo
rnAvailInfo (Avail n) = Avail <$> rnIfaceGlobal n
rnAvailInfo (AvailTC n ns) = do
    ns' <- mapM rnIfaceGlobal ns
    case ns' of
        [] -> panic "rnAvailInfoEmpty AvailInfo"
        (rep:rest) -> ASSERT( all ((== nameModule rep) . nameModule) rest ) do
                         hsc_env <- getTopEnv
                         n' <- liftIO $ setNameModule hsc_env (Just (nameModule rep)) n
                         return (AvailTC n' ns')

-- | The key function.  This gets called on every Name embedded
-- inside a ModIface, and so our job is to rename it appropriately.
-- tcIfaceGlobal
rnIfaceGlobal :: Name -> ShIfM Name
rnIfaceGlobal n = do
    hmap <- getLclEnv
    hsc_env <- getTopEnv
    eps <- getEps
    let m = nameModule n
        dflags = hsc_dflags hsc_env
        withNameSubst = return . substName (eps_shape eps)
    m' <- liftIO $ renameHoleModule dflags hmap m
    {- pprTrace "rnIfaceGlobal" (ppr m <+> ppr m' <+> ppr n) $ -}
    case () of
        _ | m == m' -> withNameSubst n
          | isHoleModule m && not (isHoleModule m') -> do
            -- The substution was from HOLE:A.T to p():A.T.
            -- But it's possible that p() actually reexports
            -- T from somewhere else.  Furthermore, we need
            -- to make sure we pick the accurate name NOW,
            -- or we might accidentally reject a merge.
            -- TODO: This might accidentally tug on an interface
            -- too early...
            iface <- liftIO . initIfaceCheck hsc_env $ loadSysInterface (text "rnIfaceGlobal") m'
            -- TODO: KNOWN BUG, bkp05
            let rs = do a <- mi_exports iface
                        n' <- availNames a
                        guard (nameOccName n' == nameOccName n)
                        return n'
            case rs of
                (b:bs) -> ASSERT ( all (b==) bs ) withNameSubst b
                [] -> pprPanic "rnIfaceGlobal" $ text "could not find" <+> ppr (nameOccName n) <+> text "in" <+> ppr m' <+> parens (text "did find:" <+> ppr (mi_exports iface))
          | otherwise -> do
            n' <- liftIO $ setNameModule hsc_env (Just m') n
            withNameSubst n'

-- PILES AND PILES OF BOILERPLATE

rnIfaceDecl' :: Rename (Fingerprint, IfaceDecl)
rnIfaceDecl' (fp, decl) = (,) fp <$> rnIfaceDecl decl

rnIfaceDecl :: Rename IfaceDecl
rnIfaceDecl d@IfaceId{} = do
            ty <- rnIfaceType (ifType d)
            details <- rnIfaceIdDetails (ifIdDetails d)
            info <- rnIfaceIdInfo (ifIdInfo d)
            return d { ifType = ty
                     , ifIdDetails = details
                     , ifIdInfo = info
                     }
rnIfaceDecl d@IfaceData{} = do
            ty_vars <- mapM rnIfaceTvBndr (ifTyVars d)
            ctxt <- mapM rnIfaceType (ifCtxt d)
            cons <- rnIfaceConDecls (ifCons d)
            parent <- rnIfaceTyConParent (ifParent d)
            return d { ifTyVars = ty_vars
                     , ifCtxt = ctxt
                     , ifCons = cons
                     , ifParent = parent
                     }
rnIfaceDecl d@IfaceSynonym{} = do
            ty_vars <- mapM rnIfaceTvBndr (ifTyVars d)
            syn_kind <- rnIfaceType (ifSynKind d)
            syn_rhs <- rnIfaceType (ifSynRhs d)
            return d { ifTyVars = ty_vars
                     , ifSynKind = syn_kind
                     , ifSynRhs = syn_rhs
                     }
rnIfaceDecl d@IfaceFamily{} = do
            ty_vars <- mapM rnIfaceTvBndr (ifTyVars d)
            fam_kind <- rnIfaceType (ifFamKind d)
            fam_flav <- rnIfaceFamTyConFlav (ifFamFlav d)
            return d { ifTyVars = ty_vars
                     , ifFamKind = fam_kind
                     , ifFamFlav = fam_flav
                     }
rnIfaceDecl d@IfaceClass{} = do
            ctxt <- mapM rnIfaceType (ifCtxt d)
            ty_vars <- mapM rnIfaceTvBndr (ifTyVars d)
            ats <- mapM rnIfaceAT (ifATs d)
            sigs <- mapM rnIfaceClassOp (ifSigs d)
            return d { ifCtxt = ctxt
                     , ifTyVars = ty_vars
                     , ifATs = ats
                     , ifSigs = sigs
                     }
rnIfaceDecl d@IfaceAxiom{} = do
            tycon <- rnIfaceTyCon (ifTyCon d)
            ax_branches <- mapM rnIfaceAxBranch (ifAxBranches d)
            return d { ifTyCon = tycon
                     , ifAxBranches = ax_branches
                     }
rnIfaceDecl d@IfacePatSyn{} =  do
            let rnPat (n, b) = (,) <$> rnIfaceGlobal n <*> pure b
            pat_matcher <- rnPat (ifPatMatcher d)
            pat_builder <- T.traverse rnPat (ifPatBuilder d)
            pat_univ_tvs <- mapM rnIfaceTvBndr (ifPatUnivTvs d)
            pat_ex_tvs <- mapM rnIfaceTvBndr (ifPatExTvs d)
            pat_prov_ctxt <- mapM rnIfaceType (ifPatProvCtxt d)
            pat_req_ctxt <- mapM rnIfaceType (ifPatReqCtxt d)
            pat_args <- mapM rnIfaceType (ifPatArgs d)
            pat_ty <- rnIfaceType (ifPatTy d)
            return d { ifPatMatcher = pat_matcher
                     , ifPatBuilder = pat_builder
                     , ifPatUnivTvs = pat_univ_tvs
                     , ifPatExTvs = pat_ex_tvs
                     , ifPatProvCtxt = pat_prov_ctxt
                     , ifPatReqCtxt = pat_req_ctxt
                     , ifPatArgs = pat_args
                     , ifPatTy = pat_ty
                     }

rnIfaceFamTyConFlav :: Rename IfaceFamTyConFlav
rnIfaceFamTyConFlav (IfaceClosedSynFamilyTyCon (Just (n, axs)))
    = IfaceClosedSynFamilyTyCon . Just <$> ((,) <$> rnIfaceGlobal n
                                                <*> mapM rnIfaceAxBranch axs)
rnIfaceFamTyConFlav flav = pure flav

rnIfaceAT :: Rename IfaceAT
rnIfaceAT (IfaceAT decl mb_ty)
    = IfaceAT <$> rnIfaceDecl decl <*> T.traverse rnIfaceType mb_ty

rnIfaceTyConParent :: Rename IfaceTyConParent
rnIfaceTyConParent (IfDataInstance n tc args)
    = IfDataInstance <$> rnIfaceGlobal n
                     <*> rnIfaceTyCon tc
                     <*> rnIfaceTcArgs args
rnIfaceTyConParent IfNoParent = pure IfNoParent

rnIfaceConDecls :: Rename IfaceConDecls
rnIfaceConDecls (IfDataTyCon ds) = IfDataTyCon <$> mapM rnIfaceConDecl ds
rnIfaceConDecls (IfNewTyCon d) = IfNewTyCon <$> rnIfaceConDecl d
rnIfaceConDecls IfDataFamTyCon = pure IfDataFamTyCon
rnIfaceConDecls (IfAbstractTyCon b) = pure (IfAbstractTyCon b)

rnIfaceConDecl :: Rename IfaceConDecl
rnIfaceConDecl d = do
    con_ex_tvs <- mapM rnIfaceTvBndr (ifConExTvs d)
    let rnIfConEqSpec (n,t) = (,) n <$> rnIfaceType t
    con_eq_spec <- mapM rnIfConEqSpec (ifConEqSpec d)
    con_ctxt <- mapM rnIfaceType (ifConCtxt d)
    con_arg_tys <- mapM rnIfaceType (ifConArgTys d)
    let rnIfaceBang (IfUnpackCo co) = IfUnpackCo <$> rnIfaceCo co
        rnIfaceBang bang = pure bang
    con_stricts <- mapM rnIfaceBang (ifConStricts d)
    return d { ifConExTvs = con_ex_tvs
             , ifConEqSpec = con_eq_spec
             , ifConCtxt = con_ctxt
             , ifConArgTys = con_arg_tys
             , ifConStricts = con_stricts
             }

rnIfaceClassOp :: Rename IfaceClassOp
rnIfaceClassOp (IfaceClassOp n dm ty) = IfaceClassOp n dm <$> rnIfaceType ty

rnIfaceAxBranch :: Rename IfaceAxBranch
rnIfaceAxBranch d = do
    ty_vars <- mapM rnIfaceTvBndr (ifaxbTyVars d)
    lhs <- rnIfaceTcArgs (ifaxbLHS d)
    rhs <- rnIfaceType (ifaxbRHS d)
    return d { ifaxbTyVars = ty_vars
             , ifaxbLHS = lhs
             , ifaxbRHS = rhs }

rnIfaceIdInfo :: Rename IfaceIdInfo
rnIfaceIdInfo NoInfo = pure NoInfo
rnIfaceIdInfo (HasInfo is) = HasInfo <$> mapM rnIfaceInfoItem is

rnIfaceInfoItem :: Rename IfaceInfoItem
rnIfaceInfoItem (HsUnfold lb if_unf)
    = HsUnfold lb <$> rnIfaceUnfolding if_unf
rnIfaceInfoItem i
    = pure i

rnIfaceUnfolding :: Rename IfaceUnfolding
rnIfaceUnfolding (IfCoreUnfold stable if_expr)
    = IfCoreUnfold stable <$> rnIfaceExpr if_expr
rnIfaceUnfolding (IfCompulsory if_expr)
    = IfCompulsory <$> rnIfaceExpr if_expr
rnIfaceUnfolding (IfInlineRule arity unsat_ok boring_ok if_expr)
    = IfInlineRule arity unsat_ok boring_ok <$> rnIfaceExpr if_expr
rnIfaceUnfolding (IfDFunUnfold bs ops)
    = IfDFunUnfold <$> rnIfaceBndrs bs <*> mapM rnIfaceExpr ops

rnIfaceExpr :: Rename IfaceExpr
rnIfaceExpr (IfaceLcl name) = pure (IfaceLcl name)
rnIfaceExpr (IfaceExt gbl) = IfaceExt <$> rnIfaceGlobal gbl
rnIfaceExpr (IfaceType ty) = IfaceType <$> rnIfaceType ty
rnIfaceExpr (IfaceCo co) = IfaceCo <$> rnIfaceCo co
rnIfaceExpr (IfaceTuple sort args) = IfaceTuple sort <$> rnIfaceExprs args
rnIfaceExpr (IfaceLam lam_bndr expr)
    = IfaceLam <$> rnIfaceLamBndr lam_bndr <*> rnIfaceExpr expr
rnIfaceExpr (IfaceApp fun arg)
    = IfaceApp <$> rnIfaceExpr fun <*> rnIfaceExpr arg
rnIfaceExpr (IfaceCase scrut case_bndr alts)
    = IfaceCase <$> rnIfaceExpr scrut
                <*> pure case_bndr
                <*> mapM rnIfaceAlt alts
rnIfaceExpr (IfaceECase scrut ty)
    = IfaceECase <$> rnIfaceExpr scrut <*> rnIfaceType ty
rnIfaceExpr (IfaceLet (IfaceNonRec bndr rhs) body)
    = IfaceLet <$> (IfaceNonRec <$> rnIfaceLetBndr bndr <*> rnIfaceExpr rhs)
               <*> rnIfaceExpr body
rnIfaceExpr (IfaceLet (IfaceRec pairs) body)
    = IfaceLet <$> (IfaceRec <$> mapM (\(bndr, rhs) ->
                                        (,) <$> rnIfaceLetBndr bndr
                                            <*> rnIfaceExpr rhs) pairs)
               <*> rnIfaceExpr body
rnIfaceExpr (IfaceCast expr co)
    = IfaceCast <$> rnIfaceExpr expr <*> rnIfaceCo co
rnIfaceExpr (IfaceLit lit) = pure (IfaceLit lit)
rnIfaceExpr (IfaceFCall cc ty) = IfaceFCall cc <$> rnIfaceType ty
rnIfaceExpr (IfaceTick tickish expr) = IfaceTick tickish <$> rnIfaceExpr expr

rnIfaceBndrs :: Rename [IfaceBndr]
rnIfaceBndrs = mapM rnIfaceBndr

rnIfaceBndr :: Rename IfaceBndr
rnIfaceBndr (IfaceIdBndr (fs, ty)) = IfaceIdBndr <$> ((,) fs <$> rnIfaceType ty)
rnIfaceBndr (IfaceTvBndr tv_bndr) = IfaceIdBndr <$> rnIfaceTvBndr tv_bndr

rnIfaceTvBndr :: Rename IfaceTvBndr
rnIfaceTvBndr (fs, kind) = (,) fs <$> rnIfaceType kind

rnIfaceAlt :: Rename IfaceAlt
rnIfaceAlt (conalt, names, rhs)
     = (,,) <$> rnIfaceConAlt conalt <*> pure names <*> rnIfaceExpr rhs

rnIfaceConAlt :: Rename IfaceConAlt
rnIfaceConAlt (IfaceDataAlt data_occ) = IfaceDataAlt <$> rnIfaceGlobal data_occ
rnIfaceConAlt alt = pure alt

rnIfaceLetBndr :: Rename IfaceLetBndr
rnIfaceLetBndr (IfLetBndr fs ty info)
    = IfLetBndr fs <$> rnIfaceType ty <*> rnIfaceIdInfo info

rnIfaceLamBndr :: Rename IfaceLamBndr
rnIfaceLamBndr (bndr, oneshot) = (,) <$> rnIfaceBndr bndr <*> pure oneshot

rnIfaceCo :: Rename IfaceCoercion
rnIfaceCo (IfaceReflCo role ty) = IfaceReflCo role <$> rnIfaceType ty
rnIfaceCo (IfaceFunCo role co1 co2)
    = IfaceFunCo role <$> rnIfaceCo co1 <*> rnIfaceCo co2
rnIfaceCo (IfaceTyConAppCo role tc cos)
    = IfaceTyConAppCo role <$> rnIfaceTyCon tc <*> mapM rnIfaceCo cos
rnIfaceCo (IfaceAppCo co1 co2)
    = IfaceAppCo <$> rnIfaceCo co1 <*> rnIfaceCo co2
rnIfaceCo (IfaceForAllCo bndr co)
    = IfaceForAllCo <$> rnIfaceTvBndr bndr <*> rnIfaceCo co
rnIfaceCo (IfaceCoVarCo lcl) = IfaceCoVarCo <$> pure lcl
rnIfaceCo (IfaceAxiomInstCo n i cs)
    = IfaceAxiomInstCo n <$> pure i <*> mapM rnIfaceCo cs
rnIfaceCo (IfaceUnivCo s r t1 t2)
    = IfaceUnivCo s r <$> rnIfaceType t1 <*> rnIfaceType t2
rnIfaceCo (IfaceSymCo c)
    = IfaceSymCo <$> rnIfaceCo c
rnIfaceCo (IfaceTransCo c1 c2)
    = IfaceTransCo <$> rnIfaceCo c1 <*> rnIfaceCo c2
rnIfaceCo (IfaceInstCo c1 t2)
    = IfaceInstCo <$> rnIfaceCo c1 <*> rnIfaceType t2
rnIfaceCo (IfaceNthCo d c) = IfaceNthCo d <$> rnIfaceCo c
rnIfaceCo (IfaceLRCo lr c) = IfaceLRCo lr <$> rnIfaceCo c
rnIfaceCo (IfaceSubCo c) = IfaceSubCo <$> rnIfaceCo c
rnIfaceCo (IfaceAxiomRuleCo ax tys cos)
    = IfaceAxiomRuleCo ax <$> mapM rnIfaceType tys
                          <*> mapM rnIfaceCo cos

rnIfaceTyCon :: Rename IfaceTyCon
rnIfaceTyCon (IfaceTyCon n info)
    = IfaceTyCon <$> rnIfaceGlobal n <*> pure info

rnIfaceExprs :: Rename [IfaceExpr]
rnIfaceExprs = mapM rnIfaceExpr

rnIfaceIdDetails :: Rename IfaceIdDetails
rnIfaceIdDetails (IfRecSelId tc b) = IfRecSelId <$> rnIfaceTyCon tc <*> pure b
rnIfaceIdDetails details = pure details

rnIfaceType :: Rename IfaceType
rnIfaceType (IfaceTyVar n) = pure (IfaceTyVar n)
rnIfaceType (IfaceAppTy t1 t2)
    = IfaceAppTy <$> rnIfaceType t1 <*> rnIfaceType t2
rnIfaceType (IfaceLitTy l)         = return (IfaceLitTy l)
rnIfaceType (IfaceFunTy t1 t2)
    = IfaceFunTy <$> rnIfaceType t1 <*> rnIfaceType t2
rnIfaceType (IfaceDFunTy t1 t2)
    = IfaceDFunTy <$> rnIfaceType t1 <*> rnIfaceType t2
rnIfaceType (IfaceTupleTy s i tks)
    = IfaceTupleTy s i <$> rnIfaceTcArgs tks
rnIfaceType (IfaceTyConApp tc tks)
    = IfaceTyConApp <$> rnIfaceTyCon tc <*> rnIfaceTcArgs tks
rnIfaceType (IfaceForAllTy tv t)
    = IfaceForAllTy <$> rnIfaceTvBndr tv <*> rnIfaceType t

rnIfaceTcArgs :: Rename IfaceTcArgs
rnIfaceTcArgs (ITC_Type t ts) = ITC_Type <$> rnIfaceType t <*> rnIfaceTcArgs ts
rnIfaceTcArgs (ITC_Kind t ts) = ITC_Kind <$> rnIfaceType t <*> rnIfaceTcArgs ts
rnIfaceTcArgs ITC_Nil = pure ITC_Nil
