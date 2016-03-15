{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}

module ShUnify(
    -- * Overall substitution
    ShSubst(..),
    mkShSubst,
    substAvailInfo,

    -- * Hole substitutions
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

    -- * Renaming
    renameHoleAvailInfo,

    -- * Unification
    uAvailInfos,

    -- * ModIface substitution
    rnModIface,
    rnModExports,

    -- * Heavy-duty unification
    ModuleU, UnitIdU,
    MuEnv, emptyMuEnv,
    MooEnv, emptyMooEnv,
    convertUnitId',
    convertModule',
    convertUnitIdU,
    convertModuleU,
    unifyUnitId,
    unifyModule,
    ) where

#include "HsVersions.h"

import Shape

import Outputable
import HscTypes
import Module
import UniqFM
import UniqSet
import Avail
import IfaceSyn
import FieldLabel

import Name
import NameEnv
import TcRnMonad
import Util
import Fingerprint
import Unique
import BasicTypes

import qualified GHC.LanguageExtensions as LangExt

-- for the unification
import qualified UnionFind
import Data.IORef
import Data.List
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

-- really, the global binder code should live in a different module
import {-# SOURCE #-} IfaceEnv

-- a bit vexing
import {-# SOURCE #-} LoadIface
import DynFlags

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
    let hsubst = fixShHoleSubst hsubst0
    -- TODO: which order of applying the substitution is best?
    nsubst1 <- T.mapM (substHoleName hsc_env hsubst) nsubst0
    let nsubst = fixShNameSubst nsubst1
    return (ShSubst hsubst nsubst)

-- | Applies an idempotent 'ShSubst' to an 'AvailInfo'.
substAvailInfo :: HscEnv -> ShSubst -> AvailInfo -> IO AvailInfo
substAvailInfo hsc_env (ShSubst hsubst nsubst) a
    = substHoleAvailInfo hsc_env hsubst a >>=
      substNameAvailInfo hsc_env nsubst

-- | Compute the NON-IDEMPOTENT substitution for filling some requirements
-- with some provisions.
--
-- Historical note: historically, this also checked the UnitId to augment
-- the substitution.  This is no longer relevant as we don't run shaping
-- unless the unit ID is all holes.
computeHoleSubst :: ShProvides -> ShRequires -> ShHoleSubst
computeHoleSubst provs reqs = do
    foldl' (\m modname ->
    -- TODO Does order matter? Shouldn't...
        case Map.lookup modname provs of
            Just (mod, _) -> addToUFM m modname mod
            Nothing -> m)
       emptyUFM (Map.keys reqs)

-- | Find the idempotent fixed point of a non-idempotent substitution on
-- 'Module's.
fixShHoleSubst :: ShHoleSubst -> ShHoleSubst
fixShHoleSubst env0 = f env0 where
    f env | not fixpoint = f (fmap (renameHoleModule env) (removeCycles env))
          | otherwise    = env
        where fixpoint = isNullUFM (intersectUFM_C const in_scope env)
              in_scope = unionManyUniqSets (map moduleFreeHoles (eltsUFM env))
              removeCycles m = filterUFM_Directly notCycle m
              notCycle u m = not (isHoleModule m && getUnique (moduleName m) == u)

-- | Substitutes holes in an 'AvailInfo'.  NOT suitable for renaming
-- when an include occurs (see 'renameHoleAvailInfo' instead).
-- See 'substHoleName' for more details.
substHoleAvailInfo :: HscEnv -> ShHoleSubst -> AvailInfo -> IO AvailInfo
substHoleAvailInfo hsc_env env (Avail p n) = Avail p `fmap` substHoleName hsc_env env n
substHoleAvailInfo hsc_env env (AvailTC n ns fs) = do
    n' <- substHoleName hsc_env env n
    ns' <- mapM (substHoleName hsc_env env) ns
    fs' <- mapM (substHoleFieldLabel hsc_env env) fs
    return (AvailTC n' ns' fs')

substHoleFieldLabel :: HscEnv -> ShHoleSubst -> FieldLabel -> IO FieldLabel
substHoleFieldLabel hsc_env env (FieldLabel l b sel) = do
    sel' <- substHoleName hsc_env env sel
    return (FieldLabel l b sel')

-- | Substitutes holes in a 'Name'. NOT suitable for renaming when
-- an include occurs.
--
-- @p(A -> HOLE:A).T@ maps to @p(A -> q():A).T@ with @A -> q():A@;
-- this substitution has no effect on @HOLE:A.T@ (we expect this
-- to be substituted via a name substitution).
substHoleName :: HscEnv -> ShHoleSubst -> Name -> IO Name
substHoleName hsc_env env n = do
    let m = nameModule n
        m' = substHoleModule env m
    if m == m'
        then return n
        else setNameModule hsc_env (Just m') n

-- | Substitutes holes in a 'Module', but not at the top level;
-- this is the behavior you want when substituting the 'nameModule' of a 'Name'.
-- @p(A -> HOLE:A):B@ maps to @p(A -> q():A):B@ with @A -> q():A@;
-- this substitution has no effect on @HOLE:A@.
substHoleModule :: ShHoleSubst -> Module -> Module
substHoleModule env m
  | not (isHoleModule m) = renameHoleModule env m
  | otherwise = m


{-
************************************************************************
*                                                                      *
                        Name substitutions
*                                                                      *
************************************************************************
-}

-- | Substitution on @HOLE:A.T@.  We enforce the invariant that the
-- 'nameModule' of keys of this map have 'moduleUnitId' @HOLE@
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
substNameAvailInfo _ env (Avail p n) = return (Avail p (substName env n))
substNameAvailInfo hsc_env env (AvailTC n ns fs) =
    let mb_mod = fmap nameModule (lookupNameEnv env n)
    in AvailTC (substName env n)
        <$> mapM (setNameModule hsc_env mb_mod) ns
        <*> mapM (setNameFieldSelector hsc_env mb_mod) fs

-- | Set the 'Module' of a 'Name'.
setNameModule :: HscEnv -> Maybe Module -> Name -> IO Name
setNameModule _ Nothing n = return n
setNameModule hsc_env (Just m) n =
    initIfaceCheck hsc_env $ newGlobalBinder m (nameOccName n) (nameSrcSpan n)

-- | Set the 'Module' of a 'FieldSelector'
setNameFieldSelector :: HscEnv -> Maybe Module -> FieldLabel -> IO FieldLabel
setNameFieldSelector _ Nothing f = return f
setNameFieldSelector hsc_env mb_mod (FieldLabel l b sel) = do
    sel' <- setNameModule hsc_env mb_mod sel
    return (FieldLabel l b sel')

-- | rn a name substitution based on the shape of the requirements
-- of a package.  E.g. anywhere we have @HOLE:A.T@ we can substitute
-- @p().T@, if in our requirements we know that the hole named @A@
-- specifically requires @p().T@.
computeShapeSubst :: HscEnv -> Shape -> IO ShNameSubst
computeShapeSubst hsc_env sh = do
    let subst = do (modname, as) <- Map.toList (sh_requires sh)
                   a <- as
                   n <- availName a : availNames a
                   return (modname, n)
    fmap mkNameEnv $ mapM (\(modname, n) ->
        do n0 <- initIfaceCheck hsc_env $
                   newGlobalBinder (mkModule holeUnitId modname)
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
renameHoleAvailInfo hsc_env env (Avail p n) = Avail p `fmap` renameHoleName hsc_env env n
renameHoleAvailInfo hsc_env env (AvailTC n ns fs) = do
    n' <- renameHoleName hsc_env env n
    ns' <- mapM (renameHoleName hsc_env env) ns
    fs' <- mapM (renameHoleFieldLabel hsc_env env) fs
    return (AvailTC n' ns' fs')

-- | Substitutes holes in a 'Name', suitable for renaming when
-- an include occurs.
--
-- @p(A -> HOLE:A).T@ maps to @p(A -> HOLE:B).T@ with @A -> HOLE:B@;
-- similarly, @HOLE:A.T@ maps to @HOLE:B.T@.
renameHoleName :: HscEnv -> ShHoleSubst -> Name -> IO Name
renameHoleName hsc_env env n = do
    let m = nameModule n
        -- This line distinguishes this from 'substHoleName'.
        m' = renameHoleModule env m
    if m == m'
        then return n
        else initIfaceCheck hsc_env $
                 newGlobalBinder m' (nameOccName n) (nameSrcSpan n)

renameHoleFieldLabel :: HscEnv -> ShHoleSubst -> FieldLabel -> IO FieldLabel
renameHoleFieldLabel hsc_env env (FieldLabel l b sel) = do
    sel' <- renameHoleName hsc_env env sel
    return (FieldLabel l b sel')

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
uAvailInfo subst (Avail _ n1) (Avail _ n2) = uName subst n1 n2
uAvailInfo subst (AvailTC n1 _ _) (AvailTC n2 _ _) = uName subst n1 n2
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

initRnIface :: HscEnv -> UnitId -> ShIfM a -> IO a
initRnIface hsc_env uid do_this = do
    MASSERT( uid /= holeUnitId )
    let hmap = listToUFM (unitIdInsts uid)
    initTcRnIf 'c' hsc_env uid hmap do_this

-- | This is UNLIKE the other substitutions, which occur during
-- the course of unification.  Called 'rn' because it is BOTH
-- hole renaming and name substitution.
--
-- What we have a generalized ModIface, which corresponds to
-- a module that looks like p(A -> HOLE:A):B (or maybe even HOLE:A).
-- We need a *specific* ModIface, e.g. p(A -> q():A):B which we can merge,
-- typecheck and load up.
--
-- This function does NOT know how to do unification; we assume
-- everything has already been unified by shaping, which has been
-- recorded in eps_shape.
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
rnModIface :: HscEnv -> UnitId -> ModIface -> IO ModIface
rnModIface hsc_env uid iface = do
    initRnIface hsc_env uid $ do
        mod <- rnModule (mi_module iface)
        exports <- mapM rnAvailInfo (mi_exports iface)
        decls <- mapM rnIfaceDecl' (mi_decls iface)
        -- TODO:
        -- mi_insts
        -- mi_fam_insts
        -- mi_rules
        -- mi_vect_info (LOW PRIORITY)
        {-pprTrace "rnModIface" (ppr mod <+> ppr exports) $ -}
        return iface { mi_module = mod
                     , mi_exports = exports
                     , mi_decls = decls }

rnModExports :: HscEnv -> UnitId -> [AvailInfo] -> IO [AvailInfo]
rnModExports hsc_env uid as = initRnIface hsc_env uid $ mapM rnAvailInfo as

rnModule :: Rename Module
rnModule mod = do
    hmap <- getLclEnv
    return (renameHoleModule hmap mod)

type ShIfM = TcRnIf UnitId ShHoleSubst
type Rename a = a -> ShIfM a

rnAvailInfo :: Rename AvailInfo
rnAvailInfo (Avail p n) = Avail p <$> rnIfaceGlobal n
rnAvailInfo (AvailTC n ns fs) = do
    -- Why don't we rnIfaceGlobal the availName itself?  It may not
    -- actually be exported by the module it putatively is from, in
    -- which case we won't be able to tell what the name actually
    -- is.  But for the availNames they MUST be exported, so they
    -- will rename fine.
    ns' <- mapM rnIfaceGlobal ns
    fs' <- mapM rnFieldLabel fs
    case ns' ++ map flSelector fs' of
        [] -> panic "rnAvailInfoEmpty AvailInfo"
        (rep:rest) -> ASSERT( all ((== nameModule rep) . nameModule) rest ) do
                         hsc_env <- getTopEnv
                         n' <- liftIO $ setNameModule hsc_env (Just (nameModule rep)) n
                         return (AvailTC n' ns' fs')

rnFieldLabel :: Rename FieldLabel
rnFieldLabel (FieldLabel l b sel) = do
    sel' <- rnIfaceGlobal sel
    return (FieldLabel l b sel')

-- | The key function.  This gets called on every Name embedded
-- inside a ModIface.  Our job is to take a Name from some
-- generalized unit ID p(A -> HOLE:A, B -> HOLE:B), and change
-- it to the correct name for a (partially) instantiated unit
-- ID, e.g. p(A -> p:A, B -> HOLE:B).
--
-- There are two important things to do:
--
--      1. If a hole is substituted with a real module implementation,
--      we can't just blindly substitute in the module because the real
--      implementation may have re-exported this name from somewhere
--      else.  So we have to look and see what the real name is by
--      looking at the mi_exports.
--
--      2. Once we have a name, if it's a concrete name we're done.
--      However, if it's a hole name like HOLE:A.T, we may have,
--      in fact, discovered that this name is something else during
--      shaping.  So we apply the substitution induced by the
--      final computed requirements after shaping.  If we're actually
--      compiling, this will never do anything because there won't
--      be any holes left.
--
-- Compare me with 'tcIfaceGlobal'!

-- In effect, this function needs compute the name substitution on the
-- fly.  What it has is the name that we would like to substitute.
-- If the name is not a hole name HOLE:M.x (e.g. isHoleModule) then
-- no renaming can take place (although the inner hole structure must
-- be updated to account for the hole module renaming.)
rnIfaceGlobal :: Name -> ShIfM Name
rnIfaceGlobal n = do
    -- TODO MASSIVE REFACTOR PLEASE
    hmap <- getLclEnv
    hsc_env <- getTopEnv
    eps <- getEps
    let m = nameModule n
        m' = renameHoleModule hmap m
    -- pprTrace "rnIfaceGlobal" (ppr m <+> ppr m' <+> ppr n) $ return ()
    -- NB: eps_shape is blank at the moment
    fmap (substName (eps_shape eps)) $ case () of
        -- The special cases for NoSignatureMerging are unsound but
        -- just to keep things working
        _ | not (xopt LangExt.NoSignatureMerging (hsc_dflags hsc_env))
          , m == m' -> return n
          | isHoleModule m
          , (xopt LangExt.NoSignatureMerging (hsc_dflags hsc_env) || not (isHoleModule m')) -> do
            -- The substution was from HOLE:A.T to p():A.T.
            -- But it's possible that p() actually reexports
            -- T from somewhere else.  Do the name
            -- substitution.  Furthermore, we need
            -- to make sure we pick the accurate name NOW,
            -- or we might accidentally reject a merge.
            let dflags = hsc_dflags hsc_env
            let m'' = if isHoleModule m'
                        -- Pull out the local guy!!
                        then mkModule (thisPackage dflags) (moduleName m')
                        else m'
            (exports, _) <- liftIO . initIfaceCheck hsc_env
                                   . withException
                                   $ computeExports (text "rnIfaceGlobal") False m''

            case lookupExport (nameOccName n) exports of
                (b:bs) -> ASSERT ( all (b==) bs ) return b
                [] -> pprPanic "rnIfaceGlobal" $
                         text "could not find" <+> ppr (nameOccName n) <+>
                         text "in" <+> ppr m'
                         <+> parens (text "did find:" <+> ppr exports)
          | otherwise -> do
            liftIO $ setNameModule hsc_env (Just m') n
  where
    -- TODO: KNOWN BUG, bkp05:
    -- There could be duplicate matches here
    lookupExport occ exports = do
        a <- exports
        n' <- availNames a
        guard (nameOccName n' == occ)
        return n'

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
rnIfaceConDecls (IfDataTyCon ds b fs)
    = IfDataTyCon <$> mapM rnIfaceConDecl ds
                  <*> return b
                  <*> return fs
rnIfaceConDecls (IfNewTyCon d b fs) = IfNewTyCon <$> rnIfaceConDecl d <*> return b <*> return fs
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
rnIfaceClassOp (IfaceClassOp n ty dm) = IfaceClassOp n <$> rnIfaceType ty <*> rnMaybeDefMethSpec dm

rnMaybeDefMethSpec :: Rename (Maybe (DefMethSpec IfaceType))
rnMaybeDefMethSpec (Just (GenericDM ty)) = Just . GenericDM <$> rnIfaceType ty
rnMaybeDefMethSpec mb = return mb

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
rnIfaceCo (IfaceForAllCo bndr co1 co2)
    = IfaceForAllCo <$> rnIfaceTvBndr bndr <*> rnIfaceCo co1 <*> rnIfaceCo co2
rnIfaceCo (IfaceCoVarCo lcl) = IfaceCoVarCo <$> pure lcl
rnIfaceCo (IfaceAxiomInstCo n i cs)
    = IfaceAxiomInstCo <$> rnIfaceGlobal n <*> pure i <*> mapM rnIfaceCo cs
rnIfaceCo (IfaceUnivCo s r t1 t2)
    = IfaceUnivCo s r <$> rnIfaceType t1 <*> rnIfaceType t2
rnIfaceCo (IfaceSymCo c)
    = IfaceSymCo <$> rnIfaceCo c
rnIfaceCo (IfaceTransCo c1 c2)
    = IfaceTransCo <$> rnIfaceCo c1 <*> rnIfaceCo c2
rnIfaceCo (IfaceInstCo c1 c2)
    = IfaceInstCo <$> rnIfaceCo c1 <*> rnIfaceCo c2
rnIfaceCo (IfaceNthCo d c) = IfaceNthCo d <$> rnIfaceCo c
rnIfaceCo (IfaceLRCo lr c) = IfaceLRCo lr <$> rnIfaceCo c
rnIfaceCo (IfaceSubCo c) = IfaceSubCo <$> rnIfaceCo c
rnIfaceCo (IfaceAxiomRuleCo ax cos)
    = IfaceAxiomRuleCo ax <$> mapM rnIfaceCo cos
rnIfaceCo (IfaceKindCo c) = IfaceKindCo <$> rnIfaceCo c
rnIfaceCo (IfaceCoherenceCo c1 c2) = IfaceCoherenceCo <$> rnIfaceCo c1 <*> rnIfaceCo c2

rnIfaceTyCon :: Rename IfaceTyCon
rnIfaceTyCon (IfaceTyCon n info)
    = IfaceTyCon <$> rnIfaceGlobal n <*> pure info

rnIfaceExprs :: Rename [IfaceExpr]
rnIfaceExprs = mapM rnIfaceExpr

rnIfaceIdDetails :: Rename IfaceIdDetails
rnIfaceIdDetails (IfRecSelId (Left tc) b) = IfRecSelId <$> fmap Left (rnIfaceTyCon tc) <*> pure b
rnIfaceIdDetails (IfRecSelId (Right decl) b) = IfRecSelId <$> fmap Right (rnIfaceDecl decl) <*> pure b
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
    = IfaceForAllTy <$> rnIfaceForAllBndr tv <*> rnIfaceType t
rnIfaceType (IfaceCoercionTy co)
    = IfaceCoercionTy <$> rnIfaceCo co
rnIfaceType (IfaceCastTy ty co)
    = IfaceCastTy <$> rnIfaceType ty <*> rnIfaceCo co

rnIfaceForAllBndr :: Rename IfaceForAllBndr
rnIfaceForAllBndr (IfaceTv tv vis) = IfaceTv <$> rnIfaceTvBndr tv <*> pure vis

rnIfaceTcArgs :: Rename IfaceTcArgs
rnIfaceTcArgs (ITC_Invis t ts) = ITC_Invis <$> rnIfaceType t <*> rnIfaceTcArgs ts
rnIfaceTcArgs (ITC_Vis t ts) = ITC_Vis <$> rnIfaceType t <*> rnIfaceTcArgs ts
rnIfaceTcArgs ITC_Nil = pure ITC_Nil

-- Actual heavy-duty unification

-- This module implements unification over Modules and UnitIds,
-- a necessary operation when performing shaping in the presence
-- of mutual recursion.

-----------------------------------------------------------------------
-- The "unifiable" variants of the data types
--
-- In order to properly do unification over infinite trees, we
-- need to union find over 'Module's and 'UnitId's.  The pure
-- representation is ill-equipped to do this, so we convert
-- from the pure representation into one which is indirected
-- through union-find.  'ModuleU' handles hole variables;
-- 'UnitIdU' handles mu-binders.

data ModuleU'
    = ModuleU UnitIdU ModuleName
    | ModuleVarU ModuleName
data UnitIdU'
    = UnitIdU UnitIdUnique ComponentId [(ModuleName, ModuleU)]
type ModuleU = UnionFind.Point ModuleU'
type UnitIdU = UnionFind.Point UnitIdU'

-- | An integer for uniquely labeling 'UnitIdU' nodes.  We need
-- these labels in order to efficiently serialize 'UnitIdU's into
-- 'UnitId's (we use the label to check if any parent is the
-- node in question, and if so insert a deBruijn index instead.)
-- These labels must be unique across all 'UnitId's/'Module's which
-- participate in unification!
type UnitIdUnique = Int

-----------------------------------------------------------------------
-- Conversion to the unifiable data types

-- An environment for tracking the mu-bindings in scope.
-- The invariant for a state @(m, i)@ is that [0..i] are
-- keys of @m@; in fact, the @i-k@th entry is the @k@th
-- de Bruijn index (this saves us from having to shift as
-- we enter mu-binders.)
type MuEnv = (IntMap UnitIdU, Int)

extendMuEnv :: MuEnv -> UnitIdU -> MuEnv
extendMuEnv (m, i) x =
    (IntMap.insert (i + 1) x m, i + 1)

lookupMuEnv :: MuEnv -> Int {- de Bruijn index -} -> UnitIdU
lookupMuEnv (m, i) k =
    case IntMap.lookup (i - k) m of
        Nothing -> error "lookupMuEnv: out of bounds"
        Just v -> v

emptyMuEnv :: MuEnv
emptyMuEnv = (IntMap.empty, -1)

-- The workhorse functions.  These share an environment:
--   * @IORef UnitIdUnique@ - the unique label supply for 'UnitIdU' nodes
--   * @IORef (Map ModuleName moduleU)@ - the (lazily initialized)
--     environment containing the implicitly universally quantified
--     @hole:A@ binders.
--   * @MuEnv@ - the environment for mu-binders.

convertUnitId' :: IORef UnitIdUnique
               -> IORef (Map ModuleName ModuleU)
               -> MuEnv
               -> UnitId
               -> IO UnitIdU
convertUnitId' fs hmap stk (UnitId{ unitIdComponentId = cid, unitIdInsts = insts }) = do
    x <- UnionFind.fresh (error "convertUnitId") -- tie the knot later
    insts_u <- forM insts $ \(mod_name, mod) -> do
                    mod_u <- convertModule' fs hmap (extendMuEnv stk x) mod
                    return (mod_name, mod_u)
    u <- readIORef fs
    writeIORef fs (u+1)
    y <- UnionFind.fresh (UnitIdU u cid insts_u)
    UnionFind.union x y
    return y
convertUnitId' _fs _hmap stk (UnitIdVar i) = return (lookupMuEnv stk i)

convertModule' :: IORef UnitIdUnique
               -> IORef (Map ModuleName ModuleU)
               -> MuEnv
               -> Module -> IO ModuleU
convertModule' fs hmap stk mod@(Module uid mod_name)
    | isHoleModule mod = do
        hm <- readIORef hmap
        case Map.lookup mod_name hm of
            Nothing -> do mod <- UnionFind.fresh (ModuleVarU mod_name)
                          writeIORef hmap (Map.insert mod_name mod hm)
                          return mod
            Just mod -> return mod
    | otherwise = do
        uid_u <- convertUnitId' fs hmap stk uid
        UnionFind.fresh (ModuleU uid_u mod_name)

-- Some utility functions.  The pluralized variants are non-trivial, as
-- they assume that the implicitly universally quantified hole:A
-- variables quantify over the ENTIRE list (not each element
-- individually!)

convertUnitId :: IORef UnitIdUnique -> UnitId -> IO UnitIdU
convertUnitId fs uid = do
    hmap <- newIORef Map.empty
    convertUnitId' fs hmap emptyMuEnv uid

convertUnitIds :: IORef UnitIdUnique -> [UnitId] -> IO [UnitIdU]
convertUnitIds fs uids = do
    hmap <- newIORef Map.empty
    mapM (convertUnitId' fs hmap emptyMuEnv) uids

convertModule :: IORef UnitIdUnique -> Module -> IO ModuleU
convertModule fs mod = do
    hmap <- newIORef Map.empty
    convertModule' fs hmap emptyMuEnv mod

convertModules :: IORef UnitIdUnique -> [Module] -> IO [ModuleU]
convertModules fs mods = do
    hmap <- newIORef Map.empty
    mapM (convertModule' fs hmap emptyMuEnv) mods

-----------------------------------------------------------------------
-- Conversion from the unifiable data types

-- An environment for tracking candidates for adding a mu-binding.
-- The invariant for a state @(m, i)@, is that if we encounter a node
-- labeled @k@ such that @m[k -> v]@, then we can replace this
-- node with the de Bruijn index @i-v@ referring to an enclosing
-- mu-binder; furthermore, @range(m) = [0..i]@.
type MooEnv = (IntMap Int, Int)

emptyMooEnv :: MooEnv
emptyMooEnv = (IntMap.empty, -1)

extendMooEnv :: MooEnv -> UnitIdUnique -> MooEnv
extendMooEnv (m, i) k = (IntMap.insert k (i + 1) m, i + 1)

lookupMooEnv :: MooEnv -> UnitIdUnique -> Maybe Int
lookupMooEnv (m, i) k =
    case IntMap.lookup k m of
        Nothing -> Nothing
        Just v -> Just (i-v) -- de Bruijn indexize

-- The workhorse functions

convertUnitIdU' :: MooEnv -> UnitIdU -> IO UnitId
convertUnitIdU' stk uid_u = do
    UnitIdU u cid insts_u <- UnionFind.find uid_u
    case lookupMooEnv stk u of
        Just i -> return (UnitIdVar i)
        Nothing -> do
            insts <- forM insts_u $ \(mod_name, mod_u) -> do
                        mod <- convertModuleU' (extendMooEnv stk u) mod_u
                        return (mod_name, mod)
            return (unsafeNewUnitId cid insts)

convertModuleU' :: MooEnv -> ModuleU -> IO Module
convertModuleU' stk mod_u = do
    mod <- UnionFind.find mod_u
    case mod of
        ModuleVarU mod_name -> return (Module holeUnitId mod_name)
        ModuleU uid_u mod_name -> do
            uid <- convertUnitIdU' stk uid_u
            return (Module uid mod_name)

-- Helper functions

convertUnitIdU :: UnitIdU -> IO UnitId
convertUnitIdU = convertUnitIdU' emptyMooEnv

convertModuleU :: ModuleU -> IO Module
convertModuleU = convertModuleU' emptyMooEnv

-----------------------------------------------------------------------
-- The unification algorithm

-- This is based off of https://gist.github.com/amnn/559551517d020dbb6588
-- which is a translation from Huet's thesis.

unifyUnitId :: UnitIdU -> UnitIdU -> IO ()
unifyUnitId uid1_u uid2_u
    | uid1_u == uid2_u = return ()
    | otherwise = do
        UnitIdU u1 cid1 insts1 <- UnionFind.find uid1_u
        UnitIdU u2 cid2 insts2 <- UnionFind.find uid2_u
        when (cid1 /= cid2) $ pprPanic "unifyUnitId: cid failed" (ppr cid1 <+> ppr cid2)
        -- The KEY STEP which makes this a Huet-style unification
        -- algorithm.  (Also a payoff of using union-find.)
        UnionFind.union uid1_u uid2_u
        zipWithM_ (\(mod_name1, mod1) (mod_name2, mod2) -> do
                    when (mod_name1 /= mod_name2) $ error "unifyUnitId: mod_name failed"
                    unifyModule mod1 mod2)
            insts1 insts2

unifyModule :: ModuleU -> ModuleU -> IO ()
unifyModule mod1_u mod2_u
    | mod1_u == mod2_u = return ()
    | otherwise = do
        mod1 <- UnionFind.find mod1_u
        mod2 <- UnionFind.find mod2_u
        case (mod1, mod2) of
            (ModuleVarU _, _) -> UnionFind.union mod1_u mod2_u
            (_, ModuleVarU _) -> UnionFind.union mod2_u mod1_u
            (ModuleU uid1 mod_name1, ModuleU uid2 mod_name2) -> do
                when (mod_name1 /= mod_name2) $ error "unifyModule: mod_name failed"
                -- NB: this is not actually necessary (because we'll
                -- detect loops eventually in 'unifyUnitId'), but it
                -- seems harmless enough
                UnionFind.union mod1_u mod2_u
                unifyUnitId uid1 uid2
