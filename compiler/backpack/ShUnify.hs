{-# LANGUAGE CPP #-}

module ShUnify(
    -- * Overall substitution
    ShSubst(..),
    mkShSubst,
    substAvailInfo,

    -- * Hole substitutions
    ShHoleSubst,
    mkShHoleSubst,
    computeHoleSubst,
    substHoleAvailInfo,
    substHoleName,
    -- NOT exporting substHoleModule
    generalizeHoleModule,

    -- * Name substitutions
    ShNameSubst,
    substName,
    substNameAvailInfo,
    computeShapeSubst,
    setNameModule,

    -- * HOLE renaming
    renameHoleModule,
    renameHoleAvailInfo,

    -- * Unification
    uAvailInfos,
    ) where

#include "HsVersions.h"

import BackpackSyn
import ShPackageKey

import Outputable
import HscTypes
import Module
import UniqFM
import UniqSet
import Avail

import DynFlags
import Name
import {-# SOURCE #-} IfaceEnv
import NameEnv
import TcRnMonad
import Util

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
computeHoleSubst :: DynFlags -> ShProvides -> ShRequires -> IO ShHoleSubst
computeHoleSubst dflags provs reqs =
    let proto_hsubst :: UniqFM Module
        proto_hsubst = listToUFM
                     . map (\(modname, (m, _)) -> (modname, m))
                     . Map.toList
                     $ Map.intersection provs reqs
    in mkShHoleSubst dflags proto_hsubst

-- | Find the idempotent fixed point of a non-idempotent substitution on
-- 'Module's.
fixShHoleSubst :: DynFlags -> ShHoleSubst -> IO ShHoleSubst
fixShHoleSubst dflags env0 = f env0 where
    f env | not fixpoint = f =<< T.mapM (renameHoleModule dflags env . fst) env
          | otherwise    = return env
        where fixpoint = isNullUFM (intersectUFM_C const in_scope env)
              in_scope = unionManyUniqSets (map snd (eltsUFM env))

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
    (m', _) <- substHoleModule (hsc_dflags hsc_env) env m
    if m == m'
        then return n
        else setNameModule hsc_env (Just m') n

-- | Substitutes holes in a 'Module', but not at the top level;
-- this is the behavior you want when substituting the 'nameModule' of a 'Name'.
-- @p(A -> HOLE:A):B@ maps to @p(A -> q():A):B@ with @A -> q():A@;
-- this substitution has no effect on @HOLE:A@.
substHoleModule :: DynFlags -> ShHoleSubst -> Module -> IO (Module, ShFreeHoles)
substHoleModule dflags env m
  | not (isHoleModule m) = renameHoleModule dflags env m
  | otherwise = return (m, unitUniqSet (moduleName m))

-- | Substitutes holes in a 'Module'.  NOT suitable for being called
-- directly on a 'nameModule'.
-- @p(A -> HOLE:A):B@ maps to @p(A -> q():A):B@ with @A -> q():A@;
-- similarly, @HOLE:A@ maps to @q():A@.
renameHoleModule :: DynFlags -> ShHoleSubst -> Module -> IO (Module, ShFreeHoles)
renameHoleModule dflags env m
  | not (isHoleModule m) = do
    shpk <- lookupPackageKey dflags (modulePackageKey m)
    case shpk of
        ShPackageKey { shPackageKeyName = pn,
                       shPackageKeySourcePackageId = spid,
                       shPackageKeyInsts = insts,
                       shPackageKeyFreeHoles = in_scope }
            | isNullUFM (intersectUFM_C const in_scope env) -> return (m, in_scope)
            | otherwise -> do
                insts' <- mapM (\(modname, mod) -> do
                            -- XXX todo use this
                            (mod', _) <- renameHoleModule dflags env mod
                            return (modname, mod')) insts
                (pk', in_scope') <- newPackageKeyWithScope dflags pn spid insts'
                return (mkModule pk' (moduleName m), in_scope')
        ShWiredPackageKey pk | pk == holePackageKey -> return (m, unitUniqSet (moduleName m))
        ShWiredPackageKey _ -> return (m, emptyUniqSet)
  | Just (m', in_scope') <- lookupUFM env (moduleName m) = return (m', in_scope')
  -- NB m = HOLE:Blah, that's what's in scope.
  | otherwise = return (m, unitUniqSet (moduleName m))

-- | Generalize a 'PackageKey' into one where all the holes are indefinite.
-- @p(A -> q():A) generalizes to p(A -> HOLE:A)@.
generalizeHolePackageKey :: DynFlags -> PackageKey -> IO PackageKey
generalizeHolePackageKey dflags pk = do
    shpk <- lookupPackageKey dflags pk
    case shpk of
        ShWiredPackageKey _ -> return pk
        ShPackageKey { shPackageKeyName = pn,
                            shPackageKeySourcePackageId = spid,
                            shPackageKeyInsts = insts0 }
          -> let insts = map (\(x, _) -> (x, mkModule holePackageKey x)) insts0
             in newPackageKey dflags pn spid insts

-- | Generalize a 'Module' into one where all the holes are indefinite.
-- @p(A -> ...):C@ generalizes to @p(A -> HOLE:A):C@.  Useful when
-- you need to figure out if you've already type-checked the generalized
-- version of this module, so you don't have to do the whole rigamarole.
generalizeHoleModule :: DynFlags -> Module -> IO Module
generalizeHoleModule dflags m = do
    pk <- generalizeHolePackageKey dflags (modulePackageKey m)
    return (mkModule pk (moduleName m))

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

-- | Compute a name substitution based on the shape of the requirements
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

-- | Substitutes names in a 'Name', suitable for renaming when
-- an include occurs.
--
-- @p(A -> HOLE:A).T@ maps to @p(A -> HOLE:B).T@ with @A -> HOLE:B@;
-- similarly, @HOLE:A.T@ maps to @HOLE:B.T@.
renameHoleName :: HscEnv -> ShHoleSubst -> Name -> IO Name
renameHoleName hsc_env env n = do
    let m = nameModule n
        dflags = hsc_dflags hsc_env
    -- This line distinguishes this from 'substHoleName'.
    (m', _) <- renameHoleModule dflags env m
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
