{-# LANGUAGE CPP #-}
module ShUnitId(
    generalizeHoleModule,
    generalizeHoleUnitId,
    canonicalizeModule,
) where

#include "HsVersions.h"

import Module
import Packages
import UniqFM
import UniqSet
import Outputable
import Util
import DynFlags
import GHC.PackageDb

import System.IO.Unsafe ( unsafePerformIO, unsafeInterleaveIO )
import Control.Monad
import Data.IORef

-- NB: didn't put this in Module, that seems a bit too low in the
-- hierarchy, need to refer to DynFlags

{-
************************************************************************
*                                                                      *
                        Unit Id
*                                                                      *
************************************************************************
-}

-- Note: [Module name in scope set]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Similar to InScopeSet, ShFreeHoles is an optimization that
-- allows us to avoid expanding a UnitId into an ShUnitId
-- if there isn't actually anything in the module expression that
-- we can substitute.

{-
-- | This creates a UnitId, but also makes sure that it's consistent
-- with what we know about it in the package database.
NewUnitId :: DynFlags
          -> ComponentId
          -> [(ModuleName, Module)]
          -> UnitId

-- | Given a 'ComponentName', an 'ComponentId', and sorted mapping of holes to
-- their implementations, compute the 'UnitId' associated with it, as well
-- as the recursively computed 'ShFreeHoles' of holes that may be substituted.
newUnitIdWithScope :: DynFlags
                   -> ComponentId
                   -> [(ModuleName, Module)]
                   -> IO (UnitId, ShFreeHoles)
newUnitIdWithScope dflags uid insts = do
    sh_uid <- newShUnitId dflags uid insts
    pk <- newUnitId' dflags sh_uid
    return (pk, shUnitIdFreeHoles sh_uid)

-- | Given a 'ComponentName' and sorted mapping of holes to
-- their implementations, compute the 'UnitId' associated with it.
-- (Analogous to 'newGlobalBinder').
newUnitId :: DynFlags
          -> ComponentId
          -> [(ModuleName, Module)]
          -> IO UnitId
newUnitId dflags uid insts = do
    fmap fst $ newUnitIdWithScope dflags uid insts

-- | Compute a 'ShUnitId'.  (This is in IO because it computes the
-- free holes.)
newShUnitId :: DynFlags
            -> ComponentId
            -> [(ModuleName, Module)]
            -> IO UnitId
newShUnitId dflags cid insts = do
    -- This is a bit terrible but it will help a lot
    fhs <- unsafeInterleaveIO (calcInstsFreeHoles dflags insts)
    return (ShUnitId cid insts fhs)

-- | Given a 'ShUnitId', compute the 'UnitId' associated with it.
-- This function doesn't calculate the 'ShFreeHoles', because it is
-- provided with 'ShUnitId'.
newUnitId' :: DynFlags -> ShUnitId -> IO UnitId
newUnitId' dflags shpk@(ShUnitId uid insts _) = do
    let pk = mkUnitId uid insts
        pkt_var = unitIdCache dflags
    pk_cache <- readIORef pkt_var
    let consistent pk_cache = maybe True (==shpk) (lookupUFM pk_cache pk)
    MASSERT2( consistent pk_cache, ppr shpk $$ ppr pk_cache )
    when (not (elemUFM pk pk_cache)) $
        atomicModifyIORef' pkt_var (\pk_cache ->
            -- Could race, but it's guaranteed to be the same
            ASSERT( consistent pk_cache ) (addToUFM pk_cache pk shpk, ()))
    return pk

-- | Given a 'UnitId', reverse lookup the 'ShUnitId' associated
-- with it.
lookupUnitId :: DynFlags
             -> UnitId
             -> IO ShUnitId
lookupUnitId dflags pk = do
    let pkt_var = unitIdCache dflags
    pk_cache <- readIORef pkt_var
    case lookupUFM pk_cache pk of
        Just r -> return r
        _ -> return (mkLegacyId pk)

-- | Creates a 'ShUnitId' from a 'UnitId' by assuming the "no holes same
-- name convention", i.e. that the unique 'UnitId' of a 'ComponentId' with
-- no holes is the same string.
mkLegacyId :: UnitId -> ShUnitId
mkLegacyId pk
    = ShUnitId { shUnitIdComponentId = ComponentId (unitIdFS pk)
               , shUnitIdInsts = []
               , shUnitIdFreeHoles = emptyUniqSet
               }
               -}

-- NB: newUnitId and lookupUnitId are mutually recursive; this
-- recursion is guaranteed to bottom out because you can't set up cycles
-- of UnitIds.


{-
************************************************************************
*                                                                      *
                        Generalize/Canonicalize
*                                                                      *
************************************************************************
-}

-- | Generalize a 'Module' into one where all the holes are indefinite.
-- @p(A -> ...):C@ generalizes to @p(A -> HOLE:A):C@.  This is primarily
-- used when we have a unit ID, and we know that the generalized version
-- has already been typechecked, so we can load that interface and then
-- rename it to the requested unit ID.
generalizeHoleModule :: Module -> Module
generalizeHoleModule m =
    let uid = generalizeHoleUnitId (moduleUnitId m)
    in mkModule uid (moduleName m)

-- | Generalize a 'UnitId' into one where all the holes are indefinite.
-- @p(A -> q():A) generalizes to p(A -> HOLE:A)@.
generalizeHoleUnitId :: UnitId -> UnitId
generalizeHoleUnitId =
    mapUnitIdInsts (\(x, _) -> mkModule holeUnitId x)

-- | Canonicalize a 'Module' so that it uniquely identifies a module.
-- For example, @p(A -> M):A@ canonicalizes to @M@.  Useful for making
-- sure the interface you've loaded as the right @mi_module@.
canonicalizeModule :: DynFlags -> Module -> Module
-- Kind of hack to make "not-actually Backpack signatures" work
canonicalizeModule dflags m
    | moduleUnitId m == thisPackage dflags
    , Just sof <- getSigOf dflags (moduleName m)
    = sof
    | otherwise
    = case lookup (moduleName m) (unitIdInsts (moduleUnitId m)) of
        Just m' -> m'
        _ -> m
