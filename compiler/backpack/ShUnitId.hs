{-# LANGUAGE CPP #-}
module ShUnitId(
    ShFreeHoles,

    newUnitId,
    newUnitId',
    newUnitIdWithScope,
    newShUnitId,
    lookupUnitId,

    unitIdComponentId,
    unitIdInsts,
    unitIdFreeHoles,
    moduleFreeHoles,

    generalizeHoleModule,
    generalizeHoleUnitId,
    canonicalizeModule,

    pprUnitId
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

-- Note: [UnitId cache]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
-- The built-in UnitId type (used by Module, Name, etc)
-- records the instantiation of the package as an MD5 hash
-- which is not reversible without some extra information.
-- However, the shape merging process requires us to be able
-- to substitute Module occurrences /inside/ the UnitID.
--
-- Thus, we maintain the invariant: for every UnitId
-- in our system, either:
--
--      1. It has an empty hole mapping (and is thus equal
--         to the ComponentId), or
--      2. We've recorded the associated mapping in the
--         UnitIdCache.
--
-- A UnitId can be expanded into a ShUnitId which has
-- the instance mapping.  In the mapping, we don't bother
-- expanding a 'Module'; depending on 'shUnitIdFreeHoles',
-- it may not be necessary to do a substitution (you only
-- need to drill down when substituing HOLE:H if H is in scope.
--
-- Note that ShUnitId is different from IndefUnitId/IndefiniteUnitId;
-- the latter data type is "fully-expanded" (whereas ShUnitId only
-- unrolls the mapping one level.)  This makes the latter suitable
-- for serializing/deserializing in the package database.

-- Note: [Module name in scope set]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Similar to InScopeSet, ShFreeHoles is an optimization that
-- allows us to avoid expanding a UnitId into an ShUnitId
-- if there isn't actually anything in the module expression that
-- we can substitute.

-- | Given a Name or Module, the 'ShFreeHoles' contains the set
-- of free variables, i.e. HOLE:A modules, which may be substituted.
-- If this set is empty no substitutions are possible.
type ShFreeHoles = UniqSet ModuleName

-- | Returns the hole mapping of a 'UnitId'.
unitIdInsts :: DynFlags -> UnitId -> IO [(ModuleName, Module)]
unitIdInsts dflags pk = fmap shUnitIdInsts (lookupUnitId dflags pk)

-- | Returns the 'ComponentId' of a 'UnitId'.
unitIdComponentId :: DynFlags -> UnitId -> IO ComponentId
unitIdComponentId dflags pk = fmap shUnitIdComponentId (lookupUnitId dflags pk)

-- | Returns the free holes of a 'UnitId'. NB: if this
-- 'UnitId' is a 'holeUnitId', this will return an
-- empty set; use 'moduleFreeHoles' to handle HOLE:A properly.
unitIdFreeHoles :: DynFlags -> UnitId -> IO (UniqSet ModuleName)
unitIdFreeHoles dflags pk = fmap shUnitIdFreeHoles (lookupUnitId dflags pk)

-- | Calculate the free holes of a 'Module'.
moduleFreeHoles :: DynFlags -> Module -> IO ShFreeHoles
moduleFreeHoles dflags m
    | moduleUnitId m == holeUnitId = return (unitUniqSet (moduleName m))
    | otherwise = unitIdFreeHoles dflags (moduleUnitId m)

-- | Calculate the free holes of the hole map @[('ModuleName', 'Module')]@.
calcInstsFreeHoles :: DynFlags -> [(ModuleName, Module)] -> IO ShFreeHoles
calcInstsFreeHoles dflags insts =
    fmap unionManyUniqSets (mapM (moduleFreeHoles dflags . snd) insts)

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
            -> IO ShUnitId
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

pprUnitId :: UnitId -> SDoc
pprUnitId pk = sdocWithDynFlags $ \dflags ->
    -- name cache is a memotable
    let shpk = unsafePerformIO (lookupUnitId dflags pk)
    in ppr (shUnitIdComponentId shpk) <>
        (if not (null (shUnitIdInsts shpk)) -- pprIf
          then
            parens (hsep
                (punctuate comma [ ppUnless (moduleName m == modname)
                                            (ppr modname <+> text "->")
                                   <+> ppr m
                                 | (modname, m) <- shUnitIdInsts shpk]))
          else empty)
        <> ifPprDebug (braces (ftext (unitIdFS pk)))

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
generalizeHoleModule :: DynFlags -> Module -> IO Module
generalizeHoleModule dflags m = do
    pk <- generalizeHoleUnitId dflags (moduleUnitId m)
    return (mkModule pk (moduleName m))

-- | Generalize a 'UnitId' into one where all the holes are indefinite.
-- @p(A -> q():A) generalizes to p(A -> HOLE:A)@.
generalizeHoleUnitId :: DynFlags -> UnitId -> IO UnitId
generalizeHoleUnitId dflags pk = do
    ShUnitId { shUnitIdComponentId = uid,
               shUnitIdInsts = insts0 } <- lookupUnitId dflags pk
    let insts = map (\(x, _) -> (x, mkModule holeUnitId x)) insts0
    newUnitId dflags uid insts

-- | Canonicalize a 'Module' so that it uniquely identifies a module.
-- For example, @p(A -> M):A@ canonicalizes to @M@.  Useful for making
-- sure the interface you've loaded as the right @mi_module@.
canonicalizeModule :: DynFlags -> Module -> IO Module
-- Kind of hack to make "not-actually Backpack signatures" work
canonicalizeModule dflags m
    | moduleUnitId m == thisPackage dflags
    , Just sof <- getSigOf dflags (moduleName m)
    = return sof
canonicalizeModule dflags m = do
    let pk = moduleUnitId m
    ShUnitId { shUnitIdInsts = insts } <- lookupUnitId dflags pk
    return $ case lookup (moduleName m) insts of
                Just m' -> m'
                _ -> m
