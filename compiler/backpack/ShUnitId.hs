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

-- NB: didn't put this in Module because we need DynFlags, that seems a bit too
-- low in the hierarchy, need to refer to DynFlags

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

