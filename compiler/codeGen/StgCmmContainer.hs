-----------------------------------------------------------------------------
--
-- Code generation for resource containers
--
-----------------------------------------------------------------------------

module StgCmmContainer (
        rcType,

        rcEnterThunk,
        rcFrom,
        rcCurrent, rcSet,

        rcSave, rcMaybeSave, rcRestore,
  ) where

#include "HsVersions.h"

import StgCmmUtils
import StgCmmMonad
import StgCmmForeign

import Cmm
import CmmUtils

import DynFlags

-----------------------------------------------------------------------------
--
-- Utils (move out later)
--
-----------------------------------------------------------------------------

cmmBlockShift, cmmBdescrShift, cmmMBlockMask, cmmBlockMask :: DynFlags -> CmmExpr
cmmBlockShift dflags = mkIntExpr dflags (bLOCK_SHIFT dflags)
cmmBdescrShift dflags = mkIntExpr dflags (bDESCR_SHIFT dflags)
cmmMBlockMask dflags = mkIntExpr dflags (mBLOCK_MASK dflags)
cmmBlockMask dflags = mkIntExpr dflags (bLOCK_MASK dflags)

--  ((((p) &  MBLOCK_MASK & ~BLOCK_MASK) >> (BLOCK_SHIFT-BDESCR_SHIFT)) \
--   | ((p) & ~MBLOCK_MASK))
-- XXX make sure this gets optimized
cmmBdescr :: DynFlags -> CmmExpr -> CmmExpr
cmmBdescr d p =
  cmmOrWord d
    (cmmUShrWord d (cmmAndWord d p (cmmAndWord d (cmmMBlockMask d) (cmmNotWord d (cmmBlockMask d))))
                   (cmmSubWord d (cmmBlockShift d) (cmmBdescrShift d)))
    (cmmAndWord d p (cmmNotWord d (cmmMBlockMask d)))

-----------------------------------------------------------------------------
--
-- Resource limits
--
-----------------------------------------------------------------------------

rcType :: DynFlags -> CmmType -- Type of a cost centre
rcType = bWord

-- Bdescr(Hp)->rc
rcCurrent :: DynFlags -> CmmExpr
rcCurrent dflags = CmmReg (CmmGlobal RC)

rcSet :: CmmReg -> FCode ()
rcSet rc = do
    dflags <- getDynFlags
    emitCloseNursery
    -- RC = rc
    emitAssign (CmmGlobal RC) (CmmReg rc)
    -- CurrentNursery = rc->nursery;
    emitAssign
        (CmmGlobal CurrentNursery)
        (CmmLoad (cmmRegOffB rc (oFFSET_ResourceContainer_nursery dflags)) (bWord dflags))
    emitOpenNursery

rcFrom :: DynFlags
               -> CmmExpr       -- A closure pointer
               -> CmmExpr       -- The resource container of that closure
rcFrom dflags cl =
    -- Bdescr(cl)->rc
    CmmLoad (cmmOffset dflags (cmmBdescr dflags cl) (oFFSET_bdescr_rc dflags)) (rcType dflags)

---------------------------------------------------------------------------
--      Saving and restoring the current resource container
---------------------------------------------------------------------------

{-
See [Saving the current cost centre]

You also have to open/close the nursery!  Wait, what about heap checks?
Well, if we cross a function boundary, we will *not* get charged
for the heap; thus, we only need to ensure the same nursery
is *restored* after, because that one is "primed" in some sense.
There is probably some debugging code that could be added here.
-}

rcSave :: FCode (Maybe LocalReg)
        -- Returns Nothing if profiling is off
rcSave
  = do dflags <- getDynFlags
       if False -- not (gopt Opt_ResourceLimitsOn dflags)
           then return Nothing
           else do local_rc <- newTemp (rcType dflags)
                   emitAssign (CmmLocal local_rc) (rcCurrent dflags)
                   return (Just local_rc)

rcMaybeSave :: Bool -> FCode (Maybe LocalReg)
rcMaybeSave False = return Nothing
rcMaybeSave True = rcSave

rcRestore :: Maybe LocalReg -> FCode ()
rcRestore Nothing
  = return ()
rcRestore (Just local_rc)
  = rcSet (CmmLocal local_rc)


-- -----------------------------------------------------------------------
-- Setting the current cost centre on entry to a closure

rcEnterThunk :: CmmExpr -> FCode ()
rcEnterThunk closure =
  ifResourceLimits $ do
      dflags <- getDynFlags
      rc <- assignTemp (rcFrom dflags closure)
      rcSet (CmmLocal rc)

ifResourceLimits :: FCode () -> FCode ()
ifResourceLimits code = do
    -- dflags <- getDynFlags
    code
    {-
    if gopt Opt_ResourceLimitsOn dflags
        then code
        else return ()
    -}

