-----------------------------------------------------------------------------
--
-- Code generation for resource containers
--
-----------------------------------------------------------------------------

module StgCmmContainer (
        rcType,
        rcFrom,
        rcCurrent,
        rcReset,
        rcRestoreFrame,
        ifResourceLimits
  ) where

#include "HsVersions.h"

import StgCmmUtils
import StgCmmMonad

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
rcCurrent _ = CmmReg (CmmGlobal RC)

-- OldRC = RC
rcReset :: DynFlags -> CmmAGraph
rcReset dflags = mkAssign (CmmGlobal OldRC) rcCurrent

rcFrom :: DynFlags
               -> CmmExpr       -- A closure pointer
               -> CmmExpr       -- The resource container of that closure
rcFrom dflags cl =
    -- Bdescr(cl)->rc
    CmmLoad (cmmOffset dflags (cmmBdescr dflags cl) (oFFSET_bdescr_rc dflags)) (rcType dflags)

ifResourceLimits :: FCode () -> FCode ()
ifResourceLimits code = do
    -- dflags <- getDynFlags
    code
    {-
    if gopt Opt_ResourceLimitsOn dflags
        then code
        else return ()
    -}

