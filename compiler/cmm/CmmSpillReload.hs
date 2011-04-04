{-# LANGUAGE GADTs,NoMonoLocalBinds #-}
-- Norman likes local bindings
-- If this module lives on I'd like to get rid of this flag in due course

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
#if __GLASGOW_HASKELL__ >= 701
-- GHC 7.0.1 improved incomplete pattern warnings with GADTs
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
#endif

module CmmSpillReload
  ( DualLive(..)
  , dualLiveLattice, dualLiveTransfers, dualLiveness
  --, insertSpillsAndReloads  --- XXX todo check live-in at entry against formals
  , dualLivenessWithInsertion

  , inlineAssignments
  , removeDeadAssignmentsAndReloads
  )
where

import BlockId
import Cmm
import CmmExpr
import CmmLive
import OptimizationFuel

import Control.Monad
import Outputable hiding (empty)
import qualified Outputable as PP
import UniqSet
import UniqFM

import Compiler.Hoopl
import Data.Maybe
import Prelude hiding (succ, zip)

{- Note [Overview of spill/reload]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The point of this module is to insert spills and reloads to
establish the invariant that at a call (or at any proc point with
an established protocol) all live variables not expected in
registers are sitting on the stack.  We use a backward analysis to
insert spills and reloads.  It should be followed by a
forward transformation to sink reloads as deeply as possible, so as
to reduce register pressure.

A variable can be expected to be live in a register, live on the
stack, or both.  This analysis ensures that spills and reloads are
inserted as needed to make sure that every live variable needed
after a call is available on the stack.  Spills are pushed back to
their reaching definitions, but reloads are dropped wherever needed
and will have to be sunk by a later forward transformation.
-}

data DualLive = DualLive { on_stack :: RegSet, in_regs :: RegSet }

dualUnion :: DualLive -> DualLive -> DualLive
dualUnion (DualLive s r) (DualLive s' r') =
    DualLive (s `unionUniqSets` s') (r `unionUniqSets` r') 

dualUnionList :: [DualLive] -> DualLive
dualUnionList ls = DualLive ss rs
    where ss = unionManyUniqSets $ map on_stack ls
          rs = unionManyUniqSets $ map in_regs  ls

changeStack, changeRegs :: (RegSet -> RegSet) -> DualLive -> DualLive
changeStack f live = live { on_stack = f (on_stack live) }
changeRegs  f live = live { in_regs  = f (in_regs  live) }


dualLiveLattice :: DataflowLattice DualLive
dualLiveLattice = DataflowLattice "variables live in registers and on stack" empty add
    where empty = DualLive emptyRegSet emptyRegSet
          add _ (OldFact old) (NewFact new) = (changeIf $ change1 || change2, DualLive stack regs)
            where (change1, stack) = add1 (on_stack old) (on_stack new)
                  (change2, regs)  = add1 (in_regs old)  (in_regs new)
          add1 old new = if sizeUniqSet join > sizeUniqSet old then (True, join) else (False, old)
            where join = unionUniqSets old new

dualLivenessWithInsertion :: BlockSet -> CmmGraph -> FuelUniqSM CmmGraph
dualLivenessWithInsertion procPoints g =
  liftM fst $ dataflowPassBwd g [] $ analRewBwd dualLiveLattice
                                                (dualLiveTransfers (g_entry g) procPoints)
                                                (insertSpillAndReloadRewrites g procPoints)

dualLiveness :: BlockSet -> CmmGraph -> FuelUniqSM (BlockEnv DualLive)
dualLiveness procPoints g =
  liftM snd $ dataflowPassBwd g [] $ analBwd dualLiveLattice $ dualLiveTransfers (g_entry g) procPoints

dualLiveTransfers :: BlockId -> BlockSet -> (BwdTransfer CmmNode DualLive)
dualLiveTransfers entry procPoints = mkBTransfer3 first middle last
    where first :: CmmNode C O -> DualLive -> DualLive
          first (CmmEntry id) live = check live id $  -- live at procPoint => spill
            if id /= entry && setMember id procPoints
               then DualLive { on_stack = on_stack live `plusRegSet` in_regs live
                             , in_regs  = emptyRegSet }
               else live
            where check live id x = if id == entry then noLiveOnEntry id (in_regs live) x else x

          middle :: CmmNode O O -> DualLive -> DualLive
          middle m live = changeStack updSlots $ changeRegs (xferLiveMiddle m) (changeRegs regs_in live)
            where xferLiveMiddle = case getBTransfer3 xferLive of (_, middle, _) -> middle
	          regs_in :: RegSet -> RegSet
                  regs_in live = case m of CmmUnsafeForeignCall {} -> emptyRegSet
                                           _ -> live
                  updSlots live = foldSlotsUsed reload (foldSlotsDefd spill live m) m
                  spill  live s@(RegSlot r, _, _) = check s $ deleteFromRegSet live r
                  spill  live _ = live
                  reload live s@(RegSlot r, _, _) = check s $ extendRegSet live r
                  reload live _ = live
                  check (RegSlot (LocalReg _ ty), o, w) x
                     | o == w && w == widthInBytes (typeWidth ty) = x
                  check _ _ = panic "middleDualLiveness unsupported: slices"
          last :: CmmNode O C -> FactBase DualLive -> DualLive
          last l fb = case l of
            CmmBranch id                   -> lkp id
            l@(CmmCall {cml_cont=Nothing}) -> changeRegs (gen l . kill l) empty
            l@(CmmCall {cml_cont=Just k})  -> call l k
            l@(CmmForeignCall {succ=k})    -> call l k
            l@(CmmCondBranch _ t f)        -> changeRegs (gen l . kill l) $ dualUnion (lkp t) (lkp f)
            l@(CmmSwitch _ tbl)            -> changeRegs (gen l . kill l) $ dualUnionList $ map lkp (catMaybes tbl)
            where empty = fact_bot dualLiveLattice
                  lkp id = empty `fromMaybe` lookupFact id fb
                  call l k = DualLive (on_stack (lkp k)) (gen l emptyRegSet)

gen  :: UserOfLocalRegs    a => a -> RegSet -> RegSet
gen  a live = foldRegsUsed extendRegSet     live a
kill :: DefinerOfLocalRegs a => a -> RegSet -> RegSet
kill a live = foldRegsDefd deleteFromRegSet live a

insertSpillAndReloadRewrites :: CmmGraph -> BlockSet -> CmmBwdRewrite DualLive
insertSpillAndReloadRewrites graph procPoints = deepBwdRw3 first middle nothing
  -- Beware: deepBwdRw with one polymorphic function seems more reasonable here,
  -- but GHC miscompiles it, see bug #4044.
    where first :: CmmNode C O -> Fact O DualLive -> CmmReplGraph C O
          first e@(CmmEntry id) live = return $
            if id /= (g_entry graph) && setMember id procPoints then
              case map reload (uniqSetToList spill_regs) of
                [] -> Nothing
                is -> Just $ mkFirst e <*> mkMiddles is
            else Nothing
              where
                -- If we are splitting procedures, we need the LastForeignCall
                -- to spill its results to the stack because they will only
                -- be used by a separate procedure (so they can't stay in LocalRegs).
                splitting = True
                spill_regs = if splitting then in_regs live
                             else in_regs live `minusRegSet` defs
                defs = case mapLookup id firstDefs of
                           Just defs -> defs
                           Nothing   -> emptyRegSet
                -- A LastForeignCall may contain some definitions, which take place
                -- on return from the function call. Therefore, we build a map (firstDefs)
                -- from BlockId to the set of variables defined on return to the BlockId.
                firstDefs = mapFold addLive emptyBlockMap (toBlockMap graph)
                addLive :: CmmBlock -> BlockEnv RegSet -> BlockEnv RegSet
                addLive b env = case lastNode b of
                                  CmmForeignCall {succ=k, res=defs} -> add k (mkRegSet defs) env
                                  _                                 -> env
                add bid defs env = mapInsert bid defs'' env
                  where defs'' = case mapLookup bid env of
                                   Just defs' -> timesRegSet defs defs'
                                   Nothing    -> defs

          middle :: CmmNode O O -> Fact O DualLive -> CmmReplGraph O O
          middle (CmmAssign (CmmLocal reg) (CmmLoad (CmmStackSlot (RegSlot reg') _) _)) _ | reg == reg' = return Nothing
          middle m@(CmmAssign (CmmLocal reg) _) live = return $
              if reg `elemRegSet` on_stack live then -- must spill
                   my_trace "Spilling" (f4sep [text "spill" <+> ppr reg,
                                               text "after"{-, ppr m-}]) $
                   Just $ mkMiddles $ [m, spill reg]
              else Nothing
          middle m@(CmmUnsafeForeignCall _ fs _) live = return $
            case map spill  (filter (flip elemRegSet (on_stack live)) fs) ++
                 map reload (uniqSetToList (kill fs (in_regs live))) of
              []      -> Nothing
              reloads -> Just $ mkMiddles (m : reloads)
          middle _ _ = return Nothing

          nothing _ _ = return Nothing

regSlot :: LocalReg -> CmmExpr
regSlot r = CmmStackSlot (RegSlot r) (widthInBytes $ typeWidth $ localRegType r)

spill, reload :: LocalReg -> CmmNode O O
spill  r = CmmStore  (regSlot r) (CmmReg $ CmmLocal r)
reload r = CmmAssign (CmmLocal r) (CmmLoad (regSlot r) $ localRegType r)

removeDeadAssignmentsAndReloads :: BlockSet -> CmmGraph -> FuelUniqSM CmmGraph
removeDeadAssignmentsAndReloads procPoints g =
   liftM fst $ dataflowPassBwd g [] $ analRewBwd dualLiveLattice
                                                 (dualLiveTransfers (g_entry g) procPoints)
                                                 rewrites
   where rewrites = deepBwdRw3 nothing middle nothing
         -- Beware: deepBwdRw with one polymorphic function seems more reasonable here,
         -- but GHC panics while compiling, see bug #4045.
         middle :: CmmNode O O -> Fact O DualLive -> CmmReplGraph O O
         middle (CmmAssign (CmmLocal reg') _) live | not (reg' `elemRegSet` in_regs live) = return $ Just emptyGraph
         -- XXX maybe this should be somewhere else...
         middle (CmmStore lhs (CmmLoad rhs _)) _ | lhs == rhs = return $ Just emptyGraph
         middle _ _ = return Nothing

         nothing _ _ = return Nothing

----------------------------------------------------------------
--- Assignment inlning

-- The idea is to maintain a map of local registers that may be
-- inlined at any given point in time.  As we process instructions,
-- changes to memory locations and registers may invalidate some of this
-- inlinings.  This also has the side effect of sinking reloads as
-- deep as possible (reducing memory pressure) as well as allowing us
-- to eliminate unnecessary memory-register roundtrips.

type AssignmentMap = UniqFM (WithTop (LocalReg, CmmExpr))

-- ToDo: Move this into somewhere more general (UniqFM? That will
-- introduce a Hoopl dependency on that file.) -- EZY
joinUFM :: JoinFun v -> JoinFun (UniqFM v)
joinUFM eltJoin l (OldFact old) (NewFact new) = foldUFM_Directly add (NoChange, old) new
    where add k new_v (ch, joinmap) =
            case lookupUFM_Directly joinmap k of
                Nothing -> (SomeChange, addToUFM_Directly joinmap k new_v)
                Just old_v -> case eltJoin l (OldFact old_v) (NewFact new_v) of
                                (SomeChange, v') -> (SomeChange, addToUFM_Directly joinmap k v')
                                (NoChange, _) -> (ch, joinmap)

assignmentLattice :: DataflowLattice AssignmentMap
assignmentLattice = DataflowLattice "assignments for registers" emptyUFM (joinUFM (extendJoinDomain add))
    where add _ (OldFact old) (NewFact new)
            | old == new = (NoChange,   PElem old)
            | otherwise  = (SomeChange, Top)

middleAssignment :: CmmNode O O -> AssignmentMap -> AssignmentMap
-- Stack slots for registers are treated specially: we maintain
-- the invariant that the stack slot will always accurately reflect the
-- contents of a variable.  This invariant only holds because we only
-- generate register slots during the spilling phase, and the spilling
-- phase always spills when the register changes, so we will never see a
-- lone 'abc = ...' (where ... is not a reload) without a subsequent
-- spill.  (We could probably write another quick analysis to check that
-- this invariant holds.) If this invariant holds, then any reload
-- (that's what an assignment to the register from a stack slot is)
-- simply adds a register to the available assignments without
-- invalidating any existing references to the register.
middleAssignment (CmmAssign (CmmLocal r) e@(CmmLoad l _)) assign
    | l `isStackSlotOf` r = addToUFM assign r (PElem (r, e))
{-
-- We do something clever for global register bumps: since at this point
-- the only global register is Hp, and most usages of it involve
-- offsets, we simply adjust all of the references to it when it gets
-- bumped.  XXX This seemed like a good idea, but it doesn't actually
-- do anything, since we actually want to /eliminate/ these bumps
-- altogether, and this analysis doesn't really help us do that...
middleAssignment (CmmAssign reg@(CmmGlobal _) new@(CmmRegOff reg'@(CmmGlobal _) i)) assign
    | reg == reg' = mapUFM p assign
                where p (PElem (r, e)) = PElem (r, sub e)
                      p old = old
                      sub (CmmLoad e t) = CmmLoad (sub e) t
                      sub (CmmReg new_reg) | new_reg == reg = new
                      sub (CmmMachOp m es) = CmmMachOp m (map sub es)
                      sub (CmmRegOff new_reg i') | new_reg == reg = CmmRegOff reg (i+i')
                      sub old = old
-}
-- When we assign anything else to a register, we invalidate all current
-- assignments that contain an assignment to that register, and then, if
-- it's a local assignment, add this assignment to our map.
middleAssignment (CmmAssign reg e) assign
    = f (mapUFM p assign)
      where p (PElem (_, e')) | reg `regUsedIn` e' = Top
            p old = old
            f m | (CmmLocal r) <- reg, inlinable e = addToUFM m r (PElem (r, e))
                | otherwise = m
-- Once again, treat stores of registers to register slots specially
middleAssignment (CmmStore l (CmmReg (CmmLocal r))) assign
    | l `isStackSlotOf` r = assign
-- When a store occurs, invalidate all current assignments that rely on
-- the memory location that got clobbered.  Note that stack slots have
-- already been handled.
middleAssignment (CmmStore lhs rhs) assign
    = mapUFM p assign
      where p (PElem x) | (lhs, rhs) `clobbers` x = Top
            p old = old
-- This is tricky, because whether or not an unsafe foreign call is safe
-- depends on how far along the pipeline we are.  Current choice is
-- liberal.
middleAssignment (CmmUnsafeForeignCall {}) assign = assign -- mapUFM (const Top) assign
middleAssignment (CmmComment {})           assign = assign

-- Policy for what kinds of expressions we will inline.
inlinable :: CmmExpr -> Bool
inlinable (CmmLit{}) = True
inlinable (CmmLoad e _) = inlinable e
inlinable (CmmReg{}) = True
inlinable (CmmMachOp _ _) = False -- maybe allow inlining a few machops
inlinable (CmmStackSlot{}) = True
inlinable (CmmRegOff _ _) = False -- same here...

-- Assumptions:
--  * Stack slots do not overlap with any other memory locations
--  * Non stack-slot stores always conflict with each other.  (This is
--    not always the case; we could probably do something special for Hp)
--  * Stack slots for different areas do not overlap
--  * Stack slots within the same area and different offsets may
--    overlap; we need to do a size check (see 'overlaps').
clobbers :: (CmmExpr, CmmExpr) -> (LocalReg, CmmExpr) -> Bool
clobbers (ss@CmmStackSlot{}, CmmReg (CmmLocal r)) (r', CmmLoad (ss'@CmmStackSlot{}) _)
    | r == r', ss == ss' = False -- No-op on the stack slot
clobbers (CmmStackSlot (CallArea a) o, rhs) (_, expr) = f expr
    where f (CmmLoad (CmmStackSlot (CallArea a') o') t)
            = (a, o, widthInBytes (cmmExprWidth rhs)) `overlaps` (a', o', widthInBytes (typeWidth t))
          f (CmmLoad e _)    = containsStackSlot e
          f (CmmMachOp _ es) = or (map f es)
          f _                = False
          -- Maybe there's an invariant broken if this actually ever
          -- returns True
          containsStackSlot (CmmLoad{}) = True -- load of a load, all bets off
          containsStackSlot (CmmMachOp _ es) = or (map containsStackSlot es)
          containsStackSlot (CmmStackSlot{}) = True
          containsStackSlot _ = False
clobbers _ (_, e) = f e
    where f (CmmLoad (CmmStackSlot _ _) _) = False
          f (CmmLoad{}) = True -- conservative
          f (CmmMachOp _ es) = or (map f es)
          f _ = False

-- Check for memory overlapping.
-- Diagram:
--      4      8     12
--      s -w-  o
--      [ I32  ]
--      [    F64     ]
--      s'   -w'-    o'
type CallSubArea = (AreaId, Int, Int) -- area, offset, width
overlaps :: CallSubArea -> CallSubArea -> Bool
overlaps (a, _, _) (a', _, _) | a /= a' = False
overlaps (_, o, w) (_, o', w') =
    let s  = o  - w
        s' = o' - w'
    in (s' < o) && (s < o) -- Not LTE, because [ I32  ][ I32  ] is OK

lastAssignment :: CmmNode O C -> AssignmentMap -> [(Label, AssignmentMap)]
-- Also very conservative choices
lastAssignment (CmmCall _ (Just k) _ _ _) assign = [(k, mapUFM (const Top) assign)]
lastAssignment (CmmForeignCall {succ=k})  assign = [(k, mapUFM (const Top) assign)]
lastAssignment l assign = map (\id -> (id, assign)) $ successors l

assignmentTransfer :: FwdTransfer CmmNode AssignmentMap
assignmentTransfer = mkFTransfer3 (flip const) middleAssignment ((mkFactBase assignmentLattice .) . lastAssignment)

inlineAssignments :: CmmGraph -> FuelUniqSM CmmGraph
inlineAssignments g =
  liftM fst $ dataflowPassFwd g [(g_entry g, fact_bot assignmentLattice)] $
                              analRewFwd assignmentLattice assignmentTransfer rewrites
  where rewrites = mkFRewrite3 first middle last
        first _ _ = return Nothing
        middle m assign = return . fmap mkMiddle $ inline assign m
        last   l assign = return . fmap mkLast   $ inline assign l
        -- don't inline spills, that's silly, and it breaks invariants
        -- when we arrange the slots later.
        inline :: AssignmentMap -> CmmNode e x -> Maybe (CmmNode e x)
        inline _ (CmmStore l (CmmReg (CmmLocal r))) | l `isStackSlotOf` r = Nothing
        inline assign n = if foldRegsUsed (\z r -> z || inside r) False n then Just (mapExp inlineExp n) else Nothing
            where inside r = case lookupUFM assign r of
                                Just (PElem _) -> True
                                _ -> False
                  inlineExp (CmmLoad e t) = CmmLoad (inlineExp e) t
                  inlineExp old@(CmmReg (CmmLocal r))
                    = case lookupUFM assign r of
                        Just (PElem (_, x)) -> x
                        _ -> old
                  inlineExp (CmmMachOp m es) = CmmMachOp m (map inlineExp es)
                  inlineExp old@(CmmRegOff (CmmLocal r) i)
                    = case lookupUFM assign r of
                        Just (PElem (_, x)) -> CmmMachOp (MO_Add rep) [x, CmmLit (CmmInt (fromIntegral i) rep)]
                            where rep = typeWidth (localRegType r)
                        _ -> old
                  inlineExp old = old

---------------------
-- prettyprinting

ppr_regs :: String -> RegSet -> SDoc
ppr_regs s regs = text s <+> commafy (map ppr $ uniqSetToList regs)
  where commafy xs = hsep $ punctuate comma xs

instance Outputable DualLive where
  ppr (DualLive {in_regs = regs, on_stack = stack}) =
      if isEmptyUniqSet regs && isEmptyUniqSet stack then
          text "<nothing-live>"
      else
          nest 2 $ fsep [if isEmptyUniqSet regs then PP.empty
                         else (ppr_regs "live in regs =" regs),
                         if isEmptyUniqSet stack then PP.empty
                         else (ppr_regs "live on stack =" stack)]

-- ToDo: Outputable instance for AssignmentMap

my_trace :: String -> SDoc -> a -> a
my_trace = if False then pprTrace else \_ _ a -> a

f4sep :: [SDoc] -> SDoc
f4sep [] = fsep []
f4sep (d:ds) = fsep (d : map (nest 4) ds)
