\begin{code}
module TcInteract ( 
     solveInteract, AtomicInert, 
     InertSet, emptyInert, extendInertSet, extractUnsolved, solveOne,
     listToWorkList
  ) where  

#include "HsVersions.h"


import BasicTypes 
import TcCanonical
import VarSet
import Type
import TypeRep 

import Id 
import Var

import TcType
import HsBinds 

import InstEnv 
import Class 
import TyCon 
import Name

import FunDeps

import Control.Monad ( when ) 

import Coercion
import Outputable

import TcRnTypes 
import TcErrors
import TcSMonad 
import qualified Bag as Bag
import qualified Data.Map as Map 
import Maybes 

import Control.Monad( zipWithM, unless )
import FastString ( sLit ) 
import DynFlags
\end{code}

Note [InsertSet invariants]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

An InertSet is a bag of canonical constraints, with the following invariants:

  1 No two constraints react with each other. 
    
    A tricky case is when there exists a given (solved) dictionary 
    constraint and a wanted identical constraint in the inert set, but do 
    not react because reaction would create loopy dictionary evidence for 
    the wanted. See note [Recursive dictionaries]

  2 Given equalities form an idempotent substitution [none of the
    given LHS's occur in any of the given RHS's or reactant parts]

  3 Wanted equalities also form an idempotent substitution
  4 The entire set of equalities is acyclic.

  5 Wanted dictionaries are inert with the top-level axiom set 

  6 Equalities of the form tv1 ~ tv2 always have a touchable variable
    on the left (if possible).
  7 No wanted constraints tv1 ~ tv2 with tv1 touchable. Such constraints 
    will be marked as solved right before being pushed into the inert set. 
    See note [Touchables and givens].
 
Note that 6 and 7 are /not/ enforced by canonicalization but rather by 
insertion in the inert list, ie by TcInteract. 

During the process of solving, the inert set will contain some
previously given constraints, some wanted constraints, and some given
constraints which have arisen from solving wanted constraints. For
now we do not distinguish between given and solved constraints.

Note that we must switch wanted inert items to given when going under an
implication constraint (when in top-level inference mode).

\begin{code}

-- See Note [InertSet invariants]
data InertSet 
  = IS { inert_cts  :: Bag.Bag CanonicalCt 
       , inert_fsks :: Map.Map TcTyVar [(TcTyVar,Coercion)] }
-- inert_fsks contains the *FlattenSkolem* equivalence classes. 
-- inert_fsks extra invariants: 
--    (a) all TcTyVars in the domain and range of inert_fsks are flatten skolems
--    (b) for every mapping tv1 |-> (tv2,co), co : tv2 ~ tv1 

-- newtype InertSet = IS (Bag.Bag CanonicalCt)
instance Outputable InertSet where
  ppr is = vcat [ vcat (map ppr (Bag.bagToList $ inert_cts is))
                , vcat (map (\(v,rest) -> ppr v <+> text "|->" <+> hsep (map (ppr.fst) rest)) 
                       (Map.toList $ inert_fsks is)
                       )
                ]
                       


emptyInert :: InertSet
emptyInert = IS { inert_cts = Bag.emptyBag, inert_fsks = Map.empty } 


extendInertSet :: InertSet -> AtomicInert -> InertSet
-- Simply extend the bag of constraints rebuilding an inert set
extendInertSet (IS { inert_cts  = cts
                   , inert_fsks = fsks }) item 
  = IS { inert_cts  = cts `Bag.snocBag` item 
       , inert_fsks = fsks }


updInertSet :: InertSet -> AtomicInert -> InertSet 
-- Introduces an element in the inert set for the first time 
updInertSet (IS { inert_cts = cts, inert_fsks = fsks })  
            item@(CTyEqCan { cc_id    = cv
                           , cc_tyvar = tv1 
                           , cc_rhs   = xi })
  | Just tv2 <- tcGetTyVar_maybe xi,
    FlatSkol {} <- tcTyVarDetails tv1, 
    FlatSkol {} <- tcTyVarDetails tv2 
  = let cts'  = cts `Bag.snocBag` item 
        fsks' = Map.insertWith (++) tv2 [(tv1, mkCoVarCoercion cv)] fsks
    in IS { inert_cts = cts', inert_fsks = fsks' }
updInertSet (IS { inert_cts = cts
                , inert_fsks = fsks }) item 
  = let cts' = cts `Bag.snocBag` item
    in IS { inert_cts = cts', inert_fsks = fsks } 


foldlInertSetM :: (Monad m) => (a -> AtomicInert -> m a) -> a -> InertSet -> m a 
foldlInertSetM k z (IS { inert_cts = cts }) 
  = Bag.foldlBagM k z cts

extractUnsolved :: InertSet -> (InertSet, CanonicalCts)
extractUnsolved is@(IS {inert_cts = cts}) 
  = (is { inert_cts = cts'}, unsolved)
  where (unsolved, cts') = Bag.partitionBag isWantedCt cts


getFskEqClass :: InertSet -> TcTyVar -> [(TcTyVar,Coercion)] 
-- Precondition: tv is a FlatSkol 
getFskEqClass (IS { inert_cts = cts, inert_fsks = fsks }) tv 
  = case lkpTyEqCanByLhs of
      Nothing  -> fromMaybe [] (Map.lookup tv fsks)  
      Just ceq -> 
        case tcGetTyVar_maybe (cc_rhs ceq) of 
          Just tv_rhs | FlatSkol {} <- tcTyVarDetails tv_rhs
            -> let ceq_co = mkSymCoercion $ mkCoVarCoercion (cc_id ceq)
                   mk_co (v,c) = (v, mkTransCoercion c ceq_co)
               in (tv_rhs, ceq_co): map mk_co (fromMaybe [] $ Map.lookup tv fsks) 
          _ -> []
  where lkpTyEqCanByLhs = Bag.foldlBag lkp Nothing cts 
        lkp :: Maybe CanonicalCt -> CanonicalCt -> Maybe CanonicalCt 
        lkp Nothing ct@(CTyEqCan {cc_tyvar = tv'}) | tv' == tv = Just ct 
        lkp other _ct = other 


isWantedCt :: CanonicalCt -> Bool 
isWantedCt ct = isWanted (cc_flavor ct)

{- TODO: Later ...
data Inert = IS { class_inerts :: FiniteMap Class Atomics
     	          ip_inerts    :: FiniteMap Class Atomics
     	          tyfun_inerts :: FiniteMap TyCon Atomics
		  tyvar_inerts :: FiniteMap TyVar Atomics
                }

Later should we also separate out givens and wanteds?
-}

\end{code}

Note [Touchables and givens]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Touchable variables will never show up in givens which are inputs to
the solver.  However, touchables may show up in givens generated by the flattener.  
For example,

  axioms:
    G Int ~ Char
    F Char ~ Int

  wanted:
    F (G alpha) ~w Int
  
canonicalises to

  G alpha ~g b
  F b ~w Int

which can be put in the inert set.  Suppose we also have a wanted

  alpha ~w Int

We cannot rewrite the given G alpha ~g b using the wanted alpha ~w
Int.  Instead, after reacting alpha ~w Int with the whole inert set,
we observe that we can solve it by unifying alpha with Int, so we mark
it as solved and put it back in the *work list*. [We also immediately unify
alpha := Int, without telling anyone, see trySpontaneousSolve function, to 
avoid doing this in the end.]

Later, because it is solved (given, in effect), we can use it to rewrite 
G alpha ~g b to G Int ~g b, which gets put back in the work list. Eventually, 
we will dispatch the remaining wanted constraints using the top-level axioms.

Finally, note that after reacting a wanted equality with the entire inert set
we may end up with something like

  b ~w alpha

which we should flip around to generate the solved constraint alpha ~s b.

%*********************************************************************
%*                                                                   * 
*                      Main Interaction Solver                       *
*                                                                    *
**********************************************************************

Note [Basic plan] 
~~~~~~~~~~~~~~~~~
1. Canonicalise (unary)
2. Pairwise interaction (binary)
    * Take one from work list 
    * Try all pair-wise interactions with each constraint in inert
3. Try to solve spontaneously for equalities involving touchables 
4. Top-level interaction (binary wrt top-level)
   Superclass decomposition belongs in (4), see note [Superclasses]

\begin{code}

type AtomicInert = CanonicalCt     -- constraint pulled from InertSet
type WorkItem    = CanonicalCt     -- constraint pulled from WorkList

type WorkList    = CanonicalCts    -- A mixture of Given, Wanted, and Solved
type SWorkList   = WorkList        -- A worklist of solved 
                   

listToWorkList :: [WorkItem] -> WorkList
listToWorkList = Bag.listToBag

unionWorkLists :: WorkList -> WorkList -> WorkList 
unionWorkLists = Bag.unionBags 

foldlWorkListM :: (Monad m) => (a -> WorkItem -> m a) -> a -> WorkList -> m a 
foldlWorkListM = Bag.foldlBagM 

isEmptyWorkList :: WorkList -> Bool 
isEmptyWorkList = Bag.isEmptyBag

emptyWorkList :: WorkList
emptyWorkList = Bag.emptyBag

singletonWorkList :: CanonicalCt -> WorkList 
singletonWorkList ct = singleCCan ct 

data StopOrContinue 
  = Stop			-- Work item is consumed
  | ContinueWith WorkItem	-- Not consumed

instance Outputable StopOrContinue where
  ppr Stop             = ptext (sLit "Stop")
  ppr (ContinueWith w) = ptext (sLit "ContinueWith") <+> ppr w

-- Results after interacting a WorkItem as far as possible with an InertSet
data StageResult
  = SR { sr_inerts     :: InertSet
           -- The new InertSet to use (REPLACES the old InertSet)
       , sr_new_work   :: WorkList
           -- Any new work items generated (should be ADDED to the old WorkList)
           -- Invariant: 
           --    sr_stop = Just workitem => workitem is *not* in sr_inerts and
           --                               workitem is inert wrt to sr_inerts
       , sr_stop       :: StopOrContinue
       }

instance Outputable StageResult where
  ppr (SR { sr_inerts = inerts, sr_new_work = work, sr_stop = stop })
    = ptext (sLit "SR") <+> 
      braces (sep [ ptext (sLit "inerts =") <+> ppr inerts <> comma
             	  , ptext (sLit "new work =") <+> ppr work <> comma
             	  , ptext (sLit "stop =") <+> ppr stop])

type SimplifierStage = WorkItem -> InertSet -> TcS StageResult 

-- Combine a sequence of simplifier 'stages' to create a pipeline 
runSolverPipeline :: [(String, SimplifierStage)]
                  -> InertSet -> WorkItem 
                  -> TcS (InertSet, WorkList)
-- Precondition: non-empty list of stages 
runSolverPipeline pipeline inerts workItem
  = do { traceTcS "Start solver pipeline" $ 
            vcat [ ptext (sLit "work item =") <+> ppr workItem
                 , ptext (sLit "inerts    =") <+> ppr inerts]

       ; let itr_in = SR { sr_inerts = inerts
                        , sr_new_work = emptyWorkList
                        , sr_stop = ContinueWith workItem }
       ; itr_out <- run_pipeline pipeline itr_in
       ; let new_inert 
              = case sr_stop itr_out of 
       	          Stop              -> sr_inerts itr_out
                  ContinueWith item -> sr_inerts itr_out `updInertSet` item
       ; return (new_inert, sr_new_work itr_out) }
  where 
    run_pipeline :: [(String, SimplifierStage)]
                 -> StageResult -> TcS StageResult
    run_pipeline [] itr                         = return itr
    run_pipeline _  itr@(SR { sr_stop = Stop }) = return itr

    run_pipeline ((name,stage):stages) 
                 (SR { sr_new_work = accum_work
                     , sr_inerts   = inerts
                     , sr_stop     = ContinueWith work_item })
      = do { itr <- stage work_item inerts 
           ; traceTcS ("Stage result (" ++ name ++ ")") (ppr itr)
           ; let itr' = itr { sr_new_work = sr_new_work itr 
                                            `unionWorkLists` accum_work }
           ; run_pipeline stages itr' }
\end{code}

Example 1:
  Inert:   {c ~ d, F a ~ t, b ~ Int, a ~ ty} (all given)
  Reagent: a ~ [b] (given)

React with (c~d)     ==> IR (ContinueWith (a~[b]))  True    []
React with (F a ~ t) ==> IR (ContinueWith (a~[b]))  False   [F [b] ~ t]
React with (b ~ Int) ==> IR (ContinueWith (a~[Int]) True    []

Example 2:
  Inert:  {c ~w d, F a ~g t, b ~w Int, a ~w ty}
  Reagent: a ~w [b]

React with (c ~w d)   ==> IR (ContinueWith (a~[b]))  True    []
React with (F a ~g t) ==> IR (ContinueWith (a~[b]))  True    []    (can't rewrite given with wanted!)
etc.

Example 3:
  Inert:  {a ~ Int, F Int ~ b} (given)
  Reagent: F a ~ b (wanted)

React with (a ~ Int)   ==> IR (ContinueWith (F Int ~ b)) True []
React with (F Int ~ b) ==> IR Stop True []    -- after substituting we re-canonicalize and get nothing

\begin{code}
-- Main interaction solver: we fully solve the worklist 'in one go', 
-- returning an extended inert set.
--
-- See Note [Touchables and givens].
solveInteract :: InertSet -> WorkList -> TcS InertSet
solveInteract inert ws 
  = do { dyn_flags <- getDynFlags
       ; solveInteractWithDepth (ctxtStkDepth dyn_flags,0,[]) inert ws 
       }
solveOne :: InertSet -> WorkItem -> TcS InertSet 
solveOne inerts workItem 
  = do { dyn_flags <- getDynFlags
       ; solveOneWithDepth (ctxtStkDepth dyn_flags,0,[]) inerts workItem
       }

-----------------
solveInteractWithDepth :: (Int, Int, [WorkItem])
                       -> InertSet -> WorkList -> TcS InertSet
solveInteractWithDepth ctxt@(max_depth,n,stack) inert ws 
  | isEmptyWorkList ws
  = return inert

  | n > max_depth 
  = solverDepthErrorTcS n stack

  | otherwise 
  = do { traceTcS "solveInteractWithDepth" $ 
         vcat [ text "Current depth =" <+> ppr n
              , text "Max depth =" <+> ppr max_depth
              ]
       ; foldlWorkListM (solveOneWithDepth ctxt) inert ws }

------------------
-- Fully interact the given work item with an inert set, and return a
-- new inert set which has assimilated the new information.
solveOneWithDepth :: (Int, Int, [WorkItem])
                  -> InertSet -> WorkItem -> TcS InertSet
solveOneWithDepth (max_depth, n, stack) inert work
  = do { traceTcS0 (indent ++ "Solving {") (ppr work)
       ; (new_inert, new_work) <- runSolverPipeline thePipeline inert work
         
       ; traceTcS0 (indent ++ "Subgoals:") (ppr new_work)

	 -- Recursively solve the new work generated 
         -- from workItem, with a greater depth
       ; res_inert <- solveInteractWithDepth (max_depth, n+1, work:stack)
                                new_inert new_work 

       ; traceTcS0 (indent ++ "Done }") (ppr work) 
       ; return res_inert }
  where
    indent = replicate (2*n) ' '

thePipeline :: [(String,SimplifierStage)]
thePipeline = [ ("interact with inerts", interactWithInertsStage)
              , ("spontaneous solve",    spontaneousSolveStage)
              , ("top-level reactions",  topReactionsStage) ]
\end{code}

*********************************************************************************
*                                                                               * 
                       The spontaneous-solve Stage
*                                                                               *
*********************************************************************************

\begin{code}
spontaneousSolveStage :: SimplifierStage 
spontaneousSolveStage workItem inerts 
  = do { mSolve <- trySpontaneousSolve workItem inerts 
       ; case mSolve of 
           Nothing -> -- no spontaneous solution for him, keep going
               return $ SR { sr_new_work   = emptyWorkList 
                           , sr_inerts     = inerts 
                           , sr_stop       = ContinueWith workItem }

           Just workList' -> -- He has been solved; workList' are all givens 
               return $ SR { sr_new_work = workList'
                           , sr_inerts   = inerts 
                           , sr_stop     = Stop } 
       }
{--
               | isWantedCt workItem 
                           -- Original was wanted we have now made him given so 
                           -- we have to ineract him with the inerts again because 
                           -- of the change in his status. This may produce some work. 
                   -> do { traceTcS "recursive interact with inerts {" $ vcat
                               [ text "work = " <+> ppr workItem'
                               , text "inerts = " <+> ppr inerts ]
                         ; itr_again <- interactWithInertsStage workItem' inerts 
                         ; case sr_stop itr_again of 
                            Stop -> pprPanic "BUG: Impossible to happen" $ 
                                    vcat [ text "Original workitem:" <+> ppr workItem
                                         , text "Spontaneously solved:" <+> ppr workItem'
                                         , text "Solved was consumed, when reacting with inerts:"
                                         , nest 2 (ppr inerts) ]
                            ContinueWith workItem'' -- Now *this* guy is inert wrt to inerts
                                ->  do { traceTcS "end recursive interact }" $ ppr workItem''
                                       ; return $ SR { sr_new_work = sr_new_work itr_again
                                                     , sr_inerts   = sr_inerts itr_again 
                                                                     `extendInertSet` workItem'' 
                                                     , sr_stop     = Stop } }
                         }
               | otherwise
                   -> return $ SR { sr_new_work   = emptyWorkList 
                                  , sr_inerts     = inerts `extendInertSet` workItem' 
                                  , sr_stop       = Stop } }
--} 

-- @trySpontaneousSolve wi@ solves equalities where one side is a
-- touchable unification variable. Returns:
--   * Nothing if we were not able to solve it
--   * Just wi' if we solved it, wi' (now a "given") should be put in the work list.
--     	    See Note [Touchables and givens] 
-- Note, just passing the inerts through for the skolem equivalence classes
trySpontaneousSolve :: WorkItem -> InertSet -> TcS (Maybe SWorkList)
trySpontaneousSolve (CTyEqCan { cc_id = cv, cc_flavor = gw, cc_tyvar = tv1, cc_rhs = xi }) inerts 
  | Just tv2 <- tcGetTyVar_maybe xi
  = do { tch1 <- isTouchableMetaTyVar tv1
       ; tch2 <- isTouchableMetaTyVar tv2
       ; case (tch1, tch2) of
           (True,  True)  -> trySpontaneousEqTwoWay inerts cv gw tv1 tv2
           (True,  False) -> trySpontaneousEqOneWay inerts cv gw tv1 xi
           (False, True)  | tyVarKind tv1 `isSubKind` tyVarKind tv2
                          -> trySpontaneousEqOneWay inerts cv gw tv2 (mkTyVarTy tv1)
	   _ -> return Nothing }
  | otherwise
  = do { tch1 <- isTouchableMetaTyVar tv1
       ; if tch1 then trySpontaneousEqOneWay inerts cv gw tv1 xi
                 else return Nothing }

  -- No need for 
  --      trySpontaneousSolve (CFunEqCan ...) = ...
  -- See Note [No touchables as FunEq RHS] in TcSMonad
trySpontaneousSolve _ _ = return Nothing 

----------------
trySpontaneousEqOneWay :: InertSet -> CoVar -> CtFlavor -> TcTyVar -> Xi
                       -> TcS (Maybe SWorkList)
-- tv is a MetaTyVar, not untouchable
-- Precondition: kind(xi) is a sub-kind of kind(tv)
trySpontaneousEqOneWay inerts cv gw tv xi	
  | not (isSigTyVar tv) || isTyVarTy xi
  = solveWithIdentity inerts cv gw tv xi
  | otherwise
  = return Nothing

----------------
trySpontaneousEqTwoWay :: InertSet -> CoVar -> CtFlavor -> TcTyVar -> TcTyVar
                       -> TcS (Maybe SWorkList)
-- Both tyvars are *touchable* MetaTyvars
-- By the CTyEqCan invariant, k2 `isSubKind` k1
trySpontaneousEqTwoWay inerts cv gw tv1 tv2
  | k1 `eqKind` k2
  , nicer_to_update_tv2 = solveWithIdentity inerts cv gw tv2 (mkTyVarTy tv1)
  | otherwise           = ASSERT( k2 `isSubKind` k1 )
                          solveWithIdentity inerts cv gw tv1 (mkTyVarTy tv2)
  where
    k1 = tyVarKind tv1
    k2 = tyVarKind tv2
    nicer_to_update_tv2 = isSigTyVar tv1 || isSystemName (Var.varName tv2)
\end{code}

Note [Loopy spontaneous solving] 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider the original wanted: 
   wanted :  Maybe (E alpha) ~ alpha 
where E is a type family, such that E (T x) = x. After canonicalization, 
as a result of flattening, we will get: 
   given  : E alpha ~ fsk 
   wanted : alpha ~ Maybe fsk
where (fsk := E alpha, on the side). Now, if we spontaneously *solve* 
(alpha := Maybe fsk) we are in trouble! Instead, we should refrain from solving 
it and keep it as wanted.  In inference mode we'll end up quantifying over
   (alpha ~ Maybe (E alpha))
Hence, 'solveWithIdentity' performs a small occurs check before
actually solving. But this occurs check *must look through* flatten
skolems.

Note [Avoid double unifications] 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The spontaneous solver has to return a given which mentions the unified unification
variable *on the left* of the equality. Here is what happens if not: 
  Original wanted:  (a ~ alpha),  (alpha ~ Int) 
We spontaneously solve the first wanted, without changing the order! 
      given : a ~ alpha      [having unifice alpha := a] 
Now the second wanted comes along, but he cannot rewrite the given, so we simply continue.
At the end we spontaneously solve that guy, *reunifying*  [alpha := Int] 

We avoid this problem by orienting the given so that the unification variable is on the left. 
[Note that alternatively we could attempt to enforce this at canonicalization] 

Avoiding double unifications is yet another reason to disallow touchable unification variables
as RHS of type family equations: F xis ~ alpha. Consider having already spontaneously solved 
a wanted (alpha ~ [b]) by setting alpha := [b]. So the inert set looks like: 
         given : alpha ~ [b]
And now a new wanted (F tau ~ alpha) comes along. Since it does not react with anything 
we will be left with a constraint (F tau ~ alpha) that must cause a unification of 
(alpha := F tau) at some point (either in spontaneous solving, or at the end). But alpha 
is *already* unified so we must not do anything to it. By disallowing naked touchables in 
the RHS of constraints (in favor of introduced flatten skolems) we do not have to worry at 
all about unifying or spontaneously solving (F xis ~ alpha) by unification. 

\begin{code}
----------------
solveWithIdentity :: InertSet 
                  -> CoVar -> CtFlavor -> TcTyVar -> Xi 
                  -> TcS (Maybe SWorkList)
-- Solve with the identity coercion 
-- Precondition: kind(xi) is a sub-kind of kind(tv)
-- See [New Wanted Superclass Work] to see why we do this for *given* as well
solveWithIdentity inerts cv gw tv xi 
  | not (isGiven gw)
  = do { m <- passOccursCheck inerts tv xi 
       ; case m of 
           Nothing -> return Nothing 
           Just (xi_unflat,coi) -- coi : xi_unflat ~ xi  
               -> do { traceTcS "Sneaky unification:" $ 
                       vcat [text "Coercion variable:  " <+> ppr gw, 
                             text "Coercion:           " <+> pprEq (mkTyVarTy tv) xi,
                             text "Left  Kind is     : " <+> ppr (typeKind (mkTyVarTy tv)),
                             text "Right Kind is     : " <+> ppr (typeKind xi)
                            ]
                     ; setWantedTyBind tv xi_unflat        -- Set tv := xi_unflat
                     ; cv_given <- newGivOrDerCoVar (mkTyVarTy tv) xi_unflat xi_unflat
                     ; let flav = mkGivenFlavor gw UnkSkol 
                     ; (cts, co) <- case coi of 
                         ACo co  -> do { can_eqs <- canEq flav cv_given (mkTyVarTy tv) xi_unflat
                                       ; return (can_eqs, co) }
                         IdCo co -> return $ 
                                    (singleCCan (CTyEqCan { cc_id = cv_given 
                                                          , cc_flavor = mkGivenFlavor gw UnkSkol
                                                          , cc_tyvar = tv, cc_rhs = xi }
                                                          -- xi, *not* xi_unflat! 
                                                ), co)
                     ; case gw of 
                         Wanted  {} -> setWantedCoBind  cv co
                         Derived {} -> setDerivedCoBind cv co 
                         _          -> pprPanic "Can't spontaneously solve *given*" empty 

       -- See Note [Avoid double unifications] 

       -- The reason that we create a new given variable (cv_given) instead of reusing cv
       -- is because we do not want to end up with coercion unification variables in the givens.
                     ; return (Just cts) } 
       }
  | otherwise 
  = return Nothing 


passOccursCheck :: InertSet -> TcTyVar -> TcType -> TcS (Maybe (TcType,CoercionI))
-- passOccursCheck inerts tv ty 
-- Traverse the type and make sure that 'tv' does not appear under 
-- some flatten skolem. If it appears under some flatten skolem 
-- look in that flatten skolem equivalence class to see if you can 
-- find a different flatten skolem to use, which does not mention the 
-- variable.
-- Postcondition: Just (ty',coi) <- passOccursCheck tv ty 
--       coi :: ty' ~ ty 
-- NB: I believe there is no need to do the tcView thing here
passOccursCheck is tv (TyConApp tc tys) 
  = do { tys_mbs <- mapM (passOccursCheck is tv) tys 
       ; case allMaybes tys_mbs of 
           Nothing -> return Nothing 
           Just tys_cois -> 
               let (tys',cois') = unzip tys_cois
               in return $ 
                  Just (TyConApp tc tys', mkTyConAppCoI tc cois')
       }
passOccursCheck is tv (PredTy sty) 
  = do { sty_mb <- passOccursCheckPred tv sty 
       ; case sty_mb of 
           Nothing -> return Nothing 
           Just (sty',coi) -> return (Just (PredTy sty', coi))
       }
  where passOccursCheckPred tv (ClassP cn tys)
          = do { tys_mbs <- mapM (passOccursCheck is tv) tys 
               ; case allMaybes tys_mbs of 
                   Nothing -> return Nothing 
                   Just tys_cois -> 
                       let (tys', cois') = unzip tys_cois 
                       in return $ 
                          Just (ClassP cn tys', mkClassPPredCoI cn cois') 
               }
        passOccursCheckPred tv (IParam nm ty)   
          = do { mty <- passOccursCheck is tv ty 
               ; case mty of 
                   Nothing -> return Nothing 
                   Just (ty',co') 
                       -> return (Just (IParam nm ty', 
                                               mkIParamPredCoI nm co')) 
               }
        passOccursCheckPred tv (EqPred ty1 ty2) 
          = do { mty1 <- passOccursCheck is tv ty1 
               ; mty2 <- passOccursCheck is tv ty2 
               ; case (mty1,mty2) of 
                   (Just (ty1',coi1), Just (ty2',coi2))
                       -> return $ 
                          Just (EqPred ty1' ty2', mkEqPredCoI coi1 coi2)
                   _ -> return Nothing 
               }
                           
passOccursCheck is tv (FunTy arg res) 
  = do { arg_mb <- passOccursCheck is tv arg 
       ; res_mb <- passOccursCheck is tv res
       ; case (arg_mb,res_mb) of 
           (Just (arg',coiarg), Just (res',coires)) 
               -> return $ 
                  Just (FunTy arg' res', mkFunTyCoI coiarg coires)
           _ -> return Nothing 
       }

passOccursCheck is tv (AppTy fun arg) 
  = do { fun_mb <- passOccursCheck is tv fun 
       ; arg_mb <- passOccursCheck is tv arg 
       ; case (fun_mb,arg_mb) of 
           (Just (fun',coifun), Just (arg',coiarg)) 
               -> return $ 
                  Just (AppTy fun' arg', mkAppTyCoI coifun coiarg)
           _ -> return Nothing 
       }

passOccursCheck is tv (ForAllTy tv1 ty1) 
  = do { ty1_mb <- passOccursCheck is tv ty1 
       ; case ty1_mb of 
           Nothing -> return Nothing 
           Just (ty1',coi) 
               -> return $ 
                  Just (ForAllTy tv1 ty1', mkForAllTyCoI tv1 coi)
       }

passOccursCheck _is tv (TyVarTy tv') 
  | tv == tv' 
  = return Nothing 

passOccursCheck is tv (TyVarTy fsk) 
  | FlatSkol ty <- tcTyVarDetails fsk 
  = do { zty <- zonkFlattenedType ty -- Must zonk as it contains unif. vars
       ; occ <- passOccursCheck is tv zty 
       ; case occ of 
           Nothing         -> go_down_eq_class $ getFskEqClass is fsk
           Just (zty',ico) -> return $ Just (zty',ico) 
       }
  where go_down_eq_class [] = return Nothing 
        go_down_eq_class ((fsk1,co1):rest) 
          = do { occ1 <- passOccursCheck is tv (TyVarTy fsk1)
               ; case occ1 of 
                   Nothing -> go_down_eq_class rest 
                   Just (ty1,co1i') 
                     -> return $ Just (ty1, mkTransCoI co1i' (ACo co1)) }  
passOccursCheck _is _tv ty 
  = return (Just (ty,IdCo ty))  

{-- 
Problematic situation: 
~~~~~~~~~~~~~~~~~~~~~~
 Suppose we have a flatten skolem f1 := F f6
 Suppose we are chasing for 'alpha', and: 
       f6 := G alpha with eq.class f7,f8 

 Then we will return F f7 potentially. 
--} 



\end{code}


*********************************************************************************
*                                                                               * 
                       The interact-with-inert Stage
*                                                                               *
*********************************************************************************

\begin{code}
-- Interaction result of  WorkItem <~> AtomicInert
data InteractResult
   = IR { ir_stop         :: StopOrContinue
            -- Stop
            --   => Reagent (work item) consumed.
            -- ContinueWith new_reagent
            --   => Reagent transformed but keep gathering interactions. 
            --      The transformed item remains inert with respect 
            --      to any previously encountered inerts.

        , ir_inert_action :: InertAction
            -- Whether the inert item should remain in the InertSet.

        , ir_new_work     :: WorkList
            -- new work items to add to the WorkList
        }

-- What to do with the inert reactant.
data InertAction = KeepInert | DropInert
  deriving Eq

mkIRContinue :: Monad m => WorkItem -> InertAction -> WorkList -> m InteractResult
mkIRContinue wi keep newWork = return $ IR (ContinueWith wi) keep newWork

mkIRStop :: Monad m => InertAction -> WorkList -> m InteractResult
mkIRStop keep newWork = return $ IR Stop keep newWork

dischargeWorkItem :: Monad m => m InteractResult
dischargeWorkItem = mkIRStop KeepInert emptyCCan

noInteraction :: Monad m => WorkItem -> m InteractResult
noInteraction workItem = mkIRContinue workItem KeepInert emptyCCan

data WhichComesFromInert = LeftComesFromInert | RightComesFromInert 

---------------------------------------------------
-- Interact a single WorkItem with an InertSet as far as possible, i.e. until we get a Stop 
-- result from an individual interaction (i.e. when the WorkItem is consumed), or until we've 
-- interacted the WorkItem with the entire InertSet.
--
-- Postcondition: the new InertSet in the resulting StageResult is subset 
-- of the input InertSet.

interactWithInertsStage :: SimplifierStage
interactWithInertsStage workItem inert
  = foldlInertSetM interactNext initITR inert
  where 
    initITR = SR { sr_inerts   = emptyInert
                 , sr_new_work = emptyCCan
                 , sr_stop     = ContinueWith workItem }


    interactNext :: StageResult -> AtomicInert -> TcS StageResult 
    interactNext it inert  
      | ContinueWith workItem <- sr_stop it
        = do { ir <- interactWithInert inert workItem 
             ; let inerts = sr_inerts it 
             ; return $ SR { sr_inerts   = if ir_inert_action ir == KeepInert
                                           then inerts `updInertSet` inert
                                           else inerts
                           , sr_new_work = sr_new_work it `unionWorkLists` ir_new_work ir
                           , sr_stop     = ir_stop ir } }
      | otherwise = return $ itrAddInert inert it
    
                             
    itrAddInert :: AtomicInert -> StageResult -> StageResult
    itrAddInert inert itr = itr { sr_inerts = (sr_inerts itr) `updInertSet` inert }

-- Do a single interaction of two constraints.
interactWithInert :: AtomicInert -> WorkItem -> TcS InteractResult
interactWithInert inert workitem 
  =  do { ctxt <- getTcSContext
        ; let is_allowed  = allowedInteraction (simplEqsOnly ctxt) inert workitem 
              inert_ev    = cc_id inert 
              work_ev     = cc_id workitem 

        -- Never interact a wanted and a derived where the derived's evidence 
        -- mentions the wanted evidence in an unguarded way. 
        -- See Note [Superclasses and recursive dictionaries] 
        -- and Note [New Wanted Superclass Work] 
        -- We don't have to do this for givens, as we fully know the evidence for them. 
        ; rec_ev_ok <- 
            case (cc_flavor inert, cc_flavor workitem) of 
              (Wanted loc, Derived _) -> isGoodRecEv work_ev  (WantedEvVar inert_ev loc)
              (Derived _, Wanted loc) -> isGoodRecEv inert_ev (WantedEvVar work_ev loc)
              _                       -> return True 

        ; if is_allowed && rec_ev_ok then 
              doInteractWithInert inert workitem 
          else 
              noInteraction workitem 
        }

allowedInteraction :: Bool -> AtomicInert -> WorkItem -> Bool 
-- Allowed interactions 
allowedInteraction eqs_only (CDictCan {}) (CDictCan {}) = not eqs_only
allowedInteraction eqs_only (CIPCan {})   (CIPCan {})   = not eqs_only
allowedInteraction _ _ _ = True 

--------------------------------------------
doInteractWithInert :: CanonicalCt -> CanonicalCt -> TcS InteractResult
-- Identical class constraints.

doInteractWithInert 
           (CDictCan { cc_id = d1, cc_flavor = fl1, cc_class = cls1, cc_tyargs = tys1 }) 
  workItem@(CDictCan { cc_id = d2, cc_flavor = fl2, cc_class = cls2, cc_tyargs = tys2 })
  | cls1 == cls2 && (and $ zipWith tcEqType tys1 tys2)
  = solveOneFromTheOther (d1,fl1) workItem 

  | cls1 == cls2 && (not (isGiven fl1 && isGiven fl2))
  = 	 -- See Note [When improvement happens]
    do { let work_item_pred_loc = (ClassP cls2 tys2, ppr d2)
             inert_pred_loc     = (ClassP cls1 tys1, ppr d1)
	     loc                = combineCtLoc fl1 fl2
             eqn_pred_locs = improveFromAnother work_item_pred_loc inert_pred_loc         
       ; wevvars <- mkWantedFunDepEqns loc eqn_pred_locs 
              	 -- See Note [Generating extra equalities]
       ; workList <- canWanteds wevvars 
       ; mkIRContinue workItem KeepInert workList -- Keep the inert there so we avoid 
                                                  -- re-introducing the fundep equalities
         -- See Note [FunDep Reactions] 
       }

-- Class constraint and given equality: use the equality to rewrite
-- the class constraint. 
doInteractWithInert (CTyEqCan { cc_id = cv, cc_flavor = ifl, cc_tyvar = tv, cc_rhs = xi }) 
                    (CDictCan { cc_id = dv, cc_flavor = wfl, cc_class = cl, cc_tyargs = xis }) 
  | ifl `canRewrite` wfl 
  , tv `elemVarSet` tyVarsOfTypes xis
    -- substitute for tv in xis.  Note that the resulting class
    -- constraint is still canonical, since substituting xi-types in
    -- xi-types generates xi-types.  However, it may no longer be
    -- inert with respect to the inert set items we've already seen.
    -- For example, consider the inert set
    --
    --   D Int (g)
    --   a ~g Int
    --
    -- and the work item D a (w). D a does not interact with D Int.
    -- Next, it does interact with a ~g Int, getting rewritten to D
    -- Int (w).  But now we must go back through the rest of the inert
    -- set again, to find that it can now be discharged by the given D
    -- Int instance.
  = do { rewritten_dict <- rewriteDict (cv,tv,xi) (dv,wfl,cl,xis)
       ; mkIRStop KeepInert (singleCCan rewritten_dict) }
    
doInteractWithInert (CDictCan { cc_id = dv, cc_flavor = ifl, cc_class = cl, cc_tyargs = xis }) 
           workItem@(CTyEqCan { cc_id = cv, cc_flavor = wfl, cc_tyvar = tv, cc_rhs = xi })
  | wfl `canRewrite` ifl
  , tv `elemVarSet` tyVarsOfTypes xis
  = do { rewritten_dict <- rewriteDict (cv,tv,xi) (dv,ifl,cl,xis) 
       ; mkIRContinue workItem DropInert (singleCCan rewritten_dict) }

-- Class constraint and given equality: use the equality to rewrite
-- the class constraint.
doInteractWithInert (CTyEqCan { cc_id = cv, cc_flavor = ifl, cc_tyvar = tv, cc_rhs = xi }) 
                    (CIPCan { cc_id = ipid, cc_flavor = wfl, cc_ip_nm = nm, cc_ip_ty = ty }) 
  | ifl `canRewrite` wfl
  , tv `elemVarSet` tyVarsOfType ty 
  = do { rewritten_ip <- rewriteIP (cv,tv,xi) (ipid,wfl,nm,ty) 
       ; mkIRStop KeepInert (singleCCan rewritten_ip) }

doInteractWithInert (CIPCan { cc_id = ipid, cc_flavor = ifl, cc_ip_nm = nm, cc_ip_ty = ty }) 
           workItem@(CTyEqCan { cc_id = cv, cc_flavor = wfl, cc_tyvar = tv, cc_rhs = xi })
  | wfl `canRewrite` ifl
  , tv `elemVarSet` tyVarsOfType ty
  = do { rewritten_ip <- rewriteIP (cv,tv,xi) (ipid,ifl,nm,ty) 
       ; mkIRContinue workItem DropInert (singleCCan rewritten_ip) } 

-- Two implicit parameter constraints.  If the names are the same,
-- but their types are not, we generate a wanted type equality 
-- that equates the type (this is "improvement").  
-- However, we don't actually need the coercion evidence,
-- so we just generate a fresh coercion variable that isn't used anywhere.
doInteractWithInert (CIPCan { cc_id = id1, cc_flavor = ifl, cc_ip_nm = nm1, cc_ip_ty = ty1 }) 
           workItem@(CIPCan { cc_flavor = wfl, cc_ip_nm = nm2, cc_ip_ty = ty2 })
  | nm1 == nm2 && isGiven wfl && isGiven ifl
  = 	-- See Note [Overriding implicit parameters]
        -- Dump the inert item, override totally with the new one
	-- Do not require type equality
    mkIRContinue workItem DropInert emptyCCan

  | nm1 == nm2 && ty1 `tcEqType` ty2 
  = solveOneFromTheOther (id1,ifl) workItem 

  | nm1 == nm2
  =  	-- See Note [When improvement happens]
    do { co_var <- newWantedCoVar ty1 ty2 
       ; let flav = Wanted (combineCtLoc ifl wfl) 
       ; mkCanonical flav co_var >>= mkIRContinue workItem KeepInert } 


-- Inert: equality, work item: function equality

-- Never rewrite a given with a wanted equality, and a type function
-- equality can never rewrite an equality.  Note also that if we have
-- F x1 ~ x2 and a ~ x3, and a occurs in x2, we don't rewrite it.  We
-- can wait until F x1 ~ x2 matches another F x1 ~ x4, and only then
-- we will ``expose'' x2 and x4 to rewriting.

-- Otherwise, we can try rewriting the type function equality with the equality.
doInteractWithInert (CTyEqCan { cc_id = cv1, cc_flavor = ifl, cc_tyvar = tv, cc_rhs = xi1 }) 
                    (CFunEqCan { cc_id = cv2, cc_flavor = wfl, cc_fun = tc
                               , cc_tyargs = args, cc_rhs = xi2 })
  | ifl `canRewrite` wfl 
  , tv `elemVarSet` tyVarsOfTypes args
  = do { rewritten_funeq <- rewriteFunEq (cv1,tv,xi1) (cv2,wfl,tc,args,xi2) 
       ; mkIRStop KeepInert (singleCCan rewritten_funeq) }

-- Inert: function equality, work item: equality

doInteractWithInert (CFunEqCan {cc_id = cv1, cc_flavor = ifl, cc_fun = tc
                              , cc_tyargs = args, cc_rhs = xi1 }) 
           workItem@(CTyEqCan { cc_id = cv2, cc_flavor = wfl, cc_tyvar = tv, cc_rhs = xi2 })
  | wfl `canRewrite` ifl
  , tv `elemVarSet` tyVarsOfTypes args
  = do { rewritten_funeq <- rewriteFunEq (cv2,tv,xi2) (cv1,ifl,tc,args,xi1) 
       ; mkIRContinue workItem DropInert (singleCCan rewritten_funeq) } 

doInteractWithInert (CFunEqCan { cc_id = cv1, cc_flavor = fl1, cc_fun = tc1
                               , cc_tyargs = args1, cc_rhs = xi1 }) 
           workItem@(CFunEqCan { cc_id = cv2, cc_flavor = fl2, cc_fun = tc2
                               , cc_tyargs = args2, cc_rhs = xi2 })
  | fl1 `canRewrite` fl2 && lhss_match
  = do { cans <- rewriteEqLHS LeftComesFromInert  (mkCoVarCoercion cv1,xi1) (cv2,fl2,xi2) 
       ; mkIRStop KeepInert cans } 
  | fl2 `canRewrite` fl1 && lhss_match
  = do { cans <- rewriteEqLHS RightComesFromInert (mkCoVarCoercion cv2,xi2) (cv1,fl1,xi1) 
       ; mkIRContinue workItem DropInert cans }
  where
    lhss_match = tc1 == tc2 && and (zipWith tcEqType args1 args2) 

doInteractWithInert 
           inert@(CTyEqCan { cc_id = cv1, cc_flavor = fl1, cc_tyvar = tv1, cc_rhs = xi1 }) 
           workItem@(CTyEqCan { cc_id = cv2, cc_flavor = fl2, cc_tyvar = tv2, cc_rhs = xi2 })
-- Check for matching LHS 
  | fl1 `canRewrite` fl2 && tv1 == tv2 
  = do { cans <- rewriteEqLHS LeftComesFromInert (mkCoVarCoercion cv1,xi1) (cv2,fl2,xi2) 
       ; mkIRStop KeepInert cans } 

  | fl2 `canRewrite` fl1 && tv1 == tv2 
  = do { cans <- rewriteEqLHS RightComesFromInert (mkCoVarCoercion cv2,xi2) (cv1,fl1,xi1) 
       ; mkIRContinue workItem DropInert cans } 

-- Check for rewriting RHS 
  | fl1 `canRewrite` fl2 && tv1 `elemVarSet` tyVarsOfType xi2 
  = do { rewritten_eq <- rewriteEqRHS (cv1,tv1,xi1) (cv2,fl2,tv2,xi2) 
       ; mkIRStop KeepInert rewritten_eq }
  | fl2 `canRewrite` fl1 && tv2 `elemVarSet` tyVarsOfType xi1
  = do { rewritten_eq <- rewriteEqRHS (cv2,tv2,xi2) (cv1,fl1,tv1,xi1) 
       ; mkIRContinue workItem DropInert rewritten_eq } 
-- Finally, if workitem is a flatten equivalence class constraint and the 
-- inert is a wanted constraints, even when the workitem cannot rewrite the 
-- inert, drop the inert out because you may have to reconsider solving him 
-- using the equivalence class you created. 

  | not $ isGiven fl1,                  -- The inert is wanted or derived
    isMetaTyVar tv1,                    -- and has a unification variable lhs
    FlatSkol {} <- tcTyVarDetails tv2,  -- And workitem is a flatten skolem equality
    Just tv2'   <- tcGetTyVar_maybe xi2, FlatSkol {} <- tcTyVarDetails tv2' 
  = mkIRContinue workItem DropInert (singletonWorkList inert)


-- Fall-through case for all other cases
doInteractWithInert _ workItem = noInteraction workItem

--------------------------------------------
combineCtLoc :: CtFlavor -> CtFlavor -> WantedLoc
-- Precondition: At least one of them should be wanted 
combineCtLoc (Wanted loc) _ = loc 
combineCtLoc _ (Wanted loc) = loc 
combineCtLoc _ _ = panic "Expected one of wanted constraints (BUG)" 


-- Equational Rewriting 
rewriteDict  :: (CoVar, TcTyVar, Xi) -> (DictId, CtFlavor, Class, [Xi]) -> TcS CanonicalCt
rewriteDict (cv,tv,xi) (dv,gw,cl,xis) 
  = do { let cos  = substTysWith [tv] [mkCoVarCoercion cv] xis -- xis[tv] ~ xis[xi]
             args = substTysWith [tv] [xi] xis
             con  = classTyCon cl 
             dict_co = mkTyConCoercion con cos 
       ; dv' <- newDictVar cl args 
       ; case gw of 
           Wanted {}         -> setDictBind dv (EvCast dv' (mkSymCoercion dict_co))
           _given_or_derived -> setDictBind dv' (EvCast dv dict_co) 
       ; return (CDictCan { cc_id = dv'
                          , cc_flavor = gw 
                          , cc_class = cl 
                          , cc_tyargs = args }) } 

rewriteIP :: (CoVar,TcTyVar,Xi) -> (EvVar,CtFlavor, IPName Name, TcType) -> TcS CanonicalCt 
rewriteIP (cv,tv,xi) (ipid,gw,nm,ty) 
  = do { let ip_co = substTyWith [tv] [mkCoVarCoercion cv] ty     -- ty[tv] ~ t[xi] 
             ty'   = substTyWith [tv] [xi] ty
       ; ipid' <- newIPVar nm ty' 
       ; case gw of 
           Wanted {}         -> setIPBind ipid  (EvCast ipid' (mkSymCoercion ip_co))
           _given_or_derived -> setIPBind ipid' (EvCast ipid ip_co) 
       ; return (CIPCan { cc_id = ipid'
                        , cc_flavor = gw
                        , cc_ip_nm = nm
                        , cc_ip_ty = ty' }) }
   
rewriteFunEq :: (CoVar,TcTyVar,Xi) -> (CoVar,CtFlavor,TyCon, [Xi], Xi) -> TcS CanonicalCt
rewriteFunEq (cv1,tv,xi1) (cv2,gw, tc,args,xi2) 
  = do { let arg_cos = substTysWith [tv] [mkCoVarCoercion cv1] args 
             args'   = substTysWith [tv] [xi1] args 
             fun_co  = mkTyConCoercion tc arg_cos 
       ; cv2' <- case gw of 
                   Wanted {} -> do { cv2' <- newWantedCoVar (mkTyConApp tc args') xi2 
                                   ; setWantedCoBind cv2 $ 
                                     mkTransCoercion fun_co (mkCoVarCoercion cv2') 
                                   ; return cv2' } 
                   _giv_or_der -> newGivOrDerCoVar (mkTyConApp tc args') xi2 $
                                  mkTransCoercion (mkSymCoercion fun_co) (mkCoVarCoercion cv2) 
       ; return (CFunEqCan { cc_id = cv2'
                           , cc_flavor = gw
                           , cc_tyargs = args'
                           , cc_fun = tc 
                           , cc_rhs = xi2 }) }


rewriteEqRHS :: (CoVar,TcTyVar,Xi) -> (CoVar,CtFlavor,TcTyVar,Xi) -> TcS CanonicalCts
-- Use the first equality to rewrite the second, flavors already checked. 
-- E.g.          c1 : tv1 ~ xi1   c2 : tv2 ~ xi2
-- rewrites c2 to give
--               c2' : tv2 ~ xi2[xi1/tv1]
-- We must do an occurs check to sure the new constraint is canonical
-- So we might return an empty bag
rewriteEqRHS (cv1,tv1,xi1) (cv2,gw,tv2,xi2) 
  | Just tv2' <- tcGetTyVar_maybe xi2'
  , tv2 == tv2'	 -- In this case xi2[xi1/tv1] = tv2, so we have tv2~tv2
  = do { when (isWanted gw) (setWantedCoBind cv2 (mkSymCoercion co2')) 
       ; return emptyCCan } 
  | otherwise 
  = do { cv2' <- 
           case gw of 
             Wanted {} 
                 -> do { cv2' <- newWantedCoVar (mkTyVarTy tv2) xi2' 
                       ; setWantedCoBind cv2 $ 
                         mkCoVarCoercion cv2' `mkTransCoercion` mkSymCoercion co2'
                       ; return cv2' } 
             _giv_or_der 
                 -> newGivOrDerCoVar (mkTyVarTy tv2) xi2' $ 
                    mkCoVarCoercion cv2 `mkTransCoercion` co2'

       ; xi2'' <- canOccursCheck gw tv2 xi2' -- we know xi2' is *not* tv2 
       ; return (singleCCan $ CTyEqCan { cc_id = cv2' 
                                       , cc_flavor = gw 
                                       , cc_tyvar = tv2 
                                       , cc_rhs   = xi2'' }) 
       }
  where 
    xi2' = substTyWith [tv1] [xi1] xi2 
    co2' = substTyWith [tv1] [mkCoVarCoercion cv1] xi2  -- xi2 ~ xi2[xi1/tv1]


rewriteEqLHS :: WhichComesFromInert -> (Coercion,Xi) -> (CoVar,CtFlavor,Xi) -> TcS CanonicalCts
-- Used to ineratct two equalities of the following form: 
-- First Equality:   co1: (XXX ~ xi1)  
-- Second Equality:  cv2: (XXX ~ xi2) 
-- Where the cv1 `canRewrite` cv2 equality 
-- We have an option of creating new work (xi1 ~ xi2) OR (xi2 ~ xi1). This 
-- depends on whether the left or the right equality comes from the inert set. 
-- We must:  
--     prefer to create (xi2 ~ xi1) if the first comes from the inert 
--     prefer to create (xi1 ~ xi2) if the second comes from the inert 
rewriteEqLHS which (co1,xi1) (cv2,gw,xi2) 
  = do { cv2' <- case (isWanted gw, which) of 
                   (True,LeftComesFromInert) ->
                       do { cv2' <- newWantedCoVar xi2 xi1 
                          ; setWantedCoBind cv2 $ 
                            co1 `mkTransCoercion` mkSymCoercion (mkCoVarCoercion cv2')
                          ; return cv2' } 
                   (True,RightComesFromInert) -> 
                       do { cv2' <- newWantedCoVar xi1 xi2 
                          ; setWantedCoBind cv2 $ 
                            co1 `mkTransCoercion` mkCoVarCoercion cv2'
                          ; return cv2' } 
                   (False,LeftComesFromInert) ->
                       newGivOrDerCoVar xi2 xi1 $ 
                       mkSymCoercion (mkCoVarCoercion cv2) `mkTransCoercion` co1 
                   (False,RightComesFromInert) -> 
                        newGivOrDerCoVar xi1 xi2 $ 
                        mkSymCoercion co1 `mkTransCoercion` mkCoVarCoercion cv2
       ; mkCanonical gw cv2' }

--                                              ->
-- if isWanted gw then 
--                      do { cv2' <- newWantedCoVar xi1 xi2 
--                         ; setWantedCoBind cv2 $ 
--                           co1 `mkTransCoercion` mkCoVarCoercion cv2'
--                         ; return cv2' } 
--                  else newGivOrDerCoVar xi1 xi2 $ 
--                       mkSymCoercion co1 `mkTransCoercion` mkCoVarCoercion cv2 
--        ; mkCanonical gw cv2' }


solveOneFromTheOther :: (EvVar, CtFlavor) -> CanonicalCt -> TcS InteractResult 
-- First argument inert, second argument workitem. They both represent 
-- wanted/given/derived evidence for the *same* predicate so we try here to 
-- discharge one directly from the other. 
--
-- Precondition: value evidence only (implicit parameters, classes) 
--               not coercion
solveOneFromTheOther (iid,ifl) workItem 
      -- Both derived needs a special case. You might think that we do not need
      -- two evidence terms for the same claim. But, since the evidence is partial, 
      -- either evidence may do in some cases; see TcSMonad.isGoodRecEv.
      -- See also Example 3 in Note [Superclasses and recursive dictionaries] 
  | isDerived ifl && isDerived wfl 
  = noInteraction workItem 

  | ifl `canRewrite` wfl
  = do { unless (isGiven wfl) $ setEvBind wid (EvId iid) 
           -- Overwrite the binding, if one exists
	   -- For Givens, which are lambda-bound, nothing to overwrite,
       ; dischargeWorkItem }

  | otherwise  -- wfl `canRewrite` ifl 
  = do { unless (isGiven ifl) $ setEvBind iid (EvId wid)
       ; mkIRContinue workItem DropInert emptyCCan }

  where 
     wfl = cc_flavor workItem
     wid = cc_id workItem
\end{code}

Note [Superclasses and recursive dictionaries]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    Overlaps with Note [SUPERCLASS-LOOP 1]
                  Note [SUPERCLASS-LOOP 2]
                  Note [Recursive instances and superclases]
    ToDo: check overlap and delete redundant stuff

Right before adding a given into the inert set, we must
produce some more work, that will bring the superclasses 
of the given into scope. The superclass constraints go into 
our worklist. 

When we simplify a wanted constraint, if we first see a matching
instance, we may produce new wanted work. To (1) avoid doing this work 
twice in the future and (2) to handle recursive dictionaries we may ``cache'' 
this item as solved (in effect, given) into our inert set and with that add 
its superclass constraints (as given) in our worklist. 

But now we have added partially solved constraints to the worklist which may 
interact with other wanteds. Consider the example: 

Example 1: 

    class Eq b => Foo a b        --- 0-th selector
    instance Eq a => Foo [a] a   --- fooDFun

and wanted (Foo [t] t). We are first going to see that the instance matches 
and create an inert set that includes the solved (Foo [t] t) and its 
superclasses. 
       d1 :_g Foo [t] t                 d1 := EvDFunApp fooDFun d3 
       d2 :_g Eq t                      d2 := EvSuperClass d1 0 
Our work list is going to contain a new *wanted* goal
       d3 :_w Eq t 
It is wrong to react the wanted (Eq t) with the given (Eq t) because that would 
construct loopy evidence. Hence the check isGoodRecEv in doInteractWithInert. 

OK, so we have ruled out bad behaviour, but how do we ge recursive dictionaries, 
at all? Consider

Example 2:

    data D r = ZeroD | SuccD (r (D r));
    
    instance (Eq (r (D r))) => Eq (D r) where
        ZeroD     == ZeroD     = True
        (SuccD a) == (SuccD b) = a == b
        _         == _         = False;
    
    equalDC :: D [] -> D [] -> Bool;
    equalDC = (==);

We need to prove (Eq (D [])). Here's how we go:

	d1 :_w Eq (D [])

by instance decl, holds if
	d2 :_w Eq [D []]
	where 	d1 = dfEqD d2

*BUT* we have an inert set which gives us (no superclasses): 
        d1 :_g Eq (D []) 
By the instance declaration of Eq we can show the 'd2' goal if 
	d3 :_w Eq (D [])
	where	d2 = dfEqList d3
		d1 = dfEqD d2
Now, however this wanted can interact with our inert d1 to set: 
        d3 := d1 
and solve the goal. Why was this interaction OK? Because, if we chase the 
evidence of d1 ~~> dfEqD d2 ~~-> dfEqList d3, so by setting d3 := d1 we 
are really setting
        d3 := dfEqD2 (dfEqList d3) 
which is FINE because the use of d3 is protected by the instance function 
applications. 

So, our strategy is to try to put solved wanted dictionaries into the
inert set along with their superclasses (when this is meaningful,
i.e. when new wanted goals are generated) but solve a wanted dictionary
from a given only in the case where the evidence variable of the
wanted is mentioned in the evidence of the given (recursively through
the evidence binds) in a protected way: more instance function applications 
than superclass selectors.

Here are some more examples from GHC's previous type checker


Example 3: 
This code arises in the context of "Scrap Your Boilerplate with Class"

    class Sat a
    class Data ctx a
    instance  Sat (ctx Char)             => Data ctx Char       -- dfunData1
    instance (Sat (ctx [a]), Data ctx a) => Data ctx [a]        -- dfunData2

    class Data Maybe a => Foo a    

    instance Foo t => Sat (Maybe t)                             -- dfunSat

    instance Data Maybe a => Foo a                              -- dfunFoo1
    instance Foo a        => Foo [a]                            -- dfunFoo2
    instance                 Foo [Char]                         -- dfunFoo3

Consider generating the superclasses of the instance declaration
	 instance Foo a => Foo [a]

So our problem is this
    d0 :_g Foo t
    d1 :_w Data Maybe [t] 

We may add the given in the inert set, along with its superclasses
[assuming we don't fail because there is a matching instance, see 
 tryTopReact, given case ]
  Inert:
    d0 :_g Foo t 
  WorkList 
    d01 :_g Data Maybe t  -- d2 := EvDictSuperClass d0 0 
    d1 :_w Data Maybe [t] 
Then d2 can readily enter the inert, and we also do solving of the wanted
  Inert: 
    d0 :_g Foo t 
    d1 :_s Data Maybe [t]           d1 := dfunData2 d2 d3 
  WorkList
    d2 :_w Sat (Maybe [t])          
    d3 :_w Data Maybe t
    d01 :_g Data Maybe t 
Now, we may simplify d2 more: 
  Inert:
      d0 :_g Foo t 
      d1 :_s Data Maybe [t]           d1 := dfunData2 d2 d3 
      d1 :_g Data Maybe [t] 
      d2 :_g Sat (Maybe [t])          d2 := dfunSat d4 
  WorkList: 
      d3 :_w Data Maybe t 
      d4 :_w Foo [t] 
      d01 :_g Data Maybe t 

Now, we can just solve d3.
  Inert
      d0 :_g Foo t 
      d1 :_s Data Maybe [t]           d1 := dfunData2 d2 d3 
      d2 :_g Sat (Maybe [t])          d2 := dfunSat d4 
  WorkList
      d4 :_w Foo [t] 
      d01 :_g Data Maybe t 
And now we can simplify d4 again, but since it has superclasses we *add* them to the worklist:
  Inert
      d0 :_g Foo t 
      d1 :_s Data Maybe [t]           d1 := dfunData2 d2 d3 
      d2 :_g Sat (Maybe [t])          d2 := dfunSat d4 
      d4 :_g Foo [t]                  d4 := dfunFoo2 d5 
  WorkList:
      d5 :_w Foo t 
      d6 :_g Data Maybe [t]           d6 := EvDictSuperClass d4 0
      d01 :_g Data Maybe t 
Now, d5 can be solved! (and its superclass enter scope) 
  Inert
      d0 :_g Foo t 
      d1 :_s Data Maybe [t]           d1 := dfunData2 d2 d3 
      d2 :_g Sat (Maybe [t])          d2 := dfunSat d4 
      d4 :_g Foo [t]                  d4 := dfunFoo2 d5 
      d5 :_g Foo t                    d5 := dfunFoo1 d7
  WorkList:
      d7 :_w Data Maybe t
      d6 :_g Data Maybe [t]
      d8 :_g Data Maybe t            d8 := EvDictSuperClass d5 0
      d01 :_g Data Maybe t 

Now, two problems: 
   [1] Suppose we pick d8 and we react him with d01. Which of the two givens should 
       we keep? Well, we *MUST NOT* drop d01 because d8 contains recursive evidence 
       that must not be used (look at case interactInert where both inert and workitem
       are givens). So we have several options: 
       - Drop the workitem always (this will drop d8)
              This feels very unsafe -- what if the work item was the "good" one
              that should be used later to solve another wanted?
       - Don't drop anyone: the inert set may contain multiple givens! 
              [This is currently implemented] 

The "don't drop anyone" seems the most safe thing to do, so now we come to problem 2: 
  [2] We have added both d6 and d01 in the inert set, and we are interacting our wanted
      d7. Now the [isRecDictEv] function in the ineration solver 
      [case inert-given workitem-wanted] will prevent us from interacting d7 := d8 
      precisely because chasing the evidence of d8 leads us to an unguarded use of d7. 

      So, no interaction happens there. Then we meet d01 and there is no recursion 
      problem there [isRectDictEv] gives us the OK to interact and we do solve d7 := d01! 
             
Note [SUPERCLASS-LOOP 1]
~~~~~~~~~~~~~~~~~~~~~~~~
We have to be very, very careful when generating superclasses, lest we
accidentally build a loop. Here's an example:

  class S a

  class S a => C a where { opc :: a -> a }
  class S b => D b where { opd :: b -> b }
  
  instance C Int where
     opc = opd
  
  instance D Int where
     opd = opc

From (instance C Int) we get the constraint set {ds1:S Int, dd:D Int}
Simplifying, we may well get:
	$dfCInt = :C ds1 (opd dd)
	dd  = $dfDInt
	ds1 = $p1 dd
Notice that we spot that we can extract ds1 from dd.  

Alas!  Alack! We can do the same for (instance D Int):

	$dfDInt = :D ds2 (opc dc)
	dc  = $dfCInt
	ds2 = $p1 dc

And now we've defined the superclass in terms of itself.
Two more nasty cases are in
	tcrun021
	tcrun033

Solution: 
  - Satisfy the superclass context *all by itself* 
    (tcSimplifySuperClasses)
  - And do so completely; i.e. no left-over constraints
    to mix with the constraints arising from method declarations


Note [SUPERCLASS-LOOP 2]
~~~~~~~~~~~~~~~~~~~~~~~~
We need to be careful when adding "the constaint we are trying to prove".
Suppose we are *given* d1:Ord a, and want to deduce (d2:C [a]) where

	class Ord a => C a where
	instance Ord [a] => C [a] where ...

Then we'll use the instance decl to deduce C [a] from Ord [a], and then add the
superclasses of C [a] to avails.  But we must not overwrite the binding
for Ord [a] (which is obtained from Ord a) with a superclass selection or we'll just
build a loop! 

Here's another variant, immortalised in tcrun020
	class Monad m => C1 m
	class C1 m => C2 m x
	instance C2 Maybe Bool
For the instance decl we need to build (C1 Maybe), and it's no good if
we run around and add (C2 Maybe Bool) and its superclasses to the avails 
before we search for C1 Maybe.

Here's another example 
 	class Eq b => Foo a b
	instance Eq a => Foo [a] a
If we are reducing
	(Foo [t] t)

we'll first deduce that it holds (via the instance decl).  We must not
then overwrite the Eq t constraint with a superclass selection!

At first I had a gross hack, whereby I simply did not add superclass constraints
in addWanted, though I did for addGiven and addIrred.  This was sub-optimal,
becuase it lost legitimate superclass sharing, and it still didn't do the job:
I found a very obscure program (now tcrun021) in which improvement meant the
simplifier got two bites a the cherry... so something seemed to be an Stop
first time, but reducible next time.

Now we implement the Right Solution, which is to check for loops directly 
when adding superclasses.  It's a bit like the occurs check in unification.

Note [Recursive instances and superclases]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider this code, which arises in the context of "Scrap Your 
Boilerplate with Class".  

    class Sat a
    class Data ctx a
    instance  Sat (ctx Char)             => Data ctx Char
    instance (Sat (ctx [a]), Data ctx a) => Data ctx [a]

    class Data Maybe a => Foo a

    instance Foo t => Sat (Maybe t)

    instance Data Maybe a => Foo a
    instance Foo a        => Foo [a]
    instance                 Foo [Char]

In the instance for Foo [a], when generating evidence for the superclasses
(ie in tcSimplifySuperClasses) we need a superclass (Data Maybe [a]).
Using the instance for Data, we therefore need
        (Sat (Maybe [a], Data Maybe a)
But we are given (Foo a), and hence its superclass (Data Maybe a).
So that leaves (Sat (Maybe [a])).  Using the instance for Sat means
we need (Foo [a]).  And that is the very dictionary we are bulding
an instance for!  So we must put that in the "givens".  So in this
case we have
	Given:  Foo a, Foo [a]
	Wanted: Data Maybe [a]

BUT we must *not not not* put the *superclasses* of (Foo [a]) in
the givens, which is what 'addGiven' would normally do. Why? Because
(Data Maybe [a]) is the superclass, so we'd "satisfy" the wanted 
by selecting a superclass from Foo [a], which simply makes a loop.

On the other hand we *must* put the superclasses of (Foo a) in
the givens, as you can see from the derivation described above.

Conclusion: in the very special case of tcSimplifySuperClasses
we have one 'given' (namely the "this" dictionary) whose superclasses
must not be added to 'givens' by addGiven.  

There is a complication though.  Suppose there are equalities
      instance (Eq a, a~b) => Num (a,b)
Then we normalise the 'givens' wrt the equalities, so the original
given "this" dictionary is cast to one of a different type.  So it's a
bit trickier than before to identify the "special" dictionary whose
superclasses must not be added. See test
   indexed-types/should_run/EqInInstance

We need a persistent property of the dictionary to record this
special-ness.  Current I'm using the InstLocOrigin (a bit of a hack,
but cool), which is maintained by dictionary normalisation.
Specifically, the InstLocOrigin is
	     NoScOrigin
then the no-superclass thing kicks in.  WATCH OUT if you fiddle
with InstLocOrigin!

Note [MATCHING-SYNONYMS]
~~~~~~~~~~~~~~~~~~~~~~~~
When trying to match a dictionary (D tau) to a top-level instance, or a 
type family equation (F taus_1 ~ tau_2) to a top-level family instance, 
we do *not* need to expand type synonyms because the matcher will do that for us.


Note [RHS-FAMILY-SYNONYMS] 
~~~~~~~~~~~~~~~~~~~~~~~~~~
The RHS of a family instance is represented as yet another constructor which is 
like a type synonym for the real RHS the programmer declared. Eg: 
    type instance F (a,a) = [a] 
Becomes: 
    :R32 a = [a]      -- internal type synonym introduced
    F (a,a) ~ :R32 a  -- instance 

When we react a family instance with a type family equation in the work list 
we keep the synonym-using RHS without expansion. 


*********************************************************************************
*                                                                               * 
                       The top-reaction Stage
*                                                                               *
*********************************************************************************

\begin{code}
-- If a work item has any form of interaction with top-level we get this 
data TopInteractResult 
  = NoTopInt 	           -- No top-level interaction
  | SomeTopInt 
      { tir_new_work  :: WorkList	-- Sub-goals or new work (could be given, 
                                        --                        for superclasses)
      , tir_new_inert :: StopOrContinue -- The input work item, ready to become *inert* now: 
      }                       		-- NB: in ``given'' (solved) form if the 
                              		-- original was wanted or given and instance match
                              		-- was found, but may also be in wanted form if we 
                                        -- only reacted with functional dependencies 
					-- arising from top-level instances.

topReactionsStage :: SimplifierStage 
topReactionsStage workItem inerts 
  = do { tir <- tryTopReact workItem 
       ; case tir of 
           NoTopInt -> 
               return $ SR { sr_inerts   = inerts 
                           , sr_new_work = emptyWorkList 
                           , sr_stop     = ContinueWith workItem } 
           SomeTopInt tir_new_work tir_new_inert -> 
               return $ SR { sr_inerts   = inerts 
                           , sr_new_work = tir_new_work
                           , sr_stop     = tir_new_inert
                           }
       }

tryTopReact :: WorkItem -> TcS TopInteractResult 
tryTopReact workitem 
  = do {  -- A flag controls the amount of interaction allowed
          -- See Note [Simplifying RULE lhs constraints]
         ctxt <- getTcSContext
       ; if allowedTopReaction (simplEqsOnly ctxt) workitem 
         then do { traceTcS "tryTopReact / calling doTopReact" (ppr workitem)
                 ; doTopReact workitem }
         else return NoTopInt 
       } 

allowedTopReaction :: Bool -> WorkItem -> Bool 
allowedTopReaction eqs_only (CDictCan {}) = not eqs_only
allowedTopReaction _        _             = True 


doTopReact :: WorkItem -> TcS TopInteractResult 
-- The work item does not react with the inert set, 
-- so try interaction with top-level instances
doTopReact workItem@(CDictCan { cc_id = dv, cc_flavor = Wanted loc
                              , cc_class = cls, cc_tyargs = xis }) 
  = do { -- See Note [MATCHING-SYNONYMS]
       ; lkp_inst_res <- matchClassInst cls xis loc
       ; case lkp_inst_res of 
           NoInstance -> do { traceTcS "doTopReact/ no class instance for" (ppr dv) 
                            ; funDepReact }
           GenInst wtvs ev_term ->  -- Solved 
	   	   -- No need to do fundeps stuff here; the instance 
		   -- matches already so we won't get any more info
		   -- from functional dependencies
               do { traceTcS "doTopReact/ found class instance for" (ppr dv) 
                  ; setDictBind dv ev_term 
                  ; workList <- canWanteds wtvs
                  ; if null wtvs
                    -- Solved in one step and no new wanted work produced. 
                    -- i.e we directly matched a top-level instance
		    -- No point in caching this in 'inert', nor in adding superclasses
                    then return $ SomeTopInt { tir_new_work  = emptyCCan 
                                             , tir_new_inert = Stop }

                    -- Solved and new wanted work produced, you may cache the 
		    -- (tentatively solved) dictionary as Derived and its superclasses
                    else do { let solved = makeSolved workItem
                            ; sc_work <- newSCWorkFromFlavored dv (Derived loc) cls xis 
                            ; return $ SomeTopInt 
                                  { tir_new_work = workList `unionWorkLists` sc_work 
                                  , tir_new_inert = ContinueWith solved } }
                  }
       }
  where 
    -- Try for a fundep reaction beween the wanted item 
    -- and a top-level instance declaration
    funDepReact 
      = do { instEnvs <- getInstEnvs
           ; let eqn_pred_locs = improveFromInstEnv (classInstances instEnvs)
                                                    (ClassP cls xis, ppr dv)
           ; wevvars <- mkWantedFunDepEqns loc eqn_pred_locs 
	     	      -- NB: fundeps generate some wanted equalities, but 
	   	      --     we don't use their evidence for anything
           ; fd_work <- canWanteds wevvars 
           ; sc_work <- newSCWorkFromFlavored dv (Derived loc) cls xis
           ; return $ SomeTopInt { tir_new_work = fd_work `unionWorkLists` sc_work
                                 , tir_new_inert = ContinueWith workItem }
           -- NB: workItem is inert, but it isn't solved
	   -- keep it as inert, although it's not solved because we
           -- have now reacted all its top-level fundep-induced equalities!
                    
           -- See Note [FunDep Reactions]
           }

-- Otherwise, we have a given or derived 
doTopReact workItem@(CDictCan { cc_id = dv, cc_flavor = fl
                              , cc_class = cls, cc_tyargs = xis }) 
  = do { sc_work <- newSCWorkFromFlavored dv fl cls xis 
       ; return $ SomeTopInt sc_work (ContinueWith workItem) }
    -- See Note [Given constraint that matches an instance declaration]

-- Type functions
doTopReact (CFunEqCan { cc_id = cv, cc_flavor = fl
                      , cc_fun = tc, cc_tyargs = args, cc_rhs = xi })
  = ASSERT (isSynFamilyTyCon tc)   -- No associated data families have reached that far 
    do { match_res <- matchFam tc args -- See Note [MATCHING-SYNONYMS]
       ; case match_res of 
           MatchInstNo 
             -> return NoTopInt 
           MatchInstSingle (rep_tc, rep_tys)
             -> do { let Just coe_tc = tyConFamilyCoercion_maybe rep_tc
                         Just rhs_ty = tcView (mkTyConApp rep_tc rep_tys)
			    -- Eagerly expand away the type synonym on the
			    -- RHS of a type function, so that it never
			    -- appears in an error message
                            -- See Note [Type synonym families] in TyCon
                         coe = mkTyConApp coe_tc rep_tys 
                   ; cv' <- case fl of
                              Wanted {} -> do { cv' <- newWantedCoVar rhs_ty xi
                                              ; setWantedCoBind cv $ 
                                                    coe `mkTransCoercion`
                                                      mkCoVarCoercion cv'
                                              ; return cv' }
                              _ -> newGivOrDerCoVar xi rhs_ty $ 
                                   mkSymCoercion (mkCoVarCoercion cv) `mkTransCoercion` coe 

                   ; workList <- mkCanonical fl cv'
                   ; return $ SomeTopInt workList Stop }
           _ 
             -> panicTcS $ text "TcSMonad.matchFam returned multiple instances!"
       }


-- Any other work item does not react with any top-level equations
doTopReact _workItem = return NoTopInt 
\end{code}

Note [FunDep and implicit parameter reactions] 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Currently, our story of interacting two dictionaries (or a dictionary
and top-level instances) for functional dependencies, and implicit
paramters, is that we simply produce new wanted equalities.  So for example

        class D a b | a -> b where ... 
    Inert: 
        d1 :g D Int Bool
    WorkItem: 
        d2 :w D Int alpha

    We generate the extra work item
        cv :w alpha ~ Bool
    where 'cv' is currently unused.  However, this new item reacts with d2,
    discharging it in favour of a new constraint d2' thus:
        d2' :w D Int Bool
	d2 := d2' |> D Int cv
    Now d2' can be discharged from d1

We could be more aggressive and try to *immediately* solve the dictionary 
using those extra equalities. With the same inert set and work item we
might dischard d2 directly:

        cv :w alpha ~ Bool
        d2 := d1 |> D Int cv

But in general it's a bit painful to figure out the necessary coercion,
so we just take the first approach.

It's exactly the same with implicit parameters, except that the
"aggressive" approach would be much easier to implement.

Note [When improvement happens]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We fire an improvement rule when

  * Two constraints match (modulo the fundep)
      e.g. C t1 t2, C t1 t3    where C a b | a->b
    The two match because the first arg is identical

  * At least one is not Given.  If they are both given, we don't fire
    the reaction because we have no way of constructing evidence for a
    new equality nor does it seem right to create a new wanted goal
    (because the goal will most likely contain untouchables, which
    can't be solved anyway)!
   
Note that we *do* fire the improvement if one is Given and one is Derived.
The latter can be a superclass of a wanted goal. Example (tcfail138)
    class L a b | a -> b
    class (G a, L a b) => C a b

    instance C a b' => G (Maybe a)
    instance C a b  => C (Maybe a) a
    instance L (Maybe a) a

When solving the superclasses of the (C (Maybe a) a) instance, we get
  Given:  C a b  ... and hance by superclasses, (G a, L a b)
  Wanted: G (Maybe a)
Use the instance decl to get
  Wanted: C a b'
The (C a b') is inert, so we generate its Derived superclasses (L a b'),
and now we need improvement between that derived superclass an the Given (L a b)

Note [Overriding implicit parameters]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
   f :: (?x::a) -> Bool -> a
  
   g v = let ?x::Int = 3 
         in (f v, let ?x::Bool = True in f v)

This should probably be well typed, with
   g :: Bool -> (Int, Bool)

So the inner binding for ?x::Bool *overrides* the outer one.
Hence a work-item Given overrides an inert-item Given.

Note [Given constraint that matches an instance declaration]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
What should we do when we discover that one (or more) top-level 
instances match a given (or solved) class constraint? We have 
two possibilities:

  1. Reject the program. The reason is that there may not be a unique
     best strategy for the solver. Example, from the OutsideIn(X) paper:
       instance P x => Q [x] 
       instance (x ~ y) => R [x] y 
     
       wob :: forall a b. (Q [b], R b a) => a -> Int 

       g :: forall a. Q [a] => [a] -> Int 
       g x = wob x 

       will generate the impliation constraint: 
            Q [a] => (Q [beta], R beta [a]) 
       If we react (Q [beta]) with its top-level axiom, we end up with a 
       (P beta), which we have no way of discharging. On the other hand, 
       if we react R beta [a] with the top-level we get  (beta ~ a), which 
       is solvable and can help us rewrite (Q [beta]) to (Q [a]) which is 
       now solvable by the given Q [a]. 
 
     However, this option is restrictive, for instance [Example 3] from 
     Note [Recursive dictionaries] will fail to work. 

  2. Ignore the problem, hoping that the situations where there exist indeed
     such multiple strategies are rare: Indeed the cause of the previous 
     problem is that (R [x] y) yields the new work (x ~ y) which can be 
     *spontaneously* solved, not using the givens. 

We are choosing option 2 below but we might consider having a flag as well.


Note [New Wanted Superclass Work] 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Even in the case of wanted constraints, we add all of its superclasses as 
new given work. There are several reasons for this: 
     a) to minimise error messages; 
        eg suppose we have wanted (Eq a, Ord a)
	     then we report only (Ord a) unsoluble

     b) to make the smallest number of constraints when *inferring* a type
        (same Eq/Ord example)

     c) for recursive dictionaries we *must* add the superclasses
        so that we can use them when solving a sub-problem

     d) To allow FD-like improvement for type families. Assume that 
        we have a class 
             class C a b | a -> b 
        and we have to solve the implication constraint: 
             C a b => C a beta 
        Then, FD improvement can help us to produce a new wanted (beta ~ b) 

        We want to have the same effect with the type family encoding of 
        functional dependencies. Namely, consider: 
             class (F a ~ b) => C a b 
        Now suppose that we have: 
               given: C a b 
               wanted: C a beta 
        By interacting the given we will get that (F a ~ b) which is not 
        enough by itself to make us discharge (C a beta). However, we 
        may create a new given equality from the super-class that we promise
        to solve: (F a ~ beta). Now we may interact this with the rest of 
        constraint to finally get: 
                  given :  beta ~ b 
        
        But 'beta' is a touchable unification variable, and hence OK to 
        unify it with 'b', replacing the given evidence with the identity. 

        This requires trySpontaneousSolve to solve given equalities that
        have a touchable in their RHS, *in addition* to solving wanted 
        equalities. 

Here is another example where this is useful. 

Example 1:
----------
   class (F a ~ b) => C a b 
And we are given the wanteds:
      w1 : C a b 
      w2 : C a c 
      w3 : b ~ c 
We surely do *not* want to quantify over (b ~ c), since if someone provides
dictionaries for (C a b) and (C a c), these dictionaries can provide a proof 
of (b ~ c), hence no extra evidence is necessary. Here is what will happen: 

     Step 1: We will get new *given* superclass work, 
             provisionally to our solving of w1 and w2
             
               g1: F a ~ b, g2 : F a ~ c, 
               w1 : C a b, w2 : C a c, w3 : b ~ c

             The evidence for g1 and g2 is a superclass evidence term: 

               g1 := sc w1, g2 := sc w2

     Step 2: The givens will solve the wanted w3, so that 
               w3 := sym (sc w1) ; sc w2 
                  
     Step 3: Now, one may naively assume that then w2 can be solve from w1
             after rewriting with the (now solved equality) (b ~ c). 
             
             But this rewriting is ruled out by the isGoodRectDict! 

Conclusion, we will (correctly) end up with the unsolved goals 
    (C a b, C a c)   

NB: The desugarer needs be more clever to deal with equalities 
    that participate in recursive dictionary bindings. 

\begin{code}
newSCWorkFromFlavored :: EvVar -> CtFlavor -> Class -> [Xi]
                      -> TcS WorkList
newSCWorkFromFlavored ev flavor cls xis
  | Given loc <- flavor	 	 -- The NoScSkol says "don't add superclasses"
  , NoScSkol <- ctLocOrigin loc  -- Very important!
  = return emptyWorkList
    
  | otherwise
  = do { let (tyvars, sc_theta, _, _) = classBigSig cls 
             sc_theta1 = substTheta (zipTopTvSubst tyvars xis) sc_theta
             -- Add *all* its superclasses (equalities or not) as new given work 
             -- See Note [New Wanted Superclass Work] 
       ; sc_vars <- zipWithM inst_one sc_theta1 [0..]
       ; mkCanonicals flavor sc_vars } 
  where
    inst_one pred n = newGivOrDerEvVar pred (EvSuperClass ev n)

data LookupInstResult
  = NoInstance
  | GenInst [WantedEvVar] EvTerm 

matchClassInst :: Class -> [Type] -> WantedLoc -> TcS LookupInstResult
matchClassInst clas tys loc
   = do { let pred = mkClassPred clas tys 
        ; mb_result <- matchClass clas tys
        ; case mb_result of
            MatchInstNo   -> return NoInstance
            MatchInstMany -> return NoInstance -- defer any reactions of a multitude until 
                                               -- we learn more about the reagent 
            MatchInstSingle (dfun_id, mb_inst_tys) -> 
              do { checkWellStagedDFun pred dfun_id loc

 	-- It's possible that not all the tyvars are in
	-- the substitution, tenv. For example:
	--	instance C X a => D X where ...
	-- (presumably there's a functional dependency in class C)
	-- Hence mb_inst_tys :: Either TyVar TcType 

                 ; tys <- instDFunTypes mb_inst_tys 
                 ; let (theta, _) = tcSplitPhiTy (applyTys (idType dfun_id) tys)
                 ; if null theta then
                       return (GenInst [] (EvDFunApp dfun_id tys [])) 
                   else do
                     { ev_vars <- instDFunConstraints theta
                     ; let wevs = [WantedEvVar w loc | w <- ev_vars]
                     ; return $ GenInst wevs (EvDFunApp dfun_id tys ev_vars) }
                 }
        }
\end{code}


