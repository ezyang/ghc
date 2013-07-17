%
% (c) The GRASP/AQUA Project, Glasgow University, 1993-1998
%
\section[SimplStg]{Driver for simplifying @STG@ programs}

\begin{code}
module SimplStg ( stg2stg ) where

#include "HsVersions.h"

import StgSyn

import CostCentre       ( CollectedCCs )
import SCCfinal         ( stgMassageForProfiling )
import StgLint          ( lintStgBindings )
import StgStats         ( showStgStats )
import UnariseStg       ( unarise )

import DynFlags
import Module           ( Module )
import ErrUtils
import SrcLoc
import UniqSupply       -- ( mkSplitUniqSupply, splitUniqSupply )
import Outputable
import Control.Monad

import Name
import qualified Var
import VarEnv
import UniqSet
import Id
import VarSet
\end{code}

\begin{code}
stg2stg :: DynFlags                  -- includes spec of what stg-to-stg passes to do
        -> Module                    -- module name (profiling only)
        -> [StgBinding]              -- input...
        -> IO ( [StgBinding]         -- output program...
              , CollectedCCs)        -- cost centre information (declared and used)

stg2stg dflags module_name binds
  = do  { showPass dflags "Stg2Stg"
        ; us <- mkSplitUniqSupply 'g'

        ; when (dopt Opt_D_verbose_stg2stg dflags)
               (log_action dflags dflags SevDump noSrcSpan defaultDumpStyle (text "VERBOSE STG-TO-STG:"))

        ; (binds', us', ccs) <- end_pass us "Stg2Stg" ([],[],[]) binds

                -- Do the main business!
        ; let (us0, us1) = splitUniqSupply us'
        ; (processed_binds, _, cost_centres)
                <- foldM do_stg_pass (binds', us0, ccs) (getStgToDo dflags)

        ; let un_binds = unarise us1 processed_binds

        ; dumpIfSet_dyn dflags Opt_D_dump_stg "STG syntax:"
                        (pprStgBindings un_binds)

        ; return (un_binds, cost_centres)
   }

  where
    stg_linter = if gopt Opt_DoStgLinting dflags
                 then lintStgBindings
                 else ( \ _whodunnit binds -> binds )

    -------------------------------------------
    do_stg_pass (binds, us, ccs) to_do
      = let
            (us1, us2) = splitUniqSupply us
        in
        case to_do of
          D_stg_stats ->
             trace (showStgStats binds)
             end_pass us2 "StgStats" ccs binds

          StgDoMassageForProfiling ->
             {-# SCC "ProfMassage" #-}
             let
                 (collected_CCs, binds3)
                   = stgMassageForProfiling dflags module_name us1 binds
             in
             end_pass us2 "ProfMassage" collected_CCs binds3

          StgGenerateNonUpdatableClosures ->
             let binds' = stgGenerateNonUpdatableClosures dflags module_name us1 binds
             in end_pass us2 "GenerateNonUpdatableClosures" ccs binds'

    end_pass us2 what ccs binds2
      = do -- report verbosely, if required
           dumpIfSet_dyn dflags Opt_D_verbose_stg2stg what
              (vcat (map ppr binds2))
           let linted_binds = stg_linter what binds2
           return (linted_binds, us2, ccs)
            -- return: processed binds
            --         UniqueSupply for the next guy to use
            --         cost-centres to be declared/registered (specialised)
            --         add to description of what's happened (reverse order)

-- The general strategy is to take every top-level closure which looks like
-- a CAF and duplicate it.  Because STG requires all local variables to unique,
-- we have to alpha-rename the closure definition.
--
-- Because we're duplicating only CAFs, this affords us a little flexibility.
-- In particular:
--
--      * None of the global references in a duplicated CAF have to be rewritten,
--        even if they point to another CAF which is duplicated.  This relies
--        on the fact that the x_info of a CAF will only ever be referred to
--        by the x_closure of the object; thus, we can update all references
--        by simply overwriting the closure itself.
--
-- Bugs:
--
--      * STG lint does not appear to notice when the SRT is inaccurate.  We
--        should fix this!
--
--      * After overwriting a closure, we leak the original info-tables, since
--        the SRTs are not updated.
--
--      * Sometimes, a non-top-level let-binding will get promoted into a CAF;
--        we don't catch this yet.
--
--      * While we assert that no one ever refers to the _info of a CAF, there
--        are no debug asserts checking this.

stgGenerateNonUpdatableClosures
        :: DynFlags
        -> Module                       -- module name
        -> UniqSupply                   -- unique supply
        -> [StgBinding]                 -- input
        -> [StgBinding]
stgGenerateNonUpdatableClosures _dflags _mod_name us stg_binds =
    let (r, _us) = initUs us (do_top_bindings stg_binds) in r
    where do_top_bindings [] = return []
          do_top_bindings (b : bs)
            | is_caf b = do
                (b', _) <- stgRenameBinding True emptyVarEnv b
                bs' <- do_top_bindings bs
                return (b' : annotateWith b b' : bs')
            | otherwise = do
                bs' <- do_top_bindings bs
                return (b : bs')
          annotateWith (StgNonRec n (StgRhsClosure ccs info fv u (SRTEntries ids) Nothing   [] e))
                       (StgNonRec n' _)
                      = StgNonRec n (StgRhsClosure ccs info fv u
                            (SRTEntries (ids `extendVarSet` n')) (Just n') [] e)
          annotateWith (StgRec ps) (StgRec ps') = StgRec (zipWith go ps ps')
            where go (n, StgRhsClosure ccs info fv u (SRTEntries ids) Nothing   [] e) (n', _)
                   = (n, StgRhsClosure ccs info fv u
                            (SRTEntries (ids `extendVarSet` n')) (Just n') [] e)
                  go (n, p) _ = (n, p)
          annotateWith e e' = pprPanic "noupd/annotateWith: bad annotation request" (ppr e $$ ppr e')
          -- just eyeball it
          is_caf (StgNonRec _ rhs) | is_caf_rhs rhs = True
          is_caf (StgRec pairs) | any (is_caf_rhs . snd) pairs = True
          is_caf _ = False
          is_caf_rhs (StgRhsClosure _ _ _ Updatable _ _ [] _) = True
          is_caf_rhs _ = False

stgRenameFresh :: IdEnv Id -> Id -> UniqSM (Id, IdEnv Id)
stgRenameFresh m b = do
    u <- getUniqueM
    let b' = Var.setVarName b (mkClonedInternalName u (Var.varName b))
    return (b', extendVarEnv m b b')

stgRenameSubst :: IdEnv Id -> Id -> Id
stgRenameSubst m v = lookupWithDefaultVarEnv m v v

stgRenameArg :: IdEnv Id -> StgArg -> StgArg
stgRenameArg m (StgVarArg occ) = StgVarArg (stgRenameSubst m occ)
stgRenameArg _ (StgLitArg l) = StgLitArg l

stgRenameArgs :: IdEnv Id -> [StgArg] -> [StgArg]
stgRenameArgs m args = map (stgRenameArg m) args

stgRenameBinding :: Bool -> IdEnv Id -> StgBinding -> UniqSM (StgBinding, IdEnv Id)
stgRenameBinding top m (StgNonRec b e) = do
    (b', m') <- stgRenameFresh m b
    e' <- stgRenameRhs top m e -- use OLD one
    return (StgNonRec b' e', m')
stgRenameBinding top m (StgRec pairs) = do
    m' <- foldM (\mm (b, _) -> snd `fmap` stgRenameFresh mm b) m pairs
    pairs' <- mapM (\(b, rhs) -> do
        rhs' <- stgRenameRhs top m' rhs
        return (stgRenameSubst m' b, rhs')) pairs
    return (StgRec pairs', m')

stgRenameRhs :: Bool -> IdEnv Id -> StgRhs -> UniqSM StgRhs
stgRenameRhs top m (StgRhsClosure ccs info fv u srt noupd args body) = do
    let args' = map (stgRenameSubst m) args
        fv' = map (stgRenameSubst m) fv
    body' <- stgRenameExpr m body
    -- XXX I don't think SRT need to be changed
    return (StgRhsClosure ccs info fv' (if top then ReEntrant else u) srt noupd args' body')
stgRenameRhs _ m (StgRhsCon ccs con args) = do
    let args' = map (stgRenameArg m) args
    return (StgRhsCon ccs con args')

stgRenameExpr :: IdEnv Id -> StgExpr -> UniqSM StgExpr
stgRenameExpr m (StgApp f args) = do
    return (StgApp (stgRenameSubst m f) (stgRenameArgs m args))
stgRenameExpr m (StgConApp k args) = return (StgConApp k (stgRenameArgs m args))
stgRenameExpr m (StgOpApp op args t) = return (StgOpApp op (stgRenameArgs m args) t)
stgRenameExpr m (StgCase expr fv1 fv2 bndr srt alt_type alts) = do
    expr' <- stgRenameExpr m expr
    let fv1' = mapUniqSet (stgRenameSubst m) fv1
        fv2' = mapUniqSet (stgRenameSubst m) fv2
    -- bndr?
    alts' <- mapM do_alt alts
    return (StgCase expr' fv1' fv2' bndr srt alt_type alts')
  where do_alt (id, bs, use_mask, e) = do
            e' <- stgRenameExpr m e
            -- bs?
            return (id, bs, use_mask, e')
-- the WHOLE POINT of this exercise
stgRenameExpr m (StgLet b e) = do
    (b, e) <- stgRenameLet m b e
    return (StgLet b e)
stgRenameExpr m (StgLetNoEscape fv1 fv2 b e) = do
    let fv1' = mapUniqSet (stgRenameSubst m) fv1
        fv2' = mapUniqSet (stgRenameSubst m) fv2
    (b, e) <- stgRenameLet m b e
    return (StgLetNoEscape fv1' fv2' b e)
stgRenameExpr m (StgSCC cc b p e) = do
    e <- stgRenameExpr m e
    return (StgSCC cc b p e)
stgRenameExpr m (StgTick mod i e) = do
    e <- stgRenameExpr m e
    return (StgTick mod i e)
stgRenameExpr _ body = return body -- XXX danger will robinson

stgRenameLet :: IdEnv Id -> StgBinding -> StgExpr -> UniqSM (StgBinding, StgExpr)
stgRenameLet m b e = do
    -- XXX SOMETIMES NEED TO SET THIS TO TRUE
    (b', m') <- stgRenameBinding False m b
    e' <- stgRenameExpr m' e
    return (b', e')

\end{code}
