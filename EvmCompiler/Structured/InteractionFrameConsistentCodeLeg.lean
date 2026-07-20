import EvmCompiler.Structured.InteractionFrameConsistentBranchLegs

/-!
# Strengthened (`realizedWitnessFC`) `hInv` leg — the `codeHead` disjunct (session 46)

Session 46 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-45 frontier item 1).

The `codeHead` disjunct is a straight-line `.code` block that falls through to `regular`.  Like
`ifHead`/`forCond` it runs source code that touches no return frame, so the post-run child's
ghost `returns` equal the entry source's `returns` (the `ActivationRestored` component of the
outcome relation, which the bare `jump_state_rel_of_outcome` discards).  This module banks the
returns-exposing outcome extractor and the strengthened `codeHead` leg.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionFrameConsistent

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)
open Simulation.Interaction (Executes)

/--
**Returns-exposing outcome extraction.**  The `jump_state_rel_of_outcome` sibling that ALSO
reads off `srcState.returns = returns` (the `ActivationRestored` fact) from the regular
elimination. -/
theorem jump_state_rel_returns_of_outcome
    {result : TypedCfgCompiler.Result} {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {returns : List ReturnDest}
    {tokens : List Word} {expected : TypedCfg.Shape}
    {srcRun : Simulation.Interaction EVMException Structured.Outcome}
    {targetRun : Simulation.Interaction EVMException TypedCfg.Outcome}
    {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {state' : EVMState}
    (hRequire : result.requireFallthrough? expected = some ())
    (hRel :
      Simulation.Interaction.Rel
        (InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
          result ctx regular returns tokens)
        srcRun targetRun)
    (hExec :
      Executes targetRun transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hSrcRegular :
      ∀ t o, Executes srcRun t (Except.ok o) →
        ∃ final, o = Structured.Outcome.regular final) :
    ∃ (srcState : RunState),
      next = regular ∧
        TypedCfgPreservation.StateRel srcState tokens state' ∧
        TypedCfgCompiler.Shape.SourceFrameFits
          expected srcState.evm.stack.length ∧
        srcState.returns = returns := by
  obtain ⟨leftOutcome, hLeft, hDone⟩ :=
    Simulation.Interaction.Rel.executes_right hRel hExec
  cases hDone with
  | ok hRel' =>
      obtain ⟨final, hFinal⟩ := hSrcRegular _ _ hLeft
      subst hFinal
      obtain ⟨targetState, hEq, hStateRel, hFits, hReturns⟩ :=
        InteractionControlPreservation.OpenOutcome.Rel.regular_elim_of_required_fallthrough
          hRequire hRel'
      injection hEq with hNext hState
      subst hState
      exact ⟨final, hNext, hStateRel, hFits, hReturns⟩

/--
**`codeHead` disjunct strengthened `hInv` leg.**  Mirrors the bare
`InteractionHInvDispatch.realizedWitness_of_codeHead_dispatch` but consumes the entry
`realizedWitnessFC` and transports its `FrameConsistent` conjunct across the straight-line run
via `srcState.returns = source.returns`. -/
theorem realizedWitnessFC_of_codeHead_dispatch
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {codeSourceProgram : Structured.Program}
    {compilerFuel sourceFuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular next : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitnessFC sourceProgram cfg calls entry target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.code code) ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hReg :
      ∀ out, result.fallthrough? = some out →
        TypedCfgPreservation.LabelShape cfg regular out)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg calls next state' := by
  -- The `.code` result is the single entry block with `input := input`; find it in the cfg and
  -- unify with the entry witness block to pin `block.input = input`.
  obtain ⟨codeOutput, _hType, hResultEq⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_code hCompile
  have hCodeMem :
      ({ label := entry
         input := input
         body := TypedCfgCompiler.Code.toCfg code
         output := codeOutput
         term := .jump regular } : TypedCfg.Block) ∈ result.blocks := by
    rw [hResultEq]; simp
  have hFindCode :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := TypedCfgCompiler.Code.toCfg code
            output := codeOutput
            term := .jump regular } :=
    hBlocks _ hCodeMem
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits0, hFC⟩ := hReal
  have hBlockEq :
      block =
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := codeOutput
          term := .jump regular } :=
    Option.some.inj (hFindReal.symm.trans hFindCode)
  subst hBlockEq
  have hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length := hFits0
  obtain ⟨expected, hFall⟩ :=
    TypedCfgCompilerFacts.Stmt.fallthrough_code_of_compileStmtFuel? hCompile
  have hRequire : result.requireFallthrough? expected = some () :=
    TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mpr (Or.inr hFall)
  have hProd :=
    InteractionControlPreservation.Stmt.openStep_code_of_compileStmtFuel?
      (sourceProgram := codeSourceProgram) (sourceFuel := sourceFuel)
      hCompile hBlocks hFits hStateRel
  obtain ⟨srcState, hNext, hStateRel', hFits', hReturns⟩ :=
    jump_state_rel_returns_of_outcome hRequire hProd hExec
      (fun _t _o hExec' =>
        InteractionConstructCoupling.stmt_openRun_code_only_regular hExec')
  subst hNext
  exact
    realizedWitnessFC_of_stateRel (hReg expected hFall) hStateRel' hFits'
      (by rw [hReturns]; exact hFC)

end InteractionFrameConsistent
end Structured
end EvmCompiler
