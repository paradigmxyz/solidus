import EvmCompiler.Structured.InteractionFrameConsistentLegs

/-!
# Strengthened (`realizedWitnessFC`) `hInv` legs — the condition-branch disjuncts (session 46)

Session 46 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-45 frontier item 1).

The `ifHead` and `forCond` disjuncts evaluate a source condition before branching.  Their child
witness is the post-condition source state `afterCond`, whose ghost `returns` equal the entry
source's `returns` (a straight-line condition run touches no return frame —
`openRunCondition_returns`).  So the entry witness's `FrameConsistent` conjunct transports once
we expose that returns equality, which the bare legs discard.

This module banks:

* `jump_state_rel_returns_of_rel` — the returns-exposing sibling of
  `InteractionBranchPreservation.Condition.jump_state_rel_of_rel`: from the condition `DoneRel`
  STRENGTHENED with `ConditionReturnsEq` it additionally reads off `afterCond.returns =
  sourceReturns`;
* `realizedWitnessFC_of_ifHead_dispatch` / `realizedWitnessFC_of_forCond_dispatch` — the two
  strengthened branch legs.

The `codeHead` leg (also a condition-free straight-line block) is handled separately; callHead
(push) and the dispatch arm (pop) shift the activation and are banked elsewhere.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionFrameConsistent

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)

/--
**Returns-exposing branch extraction.**  The `jump_state_rel_of_rel` sibling that, from the
condition `DoneRel` strengthened with `ConditionReturnsEq sourceReturns`, ALSO reads off the
post-condition returns equality `afterCond.returns = sourceReturns` — the fact the strengthened
`FrameConsistent` invariant transports across.  Mirrors the extraction inside
`allEntriesRealized_branch_step`. -/
theorem jump_state_rel_returns_of_rel
    {trueLabel falseLabel : Assembly.Label}
    {tokens : List Word} {restShape : TypedCfg.Shape}
    {sourceReturns : List ReturnDest}
    {srcRun : Simulation.Interaction EVMException (RunState × Bool)}
    {targetRun : Simulation.Interaction EVMException TypedCfg.Outcome}
    {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {state' : EVMState}
    (hStrong :
      Simulation.Interaction.Rel
        (fun leftDone rightDone =>
          InteractionBranchPreservation.Condition.DoneRel
              trueLabel falseLabel tokens restShape leftDone rightDone ∧
            InteractionSemantics.Code.ConditionReturnsEq sourceReturns leftDone)
        srcRun targetRun)
    (hExec :
      Simulation.Interaction.Executes targetRun transcript
        (Except.ok (TypedCfg.Outcome.jump next state'))) :
    ∃ (afterCond : RunState) (cond : Bool),
      next = (if cond then trueLabel else falseLabel) ∧
        TypedCfgPreservation.StateRel afterCond tokens state' ∧
        TypedCfgCompiler.Shape.SourceFrameFits
          restShape afterCond.evm.stack.length ∧
        afterCond.returns = sourceReturns := by
  obtain ⟨leftOutcome, _hLeftExec, hStrongDone⟩ :=
    Simulation.Interaction.Rel.executes_right hStrong hExec
  cases leftOutcome with
  | error e =>
      obtain ⟨hDone, _⟩ := hStrongDone
      cases hDone
  | ok conditionResult =>
      obtain ⟨hDone, hRet⟩ := hStrongDone
      cases hDone with
      | ok hResultRel =>
          obtain ⟨targetState, hEq, hAfterCondRel, hAfterCondFits⟩ := hResultRel
          rcases conditionResult with ⟨afterCond, cond⟩
          have hReturns : afterCond.returns = sourceReturns := by
            simpa [InteractionSemantics.Code.ConditionReturnsEq] using hRet
          injection hEq with hNext hState
          subst hState
          exact ⟨afterCond, cond, hNext, hAfterCondRel, hAfterCondFits, hReturns⟩

/--
**`ifHead` disjunct strengthened `hInv` leg.**  Mirrors the bare
`InteractionHInvDispatch.realizedWitness_of_ifHead_dispatch` but consumes the entry
`realizedWitnessFC` and transports its `FrameConsistent` conjunct to the body/regular child via
the returns-exposing extractor (`afterCond.returns = source.returns`). -/
theorem realizedWitnessFC_of_ifHead_dispatch
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {compilerFuel : Nat} {cond : Structured.Code} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular next : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitnessFC sourceProgram cfg calls entry target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.if_ cond body) ctx
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
  obtain ⟨output, condition, bodyResult, hType, hSource, hHead,
      hBodyCompile, hBodyRequire, hResultEq⟩ :=
    TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
  have hCondMem :
      ({ label := entry
         input := input
         body := TypedCfgCompiler.Code.toCfg cond
         output := output
         term := .jumpi (LabelSupply.label supply 0) regular } :
        TypedCfg.Block) ∈ result.blocks := by
    rw [hResultEq]; simp
  have hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := TypedCfgCompiler.Code.toCfg cond
            output := output
            term := .jumpi (LabelSupply.label supply 0) regular } :=
    hBlocks _ hCondMem
  -- Unify the entry witness block with the condition block, extracting the entry witness data.
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits0, hFC⟩ := hReal
  have hBlockEq :
      block =
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg cond
          output := output
          term := .jumpi (LabelSupply.label supply 0) regular } :=
    Option.some.inj (hFindReal.symm.trans hFind)
  subst hBlockEq
  have hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length := hFits0
  have hBodyBlocks : TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
    intro blk hMem
    apply hBlocks
    rw [hResultEq]
    simp only [List.mem_cons]
    exact Or.inr hMem
  have hBodyLS :
      TypedCfgPreservation.LabelShape cfg (LabelSupply.label supply 0)
        { output with slots := output.slots.tail } :=
    TypedCfgPreservation.LabelShape.of_compileBlockFuel? hBodyCompile hBodyBlocks
  have hDoneRel :
      Simulation.Interaction.Rel
        (InteractionBranchPreservation.Condition.DoneRel
          (LabelSupply.label supply 0) regular tokens
          { output with slots := output.slots.tail })
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target) := by
    simp only [TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa using
      InteractionBranchPreservation.Condition.openRunCondition_jumpi_toCfg
        (entry := entry) (trueLabel := LabelSupply.label supply 0)
        (falseLabel := regular) hType hSource hFits hStateRel
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_left hDoneRel
      (InteractionSemantics.Code.openRunCondition_returns cond source)
  obtain ⟨afterCond, cnd, hNext, hStateRel2, hFits', hReturns⟩ :=
    jump_state_rel_returns_of_rel hStrong hExec
  have hLS :
      TypedCfgPreservation.LabelShape cfg next
        { output with slots := output.slots.tail } := by
    rw [hNext]
    cases cnd with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact hReg _ (by rw [hResultEq])
    | true =>
        simp only [if_true]
        exact hBodyLS
  exact
    realizedWitnessFC_of_stateRel hLS hStateRel2 hFits'
      (by rw [hReturns]; exact hFC)

/--
**`forCond` disjunct strengthened `hInv` leg.**  Mirrors the bare
`InteractionHInvDispatch.realizedWitness_of_forCond_dispatch` but consumes the entry
`realizedWitnessFC` and transports its `FrameConsistent` conjunct via the returns-exposing
extractor. -/
theorem realizedWitnessFC_of_forCond_dispatch
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {cond : Structured.Code} {input output : TypedCfg.Shape}
    {label trueLabel falseLabel next : Assembly.Label}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitnessFC sourceProgram cfg calls label target)
    (hType : TypedCfgCompiler.Code.type? cond input = some output)
    (hSource : TypedCfgCompiler.Shape.requireSourceWords? 1 output = some ())
    (hFind :
      cfg.findBlock? label =
        some
          { label := label
            input := input
            body := TypedCfgCompiler.Code.toCfg cond
            output := output
            term := .jumpi trueLabel falseLabel })
    (hFalseShape :
      TypedCfgPreservation.LabelShape cfg falseLabel
        { output with slots := output.slots.tail })
    (hTrueShape :
      TypedCfgPreservation.LabelShape cfg trueLabel
        { output with slots := output.slots.tail })
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg label target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg calls next state' := by
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits0, hFC⟩ := hReal
  have hBlockEq :
      block =
        { label := label
          input := input
          body := TypedCfgCompiler.Code.toCfg cond
          output := output
          term := .jumpi trueLabel falseLabel } :=
    Option.some.inj (hFindReal.symm.trans hFind)
  subst hBlockEq
  have hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length := hFits0
  have hDoneRel :
      Simulation.Interaction.Rel
        (InteractionBranchPreservation.Condition.DoneRel trueLabel falseLabel tokens
          { output with slots := output.slots.tail })
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep cfg label target) := by
    simp only [TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa using
      InteractionBranchPreservation.Condition.openRunCondition_jumpi_toCfg
        (entry := label) (trueLabel := trueLabel) (falseLabel := falseLabel)
        hType hSource hFits hStateRel
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_left hDoneRel
      (InteractionSemantics.Code.openRunCondition_returns cond source)
  obtain ⟨afterCond, cnd, hNext, hStateRel2, hFits', hReturns⟩ :=
    jump_state_rel_returns_of_rel hStrong hExec
  have hLS :
      TypedCfgPreservation.LabelShape cfg next
        { output with slots := output.slots.tail } := by
    rw [hNext]
    cases cnd with
    | false => simp only [Bool.false_eq_true, if_false]; exact hFalseShape
    | true => simp only [if_true]; exact hTrueShape
  exact
    realizedWitnessFC_of_stateRel hLS hStateRel2 hFits'
      (by rw [hReturns]; exact hFC)

end InteractionFrameConsistent
end Structured
end EvmCompiler
