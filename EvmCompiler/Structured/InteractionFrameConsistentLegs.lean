import EvmCompiler.Structured.InteractionFrameConsistent
import EvmCompiler.Structured.InteractionHInvDispatch

/-!
# Strengthened (`realizedWitnessFC`) `hInv` legs — the transport disjuncts (session 46)

Session 46 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-45 frontier item 1).

The nine `BlockGenShapeReg` `hInv` legs of `InteractionHInvDispatch.lean` land the successor
`realizedWitness`.  For the strengthened invariant they must land `realizedWitnessFC` — i.e.
additionally carry the per-witness `FrameConsistent` invariant to the child witness.

This module banks the **transport legs**: the disjuncts whose child witness has the SAME source
`returns` and realization `tokens` as the entry witness (only the runtime EVM stack shifts).
Because `FrameConsistent` is a function of `(source.returns, tokens)` alone
(`InteractionFrameConsistent.lean`), the entry witness's `FrameConsistent` conjunct transports
UNCHANGED — no push/pop, no returns-tracking.  These are:

* `realizedWitnessFC_of_nilJoin_dispatch` — identity fallthrough (`pure`-jump, child = entry
  source);
* `realizedWitnessFC_of_terminalHalt_dispatch` — halt (vacuous, no jump);
* `realizedWitnessFC_of_procAdapter_dispatch` — relabel-then-jump (`pure`-jump, child = entry
  source, runtime state unchanged);
* `realizedWitnessFC_of_caseEntryPop_dispatch` — switch case-entry `pop` (child = entry source
  with the scrutinee popped off the EVM stack; `returns`/`tokens` unchanged);
* `realizedWitnessFC_of_switchTest_dispatch` — switch scrutinee test (target-only comparison;
  child = entry source, `returns`/`tokens` unchanged).

The remaining legs shift the activation: codeHead/ifHead/forCond evaluate a source condition
(child `returns = entry returns` needs the condition-returns fact), callHead pushes a return
frame, and the dispatch arm pops one — those are handled elsewhere.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionFrameConsistent

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness)

/--
**Generic strengthened `pure`-jump successor.**  The `realizedWitnessFC` sibling of
`InteractionRealizedWitnessSuccessor.realizedWitness_of_pure_jump`: for a silent block whose
`openStep` reduces to `pure (.jump childLabel childState)` with child `StateRel childSource
childTokens childState`, any concrete first jump lands `realizedWitnessFC … next state'`,
provided the ambient block at `childLabel` expects `childInput`, the child frame fits, and the
child activation `(childSource.returns, childTokens)` is frame-consistent. -/
theorem realizedWitnessFC_of_pure_jump
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {entry childLabel next : Assembly.Label}
    {childInput : TypedCfg.Shape}
    {target childState state' : EVMState}
    {childSource : RunState} {childTokens : List Word}
    {transcript : Simulation.Interaction.Transcript}
    (hStep :
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump childLabel childState))
    (hChildRel :
      TypedCfgPreservation.StateRel childSource childTokens childState)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape : TypedCfgPreservation.LabelShape cfg childLabel childInput)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        childInput childSource.evm.stack.length)
    (hFC :
      FrameConsistent sourceProgram cfg calls childSource.returns childTokens) :
    realizedWitnessFC sourceProgram cfg calls next state' := by
  obtain ⟨hNext, hStateRel⟩ :=
    InteractionCallPreservation.Call.jump_state_rel_of_pure hStep hChildRel hExec
  subst hNext
  exact realizedWitnessFC_of_stateRel hLabelShape hStateRel hFits hFC

/--
**`nilJoin` disjunct strengthened `hInv` leg.**  The identity fallthrough's `openStep`
reduces to `pure (.jump exitLabel target)` keeping the entry source witness, so the entry
`realizedWitnessFC` (whose `FrameConsistent` conjunct is on the SAME `(source.returns, tokens)`)
transports directly. -/
theorem realizedWitnessFC_of_nilJoin_dispatch
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {entry exitLabel next : Assembly.Label} {input : TypedCfg.Shape}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitnessFC sourceProgram cfg calls entry target)
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := []
            output := input
            term := .jump exitLabel })
    (hExit : TypedCfgPreservation.LabelShape cfg exitLabel input)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg calls next state' := by
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits, hFC⟩ := hReal
  have hBlockEq :
      block =
        { label := entry
          input := input
          body := []
          output := input
          term := .jump exitLabel } :=
    Option.some.inj (hFindReal.symm.trans hFind)
  subst hBlockEq
  -- The identity join's `openStep` reduces to the silent `pure (.jump exitLabel target)`.
  have hStep :
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump exitLabel target) := by
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind,
      TypedCfg.Control.Block.run, TypedCfg.Control.Block.runBody]
    change
      Simulation.Interaction.bind
          (Simulation.Interaction.done
            (Except.ok (target, input)))
          (fun result =>
            if result.2 = input then
              Simulation.Interaction.done
                (Except.ok
                  (TypedCfg.Outcome.jump exitLabel result.1))
            else
              Simulation.Interaction.done
                (Except.error
                  (.InvalidInstruction : EVMException))) =
        Simulation.Interaction.done
          (Except.ok
            (TypedCfg.Outcome.jump exitLabel target))
    simp [Simulation.Interaction.bind]
  exact
    realizedWitnessFC_of_pure_jump hStep hStateRel hExec hExit hFits hFC

/--
**`terminalHalt` disjunct strengthened `hInv` leg.**  A halt block never
`Executes`-produces a jump, so the obligation is vacuous. -/
theorem realizedWitnessFC_of_terminalHalt_dispatch
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {entry next : Assembly.Label} {input : TypedCfg.Shape}
    {kind : Assembly.HaltKind}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := []
            output := input
            term := .halt kind })
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg calls next state' :=
  (InteractionMachineryCoupling.halt_openStep_no_jump hFind hExec).elim

/--
**`procAdapter` disjunct strengthened `hInv` leg.**  The relabel-then-jump block runs no
primitive (the `.relabel` leaves the runtime state unchanged), so its `openStep` reduces to
`pure (.jump bodyLabel target)` keeping the entry source witness; `FrameConsistent` transports
directly.  The static-shape shift (`blockInput → output`) is bridged by `hTransport` exactly as
in the bare leg. -/
theorem realizedWitnessFC_of_procAdapter_dispatch
    {sourceProgram : Structured.Program} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {entry bodyLabel next : Assembly.Label}
    {blockInput relabelTarget output : TypedCfg.Shape}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitnessFC sourceProgram cfg calls entry target)
    (hType :
      TypedCfg.Instr.type? (.relabel relabelTarget) blockInput = some output)
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := blockInput
            body := [.relabel relabelTarget]
            output := output
            term := .jump bodyLabel })
    (hBodyShape : TypedCfgPreservation.LabelShape cfg bodyLabel output)
    (hTransport :
      ∀ n, TypedCfgCompiler.Shape.SourceFrameFits blockInput n →
        TypedCfgCompiler.Shape.SourceFrameFits output n)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg calls next state' := by
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits, hFC⟩ := hReal
  have hBlockEq :
      block =
        { label := entry
          input := blockInput
          body := [.relabel relabelTarget]
          output := output
          term := .jump bodyLabel } :=
    Option.some.inj (hFindReal.symm.trans hFind)
  subst hBlockEq
  -- The relabel-body block's `openStep` reduces to the silent `pure (.jump bodyLabel target)`.
  have hStep :
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.pure
          (TypedCfg.Outcome.jump bodyLabel target) := by
    have hOpenBody :
        TypedCfg.InteractionSemantics.Block.openRunBody
            [.relabel relabelTarget] blockInput target =
          Simulation.Interaction.pure (target, output) := by
      rw [
        TypedCfg.InteractionSemantics.Block.openRunBody_eq_done_of_forall_not_prim]
      · simp [
          TypedCfg.Block.runBody, TypedCfg.Instr.runAt,
          hType, TypedCfg.Instr.runState]
        rfl
      · intro instr hMem op hEq
        simp only [List.mem_singleton] at hMem
        exact TypedCfg.Instr.noConfusion (hMem.symm.trans hEq)
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind,
      TypedCfg.Control.Block.run]
    change
      (do
        let result ←
          TypedCfg.InteractionSemantics.Block.openRunBody
            [.relabel relabelTarget] blockInput target
        if result.2 = output then
          pure (TypedCfg.Block.runTerm output (.jump bodyLabel) result.1)
        else
          throw .InvalidInstruction) =
        Simulation.Interaction.pure (.jump bodyLabel target)
    rw [hOpenBody]
    simp [TypedCfg.Block.runTerm]
    rfl
  exact
    realizedWitnessFC_of_pure_jump hStep hStateRel hExec hBodyShape
      (hTransport _ hFits) hFC

/--
**`caseEntryPop` disjunct strengthened `hInv` leg.**  The switch case-entry `pop` block pops
the scrutinee off the runtime EVM stack — the source ghost `returns`/realization `tokens` are
UNCHANGED (`withEVM` preserves `returns`), so the entry `FrameConsistent` transports. -/
theorem realizedWitnessFC_of_caseEntryPop_dispatch
    {sourceProgram : Structured.Program}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {entry label next : Assembly.Label} {input output : TypedCfg.Shape}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitnessFC sourceProgram cfg calls entry target)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := entry
        input := input
        body := [.pop]
        output := output
        term := .jump label } ∈ result.blocks)
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hExit : TypedCfgPreservation.LabelShape cfg label output)
    (hPopTransport :
      ∀ source : RunState,
        TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length →
        ∃ (stack : EvmYul.Stack Word) (value : Word),
          source.evm.stack.pop = some (stack, value) ∧
          TypedCfgCompiler.Shape.SourceFrameFits output
            (source.withEVM { source.evm with stack := stack }).evm.stack.length)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg calls next state' := by
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits, hFC⟩ := hReal
  have hFindPop := hBlocks _ hMem
  have hBlockEq :
      block =
        { label := entry
          input := input
          body := [.pop]
          output := output
          term := .jump label } :=
    Option.some.inj (hFindReal.symm.trans hFindPop)
  subst hBlockEq
  obtain ⟨stack, value, hPop, hPopFits⟩ := hPopTransport source hFits
  obtain ⟨targetFinal, hStep, hFinalRel⟩ :=
    InteractionSwitchPreservation.Switch.openStep_pop_jump
      hBlocks hMem hType hStateRel hPop
  rw [hStep] at hExec
  cases hExec
  exact
    realizedWitnessFC_of_stateRel hExit hFinalRel hPopFits
      (by simpa using hFC)

/--
**`switchTest` disjunct strengthened `hInv` leg.**  The switch scrutinee test performs a
target-only comparison that does NOT consume the source — child `returns`/`tokens` are the
entry's, so `FrameConsistent` transports. -/
theorem realizedWitnessFC_of_switchTest_dispatch
    {sourceProgram : Structured.Program}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    {testLabel caseLabel nextTest next : Assembly.Label}
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot} {caseValue : Word}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hReal : realizedWitnessFC sourceProgram cfg calls testLabel target)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := testLabel
        input := valueShape
        body := [.dup 0, .push caseValue, .prim .eq]
        output := TypedCfgCompilerFacts.Switch.testOutput valueShape
        term := .jumpi caseLabel nextTest } ∈ result.blocks)
    (hHead : valueShape.slots.head? = some slot)
    (hPopExists :
      ∀ source : RunState,
        TypedCfgCompiler.Shape.SourceFrameFits valueShape source.evm.stack.length →
        ∃ (stack : EvmYul.Stack Word) (value : Word),
          source.evm.stack.pop = some (stack, value))
    (hCaseShape : TypedCfgPreservation.LabelShape cfg caseLabel valueShape)
    (hNextShape : TypedCfgPreservation.LabelShape cfg nextTest valueShape)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg testLabel target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    realizedWitnessFC sourceProgram cfg calls next state' := by
  obtain ⟨source, tokens, block, hFindReal, hStateRel, hFits, hFC⟩ := hReal
  have hFindTest := hBlocks _ hMem
  have hBlockEq :
      block =
        { label := testLabel
          input := valueShape
          body := [.dup 0, .push caseValue, .prim .eq]
          output := TypedCfgCompilerFacts.Switch.testOutput valueShape
          term := .jumpi caseLabel nextTest } :=
    Option.some.inj (hFindReal.symm.trans hFindTest)
  subst hBlockEq
  obtain ⟨stack, value, hPop⟩ := hPopExists source hFits
  obtain ⟨targetFinal, hStep, hFinalRel⟩ :=
    InteractionSwitchPreservation.Switch.openStep_test
      hBlocks hMem hHead hStateRel hPop
  rw [hStep] at hExec
  cases hExec
  by_cases hEq : caseValue = value
  · rw [if_pos hEq]
    exact realizedWitnessFC_of_stateRel hCaseShape hFinalRel hFits hFC
  · rw [if_neg hEq]
    exact realizedWitnessFC_of_stateRel hNextShape hFinalRel hFits hFC

end InteractionFrameConsistent
end Structured
end EvmCompiler
