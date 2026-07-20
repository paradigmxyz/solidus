import EvmCompiler.Structured.InteractionConstructCoupling
import EvmCompiler.Structured.InteractionSwitchPreservation

/-!
# Machinery-block successor suppliers (route-2 `hInv` machinery arms)

Session 33 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-32).

Sessions 27–31 banked the per-construct successor suppliers for the blocks that
ARE `compileStmtFuel?` heads (`realizedWitness_of_{if,call,code}_compile`,
`realizedWitness_of_dispatch_jump`).  The assembled provenance capstone additionally
has to classify the **non-head machinery/join blocks** that the `for`/`switch`
lowerings emit as reachable jump targets but which are NOT `compileStmtFuel?` heads:
the for-loop-condition block, the switch test / case-entry blocks, the default `pop`
block, and the nil-join block.  This module banks their successor suppliers — the
inputs the machinery disjuncts of the capstone's classification predicate feed the
`hInv` case split.

## `realizedWitness_of_condBlock_jump` — the condition-block machinery supplier

The **for-loop-condition** block (label `LabelSupply.label supply 0`) has exactly the
same shape as an `if`-condition head — `{ body := Code.toCfg cond, term := .jumpi
trueLabel falseLabel }` — differing only in that it is generated inside a `.for_`
lowering rather than being a `compileStmtFuel?` head.  Its successor story is
therefore identical to the `if` head's: its `openStep` is source-coupled to the
condition run by `Condition.DoneRel`, and `realizedWitness_of_branch_jump`
(session 27) reads the child `StateRel`/`SourceFrameFits` off the concrete first
jump.

This lemma packages that story generically, keyed on the block's `findBlock?` fact
(the exact fact the eventual `hInv` proof has in hand: `realizedWitness` carries
`cfg.findBlock? e = some block`, and the capstone identifies `block` as the
condition block) plus the condition's type/source facts (which the enclosing
`for` compile fact exposes via `Loop.components_of_compileStmtFuel?_for`).  It is a
direct composition of `openRunCondition_jumpi_toCfg` (the general condition-block
`DoneRel` producer, reused from the `if` path) with `realizedWitness_of_branch_jump`,
and subsumes the `if`-head condition case as well.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionMachineryCoupling

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness realizedWitness_of_stateRel)

/--
**Condition-block (`.jumpi` over `Code.toCfg cond`) successor supplier.**

For any ambient CFG block at `entry` of the condition shape
`{ input, body := Code.toCfg cond, output, term := .jumpi trueLabel falseLabel }`
(the shape of both an `if`-condition head and a `for`-loop-condition machinery
block), whose condition types (`hType`) and requires one source word of output
(`hSource`), given the `realizedWitness` ingredients carried at the entry
(`SourceFrameFits input …` + `StateRel source tokens target`), any concrete first
jump to `(next, state')` lands a child `realizedWitness cfg next state'`, provided
the ambient CFG block at `next` expects the branch's residual shape
(`{ output with slots := output.slots.tail }`).

Proof: rewriting `openStep` through `findBlock?` (`hFind`) reduces it to the block's
`openRun`, which `openRunCondition_jumpi_toCfg` couples to the condition run by
`Condition.DoneRel`; `realizedWitness_of_branch_jump` reads off the child
`StateRel`/`SourceFrameFits` at `state'` and packages it with the target
`LabelShape`.
-/
theorem realizedWitness_of_condBlock_jump
    {cfg : TypedCfg.Program}
    {cond : Structured.Code} {input output : TypedCfg.Shape}
    {entry trueLabel falseLabel next : Assembly.Label}
    {source : RunState} {tokens : List Word}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := TypedCfgCompiler.Code.toCfg cond
            output := output
            term := .jumpi trueLabel falseLabel })
    (hType : TypedCfgCompiler.Code.type? cond input = some output)
    (hSource : TypedCfgCompiler.Shape.requireSourceWords? 1 output = some ())
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape :
      TypedCfgPreservation.LabelShape cfg next
        { output with slots := output.slots.tail }) :
    realizedWitness cfg next state' := by
  have hDoneRel :
      Simulation.Interaction.Rel
        (InteractionBranchPreservation.Condition.DoneRel trueLabel falseLabel tokens
          { output with slots := output.slots.tail })
        (InteractionSemantics.Code.openRunCondition cond source)
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target) := by
    simp only [TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind]
    simpa using
      InteractionBranchPreservation.Condition.openRunCondition_jumpi_toCfg
        (entry := entry) (trueLabel := trueLabel) (falseLabel := falseLabel)
        hType hSource hFits hRel
  exact
    InteractionRealizedWitnessSuccessor.realizedWitness_of_branch_jump
      hDoneRel hExec hLabelShape

/--
**Switch-test block successor supplier.**

A switch test block `{ body := [.dup 0, .push caseValue, .prim .eq], term := .jumpi
caseLabel nextTest }` performs a purely target-side comparison of the retained
scrutinee against `caseValue` and conditionally jumps, WITHOUT consuming the
scrutinee — so its child `StateRel` is at the *same* source (`hFinalRel : StateRel
source tokens targetFinal`), hence its `SourceFrameFits valueShape …` witness is
unchanged from the entry (`hFits`).  Both successor labels (case-entry and next-test)
expect `valueShape`.

Given the entry `realizedWitness` ingredients (`hFits` + `hRel`), the scrutinee pop
(`hPop`), and any concrete first jump, this lands the child `realizedWitness cfg next
state'`, provided the ambient block at `next` expects `valueShape`.

Proof: `openStep_test` settles the `openStep` to a completed `.jump (if caseValue =
value then caseLabel else nextTest) targetFinal` outcome with `StateRel source tokens
targetFinal`; the concrete jump `hExec` forces `next`/`state'` to that outcome;
`realizedWitness_of_stateRel` packages the retained-source `StateRel` with the target
`LabelShape`. -/
theorem realizedWitness_of_test_jump
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {testLabel caseLabel nextTest next : Assembly.Label}
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue value : Word}
    {source : RunState} {tokens : List Word}
    {target state' : EVMState} {stack : EvmYul.Stack Word}
    {transcript : Simulation.Interaction.Transcript}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := testLabel
        input := valueShape
        body := [.dup 0, .push caseValue, .prim .eq]
        output := InteractionSwitchPreservation.Switch.testOutput valueShape
        term := .jumpi caseLabel nextTest } ∈ result.blocks)
    (hHead : valueShape.slots.head? = some slot)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits valueShape source.evm.stack.length)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg testLabel target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape : TypedCfgPreservation.LabelShape cfg next valueShape) :
    realizedWitness cfg next state' := by
  obtain ⟨targetFinal, hStep, hFinalRel⟩ :=
    InteractionSwitchPreservation.Switch.openStep_test hBlocks hMem hHead hRel hPop
  rw [hStep] at hExec
  cases hExec
  exact realizedWitness_of_stateRel hLabelShape hFinalRel hFits

/--
**Switch case-entry / default `pop` block successor supplier.**

A switch case-entry (or absent-default) block `{ body := [.pop], term := .jump label }`
removes the retained scrutinee and jumps unconditionally to the selected case body (or
regular continuation).  Its child `StateRel` is at the popped source `source.withEVM {
… stack := stack }` (`hFinalRel`), so its child `SourceFrameFits output …` witness is
supplied by `hFits` (the fits after popping one word — discharged at assembly from the
switch's `requireSourceWords? 1 valueShape` fact via `sourceFrameFits_pop`, exactly as
`realizedWitness_of_pure_jump` takes its child fits).

Given the entry `realizedWitness` `StateRel` (`hRel`), the scrutinee pop (`hPop`), the
child fits (`hFits`), and any concrete first jump, this lands the child
`realizedWitness cfg next state'`, provided the ambient block at `next` expects
`output`.

Proof: `openStep_pop_jump` settles the `openStep` to a completed `.jump label
targetFinal` outcome with `StateRel (source.withEVM …) tokens targetFinal`; `hExec`
forces `next`/`state'` to that outcome; `realizedWitness_of_stateRel` packages it with
the target `LabelShape`. -/
theorem realizedWitness_of_pop_jump
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {entry label next : Assembly.Label}
    {input output : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {target state' : EVMState} {stack : EvmYul.Stack Word} {value : Word}
    {transcript : Simulation.Interaction.Transcript}
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
    (hMem :
      { label := entry
        input := input
        body := [.pop]
        output := output
        term := .jump label } ∈ result.blocks)
    (hType : TypedCfg.Instr.type? .pop input = some output)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits output
        (source.withEVM { source.evm with stack := stack }).evm.stack.length)
    (hLabelShape : TypedCfgPreservation.LabelShape cfg next output) :
    realizedWitness cfg next state' := by
  obtain ⟨targetFinal, hStep, hFinalRel⟩ :=
    InteractionSwitchPreservation.Switch.openStep_pop_jump hBlocks hMem hType hRel hPop
  rw [hStep] at hExec
  cases hExec
  exact realizedWitness_of_stateRel hLabelShape hFinalRel hFits

/--
**Nil-join block successor supplier.**

The empty statement-list join block `{ input, body := [], output := input, term :=
.jump exitLabel }` (emitted by `compileStmtListFuel? … [] …`) is a pure identity jump:
its `openStep` reduces silently to `pure (.jump exitLabel target)` with the state
unchanged, so its child `StateRel`/`SourceFrameFits` are exactly the entry's (`hRel`,
`hFits`).  The successor `exitLabel` expects the join's `input` (its fallthrough
shape).

Given the join block's `findBlock?` fact, the entry `realizedWitness` ingredients
(`hFits` + `hRel`), and any concrete first jump, this lands the child
`realizedWitness cfg next state'`, provided the ambient block at `exitLabel` expects
`input`.

Proof: the empty-body block's `openStep` reduces to `pure (.jump exitLabel target)`
(the join is the compiler's identity fallthrough); `realizedWitness_of_pure_jump`
(session 27) forces `next = exitLabel`, keeps the child `StateRel` at `target`, and
packages it with the target `LabelShape`.  This is the `.jump`/join sibling of the
call `pure`-jump leg. -/
theorem realizedWitness_of_join_jump
    {cfg : TypedCfg.Program}
    {entry exitLabel next : Assembly.Label} {input : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := input
            body := []
            output := input
            term := .jump exitLabel })
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape : TypedCfgPreservation.LabelShape cfg exitLabel input) :
    realizedWitness cfg next state' := by
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
    InteractionRealizedWitnessSuccessor.realizedWitness_of_pure_jump
      hStep hRel hExec hLabelShape hFits

/--
**Proc-entry adapter (`.relabel`-then-`.jump`) block successor supplier.**

The procedure-entry ADAPTER block
`{ input := blockInput, body := [.relabel relabelTarget], output := output,
   term := .jump bodyLabel }` (emitted at `ProcLabel.entry proc.name` by the
adapter route of `ProcFragment.route`, `Core.lean:2969`, with
`blockInput = Shape.procEntry proc`, `relabelTarget = fragment.input`,
`bodyLabel = ProcLabel.body proc.name`) is a pure retyping jump: `.relabel` runs
no primitive and leaves the runtime state UNCHANGED, so its `openStep` reduces
silently to `pure (.jump bodyLabel target)` (exactly the reduction inside
`InteractionCallPreservation.openRunNResult_procEntry`, `:696–740`), and its child
`StateRel` is the entry's (`hRel`, state unchanged — `StateRel` mentions no shape,
so it needs no relabel transport).

The relabel DOES change the block's static shape (`blockInput → output`, where
`output = relabelTarget` when the relabel type-checks, `Typing.lean:51`), and
`SourceFrameFits` is not preserved across a relabel in general (`relabelCompatible`
lets a `.word` slot match any slot, so `sourceView`/`returnTokenDepth?` may differ).
So — exactly as `realizedWitness_of_pop_jump` / `realizedWitness_of_pure_jump` take
their child fits as a hypothesis — this supplier takes the child fits at the
successor shape (`hFits : SourceFrameFits output …`) rather than transporting the
entry fits; the concrete transport (when `output = relabelTarget = fragment.input`)
is discharged at the capstone assembly, where the proc's entry/body shapes are known.

Given the adapter's `findBlock?` fact (`hFind`), the relabel type fact (`hType`),
the entry `realizedWitness` `StateRel` (`hRel`), the child fits (`hFits`), and any
concrete first jump (`hExec`), this lands the child `realizedWitness cfg next state'`,
provided the ambient block at `bodyLabel` expects `output`.

Proof: the relabel-body block's `openStep` reduces to `pure (.jump bodyLabel target)`
(the relabel is a no-op on the runtime state, mirroring the reduction in
`openRunNResult_procEntry`); `realizedWitness_of_pure_jump` (session 27) forces
`next = bodyLabel`, keeps the child `StateRel` at `target`, and packages it with the
target `LabelShape`.  This is the `.relabel`/adapter sibling of the nil-join leg. -/
theorem realizedWitness_of_adapter_jump
    {cfg : TypedCfg.Program}
    {entry bodyLabel next : Assembly.Label}
    {blockInput relabelTarget output : TypedCfg.Shape}
    {source : RunState} {tokens : List Word}
    {target state' : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hFind :
      cfg.findBlock? entry =
        some
          { label := entry
            input := blockInput
            body := [.relabel relabelTarget]
            output := output
            term := .jump bodyLabel })
    (hType :
      TypedCfg.Instr.type? (.relabel relabelTarget) blockInput = some output)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits output source.evm.stack.length)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hLabelShape : TypedCfgPreservation.LabelShape cfg bodyLabel output) :
    realizedWitness cfg next state' := by
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
    InteractionRealizedWitnessSuccessor.realizedWitness_of_pure_jump
      hStep hRel hExec hLabelShape hFits

/--
**Terminal (`.halt`) block: no jump successor.**

A `.terminal kind` statement compiles to the empty-body halt block
`{ input, body := [], output := input, term := .halt kind }`
(`TypedCfgCompiler.lean:553`).  Its `openStep` reduces to
`.done (runTermChecked input (.halt kind) target)`, which for a halt terminator is
always either `.ok (.halt kind …)` (a non-`selfdestruct` kind, or an allowed
`selfdestruct`) or `.error .StaticModeViolation` (a static-mode `selfdestruct`) —
in NO case an `.ok (.jump …)`.  So a terminal block can never `Executes`-produce a
jump, and the `hInv` obligation at a terminal entry is vacuous — the general
sibling of `programEnd_openStep_no_jump` (which handles the single `.halt .stop`
programEnd block).  This completes the reachable-block discharge family: every
generated block category (compiled head / for-cond / switch-test / case-entry /
nil-join [which also covers brk/cont/leave] / proc-entry adapter / dispatch /
programEnd / terminal) now has its successor supplier or vacuity lemma. -/
theorem halt_openStep_no_jump
    {cfg : TypedCfg.Program}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    {kind : Assembly.HaltKind}
    {target state' : EVMState} {next : Assembly.Label}
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
    False := by
  have hStep :
      TypedCfg.InteractionSemantics.Program.openStep cfg entry target =
        Simulation.Interaction.done
          (TypedCfg.Block.runTermChecked input (.halt kind) target) := by
    simp only [
      TypedCfg.InteractionSemantics.Program.openStep,
      TypedCfg.Control.Program.step, hFind,
      TypedCfg.Control.Block.run, TypedCfg.Control.Block.runBody,
      TypedCfg.Block.runTerm]
    change
      Simulation.Interaction.bind
          (Simulation.Interaction.done (Except.ok (target, input)))
          (fun result =>
            if result.2 = input then
              match TypedCfg.Block.runTermChecked input (.halt kind) result.1 with
              | .ok outcome => Simulation.Interaction.pure outcome
              | .error err => Simulation.Interaction.error err
            else
              Simulation.Interaction.done
                (Except.error (.InvalidInstruction : EVMException))) =
        Simulation.Interaction.done
          (TypedCfg.Block.runTermChecked input (.halt kind) target)
    simp only [Simulation.Interaction.bind_done_ok, if_pos rfl]
    cases TypedCfg.Block.runTermChecked input (.halt kind) target with
    | ok outcome => rfl
    | error err => rfl
  rw [hStep] at hExec
  by_cases hSelf : kind = .selfdestruct
  · subst hSelf
    by_cases hPerm : target.executionEnv.perm = true
    · rw [TypedCfg.Block.runTermChecked_halt_of_allowed _ _ _
        (fun _ => hPerm)] at hExec
      cases hExec
    · rw [TypedCfg.Block.runTermChecked_selfdestruct_of_static _ _
        (Bool.not_eq_true _ ▸ hPerm)] at hExec
      cases hExec
  · rw [TypedCfg.Block.runTermChecked_halt_of_allowed _ _ _
      (fun h => absurd h hSelf)] at hExec
    cases hExec

end InteractionMachineryCoupling
end Structured
end EvmCompiler
