import EvmCompiler.Structured.InteractionConstructCoupling

/-!
# The `.code` (straight-line) coupling supplier — gate 1 of the route-2 `hInv`

Session 31 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-30).

Sessions 27/28/30 banked the per-entry ARM discharges of `block_category`'s case
split for `if`/`call`/dispatch/programEnd.  The last missing successor discharge is
the **`.code` (straight-line) arm**: a compiled `.code` statement lowers to a block
with terminator `.jump regular`, and under the WHOLE-PROGRAM `hInv` that jump is the
*sequential continuation* (not a fragment stop — the leaf `code_exec_realizing`
collapses it via the fragment-local `contract.stops`, which is not valid globally),
so `hInv` must produce `realizedWitness cfg regular state'`.

This module banks the `.code` leg trio, mirroring the branch/call suppliers:

* `jump_state_rel_of_outcome` — the extraction off the outcome-indexed
  `Rel (OutcomeDoneRel …)` coupling.  From a concrete first-step `.jump next state'`
  execution of the target block whose `openStep` is source-coupled by
  `Rel (OutcomeDoneRel result ctx regular returns tokens) srcRun …`, plus the fact
  that the source run only settles at a `regular` outcome (a straight-line `.code`
  run never breaks/continues/leaves — the break/continue/leave arms of
  `OpenOutcome.Rel` map to `.jump` too, but are semantically unreachable here), reads
  off `next = regular` and the child `StateRel`/`SourceFrameFits` at `state'`.
  Building block: `Rel.executes_right` + `Rel.regular_elim_of_required_fallthrough`.
* `realizedWitness_of_regular_jump` — the successor leg
  (∘ `realizedWitness_of_stateRel`), the `.code` sibling of
  `realizedWitness_of_{branch,pure,dispatch}_jump`.
* `realizedWitness_of_code_compile` — the per-construct supplier
  (∘ `openStep_code_of_compileStmtFuel?`), the `.code` sibling of
  `realizedWitness_of_{if,call}_compile`.  Discharges the `requireFallthrough?` and
  source-regular obligations from the `.code` compile fact + statement-run structure.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured

namespace InteractionControlPreservation
namespace OpenOutcome

open Simulation.Interaction (Executes)

/--
**Extraction off the outcome-indexed `Rel (OutcomeDoneRel …)` for a straight-line
`.jump regular` block.**

Given the outcome coupling `Rel (OutcomeDoneRel result ctx regular returns tokens)
srcRun targetRun` whose source run only ever settles at a `regular` outcome
(`hSrcRegular`) and whose compiled result requires the fallthrough shape `expected`
(`hRequire`), any concrete execution of `targetRun` to a `.jump next state'` is
mirrored (`Rel.executes_right`) by a `regular` source outcome; eliminating it with
`Rel.regular_elim_of_required_fallthrough` reads off `next = regular`, a source
`StateRel` for `state'`, and the child `SourceFrameFits`.

This is the `.code`/regular sibling of
`InteractionBranchPreservation.Condition.jump_state_rel_of_rel`.  `hSrcRegular` is
what discharges the CAVEAT (break/continue/leave source outcomes also map to `.jump`
under `OpenOutcome.Rel`): a straight-line `.code` run is regular-or-error, so those
arms are vacuous.
-/
theorem jump_state_rel_of_outcome
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
        (OutcomeDoneRel result ctx regular returns tokens) srcRun targetRun)
    (hExec :
      Executes targetRun transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hSrcRegular :
      ∀ t o, Executes srcRun t (Except.ok o) →
        ∃ final, o = Structured.Outcome.regular final) :
    ∃ (srcState : RunState),
      next = regular ∧
        TypedCfgPreservation.StateRel srcState tokens state' ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            expected srcState.evm.stack.length := by
  obtain ⟨leftOutcome, hLeft, hDone⟩ :=
    Simulation.Interaction.Rel.executes_right hRel hExec
  cases hDone with
  | ok hRel' =>
      obtain ⟨final, hFinal⟩ := hSrcRegular _ _ hLeft
      subst hFinal
      obtain ⟨targetState, hEq, hStateRel, hFits, _hReturns⟩ :=
        Rel.regular_elim_of_required_fallthrough hRequire hRel'
      injection hEq with hNext hState
      subst hState
      exact ⟨final, hNext, hStateRel, hFits⟩

end OpenOutcome
end InteractionControlPreservation

namespace InteractionRealizedWitnessSuccessor

open InteractionBoundedOwnerPreservation.OpenOutcome (realizedWitness realizedWitness_of_stateRel)
open Simulation.Interaction (Executes)

/--
**Regular/`.code` leg of the `realizedWitness` `openStep`-jump invariant.**

For a straight-line `.code` block whose `openStep` is source-coupled to a
regular-only source run by `Rel (OutcomeDoneRel result ctx regular returns tokens)`,
any concrete non-stopping first jump to `(next, state')` lands a child
`realizedWitness cfg next state'`, provided the ambient CFG block at `next` expects
the fallthrough shape `expected` (`LabelShape cfg next expected`).

Proof: `jump_state_rel_of_outcome` reads off `next = regular` and the child
`StateRel`/`SourceFrameFits` at `state'`; `realizedWitness_of_stateRel` packages them
with the target `LabelShape`.  Structural sibling of `realizedWitness_of_branch_jump`.
-/
theorem realizedWitness_of_regular_jump
    {cfg : TypedCfg.Program}
    {entry : Assembly.Label} {target : EVMState}
    {result : TypedCfgCompiler.Result} {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label} {returns : List ReturnDest}
    {tokens : List Word} {expected : TypedCfg.Shape}
    {srcRun : Simulation.Interaction EVMException Structured.Outcome}
    {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {state' : EVMState}
    (hRequire : result.requireFallthrough? expected = some ())
    (hRel :
      Simulation.Interaction.Rel
        (InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
          result ctx regular returns tokens)
        srcRun
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target))
    (hExec :
      Executes
        (TypedCfg.InteractionSemantics.Program.openStep cfg entry target)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
    (hSrcRegular :
      ∀ t o, Executes srcRun t (Except.ok o) →
        ∃ final, o = Structured.Outcome.regular final)
    (hLabelShape : TypedCfgPreservation.LabelShape cfg next expected) :
    realizedWitness cfg next state' := by
  obtain ⟨srcState, _hNext, hStateRel, hFits⟩ :=
    InteractionControlPreservation.OpenOutcome.jump_state_rel_of_outcome
      hRequire hRel hExec hSrcRegular
  exact realizedWitness_of_stateRel hLabelShape hStateRel hFits

end InteractionRealizedWitnessSuccessor

end Structured
end EvmCompiler
