import EvmCompiler.Structured.InteractionCallPreservation
import EvmCompiler.Structured.InteractionEntryRealizedForward

/-!
# Child-entry `StateRel` extraction for the `call` composite (Step A / item 3b)

This module is the `call` analogue of
`InteractionBranchEntryRealized.jump_state_rel_of_rel` (the `if` template landed
session 14).  It lands the concrete sub-lemma the composite `call_forward_realizing`
recursor turns on: extracting the child procedure-entry `StateRel` from a concrete
non-stopping first-step jump of a compiled call-site block.

Unlike the `if` entry block — whose first `openStep` is a *`jumpi` branch* related
to the source condition run by `InteractionBranchPreservation.Condition.DoneRel`
(an interaction `Rel`), so the child `StateRel` must be read off backwards through
`Rel.executes_right` — the compiled call-site block is **silent**:
`InteractionCallPreservation.Call.openStep_entry_of_compileStmtFuel?`
(`InteractionCallPreservation.lean:264`) proves its `openStep` reduces to a
concrete `Simulation.Interaction.pure (.jump (ProcLabel.entry name) targetFinal)`
and directly hands back `StateRel … targetFinal` for the procedure entry.

So for the `call` case the extraction is even simpler than `if`: no backward
simulation is required.  A concrete `Executes` of a `pure` leaf pins the target
outcome (`pure x = .done (.ok x)`, so `Executes (pure x) transcript out` forces
`transcript = []` and `out = .ok x`); the jumped-to label and state are therefore
literally `ProcLabel.entry name` and `targetFinal`, and the `StateRel` supplied by
`openStep_entry_of_compileStmtFuel?` transports to `state'` by that equality.

`jump_state_rel_of_pure` below is phrased over the *abstract* pure-jump
characterization (the `openStep = pure (.jump childLabel childState)` equation plus
a child `StateRel`), exactly as `jump_state_rel_of_rel` is phrased over an abstract
branch `Rel`, so it is reusable for the eventual `call_forward_realizing`
accumulator discharge: feed it the `openStep_entry_of_compileStmtFuel?` outputs,
then invoke the procedure body's realizing lemma at the extracted `StateRel`.

Additive; no existing statement touched.  peepholeBody/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionCallPreservation
namespace Call

/--
Extract the child-entry `StateRel` (and the taken label) from a concrete
first-step jump of a block whose `openStep` reduces to a `pure` jump.

The compiled call-site block is silent, so its `openStep` is a concrete
`pure (.jump childLabel childState)` (this is exactly what
`openStep_entry_of_compileStmtFuel?` establishes, with
`childLabel = ProcLabel.entry name` and the child `StateRel` for `childState`).
Any concrete `Executes` of that `pure` to a `.jump next state'` leaf forces
`next = childLabel` and `state' = childState`, so the supplied child `StateRel`
transports to `state'`.

This is the `call` counterpart of
`InteractionBranchPreservation.Condition.jump_state_rel_of_rel`, and it is the
witness the composite `call` realizing case relays to the procedure body
fragment's realizing lemma at each non-stopping first jump.
-/
theorem jump_state_rel_of_pure
    {cfg : TypedCfg.Program}
    {entry childLabel next : Assembly.Label}
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
        transcript (Except.ok (TypedCfg.Outcome.jump next state'))) :
    next = childLabel ∧
      TypedCfgPreservation.StateRel childSource childTokens state' := by
  rw [hStep] at hExec
  simp only [Simulation.Interaction.pure] at hExec
  cases hExec with
  | done =>
      refine ⟨rfl, hChildRel⟩

end Call
end InteractionCallPreservation
end Structured
end EvmCompiler
