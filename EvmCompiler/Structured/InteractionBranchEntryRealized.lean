import EvmCompiler.Structured.InteractionBranchPreservation
import EvmCompiler.Structured.InteractionEntryRealizedForward

/-!
# Child-entry `StateRel` extraction for the `if` composite (Step A / item 3b prep)

This module lands the concrete sub-lemma the composite `if_forward_realizing`
recursor turns on, and — more importantly — **empirically validates the route**
for the composite realizing cases (`if`/`switch`/`for`/`call`) that sessions
5–13 had scoped as "requires re-threading the 16.7k-line source→cfg simulation".

The de-risking discovery (this session): the per-block `openStep_*_of_compileStmtFuel?`
relations **already expose the intermediate block-entry `StateRel`**.  For the
`if` entry block, `InteractionBranchPreservation.Condition.openStep_if_of_compileStmtFuel?`
gives

    Rel (DoneRel trueLabel falseLabel tokens bodyInput)
        (openRunCondition cond source) (openStep cfg entry target)

and `DoneRel = ExceptRel _ (ResultRel …)` where `ResultRel` (this file's
`InteractionBranchPreservation.Condition.ResultRel`) *carries*
`StateRel source.1 tokens targetState` for the jumped-to target state.  So a
concrete first-step jump of the composite entry block, backward-simulated through
`Simulation.Interaction.Rel.executes_right` (landed session 13), yields exactly
the source `StateRel` + `SourceFrameFits` witness the child fragment's realizing
lemma needs at its entry — **without** the giant-sim re-threading.

`jump_state_rel_of_rel` below is that extraction, stated over an abstract branch
relation so it is reusable for the eventual `if_forward_realizing` accumulator
discharge (feed it the `openStep_if_of_compileStmtFuel?` `Rel`, then invoke the
body's realizing lemma at the extracted `StateRel`).

Additive; no existing statement touched.  peepholeBody/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionBranchPreservation
namespace Condition

/--
Extract the child-entry `StateRel` (and the taken branch label) from a concrete
first-step jump of an `if`-style condition block.

Given the branch relation `Rel (DoneRel trueLabel falseLabel tokens restShape)`
between a source condition run and a target open step, any concrete execution of
the target to a `.jump next state'` is mirrored (`Rel.executes_right`) by a source
outcome satisfying `ResultRel`; destructuring that relation reads off the taken
label `next = if cond then trueLabel else falseLabel`, a source `StateRel` for the
jumped-to `state'`, and the child `SourceFrameFits`.

This is exactly the witness the composite `if` realizing case relays to the body
fragment's realizing lemma at each non-stopping first jump.
-/
theorem jump_state_rel_of_rel
    {trueLabel falseLabel : Assembly.Label}
    {tokens : List Word} {restShape : TypedCfg.Shape}
    {srcRun : Simulation.Interaction EVMException (RunState × Bool)}
    {targetRun : Simulation.Interaction EVMException TypedCfg.Outcome}
    {transcript : Simulation.Interaction.Transcript}
    {next : Assembly.Label} {state' : EVMState}
    (hRel :
      Simulation.Interaction.Rel
        (DoneRel trueLabel falseLabel tokens restShape) srcRun targetRun)
    (hExec :
      Simulation.Interaction.Executes targetRun transcript
        (Except.ok (TypedCfg.Outcome.jump next state'))) :
    ∃ (srcState : RunState) (cond : Bool),
      next = (if cond then trueLabel else falseLabel) ∧
        TypedCfgPreservation.StateRel srcState tokens state' ∧
          TypedCfgCompiler.Shape.SourceFrameFits
            restShape srcState.evm.stack.length := by
  obtain ⟨_leftOutcome, _hLeft, hDone⟩ :=
    Simulation.Interaction.Rel.executes_right hRel hExec
  cases hDone with
  | ok hResult =>
      obtain ⟨targetState, hEq, hStateRel, hFits⟩ := hResult
      injection hEq with hNext hState
      subst hState
      exact ⟨_, _, hNext, hStateRel, hFits⟩

end Condition
end InteractionBranchPreservation
end Structured
end EvmCompiler
