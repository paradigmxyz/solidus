import EvmCompiler.TypedCfg.InteractionSettlesCap
import EvmCompiler.Solidus.OpenRunContainment

/-!
# The `RunSettles` bridge core (Step A / item 3b, session-22 lever)

`InteractionSettlesCap` supplies the upward accumulator promotion
(`AllEntriesRealized.of_runSettles`) built on the non-exhaustion witness
`RunSettles`.  The composite realizing recursors (`switch`/`call`/`for`) must
*supply* `RunSettles cfg policy childBudget childLabel childState` for the child
fragment.  This module provides the target-side, `StateRel`-free core that turns a
per-branch classification of the child's fuel-bounded run into `RunSettles`.

## The two facts that discharge a settled branch

A branch of the `budget`-fuel whole-program run is settled (never
`.ok (.exhausted …)`) as soon as it agrees, along its exact transcript, with a
*smaller*-fuel run that has already reached a proper `.stopped` result or an
interaction `.error`.  This module makes the two monotonicity facts precise and
unconditional:

* `executes_stopped_add_right` / `executes_stopped_of_le` — a `.stopped` leaf
  reached at fuel `m` persists (with padded remaining) at every fuel `n ≥ m`,
  along the same transcript.  (The tail continuation of an already-stopped run is
  the pure `.stopped (remaining + rest)` leaf.)
* `executes_error_add_right` / `executes_error_of_le` — an interaction `.error`
  leaf reached at fuel `m` persists verbatim at every fuel `n ≥ m` (a
  `.done (.error …)` is absorbing under `bind`).

Combined with the frozen determinism lemma
`Solidus.OpenRunContainment.executes_unique` (an interaction reaches a unique
terminal outcome along one fixed transcript), these give
`RunSettles.of_cover`: if every branch of the `budget`-run is covered by a
within-budget `.stopped` or `.error` along the same transcript, the `budget`-run
never exhausts.

Everything here is target-side and `StateRel`-free; the composite threading
discharges the coverage hypothesis at each child leaf from the child fragment's
`BoundedExecPreservesUnder` (success) / `BoundedRuntimeErrorExecPreservesUnder`
(runtime error).  Additive; `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace TypedCfg
namespace InteractionSemantics
namespace Program

open Simulation (Interaction)

/--
**A `.stopped` leaf persists upward in fuel (additive form).**  If the
`firstFuel`-run executes `transcript` to `.ok (.stopped remaining outcome)`, then
the `(firstFuel + restFuel)`-run executes the *same* transcript to
`.ok (.stopped (remaining + restFuel) outcome)`.

`openRunNResultWithStop_add` factors the longer run as the `firstFuel`-run bound
to `continueOpenRunNResultWithStop … restFuel`, which on an already-`.stopped`
value is the pure `.stopped (remaining + restFuel)` leaf.
-/
theorem executes_stopped_add_right
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {firstFuel : Nat} {label : Label} {state : EVMState}
    {transcript : Interaction.Transcript}
    {remaining : Nat} {outcome : TypedCfg.Outcome}
    (h :
      Interaction.Executes
        (openRunNResultWithStop stopJump program firstFuel label state)
        transcript (Except.ok (Control.Program.RunResult.stopped remaining outcome)))
    (restFuel : Nat) :
    Interaction.Executes
      (openRunNResultWithStop stopJump program (firstFuel + restFuel) label state)
      transcript
      (Except.ok
        (Control.Program.RunResult.stopped (remaining + restFuel) outcome)) := by
  rw [openRunNResultWithStop_add]
  have hRest :
      Interaction.Executes
        (continueOpenRunNResultWithStop stopJump program restFuel
          (Control.Program.RunResult.stopped remaining outcome))
        [] (Except.ok
              (Control.Program.RunResult.stopped (remaining + restFuel) outcome)) := by
    simpa only [continueOpenRunNResultWithStop] using
      Interaction.Executes.done
        (Except.ok
          (Control.Program.RunResult.stopped (remaining + restFuel) outcome))
  simpa using Interaction.Executes.bind_ok h hRest

/-- **A `.stopped` leaf persists upward in fuel (`≤` form).**  Only the *shape*
`.ok (.stopped _ outcome)` and its transcript are preserved; the exact remaining
fuel is irrelevant to the settling argument, so it is left existential. -/
theorem executes_stopped_of_le
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {m n : Nat} {label : Label} {state : EVMState}
    {transcript : Interaction.Transcript}
    {remaining : Nat} {outcome : TypedCfg.Outcome}
    (hle : m ≤ n)
    (h :
      Interaction.Executes
        (openRunNResultWithStop stopJump program m label state)
        transcript (Except.ok (Control.Program.RunResult.stopped remaining outcome))) :
    ∃ remaining',
      Interaction.Executes
        (openRunNResultWithStop stopJump program n label state)
        transcript
        (Except.ok (Control.Program.RunResult.stopped remaining' outcome)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  exact ⟨remaining + k, executes_stopped_add_right h k⟩

/--
**An interaction `.error` leaf persists upward in fuel (additive form).**  A
`.done (.error err)` is absorbing under `bind`, so the longer run reaches the same
`.error err` on the same transcript.
-/
theorem executes_error_add_right
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {firstFuel : Nat} {label : Label} {state : EVMState}
    {transcript : Interaction.Transcript} {err : EVMException}
    (h :
      Interaction.Executes
        (openRunNResultWithStop stopJump program firstFuel label state)
        transcript (Except.error err))
    (restFuel : Nat) :
    Interaction.Executes
      (openRunNResultWithStop stopJump program (firstFuel + restFuel) label state)
      transcript (Except.error err) := by
  rw [openRunNResultWithStop_add]
  exact Interaction.Executes.bind_error h

/-- **An interaction `.error` leaf persists upward in fuel (`≤` form).** -/
theorem executes_error_of_le
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {m n : Nat} {label : Label} {state : EVMState}
    {transcript : Interaction.Transcript} {err : EVMException}
    (hle : m ≤ n)
    (h :
      Interaction.Executes
        (openRunNResultWithStop stopJump program m label state)
        transcript (Except.error err)) :
    Interaction.Executes
      (openRunNResultWithStop stopJump program n label state)
      transcript (Except.error err) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  exact executes_error_add_right h k

/--
**`RunSettles` from per-branch within-budget coverage.**

If every terminal branch of the `budget`-fuel run is *covered* — its exact
transcript is executed, at some fuel `m ≤ budget`, to either a proper `.stopped`
leaf or an interaction `.error` — then the `budget`-run never yields
`.ok (.exhausted …)` on any branch, i.e. `RunSettles`.

The `budget`-run's own branch fixes the transcript; the covering smaller-fuel
`.stopped`/`.error` is promoted to `budget` (`executes_stopped_of_le` /
`executes_error_of_le`) and pinned against the `budget`-run's result by the frozen
determinism lemma `executes_unique`.  A `.stopped` or `.error` result is, in
particular, not `.ok (.exhausted …)`.

This is the target-side, `StateRel`-free reduction the composite realizing
recursors invoke: the source-`.ok` branches supply the `.stopped` cover from the
child's `BoundedExecPreservesUnder`, and the source-runtime-`.error` branches
supply the `.error` cover from `BoundedRuntimeErrorExecPreservesUnder`.
-/
theorem RunSettles.of_cover
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {budget : Nat} {label : Label} {state : EVMState}
    (hCover :
      ∀ (transcript : Interaction.Transcript)
          (result : Except EVMException Control.Program.RunResult),
        Interaction.Executes
            (openRunNResultWithStop stopJump program budget label state)
            transcript result →
        (∃ (m remaining : Nat) (outcome : TypedCfg.Outcome),
            m ≤ budget ∧
            Interaction.Executes
              (openRunNResultWithStop stopJump program m label state)
              transcript
              (Except.ok (Control.Program.RunResult.stopped remaining outcome))) ∨
        (∃ (m : Nat) (err : EVMException),
            m ≤ budget ∧
            Interaction.Executes
              (openRunNResultWithStop stopJump program m label state)
              transcript (Except.error err))) :
    RunSettles program stopJump budget label state := by
  intro transcript result hExec rLabel rState
  rcases hCover transcript result hExec with
    ⟨m, remaining, outcome, hle, hStopped⟩ | ⟨m, err, hle, hError⟩
  · obtain ⟨remaining', hBudget⟩ := executes_stopped_of_le hle hStopped
    rw [Solidus.OpenRunContainment.executes_unique hExec hBudget]
    simp
  · have hBudget := executes_error_of_le hle hError
    rw [Solidus.OpenRunContainment.executes_unique hExec hBudget]
    simp

end Program
end InteractionSemantics
end TypedCfg
end EvmCompiler
