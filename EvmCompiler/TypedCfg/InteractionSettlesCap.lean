import EvmCompiler.TypedCfg.InteractionReachesCap

/-!
# Upward reachability cap under bounded *settling* (Step A / item 3b, the `hNoError`-free lever)

This module supplies the same upward-monotone accumulator step as
`InteractionReachesCap` (`AllEntriesRealized.of_runCompletes`), but built on a
**strictly weaker** completion witness that drops the source-coupled
interpreter-totality obligation the whole tower had been blocked on.

## The finding (session 21)

`RunCompletes` (session 18) demands that the fuel-bounded runner reach a proper
`.ok (.stopped …)` on *every* answer branch — i.e. never `.exhausted` **and never
an interaction `.error`**.  Its recursion constructor `RunCompletes.succ`
therefore carries a hypothesis `hNoError` ("the head `openStep` never
`Executes … (.error e)`").  Session 20 re-scoped `hNoError` as a source-block
*interpreter-totality* theorem and identified it as "the real remaining bulk".

A close reading of the sole consumer of the completion witness —
`ReachesOpenStepAt.of_runCompletes` (and hence `AllEntriesRealized.of_runCompletes`)
— shows the `.stopped`/no-error strength is **never used**.  The cap proof uses
the witness only to rule out `.exhausted`:
* at `B = 0` it derives a contradiction from the fuel-`0` runner yielding
  `.exhausted`;
* at the `.step` case it merely needs the residual run not to exhaust.

So the accumulator promotion needs only:

* **`RunSettles program stopJump fuel label state`** — the fuel-bounded runner never
  yields `.ok (.exhausted …)` on any branch (an interaction `.error` is *allowed*).

Crucially, `RunSettles.succ` needs **no** `hNoError`: when the head `openStep`
errors, the whole run is `.error`, which is trivially *not* `.exhausted`.  The
error branches — genuine EVM `StaticModeViolation`/underflow etc. that
`callStep`/`createStep` raise as `.done (.error …)`, and which are *not* ruled out
by well-typedness — are absorbed for free instead of having to be proved absent.
This eliminates the interpreter-totality obligation from the composite promotion
path entirely: a branch that genuinely errors reaches *fewer* block entries, so it
never threatens the per-entry realization accumulator.

Everything here is target-side and `StateRel`-free.  Additive; `peepholeBody`/
public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace TypedCfg
namespace InteractionSemantics
namespace Program

open Simulation (Interaction)

/--
`RunSettles program stopJump fuel label state` asserts that the fuel-bounded
whole-program runner, started at `(label, state)`, never yields
`.ok (.exhausted …)` on any concrete answer branch.

This is strictly weaker than `RunCompletes`: an interaction `.error` (a genuine
runtime fault such as `StaticModeViolation` or a structural exception) is *not*
excluded — only fuel exhaustion is.  It is exactly the witness the upward
reachability cap needs, and — unlike `RunCompletes` — its recursion constructor
carries no source-coupled `hNoError` obligation.
-/
def RunSettles (program : TypedCfg.Program)
    (stopJump : Label → EVMState → Bool) (fuel : Nat)
    (label : Label) (state : EVMState) : Prop :=
  ∀ (transcript : Interaction.Transcript)
      (result : Except EVMException Control.Program.RunResult),
    Interaction.Executes
        (openRunNResultWithStop stopJump program fuel label state)
        transcript result →
    ∀ (rLabel : Label) (rState : EVMState),
      result ≠ Except.ok (Control.Program.RunResult.exhausted rLabel rState)

/--
**`RunSettles` recursion constructor.**  The whole-program `(fuel + 1)`-run from
`(label, state)` settles on every branch as soon as, after any head jump to a
*non-stopping* `(next, state')`, the residual `fuel`-run from there already settles
(`hStops`).

Unlike `RunCompletes.succ`, there is **no** `hNoError` hypothesis: if the head
`openStep` errors, the whole run is `.error err`, which is trivially not
`.ok (.exhausted …)`.  Every non-jump / stopping-jump head outcome settles
immediately at `.ok (.stopped …)`.
-/
theorem RunSettles.succ
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {fuel : Nat} {label : Label} {state : EVMState}
    (hStops :
      ∀ (transcript : Interaction.Transcript) (next : Label) (state' : EVMState),
        Interaction.Executes (openStep program label state) transcript
            (Except.ok (TypedCfg.Outcome.jump next state')) →
        stopJump next state' = false →
        RunSettles program stopJump fuel next state') :
    RunSettles program stopJump (fuel + 1) label state := by
  intro transcript result hExec rLabel rState
  rw [openRunNResultWithStop_succ_eq_bind] at hExec
  rcases Interaction.Executes.bind_cases hExec with
    ⟨err, hResult, _hErrExec⟩ | ⟨outcome, ft, rt, _hTr, hHead, hRest⟩
  · rw [hResult]; simp
  · cases outcome with
    | jump next state' =>
        by_cases hs : stopJump next state' = true
        · have hRest' :
              Interaction.Executes
                (Interaction.pure
                  (Control.Program.RunResult.stopped fuel
                    (TypedCfg.Outcome.jump next state'))) rt result := by
            simpa only [afterOpenStepResultWithStop, hs, if_true] using hRest
          cases hRest'; simp
        · have hsf : stopJump next state' = false := by simpa using hs
          have hRest' :
              Interaction.Executes
                (openRunNResultWithStop stopJump program fuel next state')
                rt result := by
            simpa only [afterOpenStepResultWithStop, hsf, if_false] using hRest
          exact hStops ft next state' hHead hsf rt result hRest' rLabel rState
    | fallthrough state' =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped fuel
                  (TypedCfg.Outcome.fallthrough state'))) rt result := by
          simpa only [afterOpenStepResultWithStop] using hRest
        cases hRest'; simp
    | returnDispatch state' =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped fuel
                  (TypedCfg.Outcome.returnDispatch state'))) rt result := by
          simpa only [afterOpenStepResultWithStop] using hRest
        cases hRest'; simp
    | halt kind state' =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped fuel
                  (TypedCfg.Outcome.halt kind state'))) rt result := by
          simpa only [afterOpenStepResultWithStop] using hRest
        cases hRest'; simp
    | invalid state' =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped fuel
                  (TypedCfg.Outcome.invalid state'))) rt result := by
          simpa only [afterOpenStepResultWithStop] using hRest
        cases hRest'; simp

/--
**`RunSettles` leaf constructor.**  A single-block fragment whose every jump lands
on a *stopping* boundary settles at `fuel + 1`, on every branch — including the
branches where the block's `openStep` errors.  Unlike `RunCompletes.of_head_stops`,
no `hNoError` is required.
-/
theorem RunSettles.of_head_stops
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {fuel : Nat} {label : Label} {state : EVMState}
    (hAllStop :
      ∀ (transcript : Interaction.Transcript) (next : Label) (state' : EVMState),
        Interaction.Executes (openStep program label state) transcript
            (Except.ok (TypedCfg.Outcome.jump next state')) →
        stopJump next state' = true) :
    RunSettles program stopJump (fuel + 1) label state :=
  RunSettles.succ
    (fun transcript next state' hHead hsf =>
      absurd (hAllStop transcript next state' hHead) (by rw [hsf]; simp))

/--
**`RunSettles` is monotone upward in fuel (additive form).**  Mirrors
`RunCompletes.add_right`: a run that settles within `firstFuel` steps still settles
with any extra fuel appended.  The first run never exhausts (so its result is
`.stopped`, the only other `RunResult`), and the continuation of a stopped result
is the pure `.stopped (remaining + restFuel …)` leaf.
-/
theorem RunSettles.add_right
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {firstFuel : Nat} {label : Label} {state : EVMState}
    (h : RunSettles program stopJump firstFuel label state)
    (restFuel : Nat) :
    RunSettles program stopJump (firstFuel + restFuel) label state := by
  intro transcript result hExec rLabel rState
  rw [openRunNResultWithStop_add] at hExec
  rcases Interaction.Executes.bind_cases hExec with
    ⟨err, hResult, _hErrExec⟩ | ⟨value, ft, rt, _hTr, hFirst, hRest⟩
  · rw [hResult]; simp
  · cases hval : value with
    | exhausted rl' rs' =>
        exact absurd
          (show Except.ok value
              = Except.ok (Control.Program.RunResult.exhausted rl' rs') by rw [hval])
          (h ft (Except.ok value) hFirst rl' rs')
    | stopped remaining outcome =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped (remaining + restFuel) outcome))
              rt result := by
          simpa only [hval, continueOpenRunNResultWithStop] using hRest
        cases hRest'; simp

/-- **`RunSettles` is monotone upward in fuel (`≤` form).** -/
theorem RunSettles.of_le
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {m n : Nat} {label : Label} {state : EVMState}
    (h : RunSettles program stopJump m label state)
    (hle : m ≤ n) :
    RunSettles program stopJump n label state := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  exact h.add_right k

/--
**Every `RunCompletes` is a `RunSettles`.**  The stronger completion witness
implies the weaker one, so any `RunCompletes` already discharged (e.g. at the
`if`-composite leaf) feeds the `RunSettles`-based cap unchanged.
-/
theorem RunSettles.of_runCompletes
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {fuel : Nat} {label : Label} {state : EVMState}
    (h : RunCompletes program stopJump fuel label state) :
    RunSettles program stopJump fuel label state := by
  intro transcript result hExec rLabel rState
  obtain ⟨remaining, outcome, hEq⟩ := h transcript result hExec
  rw [hEq]; simp

/--
**Upward reachability cap under settling.**  If the `B`-fuel run from
`(entry, target)` settles on every branch (`RunSettles … B`), then every block
entry reached at *any* fuel `n` is already reached at fuel `B`.

Verbatim the proof of `ReachesOpenStepAt.of_runCompletes`, but discharging the
`.exhausted` obstructions from `RunSettles` (never-exhausted) instead of
`RunCompletes` (reaches-stopped).  The `.stopped`/no-error strength was never used.
-/
theorem ReachesOpenStepAt.of_runSettles
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {n : Nat} {entry : Label} {target : EVMState}
    {rLabel : Label} {rState : EVMState}
    (hReach : ReachesOpenStepAt program stopJump n entry target rLabel rState) :
    ∀ {B : Nat}, RunSettles program stopJump B entry target →
      ReachesOpenStepAt program stopJump B entry target rLabel rState := by
  induction hReach with
  | start fuel label state =>
      intro B _
      exact .start B label state
  | @step fuel label state transcript next state' rLabel rState
        hExec hStop _hRest ih =>
      intro B hSettle
      cases B with
      | zero =>
          exfalso
          refine hSettle []
            (Except.ok (Control.Program.RunResult.exhausted label state))
            (by
              rw [openRunNResultWithStop_zero]
              exact Interaction.Executes.done _)
            label state rfl
      | succ b =>
          have hResidual :
              RunSettles program stopJump b next state' := by
            intro tr2 result2 hRes2 rl2 rs2
            have hRes2' :
                Interaction.Executes
                  (afterOpenStepResultWithStop stopJump program b
                    (TypedCfg.Outcome.jump next state'))
                  tr2 result2 := by
              simpa [afterOpenStepResultWithStop, hStop] using hRes2
            have hFull :
                Interaction.Executes
                  (openRunNResultWithStop stopJump program (b + 1) label state)
                  (transcript ++ tr2) result2 := by
              rw [openRunNResultWithStop_succ_eq_bind]
              exact Interaction.Executes.bind_ok hExec hRes2'
            exact hSettle _ _ hFull rl2 rs2
          exact .step hExec hStop (ih hResidual)

/--
**Upward accumulator promotion under settling.**  Given a `B`-budget per-entry
realization and the target-side settling witness `RunSettles … B`, every entry
reached at any budget `n` is realized.

This is the `hNoError`-free replacement for `AllEntriesRealized.of_runCompletes`:
the `switch`/`call`/`for` composites promote the child owner's `blockBudget`-level
accumulator up to the composite's larger `stmtBudget` using only that the child run
does not *exhaust* its budget — no interpreter-totality theorem required.
-/
theorem AllEntriesRealized.of_runSettles
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {B n : Nat} {entry : Label} {target : EVMState}
    {realized : Label → EVMState → Prop}
    (hSettle : RunSettles program stopJump B entry target)
    (hAll : AllEntriesRealized program stopJump B entry target realized) :
    AllEntriesRealized program stopJump n entry target realized := by
  intro label state hReach
  exact hAll label state (hReach.of_runSettles hSettle)

end Program
end InteractionSemantics
end TypedCfg
end EvmCompiler
