import EvmCompiler.TypedCfg.InteractionEntryRealized

/-!
# Upward reachability cap under bounded completion (Step A / item 3b, budget-slack lever)

This module supplies the **upward-monotone accumulator** step that
`InteractionEntryRealizedBounded.RealizingBoundedExecPreservesUnder.mono_budget`
explicitly leaves open (its docstring: "there is deliberately no upward-monotone
accumulator lemma: that direction is exactly the extra reachability the composite
threading must establish").

## Why this is needed (session-18 finding)

The `if` composite realizing recursor (`if_bounded_realizing`, session 17) lands
cleanly because its budget matches its child *exactly*:
`stmtBudget (.if_ cond body) = 1 + blockBudget body`, and the head is exactly one
`openStep`, so the residual `AllEntriesRealized` fuel is precisely
`blockBudget body` — the budget the child owner provides.

`switch` and `call` do **not** have this exact match.  Their `stmtBudget`s carry
*strict slack* over the taken path's child budget:
* `stmtBudget (.switch …) = 1 + (switchBodyBudget + cases.length + 1)` where
  `switchBodyBudget` is a `max` over case bodies (`InteractionStaticCost.lean:70`),
  and the matched case is reached after the entry `pop;jump` plus `k` test blocks,
  leaving residual `switchBodyBudget + cases.length - k ≥ blockBudget matchedBody`
  with the inequality generally **strict**.
* `stmtBudget (.call name) = 3 + procBodyBudget` (`InteractionStaticCost.lean:149`)
  where `procBodyBudget` is a `max` over procs; the proc body is reached after two
  pure jumps (call-site block + proc-entry adapter), leaving residual
  `1 + procBodyBudget ≥ blockBudget proc.body`, generally strict.

So the composite must produce `AllEntriesRealized cfg policy stmtBudget entry
target` while the child owner only supplies `AllEntriesRealized … blockBudget …`
at the leaf — a strictly larger fuel than provided.  `AllEntriesRealized` is
*antitone* in fuel (`AllEntriesRealized.of_le`), so the larger-fuel fact is
strictly stronger and cannot be recovered downward: this is precisely the
upward gap.

## The lever

The gap is closable because the run genuinely *completes* within the child budget
along every branch (the fragment stops at its recursive boundary): once the run
has stopped, extra fuel reaches **no** new block entries.  This file makes that
target-side fact precise and unconditional:

* `RunCompletes program stopJump B label state` — the `B`-fuel whole-program
  runner reaches a proper `.stopped` result (never `.exhausted`, never an error)
  on *every* concrete answer branch.
* `ReachesOpenStepAt.of_runCompletes` — if the `B`-run completes, then the set of
  reached block entries at **any** fuel `n` collapses to the set at `B`.  Hence
  `AllEntriesRealized.of_runCompletes` promotes a `B`-budget realization to any
  larger budget.

Everything here is target-side and `StateRel`-free; the composite threading
discharges `RunCompletes` at each leaf from the child fragment's bounded stopping
(the source coupling, done at the mutual anchor).  Additive; `peepholeBody`/public
spine UNTOUCHED.
-/

namespace EvmCompiler
namespace TypedCfg
namespace InteractionSemantics
namespace Program

open Simulation (Interaction)

/--
`RunCompletes program stopJump fuel label state` asserts that the fuel-bounded
whole-program runner, started at `(label, state)`, reaches a proper `.stopped`
result on **every** concrete answer branch — never running out of fuel
(`.exhausted`) and never raising an interaction error.

This is the target-side witness that the run has *settled* within `fuel` steps.
It is discharged at each fragment leaf from that fragment's bounded stopping.
-/
def RunCompletes (program : TypedCfg.Program)
    (stopJump : Label → EVMState → Bool) (fuel : Nat)
    (label : Label) (state : EVMState) : Prop :=
  ∀ (transcript : Interaction.Transcript)
      (result : Except EVMException Control.Program.RunResult),
    Interaction.Executes
        (openRunNResultWithStop stopJump program fuel label state)
        transcript result →
    ∃ remaining outcome,
      result = Except.ok (Control.Program.RunResult.stopped remaining outcome)

/--
**`RunCompletes` recursion constructor.**  The whole-program `(fuel + 1)`-run from
`(label, state)` completes on every branch as soon as:

* `hNoError` — the head `openStep` never raises an interaction error on any answer
  branch (a stopped run cannot begin with a failing step); and
* `hStops` — after any head jump to a *non-stopping* `(next, state')`, the residual
  `fuel`-run from there already completes (`RunCompletes … fuel next state'`).

Every other head outcome — a *stopping* jump, or a `fallthrough`/`returnDispatch`/
`halt`/`invalid` — settles the run immediately via
`afterOpenStepResultWithStop`'s `pure (.stopped …)` leaf, so no hypothesis about it
is required.  This is the exact branch-by-branch assembler the mutual anchor uses
to build `RunCompletes` for a composite fragment: `hNoError` from the fragment
executing cleanly under its realizing `StateRel`, `hStops` from the child
fragment's bounded stopping.
-/
theorem RunCompletes.succ
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {fuel : Nat} {label : Label} {state : EVMState}
    (hNoError :
      ∀ (transcript : Interaction.Transcript) (err : EVMException),
        ¬ Interaction.Executes (openStep program label state) transcript
            (Except.error err))
    (hStops :
      ∀ (transcript : Interaction.Transcript) (next : Label) (state' : EVMState),
        Interaction.Executes (openStep program label state) transcript
            (Except.ok (TypedCfg.Outcome.jump next state')) →
        stopJump next state' = false →
        RunCompletes program stopJump fuel next state') :
    RunCompletes program stopJump (fuel + 1) label state := by
  intro transcript result hExec
  rw [openRunNResultWithStop_succ_eq_bind] at hExec
  rcases Interaction.Executes.bind_cases hExec with
    ⟨err, _hResult, hErrExec⟩ | ⟨outcome, ft, rt, _hTr, hHead, hRest⟩
  · exact absurd hErrExec (hNoError transcript err)
  · cases outcome with
    | jump next state' =>
        by_cases hs : stopJump next state' = true
        · have hRest' :
              Interaction.Executes
                (Interaction.pure
                  (Control.Program.RunResult.stopped fuel
                    (TypedCfg.Outcome.jump next state'))) rt result := by
            simpa only [afterOpenStepResultWithStop, hs, if_true] using hRest
          cases hRest'
          exact ⟨fuel, _, rfl⟩
        · have hsf : stopJump next state' = false := by
            simpa using hs
          have hRest' :
              Interaction.Executes
                (openRunNResultWithStop stopJump program fuel next state')
                rt result := by
            simpa only [afterOpenStepResultWithStop, hsf, if_false] using hRest
          exact hStops ft next state' hHead hsf rt result hRest'
    | fallthrough state' =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped fuel
                  (TypedCfg.Outcome.fallthrough state'))) rt result := by
          simpa only [afterOpenStepResultWithStop] using hRest
        cases hRest'
        exact ⟨fuel, _, rfl⟩
    | returnDispatch state' =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped fuel
                  (TypedCfg.Outcome.returnDispatch state'))) rt result := by
          simpa only [afterOpenStepResultWithStop] using hRest
        cases hRest'
        exact ⟨fuel, _, rfl⟩
    | halt kind state' =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped fuel
                  (TypedCfg.Outcome.halt kind state'))) rt result := by
          simpa only [afterOpenStepResultWithStop] using hRest
        cases hRest'
        exact ⟨fuel, _, rfl⟩
    | invalid state' =>
        have hRest' :
            Interaction.Executes
              (Interaction.pure
                (Control.Program.RunResult.stopped fuel
                  (TypedCfg.Outcome.invalid state'))) rt result := by
          simpa only [afterOpenStepResultWithStop] using hRest
        cases hRest'
        exact ⟨fuel, _, rfl⟩

/--
**`RunCompletes` leaf constructor.**  A single-block fragment whose head `openStep`
never errors and whose every jump lands on a *stopping* boundary
(`stopJump = true`) completes at `fuel + 1`: the run settles at the first step on
every branch.  This is the shape the leaf fragments (`code`/`terminal`/`brk`/
`cont`/`leave`, all one block ending in a boundary jump) present to the anchor.
-/
theorem RunCompletes.of_head_stops
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {fuel : Nat} {label : Label} {state : EVMState}
    (hNoError :
      ∀ (transcript : Interaction.Transcript) (err : EVMException),
        ¬ Interaction.Executes (openStep program label state) transcript
            (Except.error err))
    (hAllStop :
      ∀ (transcript : Interaction.Transcript) (next : Label) (state' : EVMState),
        Interaction.Executes (openStep program label state) transcript
            (Except.ok (TypedCfg.Outcome.jump next state')) →
        stopJump next state' = true) :
    RunCompletes program stopJump (fuel + 1) label state :=
  RunCompletes.succ hNoError
    (fun transcript next state' hHead hsf =>
      absurd (hAllStop transcript next state' hHead) (by rw [hsf]; simp))

/--
**Upward reachability cap.**  If the `B`-fuel run from `(entry, target)` completes
on every branch (`RunCompletes … B`), then every block entry reached at *any*
fuel `n` is already reached at fuel `B`.

The proof inducts on the fuel-`n` reachability derivation, generalizing the target
budget `B` and its completion hypothesis:
* the reflexive `.start` witness is reached at any `B`;
* at a `.step` (a non-stopping jump `entry → next`), completion forces `B ≥ 1`
  (the fuel-`0` runner yields `.exhausted`, not `.stopped`); writing `B = b + 1`,
  the completion of the whole `b+1`-run restricts (via `Executes.bind_ok`
  composed with the head jump) to completion of the residual `b`-run from `next`,
  so the induction hypothesis caps the residual reachability at `b`, and the same
  `.step` re-assembles the fuel-`B` witness.
-/
theorem ReachesOpenStepAt.of_runCompletes
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {n : Nat} {entry : Label} {target : EVMState}
    {rLabel : Label} {rState : EVMState}
    (hReach : ReachesOpenStepAt program stopJump n entry target rLabel rState) :
    ∀ {B : Nat}, RunCompletes program stopJump B entry target →
      ReachesOpenStepAt program stopJump B entry target rLabel rState := by
  induction hReach with
  | start fuel label state =>
      intro B _
      exact .start B label state
  | @step fuel label state transcript next state' rLabel rState
        hExec hStop _hRest ih =>
      intro B hComplete
      cases B with
      | zero =>
          exfalso
          obtain ⟨remaining, outcome, hEq⟩ :=
            hComplete []
              (Except.ok (Control.Program.RunResult.exhausted label state))
              (by
                rw [openRunNResultWithStop_zero]
                exact Interaction.Executes.done _)
          exact absurd hEq (by simp)
      | succ b =>
          have hResidual :
              RunCompletes program stopJump b next state' := by
            intro tr2 result2 hRes2
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
            exact hComplete _ _ hFull
          exact .step hExec hStop (ih hResidual)

/--
**Upward accumulator promotion.**  Given a `B`-budget per-entry realization and the
target-side completion witness `RunCompletes … B`, every entry reached at any
larger (indeed *any*) budget `n` is realized.

This is the exact upward-monotone step the `switch`/`call`/`for` composite
recursors need to reconcile their budget slack with the child owner's
`blockBudget`-level accumulator: supply the child accumulator at `blockBudget`,
supply `RunCompletes` at the leaf from the child fragment's bounded stopping, and
promote to the composite's full `stmtBudget`.
-/
theorem AllEntriesRealized.of_runCompletes
    {program : TypedCfg.Program} {stopJump : Label → EVMState → Bool}
    {B n : Nat} {entry : Label} {target : EVMState}
    {realized : Label → EVMState → Prop}
    (hComplete : RunCompletes program stopJump B entry target)
    (hAll : AllEntriesRealized program stopJump B entry target realized) :
    AllEntriesRealized program stopJump n entry target realized := by
  intro label state hReach
  exact hAll label state (hReach.of_runCompletes hComplete)

end Program
end InteractionSemantics
end TypedCfg
end EvmCompiler
