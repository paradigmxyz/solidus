import EvmCompiler.TypedCfg.InteractionSemantics

/-!
# Block-entry realization along an open whole-program run (target-side substrate)

This module is **Step A / item 1** of the session-11 green-preserving recipe for
the `swap d ; swap d → ε` peephole arm (see `TypedCfg/PEEPHOLE_PROGRESS.md`).

The swap arm's body reduction (`openRunBody_swap_swap_congr`, landed session 6)
needs the runtime depth guard `d + 2 ≤ state.stack.length` at **every block
entry** the whole-program open runner `openRunNResultWithStop` steps through.
Sessions 8/9 landed the per-entry discharge
(`stackRealizes_of_stateRel_of_{token_last_of_tokens_cons,returnTokenDepth?_eq_none}`)
*given* a source `StateRel`/`SourceFrameFits` witness at that entry.  What is
missing is a way to *name* "the entries a run visits" so that a realizing
predicate can be quantified over them.

That naming is genuinely non-trivial because `openStep` (`InteractionSemantics.
lean:759`) is an **interaction tree** in `Simulation.Interaction EVMException`,
not a linear trace: a single step's `.jump next state'` leaf is only well-defined
*along a concrete answer branch* (an `Executes` transcript).  So "visited block
entry" must be phrased step-indexed over a concrete branch, not as a plain fuel
fold over states (session-11, Finding 2).

This file provides exactly that, **target-side only** (no source coupling, no
`StateRel`): a step-indexed reachability relation `ReachesOpenStepAt` over the
`openRunNResultWithStop` recursion, and a predicate `AllEntriesRealized`
quantifying an arbitrary `realized : Label → EVMState → Prop` over every reached
entry, with the two structural facts the recipe calls for (start is reached;
reachability is closed under one non-stopping `openStep .jump` leaf) plus the
fuel-0 / successor introduction lemmas a later `*_exec_realizing` layer consumes.

The `realized` predicate is left abstract here precisely so this layer stays
self-contained and green; the source instantiation
(`∃ source tokens block, findBlock? label = some block ∧ StateRel … ∧
SourceFrameFits …`) is supplied one layer up, where the Structured→cfg simulation
witness is in scope.
-/

namespace EvmCompiler
namespace TypedCfg
namespace InteractionSemantics
namespace Program

open Simulation (Interaction)

/--
`ReachesOpenStepAt program stopJump fuel entry target rLabel rState` holds when,
starting the fuel-bounded open whole-program run at block `entry` in state
`target` with fuel `fuel`, control reaches a block entry `(rLabel, rState)` along
some concrete answer branch, before the run stops.

The relation is step-indexed over the `openRunNResultWithStop` recursion
(`InteractionSemantics.lean:863`).  Each recursive `.step` records that one
`openStep` produced a `.jump next state'` leaf along a concrete `Executes`
transcript and that the stop policy did **not** fire there, so control genuinely
proceeded to `next`.  A stopping jump, a non-jump outcome, or fuel exhaustion
does not extend reachability — only the starting entry is reached in those cases.
-/
inductive ReachesOpenStepAt (program : TypedCfg.Program)
    (stopJump : Label → EVMState → Bool) :
    Nat → Label → EVMState → Label → EVMState → Prop where
  /-- Every run reaches its own starting entry. -/
  | start (fuel : Nat) (label : Label) (state : EVMState) :
      ReachesOpenStepAt program stopJump fuel label state label state
  /-- If one open step jumps (along a concrete branch) to a non-stopping `next`,
  every entry reachable from `next` with the remaining fuel is reachable from the
  starting entry. -/
  | step {fuel : Nat} {label : Label} {state : EVMState}
      {transcript : Interaction.Transcript}
      {next : Label} {state' : EVMState}
      {rLabel : Label} {rState : EVMState}
      (hExec : Interaction.Executes (openStep program label state)
        transcript (Except.ok (TypedCfg.Outcome.jump next state')))
      (hStop : stopJump next state' = false)
      (hRest : ReachesOpenStepAt program stopJump fuel next state' rLabel rState) :
      ReachesOpenStepAt program stopJump (fuel + 1) label state rLabel rState

namespace ReachesOpenStepAt

/-- Structural fact (i): the starting entry is always reached. -/
theorem reaches_start (program : TypedCfg.Program)
    (stopJump : Label → EVMState → Bool) (fuel : Nat)
    (entry : Label) (target : EVMState) :
    ReachesOpenStepAt program stopJump fuel entry target entry target :=
  .start fuel entry target

/-- Inversion at fuel `0`: no `openStep` can fire, so the only reached entry is
the starting one. -/
theorem eq_of_zero {program : TypedCfg.Program}
    {stopJump : Label → EVMState → Bool}
    {entry : Label} {target : EVMState} {rLabel : Label} {rState : EVMState}
    (h : ReachesOpenStepAt program stopJump 0 entry target rLabel rState) :
    rLabel = entry ∧ rState = target := by
  cases h with
  | start => exact ⟨rfl, rfl⟩

end ReachesOpenStepAt

/--
`AllEntriesRealized program stopJump fuel entry target realized` asserts that
every block entry visited by the fuel-bounded open run starting at `(entry,
target)` satisfies the (target-side) predicate `realized`.

`realized` is abstract at this layer.  The peephole spine will instantiate it
with the source-realization witness
`fun label state => ∃ source tokens block, program.findBlock? label = some block ∧
  StateRel source tokens state ∧ SourceFrameFits block.input state.evm.stack.length`,
from which the swap depth guard is discharged (sessions 8/9).
-/
def AllEntriesRealized (program : TypedCfg.Program)
    (stopJump : Label → EVMState → Bool) (fuel : Nat)
    (entry : Label) (target : EVMState)
    (realized : Label → EVMState → Prop) : Prop :=
  ∀ label state,
    ReachesOpenStepAt program stopJump fuel entry target label state →
    realized label state

namespace AllEntriesRealized

/-- The realizing predicate holds at the starting entry (specialize the
quantifier to the reflexive witness). -/
theorem realized_start {program : TypedCfg.Program}
    {stopJump : Label → EVMState → Bool} {fuel : Nat}
    {entry : Label} {target : EVMState} {realized : Label → EVMState → Prop}
    (h : AllEntriesRealized program stopJump fuel entry target realized) :
    realized entry target :=
  h entry target (ReachesOpenStepAt.reaches_start program stopJump fuel entry target)

/-- At fuel `0` the only reached entry is the start, so realizing the start
entry is all that is required. -/
theorem of_zero {program : TypedCfg.Program}
    {stopJump : Label → EVMState → Bool}
    {entry : Label} {target : EVMState} {realized : Label → EVMState → Prop}
    (hHere : realized entry target) :
    AllEntriesRealized program stopJump 0 entry target realized := by
  intro label state hReach
  obtain ⟨rfl, rfl⟩ := ReachesOpenStepAt.eq_of_zero hReach
  exact hHere

/--
Structural fact (ii), packaged as the successor-introduction rule: to realize
every entry of a `fuel + 1` run it suffices to realize the starting entry and,
for each concrete non-stopping first-step jump to `(next, state')`, realize every
entry of the residual `fuel`-run from there.  This is exactly the shape the
`*_exec_realizing` recursion relays: the outcome leg reuses the existing (green)
`*_exec`, and this lemma discharges the added accumulator leg one recursive call
at a time.
-/
theorem of_succ {program : TypedCfg.Program}
    {stopJump : Label → EVMState → Bool} {fuel : Nat}
    {entry : Label} {target : EVMState} {realized : Label → EVMState → Prop}
    (hHere : realized entry target)
    (hNext : ∀ (transcript : Interaction.Transcript) (next : Label)
        (state' : EVMState),
      Interaction.Executes (openStep program entry target) transcript
        (Except.ok (TypedCfg.Outcome.jump next state')) →
      stopJump next state' = false →
      AllEntriesRealized program stopJump fuel next state' realized) :
    AllEntriesRealized program stopJump (fuel + 1) entry target realized := by
  intro label state hReach
  cases hReach with
  | start => exact hHere
  | step hExec hStop hRest =>
      exact hNext _ _ _ hExec hStop _ _ hRest

/--
Leaf-discharge rule.  When every concrete first-step jump out of the starting
entry lands on a **stopping** target (`stopJump = true`) — the situation for a
single-block fragment whose terminator jumps straight to a recursive boundary
(`code` / `terminal` / `brk` / `cont` / `leave`, all of which compile to one
block ending in a `.jump` that the fragment's stop policy halts on) — the run
visits no entry beyond the start, so realizing the start entry realizes them all.

This is the target-side lemma the leaf `*_exec_realizing` cases invoke: it turns
the added accumulator obligation into the single fact `realized entry target`,
which the source contract (`StateRel` + `SourceFrameFits`) already supplies.
-/
theorem of_first_jump_stops {program : TypedCfg.Program}
    {stopJump : Label → EVMState → Bool} {fuel : Nat}
    {entry : Label} {target : EVMState} {realized : Label → EVMState → Prop}
    (hHere : realized entry target)
    (hStops : ∀ (transcript : Interaction.Transcript) (next : Label)
        (state' : EVMState),
      Interaction.Executes (openStep program entry target) transcript
        (Except.ok (TypedCfg.Outcome.jump next state')) →
      stopJump next state' = true) :
    AllEntriesRealized program stopJump (fuel + 1) entry target realized := by
  refine of_succ hHere ?_
  intro transcript next state' hExec hStop
  exact absurd (hStops transcript next state' hExec) (by rw [hStop]; simp)

end AllEntriesRealized

end Program
end InteractionSemantics
end TypedCfg
end EvmCompiler
