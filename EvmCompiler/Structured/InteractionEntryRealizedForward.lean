import EvmCompiler.Structured.InteractionControlPreservation
import EvmCompiler.TypedCfg.InteractionEntryRealized

/-!
# The realizing forward preservation family (Step A / item 2)

This module is **item 2** of the session-11/12 green-preserving recipe for the
`swap d ; swap d → ε` peephole arm (see `TypedCfg/PEEPHOLE_PROGRESS.md`).

Session 12 landed the *target-side* substrate in
`TypedCfg/InteractionEntryRealized.lean`: a step-indexed block-entry
reachability relation (`ReachesOpenStepAt`), a predicate `AllEntriesRealized`
quantifying an abstract `realized : Label → EVMState → Prop` over every visited
entry, and the leaf-discharge rule `AllEntriesRealized.of_first_jump_stops`.

This file couples that accumulator to the existing single-`targetFuel`
`ForwardPreservesUnder` outcome leg (session-12 fuel-coupling decision: attach at
the FORWARD/uniform level where the target budget is one value, NOT at the
existential-fuel `ExecPreservesUnder` level).  It provides, all **additive** — the
existing `ForwardPreservesUnder`/`ExecPreservesUnder` abbrevs and every existing
lemma statement are untouched:

* `Simulation.Interaction.Rel.executes_right` — the backward companion of the
  package's `Rel.executes`: a concrete execution of the RIGHT interaction is
  mirrored, along the same transcript, by an execution of the LEFT into a
  `doneRel`-related outcome.  This is the bridge that turns an `openStep`
  execution into the source-side relation the fragment contract's `stops` field
  constrains.
* `RealizingForwardPreservesUnder` — the parallel family: `ForwardPreservesUnder`
  conjoined with `AllEntriesRealized` at the same `targetFuel`.
* `RealizingForwardPreservesUnder.of_forward_first_jump_stops` — the generic
  single-block leaf constructor: given the forward outcome leg, the start-entry
  realization, and that every first-step jump out of the entry lands on a
  policy-stopping target, the whole family holds.  This is the exact shape the
  leaf `code`/`terminal`/`brk`/`cont`/`leave` realizing cases discharge (their
  fragments each compile to ONE block ending in a `.jump` the fragment's stop
  policy halts on).
-/

universe u1 v1 u2 v2

namespace EvmCompiler

namespace Simulation
namespace Interaction
namespace Rel

/--
Backward companion of `Rel.executes`.

The interaction-tree simulation `Rel` aligns queries on both sides (the
`request` constructor demands the same query and relates all answer branches), so
a concrete execution of the RIGHT interaction with some transcript is mirrored,
along the SAME transcript, by an execution of the LEFT interaction whose outcome
is `doneRel`-related.  This is exactly `Rel.executes` with the roles swapped and
the induction on the right execution instead of the left.
-/
theorem executes_right
    {Error₁ : Type u1} {Result₁ : Type v1}
    {Error₂ : Type u2} {Result₂ : Type v2}
    {doneRel :
      Except Error₁ Result₁ → Except Error₂ Result₂ → Prop}
    {left : Interaction Error₁ Result₁}
    {right : Interaction Error₂ Result₂}
    {transcript : Transcript}
    {rightOutcome : Except Error₂ Result₂}
    (hRel : Rel doneRel left right)
    (hExec : Executes right transcript rightOutcome) :
    ∃ leftOutcome,
      Executes left transcript leftOutcome ∧
        doneRel leftOutcome rightOutcome := by
  induction hExec generalizing left with
  | done outcome =>
      cases hRel with
      | done hDone => exact ⟨_, Executes.done _, hDone⟩
  | request answer tail ih =>
      cases hRel with
      | request hResume =>
          obtain ⟨leftOutcome, hLeft, hDone⟩ := ih (hResume answer)
          exact ⟨leftOutcome, Executes.request answer hLeft, hDone⟩

end Rel
end Interaction
end Simulation

namespace Structured
namespace InteractionControlPreservation
namespace OpenOutcome

/--
The realizing forward family.

The first conjunct is the existing single-`targetFuel` forward outcome leg
(`ForwardPreservesUnder`, unchanged).  The second is the additive target-side
accumulator: from any `StateRel`-related target, every block entry the
fuel-bounded open run visits satisfies the abstract per-entry predicate
`realized`.

`realized` stays abstract at this layer.  The peephole spine instantiates it with
the source-realization witness
`fun label state => ∃ source tokens block, cfg.findBlock? label = some block ∧
  StateRel source tokens state ∧ SourceFrameFits block.input state.evm.stack.length`,
from which the swap depth guard is discharged (sessions 8/9).
-/
def RealizingForwardPreservesUnder
    (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (regularExit : RegularExit)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome)
    (targetFuel : Nat) (policy : StopPolicy)
    (realized : Assembly.Label → EVMState → Prop) : Prop :=
  ForwardPreservesUnder result cfg entry ctx regular regularExit
      source tokens sourceRun targetFuel policy ∧
    (∀ target,
      TypedCfgPreservation.StateRel source tokens target →
        TypedCfg.InteractionSemantics.Program.AllEntriesRealized
          cfg policy targetFuel entry target realized)

namespace RealizingForwardPreservesUnder

/--
The forward outcome leg of the realizing family (first projection).
-/
theorem forward
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context} {regularExit : RegularExit}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}
    (h :
      RealizingForwardPreservesUnder result cfg entry ctx regular regularExit
        source tokens sourceRun targetFuel policy realized) :
    ForwardPreservesUnder result cfg entry ctx regular regularExit
      source tokens sourceRun targetFuel policy :=
  h.1

/--
The per-entry realization accumulator of the realizing family (second
projection).
-/
theorem allEntriesRealized
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context} {regularExit : RegularExit}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetFuel : Nat} {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}
    (h :
      RealizingForwardPreservesUnder result cfg entry ctx regular regularExit
        source tokens sourceRun targetFuel policy realized)
    {target : EVMState}
    (hStateRel : TypedCfgPreservation.StateRel source tokens target) :
    TypedCfg.InteractionSemantics.Program.AllEntriesRealized
      cfg policy targetFuel entry target realized :=
  h.2 target hStateRel

/--
Generic single-block leaf constructor at target budget `fuel + 1`.

Given
* the forward outcome leg,
* the start-entry realization (`realized entry target` for every related target),
* and that every concrete first-step jump out of the entry lands on a
  policy-stopping target,

the realizing family holds: the run visits no entry beyond the start (every first
jump stops), so the accumulator reduces to the single start-entry fact via
`AllEntriesRealized.of_first_jump_stops`.

This is the exact discharge shape for the leaf `code` / `terminal` / `brk` /
`cont` / `leave` realizing cases: each compiles to one block whose terminator is
a `.jump` the fragment's stop policy halts on, and whose `StmtContract.stops`
supplies the policy-stops fact from the `openStep` relation.
-/
theorem of_forward_first_jump_stops
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context} {regularExit : RegularExit}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {fuel : Nat} {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}
    (hForward :
      ForwardPreservesUnder result cfg entry ctx regular regularExit
        source tokens sourceRun (fuel + 1) policy)
    (hRealized :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          realized entry target)
    (hStops :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          ∀ transcript next state',
            Simulation.Interaction.Executes
                (TypedCfg.InteractionSemantics.Program.openStep
                  cfg entry target)
                transcript
                (Except.ok (TypedCfg.Outcome.jump next state')) →
              policy next state' = true) :
    RealizingForwardPreservesUnder result cfg entry ctx regular regularExit
      source tokens sourceRun (fuel + 1) policy realized := by
  refine ⟨hForward, ?_⟩
  intro target hStateRel
  refine
    TypedCfg.InteractionSemantics.Program.AllEntriesRealized.of_first_jump_stops
      (hRealized target hStateRel) ?_
  intro transcript next state' hExec
  exact hStops target hStateRel transcript next state' hExec

end RealizingForwardPreservesUnder

end OpenOutcome
end InteractionControlPreservation
end Structured
end EvmCompiler
