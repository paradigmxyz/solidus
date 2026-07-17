import EvmCompiler.Structured.InteractionEntryRealizedForward

/-!
# The bounded realizing preservation family (Step A / item 3a)

This module is **item 3a** of the session-11/12/13 green-preserving recipe for the
`swap d ; swap d → ε` peephole arm (see `TypedCfg/PEEPHOLE_PROGRESS.md`).

Session 13 landed the single-`targetFuel` `RealizingForwardPreservesUnder` family
and its five single-block leaf constructors.  As session 13 pinned, that family
cannot host the composite recursors (`if`/`switch`/`for`/`call`): the composite
`*_exec` theorems produce `ExecPreservesUnder`, whose `targetFuel` is
**existential per (transcript, sourceOutcome)** — there is no single `targetFuel`
to name for an `AllEntriesRealized` conjunct.  The composites instead reduce
internally to `BoundedExecPreservesUnder`, which carries a single source-owned
`targetBudget` ceiling with `targetFuel ≤ targetBudget`.

This file defines the parallel realizing family at exactly that bounded level:
`RealizingBoundedExecPreservesUnder` conjoins the existing (unchanged)
`BoundedExecPreservesUnder` outcome leg with an accumulator
`∀ tf ≤ targetBudget, AllEntriesRealized cfg policy tf entry target realized`.
The `∀ tf ≤ budget` shape is what lets the existential run — which uses *some*
fuel `≤ budget` — carry a per-entry realization: whichever `targetFuel` the run
picks, its reachable-entry set is covered.  By the fuel antitonicity landed this
session (`AllEntriesRealized.of_le`), that `∀`-form is equivalent to the single
fact `AllEntriesRealized … targetBudget …`; the `mk` builder below assembles the
`∀`-form from the budget-level fact.

Everything here is **additive**: no existing abbrev or lemma statement is touched.
The composite `*_forward_realizing`/`*_bounded_realizing` recursors that populate
this family remain the deferred Step-A bulk (documented in `PEEPHOLE_PROGRESS.md`);
this file is the vehicle they will produce.
-/

namespace EvmCompiler

namespace Structured
namespace InteractionControlPreservation
namespace OpenOutcome

open TypedCfg.InteractionSemantics.Program (AllEntriesRealized)

/--
The bounded realizing family.

* First conjunct: the existing source-bounded successful-execution leg
  (`BoundedExecPreservesUnder`, unchanged) — for every `StateRel`-related target
  and every successful source outcome, the canonical open runner reaches a
  matching stopped outcome at some `targetFuel ≤ targetBudget`.
* Second conjunct: the additive target-side accumulator — for every
  `StateRel`-related target and every `tf ≤ targetBudget`, every block entry the
  `tf`-fuel open run visits satisfies the abstract per-entry predicate
  `realized`.

`realized` stays abstract at this layer (as in `InteractionEntryRealized` /
`RealizingForwardPreservesUnder`).  The peephole spine instantiates it with the
source-realization witness
`fun label state => ∃ source tokens block, cfg.findBlock? label = some block ∧
  StateRel source tokens state ∧ SourceFrameFits block.input state.evm.stack.length`,
from which the swap depth guard is discharged (sessions 8/9).
-/
def RealizingBoundedExecPreservesUnder
    (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) (entry : Assembly.Label)
    (ctx : TypedCfgCompiler.Context) (regular : Assembly.Label)
    (source : RunState) (tokens : List Word)
    (sourceRun :
      Simulation.Interaction EVMException Structured.Outcome)
    (targetBudget : Nat) (policy : StopPolicy)
    (realized : Assembly.Label → EVMState → Prop) : Prop :=
  BoundedExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetBudget policy ∧
    (∀ target,
      TypedCfgPreservation.StateRel source tokens target →
        ∀ tf, tf ≤ targetBudget →
          AllEntriesRealized cfg policy tf entry target realized)

namespace RealizingBoundedExecPreservesUnder

variable
    {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {entry regular : Assembly.Label}
    {ctx : TypedCfgCompiler.Context}
    {source : RunState} {tokens : List Word}
    {sourceRun :
      Simulation.Interaction EVMException Structured.Outcome}
    {targetBudget : Nat} {policy : StopPolicy}
    {realized : Assembly.Label → EVMState → Prop}

/-- The source-bounded execution outcome leg (first projection). -/
theorem bounded
    (h :
      RealizingBoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetBudget policy realized) :
    BoundedExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetBudget policy :=
  h.1

/-- Forget both the source-owned ceiling and the accumulator, recovering the
existing pass-wide `ExecPreservesUnder` interface (via
`BoundedExecPreservesUnder.exec`).  This is how a realizing composite feeds the
unchanged spine while retaining its accumulator for the peephole leg. -/
theorem exec
    (h :
      RealizingBoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetBudget policy realized) :
    ExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun policy :=
  BoundedExecPreservesUnder.exec h.1

/-- The per-entry realization accumulator (second projection), specialized to a
concrete fuel `tf ≤ targetBudget`. -/
theorem allEntriesRealized
    (h :
      RealizingBoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetBudget policy realized)
    {target : EVMState}
    (hStateRel : TypedCfgPreservation.StateRel source tokens target)
    {tf : Nat} (hle : tf ≤ targetBudget) :
    AllEntriesRealized cfg policy tf entry target realized :=
  h.2 target hStateRel tf hle

/--
Builder from a **budget-level** accumulator.

To supply the whole `∀ tf ≤ targetBudget` conjunct it suffices to realize every
entry of the `targetBudget`-fuel run (the largest one): by fuel antitonicity
(`AllEntriesRealized.of_le`) that covers every shorter `tf ≤ targetBudget`.  This
is the shape the composite recursors will discharge — they establish
realization at the single canonical budget and this lemma spreads it downward.
-/
theorem mk
    (hBounded :
      BoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun targetBudget policy)
    (hAll :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          AllEntriesRealized cfg policy targetBudget entry target realized) :
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun targetBudget policy realized :=
  ⟨hBounded, fun target hStateRel tf hle =>
    AllEntriesRealized.of_le hle (hAll target hStateRel)⟩

/--
Raising the source-owned ceiling.

The outcome leg survives a larger budget via `BoundedExecPreservesUnder.mono_budget`.
The accumulator, however, is genuinely **stronger** at a larger budget (a longer
run visits a superset of entries), so it must be supplied afresh at the larger
budget — this lemma therefore takes the larger-budget accumulator as a hypothesis
rather than deriving it.  (There is deliberately no upward-monotone accumulator
lemma: that direction is exactly the extra reachability the composite threading
must establish.) -/
theorem mono_budget
    {smaller larger : Nat}
    (h :
      RealizingBoundedExecPreservesUnder result cfg entry ctx regular
        source tokens sourceRun smaller policy realized)
    (hLe : smaller ≤ larger)
    (hAll :
      ∀ target,
        TypedCfgPreservation.StateRel source tokens target →
          AllEntriesRealized cfg policy larger entry target realized) :
    RealizingBoundedExecPreservesUnder result cfg entry ctx regular
      source tokens sourceRun larger policy realized :=
  mk (BoundedExecPreservesUnder.mono_budget h.1 hLe) hAll

end RealizingBoundedExecPreservesUnder

end OpenOutcome
end InteractionControlPreservation
end Structured
end EvmCompiler
