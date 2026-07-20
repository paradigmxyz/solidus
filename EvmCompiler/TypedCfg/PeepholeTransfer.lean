import EvmCompiler.TypedCfg.PeepholeFuel
import EvmCompiler.TypedCfg.InteractionPrefixPreservation

/-!
# `SameRuntimeData`-stability transfer lemmas for the peephole splice

The compile-spine splice couples the SOURCE-side facts (about `openRunNPrefix cfg`
/ `openRunN cfg`) to the ASSEMBLY preservation keyed on the PEEPHOLED certificate
(`(peepholeProgram cfg).compileCertified?`).  The bridge is the whole-program
open congruence (the source-threaded `openRunN_peephole_congr_of_source` /
`openRunNPrefix_peephole_congr_of_source`), which relates the original outcome
(LEFT) to the peepholed outcome (RIGHT) up to
`InteractionCongruence.Block.RuntimeOutcomeRel` (control label / halt kind equal,
carried state `SameRuntimeData`).  This file provides the two small
`RuntimeOutcomeRel`-stability lemmas the safety side-conditions need
(`PrefixAssemblySafe`, `AssemblySafeHalted`, `AssemblySafeFinished` read only
memory/stack, which are `SameRuntimeData`-stable), plus a single generic
target-fuel padding lemma for a fully-finished assembly `Rel` (the peepholed
program lowers to a strictly-shorter budget, so its assembly run must be padded
back up to the original conclusion budget `… * fuelBudget cfg`).
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

open Assembly (EVMState SameRuntimeData)
open InteractionSemantics
open InteractionCongruence

/-- `PrefixAssemblySafe` is stable along `RuntimeOutcomeRel` (it inspects only the
halt kind and the runtime data of a completed halt). -/
theorem prefixAssemblySafe_of_runtimeRel
    {left middle : Except EVMException TypedCfg.Outcome}
    (hRel : InteractionCongruence.Block.RuntimeOutcomeRel left middle)
    (hSafe : InteractionSemantics.Program.PrefixAssemblySafe left) :
    InteractionSemantics.Program.PrefixAssemblySafe middle := by
  cases hRel with
  | error hError =>
      subst hError
      trivial
  | ok hOutcome =>
      cases hOutcome with
      | fallthrough hState => exact hSafe.elim
      | jump label hState => exact hSafe.elim
      | returnDispatch hState => exact hSafe.elim
      | invalid hState => exact hSafe.elim
      | halt kind hState =>
          exact Assembly.InteractionSemantics.Terminal.SafeAt.of_sameRuntimeData
            hState.symm hSafe

/-- A `RuntimeOutcomeRel` whose right side is a concrete error pins the left side
to the same error (the error relation is equality). -/
theorem runtimeOutcomeRel_eq_error_right
    {left : Except EVMException TypedCfg.Outcome} {e : EVMException}
    (hRel : InteractionCongruence.Block.RuntimeOutcomeRel left (.error e)) :
    left = .error e := by
  cases hRel with
  | error hErr => rw [hErr]

/-- `PrefixAssemblySafe` and `AssemblySafeFinished` are definitionally the same
predicate; this makes the coercion explicit for the terminal path. -/
theorem assemblySafeFinished_of_prefixAssemblySafe
    {outcome : Except EVMException TypedCfg.Outcome}
    (h : InteractionSemantics.Program.PrefixAssemblySafe outcome) :
    InteractionSemantics.Program.AssemblySafeFinished outcome := by
  cases outcome with
  | error e => trivial
  | ok result =>
      cases result with
      | halt kind state => exact h
      | fallthrough state => exact h.elim
      | jump label state => exact h.elim
      | returnDispatch state => exact h.elim
      | invalid state => exact h.elim

/-- `AssemblySafeHalted` is stable along `RuntimeOutcomeRel`. -/
theorem assemblySafeHalted_of_runtimeRel
    {left middle : Except EVMException TypedCfg.Outcome}
    (hRel : InteractionCongruence.Block.RuntimeOutcomeRel left middle)
    (hSafe : InteractionSemantics.Program.AssemblySafeHalted left) :
    InteractionSemantics.Program.AssemblySafeHalted middle := by
  cases hRel with
  | error hError => exact hSafe.elim
  | ok hOutcome =>
      cases hOutcome with
      | fallthrough hState => exact hSafe.elim
      | jump label hState => exact hSafe.elim
      | returnDispatch hState => exact hSafe.elim
      | invalid hState => exact hSafe.elim
      | halt kind hState =>
          exact Assembly.InteractionSemantics.Terminal.SafeAt.of_sameRuntimeData
            hState.symm hSafe

/-- `AssemblySafeFinished` is stable along `RuntimeOutcomeRel`. -/
theorem assemblySafeFinished_of_runtimeRel
    {left middle : Except EVMException TypedCfg.Outcome}
    (hRel : InteractionCongruence.Block.RuntimeOutcomeRel left middle)
    (hSafe : InteractionSemantics.Program.AssemblySafeFinished left) :
    InteractionSemantics.Program.AssemblySafeFinished middle := by
  cases hRel with
  | error hError =>
      subst hError
      trivial
  | ok hOutcome =>
      cases hOutcome with
      | fallthrough hState => exact hSafe.elim
      | jump label hState => exact hSafe.elim
      | returnDispatch hState => exact hSafe.elim
      | invalid hState => exact hSafe.elim
      | halt kind hState =>
          exact Assembly.InteractionSemantics.Terminal.SafeAt.of_sameRuntimeData
            hState.symm hSafe

/-- **Target-fuel padding for a finished assembly `Rel`.**  When every leaf of the
smaller-budget assembly run is already `Finished` (halted or errored), extra
instruction fuel is inert, so the relation lifts verbatim to any larger budget.
This is exactly what lets the terminal path keep its conclusion budget at
`… * fuelBudget cfg` while the peepholed program only needs `… * fuelBudget
(peepholeProgram cfg)`. -/
theorem rel_openRunNResult_finished_pad
    {Error : Type} {Result : Type}
    {doneRel :
      Except Error Result →
        Except EVMException Assembly.StepResult → Prop}
    {left : Simulation.Interaction Error Result}
    {program : Assembly.Program} {smaller larger : Nat}
    {state : Assembly.EVMState}
    (hFuel : smaller ≤ larger)
    (hFinished : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult program smaller state))
    (hRel : Simulation.Interaction.Rel doneRel left
      (Assembly.InteractionSemantics.Source.openRunNResult program smaller
        state)) :
    Simulation.Interaction.Rel doneRel left
      (Assembly.InteractionSemantics.Source.openRunNResult program larger
        state) := by
  apply Simulation.Interaction.Rel.of_executes
  intro transcript leftDone hLeftExec
  obtain ⟨targetDone, hTargetExec, hDone⟩ :=
    Simulation.Interaction.Rel.executes hRel hLeftExec
  have hFin :=
    Simulation.Interaction.AllDone.property_of_executes hFinished hTargetExec
  refine ⟨targetDone, ?_, hDone⟩
  have hEq : smaller + (larger - smaller) = larger := Nat.add_sub_of_le hFuel
  rw [← hEq]
  cases targetDone with
  | error error =>
      exact Assembly.InteractionSemantics.Source.openRunNResult_error_add_executes
        hTargetExec
  | ok result =>
      cases result with
      | running s =>
          exact absurd hFin (by simp [Assembly.InteractionSemantics.Finished])
      | halted halt =>
          exact
            Assembly.InteractionSemantics.Source.openRunNResult_halted_add_executes
              hTargetExec

end Peephole
end TypedCfg
end EvmCompiler
