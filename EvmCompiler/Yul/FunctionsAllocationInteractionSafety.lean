import EvmCompiler.Functions.AllocationInteractionSafeSemantics
import EvmCompiler.Yul.AllocationInteractionSafeSemantics
import EvmCompiler.Yul.FunctionsInteractionClosedPrimitive

/-!
Adjacent Yul-to-Functions transfer for reached allocation-memory safety.

This module owns only the semantic boundary between the two source layers. It
does not know an allocation plan or emitted code. The existing ordinary
primitive-preservation theorem is reused after proving that the source guard
implies the corresponding Functions guard under the established state
relation.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsAllocationInteractionSafety

open FunctionsInteractionRelation
open FunctionsInteractionPrimitive

set_option maxHeartbeats 1000000 in
private theorem externalKind_of_selected
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (hOp : Prim.toUncheckedBasicOp? prim = some op) :
    Simulation.ExternalKind.ofEVMOperation? op.toPrimOp.toEVM =
      Simulation.ExternalKind.ofYulOperation? prim := by
  cases prim <;> rename_i family <;> cases family <;>
    simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?,
      Simulation.ExternalKind.ofEVMOperation?,
      Simulation.CallKind.ofEVMOperation?,
      Simulation.CreateKind.ofEVMOperation?] at hOp ⊢
  all_goals subst op <;> rfl

namespace Primitive

theorem safe_eq_functions
    {contract : MemoryContract.Contract}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues : List Assembly.Word}
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hRel : StateRel source target) :
    AllocationInteractionSafeSemantics.PrimitiveSafe
        contract prim source sourceValues =
      Functions.AllocationInteractionPrimitive.PrimitiveSafe
        contract op target sourceValues.reverse := by
  have hTerminal : Prim.terminal? prim = none :=
    Prim.toUncheckedBasicOp?_some_terminal_none hOp
  unfold AllocationInteractionSafeSemantics.PrimitiveSafe
  rw [hTerminal]
  cases hExternal : Simulation.ExternalKind.ofYulOperation? prim with
  | some externalKind =>
      have hPrim :=
        Simulation.ExternalKind.eq_toYulOperation_of_ofYulOperation?_eq_some
          hExternal
      subst prim
      cases externalKind with
      | call kind =>
          change Prim.toUncheckedBasicOp? kind.toYulOperation = some op at hOp
          rw [FunctionsInteractionPrimitive.Primitive.toUncheckedBasicOp?_callBasicOp]
            at hOp
          cases hOp
          cases kind <;>
            simp [FunctionsInteractionPrimitive.Primitive.callBasicOp,
              Functions.AllocationInteractionPrimitive.PrimitiveSafe,
              Functions.AllocationInteractionPrimitive.callOp,
              Structured.BasicOp.toPrimOp, Assembly.PrimOp.toEVM,
              Simulation.ExternalKind.ofEVMOperation?,
              Simulation.CallKind.ofEVMOperation?,
              Simulation.CreateKind.ofEVMOperation?]
      | create kind =>
          change Prim.toUncheckedBasicOp? kind.toYulOperation = some op at hOp
          rw [FunctionsInteractionPrimitive.Primitive.toUncheckedBasicOp?_createBasicOp]
            at hOp
          cases hOp
          cases kind <;>
            simp [FunctionsInteractionPrimitive.Primitive.createBasicOp,
              Functions.AllocationInteractionPrimitive.PrimitiveSafe,
              Functions.AllocationInteractionPrimitive.createOp,
              Structured.BasicOp.toPrimOp, Assembly.PrimOp.toEVM,
              Simulation.ExternalKind.ofEVMOperation?,
              Simulation.CallKind.ofEVMOperation?,
              Simulation.CreateKind.ofEVMOperation?]
  | none =>
      simp only [hOp]
      have hTargetExternal :
          Simulation.ExternalKind.ofEVMOperation? op.toPrimOp.toEVM = none := by
        rw [externalKind_of_selected hOp, hExternal]
      unfold Functions.AllocationInteractionPrimitive.PrimitiveSafe
      rw [hTargetExternal]
      have hMachine := (StateRel.shared hRel).machine
      simp [hMachine]

theorem safe_to_functions
    {contract : MemoryContract.Contract}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues : List Assembly.Word}
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hRel : StateRel source target)
    (hSafe : AllocationInteractionSafeSemantics.PrimitiveSafe
      contract prim source sourceValues) :
    Functions.AllocationInteractionPrimitive.PrimitiveSafe
      contract op target sourceValues.reverse := by
  rw [← safe_eq_functions hOp hRel]
  exact hSafe

theorem terminalSafe_to_functions
    {contract : MemoryContract.Contract}
    {source : Yul.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {kind : Assembly.HaltKind}
    {sourceValues : List Assembly.Word}
    (hTerminal : Prim.terminal? prim = some kind)
    (hSafe : AllocationInteractionSafeSemantics.PrimitiveSafe
      contract prim source sourceValues) :
    Simulation.MemorySafety.TerminalMemorySafe
      contract kind sourceValues.reverse := by
  simpa [AllocationInteractionSafeSemantics.PrimitiveSafe, hTerminal]
    using hSafe

end Primitive

/-- Primitive capability used by the future recursive guarded-safety transfer.
It is independent of the ordinary forward capability so the two adjacent
properties remain separately reusable. -/
def CompilerSelectedSafe (contract : MemoryContract.Contract) : Prop :=
  ∀ {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues : List Assembly.Word},
    Prim.toUncheckedBasicOp? prim = some op →
    sourceValues.length = Expressions.Structured.BasicOp.inputs op →
    StateRel source target →
    Simulation.Interaction.ForwardRel Truncated (PrimitiveDoneRel source op)
      (AllocationInteractionSafeSemantics.openEval
        contract (fuel + 1) source prim sourceValues)
      (Functions.AllocationInteractionSafeSemantics.openEval
        contract op target sourceValues.reverse)

theorem compilerSelectedSafe
    (contract : MemoryContract.Contract) : CompilerSelectedSafe contract := by
  intro fuel source target prim op sourceValues hOp hLength hRel
  by_cases hSourceSafe :
      AllocationInteractionSafeSemantics.PrimitiveSafe
        contract prim source sourceValues
  · have hTargetSafe := Primitive.safe_to_functions hOp hRel hSourceSafe
    rw [AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary
        hSourceSafe,
      Functions.AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary
        hTargetSafe]
    exact FunctionsInteractionClosedPrimitive.compilerSelected
      hOp hLength hRel
  · have hTargetUnsafe :
        ¬ Functions.AllocationInteractionPrimitive.PrimitiveSafe
          contract op target sourceValues.reverse := by
      rwa [← Primitive.safe_eq_functions hOp hRel]
    unfold AllocationInteractionSafeSemantics.openEval
      Functions.AllocationInteractionSafeSemantics.openEval
    simp only [hSourceSafe, hTargetUnsafe, ↓reduceIte]
    exact Simulation.Interaction.ForwardRel.done
      (.error (by simp [FunctionsInteractionPrimitive.ErrorRel]))

end FunctionsAllocationInteractionSafety
end Yul
end EvmCompiler
