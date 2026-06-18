import EvmCompiler.Yul.FunctionsInteractionPrimitive

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionClosedPrimitive

open FunctionsInteractionRelation
open FunctionsInteractionPrimitive

/-- Shared proof interface for closed primitives that preserve shared state and
compute only a list of result words. -/
structure PureSpec (prim : EvmYul.Operation .Yul)
    (op : Structured.BasicOp) where
  result : List Word → List Word
  resultLength :
    ∀ values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        (result values).length = Expressions.Structured.BasicOp.outputs op
  sourceZero :
    ∀ source values,
      Yul.InteractionSemantics.Primitive.openEval 1 source prim values =
        .done
          (.error
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure))
  sourceSucc :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
            (EvmYul.Yul.State.Ok sourceShared sourceVars) prim values =
          .done (.ok (.Ok sourceShared sourceVars, result values))
  target :
    ∀ state values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Locals.InteractionSemantics.Primitive.openEval
            op state values.reverse =
          .done (.ok (state, result values))

namespace PureSpec

theorem forward
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (spec : PureSpec prim op)
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      rw [spec.sourceZero]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source op)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hStateRel :
          FunctionsInteractionRelation.StateRel
            (.Ok sourceShared sourceVars) target :=
        ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
      have hDone :
          PrimitiveDoneRel (.Ok sourceShared sourceVars) op
            (.ok
              (.Ok sourceShared sourceVars,
                spec.result sourceValues))
            (.ok (target, spec.result sourceValues)) :=
        .ok
          ⟨FunctionsInteractionPrimitive.ResultRel.refl_values
              hStateRel (spec.result sourceValues),
            spec.resultLength sourceValues hLength,
            rfl⟩
      rw [show previous.succ + 1 = previous + 2 by omega,
        spec.sourceSucc previous sourceShared sourceVars sourceValues hLength,
        spec.target target sourceValues hLength]
      exact Simulation.Interaction.ForwardRel.done hDone

end PureSpec

/-- Shared proof interface for closed primitives whose only shared-state effect
is a deterministic active-machine update. -/
structure MachineSpec (prim : EvmYul.Operation .Yul)
    (op : Structured.BasicOp) where
  result : EvmYul.MachineState → List Word → EvmYul.MachineState × List Word
  resultLength :
    ∀ machine values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        (result machine values).2.length =
          Expressions.Structured.BasicOp.outputs op
  sourceZero :
    ∀ source values,
      Yul.InteractionSemantics.Primitive.openEval 1 source prim values =
        .done
          (.error
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure))
  sourceSucc :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
            (.Ok sourceShared sourceVars) prim values =
          .done
            (.ok
              ((EvmYul.Yul.State.Ok sourceShared sourceVars).setMachineState
                  (result sourceShared.toMachineState values).1,
                (result sourceShared.toMachineState values).2))
  target :
    ∀ state values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Locals.InteractionSemantics.Primitive.openEval
            op state values.reverse =
          .done
            (.ok
              (state.withShared
                  { state.shared with
                    toMachineState :=
                      (result state.shared.toMachineState values).1 },
                (result state.shared.toMachineState values).2))

namespace MachineSpec

theorem forward
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (spec : MachineSpec prim op)
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      rw [spec.sourceZero]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source op)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      let sourceResult :=
        spec.result sourceShared.toMachineState sourceValues
      let targetResult :=
        spec.result target.shared.toMachineState sourceValues
      have hResult : sourceResult = targetResult := by
        simp [sourceResult, targetResult, hShared.machine]
      have hTargetResult :
          spec.result target.shared.toMachineState sourceValues =
            sourceResult := by
        simpa [targetResult] using hResult.symm
      have hStateRel :
          FunctionsInteractionRelation.StateRel
            (EvmYul.Yul.State.Ok sourceShared sourceVars) target :=
        ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
      have hFinalRel :=
        FunctionsInteractionRelation.StateRel.withMachine hStateRel
          sourceResult.1 sourceResult.1 rfl
      have hDone :
          PrimitiveDoneRel (EvmYul.Yul.State.Ok sourceShared sourceVars) op
            (.ok
              ((EvmYul.Yul.State.Ok sourceShared sourceVars).setMachineState
                  sourceResult.1,
                sourceResult.2))
            (.ok
              (target.withShared
                  { target.shared with toMachineState := sourceResult.1 },
                sourceResult.2)) :=
        .ok
          ⟨⟨hFinalRel, rfl⟩,
            spec.resultLength sourceShared.toMachineState sourceValues hLength,
            rfl⟩
      have hTarget := spec.target target sourceValues hLength
      rw [hTargetResult] at hTarget
      rw [show previous.succ + 1 = previous + 2 by omega,
        spec.sourceSucc previous sourceShared sourceVars sourceValues hLength,
        hTarget]
      exact Simulation.Interaction.ForwardRel.done hDone

end MachineSpec

/-- Shared proof interface for deterministic closed primitives that may replace
the complete shared state while preserving its code-erased relation. -/
structure SharedSpec (prim : EvmYul.Operation .Yul)
    (op : Structured.BasicOp) where
  sourceResult :
    EvmYul.SharedState .Yul → List Word →
      EvmYul.SharedState .Yul × List Word
  targetResult :
    EvmYul.SharedState .EVM → List Word →
      EvmYul.SharedState .EVM × List Word
  resultLength :
    ∀ shared values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        (sourceResult shared values).2.length =
          Expressions.Structured.BasicOp.outputs op
  related :
    ∀ source target values,
      FunctionsInteractionRelation.SharedRel source target →
        FunctionsInteractionRelation.SharedRel
            (sourceResult source values).1
            (targetResult target values).1 ∧
          (sourceResult source values).2 =
            (targetResult target values).2
  sourceZero :
    ∀ source values,
      Yul.InteractionSemantics.Primitive.openEval 1 source prim values =
        .done
          (.error
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure))
  sourceSucc :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
            (.Ok sourceShared sourceVars) prim values =
          .done
            (.ok
              ((EvmYul.Yul.State.Ok sourceShared sourceVars).setSharedState
                  (sourceResult sourceShared values).1,
                (sourceResult sourceShared values).2))
  target :
    ∀ state values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Locals.InteractionSemantics.Primitive.openEval
            op state values.reverse =
          .done
            (.ok
              (state.withShared (targetResult state.shared values).1,
                (targetResult state.shared values).2))

namespace SharedSpec

theorem forward
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (spec : SharedSpec prim op)
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      rw [spec.sourceZero]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source op)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      let sourceResult := spec.sourceResult sourceShared sourceValues
      let targetResult := spec.targetResult target.shared sourceValues
      have hRelated :
          FunctionsInteractionRelation.SharedRel
              sourceResult.1 targetResult.1 ∧
            sourceResult.2 = targetResult.2 := by
        simpa [sourceResult, targetResult] using
          spec.related sourceShared target.shared sourceValues hShared
      have hStateRel :
          FunctionsInteractionRelation.StateRel
            (EvmYul.Yul.State.Ok sourceShared sourceVars) target :=
        ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
      have hFinalRel :=
        FunctionsInteractionRelation.StateRel.withSharedState hStateRel
          sourceResult.1 targetResult.1 hRelated.1
      have hDone :
          PrimitiveDoneRel (EvmYul.Yul.State.Ok sourceShared sourceVars) op
            (.ok
              ((EvmYul.Yul.State.Ok sourceShared sourceVars).setSharedState
                  sourceResult.1,
                sourceResult.2))
            (.ok
              (target.withShared targetResult.1,
                sourceResult.2)) :=
        .ok
          ⟨⟨hFinalRel, rfl⟩,
            by simpa [sourceResult] using
              spec.resultLength sourceShared sourceValues hLength,
            rfl⟩
      have hTarget := spec.target target sourceValues hLength
      change
        Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse =
          .done (.ok (target.withShared targetResult.1, targetResult.2))
        at hTarget
      rw [← hRelated.2] at hTarget
      rw [show previous.succ + 1 = previous + 2 by omega,
        spec.sourceSucc previous sourceShared sourceVars sourceValues hLength,
        hTarget]
      exact Simulation.Interaction.ForwardRel.done hDone

end SharedSpec

/-- Shared-state writes share a deterministic permitted transition and an
exact static-mode failure on both sides. -/
structure SharedWriteSpec (prim : EvmYul.Operation .Yul)
    (op : Structured.BasicOp) where
  sourceResult :
    EvmYul.SharedState .Yul → List Word →
      EvmYul.SharedState .Yul × List Word
  targetResult :
    EvmYul.SharedState .EVM → List Word →
      EvmYul.SharedState .EVM × List Word
  resultLength :
    ∀ shared values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        (sourceResult shared values).2.length =
          Expressions.Structured.BasicOp.outputs op
  related :
    ∀ source target values,
      values.length = Expressions.Structured.BasicOp.inputs op →
      FunctionsInteractionRelation.SharedRel source target →
        FunctionsInteractionRelation.SharedRel
            (sourceResult source values).1
            (targetResult target values).1 ∧
          (sourceResult source values).2 =
            (targetResult target values).2
  sourceZero :
    ∀ source values,
      Yul.InteractionSemantics.Primitive.openEval 1 source prim values =
        .done
          (.error
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure))
  sourceAllowed :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        sourceShared.executionEnv.perm = true →
          Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
              (.Ok sourceShared sourceVars) prim values =
            .done
              (.ok
                ((EvmYul.Yul.State.Ok sourceShared sourceVars).setSharedState
                    (sourceResult sourceShared values).1,
                  (sourceResult sourceShared values).2))
  sourceDenied :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        sourceShared.executionEnv.perm = false →
          Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
              (.Ok sourceShared sourceVars) prim values =
            .done
              (.error
                ({ exception := .StaticModeViolation,
                    state := .Ok sourceShared sourceVars } :
                  Yul.InteractionSemantics.Failure))
  targetAllowed :
    ∀ (state : Functions.InteractionSemantics.State) (values : List Word),
      values.length = Expressions.Structured.BasicOp.inputs op →
        state.shared.executionEnv.perm = true →
          Locals.InteractionSemantics.Primitive.openEval
              op state values.reverse =
            .done
              (.ok
                (state.withShared (targetResult state.shared values).1,
                  (targetResult state.shared values).2))
  targetDenied :
    ∀ (state : Functions.InteractionSemantics.State) (values : List Word),
      values.length = Expressions.Structured.BasicOp.inputs op →
        state.shared.executionEnv.perm = false →
          Locals.InteractionSemantics.Primitive.openEval
              op state values.reverse =
            .done (.error .StaticModeViolation)

namespace SharedWriteSpec

theorem forward
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (spec : SharedWriteSpec prim op)
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      rw [spec.sourceZero]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source op)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          have hTargetPermission :
              target.shared.executionEnv.perm = false := by
            simpa [hPermission] using hShared.executionEnv.permission.symm
          rw [show previous.succ + 1 = previous + 2 by omega,
            spec.sourceDenied previous sourceShared sourceVars sourceValues
              hLength hPermission,
            spec.targetDenied target sourceValues hLength hTargetPermission]
          exact Simulation.Interaction.ForwardRel.done
            (Simulation.Interaction.ExceptRel.error trivial)
      | true =>
          have hTargetPermission :
              target.shared.executionEnv.perm = true := by
            simpa [hPermission] using hShared.executionEnv.permission.symm
          let sourceResult := spec.sourceResult sourceShared sourceValues
          let targetResult := spec.targetResult target.shared sourceValues
          have hRelated :
              FunctionsInteractionRelation.SharedRel
                  sourceResult.1 targetResult.1 ∧
                sourceResult.2 = targetResult.2 := by
            simpa [sourceResult, targetResult] using
              spec.related sourceShared target.shared sourceValues hLength hShared
          have hStateRel :
              FunctionsInteractionRelation.StateRel
                (EvmYul.Yul.State.Ok sourceShared sourceVars) target :=
            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
          have hFinalRel :=
            FunctionsInteractionRelation.StateRel.withSharedState hStateRel
              sourceResult.1 targetResult.1 hRelated.1
          have hDone :
              PrimitiveDoneRel
                (EvmYul.Yul.State.Ok sourceShared sourceVars) op
                (.ok
                  ((EvmYul.Yul.State.Ok sourceShared sourceVars).setSharedState
                      sourceResult.1,
                    sourceResult.2))
                (.ok
                  (target.withShared targetResult.1,
                    sourceResult.2)) :=
            .ok
              ⟨⟨hFinalRel, rfl⟩,
                by simpa [sourceResult] using
                  spec.resultLength sourceShared sourceValues hLength,
                rfl⟩
          have hTarget :=
            spec.targetAllowed target sourceValues hLength hTargetPermission
          change
            Locals.InteractionSemantics.Primitive.openEval
                op target sourceValues.reverse =
              .done (.ok (target.withShared targetResult.1, targetResult.2))
            at hTarget
          rw [← hRelated.2] at hTarget
          rw [show previous.succ + 1 = previous + 2 by omega,
            spec.sourceAllowed previous sourceShared sourceVars sourceValues
              hLength hPermission,
            hTarget]
          exact Simulation.Interaction.ForwardRel.done hDone

end SharedWriteSpec

/-- Shared proof interface for read-only execution-environment primitives.
Source and target environment types differ only at their code representation,
so each family supplies one result-equality theorem over `ExecutionEnvRel`. -/
structure EnvironmentSpec (prim : EvmYul.Operation .Yul)
    (op : Structured.BasicOp) where
  sourceResult : EvmYul.ExecutionEnv .Yul → List Word → List Word
  targetResult : EvmYul.ExecutionEnv .EVM → List Word → List Word
  resultLength :
    ∀ env values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        (sourceResult env values).length =
          Expressions.Structured.BasicOp.outputs op
  resultEq :
    ∀ sourceEnv targetEnv values,
      FunctionsInteractionRelation.ExecutionEnvRel sourceEnv targetEnv →
        sourceResult sourceEnv values = targetResult targetEnv values
  sourceZero :
    ∀ source values,
      Yul.InteractionSemantics.Primitive.openEval 1 source prim values =
        .done
          (.error
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure))
  sourceSucc :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
            (EvmYul.Yul.State.Ok sourceShared sourceVars) prim values =
          .done
            (.ok
              (EvmYul.Yul.State.Ok sourceShared sourceVars,
                sourceResult sourceShared.executionEnv values))
  target :
    ∀ state values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Locals.InteractionSemantics.Primitive.openEval
            op state values.reverse =
          .done
            (.ok
              (state, targetResult state.shared.executionEnv values))

namespace EnvironmentSpec

theorem forward
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (spec : EnvironmentSpec prim op)
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      rw [spec.sourceZero]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source op)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hStateRel :
          FunctionsInteractionRelation.StateRel
            (EvmYul.Yul.State.Ok sourceShared sourceVars) target :=
        ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
      have hResult :=
        spec.resultEq sourceShared.executionEnv target.shared.executionEnv
          sourceValues hShared.executionEnv
      have hDone :
          PrimitiveDoneRel (EvmYul.Yul.State.Ok sourceShared sourceVars) op
            (.ok
              (EvmYul.Yul.State.Ok sourceShared sourceVars,
                spec.sourceResult sourceShared.executionEnv sourceValues))
            (.ok
              (target,
                spec.sourceResult sourceShared.executionEnv sourceValues)) :=
        .ok
          ⟨FunctionsInteractionPrimitive.ResultRel.refl_values hStateRel _,
            spec.resultLength sourceShared.executionEnv sourceValues hLength,
            rfl⟩
      have hTarget := spec.target target sourceValues hLength
      rw [← hResult] at hTarget
      rw [show previous.succ + 1 = previous + 2 by omega,
        spec.sourceSucc previous sourceShared sourceVars sourceValues hLength,
        hTarget]
      exact Simulation.Interaction.ForwardRel.done hDone

end EnvironmentSpec

/-- Read-only nullary operations whose result is selected from the execution
environment. -/
inductive EnvironmentNullary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.ExecutionEnv .Yul → Word) →
      (EvmYul.ExecutionEnv .EVM → Word) → Prop where
  | address :
      EnvironmentNullary (.Env .ADDRESS) .address
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.codeOwner)
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.codeOwner)
  | origin :
      EnvironmentNullary (.Env .ORIGIN) .origin
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.sender)
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.sender)
  | caller :
      EnvironmentNullary (.Env .CALLER) .caller
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.source)
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘
          EvmYul.ExecutionEnv.source)
  | callvalue :
      EnvironmentNullary (.Env .CALLVALUE) .callvalue
        EvmYul.ExecutionEnv.weiValue
        EvmYul.ExecutionEnv.weiValue
  | calldatasize :
      EnvironmentNullary (.Env .CALLDATASIZE) .calldatasize
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.ExecutionEnv.calldata)
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.ExecutionEnv.calldata)
  | codesize :
      EnvironmentNullary (.Env .CODESIZE) .codesize
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.ExecutionEnv.codeBytes)
        (EvmYul.UInt256.ofNat ∘ ByteArray.size ∘
          EvmYul.ExecutionEnv.code)
  | gasprice :
      EnvironmentNullary (.Env .GASPRICE) .gasprice
        (EvmYul.UInt256.ofNat ∘ EvmYul.ExecutionEnv.gasPrice)
        (EvmYul.UInt256.ofNat ∘ EvmYul.ExecutionEnv.gasPrice)
  | prevrandao :
      EnvironmentNullary (.Block .PREVRANDAO) .prevrandao
        EvmYul.prevRandao EvmYul.prevRandao
  | basefee :
      EnvironmentNullary (.Block .BASEFEE) .basefee
        EvmYul.basefee EvmYul.basefee
  | blobbasefee :
      EnvironmentNullary (.Block .BLOBBASEFEE) .blobbasefee
        EvmYul.ExecutionEnv.getBlobGasprice
        EvmYul.ExecutionEnv.getBlobGasprice

namespace EnvironmentNullary

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily : EnvironmentNullary prim op sourceResult targetResult) :
    Expressions.Structured.BasicOp.inputs op = 0 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily : EnvironmentNullary prim op sourceResult targetResult) :
    Expressions.Structured.BasicOp.outputs op = 1 := by
  cases hFamily <;> rfl

theorem resultEq
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily : EnvironmentNullary prim op sourceResult targetResult)
    {source : EvmYul.ExecutionEnv .Yul}
    {target : EvmYul.ExecutionEnv .EVM}
    (hRel : FunctionsInteractionRelation.ExecutionEnvRel source target) :
    sourceResult source = targetResult target := by
  cases hFamily with
  | address =>
      simpa [Function.comp_def] using
        congrArg (fun address => EvmYul.UInt256.ofNat address.val)
          hRel.codeOwner
  | origin =>
      simpa [Function.comp_def] using
        congrArg (fun address => EvmYul.UInt256.ofNat address.val)
          hRel.sender
  | caller =>
      simpa [Function.comp_def] using
        congrArg (fun address => EvmYul.UInt256.ofNat address.val)
          hRel.sourceAddress
  | callvalue => exact hRel.weiValue
  | calldatasize =>
      simpa [Function.comp_def] using
        congrArg (fun bytes => EvmYul.UInt256.ofNat bytes.size)
          hRel.calldata
  | codesize =>
      simpa [Function.comp_def] using
        congrArg (fun bytes => EvmYul.UInt256.ofNat bytes.size)
          hRel.codeImage
  | gasprice =>
      simpa [Function.comp_def] using
        congrArg EvmYul.UInt256.ofNat hRel.gasPrice
  | prevrandao =>
      simpa [EvmYul.prevRandao] using
        congrArg EvmYul.BlockHeader.prevRandao hRel.header
  | basefee =>
      simpa [EvmYul.basefee] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.baseFeePerGas)
          hRel.header
  | blobbasefee =>
      simpa [EvmYul.ExecutionEnv.getBlobGasprice] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.getBlobGasprice)
          hRel.header

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    (hFamily : EnvironmentNullary prim op sourceResult targetResult) :
    EnvironmentSpec prim op where
  sourceResult env values := if values = [] then [sourceResult env] else []
  targetResult env values := if values = [] then [targetResult env] else []
  resultLength := by
    intro env values hLength
    have hValues : values = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [hFamily.inputs] using hLength
    subst values
    simp [hFamily.outputs]
  resultEq := by
    intro source target values hRel
    by_cases hValues : values = []
    · simp [hValues, hFamily.resultEq hRel]
    · simp [hValues]
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hValues : values = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [hFamily.inputs] using hLength
    subst values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.executionEnvOp] <;>
      unfold EvmYul.step <;> rfl
  target := by
    intro state values hLength
    have hValues : values = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [hFamily.inputs] using hLength
    subst values
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.executionEnv targetResult) := by
      cases hFamily <;> rfl
    have hGas : op.toPrimOp ≠ .gas := by
      cases hFamily <;> decide
    have hMsize : op.toPrimOp ≠ .msize := by
      cases hFamily <;> decide
    change
      Locals.InteractionSemantics.Primitive.openEval op state [] =
        .done (.ok (state, [targetResult state.shared.executionEnv]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep hGas hMsize]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word}
    {sourceValues : List Word}
    (hFamily : EnvironmentNullary prim op sourceResult targetResult)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end EnvironmentNullary

/-- Read-only unary execution-environment operations. -/
inductive EnvironmentUnary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.ExecutionEnv .Yul → Word → Word) →
      (EvmYul.ExecutionEnv .EVM → Word → Word) → Prop where
  | blobhash :
      EnvironmentUnary (.Block .BLOBHASH) .blobhash
        EvmYul.blobhash EvmYul.blobhash

namespace EnvironmentUnary

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    (hFamily : EnvironmentUnary prim op sourceResult targetResult) :
    EnvironmentSpec prim op where
  sourceResult env values :=
    match values with
    | [value] => [sourceResult env value]
    | _ => []
  targetResult env values :=
    match values with
    | [value] => [targetResult env value]
    | _ => []
  resultLength := by
    intro env values hLength
    have hLengthOne : values.length = 1 := by
      cases hFamily
      simpa using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    cases hFamily
    rfl
  resultEq := by
    intro source target values hRel
    cases hFamily
    cases values with
    | nil => rfl
    | cons value rest =>
        cases rest with
        | nil => simp [EvmYul.blobhash, hRel.blobVersionedHashes]
        | cons next tail => rfl
  sourceZero := by
    intro source values
    cases hFamily
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.InteractionSemantics.State.afterException,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hLengthOne : values.length = 1 := by
      cases hFamily
      simpa using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    cases hFamily
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
      EvmYul.Yul.unaryExecutionEnvOp]
    unfold EvmYul.step
    rfl
  target := by
    intro state values hLength
    have hLengthOne : values.length = 1 := by
      cases hFamily
      simpa using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    cases hFamily
    change
      Locals.InteractionSemantics.Primitive.openEval
          .blobhash state [value] =
        .done
          (.ok
            (state, [EvmYul.blobhash state.shared.executionEnv value]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.ExecutionEnv .Yul → Word → Word}
    {targetResult : EvmYul.ExecutionEnv .EVM → Word → Word}
    {sourceValues : List Word}
    (hFamily : EnvironmentUnary prim op sourceResult targetResult)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end EnvironmentUnary

/-- Shared proof interface for world reads that do not mutate the code-erased
world. -/
structure WorldReadSpec (prim : EvmYul.Operation .Yul)
    (op : Structured.BasicOp) where
  sourceResult : EvmYul.State .Yul → List Word → List Word
  targetResult : EvmYul.State .EVM → List Word → List Word
  resultLength :
    ∀ world values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        (sourceResult world values).length =
          Expressions.Structured.BasicOp.outputs op
  resultEq :
    ∀ sourceWorld targetWorld values,
      FunctionsInteractionRelation.WorldRel sourceWorld targetWorld →
        sourceResult sourceWorld values = targetResult targetWorld values
  sourceZero :
    ∀ source values,
      Yul.InteractionSemantics.Primitive.openEval 1 source prim values =
        .done
          (.error
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure))
  sourceSucc :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
            (EvmYul.Yul.State.Ok sourceShared sourceVars) prim values =
          .done
            (.ok
              (EvmYul.Yul.State.Ok sourceShared sourceVars,
                sourceResult sourceShared.toState values))
  target :
    ∀ state values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Locals.InteractionSemantics.Primitive.openEval
            op state values.reverse =
          .done (.ok (state, targetResult state.shared.toState values))

namespace WorldReadSpec

theorem forward
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (spec : WorldReadSpec prim op)
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      rw [spec.sourceZero]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source op)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hStateRel :
          FunctionsInteractionRelation.StateRel
            (EvmYul.Yul.State.Ok sourceShared sourceVars) target :=
        ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
      have hResult :=
        spec.resultEq sourceShared.toState target.shared.toState sourceValues
          hShared.world
      have hDone :
          PrimitiveDoneRel (EvmYul.Yul.State.Ok sourceShared sourceVars) op
            (.ok
              (EvmYul.Yul.State.Ok sourceShared sourceVars,
                spec.sourceResult sourceShared.toState sourceValues))
            (.ok
              (target,
                spec.sourceResult sourceShared.toState sourceValues)) :=
        .ok
          ⟨FunctionsInteractionPrimitive.ResultRel.refl_values hStateRel _,
            spec.resultLength sourceShared.toState sourceValues hLength,
            rfl⟩
      have hTarget := spec.target target sourceValues hLength
      rw [← hResult] at hTarget
      rw [show previous.succ + 1 = previous + 2 by omega,
        spec.sourceSucc previous sourceShared sourceVars sourceValues hLength,
        hTarget]
      exact Simulation.Interaction.ForwardRel.done hDone

end WorldReadSpec

inductive WorldNullary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.State .Yul → Word) →
      (EvmYul.State .EVM → Word) → Prop where
  | coinbase :
      WorldNullary (.Block .COINBASE) .coinbase
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
        (EvmYul.UInt256.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
  | timestamp :
      WorldNullary (.Block .TIMESTAMP) .timestamp
        EvmYul.State.timeStamp EvmYul.State.timeStamp
  | number :
      WorldNullary (.Block .NUMBER) .number
        EvmYul.State.number EvmYul.State.number
  | gaslimit :
      WorldNullary (.Block .GASLIMIT) .gaslimit
        EvmYul.State.gasLimit EvmYul.State.gasLimit
  | chainid :
      WorldNullary (.Block .CHAINID) .chainid
        EvmYul.State.chainId EvmYul.State.chainId
  | selfbalance :
      WorldNullary (.Block .SELFBALANCE) .selfbalance
        EvmYul.State.selfbalance EvmYul.State.selfbalance

namespace WorldNullary

private theorem selfbalanceEq
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : FunctionsInteractionRelation.WorldRel source target) :
    EvmYul.State.selfbalance source =
      EvmYul.State.selfbalance target := by
  unfold EvmYul.State.selfbalance
  rw [← hRel.executionEnv.codeOwner]
  let owner := source.executionEnv.codeOwner
  have hLookup := hRel.accountViews owner
  cases hSource : source.accountMap.find? owner with
  | none =>
      rw [hSource] at hLookup
      cases hTarget : target.accountMap.find? owner with
      | none => simp [hSource, hTarget]
      | some targetAccount => simp [hTarget] at hLookup
  | some sourceAccount =>
      rw [hSource] at hLookup
      cases hTarget : target.accountMap.find? owner with
      | none => simp [hTarget] at hLookup
      | some targetAccount =>
          rw [hTarget] at hLookup
          have hAccount :
              Simulation.OpenAccount.ofYul sourceAccount =
                Simulation.OpenAccount.ofEVM targetAccount := by
            simpa using Option.some.inj hLookup
          simpa [hSource, hTarget] using
            congrArg Simulation.OpenAccount.balance hAccount

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult) :
    Expressions.Structured.BasicOp.inputs op = 0 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult) :
    Expressions.Structured.BasicOp.outputs op = 1 := by
  cases hFamily <;> rfl

theorem resultEq
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult)
    {source : EvmYul.State .Yul}
    {target : EvmYul.State .EVM}
    (hRel : FunctionsInteractionRelation.WorldRel source target) :
    sourceResult source = targetResult target := by
  cases hFamily with
  | coinbase =>
      simpa [Function.comp_def, EvmYul.State.coinBase] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.beneficiary.val)
          hRel.executionEnv.header
  | timestamp =>
      simpa [EvmYul.State.timeStamp] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.timestamp)
          hRel.executionEnv.header
  | number =>
      simpa [EvmYul.State.number] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.number)
          hRel.executionEnv.header
  | gaslimit =>
      simpa [EvmYul.State.gasLimit] using
        congrArg
          (fun header => EvmYul.UInt256.ofNat header.gasLimit)
          hRel.executionEnv.header
  | chainid => rfl
  | selfbalance => exact selfbalanceEq hRel

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    (hFamily : WorldNullary prim op sourceResult targetResult) :
    WorldReadSpec prim op where
  sourceResult world values := if values = [] then [sourceResult world] else []
  targetResult world values := if values = [] then [targetResult world] else []
  resultLength := by
    intro world values hLength
    have hValues : values = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [hFamily.inputs] using hLength
    subst values
    simp [hFamily.outputs]
  resultEq := by
    intro source target values hRel
    by_cases hValues : values = []
    · simp [hValues, hFamily.resultEq hRel]
    · simp [hValues]
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hValues : values = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [hFamily.inputs] using hLength
    subst values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.stateOp] <;>
      unfold EvmYul.step <;> rfl
  target := by
    intro state values hLength
    have hValues : values = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa [hFamily.inputs] using hLength
    subst values
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.state targetResult) := by
      cases hFamily <;> rfl
    change
      Locals.InteractionSemantics.Primitive.openEval op state [] =
        .done (.ok (state, [targetResult state.shared.toState]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep
      (by cases hFamily <;> decide) (by cases hFamily <;> decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word}
    {targetResult : EvmYul.State .EVM → Word}
    {sourceValues : List Word}
    (hFamily : WorldNullary prim op sourceResult targetResult)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end WorldNullary

inductive WorldUnaryRead :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.State .Yul → Word → Word) →
      (EvmYul.State .EVM → Word → Word) → Prop where
  | calldataload :
      WorldUnaryRead (.Env .CALLDATALOAD) .calldataload
        EvmYul.State.calldataload EvmYul.State.calldataload
  | blockhash :
      WorldUnaryRead (.Block .BLOCKHASH) .blockhash
        EvmYul.State.blockHash EvmYul.State.blockHash

namespace WorldUnaryRead

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult) :
    WorldReadSpec prim op where
  sourceResult world values :=
    match values with
    | [value] => [sourceResult world value]
    | _ => []
  targetResult world values :=
    match values with
    | [value] => [targetResult world value]
    | _ => []
  resultLength := by
    intro world values hLength
    have hLengthOne : values.length = 1 := by
      cases hFamily <;> simpa using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    cases hFamily <;> rfl
  resultEq := by
    intro source target values hRel
    cases values with
    | nil => rfl
    | cons value rest =>
        cases rest with
        | cons next tail => rfl
        | nil =>
            cases hFamily with
            | calldataload =>
                simp [EvmYul.State.calldataload,
                  hRel.executionEnv.calldata]
            | blockhash =>
                simp [EvmYul.State.blockHash, EvmYul.State.blockHashes,
                  hRel.executionEnv.header, hRel.blocks]
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hLengthOne : values.length = 1 := by
      cases hFamily <;> simpa using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.unaryStateOp] <;>
      unfold EvmYul.step <;> rfl
  target := by
    intro state values hLength
    have hLengthOne : values.length = 1 := by
      cases hFamily <;> simpa using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.unaryState
            (fun world value => (world, targetResult world value))) := by
      cases hFamily <;> rfl
    change
      Locals.InteractionSemantics.Primitive.openEval op state [value] =
        .done (.ok (state, [targetResult state.shared.toState value]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by cases hFamily <;> rfl) hSupports hStep
      (by cases hFamily <;> decide) (by cases hFamily <;> decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceResult : EvmYul.State .Yul → Word → Word}
    {targetResult : EvmYul.State .EVM → Word → Word}
    {sourceValues : List Word}
    (hFamily : WorldUnaryRead prim op sourceResult targetResult)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end WorldUnaryRead

/-- Shared proof interface for deterministic closed world transitions. -/
structure WorldSpec (prim : EvmYul.Operation .Yul)
    (op : Structured.BasicOp) where
  sourceStep :
    EvmYul.State .Yul → List Word → EvmYul.State .Yul × List Word
  targetStep :
    EvmYul.State .EVM → List Word → EvmYul.State .EVM × List Word
  resultLength :
    ∀ world values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        (sourceStep world values).2.length =
          Expressions.Structured.BasicOp.outputs op
  related :
    ∀ sourceWorld targetWorld values,
      FunctionsInteractionRelation.WorldRel sourceWorld targetWorld →
        FunctionsInteractionRelation.WorldRel
            (sourceStep sourceWorld values).1
            (targetStep targetWorld values).1 ∧
          (sourceStep sourceWorld values).2 =
            (targetStep targetWorld values).2
  sourceZero :
    ∀ source values,
      Yul.InteractionSemantics.Primitive.openEval 1 source prim values =
        .done
          (.error
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure))
  sourceSucc :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
            (EvmYul.Yul.State.Ok sourceShared sourceVars) prim values =
          .done
            (.ok
              ((EvmYul.Yul.State.Ok sourceShared sourceVars).setState
                  (sourceStep sourceShared.toState values).1,
                (sourceStep sourceShared.toState values).2))
  target :
    ∀ state values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        Locals.InteractionSemantics.Primitive.openEval
            op state values.reverse =
          .done
            (.ok
              (state.withShared
                  { state.shared with
                    toState := (targetStep state.shared.toState values).1 },
                (targetStep state.shared.toState values).2))

namespace WorldSpec

theorem forward
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (spec : WorldSpec prim op)
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      rw [spec.sourceZero]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source op)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      let sourceResult := spec.sourceStep sourceShared.toState sourceValues
      let targetResult := spec.targetStep target.shared.toState sourceValues
      have hRelated :
          FunctionsInteractionRelation.WorldRel sourceResult.1 targetResult.1 ∧
            sourceResult.2 = targetResult.2 := by
        simpa [sourceResult, targetResult] using
          spec.related sourceShared.toState target.shared.toState
            sourceValues hShared.world
      have hStateRel :
          FunctionsInteractionRelation.StateRel
            (EvmYul.Yul.State.Ok sourceShared sourceVars) target :=
        ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
      have hFinalRel :=
        FunctionsInteractionRelation.StateRel.withWorldState hStateRel
          sourceResult.1 targetResult.1 hRelated.1
      have hDone :
          PrimitiveDoneRel (EvmYul.Yul.State.Ok sourceShared sourceVars) op
            (.ok
              ((EvmYul.Yul.State.Ok sourceShared sourceVars).setState
                  sourceResult.1,
                sourceResult.2))
            (.ok
              (target.withShared
                  { target.shared with toState := targetResult.1 },
                sourceResult.2)) :=
        .ok
          ⟨FunctionsInteractionPrimitive.ResultRel.refl_values
              hFinalRel sourceResult.2,
            by simpa [sourceResult] using
              spec.resultLength sourceShared.toState sourceValues hLength,
            rfl⟩
      have hTarget := spec.target target sourceValues hLength
      change
        Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse =
          .done
            (.ok
              (target.withShared
                  { target.shared with toState := targetResult.1 },
                targetResult.2)) at hTarget
      rw [← hRelated.2] at hTarget
      rw [show previous.succ + 1 = previous + 2 by omega,
        spec.sourceSucc previous sourceShared sourceVars sourceValues hLength]
      change
        Simulation.Interaction.ForwardRel Truncated
          (PrimitiveDoneRel (EvmYul.Yul.State.Ok sourceShared sourceVars) op)
          (.done
            (.ok
              ((EvmYul.Yul.State.Ok sourceShared sourceVars).setState
                  sourceResult.1,
                sourceResult.2)))
          (Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
      rw [hTarget]
      exact Simulation.Interaction.ForwardRel.done hDone

end WorldSpec

inductive WorldUnaryAccess :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.State .Yul → Word → EvmYul.State .Yul × Word) →
      (EvmYul.State .EVM → Word → EvmYul.State .EVM × Word) → Prop where
  | balance :
      WorldUnaryAccess (.Env .BALANCE) .balance
        EvmYul.State.balance EvmYul.State.balance
  | extcodesize :
      WorldUnaryAccess (.Env .EXTCODESIZE) .extcodesize
        EvmYul.State.extCodeSize EvmYul.State.extCodeSize
  | extcodehash :
      WorldUnaryAccess (.Env .EXTCODEHASH) .extcodehash
        Simulation.CodeErasedState.extCodeHash EvmYul.State.extCodeHash
  | sload :
      WorldUnaryAccess (.StackMemFlow .SLOAD) .sload
        EvmYul.State.sload EvmYul.State.sload
  | tload :
      WorldUnaryAccess (.StackMemFlow .TLOAD) .tload
        EvmYul.State.tload EvmYul.State.tload

namespace WorldUnaryAccess

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep : EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep) :
    Expressions.Structured.BasicOp.inputs op = 1 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep : EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep) :
    Expressions.Structured.BasicOp.outputs op = 1 := by
  cases hFamily <;> rfl

theorem related
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep : EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep)
    {source : EvmYul.State .Yul} {target : EvmYul.State .EVM}
    (hRel : FunctionsInteractionRelation.WorldRel source target)
    (value : Word) :
    FunctionsInteractionRelation.WorldRel
        (sourceStep source value).1 (targetStep target value).1 ∧
      (sourceStep source value).2 = (targetStep target value).2 := by
  let address := EvmYul.AccountAddress.ofUInt256 value
  cases hFamily with
  | balance =>
      constructor
      · simpa [EvmYul.State.balance, address] using
          hRel.addAccessedAccount address
      · simpa [EvmYul.State.balance, address,
          Simulation.OpenAccount.ofYul,
          Simulation.OpenAccount.ofEVM] using
          hRel.accountElimValueEq address (⟨0⟩ : Word)
            Simulation.OpenAccount.balance
  | extcodesize =>
      constructor
      · simpa [EvmYul.State.extCodeSize, address] using
          hRel.addAccessedAccount address
      · simpa [EvmYul.State.extCodeSize,
          EvmYul.State.lookupAccount, address,
          EvmYul.State.accountCodeImage,
          Simulation.OpenAccount.ofYul,
          Simulation.OpenAccount.ofEVM, Function.comp_def] using
          hRel.accountValueEq address (⟨0⟩ : Word)
            (fun account => EvmYul.UInt256.ofNat account.codeBytes.size)
  | extcodehash =>
      simpa [Simulation.CodeErasedState.extCodeHash_evm] using
        hRel.codeErasedExtCodeHash value
  | sload =>
      let owner := source.executionEnv.codeOwner
      have hTargetOwner : target.executionEnv.codeOwner = owner := by
        simpa [owner] using hRel.executionEnv.codeOwner.symm
      constructor
      · simpa [EvmYul.State.sload, owner, hTargetOwner] using
          hRel.addAccessedStorageKey (owner, value)
      · simpa [EvmYul.State.sload, EvmYul.State.lookupAccount,
          owner, hTargetOwner, Simulation.OpenAccount.ofYul,
          Simulation.OpenAccount.ofEVM,
          EvmYul.Account.lookupStorage] using
          hRel.accountValueEq owner (⟨0⟩ : Word)
            (fun account => account.storage.findD value ⟨0⟩)
  | tload =>
      let owner := source.executionEnv.codeOwner
      have hTargetOwner : target.executionEnv.codeOwner = owner := by
        simpa [owner] using hRel.executionEnv.codeOwner.symm
      constructor
      · simpa [EvmYul.State.tload] using hRel
      · simpa [EvmYul.State.tload, EvmYul.State.lookupAccount,
          owner, hTargetOwner, Simulation.OpenAccount.ofYul,
          Simulation.OpenAccount.ofEVM,
          EvmYul.Account.lookupTransientStorage] using
          hRel.accountValueEq owner (⟨0⟩ : Word)
            (fun account => account.transientStorage.findD value ⟨0⟩)

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep : EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep) :
    WorldSpec prim op where
  sourceStep world values :=
    match values with
    | [value] =>
        let result := sourceStep world value
        (result.1, [result.2])
    | _ => (world, [])
  targetStep world values :=
    match values with
    | [value] =>
        let result := targetStep world value
        (result.1, [result.2])
    | _ => (world, [])
  resultLength := by
    intro world values hLength
    have hLengthOne : values.length = 1 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    simpa [hFamily.outputs]
  related := by
    intro source target values hRel
    cases values with
    | nil => exact ⟨hRel, rfl⟩
    | cons value rest =>
        cases rest with
        | cons next tail => exact ⟨hRel, rfl⟩
        | nil => simpa using hFamily.related hRel value
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hLengthOne : values.length = 1 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    cases hFamily with
    | extcodehash =>
        simp [Yul.InteractionSemantics.Primitive.openEval,
          Yul.InteractionSemantics.Primitive.closedEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?,
          EvmYul.Yul.unaryStateOp,
          EvmYul.Yul.State.setState,
          EvmYul.Yul.State.setSharedState, Except.map]
        exact ⟨⟨rfl, rfl⟩, rfl⟩
    | balance | extcodesize | sload | tload =>
        simp [Yul.InteractionSemantics.Primitive.openEval,
          Yul.InteractionSemantics.Primitive.closedEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
          EvmYul.Yul.unaryStateOp,
          EvmYul.Yul.State.setState,
          EvmYul.Yul.State.setSharedState]
        unfold EvmYul.step
        rfl
  target := by
    intro state values hLength
    have hLengthOne : values.length = 1 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.unaryState targetStep) := by
      cases hFamily <;> rfl
    let result := targetStep state.shared.toState value
    change
      Locals.InteractionSemantics.Primitive.openEval op state [value] =
        .done
          (.ok
            (state.withShared
              { state.shared with toState := result.1 }, [result.2]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep
      (by cases hFamily <;> decide) (by cases hFamily <;> decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → EvmYul.State .Yul × Word}
    {targetStep : EvmYul.State .EVM → Word → EvmYul.State .EVM × Word}
    {sourceValues : List Word}
    (hFamily : WorldUnaryAccess prim op sourceStep targetStep)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end WorldUnaryAccess

/-- Closed world writes share a deterministic permitted transition and an
exact static-mode failure on both sides. -/
structure WorldWriteSpec (prim : EvmYul.Operation .Yul)
    (op : Structured.BasicOp) where
  sourceStep :
    EvmYul.State .Yul → List Word → EvmYul.State .Yul × List Word
  targetStep :
    EvmYul.State .EVM → List Word → EvmYul.State .EVM × List Word
  resultLength :
    ∀ world values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        (sourceStep world values).2.length =
          Expressions.Structured.BasicOp.outputs op
  related :
    ∀ sourceWorld targetWorld values,
      FunctionsInteractionRelation.WorldRel sourceWorld targetWorld →
        FunctionsInteractionRelation.WorldRel
            (sourceStep sourceWorld values).1
            (targetStep targetWorld values).1 ∧
          (sourceStep sourceWorld values).2 =
            (targetStep targetWorld values).2
  sourceZero :
    ∀ source values,
      Yul.InteractionSemantics.Primitive.openEval 1 source prim values =
        .done
          (.error
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure))
  sourceAllowed :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        sourceShared.executionEnv.perm = true →
          Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
              (EvmYul.Yul.State.Ok sourceShared sourceVars) prim values =
            .done
              (.ok
                ((EvmYul.Yul.State.Ok sourceShared sourceVars).setState
                    (sourceStep sourceShared.toState values).1,
                  (sourceStep sourceShared.toState values).2))
  sourceDenied :
    ∀ fuel sourceShared sourceVars values,
      values.length = Expressions.Structured.BasicOp.inputs op →
        sourceShared.executionEnv.perm = false →
          Yul.InteractionSemantics.Primitive.openEval (fuel + 2)
              (EvmYul.Yul.State.Ok sourceShared sourceVars) prim values =
            .done
              (.error
                ({ exception := .StaticModeViolation,
                    state := EvmYul.Yul.State.Ok sourceShared sourceVars } :
                  Yul.InteractionSemantics.Failure))
  targetAllowed :
    ∀ (state : Functions.InteractionSemantics.State)
      (values : List Word),
      values.length = Expressions.Structured.BasicOp.inputs op →
        state.shared.executionEnv.perm = true →
          Locals.InteractionSemantics.Primitive.openEval
              op state values.reverse =
            .done
              (.ok
                (state.withShared
                    { state.shared with
                      toState := (targetStep state.shared.toState values).1 },
                  (targetStep state.shared.toState values).2))
  targetDenied :
    ∀ (state : Functions.InteractionSemantics.State)
      (values : List Word),
      values.length = Expressions.Structured.BasicOp.inputs op →
        state.shared.executionEnv.perm = false →
          Locals.InteractionSemantics.Primitive.openEval
              op state values.reverse =
            .done (.error .StaticModeViolation)

namespace WorldWriteSpec

theorem forward
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    (spec : WorldWriteSpec prim op)
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      rw [spec.sourceZero]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source op)
          (right := Locals.InteractionSemantics.Primitive.openEval
            op target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      cases hPermission : sourceShared.executionEnv.perm with
      | false =>
          have hTargetPermission :
              target.shared.executionEnv.perm = false := by
            simpa [hPermission] using hShared.executionEnv.permission.symm
          rw [show previous.succ + 1 = previous + 2 by omega,
            spec.sourceDenied previous sourceShared sourceVars sourceValues
              hLength hPermission,
            spec.targetDenied target sourceValues hLength hTargetPermission]
          exact
            Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.error trivial)
      | true =>
          have hTargetPermission :
              target.shared.executionEnv.perm = true := by
            simpa [hPermission] using hShared.executionEnv.permission.symm
          let sourceResult :=
            spec.sourceStep sourceShared.toState sourceValues
          let targetResult :=
            spec.targetStep target.shared.toState sourceValues
          have hRelated :
              FunctionsInteractionRelation.WorldRel
                  sourceResult.1 targetResult.1 ∧
                sourceResult.2 = targetResult.2 := by
            simpa [sourceResult, targetResult] using
              spec.related sourceShared.toState target.shared.toState
                sourceValues hShared.world
          have hStateRel :
              FunctionsInteractionRelation.StateRel
                (EvmYul.Yul.State.Ok sourceShared sourceVars) target :=
            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
          have hFinalRel :=
            FunctionsInteractionRelation.StateRel.withWorldState hStateRel
              sourceResult.1 targetResult.1 hRelated.1
          have hDone :
              PrimitiveDoneRel
                (EvmYul.Yul.State.Ok sourceShared sourceVars) op
                (.ok
                  ((EvmYul.Yul.State.Ok sourceShared sourceVars).setState
                      sourceResult.1,
                    sourceResult.2))
                (.ok
                  (target.withShared
                      { target.shared with toState := targetResult.1 },
                    sourceResult.2)) :=
            .ok
              ⟨FunctionsInteractionPrimitive.ResultRel.refl_values
                  hFinalRel sourceResult.2,
                by simpa [sourceResult] using
                  spec.resultLength sourceShared.toState sourceValues hLength,
                rfl⟩
          have hTarget :=
            spec.targetAllowed target sourceValues hLength hTargetPermission
          change
            Locals.InteractionSemantics.Primitive.openEval
                op target sourceValues.reverse =
              .done
                (.ok
                  (target.withShared
                      { target.shared with toState := targetResult.1 },
                    targetResult.2)) at hTarget
          rw [← hRelated.2] at hTarget
          rw [show previous.succ + 1 = previous + 2 by omega,
            spec.sourceAllowed previous sourceShared sourceVars sourceValues
              hLength hPermission]
          change
            Simulation.Interaction.ForwardRel Truncated
              (PrimitiveDoneRel
                (EvmYul.Yul.State.Ok sourceShared sourceVars) op)
              (.done
                (.ok
                  ((EvmYul.Yul.State.Ok sourceShared sourceVars).setState
                      sourceResult.1,
                    sourceResult.2)))
              (Locals.InteractionSemantics.Primitive.openEval
                op target sourceValues.reverse)
          rw [hTarget]
          exact Simulation.Interaction.ForwardRel.done hDone

end WorldWriteSpec

inductive WorldBinaryWrite :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.State .Yul → Word → Word → EvmYul.State .Yul) →
      (EvmYul.State .EVM → Word → Word → EvmYul.State .EVM) → Prop where
  | sstore :
      WorldBinaryWrite (.StackMemFlow .SSTORE) .sstore
        EvmYul.State.sstore EvmYul.State.sstore
  | tstore :
      WorldBinaryWrite (.StackMemFlow .TSTORE) .tstore
        EvmYul.State.tstore EvmYul.State.tstore

namespace WorldBinaryWrite

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep : EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep) :
    Expressions.Structured.BasicOp.inputs op = 2 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep : EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep) :
    Expressions.Structured.BasicOp.outputs op = 0 := by
  cases hFamily <;> rfl

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep : EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep) :
    WorldWriteSpec prim op where
  sourceStep world values :=
    match values with
    | [key, value] => (sourceStep world key value, [])
    | _ => (world, [])
  targetStep world values :=
    match values with
    | [key, value] => (targetStep world key value, [])
    | _ => (world, [])
  resultLength := by
    intro world values hLength
    rw [hFamily.outputs]
    cases values with
    | nil => rfl
    | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second extra => cases extra <;> rfl
  related := by
    intro source target values hRel
    cases values with
    | nil => exact ⟨hRel, rfl⟩
    | cons key rest =>
        cases rest with
        | nil => exact ⟨hRel, rfl⟩
        | cons value extra =>
            cases extra with
            | cons next tail => exact ⟨hRel, rfl⟩
            | nil =>
                constructor
                · cases hFamily with
                  | sstore => exact hRel.sstore key value
                  | tstore => exact hRel.tstore key value
                · rfl
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceAllowed := by
    intro fuel sourceShared sourceVars values hLength hPermission
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨key, value, rfl⟩ := List.length_eq_two.mp hLengthTwo
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.State.executionEnv,
        EvmYul.Yul.binaryStateOp, EvmYul.Yul.State.setState,
        EvmYul.Yul.State.setSharedState, hPermission] <;>
      unfold EvmYul.step <;> rfl
  sourceDenied := by
    intro fuel sourceShared sourceVars values hLength hPermission
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨key, value, rfl⟩ := List.length_eq_two.mp hLengthTwo
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.State.executionEnv, hPermission] <;>
      unfold EvmYul.step <;> rfl
  targetAllowed := by
    intro state values hLength hPermission
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨key, value, rfl⟩ := List.length_eq_two.mp hLengthTwo
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.binaryState targetStep) := by
      cases hFamily <;> rfl
    let result := targetStep state.shared.toState key value
    change
      Locals.InteractionSemantics.Primitive.openEval
          op state [value, key] =
        .done
          (.ok
            (state.withShared
              { state.shared with toState := result }, []))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep
      (by cases hFamily <;> decide) (by cases hFamily <;> decide)]
    cases hFamily <;>
      simp [Assembly.PrimStep.run, EvmYul.EVM.binaryStateOp,
        Locals.InteractionSemantics.Primitive.finish,
        Locals.InteractionSemantics.Primitive.isolated,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.pop2,
        Locals.Source.State.withShared, Simulation.Interaction.map,
        Simulation.Interaction.bind, Simulation.Interaction.pure,
        hPermission, result] <;> rfl
  targetDenied := by
    intro state values hLength hPermission
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨key, value, rfl⟩ := List.length_eq_two.mp hLengthTwo
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.binaryState targetStep) := by
      cases hFamily <;> rfl
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep
      (by cases hFamily <;> decide) (by cases hFamily <;> decide)]
    cases hFamily <;>
      simp [Assembly.PrimStep.run, EvmYul.EVM.binaryStateOp,
        Locals.InteractionSemantics.Primitive.isolated,
        Simulation.Interaction.map, Simulation.Interaction.bind,
        hPermission]

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceStep : EvmYul.State .Yul → Word → Word → EvmYul.State .Yul}
    {targetStep : EvmYul.State .EVM → Word → Word → EvmYul.State .EVM}
    {sourceValues : List Word}
    (hFamily : WorldBinaryWrite prim op sourceStep targetStep)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end WorldBinaryWrite

/-- Pure two-input operations whose Yul and Functions meanings are the same
word function and leave shared state unchanged. -/
inductive PureBinary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      EvmYul.Primop.Binary → Prop where
  | add : PureBinary (.StopArith .ADD) .add EvmYul.UInt256.add
  | mul : PureBinary (.StopArith .MUL) .mul EvmYul.UInt256.mul
  | sub : PureBinary (.StopArith .SUB) .sub EvmYul.UInt256.sub
  | div : PureBinary (.StopArith .DIV) .div EvmYul.UInt256.div
  | sdiv : PureBinary (.StopArith .SDIV) .sdiv EvmYul.UInt256.sdiv
  | mod : PureBinary (.StopArith .MOD) .mod EvmYul.UInt256.mod
  | smod : PureBinary (.StopArith .SMOD) .smod EvmYul.UInt256.smod
  | exp : PureBinary (.StopArith .EXP) .exp EvmYul.UInt256.exp
  | signextend :
      PureBinary (.StopArith .SIGNEXTEND) .signextend
        EvmYul.UInt256.signextend
  | lt : PureBinary (.CompBit .LT) .lt EvmYul.UInt256.lt
  | gt : PureBinary (.CompBit .GT) .gt EvmYul.UInt256.gt
  | slt : PureBinary (.CompBit .SLT) .slt EvmYul.UInt256.slt
  | sgt : PureBinary (.CompBit .SGT) .sgt EvmYul.UInt256.sgt
  | eq : PureBinary (.CompBit .EQ) .eq EvmYul.UInt256.eq
  | and : PureBinary (.CompBit .AND) .and EvmYul.UInt256.land
  | or : PureBinary (.CompBit .OR) .or EvmYul.UInt256.lor
  | xor : PureBinary (.CompBit .XOR) .xor EvmYul.UInt256.xor
  | byte : PureBinary (.CompBit .BYTE) .byte EvmYul.UInt256.byteAt
  | shl :
      PureBinary (.CompBit .SHL) .shl
        (flip EvmYul.UInt256.shiftLeft)
  | shr :
      PureBinary (.CompBit .SHR) .shr
        (flip EvmYul.UInt256.shiftRight)
  | sar : PureBinary (.CompBit .SAR) .sar EvmYul.UInt256.sar

namespace PureBinary

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary} (hFamily : PureBinary prim op f) :
    Expressions.Structured.BasicOp.inputs op = 2 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary} (hFamily : PureBinary prim op f) :
    Expressions.Structured.BasicOp.outputs op = 1 := by
  cases hFamily <;> rfl

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary} (hFamily : PureBinary prim op f) :
    PureSpec prim op where
  result values :=
    match values with
    | [left, right] => [f left right]
    | _ => []
  resultLength := by
    intro values hLength
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hLengthTwo
    simpa [hFamily.outputs]
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hLengthTwo
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.execBinOp] <;>
      unfold EvmYul.step <;> rfl
  target := by
    intro state values hLength
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hLengthTwo
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.bin f) := by
      cases hFamily <;> rfl
    have hGas : op.toPrimOp ≠ .gas := by
      cases hFamily <;> decide
    have hMsize : op.toPrimOp ≠ .msize := by
      cases hFamily <;> decide
    change
      Locals.InteractionSemantics.Primitive.openEval
          op state [right, left] =
        .done (.ok (state, [f left right]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep hGas hMsize]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary} {sourceValues : List Word}
    (hFamily : PureBinary prim op f)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end PureBinary

inductive PureUnary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      EvmYul.Primop.Unary → Prop where
  | iszero : PureUnary (.CompBit .ISZERO) .iszero EvmYul.UInt256.isZero
  | not : PureUnary (.CompBit .NOT) .not EvmYul.UInt256.lnot

namespace PureUnary

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Unary} (hFamily : PureUnary prim op f) :
    Expressions.Structured.BasicOp.inputs op = 1 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Unary} (hFamily : PureUnary prim op f) :
    Expressions.Structured.BasicOp.outputs op = 1 := by
  cases hFamily <;> rfl

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Unary} (hFamily : PureUnary prim op f) :
    PureSpec prim op where
  result values :=
    match values with
    | [value] => [f value]
    | _ => []
  resultLength := by
    intro values hLength
    have hLengthOne : values.length = 1 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    simpa [hFamily.outputs]
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hLengthOne : values.length = 1 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.execUnOp] <;>
      unfold EvmYul.step <;> rfl
  target := by
    intro state values hLength
    have hLengthOne : values.length = 1 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLengthOne
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.un f) := by
      cases hFamily <;> rfl
    have hGas : op.toPrimOp ≠ .gas := by
      cases hFamily <;> decide
    have hMsize : op.toPrimOp ≠ .msize := by
      cases hFamily <;> decide
    change
      Locals.InteractionSemantics.Primitive.openEval op state [value] =
        .done (.ok (state, [f value]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep hGas hMsize]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Unary} {sourceValues : List Word}
    (hFamily : PureUnary prim op f)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end PureUnary

inductive PureTernary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      EvmYul.Primop.Ternary → Prop where
  | addmod :
      PureTernary (.StopArith .ADDMOD) .addmod EvmYul.UInt256.addMod
  | mulmod :
      PureTernary (.StopArith .MULMOD) .mulmod EvmYul.UInt256.mulMod

namespace PureTernary

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Ternary} (hFamily : PureTernary prim op f) :
    Expressions.Structured.BasicOp.inputs op = 3 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Ternary} (hFamily : PureTernary prim op f) :
    Expressions.Structured.BasicOp.outputs op = 1 := by
  cases hFamily <;> rfl

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Ternary} (hFamily : PureTernary prim op f) :
    PureSpec prim op where
  result values :=
    match values with
    | [first, second, third] => [f first second third]
    | _ => []
  resultLength := by
    intro values hLength
    have hLengthThree : values.length = 3 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨first, second, third, rfl⟩ :=
      List.length_eq_three.mp hLengthThree
    simpa [hFamily.outputs]
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hLengthThree : values.length = 3 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨first, second, third, rfl⟩ :=
      List.length_eq_three.mp hLengthThree
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.execTriOp] <;>
      unfold EvmYul.step <;> rfl
  target := by
    intro state values hLength
    have hLengthThree : values.length = 3 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨first, second, third, rfl⟩ :=
      List.length_eq_three.mp hLengthThree
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.tri f) := by
      cases hFamily <;> rfl
    have hGas : op.toPrimOp ≠ .gas := by
      cases hFamily <;> decide
    have hMsize : op.toPrimOp ≠ .msize := by
      cases hFamily <;> decide
    change
      Locals.InteractionSemantics.Primitive.openEval
          op state [third, second, first] =
        .done (.ok (state, [f first second third]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep hGas hMsize]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Ternary} {sourceValues : List Word}
    (hFamily : PureTernary prim op f)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end PureTernary

inductive MachineBinaryZero :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.MachineState → Word → Word → EvmYul.MachineState) → Prop where
  | mstore :
      MachineBinaryZero (.StackMemFlow .MSTORE) .mstore
        EvmYul.MachineState.mstore
  | mstore8 :
      MachineBinaryZero (.StackMemFlow .MSTORE8) .mstore8
        EvmYul.MachineState.mstore8

namespace MachineBinaryZero

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    (hFamily : MachineBinaryZero prim op f) :
    Expressions.Structured.BasicOp.inputs op = 2 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    (hFamily : MachineBinaryZero prim op f) :
    Expressions.Structured.BasicOp.outputs op = 0 := by
  cases hFamily <;> rfl

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    (hFamily : MachineBinaryZero prim op f) : MachineSpec prim op where
  result machine values :=
    match values with
    | [left, right] => (f machine left right, [])
    | _ => (machine, [])
  resultLength := by
    intro machine values hLength
    rw [hFamily.outputs]
    cases values with
    | nil => rfl
    | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second extra =>
            cases extra <;> rfl
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hLengthTwo
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.binaryMachineStateOp,
        EvmYul.Yul.State.setMachineState,
        EvmYul.Yul.State.setSharedState] <;>
      unfold EvmYul.step <;> rfl
  target := by
    intro state values hLength
    have hLengthTwo : values.length = 2 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hLengthTwo
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.binaryMachineState f) := by
      cases hFamily <;> rfl
    have hGas : op.toPrimOp ≠ .gas := by
      cases hFamily <;> decide
    have hMsize : op.toPrimOp ≠ .msize := by
      cases hFamily <;> decide
    change
      Locals.InteractionSemantics.Primitive.openEval
          op state [right, left] =
        .done
          (.ok
            (state.withShared
              { state.shared with
                toMachineState :=
                  f state.shared.toMachineState left right }, []))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep hGas hMsize]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.MachineState → Word → Word → EvmYul.MachineState}
    {sourceValues : List Word}
    (hFamily : MachineBinaryZero prim op f)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end MachineBinaryZero

namespace MachineMCopy

def spec : MachineSpec (.StackMemFlow .MCOPY) .mcopy where
  result machine values :=
    match values with
    | [destination, readStart, size] =>
        (machine.mcopy destination readStart size, [])
    | _ => (machine, [])
  resultLength := by
    intro machine values hLength
    cases values with
    | nil => rfl
    | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second rest =>
            cases rest with
            | nil => rfl
            | cons third extra =>
                cases extra <;> rfl
  sourceZero := by
    intro source values
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.InteractionSemantics.State.afterException,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    obtain ⟨destination, readStart, size, rfl⟩ :=
      List.length_eq_three.mp hLength
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
      EvmYul.Yul.ternaryMachineStateOp,
      EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.setSharedState]
    unfold EvmYul.step
    rfl
  target := by
    intro state values hLength
    obtain ⟨destination, readStart, size, rfl⟩ :=
      List.length_eq_three.mp hLength
    change
      Locals.InteractionSemantics.Primitive.openEval .mcopy state
          [size, readStart, destination] =
        .done
          (.ok
            (state.withShared
              { state.shared with
                toMachineState :=
                  state.shared.toMachineState.mcopy
                    destination readStart size }, []))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength : sourceValues.length = 3)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source .mcopy)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source (.StackMemFlow .MCOPY) sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        .mcopy target sourceValues.reverse) :=
  spec.forward hLength hRel

end MachineMCopy

namespace MachineMLoad

def result (machine : EvmYul.MachineState) (values : List Word) :
    EvmYul.MachineState × List Word :=
  match values with
  | [address] =>
      let loaded := machine.mload address
      (loaded.2, [loaded.1])
  | _ => (machine, [])

def spec : MachineSpec (.StackMemFlow .MLOAD) .mload where
  result := result
  resultLength := by
    intro machine values hLength
    obtain ⟨address, rfl⟩ := List.length_eq_one_iff.mp hLength
    rfl
  sourceZero := by
    intro source values
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.InteractionSemantics.State.afterException,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    obtain ⟨address, rfl⟩ := List.length_eq_one_iff.mp hLength
    simp [result, Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
      EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.setSharedState]
    unfold EvmYul.step
    rfl
  target := by
    intro state values hLength
    obtain ⟨address, rfl⟩ := List.length_eq_one_iff.mp hLength
    let loaded := state.shared.toMachineState.mload address
    change
      Locals.InteractionSemantics.Primitive.openEval .mload state [address] =
        .done
          (.ok
            (state.withShared
              { state.shared with toMachineState := loaded.2 }, [loaded.1]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength : sourceValues.length = 1)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source .mload)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source (.StackMemFlow .MLOAD) sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        .mload target sourceValues.reverse) :=
  spec.forward hLength hRel

end MachineMLoad

namespace MachineKeccak256

def result (machine : EvmYul.MachineState) (values : List Word) :
    EvmYul.MachineState × List Word :=
  match values with
  | [address, size] =>
      let hashed := machine.keccak256 address size
      (hashed.2, [hashed.1])
  | _ => (machine, [])

def spec : MachineSpec (.Keccak .KECCAK256) .keccak256 where
  result := result
  resultLength := by
    intro machine values hLength
    obtain ⟨address, size, rfl⟩ := List.length_eq_two.mp hLength
    rfl
  sourceZero := by
    intro source values
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.InteractionSemantics.State.afterException,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    obtain ⟨address, size, rfl⟩ := List.length_eq_two.mp hLength
    simp [result, Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
      EvmYul.Yul.binaryMachineStateOp',
      EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.setSharedState]
    unfold EvmYul.step
    rfl
  target := by
    intro state values hLength
    obtain ⟨address, size, rfl⟩ := List.length_eq_two.mp hLength
    let hashed := state.shared.toMachineState.keccak256 address size
    change
      Locals.InteractionSemantics.Primitive.openEval
          .keccak256 state [size, address] =
        .done
          (.ok
            (state.withShared
              { state.shared with toMachineState := hashed.2 }, [hashed.1]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength : sourceValues.length = 2)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source .keccak256)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source (.Keccak .KECCAK256) sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        .keccak256 target sourceValues.reverse) :=
  spec.forward hLength hRel

end MachineKeccak256

namespace MachineReturnDataSize

def spec : MachineSpec (.Env .RETURNDATASIZE) .returndatasize where
  result machine values :=
    match values with
    | [] => (machine, [machine.returndatasize])
    | _ => (machine, [])
  resultLength := by
    intro machine values hLength
    have hValues : values = [] := List.eq_nil_of_length_eq_zero hLength
    subst values
    rfl
  sourceZero := by
    intro source values
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.InteractionSemantics.State.afterException,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hValues : values = [] := List.eq_nil_of_length_eq_zero hLength
    subst values
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
    unfold EvmYul.step
    rfl
  target := by
    intro state values hLength
    have hValues : values = [] := List.eq_nil_of_length_eq_zero hLength
    subst values
    change
      Locals.InteractionSemantics.Primitive.openEval
          .returndatasize state [] =
        .done
          (.ok
            (state.withShared
              { state.shared with
                toMachineState := state.shared.toMachineState },
              [state.shared.toMachineState.returndatasize]))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength : sourceValues.length = 0)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source .returndatasize)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source (.Env .RETURNDATASIZE) sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        .returndatasize target sourceValues.reverse) :=
  spec.forward hLength hRel

end MachineReturnDataSize

namespace MachinePop

def spec : MachineSpec (.StackMemFlow .POP) .pop where
  result machine values :=
    match values with
    | [_] => (machine, [])
    | _ => (machine, [])
  resultLength := by
    intro machine values hLength
    cases values with
    | nil => rfl
    | cons first rest =>
        cases rest <;> rfl
  sourceZero := by
    intro source values
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.InteractionSemantics.State.afterException,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLength
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
    unfold EvmYul.step
    rfl
  target := by
    intro state values hLength
    obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLength
    change
      Locals.InteractionSemantics.Primitive.openEval .pop state [value] =
        .done
          (.ok
            (state.withShared
              { state.shared with
                toMachineState := state.shared.toMachineState }, []))
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
    rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength : sourceValues.length = 1)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source .pop)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source (.StackMemFlow .POP) sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        .pop target sourceValues.reverse) :=
  spec.forward hLength hRel

end MachinePop

inductive SharedTernaryCopy :
    EvmYul.Operation .Yul → Structured.BasicOp →
      (EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul) →
      (EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM) → Prop where
  | calldatacopy :
      SharedTernaryCopy (.Env .CALLDATACOPY) .calldatacopy
        EvmYul.SharedState.calldatacopy
        EvmYul.SharedState.calldatacopy
  | codecopy :
      SharedTernaryCopy (.Env .CODECOPY) .codecopy
        EvmYul.SharedState.codeBytesCopy
        EvmYul.SharedState.codeCopy

namespace SharedTernaryCopy

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy) :
    Expressions.Structured.BasicOp.inputs op = 3 := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy) :
    Expressions.Structured.BasicOp.outputs op = 0 := by
  cases hFamily <;> rfl

theorem related
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy)
    {source : EvmYul.SharedState .Yul}
    {target : EvmYul.SharedState .EVM}
    (hRel : FunctionsInteractionRelation.SharedRel source target)
    (destination readStart size : Word) :
    FunctionsInteractionRelation.SharedRel
      (sourceCopy source destination readStart size)
      (targetCopy target destination readStart size) := by
  cases hFamily with
  | calldatacopy =>
      exact
        { openWorld := by
            simpa [EvmYul.SharedState.calldatacopy] using hRel.openWorld
          machine := by
            simp [EvmYul.SharedState.calldatacopy, hRel.machine,
              hRel.executionEnv.calldata]
          initialAccounts := by
            simpa [EvmYul.SharedState.calldatacopy] using hRel.initialAccounts
          totalGasUsedInBlock := by
            simpa [EvmYul.SharedState.calldatacopy] using
              hRel.totalGasUsedInBlock
          transactionReceipts := by
            simpa [EvmYul.SharedState.calldatacopy] using
              hRel.transactionReceipts
          executionEnv := by
            simpa [EvmYul.SharedState.calldatacopy] using hRel.executionEnv
          blocks := by
            simpa [EvmYul.SharedState.calldatacopy] using hRel.blocks
          genesisBlockHeader := by
            simpa [EvmYul.SharedState.calldatacopy] using
              hRel.genesisBlockHeader }
  | codecopy =>
      exact
        { openWorld := by
            simpa [EvmYul.SharedState.codeBytesCopy,
              EvmYul.SharedState.codeCopy] using hRel.openWorld
          machine := by
            simp [EvmYul.SharedState.codeBytesCopy,
              EvmYul.SharedState.codeCopy, hRel.machine,
              hRel.executionEnv.codeImage]
          initialAccounts := by
            simpa [EvmYul.SharedState.codeBytesCopy,
              EvmYul.SharedState.codeCopy] using hRel.initialAccounts
          totalGasUsedInBlock := by
            simpa [EvmYul.SharedState.codeBytesCopy,
              EvmYul.SharedState.codeCopy] using hRel.totalGasUsedInBlock
          transactionReceipts := by
            simpa [EvmYul.SharedState.codeBytesCopy,
              EvmYul.SharedState.codeCopy] using hRel.transactionReceipts
          executionEnv := by
            simpa [EvmYul.SharedState.codeBytesCopy,
              EvmYul.SharedState.codeCopy] using hRel.executionEnv
          blocks := by
            simpa [EvmYul.SharedState.codeBytesCopy,
              EvmYul.SharedState.codeCopy] using hRel.blocks
          genesisBlockHeader := by
            simpa [EvmYul.SharedState.codeBytesCopy,
              EvmYul.SharedState.codeCopy] using hRel.genesisBlockHeader }

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy) :
    SharedSpec prim op where
  sourceResult shared values :=
    match values with
    | [destination, readStart, size] =>
        (sourceCopy shared destination readStart size, [])
    | _ => (shared, [])
  targetResult shared values :=
    match values with
    | [destination, readStart, size] =>
        (targetCopy shared destination readStart size, [])
    | _ => (shared, [])
  resultLength := by
    intro shared values hLength
    rw [hFamily.outputs]
    cases values with
    | nil => rfl
    | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second rest =>
            cases rest with
            | nil => rfl
            | cons third extra => cases extra <;> rfl
  related := by
    intro source target values hRel
    cases values with
    | nil => exact ⟨hRel, rfl⟩
    | cons destination rest =>
        cases rest with
        | nil => exact ⟨hRel, rfl⟩
        | cons readStart rest =>
            cases rest with
            | nil => exact ⟨hRel, rfl⟩
            | cons size extra =>
                cases extra with
                | nil => exact ⟨hFamily.related hRel destination readStart size, rfl⟩
                | cons next tail => exact ⟨hRel, rfl⟩
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    have hLengthThree : values.length = 3 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨destination, readStart, size, rfl⟩ :=
      List.length_eq_three.mp hLengthThree
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
        EvmYul.Yul.ternaryCopyOp, EvmYul.Yul.State.setSharedState] <;>
      unfold EvmYul.step <;> rfl
  target := by
    intro state values hLength
    have hLengthThree : values.length = 3 := by
      simpa [hFamily.inputs] using hLength
    obtain ⟨destination, readStart, size, rfl⟩ :=
      List.length_eq_three.mp hLengthThree
    have hSupports :
        Locals.InteractionSemantics.Primitive.supportsOpen op = true := by
      cases hFamily <;> rfl
    have hStep :
        Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
          some (.ternaryCopy targetCopy) := by
      cases hFamily <;> rfl
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by simpa [hFamily.inputs]) hSupports hStep
      (by cases hFamily <;> decide) (by cases hFamily <;> decide)]
    cases hFamily <;>
      simp [Assembly.PrimStep.run, EvmYul.EVM.ternaryCopyOp,
        Locals.InteractionSemantics.Primitive.finish,
        Locals.InteractionSemantics.Primitive.isolated,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, EvmYul.Stack.pop3,
        Locals.Source.State.withShared, Simulation.Interaction.map,
        Simulation.Interaction.bind, Simulation.Interaction.pure] <;> rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceCopy :
      EvmYul.SharedState .Yul → Word → Word → Word →
        EvmYul.SharedState .Yul}
    {targetCopy :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM}
    {sourceValues : List Word}
    (hFamily : SharedTernaryCopy prim op sourceCopy targetCopy)
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward hLength hRel

end SharedTernaryCopy

namespace SharedExtCodeCopy

def spec : SharedSpec (.Env .EXTCODECOPY) .extcodecopy where
  sourceResult shared values :=
    match values with
    | [account, destination, readStart, size] =>
        (EvmYul.SharedState.extCodeCopy'
          shared account destination readStart size, [])
    | _ => (shared, [])
  targetResult shared values :=
    match values with
    | [account, destination, readStart, size] =>
        (EvmYul.SharedState.extCodeCopy'
          shared account destination readStart size, [])
    | _ => (shared, [])
  resultLength := by
    intro shared values hLength
    cases values with
    | nil => rfl
    | cons first rest =>
        cases rest with
        | nil => rfl
        | cons second rest =>
            cases rest with
            | nil => rfl
            | cons third rest =>
                cases rest with
                | nil => rfl
                | cons fourth extra => cases extra <;> rfl
  related := by
    intro source target values hRel
    cases values with
    | nil => exact ⟨hRel, rfl⟩
    | cons account rest =>
        cases rest with
        | nil => exact ⟨hRel, rfl⟩
        | cons destination rest =>
            cases rest with
            | nil => exact ⟨hRel, rfl⟩
            | cons readStart rest =>
                cases rest with
                | nil => exact ⟨hRel, rfl⟩
                | cons size extra =>
                    cases extra with
                    | nil =>
                        exact
                          ⟨hRel.extCodeCopy account destination readStart size,
                            rfl⟩
                    | cons next tail => exact ⟨hRel, rfl⟩
  sourceZero := by
    intro source values
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.InteractionSemantics.State.afterException,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceSucc := by
    intro fuel sourceShared sourceVars values hLength
    obtain ⟨account, destination, readStart, size, rfl⟩ :=
      List.length_eq_four.mp hLength
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
      EvmYul.Yul.quaternaryCopyOp,
      EvmYul.Yul.State.setSharedState]
    unfold EvmYul.step
    rfl
  target := by
    intro state values hLength
    obtain ⟨account, destination, readStart, size, rfl⟩ :=
      List.length_eq_four.mp hLength
    rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
      (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
    simp [Assembly.PrimStep.run, EvmYul.EVM.quaternaryCopyOp,
      Locals.InteractionSemantics.Primitive.finish,
      Locals.InteractionSemantics.Primitive.isolated,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, EvmYul.Stack.pop4,
      Locals.Source.State.withShared, Simulation.Interaction.map,
      Simulation.Interaction.bind, Simulation.Interaction.pure] <;> rfl

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength : sourceValues.length = 4)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source .extcodecopy)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source (.Env .EXTCODECOPY) sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        .extcodecopy target sourceValues.reverse) :=
  spec.forward hLength hRel

end SharedExtCodeCopy

inductive LogFamily :
    EvmYul.Operation .Yul → Structured.BasicOp → Nat → Type where
  | log0 : LogFamily (.Log .LOG0) .log0 2
  | log1 : LogFamily (.Log .LOG1) .log1 3
  | log2 : LogFamily (.Log .LOG2) .log2 4
  | log3 : LogFamily (.Log .LOG3) .log3 5
  | log4 : LogFamily (.Log .LOG4) .log4 6

namespace LogFamily

def result {τ : EvmYul.OperationType}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp} {arity : Nat}
    (hFamily : LogFamily prim op arity)
    (shared : EvmYul.SharedState τ) (values : List Word) :
    EvmYul.SharedState τ × List Word :=
  match hFamily with
  | .log0 =>
      match values with
      | [offset, size] =>
          (EvmYul.SharedState.logOp offset size #[] shared, [])
      | _ => (shared, [])
  | .log1 =>
      match values with
      | [offset, size, topic0] =>
          (EvmYul.SharedState.logOp offset size #[topic0] shared, [])
      | _ => (shared, [])
  | .log2 =>
      match values with
      | [offset, size, topic0, topic1] =>
          (EvmYul.SharedState.logOp offset size #[topic0, topic1] shared, [])
      | _ => (shared, [])
  | .log3 =>
      match values with
      | [offset, size, topic0, topic1, topic2] =>
          (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2]
            shared, [])
      | _ => (shared, [])
  | .log4 =>
      match values with
      | [offset, size, topic0, topic1, topic2, topic3] =>
          (EvmYul.SharedState.logOp offset size
            #[topic0, topic1, topic2, topic3] shared, [])
      | _ => (shared, [])

theorem inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp} {arity : Nat}
    (hFamily : LogFamily prim op arity) :
    Expressions.Structured.BasicOp.inputs op = arity := by
  cases hFamily <;> rfl

theorem outputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp} {arity : Nat}
    (hFamily : LogFamily prim op arity) :
    Expressions.Structured.BasicOp.outputs op = 0 := by
  cases hFamily <;> rfl

private theorem list_eq_five_of_length
    {α : Type} {values : List α} (hLength : values.length = 5) :
    ∃ first second third fourth fifth,
      values = [first, second, third, fourth, fifth] := by
  cases values with
  | nil => simp at hLength
  | cons first rest =>
      have hRest : rest.length = 4 := by simpa using hLength
      obtain ⟨second, third, fourth, fifth, rfl⟩ :=
        List.length_eq_four.mp hRest
      exact ⟨first, second, third, fourth, fifth, rfl⟩

private theorem list_eq_six_of_length
    {α : Type} {values : List α} (hLength : values.length = 6) :
    ∃ first second third fourth fifth sixth,
      values = [first, second, third, fourth, fifth, sixth] := by
  cases values with
  | nil => simp at hLength
  | cons first rest =>
      have hRest : rest.length = 5 := by simpa using hLength
      obtain ⟨second, third, fourth, fifth, sixth, rfl⟩ :=
        list_eq_five_of_length hRest
      exact ⟨first, second, third, fourth, fifth, sixth, rfl⟩

def spec
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp} {arity : Nat}
    (hFamily : LogFamily prim op arity) : SharedWriteSpec prim op where
  sourceResult := result hFamily
  targetResult := result hFamily
  resultLength := by
    intro shared values hLength
    rw [hFamily.outputs]
    cases hFamily <;> simp only [result] <;> split <;> rfl
  related := by
    intro source target values hLength hRel
    rw [hFamily.inputs] at hLength
    cases hFamily with
    | log0 =>
        obtain ⟨offset, size, rfl⟩ := List.length_eq_two.mp hLength
        exact ⟨by simpa [result] using hRel.logOp offset size #[], rfl⟩
    | log1 =>
        obtain ⟨offset, size, topic0, rfl⟩ :=
          List.length_eq_three.mp hLength
        exact
          ⟨by simpa [result] using hRel.logOp offset size #[topic0], rfl⟩
    | log2 =>
        obtain ⟨offset, size, topic0, topic1, rfl⟩ :=
          List.length_eq_four.mp hLength
        exact
          ⟨by simpa [result] using
              hRel.logOp offset size #[topic0, topic1],
            rfl⟩
    | log3 =>
        obtain ⟨offset, size, topic0, topic1, topic2, rfl⟩ :=
          list_eq_five_of_length hLength
        exact
          ⟨by simpa [result] using
              hRel.logOp offset size #[topic0, topic1, topic2],
            rfl⟩
    | log4 =>
        obtain ⟨offset, size, topic0, topic1, topic2, topic3, rfl⟩ :=
          list_eq_six_of_length hLength
        exact
          ⟨by simpa [result] using
              hRel.logOp offset size #[topic0, topic1, topic2, topic3],
            rfl⟩
  sourceZero := by
    intro source values
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
  sourceAllowed := by
    intro fuel sourceShared sourceVars values hLength hPermission
    rw [hFamily.inputs] at hLength
    cases hFamily with
    | log0 =>
        obtain ⟨offset, size, rfl⟩ := List.length_eq_two.mp hLength
        simp [Yul.InteractionSemantics.Primitive.openEval,
          Yul.InteractionSemantics.Primitive.closedEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
        unfold EvmYul.step
        simp [Id.run, EvmYul.Yul.State.executionEnv, hPermission,
          EvmYul.Yul.State.setSharedState, result] <;> rfl
    | log1 =>
        obtain ⟨offset, size, topic0, rfl⟩ :=
          List.length_eq_three.mp hLength
        simp [Yul.InteractionSemantics.Primitive.openEval,
          Yul.InteractionSemantics.Primitive.closedEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
        unfold EvmYul.step
        simp [Id.run, EvmYul.Yul.State.executionEnv, hPermission,
          EvmYul.Yul.State.setSharedState, result] <;> rfl
    | log2 =>
        obtain ⟨offset, size, topic0, topic1, rfl⟩ :=
          List.length_eq_four.mp hLength
        simp [Yul.InteractionSemantics.Primitive.openEval,
          Yul.InteractionSemantics.Primitive.closedEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
        unfold EvmYul.step
        simp [Id.run, EvmYul.Yul.State.executionEnv, hPermission,
          EvmYul.Yul.State.setSharedState, result] <;> rfl
    | log3 =>
        obtain ⟨offset, size, topic0, topic1, topic2, rfl⟩ :=
          list_eq_five_of_length hLength
        simp [Yul.InteractionSemantics.Primitive.openEval,
          Yul.InteractionSemantics.Primitive.closedEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
        unfold EvmYul.step
        simp [Id.run, EvmYul.Yul.State.executionEnv, hPermission,
          EvmYul.Yul.State.setSharedState, result] <;> rfl
    | log4 =>
        obtain ⟨offset, size, topic0, topic1, topic2, topic3, rfl⟩ :=
          list_eq_six_of_length hLength
        simp [Yul.InteractionSemantics.Primitive.openEval,
          Yul.InteractionSemantics.Primitive.closedEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
        unfold EvmYul.step
        simp [Id.run, EvmYul.Yul.State.executionEnv, hPermission,
          EvmYul.Yul.State.setSharedState, result] <;> rfl
  sourceDenied := by
    intro fuel sourceShared sourceVars values hLength hPermission
    cases hFamily <;>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall] <;>
      unfold EvmYul.step <;>
      simp [Id.run, EvmYul.Yul.State.executionEnv, hPermission,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException] <;> rfl
  targetAllowed := by
    intro state values hLength hPermission
    rw [hFamily.inputs] at hLength
    cases hFamily with
    | log0 =>
        obtain ⟨offset, size, rfl⟩ := List.length_eq_two.mp hLength
        rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
          (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
        simp [Assembly.PrimStep.run, hPermission,
          Locals.InteractionSemantics.Primitive.finish,
          Locals.InteractionSemantics.Primitive.isolated,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.pop2,
          Locals.Source.State.withShared, Simulation.Interaction.map,
          Simulation.Interaction.bind, Simulation.Interaction.pure, result] <;>
          rfl
    | log1 =>
        obtain ⟨offset, size, topic0, rfl⟩ :=
          List.length_eq_three.mp hLength
        rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
          (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
        simp [Assembly.PrimStep.run, hPermission,
          Locals.InteractionSemantics.Primitive.finish,
          Locals.InteractionSemantics.Primitive.isolated,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.pop3,
          Locals.Source.State.withShared, Simulation.Interaction.map,
          Simulation.Interaction.bind, Simulation.Interaction.pure, result] <;>
          rfl
    | log2 =>
        obtain ⟨offset, size, topic0, topic1, rfl⟩ :=
          List.length_eq_four.mp hLength
        rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
          (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
        simp [Assembly.PrimStep.run, hPermission,
          Locals.InteractionSemantics.Primitive.finish,
          Locals.InteractionSemantics.Primitive.isolated,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.pop4,
          Locals.Source.State.withShared, Simulation.Interaction.map,
          Simulation.Interaction.bind, Simulation.Interaction.pure, result] <;>
          rfl
    | log3 =>
        obtain ⟨offset, size, topic0, topic1, topic2, rfl⟩ :=
          list_eq_five_of_length hLength
        rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
          (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
        simp [Assembly.PrimStep.run, hPermission,
          Locals.InteractionSemantics.Primitive.finish,
          Locals.InteractionSemantics.Primitive.isolated,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.pop5,
          Locals.Source.State.withShared, Simulation.Interaction.map,
          Simulation.Interaction.bind, Simulation.Interaction.pure, result] <;>
          rfl
    | log4 =>
        obtain ⟨offset, size, topic0, topic1, topic2, topic3, rfl⟩ :=
          list_eq_six_of_length hLength
        rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
          (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
        simp [Assembly.PrimStep.run, hPermission,
          Locals.InteractionSemantics.Primitive.finish,
          Locals.InteractionSemantics.Primitive.isolated,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.pop6,
          Locals.Source.State.withShared, Simulation.Interaction.map,
          Simulation.Interaction.bind, Simulation.Interaction.pure, result] <;>
          rfl
  targetDenied := by
    intro state values hLength hPermission
    cases hFamily <;>
      rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
        (by simpa using hLength) (by rfl) (by rfl)
        (by decide) (by decide)] <;>
      simp [Assembly.PrimStep.run, hPermission,
        Locals.InteractionSemantics.Primitive.isolated,
        Simulation.Interaction.map]

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp} {arity : Nat}
    {sourceValues : List Word}
    (hFamily : LogFamily prim op arity)
    (hLength : sourceValues.length = arity)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse) :=
  (spec hFamily).forward (by simpa [hFamily.inputs]) hRel

end LogFamily

namespace Invalid

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength :
      sourceValues.length = Expressions.Structured.BasicOp.inputs .invalid)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source .invalid)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source (.System .INVALID) sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        .invalid target sourceValues.reverse) := by
  have hValues : sourceValues = [] := by
    apply List.eq_nil_of_length_eq_zero
    change sourceValues.length = 0 at hLength
    exact hLength
  subst sourceValues
  cases fuel with
  | zero =>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source .invalid)
          (right := Locals.InteractionSemantics.Primitive.openEval
            .invalid target [])
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hSourceEval :
          Yul.InteractionSemantics.Primitive.openEval (previous + 2)
              (.Ok sourceShared sourceVars) (.System .INVALID) [] =
            .done
              (.error
                ({ exception := .InvalidInstruction,
                    state := .Ok sourceShared sourceVars } :
                  Yul.InteractionSemantics.Failure)) := by
        simp [Yul.InteractionSemantics.Primitive.openEval,
          Yul.InteractionSemantics.Primitive.closedEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall,
          Yul.InteractionSemantics.Primitive.fail,
          Yul.InteractionSemantics.State.afterException]
        unfold EvmYul.step
        rfl
      have hTargetEval :
          Locals.InteractionSemantics.Primitive.openEval
              .invalid target [] =
            .done (.error .InvalidInstruction) := by
        simp [Locals.InteractionSemantics.Primitive.openEval,
          Locals.InteractionSemantics.Primitive.supportsOpen, hLength]
        rfl
      simp only [List.reverse_nil]
      rw [show previous.succ + 1 = previous + 2 by omega,
        hSourceEval, hTargetEval]
      exact Simulation.Interaction.ForwardRel.done
        (Simulation.Interaction.ExceptRel.error trivial)

end Invalid

namespace MachineReturnDataCopy

theorem forward
    {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {sourceValues : List Word}
    (hLength : sourceValues.length = 3)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source .returndatacopy)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source (.Env .RETURNDATACOPY) sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        .returndatacopy target sourceValues.reverse) := by
  cases fuel with
  | zero =>
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Yul.InteractionSemantics.State.afterException,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (doneRel := PrimitiveDoneRel source .returndatacopy)
          (right := Locals.InteractionSemantics.Primitive.openEval
            .returndatacopy target sourceValues.reverse)
          (by trivial)
  | succ previous =>
      rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      obtain ⟨destination, readStart, size, rfl⟩ :=
        List.length_eq_three.mp hLength
      by_cases hInvalid :
          sourceShared.returnData.size < readStart.toNat + size.toNat
      · have hTargetInvalid :
            target.shared.returnData.size < readStart.toNat + size.toNat := by
          simpa [hShared.machine] using hInvalid
        have hSourceEval :
            Yul.InteractionSemantics.Primitive.openEval (previous + 2)
                (EvmYul.Yul.State.Ok sourceShared sourceVars)
                (.Env .RETURNDATACOPY)
                [destination, readStart, size] =
              .done
                (.error
                  ({ exception := .InvalidMemoryAccess,
                      state := EvmYul.Yul.State.Ok sourceShared sourceVars } :
                    Yul.InteractionSemantics.Failure)) := by
          simp [Yul.InteractionSemantics.Primitive.openEval,
            Yul.InteractionSemantics.Primitive.closedEval,
            Simulation.ExternalKind.ofYulOperation?,
            Simulation.CallKind.ofYulOperation?,
            Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
          unfold EvmYul.step
          simp [Id.run, EvmYul.Yul.State.toSharedState, hInvalid,
            Yul.InteractionSemantics.Primitive.fail,
            Yul.InteractionSemantics.State.afterException]
        have hTargetEval :
            Locals.InteractionSemantics.Primitive.openEval .returndatacopy
                target [size, readStart, destination] =
              .done (.error .InvalidMemoryAccess) := by
          rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
            (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
          simp [Assembly.PrimStep.run,
            Locals.InteractionSemantics.Primitive.isolated,
            Simulation.Interaction.map, hTargetInvalid, EvmYul.Stack.pop3,
            Id.run]
        rw [show previous.succ + 1 = previous + 2 by omega,
          hSourceEval,
          show [destination, readStart, size].reverse =
              [size, readStart, destination] by rfl,
          hTargetEval]
        exact Simulation.Interaction.ForwardRel.done
          (Simulation.Interaction.ExceptRel.error trivial)
      · have hTargetValid :
            ¬ target.shared.returnData.size <
              readStart.toNat + size.toNat := by
          simpa [hShared.machine] using hInvalid
        let sourceMachine :=
          sourceShared.toMachineState.returndatacopy
            destination readStart size
        let targetMachine :=
          target.shared.toMachineState.returndatacopy
            destination readStart size
        have hMachine : sourceMachine = targetMachine := by
          simp [sourceMachine, targetMachine, hShared.machine]
        have hStateRel :
            FunctionsInteractionRelation.StateRel
              (EvmYul.Yul.State.Ok sourceShared sourceVars) target :=
          ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
        have hFinalRel :=
          FunctionsInteractionRelation.StateRel.withMachine hStateRel
            sourceMachine targetMachine hMachine
        have hSourceEval :
            Yul.InteractionSemantics.Primitive.openEval (previous + 2)
                (EvmYul.Yul.State.Ok sourceShared sourceVars)
                (.Env .RETURNDATACOPY)
                [destination, readStart, size] =
              .done
                (.ok
                  ((EvmYul.Yul.State.Ok sourceShared sourceVars).setMachineState
                    sourceMachine,
                    [])) := by
          simp [Yul.InteractionSemantics.Primitive.openEval,
            Yul.InteractionSemantics.Primitive.closedEval,
            Simulation.ExternalKind.ofYulOperation?,
            Simulation.CallKind.ofYulOperation?,
            Simulation.CreateKind.ofYulOperation?, EvmYul.Yul.primCall]
          unfold EvmYul.step
          simp [Id.run, EvmYul.Yul.State.toSharedState, hInvalid,
            EvmYul.Yul.State.setMachineState, sourceMachine]
        have hTargetEval :
            Locals.InteractionSemantics.Primitive.openEval .returndatacopy
                target [size, readStart, destination] =
              .done
                (.ok
                  (target.withShared
                    { target.shared with toMachineState := targetMachine },
                    [])) := by
          rw [Locals.InteractionSemantics.Primitive.openEval_closedStep
            (by rfl) (by rfl) (by rfl) (by decide) (by decide)]
          simp [Assembly.PrimStep.run,
            Locals.InteractionSemantics.Primitive.finish,
            Locals.InteractionSemantics.Primitive.isolated,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, EvmYul.Stack.pop3,
            Locals.Source.State.withShared, Simulation.Interaction.map,
            Simulation.Interaction.bind, Simulation.Interaction.pure,
            hTargetValid, targetMachine, Id.run] <;> rfl
        have hDone :
            PrimitiveDoneRel (EvmYul.Yul.State.Ok sourceShared sourceVars)
              .returndatacopy
              (.ok
                ((EvmYul.Yul.State.Ok sourceShared sourceVars).setMachineState
                  sourceMachine,
                  []))
              (.ok
                (target.withShared
                  { target.shared with toMachineState := targetMachine },
                  [])) :=
          .ok ⟨⟨hFinalRel, rfl⟩, rfl, rfl⟩
        rw [show previous.succ + 1 = previous + 2 by omega,
          hSourceEval,
          show [destination, readStart, size].reverse =
              [size, readStart, destination] by rfl,
          hTargetEval]
        exact Simulation.Interaction.ForwardRel.done hDone

end MachineReturnDataCopy

/-- Every compiler-selected closed primitive is discharged by its adjacent
semantic-family theorem. External CALL/CREATE and resource queries are composed
separately by `compilerSelected_of_closed`. -/
theorem closedSelected : ClosedSelected := by
  intro fuel source target prim op sourceValues hExternal hGas hMsize hOp
    hLength hRel
  cases prim with
  | StopArith primitive =>
      cases primitive with
      | STOP => simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
      | ADD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .add hLength hRel
      | MUL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .mul hLength hRel
      | SUB =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .sub hLength hRel
      | DIV =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .div hLength hRel
      | SDIV =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .sdiv hLength hRel
      | MOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .mod hLength hRel
      | SMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .smod hLength hRel
      | ADDMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureTernary.forward .addmod hLength hRel
      | MULMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureTernary.forward .mulmod hLength hRel
      | EXP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .exp hLength hRel
      | SIGNEXTEND =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .signextend hLength hRel
  | CompBit primitive =>
      cases primitive with
      | LT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .lt hLength hRel
      | GT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .gt hLength hRel
      | SLT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .slt hLength hRel
      | SGT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .sgt hLength hRel
      | EQ =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .eq hLength hRel
      | ISZERO =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureUnary.forward .iszero hLength hRel
      | AND =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .and hLength hRel
      | OR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .or hLength hRel
      | XOR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .xor hLength hRel
      | NOT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureUnary.forward .not hLength hRel
      | BYTE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .byte hLength hRel
      | SHL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .shl hLength hRel
      | SHR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .shr hLength hRel
      | SAR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact PureBinary.forward .sar hLength hRel
  | Keccak primitive =>
      cases primitive with
      | KECCAK256 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact MachineKeccak256.forward (by simpa using hLength) hRel
  | Env primitive =>
      cases primitive with
      | ADDRESS =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .address hLength hRel
      | BALANCE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldUnaryAccess.forward .balance hLength hRel
      | ORIGIN =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .origin hLength hRel
      | CALLER =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .caller hLength hRel
      | CALLVALUE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .callvalue hLength hRel
      | CALLDATALOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldUnaryRead.forward .calldataload hLength hRel
      | CALLDATASIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .calldatasize hLength hRel
      | CALLDATACOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact SharedTernaryCopy.forward .calldatacopy hLength hRel
      | GASPRICE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .gasprice hLength hRel
      | CODESIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .codesize hLength hRel
      | CODECOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact SharedTernaryCopy.forward .codecopy hLength hRel
      | EXTCODESIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldUnaryAccess.forward .extcodesize hLength hRel
      | EXTCODECOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact SharedExtCodeCopy.forward (by simpa using hLength) hRel
      | RETURNDATASIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          change sourceValues.length = 0 at hLength
          exact MachineReturnDataSize.forward hLength hRel
      | RETURNDATACOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact MachineReturnDataCopy.forward (by simpa using hLength) hRel
      | EXTCODEHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldUnaryAccess.forward .extcodehash hLength hRel
  | Block primitive =>
      cases primitive with
      | BLOCKHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldUnaryRead.forward .blockhash hLength hRel
      | COINBASE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldNullary.forward .coinbase hLength hRel
      | TIMESTAMP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldNullary.forward .timestamp hLength hRel
      | NUMBER =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldNullary.forward .number hLength hRel
      | PREVRANDAO =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .prevrandao hLength hRel
      | GASLIMIT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldNullary.forward .gaslimit hLength hRel
      | CHAINID =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldNullary.forward .chainid hLength hRel
      | SELFBALANCE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldNullary.forward .selfbalance hLength hRel
      | BASEFEE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .basefee hLength hRel
      | BLOBHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentUnary.forward .blobhash hLength hRel
      | BLOBBASEFEE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact EnvironmentNullary.forward .blobbasefee hLength hRel
  | StackMemFlow primitive =>
      cases primitive with
      | POP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact MachinePop.forward (by simpa using hLength) hRel
      | MLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact MachineMLoad.forward (by simpa using hLength) hRel
      | MSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact MachineBinaryZero.forward .mstore hLength hRel
      | SLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldUnaryAccess.forward .sload hLength hRel
      | SSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldBinaryWrite.forward .sstore hLength hRel
      | MSTORE8 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact MachineBinaryZero.forward .mstore8 hLength hRel
      | MSIZE => exact (hMsize rfl).elim
      | GAS => exact (hGas rfl).elim
      | TLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldUnaryAccess.forward .tload hLength hRel
      | TSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact WorldBinaryWrite.forward .tstore hLength hRel
      | MCOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact MachineMCopy.forward (by simpa using hLength) hRel
  | Log primitive =>
      cases primitive with
      | LOG0 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact LogFamily.forward .log0 (by simpa using hLength) hRel
      | LOG1 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact LogFamily.forward .log1 (by simpa using hLength) hRel
      | LOG2 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact LogFamily.forward .log2 (by simpa using hLength) hRel
      | LOG3 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact LogFamily.forward .log3 (by simpa using hLength) hRel
      | LOG4 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact LogFamily.forward .log4 (by simpa using hLength) hRel
  | System primitive =>
      cases primitive with
      | CREATE =>
          simp [Simulation.ExternalKind.ofYulOperation?,
            Simulation.CallKind.ofYulOperation?,
            Simulation.CreateKind.ofYulOperation?] at hExternal
      | CALL =>
          simp [Simulation.ExternalKind.ofYulOperation?,
            Simulation.CallKind.ofYulOperation?,
            Simulation.CreateKind.ofYulOperation?] at hExternal
      | CALLCODE =>
          simp [Simulation.ExternalKind.ofYulOperation?,
            Simulation.CallKind.ofYulOperation?,
            Simulation.CreateKind.ofYulOperation?] at hExternal
      | RETURN => simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
      | DELEGATECALL =>
          simp [Simulation.ExternalKind.ofYulOperation?,
            Simulation.CallKind.ofYulOperation?,
            Simulation.CreateKind.ofYulOperation?] at hExternal
      | CREATE2 =>
          simp [Simulation.ExternalKind.ofYulOperation?,
            Simulation.CallKind.ofYulOperation?,
            Simulation.CreateKind.ofYulOperation?] at hExternal
      | STATICCALL =>
          simp [Simulation.ExternalKind.ofYulOperation?,
            Simulation.CallKind.ofYulOperation?,
            Simulation.CreateKind.ofYulOperation?] at hExternal
      | REVERT => simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
      | INVALID =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact Invalid.forward hLength hRel
      | SELFDESTRUCT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp

/-- Complete primitive capability: closed families above, plus the open
CALL/CREATE and GAS/MSIZE families owned by `FunctionsInteractionPrimitive`. -/
theorem compilerSelected : CompilerSelected :=
  FunctionsInteractionPrimitive.Primitive.compilerSelected_of_closed
    closedSelected

end FunctionsInteractionClosedPrimitive
end Yul
end EvmCompiler
