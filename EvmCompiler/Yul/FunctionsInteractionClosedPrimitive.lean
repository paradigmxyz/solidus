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

end FunctionsInteractionClosedPrimitive
end Yul
end EvmCompiler
