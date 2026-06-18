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

end FunctionsInteractionClosedPrimitive
end Yul
end EvmCompiler
