import EvmCompiler.Yul.FunctionsInteractionRelation
import EvmCompiler.Solidus.SourceRun

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPrimitive

open FunctionsInteractionRelation

def ErrorRel (source : Yul.InteractionSemantics.Failure)
    (target : EVMException) : Prop :=
  match source.exception, target with
  | .OutOfFuel, .OutOfFuel => True
  | .InvalidArguments, .StackUnderflow => True
  | .InvalidInstruction, .InvalidInstruction => True
  | .InvalidMemoryAccess, .InvalidMemoryAccess => True
  | .StaticModeViolation, .StaticModeViolation => True
  | _, _ => False

theorem truncated_iff_outOfFuel
    {failure : Yul.InteractionSemantics.Failure} :
    Truncated failure ↔ failure.exception = .OutOfFuel := by
  rcases failure with ⟨exception, state⟩
  cases exception <;> simp [Truncated]

def ResultRel
    (source : Yul.InteractionSemantics.State × List Word)
    (target : Functions.InteractionSemantics.State × List Word) : Prop :=
  FunctionsInteractionRelation.StateRel source.1 target.1 ∧
    source.2 = target.2

abbrev DoneRel :=
  Simulation.Interaction.ExceptRel ErrorRel ResultRel

def PrimitiveResultRel (entry : Yul.InteractionSemantics.State)
    (op : Structured.BasicOp)
    (source : Yul.InteractionSemantics.State × List Word)
    (target : Functions.InteractionSemantics.State × List Word) : Prop :=
  ResultRel source target ∧
    source.2.length = Expressions.Structured.BasicOp.outputs op ∧
    source.1.store = entry.store

abbrev PrimitiveDoneRel (entry : Yul.InteractionSemantics.State)
    (op : Structured.BasicOp) :=
  Simulation.Interaction.ExceptRel ErrorRel (PrimitiveResultRel entry op)

/-- The one primitive capability consumed by recursive Yul expression and
statement proofs. It refers only to the ordinary compiler's selected opcode;
family modules discharge it without changing either interpreter. -/
def CompilerSelected : Prop :=
  ∀ {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues : List Word},
    Prim.toUncheckedBasicOp? prim = some op →
    sourceValues.length = Expressions.Structured.BasicOp.inputs op →
    FunctionsInteractionRelation.StateRel source target →
    Simulation.Interaction.ForwardRel Truncated (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse)

/-- Closed ordinary primitive capability, independent of open external and
resource families. The final compiler-selected capability is assembled from
this interface plus the CALL/CREATE and GAS/MSIZE family theorems below. -/
def ClosedSelected : Prop :=
  ∀ {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues : List Word},
    Simulation.ExternalKind.ofYulOperation? prim = none →
    prim ≠ .StackMemFlow .GAS →
    prim ≠ .StackMemFlow .MSIZE →
    Prim.toUncheckedBasicOp? prim = some op →
    sourceValues.length = Expressions.Structured.BasicOp.inputs op →
    FunctionsInteractionRelation.StateRel source target →
    Simulation.Interaction.ForwardRel Truncated (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 1) source prim sourceValues)
      (Locals.InteractionSemantics.Primitive.openEval
        op target sourceValues.reverse)

namespace ResultRel

theorem refl_values
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target)
    (values : List Word) :
    ResultRel (source, values) (target, values) :=
  ⟨hRel, rfl⟩

end ResultRel

namespace Primitive

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

private theorem list_eq_seven_of_length
    {α : Type} {values : List α} (hLength : values.length = 7) :
    ∃ first second third fourth fifth sixth seventh,
      values = [first, second, third, fourth, fifth, sixth, seventh] := by
  cases values with
  | nil => simp at hLength
  | cons first rest =>
      have hRest : rest.length = 6 := by simpa using hLength
      obtain ⟨second, third, fourth, fifth, sixth, seventh, rfl⟩ :=
        list_eq_six_of_length hRest
      exact ⟨first, second, third, fourth, fifth, sixth, seventh, rfl⟩

theorem callOperands_of_length
    (kind : Simulation.CallKind) {args : List Word}
    (hLength : args.length = kind.inputArity) :
    ∃ operands,
      kind.evmOperands? args = some ([], operands) := by
  cases kind with
  | call =>
      obtain ⟨gas, address, value, inputOffset, inputSize, outputOffset,
          outputSize, rfl⟩ := list_eq_seven_of_length hLength
      exact ⟨_, rfl⟩
  | callcode =>
      obtain ⟨gas, address, value, inputOffset, inputSize, outputOffset,
          outputSize, rfl⟩ := list_eq_seven_of_length hLength
      exact ⟨_, rfl⟩
  | delegatecall =>
      obtain ⟨gas, address, inputOffset, inputSize, outputOffset,
          outputSize, rfl⟩ := list_eq_six_of_length hLength
      exact ⟨_, rfl⟩
  | staticcall =>
      obtain ⟨gas, address, inputOffset, inputSize, outputOffset,
          outputSize, rfl⟩ := list_eq_six_of_length hLength
      exact ⟨_, rfl⟩

theorem createOperands_of_length
    (kind : Simulation.CreateKind) {args : List Word}
    (hLength : args.length = kind.inputArity) :
    ∃ operands,
      kind.evmOperands? args = some ([], operands) := by
  cases kind with
  | create =>
      obtain ⟨value, inputOffset, inputSize, rfl⟩ :=
        List.length_eq_three.mp hLength
      exact ⟨_, rfl⟩
  | create2 =>
      obtain ⟨value, inputOffset, inputSize, salt, rfl⟩ :=
        List.length_eq_four.mp hLength
      exact ⟨_, rfl⟩

def callBasicOp : Simulation.CallKind → Structured.BasicOp
  | .call => .call
  | .callcode => .callcode
  | .delegatecall => .delegatecall
  | .staticcall => .staticcall

def createBasicOp : Simulation.CreateKind → Structured.BasicOp
  | .create => .create
  | .create2 => .create2

@[simp] theorem toUncheckedBasicOp?_callBasicOp
    (kind : Simulation.CallKind) :
    Prim.toUncheckedBasicOp? kind.toYulOperation =
      some (callBasicOp kind) := by
  cases kind <;> rfl

@[simp] theorem toUncheckedBasicOp?_createBasicOp
    (kind : Simulation.CreateKind) :
    Prim.toUncheckedBasicOp? kind.toYulOperation =
      some (createBasicOp kind) := by
  cases kind <;> rfl

@[simp] theorem callBasicOp_inputs (kind : Simulation.CallKind) :
    Expressions.Structured.BasicOp.inputs (callBasicOp kind) =
      kind.inputArity := by
  cases kind <;> rfl

@[simp] theorem createBasicOp_inputs (kind : Simulation.CreateKind) :
    Expressions.Structured.BasicOp.inputs (createBasicOp kind) =
      kind.inputArity := by
  cases kind <;> rfl

theorem openEval_callBasicOp
    (kind : Simulation.CallKind)
    {target : Functions.InteractionSemantics.State}
    {args : List Word}
    (hLength : args.length = kind.inputArity) :
    Locals.InteractionSemantics.Primitive.openEval
        (callBasicOp kind) target args.reverse =
      Simulation.Interaction.map
        (Locals.InteractionSemantics.Primitive.finish target)
        (Assembly.InteractionSemantics.PrimOp.callStep kind
          (Locals.InteractionSemantics.Primitive.isolated
            target args.reverse)) := by
  cases kind with
  | call =>
      exact Locals.InteractionSemantics.Primitive.openEval_call
        target args.reverse (by simpa [Simulation.CallKind.inputArity] using hLength)
  | callcode =>
      exact Locals.InteractionSemantics.Primitive.openEval_callcode
        target args.reverse (by simpa [Simulation.CallKind.inputArity] using hLength)
  | delegatecall =>
      exact Locals.InteractionSemantics.Primitive.openEval_delegatecall
        target args.reverse (by simpa [Simulation.CallKind.inputArity] using hLength)
  | staticcall =>
      exact Locals.InteractionSemantics.Primitive.openEval_staticcall
        target args.reverse (by simpa [Simulation.CallKind.inputArity] using hLength)

theorem openEval_createBasicOp
    (kind : Simulation.CreateKind)
    {target : Functions.InteractionSemantics.State}
    {args : List Word}
    (hLength : args.length = kind.inputArity) :
    Locals.InteractionSemantics.Primitive.openEval
        (createBasicOp kind) target args.reverse =
      Simulation.Interaction.map
        (Locals.InteractionSemantics.Primitive.finish target)
        (Assembly.InteractionSemantics.PrimOp.createStep kind
          (Locals.InteractionSemantics.Primitive.isolated
            target args.reverse)) := by
  cases kind with
  | create =>
      exact Locals.InteractionSemantics.Primitive.openEval_create
        target args.reverse (by simpa [Simulation.CreateKind.inputArity] using hLength)
  | create2 =>
      exact Locals.InteractionSemantics.Primitive.openEval_create2
        target args.reverse (by simpa [Simulation.CreateKind.inputArity] using hLength)

theorem resourceEval_rel
    (kind : Simulation.ResourceQuery) (op : Structured.BasicOp)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 1)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel (PrimitiveDoneRel source op)
      (Yul.InteractionSemantics.Primitive.resourceEval kind source)
      (.request (.resource kind) fun value =>
        .done (.ok (target, [value]))) := by
  apply Simulation.Interaction.Rel.request
  intro value
  exact .done
    (.ok ⟨ResultRel.refl_values hRel [value], by simpa [hOutputs], rfl⟩)

/-- One CALL-family suspension, before choosing the concrete source/target
opcode wrappers. Arguments are in Yul source order; the isolated EVM stack is
that exact list because the Functions primitive receives `args.reverse`. -/
theorem callEval_rel_callStep
    (kind : Simulation.CallKind)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {args : List Word} {operands : Simulation.CallOperands}
    (hOperands : kind.evmOperands? args = some ([], operands))
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel (PrimitiveDoneRel source (callBasicOp kind))
      (Yul.InteractionSemantics.Primitive.callEval kind source args)
      (Simulation.Interaction.map
        (Locals.InteractionSemantics.Primitive.finish target)
        (Assembly.InteractionSemantics.PrimOp.callStep kind
          (Locals.InteractionSemantics.Primitive.isolated
            target args.reverse))) := by
  have hFrame := FunctionsInteractionRelation.StateRel.externalFrame_eq hRel
  have hWorld := FunctionsInteractionRelation.StateRel.openWorld_eq hRel
  unfold Yul.InteractionSemantics.Primitive.callEval
  rw [hOperands]
  unfold Locals.InteractionSemantics.Primitive.isolated
  simp only [List.reverse_reverse]
  unfold Assembly.InteractionSemantics.PrimOp.callStep
  rw [hOperands]
  rw [← hFrame, ← hWorld]
  by_cases hAllowed :
      kind.allowedIn
        (Simulation.ExternalFrame.ofShared source.sharedState) operands = true
  · simp only [hAllowed, if_pos]
    apply Simulation.Interaction.Rel.request
    intro response
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    refine ⟨⟨?_, rfl⟩, ?_, ?_⟩
    · simpa [Simulation.Interaction.map,
        Assembly.InteractionSemantics.EVMState.finishCall,
        Assembly.InteractionSemantics.EVMState.installWorld,
        Locals.InteractionSemantics.Primitive.finish,
        EvmYul.EVM.State.incrPC,
        EvmYul.EVM.State.replaceStackAndIncrPC] using
        FunctionsInteractionRelation.StateRel.withWorldAndMachine hRel
          response.postWorld
          (operands.callLocal.finishMachine
            source.sharedState.toMachineState response.returnData)
          (operands.callLocal.finishMachine
            target.shared.toMachineState response.returnData)
          (congrArg
            (fun machine =>
              operands.callLocal.finishMachine machine response.returnData)
            (FunctionsInteractionRelation.StateRel.shared hRel).machine)
    · cases kind <;> rfl
    · rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      rfl
  · simp only [hAllowed, if_neg]
    exact .done (.error trivial)

/-- One CREATE-family suspension, before choosing CREATE versus CREATE2. -/
theorem createEval_rel_createStep
    (kind : Simulation.CreateKind)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {args : List Word} {operands : Simulation.CreateOperands}
    (hOperands : kind.evmOperands? args = some ([], operands))
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel (PrimitiveDoneRel source (createBasicOp kind))
      (Yul.InteractionSemantics.Primitive.createEval kind source args)
      (Simulation.Interaction.map
        (Locals.InteractionSemantics.Primitive.finish target)
        (Assembly.InteractionSemantics.PrimOp.createStep kind
          (Locals.InteractionSemantics.Primitive.isolated
            target args.reverse))) := by
  have hFrame := FunctionsInteractionRelation.StateRel.externalFrame_eq hRel
  have hWorld := FunctionsInteractionRelation.StateRel.openWorld_eq hRel
  unfold Yul.InteractionSemantics.Primitive.createEval
  rw [hOperands]
  unfold Locals.InteractionSemantics.Primitive.isolated
  simp only [List.reverse_reverse]
  unfold Assembly.InteractionSemantics.PrimOp.createStep
  rw [hOperands]
  rw [← hFrame, ← hWorld]
  by_cases hAllowed :
      (Simulation.ExternalFrame.ofShared source.sharedState).permission = true
  · simp only [hAllowed, if_pos]
    apply Simulation.Interaction.Rel.request
    intro response
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    refine ⟨⟨?_, rfl⟩, ?_, ?_⟩
    · simpa [Simulation.Interaction.map,
        Assembly.InteractionSemantics.EVMState.finishCreate,
        Assembly.InteractionSemantics.EVMState.installWorld,
        Locals.InteractionSemantics.Primitive.finish,
        EvmYul.EVM.State.incrPC,
        EvmYul.EVM.State.replaceStackAndIncrPC] using
        FunctionsInteractionRelation.StateRel.withWorldAndMachine hRel
          response.postWorld
          (operands.createLocal.finishMachine
            source.sharedState.toMachineState response.returnData)
          (operands.createLocal.finishMachine
            target.shared.toMachineState response.returnData)
          (congrArg
            (fun machine =>
              operands.createLocal.finishMachine machine response.returnData)
            (FunctionsInteractionRelation.StateRel.shared hRel).machine)
    · cases kind <;> rfl
    · rcases hRel with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      rfl
  · simp only [hAllowed, if_neg]
    exact .done (.error trivial)

theorem gas
    (fuel : Nat)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel (PrimitiveDoneRel source .gas)
      (Yul.InteractionSemantics.Primitive.openEval (fuel + 1) source
        (.StackMemFlow .GAS) [])
      (Locals.InteractionSemantics.Primitive.openEval .gas target []) := by
  simpa [Yul.InteractionSemantics.Primitive.openEval,
    Locals.InteractionSemantics.Primitive.openEval,
    Locals.InteractionSemantics.Primitive.supportsOpen,
    Locals.InteractionSemantics.Primitive.isolated,
    Locals.InteractionSemantics.Primitive.finish,
    Assembly.InteractionSemantics.PrimOp.resourceStep,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC,
    Simulation.Interaction.map] using resourceEval_rel .gas .gas rfl hRel

theorem msize
    (fuel : Nat)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel (PrimitiveDoneRel source .msize)
      (Yul.InteractionSemantics.Primitive.openEval (fuel + 1) source
        (.StackMemFlow .MSIZE) [])
      (Locals.InteractionSemantics.Primitive.openEval .msize target []) := by
  simpa [Yul.InteractionSemantics.Primitive.openEval,
    Locals.InteractionSemantics.Primitive.openEval,
    Locals.InteractionSemantics.Primitive.supportsOpen,
    Locals.InteractionSemantics.Primitive.isolated,
    Locals.InteractionSemantics.Primitive.finish,
    Assembly.InteractionSemantics.PrimOp.resourceStep,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC,
    Simulation.Interaction.map] using resourceEval_rel .msize .msize rfl hRel

theorem callFamily
    (kind : Simulation.CallKind) (fuel : Nat)
    (operands : Simulation.CallOperands)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel (PrimitiveDoneRel source (callBasicOp kind))
      (Yul.InteractionSemantics.Primitive.openEval (fuel + 1) source
        kind.toYulOperation (kind.args operands))
      (Locals.InteractionSemantics.Primitive.openEval
        (callBasicOp kind) target (kind.args operands).reverse) := by
  cases kind with
  | call =>
      simpa [callBasicOp, Yul.InteractionSemantics.Primitive.openEval] using
        callEval_rel_callStep .call
          (Simulation.CallKind.evmOperands?_args .call operands []) hRel
  | callcode =>
      simpa [callBasicOp, Yul.InteractionSemantics.Primitive.openEval] using
        callEval_rel_callStep .callcode
          (Simulation.CallKind.evmOperands?_args .callcode operands []) hRel
  | delegatecall =>
      simpa [callBasicOp, Yul.InteractionSemantics.Primitive.openEval] using
        callEval_rel_callStep .delegatecall
          (Simulation.CallKind.evmOperands?_args .delegatecall operands [])
          hRel
  | staticcall =>
      simpa [callBasicOp, Yul.InteractionSemantics.Primitive.openEval] using
        callEval_rel_callStep .staticcall
          (Simulation.CallKind.evmOperands?_args .staticcall operands []) hRel

theorem createFamily
    (kind : Simulation.CreateKind) (fuel : Nat)
    (operands : Simulation.CreateOperands)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel (PrimitiveDoneRel source (createBasicOp kind))
      (Yul.InteractionSemantics.Primitive.openEval (fuel + 1) source
        kind.toYulOperation (kind.args operands))
      (Locals.InteractionSemantics.Primitive.openEval
        (createBasicOp kind) target (kind.args operands).reverse) := by
  cases kind with
  | create =>
      simpa [createBasicOp, Yul.InteractionSemantics.Primitive.openEval] using
        createEval_rel_createStep .create
          (Simulation.CreateKind.evmOperands?_args .create operands []) hRel
  | create2 =>
      simpa [createBasicOp, Yul.InteractionSemantics.Primitive.openEval] using
        createEval_rel_createStep .create2
          (Simulation.CreateKind.evmOperands?_args .create2 operands []) hRel

theorem callArbitrary
    (kind : Simulation.CallKind) (fuel : Nat)
    {args : List Word}
    (hLength : args.length = kind.inputArity)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source (callBasicOp kind))
      (Yul.InteractionSemantics.Primitive.openEval (fuel + 1) source
        kind.toYulOperation args)
      (Locals.InteractionSemantics.Primitive.openEval
        (callBasicOp kind) target args.reverse) := by
  obtain ⟨operands, hOperands⟩ := callOperands_of_length kind hLength
  have hRaw :
      Simulation.Interaction.Rel
        (PrimitiveDoneRel source (callBasicOp kind))
        (Yul.InteractionSemantics.Primitive.openEval (fuel + 1) source
          kind.toYulOperation args)
        (Locals.InteractionSemantics.Primitive.openEval
          (callBasicOp kind) target args.reverse) := by
    rw [openEval_callBasicOp kind hLength]
    cases kind with
    | call =>
        simpa [callBasicOp, Yul.InteractionSemantics.Primitive.openEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CallKind.toYulOperation,
          Simulation.CallKind.inputArity] using
          callEval_rel_callStep .call hOperands hRel
    | callcode =>
        simpa [callBasicOp, Yul.InteractionSemantics.Primitive.openEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CallKind.toYulOperation,
          Simulation.CallKind.inputArity] using
          callEval_rel_callStep .callcode hOperands hRel
    | delegatecall =>
        simpa [callBasicOp, Yul.InteractionSemantics.Primitive.openEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CallKind.toYulOperation,
          Simulation.CallKind.inputArity] using
          callEval_rel_callStep .delegatecall hOperands hRel
    | staticcall =>
        simpa [callBasicOp, Yul.InteractionSemantics.Primitive.openEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CallKind.toYulOperation,
          Simulation.CallKind.inputArity] using
          callEval_rel_callStep .staticcall hOperands hRel
  exact Simulation.Interaction.ForwardRel.ofRel hRaw

theorem createArbitrary
    (kind : Simulation.CreateKind) (fuel : Nat)
    {args : List Word}
    (hLength : args.length = kind.inputArity)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel source (createBasicOp kind))
      (Yul.InteractionSemantics.Primitive.openEval (fuel + 1) source
        kind.toYulOperation args)
      (Locals.InteractionSemantics.Primitive.openEval
        (createBasicOp kind) target args.reverse) := by
  obtain ⟨operands, hOperands⟩ := createOperands_of_length kind hLength
  have hRaw :
      Simulation.Interaction.Rel
        (PrimitiveDoneRel source (createBasicOp kind))
        (Yul.InteractionSemantics.Primitive.openEval (fuel + 1) source
          kind.toYulOperation args)
        (Locals.InteractionSemantics.Primitive.openEval
          (createBasicOp kind) target args.reverse) := by
    rw [openEval_createBasicOp kind hLength]
    cases kind with
    | create =>
        simpa [createBasicOp, Yul.InteractionSemantics.Primitive.openEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?,
          Simulation.CreateKind.toYulOperation,
          Simulation.CreateKind.inputArity] using
          createEval_rel_createStep .create hOperands hRel
    | create2 =>
        simpa [createBasicOp, Yul.InteractionSemantics.Primitive.openEval,
          Simulation.ExternalKind.ofYulOperation?,
          Simulation.CallKind.ofYulOperation?,
          Simulation.CreateKind.ofYulOperation?,
          Simulation.CreateKind.toYulOperation,
          Simulation.CreateKind.inputArity] using
          createEval_rel_createStep .create2 hOperands hRel
  exact Simulation.Interaction.ForwardRel.ofRel hRaw

/-- Assemble the one recursive-expression primitive capability from adjacent,
independently reusable family capabilities. -/
theorem compilerSelected_of_closed
    (hClosed : ClosedSelected) : CompilerSelected := by
  intro fuel source target prim op sourceValues hOp hLength hRel
  cases hExternal : Simulation.ExternalKind.ofYulOperation? prim with
  | some kind =>
      have hPrim :=
        Simulation.ExternalKind.eq_toYulOperation_of_ofYulOperation?_eq_some
          hExternal
      subst prim
      cases kind with
      | call kind =>
          change
            Prim.toUncheckedBasicOp? kind.toYulOperation = some op at hOp
          rw [toUncheckedBasicOp?_callBasicOp] at hOp
          cases hOp
          exact callArbitrary kind fuel (by simpa using hLength) hRel
      | create kind =>
          change
            Prim.toUncheckedBasicOp? kind.toYulOperation = some op at hOp
          rw [toUncheckedBasicOp?_createBasicOp] at hOp
          cases hOp
          exact createArbitrary kind fuel (by simpa using hLength) hRel
  | none =>
      by_cases hGas : prim = .StackMemFlow .GAS
      · subst prim
        simp [Prim.toUncheckedBasicOp?] at hOp
        subst op
        have hValues : sourceValues = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa [Expressions.Structured.BasicOp.inputs] using hLength
        subst sourceValues
        exact Simulation.Interaction.ForwardRel.ofRel (gas fuel hRel)
      · by_cases hMsize : prim = .StackMemFlow .MSIZE
        · subst prim
          simp [Prim.toUncheckedBasicOp?] at hOp
          subst op
          have hValues : sourceValues = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa [Expressions.Structured.BasicOp.inputs] using hLength
          subst sourceValues
          exact Simulation.Interaction.ForwardRel.ofRel (msize fuel hRel)
        · exact hClosed hExternal hGas hMsize hOp hLength hRel

end Primitive

end FunctionsInteractionPrimitive
end Yul
end EvmCompiler
