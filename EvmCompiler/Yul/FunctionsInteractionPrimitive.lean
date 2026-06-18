import EvmCompiler.Yul.FunctionsInteractionRelation

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPrimitive

open FunctionsInteractionRelation

def ErrorRel (source : Yul.InteractionSemantics.Failure)
    (target : EVMException) : Prop :=
  match source.exception, target with
  | .OutOfFuel, .OutOfFuel => True
  | .InvalidArguments, .StackUnderflow => True
  | .StaticModeViolation, .StaticModeViolation => True
  | _, _ => False

def ResultRel
    (source : Yul.InteractionSemantics.State × List Word)
    (target : Functions.InteractionSemantics.State × List Word) : Prop :=
  FunctionsInteractionRelation.StateRel source.1 target.1 ∧
    source.2 = target.2

abbrev DoneRel :=
  Simulation.Interaction.ExceptRel ErrorRel ResultRel

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

def callBasicOp : Simulation.CallKind → Structured.BasicOp
  | .call => .call
  | .callcode => .callcode
  | .delegatecall => .delegatecall
  | .staticcall => .staticcall

def createBasicOp : Simulation.CreateKind → Structured.BasicOp
  | .create => .create
  | .create2 => .create2

theorem resourceEval_rel
    (kind : Simulation.ResourceQuery)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel DoneRel
      (Yul.InteractionSemantics.Primitive.resourceEval kind source)
      (.request (.resource kind) fun value =>
        .done (.ok (target, [value]))) := by
  apply Simulation.Interaction.Rel.request
  intro value
  exact .done (.ok (ResultRel.refl_values hRel [value]))

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
    Simulation.Interaction.Rel DoneRel
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
    refine ⟨?_, rfl⟩
    simpa [Simulation.Interaction.map,
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
    Simulation.Interaction.Rel DoneRel
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
    refine ⟨?_, rfl⟩
    simpa [Simulation.Interaction.map,
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
  · simp only [hAllowed, if_neg]
    exact .done (.error trivial)

theorem gas
    (fuel : Nat)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel DoneRel
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
    Simulation.Interaction.map] using resourceEval_rel .gas hRel

theorem msize
    (fuel : Nat)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel DoneRel
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
    Simulation.Interaction.map] using resourceEval_rel .msize hRel

theorem callFamily
    (kind : Simulation.CallKind) (fuel : Nat)
    (operands : Simulation.CallOperands)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.Rel DoneRel
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
    Simulation.Interaction.Rel DoneRel
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

end Primitive

end FunctionsInteractionPrimitive
end Yul
end EvmCompiler
