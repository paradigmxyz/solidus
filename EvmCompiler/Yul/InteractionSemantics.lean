import EvmCompiler.Simulation.Interaction
import EvmCompiler.Yul.EffectSemantics
import EvmCompiler.Yul.Primitive

namespace EvmCompiler
namespace Yul
namespace InteractionSemantics

/-!
Open-world Yul semantics as a specialization of the canonical control kernel.

Only primitive effects are interpreted here. Expression evaluation, internal
calls, blocks, switches, and loops remain owned by `Yul.Source.Canonical`.
-/

abbrev State := EvmYul.Yul.State
abbrev Failure := Yul.Source.Canonical.Failure State
abbrev Open (α : Type) := Simulation.Interaction Failure α

def stateModel : Yul.Source.Canonical.StateModel State where
  source := id
  withSource := fun _ source => source

namespace State

def afterException (state : State) : EvmYul.Yul.Exception → State
  | .YulHalt final _ => final
  | .Revert final => final
  | _ => state

def withWorldAndMachine (state : State) (world : Simulation.OpenWorld)
    (machine : EvmYul.MachineState) : State :=
  let shared :=
    Simulation.OpenWorld.installYulShared state.sharedState world
  state.setSharedState { shared with toMachineState := machine }

end State

namespace Primitive

def fail {α : Type} (state : State)
    (exception : EvmYul.Yul.Exception) : Open α :=
  .done (.error { exception := exception, state := state })

def closedEval (fuel : Nat) (state : State)
    (op : EvmYul.Operation .Yul) (args : List Word) : Open (State × List Word) :=
  match EvmYul.Yul.primCall fuel state op args with
  | .ok result => .done (.ok result)
  | .error exception =>
      fail (state.afterException exception) exception

def resourceEval (kind : Simulation.ResourceQuery) (state : State) :
    Open (State × List Word) :=
  .request (.resource kind) fun value =>
    .done (.ok (state, [value]))

def callEval (kind : Simulation.CallKind) (state : State)
    (args : List Word) : Open (State × List Word) :=
  match kind.evmOperands? args with
  | some ([], operands) =>
      let frame := Simulation.ExternalFrame.ofShared state.sharedState
      if kind.allowedIn frame operands then
        let callLocal := operands.callLocal
        let request := frame.callRequest kind operands
        let world := Simulation.OpenWorld.ofYulShared state.sharedState
        .request (.external world (.call request)) fun response =>
          let machine :=
            callLocal.finishMachine state.sharedState.toMachineState
              response.returnData
          .done
            (.ok
              (state.withWorldAndMachine response.postWorld machine,
                [response.statusWord]))
      else
        fail state .StaticModeViolation
  | _ => fail state .InvalidArguments

def createEval (kind : Simulation.CreateKind) (state : State)
    (args : List Word) : Open (State × List Word) :=
  match kind.evmOperands? args with
  | some ([], operands) =>
      let frame := Simulation.ExternalFrame.ofShared state.sharedState
      if frame.permission then
        let createLocal := operands.createLocal
        let request := frame.createRequest kind operands
        let world := Simulation.OpenWorld.ofYulShared state.sharedState
        .request (.external world (.create request)) fun response =>
          let machine :=
            createLocal.finishMachine state.sharedState.toMachineState
              response.returnData
          .done
            (.ok
              (state.withWorldAndMachine response.postWorld machine,
                [response.address]))
      else
        fail state .StaticModeViolation
  | _ => fail state .InvalidArguments

def openEval (fuel : Nat) (state : State)
    (op : EvmYul.Operation .Yul) (args : List Word) :
    Open (State × List Word) :=
  match fuel with
  | 0 => fail state .OutOfFuel
  | fuel' + 1 =>
      match Simulation.ExternalKind.ofYulOperation? op with
      | some (.call kind) => callEval kind state args
      | some (.create kind) => createEval kind state args
      | none =>
          match op with
          | .StackMemFlow .GAS => resourceEval .gas state
          | .StackMemFlow .MSIZE => resourceEval .msize state
          | _ => closedEval fuel' state op args

end Primitive

def primitiveSemantics :
    Yul.Source.Canonical.PrimitiveSemantics Open State where
  eval := Primitive.openEval

abbrev evalArgs :=
  Yul.Source.Canonical.evalArgs stateModel primitiveSemantics

abbrev evalValues :=
  Yul.Source.Canonical.evalValues stateModel primitiveSemantics

abbrev eval :=
  Yul.Source.Canonical.eval stateModel primitiveSemantics

abbrev call :=
  Yul.Source.Canonical.call stateModel primitiveSemantics

abbrev execSeq :=
  Yul.Source.Canonical.execSeq stateModel primitiveSemantics

abbrev exec :=
  Yul.Source.Canonical.exec stateModel primitiveSemantics

abbrev loop :=
  Yul.Source.Canonical.loop stateModel primitiveSemantics

namespace EvalArgs

/-- One argument followed by exhausted list fuel. Adjacent compiler proofs use
this equation without unfolding the canonical mutual evaluator. -/
theorem one_cons
    (head : EvmYul.Yul.Ast.Expr) (rest : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    evalArgs 1 (head :: rest) code state =
      Simulation.Interaction.bind (evalValues 0 head code state) fun result =>
        Primitive.fail result.1 .OutOfFuel := by
  simp only [evalArgs, Yul.Source.Canonical.evalArgs,
    Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.evalTail,
    Yul.Source.Effectful.eval]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind (evalValues 0 head code state)
          (fun result => pure (result.1, result.2.head!)))
        (fun result => Primitive.fail result.1 .OutOfFuel) = _
  rw [Simulation.Interaction.bind_assoc]
  rfl

/-- Positive residual list fuel exposes the head expression and exact tail. -/
theorem succ_succ_cons
    (fuel : Nat) (head : EvmYul.Yul.Ast.Expr)
    (rest : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    evalArgs (fuel + 2) (head :: rest) code state =
      Simulation.Interaction.bind (evalValues (fuel + 1) head code state)
        fun headResult =>
          Simulation.Interaction.bind
            (evalArgs fuel rest code headResult.1) fun tailResult =>
              pure
                (tailResult.1, headResult.2.head! :: tailResult.2) := by
  simp only [evalArgs, Yul.Source.Canonical.evalArgs,
    Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.evalTail,
    Yul.Source.Effectful.eval]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (evalValues (fuel + 1) head code state)
          (fun result => pure (result.1, result.2.head!)))
        (fun headResult =>
          Simulation.Interaction.bind
            (evalArgs fuel rest code headResult.1)
            (fun tailResult =>
              pure (tailResult.1, headResult.2 :: tailResult.2))) = _
  rw [Simulation.Interaction.bind_assoc]
  rfl

end EvalArgs

namespace Program

def openRun (fuel : Nat) (code : EvmYul.Yul.Ast.YulContract)
    (state : State) : Open (State × List Word) :=
  Yul.Source.Canonical.Program.run
    stateModel primitiveSemantics fuel code state

end Program

end InteractionSemantics
end Yul
end EvmCompiler
