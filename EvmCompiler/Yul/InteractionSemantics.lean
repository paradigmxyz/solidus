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

theorem zeroFill_eq_multifill_zero
    (shared : EvmYul.SharedState .Yul)
    (source : EvmYul.Yul.VarStore) (names : List Functions.Name) :
    (EvmYul.Yul.State.Ok shared source).zeroFill names =
      (EvmYul.Yul.State.Ok shared source).multifill names
        (names.map fun _name => EvmYul.UInt256.ofNat 0) := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simpa [EvmYul.Yul.State.zeroFill,
        EvmYul.Yul.State.multifill] using
          congrArg
            (fun state => state.insert name (EvmYul.UInt256.ofNat 0)) ih

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
  let result : Except EvmYul.Yul.Exception (State × List Word) :=
    match op, fuel with
    | .Env .EXTCODEHASH, 0 => Except.error .OutOfFuel
    | .Env .EXTCODEHASH, _ + 1 =>
        EvmYul.Yul.unaryStateOp Simulation.CodeErasedState.extCodeHash
          state args |>.map fun result => (result.1, result.2.toList)
    | _, _ => EvmYul.Yul.primCall fuel state op args
  match result with
  | .ok value => .done (.ok value)
  | .error exception => fail (state.afterException exception) exception

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

namespace ExecSeq

theorem zero
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    execSeq 0 stmts code state = Primitive.fail state .OutOfFuel := by
  simp [execSeq, Yul.Source.Canonical.execSeq,
    Yul.Source.Effectful.execSeq, Primitive.fail,
    Yul.Source.Effectful.Control.fail]
  rfl

theorem nil_succ
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract)
    (state : State) :
    execSeq (fuel + 1) [] code state = pure state := by
  simp [execSeq, Yul.Source.Canonical.execSeq,
    Yul.Source.Effectful.execSeq]

theorem cons_succ
    (fuel : Nat) (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    execSeq (fuel + 1) (stmt :: rest) code state =
      Simulation.Interaction.bind (exec fuel stmt code state)
        (fun stateAfterStmt =>
          match stateAfterStmt with
          | .Ok _ _ => execSeq fuel rest code stateAfterStmt
          | .OutOfFuel | .Checkpoint _ => pure stateAfterStmt) := by
  simp only [execSeq, exec, Yul.Source.Canonical.execSeq,
    Yul.Source.Canonical.exec, Yul.Source.Effectful.execSeq]
  rfl

end ExecSeq

namespace Exec

theorem zero
    (stmt : EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec 0 stmt code state = Primitive.fail state .OutOfFuel := by
  simp [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    Primitive.fail, Yul.Source.Effectful.Control.fail]
  change
    Simulation.Interaction.done
        (.error ({ exception := .OutOfFuel, state := state } : Failure) :
          Except Failure State) =
      Simulation.Interaction.done
        (.error ({ exception := .OutOfFuel, state := state } : Failure) :
          Except Failure State)
  rfl

theorem block_succ
    (fuel : Nat) (body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec (fuel + 1) (.Block body) code state =
      Simulation.Interaction.bind (execSeq fuel body code state)
        (fun stateAfterBody =>
          pure (stateAfterBody.restrictStoreTo state.store)) := by
  simp only [exec, execSeq, Yul.Source.Canonical.exec,
    Yul.Source.Canonical.execSeq, Yul.Source.Effectful.exec]
  rfl

theorem if_succ
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec (fuel + 1) (.If cond body) code state =
      Simulation.Interaction.bind (eval fuel cond code state)
        (fun result =>
          if result.2 ≠ EvmYul.UInt256.ofNat 0 then
            exec fuel (.Block body) code result.1
          else
            pure result.1) := by
  simp only [exec, eval, Yul.Source.Canonical.exec,
    Yul.Source.Canonical.eval, Yul.Source.Effectful.exec]
  rfl

theorem switch_succ
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (cases : List (Word × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec (fuel + 1) (.Switch cond cases defaultBody) code state =
      Simulation.Interaction.bind (eval fuel cond code state)
        (fun result =>
          exec fuel
            (.Block
              (EvmYul.Yul.selectSwitchCase
                result.2 defaultBody cases))
            code result.1) := by
  simp only [exec, eval, Yul.Source.Canonical.exec,
    Yul.Source.Canonical.eval, Yul.Source.Effectful.exec]
  rfl

theorem for_succ
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec (fuel + 1) (.For cond post body) code state =
      loop fuel cond post body code state := by
  simp only [exec, loop, Yul.Source.Canonical.exec,
    Yul.Source.Canonical.loop, Yul.Source.Effectful.exec]

theorem brk_zero
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec 0 .Break code state = Primitive.fail state .OutOfFuel :=
  zero .Break code state

theorem brk_succ
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract)
    (state : State) :
    exec (fuel + 1) .Break code state = pure state.setBreak := by
  simp [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    stateModel]

theorem cont_succ
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract)
    (state : State) :
    exec (fuel + 1) .Continue code state = pure state.setContinue := by
  simp [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    stateModel]

theorem leave_succ
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract)
    (state : State) :
    exec (fuel + 1) .Leave code state = pure state.setLeave := by
  simp [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    stateModel]

theorem let_none_succ
    (fuel : Nat) (names : List EvmYul.Identifier)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkDeclaration state names = .ok ()) :
    exec (fuel + 1) (.Let names none) code state =
      pure (state.zeroFill names) := by
  simp [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    hCheck, stateModel]

theorem let_one_succ
    (fuel : Nat) (name : EvmYul.Identifier)
    (expr : EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkDeclaration state [name] = .ok ()) :
    exec (fuel + 1) (.Let [name] (some expr)) code state =
      Simulation.Interaction.bind (evalValues fuel expr code state)
        (fun result =>
          pure (stateModel.multifill [name] result.1 result.2)) := by
  simp [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    evalValues, hCheck, Yul.Source.Effectful.Control.multifill, stateModel]
  rfl

theorem assign_one_succ
    (fuel : Nat) (name : EvmYul.Identifier)
    (expr : EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkAssignment state [name] = .ok ()) :
    exec (fuel + 1) (.Assign [name] expr) code state =
      Simulation.Interaction.bind (evalValues fuel expr code state)
        (fun result =>
          pure (stateModel.multifill [name] result.1 result.2)) := by
  simp [exec, Yul.Source.Canonical.exec, Yul.Source.Effectful.exec,
    evalValues, hCheck, Yul.Source.Effectful.Control.multifill, stateModel]
  rfl

/-- A primitive expression statement is canonical value evaluation followed
by the empty destination assignment. -/
theorem expr_primitive
    (fuel : Nat) (prim : EvmYul.Operation .Yul)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec fuel (.ExprStmtCall (.Call (.inl prim) args)) code state =
      Simulation.Interaction.bind
        (evalValues fuel (.Call (.inl prim) args) code state)
        (fun result =>
          pure (stateModel.multifill [] result.1 result.2)) := by
  cases fuel with
  | zero =>
      simp only [exec, evalValues, Yul.Source.Canonical.exec,
        Yul.Source.Canonical.evalValues, Yul.Source.Effectful.exec,
        Yul.Source.Effectful.evalValues]
      unfold Yul.Source.Effectful.Control.fail
      rfl
  | succ fuel =>
      simp only [exec, evalValues, Yul.Source.Canonical.exec,
        Yul.Source.Canonical.evalValues, Yul.Source.Effectful.exec,
        Yul.Source.Effectful.evalValues,
        Yul.Source.Effectful.Control.multifill]
      change
        Simulation.Interaction.bind
            (evalArgs fuel args.reverse code state)
            (fun argsResult =>
              Simulation.Interaction.bind
                (primitiveSemantics.eval fuel argsResult.1 prim
                  argsResult.2.reverse)
                (fun result =>
                  pure (stateModel.multifill [] result.1 result.2))) =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind
              (evalArgs fuel args.reverse code state)
              (fun argsResult =>
                primitiveSemantics.eval fuel argsResult.1 prim
                  argsResult.2.reverse))
            (fun result =>
              pure (stateModel.multifill [] result.1 result.2))
      exact
        (Simulation.Interaction.bind_assoc
          (evalArgs fuel args.reverse code state)
          (fun argsResult =>
            primitiveSemantics.eval fuel argsResult.1 prim
              argsResult.2.reverse)
          (fun result =>
            pure (stateModel.multifill [] result.1 result.2))).symm

end Exec

namespace Program

def openRun (fuel : Nat) (code : EvmYul.Yul.Ast.YulContract)
    (state : State) : Open (State × List Word) :=
  Yul.Source.Canonical.Program.run
    stateModel primitiveSemantics fuel code state

end Program

end InteractionSemantics
end Yul
end EvmCompiler
