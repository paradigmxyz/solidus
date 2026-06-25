import EvmCompiler.Simulation.Interaction
import EvmCompiler.Yul.EffectSemantics
import EvmCompiler.Yul.Installation
import EvmCompiler.Yul.Primitive
import EvmCompiler.Yul.VarStoreRestriction

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

/-- Source-facing assertion that the active Yul frame observes a particular
byte image through `codesize` and `codecopy`. -/
def CodeImageInstalled (state : State) (image : ByteArray) : Prop :=
  match state with
  | .Ok shared _ => shared.executionEnv.codeBytes = image
  | _ => False

theorem installContractWithCodeImage_codeImageInstalled
    (contract : AstContract) (image : ByteArray)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) :
    CodeImageInstalled
      (.Ok
        (Source.Installation.installContractWithCodeImage
          contract image shared)
        store)
      image := by
  rfl

theorem restrictStoreTo_idem (state : State)
    (scope : EvmYul.Yul.VarStore) :
    (state.restrictStoreTo scope).restrictStoreTo scope =
      state.restrictStoreTo scope := by
  have hVars (vars : EvmYul.Yul.VarStore) :
      EvmYul.Yul.State.restrictVarStore
          (EvmYul.Yul.State.restrictVarStore vars scope) scope =
        EvmYul.Yul.State.restrictVarStore vars scope := by
    rw [VarStoreRestriction.restrict_restrict_of_inner_defined]
    intro key value hLookup
    exact ⟨value, hLookup⟩
  cases state with
  | OutOfFuel => rfl
  | Ok shared vars => simpa [EvmYul.Yul.State.restrictStoreTo] using hVars vars
  | Checkpoint jump =>
      cases jump with
      | Break shared vars | Continue shared vars | Leave shared vars =>
          simpa [EvmYul.Yul.State.restrictStoreTo] using hVars vars

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

@[simp] theorem bind_fail {α β : Type} (state : State)
    (exception : EvmYul.Yul.Exception) (next : α → Open β) :
    Simulation.Interaction.bind (fail state exception) next =
      fail state exception := rfl

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

theorem eval_eq_bind
    (fuel : Nat) (expr : EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    eval fuel expr code state =
      Simulation.Interaction.bind (evalValues fuel expr code state)
        (fun result => pure (result.1, result.2.head!)) := by
  unfold eval Yul.Source.Canonical.eval Yul.Source.Effectful.eval
  rfl

namespace Call

/-- An internal call with exhausted canonical meta-fuel fails before resolving
the active source contract. -/
theorem zero
    (args : List Word)
    (functionName? : Option EvmYul.Yul.Ast.YulFunctionName)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    call 0 args functionName? code state =
      Primitive.fail state .OutOfFuel := by
  unfold call Yul.Source.Canonical.call Yul.Source.Effectful.call
    Yul.Source.Effectful.Control.fail Primitive.fail
  rfl

/-- Positive-fuel internal calls against an explicit active program expose
exactly the selected source body and caller-frame restoration. -/
theorem explicit_succ
    (fuel : Nat) (args : List Word)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (code : EvmYul.Yul.Ast.YulContract)
    (params returns : List EvmYul.Identifier)
    (body : List EvmYul.Yul.Ast.Stmt) (state : State)
    (hLookup : code.functions.lookup functionName =
      some (.Def params returns body)) :
    call (fuel + 1) args (some functionName) (some code) state =
      Simulation.Interaction.bind
        (exec fuel (.Block body) (some code)
          (EvmYul.Yul.State.mkOk
            (state.initcall params returns args)))
        (fun stateAfterBody =>
          pure
            ((stateAfterBody.reviveJump.overwrite? state).setStore state,
              List.map stateAfterBody.lookup! returns)) := by
  simp only [call, Yul.Source.Canonical.call,
    Yul.Source.Effectful.call, Yul.Source.Effectful.resolveActiveCode?_some,
    hLookup, stateModel]
  rfl

end Call

namespace EvalValues

/-- Every expression exhausts canonical meta-fuel before inspection at zero. -/
theorem zero
    (expr : EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    evalValues 0 expr code state = Primitive.fail state .OutOfFuel := by
  unfold evalValues Yul.Source.Canonical.evalValues
    Yul.Source.Effectful.evalValues Yul.Source.Effectful.Control.fail
    Primitive.fail
  rfl

/-- Positive-fuel internal value evaluation exposes ordered argument
evaluation followed by the canonical internal call. -/
theorem internal_succ
    (fuel : Nat) (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    evalValues (fuel + 1) (.Call (.inr functionName) args) code state =
      Simulation.Interaction.bind
        (evalArgs fuel args.reverse code state)
        (fun result =>
          call fuel result.2.reverse (some functionName) code result.1) := by
  simp only [evalValues, Yul.Source.Canonical.evalValues,
    Yul.Source.Effectful.evalValues]
  rfl

theorem call_succ
    (fuel : Nat)
    (callee : EvmYul.Operation .Yul ⊕ EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    evalValues (fuel + 1) (.Call callee args) code state =
      Simulation.Interaction.bind
        (evalArgs fuel args.reverse code state)
        (fun result =>
          match callee with
          | .inl prim =>
              primitiveSemantics.eval fuel result.1 prim result.2.reverse
          | .inr functionName =>
              call fuel result.2.reverse (some functionName) code result.1) := by
  cases callee with
  | inl prim =>
      simp only [evalValues, Yul.Source.Canonical.evalValues,
        Yul.Source.Effectful.evalValues]
      rfl
  | inr functionName =>
      exact internal_succ fuel functionName args code state

end EvalValues

namespace EvalArgs

/-- Every argument list exhausts canonical meta-fuel before inspection at
zero. -/
theorem zero
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    evalArgs 0 args code state = Primitive.fail state .OutOfFuel := by
  unfold evalArgs Yul.Source.Canonical.evalArgs
    Yul.Source.Effectful.evalArgs Yul.Source.Effectful.Control.fail
    Primitive.fail
  rfl

/-- An empty argument list completes without inspecting the residual positive
fuel. -/
theorem nil_succ
    (fuel : Nat) (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    evalArgs (fuel + 1) [] code state = pure (state, []) := by
  simp [evalArgs, Yul.Source.Canonical.evalArgs,
    Yul.Source.Effectful.evalArgs]

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

/-- A nonempty argument list at fuel one fails in its head value evaluation. -/
theorem one_nonempty
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hArgs : args ≠ []) :
    evalArgs 1 args code state = Primitive.fail state .OutOfFuel := by
  cases args with
  | nil => exact (hArgs rfl).elim
  | cons head rest =>
      rw [one_cons, EvalValues.zero, Primitive.bind_fail]

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

/-- Split ordered argument evaluation at a list boundary. The suffix receives
the exact residual list fuel after two units per prefix expression. -/
theorem append
    {fuel : Nat} (left right : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    evalArgs fuel (left ++ right) code state =
      Simulation.Interaction.bind
        (evalArgs fuel left code state)
        (fun leftResult =>
          Simulation.Interaction.bind
            (evalArgs (fuel - 2 * left.length) right code leftResult.1)
            (fun rightResult =>
              pure
                (rightResult.1, leftResult.2 ++ rightResult.2))) := by
  induction left generalizing fuel state with
  | nil =>
      cases fuel with
      | zero =>
          simp only [List.nil_append, List.length_nil, Nat.mul_zero,
            Nat.sub_zero]
          unfold evalArgs Yul.Source.Canonical.evalArgs
            Yul.Source.Effectful.evalArgs
          unfold Yul.Source.Effectful.Control.fail
          change
            Simulation.Interaction.error
                ({ exception := .OutOfFuel, state := state } : Failure) =
              Simulation.Interaction.bind
                (Simulation.Interaction.error
                  ({ exception := .OutOfFuel, state := state } : Failure)) _
          exact
            (Simulation.Interaction.monad_error_bind
              ({ exception := .OutOfFuel, state := state } : Failure) _).symm
      | succ fuel =>
          simp only [List.nil_append, List.length_nil, Nat.mul_zero,
            Nat.sub_zero]
          rw [show
            evalArgs (fuel + 1) [] code state = pure (state, []) by
              simp [evalArgs, Yul.Source.Canonical.evalArgs,
                Yul.Source.Effectful.evalArgs]]
          change
            evalArgs (fuel + 1) right code state =
              Simulation.Interaction.bind
                (Simulation.Interaction.done (.ok (state, []))) _
          rw [Simulation.Interaction.bind_done_ok]
          change
            evalArgs (fuel + 1) right code state =
              Simulation.Interaction.bind
                (evalArgs (fuel + 1) right code state)
                Simulation.Interaction.pure
          exact
            (Simulation.Interaction.bind_pure
              (evalArgs (fuel + 1) right code state)).symm
  | cons head rest ih =>
      cases fuel with
      | zero =>
          unfold evalArgs Yul.Source.Canonical.evalArgs
            Yul.Source.Effectful.evalArgs
          unfold Yul.Source.Effectful.Control.fail
          change
            Simulation.Interaction.error
                ({ exception := .OutOfFuel, state := state } : Failure) =
              Simulation.Interaction.bind
                (Simulation.Interaction.error
                  ({ exception := .OutOfFuel, state := state } : Failure)) _
          exact
            (Simulation.Interaction.monad_error_bind
              ({ exception := .OutOfFuel, state := state } : Failure) _).symm
      | succ fuel =>
          cases fuel with
          | zero =>
              rw [List.cons_append, one_cons, one_cons]
              have hZero :
                  evalValues 0 head code state =
                    Primitive.fail state .OutOfFuel := by
                unfold evalValues Yul.Source.Canonical.evalValues
                  Yul.Source.Effectful.evalValues
                rfl
              rw [hZero]
              unfold Primitive.fail
              change
                Simulation.Interaction.error
                    ({ exception := .OutOfFuel, state := state } : Failure) =
                  Simulation.Interaction.error
                    ({ exception := .OutOfFuel, state := state } : Failure)
              rfl
          | succ tailFuel =>
              rw [List.cons_append, show tailFuel + 1 + 1 = tailFuel + 2 by
                omega, succ_succ_cons, succ_succ_cons]
              rw [Simulation.Interaction.bind_assoc]
              apply congrArg
              funext headResult
              rw [ih headResult.1]
              have hResidual :
                  tailFuel + 2 - 2 * (head :: rest).length =
                    tailFuel - 2 * rest.length := by
                simp only [List.length_cons]
                omega
              rw [hResidual]
              simp only [Simulation.Interaction.bind_assoc,
                Simulation.Interaction.monad_pure_bind]
              apply congrArg
              funext restResult
              change
                Simulation.Interaction.bind
                    (evalArgs (tailFuel - 2 * rest.length)
                      right code restResult.1)
                    (fun rightResult =>
                      Simulation.Interaction.bind
                        (Simulation.Interaction.done
                          (.ok
                            (rightResult.1,
                              restResult.2 ++ rightResult.2)))
                        (fun tailResult =>
                          pure
                            (tailResult.1,
                              headResult.2.head! :: tailResult.2))) =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.done
                      (.ok
                        (restResult.1,
                          headResult.2.head! :: restResult.2)))
                    (fun leftResult =>
                      Simulation.Interaction.bind
                        (evalArgs (tailFuel - 2 * rest.length)
                          right code leftResult.1)
                        (fun rightResult =>
                          pure
                            (rightResult.1,
                              leftResult.2 ++ rightResult.2)))
              apply congrArg
              funext rightResult
              change
                Simulation.Interaction.bind
                    (Simulation.Interaction.done
                      (.ok
                        (rightResult.1,
                          restResult.2 ++ rightResult.2)))
                    (fun tailResult =>
                      pure
                        (tailResult.1,
                          headResult.2.head! :: tailResult.2)) =
                  pure
                    (rightResult.1,
                      (headResult.2.head! :: restResult.2) ++ rightResult.2)
              rw [Simulation.Interaction.bind_done_ok]
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

def DoneRestrictedTo (scope : EvmYul.Yul.VarStore) :
    Except Failure State → Prop
  | .error _ => True
  | .ok state => state.restrictStoreTo scope = state

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

/-- Every successful result of a lexical block has already been restricted to
the block-entry store. This is the source-side invariant needed when an outer
loop catches a `break` or routes a `continue` through its post block. -/
theorem block_allDone_restricted
    (fuel : Nat) (body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    Simulation.Interaction.AllDone (DoneRestrictedTo state.store)
      (exec (fuel + 1) (.Block body) code state) := by
  rw [block_succ]
  apply Simulation.Interaction.AllDone.bind
    (Simulation.Interaction.AllDone.trivial
      (execSeq fuel body code state))
  · intro _error _hTrivial
    trivial
  · intro stateAfterBody _hTrivial
    exact Simulation.Interaction.AllDone.done
      (State.restrictStoreTo_idem stateAfterBody state.store)

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

theorem loop_zero
    (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    loop 0 cond post body code state = Primitive.fail state .OutOfFuel := by
  unfold loop Yul.Source.Canonical.loop Yul.Source.Effectful.loop
  rfl

theorem loop_one
    (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    loop 1 cond post body code state = Primitive.fail state .OutOfFuel := by
  unfold loop Yul.Source.Canonical.loop Yul.Source.Effectful.loop
  rfl

theorem loop_succ_succ
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    loop (fuel + 1 + 1) cond post body code state =
      Simulation.Interaction.bind
        (eval fuel cond code
          (stateModel.withSource state
            (EvmYul.Yul.State.mkOk (stateModel.source state))))
        (fun result =>
          if result.2 = EvmYul.UInt256.ofNat 0 then
            pure
              (stateModel.withSource result.1
                ((stateModel.source result.1).overwrite?
                  (stateModel.source state)))
          else
            Simulation.Interaction.bind
              (exec fuel (.Block body) code result.1)
              (fun stateAfterBody =>
                let source := stateModel.source state
                let bodySource := stateModel.source stateAfterBody
                match bodySource with
                | .OutOfFuel =>
                    pure
                      (stateModel.withSource stateAfterBody
                        (bodySource.overwrite? source))
                | .Checkpoint (.Break _ _) =>
                    pure
                      (stateModel.withSource stateAfterBody
                        (bodySource.reviveJump.overwrite? source))
                | .Checkpoint (.Leave _ _) =>
                    pure
                      (stateModel.withSource stateAfterBody
                        (bodySource.overwrite? source))
                | .Checkpoint (.Continue _ _) | _ =>
                    Simulation.Interaction.bind
                      (exec fuel (.Block post) code
                        (stateModel.withSource stateAfterBody
                          bodySource.reviveJump))
                      (fun stateAfterPost =>
                        let postSource := stateModel.source stateAfterPost
                        let sourceAfterPost := postSource.overwrite? source
                        match postSource with
                        | .OutOfFuel =>
                            pure
                              (stateModel.withSource stateAfterPost
                                sourceAfterPost)
                        | .Checkpoint (.Leave _ _) =>
                            pure
                              (stateModel.withSource stateAfterPost
                                sourceAfterPost)
                        | _ =>
                            Simulation.Interaction.bind
                              (exec fuel (.For cond post body) code
                                (stateModel.withSource stateAfterPost
                                  sourceAfterPost))
                              (fun stateAfterLoop =>
                                pure
                                  (stateModel.withSource stateAfterLoop
                                    ((stateModel.source stateAfterLoop).overwrite?
                                      source)))))) := by
  unfold loop Yul.Source.Canonical.loop Yul.Source.Effectful.loop
  rfl

/-- Factor one canonical loop iteration through the guarded condition/body
shape used by the ordinary Yul compiler. This is specialized to a valid `Ok`
loop entry, where the kernel's outer `overwrite?` operations are identities. -/
theorem loop_succ_succ_guarded
    (fuel : Nat) (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (entryShared : EvmYul.SharedState .Yul)
    (entryVars : EvmYul.Yul.VarStore) :
    loop (fuel + 1 + 1) cond post body code (.Ok entryShared entryVars) =
      Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (evalValues fuel cond code (.Ok entryShared entryVars))
          (fun result =>
            if result.2.head! = EvmYul.UInt256.ofNat 0 then
              Simulation.Interaction.pure (.inl result.1)
            else
              Simulation.Interaction.map Sum.inr
                (exec fuel (.Block body) code result.1)))
        (fun guarded =>
          match guarded with
          | .inl stateAfterCond => Simulation.Interaction.pure stateAfterCond
          | .inr stateAfterBody =>
              match stateAfterBody with
              | .OutOfFuel => Simulation.Interaction.pure .OutOfFuel
              | .Checkpoint (.Break shared vars) =>
                  Simulation.Interaction.pure (.Ok shared vars)
              | .Checkpoint (.Leave shared vars) =>
                  Simulation.Interaction.pure
                    (.Checkpoint (.Leave shared vars))
              | .Checkpoint (.Continue shared vars) | .Ok shared vars =>
                  Simulation.Interaction.bind
                    (exec fuel (.Block post) code (.Ok shared vars))
                    (fun stateAfterPost =>
                      match stateAfterPost with
                      | .OutOfFuel => Simulation.Interaction.pure .OutOfFuel
                      | .Checkpoint (.Leave shared vars) =>
                          Simulation.Interaction.pure
                            (.Checkpoint (.Leave shared vars))
                      | _ =>
                          exec fuel (.For cond post body) code stateAfterPost)) := by
  rw [loop_succ_succ, eval_eq_bind,
    Simulation.Interaction.bind_assoc,
    Simulation.Interaction.bind_assoc]
  simp only [stateModel, id_eq, EvmYul.Yul.State.mkOk,
    EvmYul.Yul.State.overwrite?]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (evalValues fuel cond code (.Ok entryShared entryVars)))
  intro result _hResult
  have pure_eq : ∀ {α : Type} (value : α),
      (pure value : Open α) = Simulation.Interaction.pure value :=
    fun _ => rfl
  rw [pure_eq (result.1, result.2.head!),
    show Simulation.Interaction.pure (result.1, result.2.head!) =
      Simulation.Interaction.done (.ok (result.1, result.2.head!)) by rfl,
    Simulation.Interaction.bind_done_ok]
  by_cases hZero : result.2.head! = EvmYul.UInt256.ofNat 0
  · simp [hZero, stateModel, pure_eq, Simulation.Interaction.pure,
      Simulation.Interaction.bind]
  · simp only [hZero, ↓reduceIte]
    unfold Simulation.Interaction.map
    rw [Simulation.Interaction.bind_assoc]
    apply Simulation.Interaction.AllDone.bind_congr
      (Simulation.Interaction.AllDone.trivial
        (exec fuel (.Block body) code result.1))
    intro stateAfterBody _hBody
    rw [show Simulation.Interaction.pure (Sum.inr stateAfterBody) =
        Simulation.Interaction.done (.ok (Sum.inr stateAfterBody)) by rfl,
      Simulation.Interaction.bind_done_ok]
    cases stateAfterBody with
    | OutOfFuel => rfl
    | Ok shared vars =>
        simp [stateModel, EvmYul.Yul.State.reviveJump,
          EvmYul.Yul.State.overwrite?, pure_eq,
          Simulation.Interaction.bind_pure]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial
            (exec fuel (.Block post) code (.Ok shared vars)))
        intro stateAfterPost _hPost
        cases stateAfterPost with
        | OutOfFuel => rfl
        | Ok => rfl
        | Checkpoint jump => cases jump <;> rfl
    | Checkpoint jump =>
        cases jump with
        | Break shared vars =>
            simp [stateModel, EvmYul.Yul.State.reviveJump,
              EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?, pure_eq]
        | Leave shared vars =>
            simp [stateModel, EvmYul.Yul.State.reviveJump,
              EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?, pure_eq]
        | Continue shared vars =>
            simp [stateModel, EvmYul.Yul.State.reviveJump,
              EvmYul.Yul.State.revive, EvmYul.Yul.State.overwrite?,
              pure_eq, Simulation.Interaction.bind_pure]
            apply Simulation.Interaction.AllDone.bind_congr
              (Simulation.Interaction.AllDone.trivial
                (exec fuel (.Block post) code (.Ok shared vars)))
            intro stateAfterPost _hPost
            cases stateAfterPost with
            | OutOfFuel => rfl
            | Ok => rfl
            | Checkpoint jump => cases jump <;> rfl

theorem loop_two
    (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul) (vars : EvmYul.Yul.VarStore) :
    loop 2 cond post body code (.Ok shared vars) =
      Primitive.fail (.Ok shared vars) .OutOfFuel := by
  rw [show 2 = 0 + 1 + 1 by omega,
    loop_succ_succ_guarded]
  have hEval :
      evalValues 0 cond code (.Ok shared vars) =
        Primitive.fail (.Ok shared vars) .OutOfFuel := by
    unfold evalValues Yul.Source.Canonical.evalValues
      Yul.Source.Effectful.evalValues
    rfl
  rw [hEval]
  simp [Primitive.fail, Yul.Source.Effectful.Control.fail]

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

theorem let_some_succ
    (fuel : Nat) (names : List EvmYul.Identifier)
    (expr : EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkDeclaration state names = .ok ()) :
    exec (fuel + 1) (.Let names (some expr)) code state =
      Simulation.Interaction.bind (evalValues fuel expr code state)
        (fun result =>
          pure (stateModel.multifill names result.1 result.2)) := by
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

theorem assign_succ
    (fuel : Nat) (names : List EvmYul.Identifier)
    (expr : EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkAssignment state names = .ok ()) :
    exec (fuel + 1) (.Assign names expr) code state =
      Simulation.Interaction.bind (evalValues fuel expr code state)
        (fun result =>
          pure (stateModel.multifill names result.1 result.2)) := by
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

/-- A positive-fuel internal-call expression statement exposes ordered argument
evaluation, the canonical internal call, and empty-destination writeback. -/
theorem expr_internal_succ
    (fuel : Nat) (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec (fuel + 2) (.ExprStmtCall (.Call (.inr functionName) args))
        code state =
      Simulation.Interaction.bind
        (evalArgs (fuel + 1) args.reverse code state)
        (fun argsResult =>
          Simulation.Interaction.bind
            (call fuel argsResult.2.reverse (some functionName)
              code argsResult.1)
            (fun callResult =>
              pure (stateModel.multifill [] callResult.1 callResult.2))) := by
  simp only [exec, evalValues, Yul.Source.Canonical.exec,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.exec,
    Yul.Source.Effectful.evalValues,
    Yul.Source.Effectful.Control.multifill]
  rfl

/-- Internal-call expression statements exhaust canonical meta-fuel before
executing arguments or the callee at the first positive fuel level. -/
theorem expr_internal_one
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec 1 (.ExprStmtCall (.Call (.inr functionName) args)) code state =
      Primitive.fail state .OutOfFuel := by
  unfold exec Yul.Source.Canonical.exec Yul.Source.Effectful.exec
  change
    Simulation.Interaction.bind
        (evalArgs 0 args.reverse code state)
        (fun argsResult => Primitive.fail argsResult.1 .OutOfFuel) =
      Primitive.fail state .OutOfFuel
  rw [EvalArgs.zero, Primitive.bind_fail]

/-- With two units of canonical meta-fuel, an internal-call expression
statement still exhausts fuel before any argument value can complete. -/
theorem expr_internal_two
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) :
    exec 2 (.ExprStmtCall (.Call (.inr functionName) args)) code state =
      Primitive.fail state .OutOfFuel := by
  rw [show 2 = 0 + 2 by omega, expr_internal_succ]
  cases hArgs : args.reverse with
  | nil =>
      rw [EvalArgs.nil_succ]
      change
        Simulation.Interaction.bind
            (.done (.ok (state, [])))
            (fun argsResult =>
              Simulation.Interaction.bind
                (call 0 argsResult.2.reverse (some functionName)
                  code argsResult.1) _) =
          Primitive.fail state .OutOfFuel
      rw [Simulation.Interaction.bind_done_ok, Call.zero,
        Primitive.bind_fail]
  | cons head rest =>
      rw [EvalArgs.one_nonempty _ code state (by simp [hArgs]),
        Primitive.bind_fail]

/-- Checked declaration calls at fuel one fail before value evaluation. -/
theorem let_internal_one
    (names : List EvmYul.Identifier)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkDeclaration state names = .ok ()) :
    exec 1 (.Let names (some (.Call (.inr functionName) args))) code state =
      Primitive.fail state .OutOfFuel := by
  rw [show 1 = 0 + 1 by omega,
    let_some_succ 0 names _ code state hCheck,
    EvalValues.zero, Primitive.bind_fail]

/-- Checked declaration calls at fuel two fail in argument evaluation. -/
theorem let_internal_two
    (names : List EvmYul.Identifier)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkDeclaration state names = .ok ()) :
    exec 2 (.Let names (some (.Call (.inr functionName) args))) code state =
      Primitive.fail state .OutOfFuel := by
  rw [show 2 = 1 + 1 by omega,
    let_some_succ 1 names _ code state hCheck,
    EvalValues.internal_succ 0, EvalArgs.zero,
    Primitive.bind_fail, Primitive.bind_fail]

/-- Checked assignment calls at fuel one fail before value evaluation. -/
theorem assign_internal_one
    (names : List EvmYul.Identifier)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkAssignment state names = .ok ()) :
    exec 1 (.Assign names (.Call (.inr functionName) args)) code state =
      Primitive.fail state .OutOfFuel := by
  rw [show 1 = 0 + 1 by omega,
    assign_succ 0 names _ code state hCheck,
    EvalValues.zero, Primitive.bind_fail]

/-- Checked assignment calls at fuel two fail in argument evaluation. -/
theorem assign_internal_two
    (names : List EvmYul.Identifier)
    (functionName : EvmYul.Yul.Ast.YulFunctionName)
    (args : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State)
    (hCheck : EvmYul.Yul.checkAssignment state names = .ok ()) :
    exec 2 (.Assign names (.Call (.inr functionName) args)) code state =
      Primitive.fail state .OutOfFuel := by
  rw [show 2 = 1 + 1 by omega,
    assign_succ 1 names _ code state hCheck,
    EvalValues.internal_succ 0, EvalArgs.zero,
    Primitive.bind_fail, Primitive.bind_fail]

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
