import EvmCompiler.Yul.Syntax
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace Yul
namespace Source
namespace Effectful

/-!
Reusable effect-carrying semantics for the imported Yul AST.

The control evaluator is parameterized by a source-state projection and a
primitive handler. Observer replay and future effect handlers can extend state
without copying Yul expression, call, block, switch, or loop evaluation.
-/

structure StateModel (σ : Type) where
  source : σ → EvmYul.Yul.State
  withSource : σ → EvmYul.Yul.State → σ

structure Failure (σ : Type) where
  exception : EvmYul.Yul.Exception
  state : σ

abbrev Result (σ α : Type) :=
  Except (Failure σ) α

def fail {σ α : Type} (state : σ) (exception : EvmYul.Yul.Exception) :
    Result σ α :=
  .error { exception := exception, state := state }

structure PrimitiveSemantics (σ : Type) where
  eval :
    Nat → σ → EvmYul.Operation .Yul → List Word →
      Result σ (σ × List Word)

namespace StateModel

def multifill {σ : Type} (model : StateModel σ)
    (vars : List EvmYul.Identifier) (state : σ) (values : List Word) : σ :=
  model.withSource state ((model.source state).multifill vars values)

end StateModel

def multifill {σ : Type} (model : StateModel σ)
    (vars : List EvmYul.Identifier) :
    Result σ (σ × List Word) → Result σ σ
  | .ok (state, values) => .ok (model.multifill vars state values)
  | .error failure => .error failure

mutual

  def evalTail {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat)
      (args : List EvmYul.Yul.Ast.Expr)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (result : Result σ (σ × Word)) :
      Result σ (σ × List Word) :=
    match result with
    | .ok (state, arg) =>
        match fuel with
        | 0 => fail state .OutOfFuel
        | fuel' + 1 =>
            match evalArgs model prim fuel' args codeOverride state with
            | .ok (state', args') => .ok (state', arg :: args')
            | .error failure => .error failure
    | .error failure => .error failure
  termination_by (fuel, 0, sizeOf args)

  def evalArgs {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat)
      (args : List EvmYul.Yul.Ast.Expr)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (state : σ) :
      Result σ (σ × List Word) :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match args with
        | [] => .ok (state, [])
        | arg :: args =>
            evalTail model prim fuel' args codeOverride
              (eval model prim fuel' arg codeOverride state)
  termination_by (fuel, 1, sizeOf args)

  def evalValues {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat)
      (expr : EvmYul.Yul.Ast.Expr)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (state : σ) :
      Result σ (σ × List Word) :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match expr with
        | .Call (.inl op) args =>
            match evalArgs model prim fuel' args.reverse codeOverride state with
            | .ok (stateAfterArgs, values) =>
                prim.eval fuel' stateAfterArgs op values.reverse
            | .error failure => .error failure
        | .Call (.inr functionName) args =>
            match evalArgs model prim fuel' args.reverse codeOverride state with
            | .ok (stateAfterArgs, values) =>
                call model prim fuel' values.reverse (some functionName)
                  codeOverride stateAfterArgs
            | .error failure => .error failure
        | .Var id =>
            match (model.source state).lookup? id with
            | some value => .ok (state, [value])
            | none => fail state (.UnknownIdentifier id)
        | .Lit value => .ok (state, [value])
  termination_by (fuel, 2, sizeOf expr)

  def eval {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat)
      (expr : EvmYul.Yul.Ast.Expr)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (state : σ) :
      Result σ (σ × Word) :=
    match evalValues model prim fuel expr codeOverride state with
    | .ok (state', values) => .ok (state', values.head!)
    | .error failure => .error failure
  termination_by (fuel, 3, sizeOf expr)

  def call {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat) (args : List Word)
      (functionName? : Option EvmYul.Yul.Ast.YulFunctionName)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (state : σ) :
      Result σ (σ × List Word) :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        let source := model.source state
        match source.sharedState.accountMap.find?
            source.executionEnv.codeOwner with
        | none =>
            fail state (.MissingContract (s!"{source.executionEnv.codeOwner}"))
        | some yulContract =>
            let code : EvmYul.Yul.Ast.YulContract :=
              codeOverride.getD yulContract.code
            let function? : Option EvmYul.Yul.Ast.FunctionDefinition :=
              match functionName? with
              | none =>
                  some
                    (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
                      [code.dispatcher])
              | some functionName =>
                  code.functions.lookup functionName
            match function? with
            | none =>
                fail state
                  (.MissingContractFunction (functionName?.getD ".none"))
            | some function =>
                match function with
                | EvmYul.Yul.Ast.FunctionDefinition.Def params rets body =>
                    let sourceAtEntry :=
                      EvmYul.Yul.State.mkOk
                        (source.initcall params rets args)
                    match exec model prim fuel' (.Block body) codeOverride
                        (model.withSource state sourceAtEntry) with
                    | .error failure => .error failure
                    | .ok stateAfterBody =>
                        let bodySource := model.source stateAfterBody
                        let sourceAfterCall :=
                          (bodySource.reviveJump.overwrite? source).setStore
                            source
                        .ok
                          (model.withSource stateAfterBody sourceAfterCall,
                            List.map bodySource.lookup! rets)
  termination_by (fuel, 4, sizeOf args)

  def callDispatcher {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (state : σ) :
      Result σ (σ × List Word) :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        let source := model.source state
        let function :=
          EvmYul.Yul.Ast.FunctionDefinition.Def [] []
            [source.executionEnv.code.dispatcher]
        match function with
        | EvmYul.Yul.Ast.FunctionDefinition.Def params rets body =>
            let sourceAtEntry :=
              EvmYul.Yul.State.mkOk (source.initcall params rets [])
            match exec model prim fuel' (.Block body) codeOverride
                (model.withSource state sourceAtEntry) with
            | .error failure => .error failure
            | .ok stateAfterBody =>
                let bodySource := model.source stateAfterBody
                let sourceAfterCall :=
                  (bodySource.reviveJump.overwrite? source).setStore source
                .ok
                  (model.withSource stateAfterBody sourceAfterCall,
                    List.map bodySource.lookup! rets)
  def execSeq {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat)
      (stmts : List EvmYul.Yul.Ast.Stmt)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (state : σ) :
      Result σ σ :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match stmts with
        | [] => .ok state
        | stmt :: stmts =>
            match exec model prim fuel' stmt codeOverride state with
            | .error failure => .error failure
            | .ok stateAfterStmt =>
                match model.source stateAfterStmt with
                | .Ok _ _ =>
                    execSeq model prim fuel' stmts codeOverride stateAfterStmt
                | .OutOfFuel => .ok stateAfterStmt
                | .Checkpoint _ => .ok stateAfterStmt
  termination_by (fuel, 6, sizeOf stmts)

  def exec {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat)
      (stmt : EvmYul.Yul.Ast.Stmt)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (state : σ) :
      Result σ σ :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        let source := model.source state
        match stmt with
        | .Block stmts =>
            match execSeq model prim fuel' stmts codeOverride state with
            | .error failure => .error failure
            | .ok stateAfterBody =>
                .ok
                  (model.withSource stateAfterBody
                    ((model.source stateAfterBody).restrictStoreTo source.store))
        | .Let vars expr? =>
            match EvmYul.Yul.checkDeclaration source vars with
            | .error err => fail state err
            | .ok () =>
                match expr? with
                | none =>
                    .ok (model.withSource state (source.zeroFill vars))
                | some expr =>
                    multifill model vars
                      (evalValues model prim fuel' expr codeOverride state)
        | .Assign vars expr =>
            match EvmYul.Yul.checkAssignment source vars with
            | .error err => fail state err
            | .ok () =>
                multifill model vars
                  (evalValues model prim fuel' expr codeOverride state)
        | .If cond body =>
            match eval model prim fuel' cond codeOverride state with
            | .error failure => .error failure
            | .ok (stateAfterCond, condValue) =>
                if condValue ≠ ⟨0⟩ then
                  exec model prim fuel' (.Block body) codeOverride
                    stateAfterCond
                else
                  .ok stateAfterCond
        | .ExprStmtCall expr =>
            match expr with
            | .Call (.inl op) args =>
                match
                    evalArgs model prim fuel' args.reverse codeOverride state
                with
                | .ok (stateAfterArgs, values) =>
                    multifill model []
                      (prim.eval fuel' stateAfterArgs op values.reverse)
                | .error failure => .error failure
            | .Call (.inr functionName) args =>
                match
                    evalArgs model prim fuel' args.reverse codeOverride state
                with
                | .ok (stateAfterArgs, values) =>
                    match fuel' with
                    | 0 => fail stateAfterArgs .OutOfFuel
                    | fuel'' + 1 =>
                        multifill model []
                          (call model prim fuel'' values.reverse
                            (some functionName) codeOverride stateAfterArgs)
                | .error failure => .error failure
            | _ => fail state .InvalidExpression
        | .Switch cond cases default =>
            match eval model prim fuel' cond codeOverride state with
            | .error failure => .error failure
            | .ok (stateAfterCond, condValue) =>
                exec model prim fuel'
                  (.Block
                    (EvmYul.Yul.selectSwitchCase condValue default cases))
                  codeOverride stateAfterCond
        | .For cond post body =>
            loop model prim fuel' cond post body codeOverride state
        | .Continue =>
            .ok
              (model.withSource state
                (EvmYul.Yul.State.setContinue source))
        | .Break =>
            .ok
              (model.withSource state
                (EvmYul.Yul.State.setBreak source))
        | .Leave =>
            .ok
              (model.withSource state
                (EvmYul.Yul.State.setLeave source))
  termination_by (fuel, 7, sizeOf stmt)

  def loop {σ : Type} (model : StateModel σ)
      (prim : PrimitiveSemantics σ) (fuel : Nat)
      (cond : EvmYul.Yul.Ast.Expr)
      (post body : List EvmYul.Yul.Ast.Stmt)
      (codeOverride : Option EvmYul.Yul.Ast.YulContract)
      (state : σ) :
      Result σ σ :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | 1 => fail state .OutOfFuel
    | fuel' + 1 + 1 =>
        let source := model.source state
        match
            eval model prim fuel' cond codeOverride
              (model.withSource state (EvmYul.Yul.State.mkOk source))
        with
        | .error failure => .error failure
        | .ok (stateAfterCond, condValue) =>
            if condValue = ⟨0⟩ then
              .ok
                (model.withSource stateAfterCond
                  ((model.source stateAfterCond).overwrite? source))
            else
              match
                  exec model prim fuel' (.Block body) codeOverride
                    stateAfterCond
              with
              | .error failure => .error failure
              | .ok stateAfterBody =>
                  let bodySource := model.source stateAfterBody
                  match bodySource with
                  | .OutOfFuel =>
                      .ok
                        (model.withSource stateAfterBody
                          (bodySource.overwrite? source))
                  | .Checkpoint (.Break _ _) =>
                      .ok
                        (model.withSource stateAfterBody
                          (bodySource.reviveJump.overwrite? source))
                  | .Checkpoint (.Leave _ _) =>
                      .ok
                        (model.withSource stateAfterBody
                          (bodySource.overwrite? source))
                  | .Checkpoint (.Continue _ _)
                  | _ =>
                      match
                          exec model prim fuel' (.Block post) codeOverride
                            (model.withSource stateAfterBody
                              bodySource.reviveJump)
                      with
                      | .error failure => .error failure
                      | .ok stateAfterPost =>
                          let postSource := model.source stateAfterPost
                          let sourceAfterPost := postSource.overwrite? source
                          match postSource with
                          | .OutOfFuel =>
                              .ok
                                (model.withSource stateAfterPost
                                  sourceAfterPost)
                          | .Checkpoint (.Leave _ _) =>
                              .ok
                                (model.withSource stateAfterPost
                                  sourceAfterPost)
                          | _ =>
                              match
                                  exec model prim fuel'
                                    (.For cond post body) codeOverride
                                    (model.withSource stateAfterPost
                                      sourceAfterPost)
                              with
                              | .error failure => .error failure
                              | .ok stateAfterLoop =>
                                  .ok
                                    (model.withSource stateAfterLoop
                                      ((model.source stateAfterLoop).overwrite?
                                        source))
  termination_by (fuel, 8, sizeOf cond + sizeOf post + sizeOf body)

  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega

end

theorem evalValues_lit_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {value : Word}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hRun :
      evalValues model prim fuel (.Lit value) codeOverride state =
        .ok (final, values)) :
    final = state ∧ values = [value] := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
  | succ previous =>
      simp [evalValues] at hRun
      exact ⟨hRun.1.symm, hRun.2.symm⟩

theorem evalValues_var_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {name : EvmYul.Identifier}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hRun :
      evalValues model prim fuel (.Var name) codeOverride state =
        .ok (final, values)) :
    ∃ value,
      (model.source state).lookup? name = some value ∧
        final = state ∧ values = [value] := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
  | succ previous =>
      cases hLookup : (model.source state).lookup? name with
      | none =>
          simp [evalValues, hLookup, fail] at hRun
      | some value =>
          simp [evalValues, hLookup] at hRun
          exact
            ⟨value, by simp [hLookup], hRun.1.symm, hRun.2.symm⟩

theorem evalValues_prim_nil_ok_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hRun :
      evalValues model primSemantics fuel (.Call (.inl prim) [])
          codeOverride state =
        .ok (final, values)) :
    ∃ previous,
      fuel = previous + 2 ∧
        primSemantics.eval previous.succ state prim [] =
          .ok (final, values) := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
  | succ first =>
      cases first with
      | zero =>
          simp [evalValues, evalArgs, fail] at hRun
      | succ previous =>
          exact
            ⟨previous, by omega,
              by simpa [evalValues, evalArgs] using hRun⟩

theorem evalValues_primitive_ok_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hRun :
      evalValues model primSemantics fuel (.Call (.inl prim) args)
          codeOverride state =
        .ok (final, values)) :
    ∃ callFuel stateAfterArgs reversedValues,
      fuel = callFuel + 1 ∧
      evalArgs model primSemantics callFuel args.reverse
          codeOverride state =
        .ok (stateAfterArgs, reversedValues) ∧
      primSemantics.eval callFuel stateAfterArgs prim
          reversedValues.reverse =
        .ok (final, values) := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
  | succ callFuel =>
      cases hArgs :
          evalArgs model primSemantics callFuel args.reverse
            codeOverride state with
      | error failure =>
          simp [evalValues, hArgs] at hRun
      | ok result =>
          rcases result with ⟨stateAfterArgs, reversedValues⟩
          exact
            ⟨callFuel, stateAfterArgs, reversedValues, by omega,
              hArgs, by simpa [evalValues, hArgs] using hRun⟩

theorem evalValues_function_ok_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hRun :
      evalValues model primSemantics fuel
          (.Call (.inr functionName) args) codeOverride state =
        .ok (final, values)) :
    ∃ callFuel stateAfterArgs reversedValues,
      fuel = callFuel + 1 ∧
      evalArgs model primSemantics callFuel args.reverse
          codeOverride state =
        .ok (stateAfterArgs, reversedValues) ∧
      call model primSemantics callFuel reversedValues.reverse
          (some functionName) codeOverride stateAfterArgs =
        .ok (final, values) := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
  | succ callFuel =>
      cases hArgs :
          evalArgs model primSemantics callFuel args.reverse
            codeOverride state with
      | error failure =>
          simp [evalValues, hArgs] at hRun
      | ok result =>
          rcases result with ⟨stateAfterArgs, reversedValues⟩
          exact
            ⟨callFuel, stateAfterArgs, reversedValues, by omega,
              hArgs, by simpa [evalValues, hArgs] using hRun⟩

theorem call_succ_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {args : List Word}
    {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hRun :
      call model prim (fuel + 1) args (some functionName)
          codeOverride state =
        .ok (final, values)) :
    ∃ yulContract params returns body stateAfterBody,
      (model.source state).sharedState.accountMap.find?
          (model.source state).executionEnv.codeOwner =
        some yulContract ∧
      (codeOverride.getD yulContract.code).functions.lookup functionName =
        some (.Def params returns body) ∧
      exec model prim fuel (.Block body) codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall params returns args))) =
        .ok stateAfterBody ∧
      final =
        model.withSource stateAfterBody
          (((model.source stateAfterBody).reviveJump.overwrite?
              (model.source state)).setStore (model.source state)) ∧
      values = List.map (model.source stateAfterBody).lookup! returns := by
  unfold call at hRun
  cases hContract :
      (model.source state).sharedState.accountMap.find?
        (model.source state).executionEnv.codeOwner with
  | none =>
      simp [hContract, fail] at hRun
  | some yulContract =>
      cases hFunction :
          (codeOverride.getD yulContract.code).functions.lookup functionName with
      | none =>
          simp [hContract, hFunction, fail] at hRun
      | some fn =>
          cases fn with
          | Def params returns body =>
              cases hBody :
                  exec model prim fuel (.Block body) codeOverride
                    (model.withSource state
                      (EvmYul.Yul.State.mkOk
                        ((model.source state).initcall
                          params returns args))) with
              | error failure =>
                  simp [hContract, hFunction, hBody] at hRun
              | ok stateAfterBody =>
                  simp [hContract, hFunction, hBody] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  exact
                    ⟨yulContract, params, returns, body, stateAfterBody,
                      rfl, hFunction, hBody, rfl, rfl⟩

theorem evalValues_function_ok_length
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {contract : EvmYul.Yul.Ast.YulContract}
    {params returns : List EvmYul.Identifier}
    {body : List EvmYul.Yul.Ast.Stmt}
    {state final : σ} {values : List Word}
    (hLookup :
      contract.functions.lookup functionName =
        some (.Def params returns body))
    (hRun :
      evalValues model prim fuel (.Call (.inr functionName) args)
          (some contract) state =
        .ok (final, values)) :
    values.length = returns.length := by
  obtain
      ⟨callFuel, stateAfterArgs, reversedValues,
        _hFuel, _hArgs, hCall⟩ :=
    evalValues_function_ok_parts model prim hRun
  cases callFuel with
  | zero =>
      simp [call, fail] at hCall
  | succ bodyFuel =>
      obtain
          ⟨_accountContract, callParams, callReturns, callBody,
            _stateAfterBody, _hAccount, hFunction, _hBody,
            _hFinal, hValues⟩ :=
        call_succ_ok_parts model prim hCall
      simp at hFunction
      rw [hLookup] at hFunction
      cases hFunction
      simpa using congrArg List.length hValues

theorem eval_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {value : Word}
    (hRun :
      eval model prim fuel expr codeOverride state =
        .ok (final, value)) :
    ∃ values,
      evalValues model prim fuel expr codeOverride state =
        .ok (final, values) ∧
      value = values.head! := by
  unfold eval at hRun
  cases hValues :
      evalValues model prim fuel expr codeOverride state with
  | error failure =>
      simp [hValues] at hRun
  | ok result =>
      rcases result with ⟨stateAfterEval, values⟩
      simp [hValues] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      exact ⟨values, rfl, rfl⟩

theorem eval_function_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {value : Word}
    (hRun :
      eval model prim fuel (.Call (.inr functionName) args)
          codeOverride state =
        .ok (final, value)) :
    ∃ callFuel stateAfterArgs reversedValues returnValues,
      fuel = callFuel + 1 ∧
      evalArgs model prim callFuel args.reverse codeOverride state =
        .ok (stateAfterArgs, reversedValues) ∧
      call model prim callFuel reversedValues.reverse
          (some functionName) codeOverride stateAfterArgs =
        .ok (final, returnValues) ∧
      value = returnValues.head! := by
  unfold eval at hRun
  cases hValues :
      evalValues model prim fuel (.Call (.inr functionName) args)
        codeOverride state with
  | error failure =>
      simp [hValues] at hRun
  | ok result =>
      rcases result with ⟨stateAfterCall, returnValues⟩
      simp [hValues] at hRun
      rcases hRun with ⟨rfl, rfl⟩
      cases fuel with
      | zero =>
          simp [evalValues, fail] at hValues
      | succ callFuel =>
          cases hArgs :
              evalArgs model prim callFuel args.reverse codeOverride state with
          | error failure =>
              simp [evalValues, hArgs] at hValues
          | ok result =>
              rcases result with ⟨stateAfterArgs, reversedValues⟩
              cases hCall :
                  call model prim callFuel reversedValues.reverse
                    (some functionName) codeOverride stateAfterArgs with
              | error failure =>
                  simp [evalValues, hArgs, hCall] at hValues
              | ok result =>
                  rcases result with ⟨final, values⟩
                  simp [evalValues, hArgs, hCall] at hValues
                  rcases hValues with ⟨rfl, rfl⟩
                  exact
                    ⟨callFuel, stateAfterArgs, reversedValues,
                      values, rfl, hArgs, hCall, rfl⟩

theorem evalArgs_ok_length {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ) :
    ∀ {fuel : Nat} {args : List EvmYul.Yul.Ast.Expr}
      {codeOverride : Option EvmYul.Yul.Ast.YulContract}
      {state final : σ} {values : List Word},
      evalArgs model prim fuel args codeOverride state =
          .ok (final, values) →
        values.length = args.length
  | fuel, [], codeOverride, state, final, values, hRun => by
      cases fuel with
      | zero =>
          simp [evalArgs, fail] at hRun
      | succ previous =>
          simp [evalArgs] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          rfl
  | fuel, head :: rest, codeOverride, state, final, values, hRun => by
      cases fuel with
      | zero =>
          simp [evalArgs, fail] at hRun
      | succ previous =>
          cases hHead :
              eval model prim previous head codeOverride state with
          | error failure =>
              simp [evalArgs, evalTail, hHead] at hRun
          | ok headResult =>
              rcases headResult with ⟨stateAfterHead, headValue⟩
              cases previous with
              | zero =>
                  simp [evalArgs, evalTail, hHead, fail] at hRun
              | succ tailFuel =>
                  cases hTail :
                      evalArgs model prim tailFuel rest codeOverride
                        stateAfterHead with
                  | error failure =>
                      simp [evalArgs, evalTail, hHead, hTail] at hRun
                  | ok tailResult =>
                      rcases tailResult with ⟨stateAfterTail, tailValues⟩
                      simp [evalArgs, evalTail, hHead, hTail] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      have hLength :=
                        evalArgs_ok_length model prim hTail
                      simp [hLength]

theorem exec_block_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel (.Block body) codeOverride state =
        .ok final) :
    ∃ previous stateAfterBody,
      fuel = previous + 1 ∧
      execSeq model prim previous body codeOverride state =
        .ok stateAfterBody ∧
      final =
        model.withSource stateAfterBody
          ((model.source stateAfterBody).restrictStoreTo
            (model.source state).store) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      cases hBody :
          execSeq model prim previous body codeOverride state with
      | error failure =>
          simp [exec, hBody] at hRun
      | ok stateAfterBody =>
          simp [exec, hBody] at hRun
          subst final
          exact ⟨previous, stateAfterBody, rfl, hBody, rfl⟩

theorem exec_leave_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel .Leave codeOverride state =
        .ok final) :
    ∃ previous,
      fuel = previous + 1 ∧
      final =
        model.withSource state
          (EvmYul.Yul.State.setLeave (model.source state)) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      simp [exec] at hRun
      subst final
      exact ⟨previous, rfl, rfl⟩

theorem exec_continue_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel .Continue codeOverride state =
        .ok final) :
    ∃ previous,
      fuel = previous + 1 ∧
      final =
        model.withSource state
          (EvmYul.Yul.State.setContinue (model.source state)) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      simp [exec] at hRun
      subst final
      exact ⟨previous, rfl, rfl⟩

theorem exec_break_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel .Break codeOverride state =
        .ok final) :
    ∃ previous,
      fuel = previous + 1 ∧
      final =
        model.withSource state
          (EvmYul.Yul.State.setBreak (model.source state)) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      simp [exec] at hRun
      subst final
      exact ⟨previous, rfl, rfl⟩

theorem exec_let_none_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {names : List EvmYul.Identifier}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel (.Let names none) codeOverride state =
        .ok final) :
    ∃ previous,
      fuel = previous + 1 ∧
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok () ∧
      final =
        model.withSource state ((model.source state).zeroFill names) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      cases hCheck :
          EvmYul.Yul.checkDeclaration (model.source state) names with
      | error err =>
          simp [exec, hCheck, fail] at hRun
      | ok unit =>
          cases unit
          simp [exec, hCheck] at hRun
          subst final
          exact ⟨previous, rfl, by simpa using hCheck, rfl⟩

theorem eval_of_evalValues_singleton
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {value : Word}
    (hRun :
      evalValues model prim fuel expr codeOverride state =
        .ok (final, [value])) :
    eval model prim fuel expr codeOverride state =
      .ok (final, value) := by
  simp [eval, hRun]

theorem exec_let_some_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {names : List EvmYul.Identifier}
    {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel (.Let names (some expr))
          codeOverride state =
        .ok final) :
    ∃ previous stateAfterValue values,
      fuel = previous + 1 ∧
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok () ∧
      evalValues model prim previous expr codeOverride state =
        .ok (stateAfterValue, values) ∧
      final = model.multifill names stateAfterValue values := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      cases hCheck :
          EvmYul.Yul.checkDeclaration (model.source state) names with
      | error err =>
          simp [exec, hCheck, fail] at hRun
      | ok unit =>
          cases unit
          cases hValues :
              evalValues model prim previous expr codeOverride state with
          | error failure =>
              simp [exec, hCheck, multifill, hValues] at hRun
          | ok result =>
              rcases result with ⟨stateAfterValue, values⟩
              simp [exec, hCheck, multifill, hValues] at hRun
              subst final
              exact
                ⟨previous, stateAfterValue, values, rfl,
                  by simpa using hCheck, hValues, rfl⟩

theorem exec_assign_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {names : List EvmYul.Identifier}
    {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel (.Assign names expr)
          codeOverride state =
        .ok final) :
    ∃ previous stateAfterValue values,
      fuel = previous + 1 ∧
      EvmYul.Yul.checkAssignment (model.source state) names = .ok () ∧
      evalValues model prim previous expr codeOverride state =
        .ok (stateAfterValue, values) ∧
      final = model.multifill names stateAfterValue values := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      cases hCheck :
          EvmYul.Yul.checkAssignment (model.source state) names with
      | error err =>
          simp [exec, hCheck, fail] at hRun
      | ok unit =>
          cases unit
          cases hValues :
              evalValues model prim previous expr codeOverride state with
          | error failure =>
              simp [exec, hCheck, multifill, hValues] at hRun
          | ok result =>
              rcases result with ⟨stateAfterValue, values⟩
              simp [exec, hCheck, multifill, hValues] at hRun
              subst final
              exact
                ⟨previous, stateAfterValue, values, rfl,
                  by simpa using hCheck, hValues, rfl⟩

theorem execSeq_nil_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      execSeq model prim fuel [] codeOverride state =
        .ok final) :
    ∃ previous, fuel = previous + 1 ∧ final = state := by
  cases fuel with
  | zero =>
      simp [execSeq, fail] at hRun
  | succ previous =>
      simp [execSeq] at hRun
      subst final
      exact ⟨previous, rfl, rfl⟩

theorem execSeq_cons_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {stmt : EvmYul.Yul.Ast.Stmt}
    {rest : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      execSeq model prim fuel (stmt :: rest) codeOverride state =
        .ok final) :
    ∃ previous stateAfterStmt,
      fuel = previous + 1 ∧
      exec model prim previous stmt codeOverride state =
        .ok stateAfterStmt ∧
      match model.source stateAfterStmt with
      | .Ok _ _ =>
          execSeq model prim previous rest codeOverride stateAfterStmt =
            .ok final
      | .OutOfFuel | .Checkpoint _ =>
          final = stateAfterStmt := by
  cases fuel with
  | zero =>
      simp [execSeq, fail] at hRun
  | succ previous =>
      cases hStmt :
          exec model prim previous stmt codeOverride state with
      | error failure =>
          simp [execSeq, hStmt] at hRun
      | ok stateAfterStmt =>
          cases hSource : model.source stateAfterStmt with
          | Ok shared vars =>
              cases hRest :
                  execSeq model prim previous rest codeOverride
                    stateAfterStmt with
              | error failure =>
                  simp [execSeq, hStmt, hSource, hRest] at hRun
              | ok stateAfterRest =>
                  simp [execSeq, hStmt, hSource, hRest] at hRun
                  subst final
                  exact
                    ⟨previous, stateAfterStmt, rfl, hStmt,
                      by simpa [hSource] using hRest⟩
          | OutOfFuel =>
              simp [execSeq, hStmt, hSource] at hRun
              subst final
              exact
                ⟨previous, stateAfterStmt, rfl, hStmt,
                  by simp [hSource]⟩
          | Checkpoint jump =>
              simp [execSeq, hStmt, hSource] at hRun
              subst final
              exact
                ⟨previous, stateAfterStmt, rfl, hStmt,
                  by simp [hSource]⟩

theorem evalArgs_append_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ) :
    ∀ {fuel : Nat} {left right : List EvmYul.Yul.Ast.Expr}
      {codeOverride : Option EvmYul.Yul.Ast.YulContract}
      {source final : σ} {values : List Word},
      evalArgs model prim fuel (left ++ right) codeOverride source =
          .ok (final, values) →
      ∃ middle leftValues rightValues remainingFuel,
        fuel = remainingFuel + 2 * left.length ∧
        evalArgs model prim fuel left codeOverride source =
          .ok (middle, leftValues) ∧
        evalArgs model prim remainingFuel right codeOverride middle =
          .ok (final, rightValues) ∧
        values = leftValues ++ rightValues
  | fuel, [], right, codeOverride, source, final, values, hRun => by
      cases fuel with
      | zero =>
          simp [evalArgs, fail] at hRun
      | succ previous =>
          refine
            ⟨source, [], values, previous.succ, by simp, ?_, hRun, by simp⟩
          simp [evalArgs]
  | fuel, head :: tail, right, codeOverride, source, final, values, hRun => by
      cases fuel with
      | zero =>
          simp [evalArgs, fail] at hRun
      | succ previous =>
          cases hHead :
              eval model prim previous head codeOverride source with
          | error failure =>
              simp [evalArgs, hHead, evalTail] at hRun
          | ok headResult =>
              rcases headResult with ⟨afterHead, headValue⟩
              cases previous with
              | zero =>
                  simp [evalArgs, hHead, evalTail, fail] at hRun
              | succ tailFuel =>
                  cases hTailRun :
                      evalArgs model prim tailFuel (tail ++ right)
                        codeOverride afterHead with
                  | error failure =>
                      simp [evalArgs, hHead, evalTail, hTailRun] at hRun
                  | ok tailResult =>
                      rcases tailResult with ⟨tailFinal, tailResultValues⟩
                      simp [evalArgs, hHead, evalTail, hTailRun] at hRun
                      rcases hRun with ⟨rfl, rfl⟩
                      obtain
                          ⟨middle, tailValues, rightValues, remainingFuel,
                            hFuel, hTail, hRight, hValues⟩ :=
                        evalArgs_append_ok_parts model prim hTailRun
                      refine
                        ⟨middle, headValue :: tailValues, rightValues,
                          remainingFuel, ?_, ?_, hRight, ?_⟩
                      · simp only [List.length_cons]
                        omega
                      · simp [evalArgs, hHead, evalTail, hTail]
                      · simp [hValues]

theorem evalArgs_singleton_ok_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {fuel : Nat} {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source final : σ} {values : List Word}
    (hRun :
      evalArgs model prim fuel [expr] codeOverride source =
        .ok (final, values)) :
    ∃ evalFuel value,
      fuel = evalFuel + 1 ∧
      eval model prim evalFuel expr codeOverride source =
        .ok (final, value) ∧
      values = [value] := by
  cases fuel with
  | zero =>
      simp [evalArgs, fail] at hRun
  | succ evalFuel =>
      cases hEval :
          eval model prim evalFuel expr codeOverride source with
      | error failure =>
          simp [evalArgs, hEval, evalTail] at hRun
      | ok result =>
          rcases result with ⟨afterExpr, value⟩
          cases evalFuel with
          | zero =>
              simp [evalArgs, hEval, evalTail, fail] at hRun
          | succ remainingFuel =>
              cases remainingFuel with
              | zero =>
                  simp [evalArgs, hEval, evalTail, fail] at hRun
              | succ emptyFuel =>
                  simp [evalArgs, hEval, evalTail] at hRun
                  rcases hRun with ⟨rfl, rfl⟩
                  exact
                    ⟨emptyFuel.succ.succ, value, by omega, hEval, rfl⟩

end Effectful
end Source
end Yul
end EvmCompiler
