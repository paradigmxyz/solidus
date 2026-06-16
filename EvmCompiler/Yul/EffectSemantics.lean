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

theorem call_succ_of_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {args : List Word}
    {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterBody : σ}
    {yulContract : EvmYul.Account .Yul}
    {params returns : List EvmYul.Identifier}
    {body : List EvmYul.Yul.Ast.Stmt}
    (hContract :
      (model.source state).sharedState.accountMap.find?
          (model.source state).executionEnv.codeOwner =
        some yulContract)
    (hFunction :
      (codeOverride.getD yulContract.code).functions.lookup functionName =
        some (.Def params returns body))
    (hBody :
      exec model prim fuel (.Block body) codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall params returns args))) =
        .ok stateAfterBody) :
    call model prim (fuel + 1) args (some functionName)
        codeOverride state =
      .ok
        (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source state)).setStore (model.source state)),
          List.map (model.source stateAfterBody).lookup! returns) := by
  simp [call, hContract, hFunction, hBody]

theorem call_succ_error_of_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {args : List Word}
    {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    {yulContract : EvmYul.Account .Yul}
    {params returns : List EvmYul.Identifier}
    {body : List EvmYul.Yul.Ast.Stmt}
    (hContract :
      (model.source state).sharedState.accountMap.find?
          (model.source state).executionEnv.codeOwner =
        some yulContract)
    (hFunction :
      (codeOverride.getD yulContract.code).functions.lookup functionName =
        some (.Def params returns body))
    (hBody :
      exec model prim fuel (.Block body) codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall params returns args))) =
        .error failure) :
    call model prim (fuel + 1) args (some functionName)
        codeOverride state =
      .error failure := by
  simp [call, hContract, hFunction, hBody]

theorem callDispatcher_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hRun :
      callDispatcher model prim fuel codeOverride state =
        .ok (final, values)) :
    ∃ previous stateAfterBody,
      fuel = previous + 1 ∧
      exec model prim previous
          (.Block [(model.source state).executionEnv.code.dispatcher])
          codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall [] [] []))) =
        .ok stateAfterBody ∧
      final =
        model.withSource stateAfterBody
          (((model.source stateAfterBody).reviveJump.overwrite?
              (model.source state)).setStore (model.source state)) ∧
      values = [] := by
  cases fuel with
  | zero =>
      simp [callDispatcher, fail] at hRun
  | succ previous =>
      cases hBody :
          exec model prim previous
            (.Block [(model.source state).executionEnv.code.dispatcher])
            codeOverride
            (model.withSource state
              (EvmYul.Yul.State.mkOk
                ((model.source state).initcall [] [] []))) with
      | error failure =>
          simp [callDispatcher, hBody] at hRun
      | ok stateAfterBody =>
          simp [callDispatcher, hBody] at hRun
          rcases hRun with ⟨rfl, rfl⟩
          exact ⟨previous, stateAfterBody, rfl, hBody, rfl, rfl⟩

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

theorem eval_function_of_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {callFuel : Nat}
    {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterArgs final : σ}
    {reversedValues returnValues : List Word}
    (hArgs :
      evalArgs model prim callFuel args.reverse codeOverride state =
        .ok (stateAfterArgs, reversedValues))
    (hCall :
      call model prim callFuel reversedValues.reverse
          (some functionName) codeOverride stateAfterArgs =
        .ok (final, returnValues)) :
    eval model prim (callFuel + 1) (.Call (.inr functionName) args)
        codeOverride state =
      .ok (final, returnValues.head!) := by
  simp [eval, evalValues, hArgs, hCall]

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

theorem exec_if_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel (.If cond body) codeOverride state =
        .ok final) :
    ∃ previous stateAfterCond condValue,
      fuel = previous + 1 ∧
      eval model prim previous cond codeOverride state =
        .ok (stateAfterCond, condValue) ∧
      ((condValue ≠ EvmYul.UInt256.ofNat 0 ∧
          exec model prim previous (.Block body) codeOverride
              stateAfterCond =
            .ok final) ∨
        (condValue = EvmYul.UInt256.ofNat 0 ∧
          final = stateAfterCond)) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      cases hCond :
          eval model prim previous cond codeOverride state with
      | error failure =>
          simp [exec, hCond] at hRun
      | ok condResult =>
          rcases condResult with ⟨stateAfterCond, condValue⟩
          simp only [exec, hCond] at hRun
          split at hRun
          · rename_i hTrue
            exact
              ⟨previous, stateAfterCond, condValue, rfl, hCond,
                Or.inl ⟨hTrue, hRun⟩⟩
          · rename_i hFalse
            have hZero : condValue = EvmYul.UInt256.ofNat 0 :=
              Classical.not_not.mp hFalse
            exact
              ⟨previous, stateAfterCond, condValue, rfl, hCond,
                Or.inr ⟨hZero, (Except.ok.inj hRun).symm⟩⟩

theorem exec_if_false_of_eval
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterCond : σ} {condValue : Word}
    (hEval :
      eval model prim fuel cond codeOverride state =
        .ok (stateAfterCond, condValue))
    (hZero : condValue = EvmYul.UInt256.ofNat 0) :
    exec model prim (fuel + 1) (.If cond body) codeOverride state =
      .ok stateAfterCond := by
  have hZero' : condValue = (⟨0⟩ : Word) := by
    simpa [EvmYul.UInt256.ofNat] using hZero
  simp [exec, hEval, hZero']

theorem exec_if_true_of_eval
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterCond final : σ} {condValue : Word}
    (hEval :
      eval model prim fuel cond codeOverride state =
        .ok (stateAfterCond, condValue))
    (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
    (hBody :
      exec model prim fuel (.Block body) codeOverride stateAfterCond =
        .ok final) :
    exec model prim (fuel + 1) (.If cond body) codeOverride state =
      .ok final := by
  have hNonzero' : condValue ≠ (⟨0⟩ : Word) := by
    simpa [EvmYul.UInt256.ofNat] using hNonzero
  simp [exec, hEval, hNonzero', hBody]

theorem exec_switch_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {scrutinee : EvmYul.Yul.Ast.Expr}
    {cases : List (Word × List EvmYul.Yul.Ast.Stmt)}
    {defaultBody : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel (.Switch scrutinee cases defaultBody)
          codeOverride state =
        .ok final) :
    ∃ previous stateAfterScrutinee value,
      fuel = previous + 1 ∧
      eval model prim previous scrutinee codeOverride state =
        .ok (stateAfterScrutinee, value) ∧
      exec model prim previous
          (.Block
            (EvmYul.Yul.selectSwitchCase value defaultBody cases))
          codeOverride stateAfterScrutinee =
        .ok final := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      cases hScrutinee :
          eval model prim previous scrutinee codeOverride state with
      | error failure =>
          simp [exec, hScrutinee] at hRun
      | ok result =>
          rcases result with ⟨stateAfterScrutinee, value⟩
          simp [exec, hScrutinee] at hRun
          exact
            ⟨previous, stateAfterScrutinee, value,
              rfl, hScrutinee, hRun⟩

theorem exec_switch_of_eval
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {scrutinee : EvmYul.Yul.Ast.Expr}
    {cases : List (Word × List EvmYul.Yul.Ast.Stmt)}
    {defaultBody : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterScrutinee final : σ} {value : Word}
    (hEval :
      eval model prim fuel scrutinee codeOverride state =
        .ok (stateAfterScrutinee, value))
    (hBody :
      exec model prim fuel
          (.Block
            (EvmYul.Yul.selectSwitchCase value defaultBody cases))
          codeOverride stateAfterScrutinee =
        .ok final) :
    exec model prim (fuel + 1)
        (.Switch scrutinee cases defaultBody) codeOverride state =
      .ok final := by
  simp [exec, hEval, hBody]

theorem exec_for_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {post body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model prim fuel (.For cond post body) codeOverride state =
        .ok final) :
    ∃ previous,
      fuel = previous + 1 ∧
      loop model prim previous cond post body codeOverride state =
        .ok final := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      exact ⟨previous, rfl, by simpa [exec] using hRun⟩

def LoopBodyContinues : EvmYul.Yul.State → Prop
  | .Ok _ _ => True
  | .Checkpoint (.Continue _ _) => True
  | _ => False

def LoopPostRecurs : EvmYul.Yul.State → Prop
  | .OutOfFuel => False
  | .Checkpoint (.Leave _ _) => False
  | _ => True

inductive LoopAfterCondCase
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ) (fuel : Nat)
    (cond : EvmYul.Yul.Ast.Expr)
    (post body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (outer : EvmYul.Yul.State)
    (afterCond : σ) (condValue : Word) (final : σ) : Prop where
  | false
      (hZero : condValue = EvmYul.UInt256.ofNat 0)
      (hFinal :
        final =
          model.withSource afterCond
            ((model.source afterCond).overwrite? outer)) :
      LoopAfterCondCase model prim fuel cond post body codeOverride
        outer afterCond condValue final
  | bodyOutOfFuel
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      {afterBody : σ}
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .ok afterBody)
      (hBodySource : model.source afterBody = .OutOfFuel)
      (hFinal :
        final =
          model.withSource afterBody
            ((model.source afterBody).overwrite? outer)) :
      LoopAfterCondCase model prim fuel cond post body codeOverride
        outer afterCond condValue final
  | bodyBreak
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      {afterBody : σ} {shared : EvmYul.SharedState .Yul}
      {store : EvmYul.Yul.VarStore}
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .ok afterBody)
      (hBodySource :
        model.source afterBody = .Checkpoint (.Break shared store))
      (hFinal :
        final =
          model.withSource afterBody
            ((model.source afterBody).reviveJump.overwrite? outer)) :
      LoopAfterCondCase model prim fuel cond post body codeOverride
        outer afterCond condValue final
  | bodyLeave
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      {afterBody : σ} {shared : EvmYul.SharedState .Yul}
      {store : EvmYul.Yul.VarStore}
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .ok afterBody)
      (hBodySource :
        model.source afterBody = .Checkpoint (.Leave shared store))
      (hFinal :
        final =
          model.withSource afterBody
            ((model.source afterBody).overwrite? outer)) :
      LoopAfterCondCase model prim fuel cond post body codeOverride
        outer afterCond condValue final
  | postOutOfFuel
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      {afterBody afterPost : σ}
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .ok afterBody)
      (hBodyContinues : LoopBodyContinues (model.source afterBody))
      (hPost :
        exec model prim fuel (.Block post) codeOverride
            (model.withSource afterBody
              (model.source afterBody).reviveJump) =
          .ok afterPost)
      (hPostSource : model.source afterPost = .OutOfFuel)
      (hFinal :
        final =
          model.withSource afterPost
            ((model.source afterPost).overwrite? outer)) :
      LoopAfterCondCase model prim fuel cond post body codeOverride
        outer afterCond condValue final
  | postLeave
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      {afterBody afterPost : σ}
      {shared : EvmYul.SharedState .Yul}
      {store : EvmYul.Yul.VarStore}
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .ok afterBody)
      (hBodyContinues : LoopBodyContinues (model.source afterBody))
      (hPost :
        exec model prim fuel (.Block post) codeOverride
            (model.withSource afterBody
              (model.source afterBody).reviveJump) =
          .ok afterPost)
      (hPostSource :
        model.source afterPost = .Checkpoint (.Leave shared store))
      (hFinal :
        final =
          model.withSource afterPost
            ((model.source afterPost).overwrite? outer)) :
      LoopAfterCondCase model prim fuel cond post body codeOverride
        outer afterCond condValue final
  | recurse
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      {afterBody afterPost afterLoop : σ}
      (hBody :
        exec model prim fuel (.Block body) codeOverride afterCond =
          .ok afterBody)
      (hBodyContinues : LoopBodyContinues (model.source afterBody))
      (hPost :
        exec model prim fuel (.Block post) codeOverride
            (model.withSource afterBody
              (model.source afterBody).reviveJump) =
          .ok afterPost)
      (hPostRecurs : LoopPostRecurs (model.source afterPost))
      (hLoop :
        exec model prim fuel (.For cond post body) codeOverride
            (model.withSource afterPost
              ((model.source afterPost).overwrite? outer)) =
          .ok afterLoop)
      (hFinal :
        final =
          model.withSource afterLoop
            ((model.source afterLoop).overwrite? outer)) :
      LoopAfterCondCase model prim fuel cond post body codeOverride
        outer afterCond condValue final

theorem loop_ok_parts
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {cond : EvmYul.Yul.Ast.Expr}
    {post body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      loop model prim fuel cond post body codeOverride state =
        .ok final) :
    ∃ previous afterCond condValue,
      fuel = previous + 2 ∧
      eval model prim previous cond codeOverride
          (model.withSource state
            (EvmYul.Yul.State.mkOk (model.source state))) =
        .ok (afterCond, condValue) ∧
      LoopAfterCondCase model prim previous cond post body codeOverride
        (model.source state) afterCond condValue final := by
  cases fuel with
  | zero =>
      simp [loop, fail] at hRun
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [loop, fail] at hRun
      | succ previous =>
          cases hCond :
              eval model prim previous cond codeOverride
                (model.withSource state
                  (EvmYul.Yul.State.mkOk (model.source state))) with
          | error failure =>
              simp [loop, hCond] at hRun
          | ok condResult =>
              rcases condResult with ⟨afterCond, condValue⟩
              simp only [loop, hCond] at hRun
              by_cases hZero :
                  condValue = EvmYul.UInt256.ofNat 0
              · have hZeroLit : condValue = ⟨0⟩ := by
                  simpa using hZero
                rw [if_pos hZeroLit] at hRun
                exact
                  ⟨previous, afterCond, condValue, by omega, hCond,
                    .false hZero (Except.ok.inj hRun).symm⟩
              · have hNonzeroLit : condValue ≠ ⟨0⟩ := by
                  simpa using hZero
                rw [if_neg hNonzeroLit] at hRun
                cases hBody :
                    exec model prim previous (.Block body) codeOverride
                      afterCond with
                | error failure =>
                    simp [loop, hCond, hZero, hBody] at hRun
                | ok afterBody =>
                    rw [hBody] at hRun
                    simp only at hRun
                    cases hBodySource : model.source afterBody with
                    | OutOfFuel =>
                        simp [loop, hCond, hZero, hBody, hBodySource] at hRun
                        exact
                          ⟨previous, afterCond, condValue, by omega, hCond,
                            .bodyOutOfFuel hZero hBody hBodySource
                              (by simpa [hBodySource] using hRun.symm)⟩
                    | Checkpoint jump =>
                        cases jump with
                        | Break shared store =>
                            simp [loop, hCond, hZero, hBody, hBodySource]
                              at hRun
                            exact
                              ⟨previous, afterCond, condValue, by omega,
                                hCond,
                                .bodyBreak hZero hBody hBodySource
                                  (by simpa [hBodySource] using hRun.symm)⟩
                        | Leave shared store =>
                            simp [loop, hCond, hZero, hBody, hBodySource]
                              at hRun
                            exact
                              ⟨previous, afterCond, condValue, by omega,
                                hCond,
                                .bodyLeave hZero hBody hBodySource
                                  (by simpa [hBodySource] using hRun.symm)⟩
                        | Continue shared store =>
                            rw [hBodySource] at hRun
                            simp only at hRun
                            cases hPost :
                                exec model prim previous (.Block post)
                                  codeOverride
                                  (model.withSource afterBody
                                    (model.source afterBody).reviveJump) with
                            | error failure =>
                                have hPost' :
                                    exec model prim previous (.Block post)
                                        codeOverride
                                        (model.withSource afterBody
                                          (EvmYul.Yul.State.Checkpoint
                                            (.Continue shared store)).reviveJump) =
                                      .error failure := by
                                  simpa [hBodySource] using hPost
                                rw [hPost'] at hRun
                                contradiction
                            | ok afterPost =>
                                have hPost' :
                                    exec model prim previous (.Block post)
                                        codeOverride
                                        (model.withSource afterBody
                                          (EvmYul.Yul.State.Checkpoint
                                            (.Continue shared store)).reviveJump) =
                                      .ok afterPost := by
                                  simpa [hBodySource] using hPost
                                rw [hPost'] at hRun
                                simp only at hRun
                                cases hPostSource :
                                    model.source afterPost with
                                | OutOfFuel =>
                                    simp [loop, hCond, hZero, hBody,
                                      hBodySource, hPost, hPostSource] at hRun
                                    exact
                                      ⟨previous, afterCond, condValue,
                                        by omega, hCond,
                                        .postOutOfFuel hZero hBody
                                          (by simp [LoopBodyContinues,
                                            hBodySource])
                                          hPost hPostSource
                                          (by
                                            simpa [hPostSource] using
                                              hRun.symm)⟩
                                | Checkpoint postJump =>
                                    cases postJump with
                                    | Leave postShared postStore =>
                                        simp [loop, hCond, hZero, hBody,
                                          hBodySource, hPost, hPostSource]
                                          at hRun
                                        exact
                                          ⟨previous, afterCond, condValue,
                                            by omega, hCond,
                                            .postLeave hZero hBody
                                              (by simp [LoopBodyContinues,
                                                hBodySource])
                                              hPost hPostSource
                                              (by
                                                simpa [hPostSource] using
                                                  hRun.symm)⟩
                                    | Continue postShared postStore =>
                                        rw [hPostSource] at hRun
                                        simp only at hRun
                                        cases hLoop :
                                            exec model prim previous
                                              (.For cond post body)
                                              codeOverride
                                              (model.withSource afterPost
                                                ((model.source afterPost).overwrite?
                                                  (model.source state))) with
                                        | error failure =>
                                            have hLoop' := hLoop
                                            simp only [hPostSource] at hLoop'
                                            rw [hLoop'] at hRun
                                            contradiction
                                        | ok afterLoop =>
                                            have hLoop' := hLoop
                                            simp only [hPostSource] at hLoop'
                                            rw [hLoop'] at hRun
                                            simp only at hRun
                                            exact
                                              ⟨previous, afterCond, condValue,
                                                by omega, hCond,
                                                .recurse hZero hBody
                                                  (by simp [LoopBodyContinues,
                                                    hBodySource])
                                                  hPost
                                                  (by simp [LoopPostRecurs,
                                                    hPostSource])
                                                  hLoop
                                                  (Except.ok.inj hRun).symm⟩
                                    | Break postShared postStore =>
                                        rw [hPostSource] at hRun
                                        simp only at hRun
                                        cases hLoop :
                                            exec model prim previous
                                              (.For cond post body)
                                              codeOverride
                                              (model.withSource afterPost
                                                ((model.source afterPost).overwrite?
                                                  (model.source state))) with
                                        | error failure =>
                                            have hLoop' := hLoop
                                            simp only [hPostSource] at hLoop'
                                            rw [hLoop'] at hRun
                                            contradiction
                                        | ok afterLoop =>
                                            have hLoop' := hLoop
                                            simp only [hPostSource] at hLoop'
                                            rw [hLoop'] at hRun
                                            simp only at hRun
                                            exact
                                              ⟨previous, afterCond, condValue,
                                                by omega, hCond,
                                                .recurse hZero hBody
                                                  (by simp [LoopBodyContinues,
                                                    hBodySource])
                                                  hPost
                                                  (by simp [LoopPostRecurs,
                                                    hPostSource])
                                                  hLoop
                                                  (Except.ok.inj hRun).symm⟩
                                | Ok postShared postStore =>
                                    rw [hPostSource] at hRun
                                    simp only at hRun
                                    cases hLoop :
                                        exec model prim previous
                                          (.For cond post body) codeOverride
                                          (model.withSource afterPost
                                            ((model.source afterPost).overwrite?
                                              (model.source state))) with
                                    | error failure =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        contradiction
                                    | ok afterLoop =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        simp only at hRun
                                        exact
                                          ⟨previous, afterCond, condValue,
                                            by omega, hCond,
                                            .recurse hZero hBody
                                              (by simp [LoopBodyContinues,
                                                hBodySource])
                                              hPost
                                              (by simp [LoopPostRecurs,
                                                hPostSource])
                                              hLoop
                                              (Except.ok.inj hRun).symm⟩
                    | Ok shared store =>
                        rw [hBodySource] at hRun
                        simp only at hRun
                        cases hPost :
                            exec model prim previous (.Block post)
                              codeOverride
                              (model.withSource afterBody
                                (model.source afterBody).reviveJump) with
                        | error failure =>
                            have hPost' :
                                exec model prim previous (.Block post)
                                    codeOverride
                                    (model.withSource afterBody
                                      (EvmYul.Yul.State.Ok
                                        shared store).reviveJump) =
                                  .error failure := by
                              simpa [hBodySource] using hPost
                            rw [hPost'] at hRun
                            contradiction
                        | ok afterPost =>
                            have hPost' :
                                exec model prim previous (.Block post)
                                    codeOverride
                                    (model.withSource afterBody
                                      (EvmYul.Yul.State.Ok
                                        shared store).reviveJump) =
                                  .ok afterPost := by
                              simpa [hBodySource] using hPost
                            rw [hPost'] at hRun
                            simp only at hRun
                            cases hPostSource : model.source afterPost with
                            | OutOfFuel =>
                                simp [loop, hCond, hZero, hBody,
                                  hBodySource, hPost, hPostSource] at hRun
                                exact
                                  ⟨previous, afterCond, condValue, by omega,
                                    hCond,
                                    .postOutOfFuel hZero hBody
                                      (by simp [LoopBodyContinues,
                                        hBodySource])
                                      hPost hPostSource
                                      (by
                                        simpa [hPostSource] using
                                          hRun.symm)⟩
                            | Checkpoint postJump =>
                                cases postJump with
                                | Leave postShared postStore =>
                                    simp [loop, hCond, hZero, hBody,
                                      hBodySource, hPost, hPostSource] at hRun
                                    exact
                                      ⟨previous, afterCond, condValue,
                                        by omega, hCond,
                                        .postLeave hZero hBody
                                          (by simp [LoopBodyContinues,
                                            hBodySource])
                                          hPost hPostSource
                                          (by
                                            simpa [hPostSource] using
                                              hRun.symm)⟩
                                | Continue postShared postStore =>
                                    rw [hPostSource] at hRun
                                    simp only at hRun
                                    cases hLoop :
                                        exec model prim previous
                                          (.For cond post body) codeOverride
                                          (model.withSource afterPost
                                            ((model.source afterPost).overwrite?
                                              (model.source state))) with
                                    | error failure =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        contradiction
                                    | ok afterLoop =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        simp only at hRun
                                        exact
                                          ⟨previous, afterCond, condValue,
                                            by omega, hCond,
                                            .recurse hZero hBody
                                              (by simp [LoopBodyContinues,
                                                hBodySource])
                                              hPost
                                              (by simp [LoopPostRecurs,
                                                hPostSource])
                                              hLoop
                                              (Except.ok.inj hRun).symm⟩
                                | Break postShared postStore =>
                                    rw [hPostSource] at hRun
                                    simp only at hRun
                                    cases hLoop :
                                        exec model prim previous
                                          (.For cond post body) codeOverride
                                          (model.withSource afterPost
                                            ((model.source afterPost).overwrite?
                                              (model.source state))) with
                                    | error failure =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        contradiction
                                    | ok afterLoop =>
                                        have hLoop' := hLoop
                                        simp only [hPostSource] at hLoop'
                                        rw [hLoop'] at hRun
                                        simp only at hRun
                                        exact
                                          ⟨previous, afterCond, condValue,
                                            by omega, hCond,
                                            .recurse hZero hBody
                                              (by simp [LoopBodyContinues,
                                                hBodySource])
                                              hPost
                                              (by simp [LoopPostRecurs,
                                                hPostSource])
                                              hLoop
                                              (Except.ok.inj hRun).symm⟩
                            | Ok postShared postStore =>
                                rw [hPostSource] at hRun
                                simp only at hRun
                                cases hLoop :
                                    exec model prim previous
                                      (.For cond post body) codeOverride
                                      (model.withSource afterPost
                                        ((model.source afterPost).overwrite?
                                          (model.source state))) with
                                | error failure =>
                                    have hLoop' := hLoop
                                    simp only [hPostSource] at hLoop'
                                    rw [hLoop'] at hRun
                                    contradiction
                                | ok afterLoop =>
                                    have hLoop' := hLoop
                                    simp only [hPostSource] at hLoop'
                                    rw [hLoop'] at hRun
                                    simp only at hRun
                                    exact
                                      ⟨previous, afterCond, condValue,
                                        by omega, hCond,
                                        .recurse hZero hBody
                                          (by simp [LoopBodyContinues,
                                            hBodySource])
                                          hPost
                                          (by simp [LoopPostRecurs,
                                            hPostSource])
                                          hLoop
                                          (Except.ok.inj hRun).symm⟩

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

theorem exec_let_some_of_evalValues
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {names : List EvmYul.Identifier}
    {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterValue : σ} {values : List Word}
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
    (hRun :
      evalValues model prim fuel expr codeOverride state =
        .ok (stateAfterValue, values)) :
    exec model prim (fuel + 1) (.Let names (some expr))
        codeOverride state =
      .ok (model.multifill names stateAfterValue values) := by
  simp [exec, hCheck, hRun, multifill]

theorem exec_assign_of_evalValues
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {names : List EvmYul.Identifier}
    {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterValue : σ} {values : List Word}
    (hCheck :
      EvmYul.Yul.checkAssignment (model.source state) names = .ok ())
    (hRun :
      evalValues model prim fuel expr codeOverride state =
        .ok (stateAfterValue, values)) :
    exec model prim (fuel + 1) (.Assign names expr)
        codeOverride state =
      .ok (model.multifill names stateAfterValue values) := by
  simp [exec, hCheck, hRun, multifill]

theorem exec_expr_primitive_ok_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model primSemantics fuel
          (.ExprStmtCall (.Call (.inl prim) args))
          codeOverride state =
        .ok final) :
    ∃ previous stateAfterPrim values,
      fuel = previous + 1 ∧
      evalValues model primSemantics (previous + 1)
          (.Call (.inl prim) args) codeOverride state =
        .ok (stateAfterPrim, values) ∧
      final = model.multifill [] stateAfterPrim values := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ previous =>
      cases hArgs :
          evalArgs model primSemantics previous args.reverse
            codeOverride state with
      | error failure =>
          simp [exec, hArgs] at hRun
      | ok result =>
          rcases result with ⟨stateAfterArgs, reversedValues⟩
          cases hPrim :
              primSemantics.eval previous stateAfterArgs prim
                reversedValues.reverse with
          | error failure =>
              simp [exec, hArgs, hPrim, multifill] at hRun
          | ok result =>
              rcases result with ⟨stateAfterPrim, values⟩
              simp [exec, hArgs, hPrim, multifill] at hRun
              exact
                ⟨previous, stateAfterPrim, values, rfl,
                  by simp [evalValues, hArgs, hPrim], hRun.symm⟩

theorem exec_expr_primitive_of_evalValues
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ} {values : List Word}
    (hRun :
      evalValues model primSemantics fuel
          (.Call (.inl prim) args) codeOverride state =
        .ok (final, values)) :
    exec model primSemantics fuel
        (.ExprStmtCall (.Call (.inl prim) args))
        codeOverride state =
      .ok (model.multifill [] final values) := by
  cases fuel with
  | zero =>
      simp [evalValues, fail] at hRun
  | succ previous =>
      cases hArgs :
          evalArgs model primSemantics previous args.reverse
            codeOverride state with
      | error failure =>
          simp [evalValues, hArgs] at hRun
      | ok result =>
          rcases result with ⟨stateAfterArgs, reversedValues⟩
          cases hPrim :
              primSemantics.eval previous stateAfterArgs prim
                reversedValues.reverse with
          | error failure =>
              simp [evalValues, hArgs, hPrim] at hRun
          | ok result =>
              rcases result with ⟨stateAfterPrim, outputs⟩
              simp [evalValues, hArgs, hPrim] at hRun
              rcases hRun with ⟨rfl, rfl⟩
              simp [exec, hArgs, hPrim, multifill]

theorem exec_expr_function_of_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterArgs final : σ}
    {reversedValues values : List Word}
    (hArgs :
      evalArgs model primSemantics (fuel + 1) args.reverse
          codeOverride state =
        .ok (stateAfterArgs, reversedValues))
    (hCall :
      call model primSemantics fuel reversedValues.reverse
          (some functionName) codeOverride stateAfterArgs =
        .ok (final, values)) :
    exec model primSemantics (fuel + 2)
        (.ExprStmtCall (.Call (.inr functionName) args))
        codeOverride state =
      .ok (model.multifill [] final values) := by
  simp [exec, hArgs, hCall, multifill]

theorem evalValues_function_error_of_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterArgs : σ}
    {reversedValues : List Word} {failure : Failure σ}
    (hArgs :
      evalArgs model primSemantics fuel args.reverse
          codeOverride state =
        .ok (stateAfterArgs, reversedValues))
    (hCall :
      call model primSemantics fuel reversedValues.reverse
          (some functionName) codeOverride stateAfterArgs =
        .error failure) :
    evalValues model primSemantics (fuel + 1)
        (.Call (.inr functionName) args) codeOverride state =
      .error failure := by
  simp [evalValues, hArgs, hCall]

theorem exec_expr_function_error_of_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterArgs : σ}
    {reversedValues : List Word} {failure : Failure σ}
    (hArgs :
      evalArgs model primSemantics (fuel + 1) args.reverse
          codeOverride state =
        .ok (stateAfterArgs, reversedValues))
    (hCall :
      call model primSemantics fuel reversedValues.reverse
          (some functionName) codeOverride stateAfterArgs =
        .error failure) :
    exec model primSemantics (fuel + 2)
        (.ExprStmtCall (.Call (.inr functionName) args))
        codeOverride state =
      .error failure := by
  simp [exec, hArgs, hCall, multifill]

theorem exec_expr_primitive_error_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel
          (.ExprStmtCall (.Call (.inl prim) args))
          codeOverride state =
        .error failure) :
    (fuel = 0 ∧
      { exception := EvmYul.Yul.Exception.OutOfFuel
        state := state } = failure) ∨
    ∃ previous,
      fuel = previous + 1 ∧
        ((evalArgs model primSemantics previous args.reverse
              codeOverride state =
            .error failure) ∨
          ∃ stateAfterArgs reversedValues,
            evalArgs model primSemantics previous args.reverse
                codeOverride state =
              .ok (stateAfterArgs, reversedValues) ∧
            primSemantics.eval previous stateAfterArgs prim
                reversedValues.reverse =
              .error failure) := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      exact Or.inl ⟨rfl, hRun⟩
  | succ previous =>
      refine Or.inr ⟨previous, by omega, ?_⟩
      cases hArgs :
          evalArgs model primSemantics previous args.reverse
            codeOverride state with
      | error argsFailure =>
          simp [exec, hArgs] at hRun
          subst failure
          exact Or.inl rfl
      | ok result =>
          rcases result with ⟨stateAfterArgs, reversedValues⟩
          cases hPrim :
              primSemantics.eval previous stateAfterArgs prim
                reversedValues.reverse with
          | error primFailure =>
              simp [exec, hArgs, hPrim, multifill] at hRun
              subst failure
              exact Or.inr
                ⟨stateAfterArgs, reversedValues, rfl, hPrim⟩
          | ok result =>
              simp [exec, hArgs, hPrim, multifill] at hRun

theorem exec_block_error_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {body : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      exec model primSemantics fuel (.Block body)
          codeOverride state =
        .error failure) :
    (fuel = 0 ∧
      { exception := EvmYul.Yul.Exception.OutOfFuel
        state := state } = failure) ∨
    ∃ previous,
      fuel = previous + 1 ∧
        execSeq model primSemantics previous body
            codeOverride state =
          .error failure := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
      exact Or.inl ⟨rfl, hRun⟩
  | succ previous =>
      cases hBody :
          execSeq model primSemantics previous body
            codeOverride state with
      | error bodyFailure =>
          simp [exec, hBody] at hRun
          subst failure
          exact Or.inr ⟨previous, rfl, hBody⟩
      | ok stateAfterBody =>
          simp [exec, hBody] at hRun

theorem execSeq_cons_error_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {head : EvmYul.Yul.Ast.Stmt}
    {tail : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state : σ} {failure : Failure σ}
    (hRun :
      execSeq model primSemantics fuel (head :: tail)
          codeOverride state =
        .error failure) :
    (fuel = 0 ∧
      { exception := EvmYul.Yul.Exception.OutOfFuel
        state := state } = failure) ∨
    ∃ previous,
      fuel = previous + 1 ∧
        ((exec model primSemantics previous head
              codeOverride state =
            .error failure) ∨
          ∃ stateAfterHead shared vars,
            exec model primSemantics previous head
                codeOverride state =
              .ok stateAfterHead ∧
            model.source stateAfterHead = .Ok shared vars ∧
            execSeq model primSemantics previous tail
                codeOverride stateAfterHead =
              .error failure) := by
  cases fuel with
  | zero =>
      simp [execSeq, fail] at hRun
      exact Or.inl ⟨rfl, hRun⟩
  | succ previous =>
      cases hHead :
          exec model primSemantics previous head
            codeOverride state with
      | error headFailure =>
          simp [execSeq, hHead] at hRun
          subst failure
          exact Or.inr ⟨previous, rfl, Or.inl hHead⟩
      | ok stateAfterHead =>
          cases hSource : model.source stateAfterHead with
          | Ok shared vars =>
              cases hTail :
                  execSeq model primSemantics previous tail
                    codeOverride stateAfterHead with
              | error tailFailure =>
                  simp [execSeq, hHead, hSource, hTail] at hRun
                  subst failure
                  exact
                    Or.inr
                      ⟨previous, rfl, Or.inr
                        ⟨stateAfterHead, shared, vars,
                          hHead, hSource, hTail⟩⟩
              | ok stateAfterTail =>
                  simp [execSeq, hHead, hSource, hTail] at hRun
          | OutOfFuel =>
              simp [execSeq, hHead, hSource] at hRun
          | Checkpoint jump =>
              simp [execSeq, hHead, hSource] at hRun

theorem exec_expr_function_ok_parts
    {σ : Type} (model : StateModel σ)
    (primSemantics : PrimitiveSemantics σ)
    {fuel : Nat} {functionName : EvmYul.Yul.Ast.YulFunctionName}
    {args : List EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state final : σ}
    (hRun :
      exec model primSemantics fuel
          (.ExprStmtCall (.Call (.inr functionName) args))
          codeOverride state =
        .ok final) :
    ∃ argsFuel callFuel stateAfterArgs reversedValues
        stateAfterCall returnValues,
      fuel = argsFuel + 1 ∧
      argsFuel = callFuel + 1 ∧
      evalArgs model primSemantics argsFuel args.reverse
          codeOverride state =
        .ok (stateAfterArgs, reversedValues) ∧
      call model primSemantics callFuel reversedValues.reverse
          (some functionName) codeOverride stateAfterArgs =
        .ok (stateAfterCall, returnValues) ∧
      final = model.multifill [] stateAfterCall returnValues := by
  cases fuel with
  | zero =>
      simp [exec, fail] at hRun
  | succ argsFuel =>
      cases hArgs :
          evalArgs model primSemantics argsFuel args.reverse
            codeOverride state with
      | error failure =>
          simp [exec, hArgs] at hRun
      | ok result =>
          rcases result with ⟨stateAfterArgs, reversedValues⟩
          cases argsFuel with
          | zero =>
              simp [exec, hArgs, fail] at hRun
          | succ callFuel =>
              cases hCall :
                  call model primSemantics callFuel reversedValues.reverse
                    (some functionName) codeOverride stateAfterArgs with
              | error failure =>
                  simp [exec, hArgs, hCall, multifill] at hRun
              | ok result =>
                  rcases result with ⟨stateAfterCall, returnValues⟩
                  simp [exec, hArgs, hCall, multifill] at hRun
                  exact
                    ⟨callFuel + 1, callFuel, stateAfterArgs,
                      reversedValues, stateAfterCall, returnValues,
                      by omega, rfl, hArgs, hCall, hRun.symm⟩

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

/--
Compose a regularly completed statement with the remaining source sequence.
-/
theorem execSeq_cons_of_regular
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {stmt : EvmYul.Yul.Ast.Stmt}
    {rest : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state afterStmt final : σ}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    (hStmt :
      exec model prim fuel stmt codeOverride state =
        .ok afterStmt)
    (hSource : model.source afterStmt = .Ok shared vars)
    (hRest :
      execSeq model prim fuel rest codeOverride afterStmt =
        .ok final) :
    execSeq model prim (fuel + 1) (stmt :: rest)
        codeOverride state =
      .ok final := by
  simp [execSeq, hStmt, hSource, hRest]

/--
An abrupt source statement makes the remaining source sequence unreachable.
-/
theorem execSeq_cons_of_checkpoint
    {σ : Type} (model : StateModel σ)
    (prim : PrimitiveSemantics σ)
    {fuel : Nat} {stmt : EvmYul.Yul.Ast.Stmt}
    {rest : List EvmYul.Yul.Ast.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state afterStmt : σ}
    {jump : EvmYul.Yul.Jump}
    (hStmt :
      exec model prim fuel stmt codeOverride state =
        .ok afterStmt)
    (hSource : model.source afterStmt = .Checkpoint jump) :
    execSeq model prim (fuel + 1) (stmt :: rest)
        codeOverride state =
      .ok afterStmt := by
  simp [execSeq, hStmt, hSource]

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

theorem evalArgs_append_of_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ) :
    ∀ {fuel remainingFuel : Nat}
      {left right : List EvmYul.Yul.Ast.Expr}
      {codeOverride : Option EvmYul.Yul.Ast.YulContract}
      {source middle final : σ}
      {leftValues rightValues : List Word},
      fuel = remainingFuel + 2 * left.length →
      evalArgs model prim fuel left codeOverride source =
        .ok (middle, leftValues) →
      evalArgs model prim remainingFuel right codeOverride middle =
        .ok (final, rightValues) →
      evalArgs model prim fuel (left ++ right) codeOverride source =
        .ok (final, leftValues ++ rightValues)
  | fuel, remainingFuel, [], right, codeOverride, source, middle, final,
      leftValues, rightValues, hFuel, hLeft, hRight => by
      subst fuel
      cases remainingFuel with
      | zero =>
          simp [evalArgs, fail] at hLeft
      | succ previous =>
          simp [evalArgs] at hLeft
          rcases hLeft with ⟨rfl, rfl⟩
          simpa using hRight
  | fuel, remainingFuel, head :: tail, right, codeOverride, source,
      middle, final, leftValues, rightValues, hFuel, hLeft, hRight => by
      cases fuel with
      | zero =>
          simp [evalArgs, fail] at hLeft
      | succ previous =>
          cases hHead :
              eval model prim previous head codeOverride source with
          | error failure =>
              simp [evalArgs, hHead, evalTail] at hLeft
          | ok headResult =>
              rcases headResult with ⟨afterHead, headValue⟩
              cases previous with
              | zero =>
                  simp [evalArgs, hHead, evalTail, fail] at hLeft
              | succ tailFuel =>
                  cases hTail :
                      evalArgs model prim tailFuel tail codeOverride
                        afterHead with
                  | error failure =>
                      simp [evalArgs, hHead, evalTail, hTail] at hLeft
                  | ok tailResult =>
                      rcases tailResult with ⟨tailFinal, tailValues⟩
                      simp [evalArgs, hHead, evalTail, hTail] at hLeft
                      rcases hLeft with ⟨rfl, rfl⟩
                      have hTailFuel :
                          tailFuel =
                            remainingFuel + 2 * tail.length := by
                        simp only [List.length_cons] at hFuel
                        omega
                      have hCombined :=
                        evalArgs_append_of_parts model prim
                          hTailFuel hTail hRight
                      simpa [evalArgs, hHead, evalTail, hCombined]

theorem evalArgs_singleton_of_eval {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ)
    {fuel : Nat} {expr : EvmYul.Yul.Ast.Expr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {source final : σ} {value : Word}
    (hFuel : 2 ≤ fuel)
    (hEval :
      eval model prim fuel expr codeOverride source =
        .ok (final, value)) :
    evalArgs model prim (fuel + 1) [expr] codeOverride source =
      .ok (final, [value]) := by
  cases fuel with
  | zero =>
      omega
  | succ previous =>
      cases previous with
      | zero =>
          omega
      | succ remaining =>
          simp [evalArgs, evalTail, hEval]

theorem evalArgs_append_error_parts {σ : Type}
    (model : StateModel σ) (prim : PrimitiveSemantics σ) :
    ∀ {fuel : Nat} {left right : List EvmYul.Yul.Ast.Expr}
      {codeOverride : Option EvmYul.Yul.Ast.YulContract}
      {source : σ} {failure : Failure σ},
      evalArgs model prim fuel (left ++ right) codeOverride source =
          .error failure →
      (evalArgs model prim fuel left codeOverride source =
          .error failure) ∨
        ∃ middle leftValues remainingFuel,
          fuel = remainingFuel + 2 * left.length ∧
          evalArgs model prim fuel left codeOverride source =
            .ok (middle, leftValues) ∧
          evalArgs model prim remainingFuel right codeOverride middle =
            .error failure
  | fuel, [], right, codeOverride, source, failure, hRun => by
      cases fuel with
      | zero =>
          left
          simpa [evalArgs, fail] using hRun
      | succ previous =>
          right
          exact
            ⟨source, [], previous + 1, by simp,
              by simp [evalArgs], hRun⟩
  | fuel, head :: tail, right, codeOverride, source, failure, hRun => by
      cases fuel with
      | zero =>
          left
          simpa [evalArgs, fail] using hRun
      | succ previous =>
          cases hHead :
              eval model prim previous head codeOverride source with
          | error headFailure =>
              simp [evalArgs, hHead, evalTail] at hRun
              subst failure
              left
              simp [evalArgs, hHead, evalTail]
          | ok headResult =>
              rcases headResult with ⟨afterHead, headValue⟩
              cases previous with
              | zero =>
                  simp [evalArgs, hHead, evalTail, fail] at hRun
                  subst failure
                  left
                  simp [evalArgs, hHead, evalTail, fail]
              | succ tailFuel =>
                  cases hTailRun :
                      evalArgs model prim tailFuel (tail ++ right)
                        codeOverride afterHead with
                  | error tailFailure =>
                      simp [evalArgs, hHead, evalTail, hTailRun] at hRun
                      subst failure
                      rcases
                          evalArgs_append_error_parts
                            model prim hTailRun with
                        hTailError | hRightError
                      · left
                        simp [evalArgs, hHead, evalTail, hTailError]
                      · rcases hRightError with
                          ⟨middle, tailValues, remainingFuel,
                            hFuel, hTail, hRight⟩
                        right
                        refine
                          ⟨middle, headValue :: tailValues,
                            remainingFuel, ?_, ?_, hRight⟩
                        · simp only [List.length_cons]
                          omega
                        · simp [evalArgs, hHead, evalTail, hTail]
                  | ok tailResult =>
                      simp [evalArgs, hHead, evalTail, hTailRun] at hRun

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
