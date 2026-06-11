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

end Effectful
end Source
end Yul
end EvmCompiler
