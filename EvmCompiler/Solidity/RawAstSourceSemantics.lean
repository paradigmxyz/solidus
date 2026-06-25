import EvmCompiler.Solidity.RawAst
import EvmCompiler.Yul.InteractionSemantics

/-!
Independent execution semantics for accepted raw solc `irOptimizedAst` Yul.

The raw decoder/elaborator remains the construction path for compiler
artifacts.  This module gives the decoded raw syntax its own source semantics so
the frontend theorem can relate raw execution to the canonical ordered-Yul
artifact rather than treating elaboration as part of the source definition.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst
namespace Raw
namespace SourceSemantics

abbrev State := Yul.InteractionSemantics.State
abbrev Open (α : Type) := Yul.InteractionSemantics.Open α
abbrev FunctionName := Name

structure FunctionDef where
  params : List Name
  returns : List Name
  body : List Stmt
  deriving Inhabited, Repr

abbrev FunctionScope := List (FunctionName × FunctionDef)

structure Context where
  functionScopes : List FunctionScope := []
  objectBuiltins : Frontend.ObjectBuiltinContext := default
  deriving Inhabited, Repr

namespace Context

def withFunctionScope (ctx : Context) (scope : FunctionScope) : Context :=
  { ctx with functionScopes := scope :: ctx.functionScopes }

end Context

def fail {α : Type} (state : State)
    (exception : EvmYul.Yul.Exception) : Open α :=
  Yul.InteractionSemantics.Primitive.fail state exception

def literalWord? : Literal → Option Word
  | .number value => some value
  | .bool value =>
      some (EvmYul.UInt256.ofNat (if value then 1 else 0))
  | .stringLit value => Frontend.StringLiteral.word? value
  | .bytesLit bytes => Frontend.StringLiteral.wordBytes? bytes

def switchCaseValueWord? : SwitchCaseValue → Option Word
  | .literal literal => literalWord? literal

def objectBuiltinNameArg? : Expr → Option Name
  | .literal (.stringLit name) => some name
  | .literal (.bytesLit bytes) =>
      some (Frontend.Expr.objectBuiltinNameFromBytes bytes)
  | _ => none

def lookupFunctionInScope (name : FunctionName) :
    FunctionScope → Option FunctionDef
  | [] => none
  | (headName, fn) :: rest =>
      if headName == name then some fn else lookupFunctionInScope name rest

def lookupFunction (ctx : Context) (name : FunctionName) :
    Option FunctionDef :=
  let rec go : List FunctionScope → Option FunctionDef
    | [] => none
    | scope :: rest =>
        match lookupFunctionInScope name scope with
        | some fn => some fn
        | none => go rest
  go ctx.functionScopes

def functionScope? : List Stmt → Option FunctionScope
  | [] => some []
  | stmt :: rest => do
      let tail ← functionScope? rest
      match stmt with
      | .functionDefinition name params returns body =>
          if tail.any fun entry => entry.fst == name then
            none
          else
            some ((name, { params, returns, body }) :: tail)
      | _ => some tail

def patchSetImmutableStmt? (reference : Frontend.ImmutableReference)
    (base value : Expr) : Option Stmt :=
  if reference.isPatchable then
    some
      (.expressionStatement
        (.functionCall "mstore"
          [ .functionCall "add"
              [base, .literal (.number (EvmYul.UInt256.ofNat reference.start))]
          , value ]))
  else
    none

def patchSetImmutableStmts? :
    List Frontend.ImmutableReference → Expr → Expr → Option (List Stmt)
  | [], _base, _value => some []
  | reference :: rest, base, value => do
      let head ← patchSetImmutableStmt? reference base value
      let tail ← patchSetImmutableStmts? rest base value
      some (head :: tail)

def selectSwitchCase (value : Word) (default : List Stmt) :
    List (SwitchCaseValue × List Stmt) → Option (List Stmt)
  | [] => some default
  | (caseValue, body) :: rest =>
      match switchCaseValueWord? caseValue with
      | none => none
      | some word =>
          if value == word then
            some body
          else
            selectSwitchCase value default rest

mutual

  def evalTail (fuel : Nat) (ctx : Context) (args : List Expr)
      (result : Open (State × Word)) : Open (State × List Word) := do
    let (state, arg) ← result
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        let (state', args') ← evalArgs fuel' ctx args state
        pure (state', arg :: args')
  termination_by (fuel, 0, sizeOf args, 0)

  def evalArgs (fuel : Nat) (ctx : Context) (args : List Expr)
      (state : State) : Open (State × List Word) :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match args with
        | [] => pure (state, [])
        | arg :: rest =>
            evalTail fuel' ctx rest (eval fuel' ctx arg state)
  termination_by (fuel, 1, sizeOf args, 0)

  def evalValues (fuel : Nat) (ctx : Context) (expr : Expr)
      (state : State) : Open (State × List Word) :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match expr with
        | .literal literal =>
            match literalWord? literal with
            | some value => pure (state, [value])
            | none => fail state .InvalidExpression
        | .identifier name =>
            match state.lookup? name with
            | some value => pure (state, [value])
            | none => fail state (.UnknownIdentifier name)
        | .functionCall "clz" [arg] => do
            let (stateAfterArg, value) ← eval fuel' ctx arg state
            pure (stateAfterArg, [Elab.ClzHelperModel.reference value])
        | .functionCall "clz" _ =>
            fail state .InvalidArguments
        | .functionCall name args =>
            match CallClass.classifyCall name with
            | .primitive =>
                match Frontend.Primitive.ofName? name with
                | none => fail state .InvalidExpression
                | some op => do
                    let (stateAfterArgs, values) ←
                      evalArgs fuel' ctx args.reverse state
                    Yul.InteractionSemantics.primitiveSemantics.eval fuel'
                      stateAfterArgs op values.reverse
            | .user => do
                let (stateAfterArgs, values) ←
                  evalArgs fuel' ctx args.reverse state
                call fuel' ctx values.reverse name stateAfterArgs
            | .objectBuiltin =>
                evalObjectBuiltin fuel' ctx name args state
            | .dialectBuiltin =>
                fail state .InvalidExpression
  termination_by (fuel, 2, sizeOf expr, 0)

  def eval (fuel : Nat) (ctx : Context) (expr : Expr)
      (state : State) : Open (State × Word) := do
    let (state', values) ← evalValues fuel ctx expr state
    pure (state', values.head!)
  termination_by (fuel, 3, sizeOf expr, 0)

  def evalObjectBuiltin (fuel : Nat) (ctx : Context) (name : Name)
      (args : List Expr) (state : State) : Open (State × List Word) :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match name, args with
        | "datasize", [nameArg] =>
            match objectBuiltinNameArg? nameArg >>= ctx.objectBuiltins.size? with
            | some size => pure (state, [size])
            | none => fail state .InvalidArguments
        | "dataoffset", [nameArg] =>
            match objectBuiltinNameArg? nameArg >>= ctx.objectBuiltins.offset? with
            | some offset => pure (state, [offset])
            | none => fail state .InvalidArguments
        | "linkersymbol", [nameArg] =>
            match objectBuiltinNameArg? nameArg >>=
                ctx.objectBuiltins.findLinkerSymbol? with
            | some value => pure (state, [value])
            | none => fail state .InvalidArguments
        | "loadimmutable", [nameArg] =>
            match objectBuiltinNameArg? nameArg >>=
                ctx.objectBuiltins.findImmutableValue? with
            | some value => pure (state, [value])
            | none => fail state .InvalidArguments
        | "memoryguard", [value] => do
            let (stateAfterValue, size) ← eval fuel' ctx value state
            pure (stateAfterValue, [size])
        | "datacopy", args =>
            match Frontend.Primitive.ofName? "codecopy" with
            | none => fail state .InvalidExpression
            | some op => do
                let (stateAfterArgs, values) ←
                  evalArgs fuel' ctx args.reverse state
                Yul.InteractionSemantics.primitiveSemantics.eval fuel'
                  stateAfterArgs op values.reverse
        | _, _ => fail state .InvalidExpression
  termination_by (fuel, 4, sizeOf args, 0)

  def call (fuel : Nat) (ctx : Context) (args : List Word)
      (functionName : FunctionName) (state : State) :
      Open (State × List Word) :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match lookupFunction ctx functionName with
        | none => fail state (.MissingContractFunction functionName)
        | some fn => do
            let sourceAtEntry :=
              EvmYul.Yul.State.mkOk
                (state.initcall fn.params fn.returns args)
            let stateAfterBody ←
              execBlock fuel' ctx fn.body
                (Yul.InteractionSemantics.stateModel.withSource
                  state sourceAtEntry)
            let sourceAfterCall :=
              (stateAfterBody.reviveJump.overwrite? state).setStore state
            pure (sourceAfterCall, fn.returns.map stateAfterBody.lookup!)
  termination_by (fuel, 5, sizeOf args, 0)

  def execSeq (fuel : Nat) (ctx : Context) (stmts : List Stmt)
      (state : State) : Open State :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match stmts with
        | [] => pure state
        | stmt :: rest => do
            let stateAfterStmt ← exec fuel' ctx stmt state
            match stateAfterStmt with
            | .Ok _ _ => execSeq fuel' ctx rest stateAfterStmt
            | .OutOfFuel => pure stateAfterStmt
            | .Checkpoint _ => pure stateAfterStmt
  termination_by (fuel, 6, sizeOf stmts, 0)

  def execBlock (fuel : Nat) (ctx : Context) (stmts : List Stmt)
      (state : State) : Open State :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match functionScope? stmts with
        | none => fail state (.DuplicateDeclaration "Yul function")
        | some scope => do
            let source := state
            let stateAfterBody ←
              execSeq fuel' (ctx.withFunctionScope scope) stmts state
            pure (stateAfterBody.restrictStoreTo source.store)
  termination_by (fuel, 7, sizeOf stmts, 0)

  def exec (fuel : Nat) (ctx : Context) (stmt : Stmt)
      (state : State) : Open State :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match stmt with
        | .block stmts =>
            execBlock fuel' ctx stmts state
        | .variableDeclaration names none =>
            match EvmYul.Yul.checkDeclaration state names with
            | .error err => fail state err
            | .ok () => pure (state.zeroFill names)
        | .variableDeclaration names (some value) =>
            match EvmYul.Yul.checkDeclaration state names with
            | .error err => fail state err
            | .ok () => do
                let (stateAfterValue, values) ←
                  evalValues fuel' ctx value state
                pure (stateAfterValue.multifill names values)
        | .assignment names value =>
            match EvmYul.Yul.checkAssignment state names with
            | .error err => fail state err
            | .ok () => do
                let (stateAfterValue, values) ←
                  evalValues fuel' ctx value state
                pure (stateAfterValue.multifill names values)
        | .expressionStatement (.functionCall "setimmutable"
            [base, nameArg, value]) =>
            match objectBuiltinNameArg? nameArg >>=
                ctx.objectBuiltins.findImmutableReferences? with
            | none => fail state .InvalidArguments
            | some references =>
                match patchSetImmutableStmts? references base value with
                | none => fail state .InvalidArguments
                | some stmts => execBlock fuel' ctx stmts state
        | .expressionStatement expr => do
            let (stateAfterExpr, _values) ← evalValues fuel' ctx expr state
            pure stateAfterExpr
        | .functionDefinition _name _params _returns _body =>
            pure state
        | .switch scrutinee cases default => do
            let (stateAfterScrutinee, value) ←
              eval fuel' ctx scrutinee state
            match selectSwitchCase value default cases with
            | none => fail stateAfterScrutinee .InvalidArguments
            | some body => execBlock fuel' ctx body stateAfterScrutinee
        | .forLoop pre condition post body =>
            execFor fuel' ctx pre condition post body state
        | .ifThen condition body => do
            let (stateAfterCondition, value) ←
              eval fuel' ctx condition state
            if value ≠ ⟨0⟩ then
              execBlock fuel' ctx body stateAfterCondition
            else
              pure stateAfterCondition
        | .break => pure (EvmYul.Yul.State.setBreak state)
        | .continue => pure (EvmYul.Yul.State.setContinue state)
        | .leave => pure (EvmYul.Yul.State.setLeave state)
  termination_by (fuel, 8, sizeOf stmt, 0)

  def execFor (fuel : Nat) (ctx : Context) (pre : List Stmt)
      (condition : Expr) (post body : List Stmt) (state : State) :
      Open State :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | fuel' + 1 =>
        match functionScope? pre with
        | none => fail state (.DuplicateDeclaration "Yul for-init function")
        | some scope => do
            let source := state
            let ctx' := ctx.withFunctionScope scope
            let stateAfterPre ← execSeq fuel' ctx' pre state
            let stateAfterLoop ←
              match stateAfterPre with
              | .Ok _ _ => loop fuel' ctx' condition post body stateAfterPre
              | .OutOfFuel => pure stateAfterPre
              | .Checkpoint _ => pure stateAfterPre
            pure (stateAfterLoop.restrictStoreTo source.store)
  termination_by (fuel, 9, sizeOf pre + sizeOf condition + sizeOf post + sizeOf body, 0)

  def loop (fuel : Nat) (ctx : Context) (condition : Expr)
      (post body : List Stmt) (state : State) : Open State :=
    match fuel with
    | 0 => fail state .OutOfFuel
    | 1 => fail state .OutOfFuel
    | fuel' + 1 + 1 => do
        let source := state
        let (stateAfterCond, condValue) ←
          eval fuel' ctx condition (EvmYul.Yul.State.mkOk state)
        if condValue = ⟨0⟩ then
          pure (stateAfterCond.overwrite? source)
        else
          let stateAfterBody ← execBlock fuel' ctx body stateAfterCond
          match stateAfterBody with
          | .OutOfFuel =>
              pure (stateAfterBody.overwrite? source)
          | .Checkpoint (.Break _ _) =>
              pure (stateAfterBody.reviveJump.overwrite? source)
          | .Checkpoint (.Leave _ _) =>
              pure (stateAfterBody.overwrite? source)
          | .Checkpoint (.Continue _ _)
          | .Ok _ _ => do
              let stateAfterPost ←
                execBlock fuel' ctx post stateAfterBody.reviveJump
              let sourceAfterPost := stateAfterPost.overwrite? source
              match stateAfterPost with
              | .OutOfFuel => pure sourceAfterPost
              | .Checkpoint (.Leave _ _) => pure sourceAfterPost
              | _ =>
                  let stateAfterLoop ←
                    loop fuel' ctx condition post body sourceAfterPost
                  pure (stateAfterLoop.overwrite? source)
  termination_by (fuel, 10, sizeOf condition + sizeOf post + sizeOf body, 0)

  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega

end

def execCode (fuel : Nat) (ctx : Context) (code : List Stmt)
    (state : State) : Open State :=
  execBlock fuel ctx code state

def execObjectCode (fuel : Nat) (ctx : Context) (object : Object)
    (state : State) : Open State :=
  match object.code? with
  | none => pure state
  | some code => execCode fuel ctx code state

def contextForObject (context : Frontend.ObjectBuiltinContext) : Context :=
  { objectBuiltins := context }

@[simp] theorem evalArgs_zero
    (ctx : Context) (args : List Expr) (state : State) :
    evalArgs 0 ctx args state = fail state .OutOfFuel := by
  simp [evalArgs]

@[simp] theorem execSeq_zero
    (ctx : Context) (stmts : List Stmt) (state : State) :
    execSeq 0 ctx stmts state = fail state .OutOfFuel := by
  simp [execSeq]

@[simp] theorem execBlock_zero
    (ctx : Context) (stmts : List Stmt) (state : State) :
    execBlock 0 ctx stmts state = fail state .OutOfFuel := by
  simp [execBlock]

end SourceSemantics
end Raw
end RawAst
end Solidity
end EvmCompiler
