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

def lookupFunctionWithLexicalScopesIn (name : FunctionName) :
    List FunctionScope → Option (FunctionDef × List FunctionScope)
  | [] => none
  | scope :: rest =>
      match lookupFunctionInScope name scope with
      | some fn => some (fn, scope :: rest)
      | none => lookupFunctionWithLexicalScopesIn name rest

def lookupFunctionWithLexicalScopes (ctx : Context) (name : FunctionName) :
    Option (FunctionDef × List FunctionScope) :=
  lookupFunctionWithLexicalScopesIn name ctx.functionScopes

def lookupFunction (ctx : Context) (name : FunctionName) :
    Option FunctionDef :=
  (lookupFunctionWithLexicalScopes ctx name).map Prod.fst

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
        match lookupFunctionWithLexicalScopes ctx functionName with
        | none => fail state (.MissingContractFunction functionName)
        | some (fn, lexicalScopes) => do
            let sourceAtEntry :=
              EvmYul.Yul.State.mkOk
                (state.initcall fn.params fn.returns args)
            let stateAfterBody ←
              execBlock fuel' { ctx with functionScopes := lexicalScopes } fn.body
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

namespace ExecCode

theorem eq_execBlock
    (fuel : Nat) (ctx : Context) (code : List Stmt) (state : State) :
    execCode fuel ctx code state =
      execBlock fuel ctx code state := by
  rfl

end ExecCode

namespace ExecObjectCode

theorem code_none
    (fuel : Nat) (ctx : Context) (object : Object) (state : State)
    (hCode : object.code? = none) :
    execObjectCode fuel ctx object state = pure state := by
  simp [execObjectCode, hCode]

theorem code_some
    (fuel : Nat) (ctx : Context) (object : Object) (state : State)
    {code : List Stmt}
    (hCode : object.code? = some code) :
    execObjectCode fuel ctx object state = execCode fuel ctx code state := by
  simp [execObjectCode, hCode]

theorem code_some_succ
    (fuel : Nat) (ctx : Context) (object : Object) (state : State)
    {code : List Stmt}
    (hCode : object.code? = some code) :
    execObjectCode (fuel + 1) ctx object state =
      execBlock (fuel + 1) ctx code state := by
  rw [code_some (fuel + 1) ctx object state hCode]
  rfl

end ExecObjectCode

namespace LookupFunctionWithLexicalScopes

theorem head
    (ctx : Context) (name : FunctionName) (scope : FunctionScope)
    (fn : FunctionDef)
    (hLookup : lookupFunctionInScope name scope = some fn) :
    lookupFunctionWithLexicalScopes
        { ctx with functionScopes := scope :: ctx.functionScopes } name =
      some (fn, scope :: ctx.functionScopes) := by
  simp [lookupFunctionWithLexicalScopes,
    lookupFunctionWithLexicalScopesIn, hLookup]

theorem tail
    (ctx : Context) (name : FunctionName) (scope : FunctionScope)
    (hLookup : lookupFunctionInScope name scope = none) :
    lookupFunctionWithLexicalScopes
        { ctx with functionScopes := scope :: ctx.functionScopes } name =
      lookupFunctionWithLexicalScopes ctx name := by
  simp [lookupFunctionWithLexicalScopes,
    lookupFunctionWithLexicalScopesIn, hLookup]

end LookupFunctionWithLexicalScopes

namespace LexicalScopeRegression

private def outerFunction : FunctionDef :=
  { params := [], returns := [], body := [] }

private def outerTarget : FunctionDef :=
  { params := [], returns := [], body := [.leave] }

private def callerLocalTarget : FunctionDef :=
  { params := [], returns := [], body := [.break] }

private def outerScope : FunctionScope :=
  [("f", outerFunction), ("g", outerTarget)]

private def callerLocalScope : FunctionScope :=
  [("g", callerLocalTarget)]

/-- Looking up an outer function from a nested caller drops the caller's local
function frame. Calls made by `f` therefore resolve `g` in `outerScope`, where
`f` was defined, rather than in `callerLocalScope`. -/
theorem outer_function_captures_definition_suffix :
    lookupFunctionWithLexicalScopes
        { functionScopes := [callerLocalScope, outerScope] } "f" =
      some (outerFunction, [outerScope]) := by
  rfl

end LexicalScopeRegression

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

namespace Eval

theorem eval_eq_bind
    (fuel : Nat) (ctx : Context) (expr : Expr) (state : State) :
    eval fuel ctx expr state =
      Simulation.Interaction.bind (evalValues fuel ctx expr state)
        (fun result => pure (result.1, result.2.head!)) := by
  unfold eval
  rfl

end Eval

namespace EvalArgs

theorem nil_succ (fuel : Nat) (ctx : Context) (state : State) :
    evalArgs (fuel + 1) ctx [] state = pure (state, []) := by
  simp [evalArgs]

theorem cons_succ
    (fuel : Nat) (ctx : Context) (arg : Expr) (rest : List Expr)
    (state : State) :
    evalArgs (fuel + 1) ctx (arg :: rest) state =
      evalTail fuel ctx rest (eval fuel ctx arg state) := by
  simp [evalArgs]

end EvalArgs

namespace EvalValues

theorem literal_succ
    (fuel : Nat) (ctx : Context) (literal : Literal)
    (state : State) (value : Word)
    (hLiteral : literalWord? literal = some value) :
    evalValues (fuel + 1) ctx (.literal literal) state =
      pure (state, [value]) := by
  simp [evalValues, hLiteral]

theorem identifier_succ
    (fuel : Nat) (ctx : Context) (name : Name)
    (state : State) (value : Word)
    (hLookup : state.lookup? name = some value) :
    evalValues (fuel + 1) ctx (.identifier name) state =
      pure (state, [value]) := by
  simp [evalValues, hLookup]

theorem clz_succ
    (fuel : Nat) (ctx : Context) (arg : Expr) (state : State) :
    evalValues (fuel + 1) ctx (.functionCall "clz" [arg]) state =
      (do
        let result ← eval fuel ctx arg state
        pure (result.1, [Elab.ClzHelperModel.reference result.2])) := by
  simp [evalValues]

theorem functionCall_succ_of_ne_clz
    (fuel : Nat) (ctx : Context) (name : Name) (args : List Expr)
    (state : State)
    (hClz : name ≠ "clz") :
    evalValues (fuel + 1) ctx (.functionCall name args) state =
      match CallClass.classifyCall name with
      | .primitive =>
          match Frontend.Primitive.ofName? name with
          | none => fail state .InvalidExpression
          | some op =>
              (do
                let result ← evalArgs fuel ctx args.reverse state
                Yul.InteractionSemantics.primitiveSemantics.eval
                  fuel result.1 op result.2.reverse)
      | .user =>
          (do
            let result ← evalArgs fuel ctx args.reverse state
            call fuel ctx result.2.reverse name result.1)
      | .objectBuiltin =>
          evalObjectBuiltin fuel ctx name args state
      | .dialectBuiltin =>
          fail state .InvalidExpression := by
  simp [evalValues, hClz]

end EvalValues

namespace EvalObjectBuiltin

theorem datasize_succ
    (fuel : Nat) (ctx : Context) (nameArg : Expr) (state : State)
    (dataName : Name) (size : Word)
    (hName : objectBuiltinNameArg? nameArg = some dataName)
    (hSize : ctx.objectBuiltins.size? dataName = some size) :
    evalObjectBuiltin (fuel + 1) ctx "datasize" [nameArg] state =
      pure (state, [size]) := by
  simp [evalObjectBuiltin, hName, hSize]

theorem dataoffset_succ
    (fuel : Nat) (ctx : Context) (nameArg : Expr) (state : State)
    (dataName : Name) (offset : Word)
    (hName : objectBuiltinNameArg? nameArg = some dataName)
    (hOffset : ctx.objectBuiltins.offset? dataName = some offset) :
    evalObjectBuiltin (fuel + 1) ctx "dataoffset" [nameArg] state =
      pure (state, [offset]) := by
  simp [evalObjectBuiltin, hName, hOffset]

theorem linkersymbol_succ
    (fuel : Nat) (ctx : Context) (nameArg : Expr) (state : State)
    (linkerName : Name) (value : Word)
    (hName : objectBuiltinNameArg? nameArg = some linkerName)
    (hValue : ctx.objectBuiltins.findLinkerSymbol? linkerName = some value) :
    evalObjectBuiltin (fuel + 1) ctx "linkersymbol" [nameArg] state =
      pure (state, [value]) := by
  simp [evalObjectBuiltin, hName, hValue]

theorem loadimmutable_succ
    (fuel : Nat) (ctx : Context) (nameArg : Expr) (state : State)
    (immutableName : Name) (value : Word)
    (hName : objectBuiltinNameArg? nameArg = some immutableName)
    (hValue :
      ctx.objectBuiltins.findImmutableValue? immutableName = some value) :
    evalObjectBuiltin (fuel + 1) ctx "loadimmutable" [nameArg] state =
      pure (state, [value]) := by
  simp [evalObjectBuiltin, hName, hValue]

theorem memoryguard_succ
    (fuel : Nat) (ctx : Context) (value : Expr) (state : State) :
    evalObjectBuiltin (fuel + 1) ctx "memoryguard" [value] state =
      (do
        let result ← eval fuel ctx value state
        pure (result.1, [result.2])) := by
  simp [evalObjectBuiltin]

theorem datacopy_succ
    (fuel : Nat) (ctx : Context) (args : List Expr) (state : State)
    (op : EvmYul.Operation .Yul)
    (hOp : Frontend.Primitive.ofName? "codecopy" = some op) :
    evalObjectBuiltin (fuel + 1) ctx "datacopy" args state =
      (do
        let result ← evalArgs fuel ctx args.reverse state
        Yul.InteractionSemantics.primitiveSemantics.eval
          fuel result.1 op result.2.reverse) := by
  simp [evalObjectBuiltin, hOp]

end EvalObjectBuiltin

namespace Call

theorem explicit_succ
    (fuel : Nat) (ctx : Context) (args : List Word)
    (functionName : FunctionName) (state : State)
    (fn : FunctionDef) (lexicalScopes : List FunctionScope)
    (hLookup :
      lookupFunctionWithLexicalScopes ctx functionName =
        some (fn, lexicalScopes)) :
    call (fuel + 1) ctx args functionName state =
      (do
        let sourceAtEntry :=
          EvmYul.Yul.State.mkOk
            (state.initcall fn.params fn.returns args)
        let stateAfterBody ←
          execBlock fuel { ctx with functionScopes := lexicalScopes } fn.body
            (Yul.InteractionSemantics.stateModel.withSource
              state sourceAtEntry)
        let sourceAfterCall :=
          (stateAfterBody.reviveJump.overwrite? state).setStore state
        pure (sourceAfterCall, fn.returns.map stateAfterBody.lookup!)) := by
  simp [call, hLookup]

end Call

namespace ExecSeq

theorem nil_succ (fuel : Nat) (ctx : Context) (state : State) :
    execSeq (fuel + 1) ctx [] state = pure state := by
  simp [execSeq]

theorem cons_succ
    (fuel : Nat) (ctx : Context) (stmt : Stmt) (rest : List Stmt)
    (state : State) :
    execSeq (fuel + 1) ctx (stmt :: rest) state =
      (do
        let stateAfterStmt ← exec fuel ctx stmt state
        match stateAfterStmt with
        | .Ok _ _ => execSeq fuel ctx rest stateAfterStmt
        | .OutOfFuel => pure stateAfterStmt
        | .Checkpoint _ => pure stateAfterStmt) := by
  simp [execSeq]

end ExecSeq

namespace ExecBlock

theorem succ
    (fuel : Nat) (ctx : Context) (stmts : List Stmt) (state : State) :
    execBlock (fuel + 1) ctx stmts state =
      match functionScope? stmts with
      | none => fail state (.DuplicateDeclaration "Yul function")
      | some scope =>
          (do
            let stateAfterBody ←
              execSeq fuel (ctx.withFunctionScope scope) stmts state
            pure (stateAfterBody.restrictStoreTo state.store)) := by
  simp [execBlock]

end ExecBlock

namespace Exec

theorem block_succ
    (fuel : Nat) (ctx : Context) (stmts : List Stmt) (state : State) :
    exec (fuel + 1) ctx (.block stmts) state =
      execBlock fuel ctx stmts state := by
  simp [exec]

theorem variableDeclaration_none_succ
    (fuel : Nat) (ctx : Context) (names : List Name) (state : State) :
    exec (fuel + 1) ctx (.variableDeclaration names none) state =
      match EvmYul.Yul.checkDeclaration state names with
      | .error err => fail state err
      | .ok () => pure (state.zeroFill names) := by
  simp [exec]

theorem variableDeclaration_some_succ
    (fuel : Nat) (ctx : Context) (names : List Name)
    (value : Expr) (state : State) :
    exec (fuel + 1) ctx (.variableDeclaration names (some value)) state =
      match EvmYul.Yul.checkDeclaration state names with
      | .error err => fail state err
      | .ok () =>
          (do
            let result ← evalValues fuel ctx value state
            pure (result.1.multifill names result.2)) := by
  simp [exec]

theorem assignment_succ
    (fuel : Nat) (ctx : Context) (names : List Name)
    (value : Expr) (state : State) :
    exec (fuel + 1) ctx (.assignment names value) state =
      match EvmYul.Yul.checkAssignment state names with
      | .error err => fail state err
      | .ok () =>
          (do
            let result ← evalValues fuel ctx value state
            pure (result.1.multifill names result.2)) := by
  simp [exec]

theorem expressionStatement_succ
    (fuel : Nat) (ctx : Context) (expr : Expr) (state : State) :
    exec (fuel + 1) ctx (.expressionStatement expr) state =
      match expr with
      | .functionCall "setimmutable" [base, nameArg, value] =>
          match objectBuiltinNameArg? nameArg >>=
              ctx.objectBuiltins.findImmutableReferences? with
          | none => fail state .InvalidArguments
          | some references =>
              match patchSetImmutableStmts? references base value with
              | none => fail state .InvalidArguments
              | some stmts => execBlock fuel ctx stmts state
      | _ =>
          (do
            let result ← evalValues fuel ctx expr state
            pure result.1) := by
  cases expr <;> simp [exec]
  next name args =>
    by_cases hName : name = "setimmutable"
    · subst name
      cases args with
      | nil =>
          simp [exec]
      | cons base rest =>
          cases rest with
          | nil =>
              simp [exec]
          | cons nameArg rest =>
              cases rest with
              | nil =>
                  simp [exec]
              | cons value rest =>
                  cases rest with
                  | nil =>
                      simp [exec]
                  | cons extra rest =>
                      simp [exec]
    · simp [exec, hName]

theorem functionDefinition_succ
    (fuel : Nat) (ctx : Context) (name : Name)
    (params returns : List Name) (body : List Stmt) (state : State) :
    exec (fuel + 1) ctx
        (.functionDefinition name params returns body) state =
      pure state := by
  simp [exec]

theorem switch_succ
    (fuel : Nat) (ctx : Context) (scrutinee : Expr)
    (cases : List (SwitchCaseValue × List Stmt)) (default : List Stmt)
    (state : State) :
    exec (fuel + 1) ctx (.switch scrutinee cases default) state =
      (do
        let result ← eval fuel ctx scrutinee state
        match selectSwitchCase result.2 default cases with
        | none => fail result.1 .InvalidArguments
        | some body => execBlock fuel ctx body result.1) := by
  simp [exec]

theorem forLoop_succ
    (fuel : Nat) (ctx : Context) (pre : List Stmt)
    (condition : Expr) (post body : List Stmt) (state : State) :
    exec (fuel + 1) ctx (.forLoop pre condition post body) state =
      execFor fuel ctx pre condition post body state := by
  simp [exec]

theorem ifThen_succ
    (fuel : Nat) (ctx : Context) (condition : Expr)
    (body : List Stmt) (state : State) :
    exec (fuel + 1) ctx (.ifThen condition body) state =
      (do
        let result ← eval fuel ctx condition state
        if result.2 ≠ ⟨0⟩ then
          execBlock fuel ctx body result.1
        else
          pure result.1) := by
  simp [exec]

theorem break_succ (fuel : Nat) (ctx : Context) (state : State) :
    exec (fuel + 1) ctx .break state =
      pure (EvmYul.Yul.State.setBreak state) := by
  simp [exec]

theorem continue_succ (fuel : Nat) (ctx : Context) (state : State) :
    exec (fuel + 1) ctx .continue state =
      pure (EvmYul.Yul.State.setContinue state) := by
  simp [exec]

theorem leave_succ (fuel : Nat) (ctx : Context) (state : State) :
    exec (fuel + 1) ctx .leave state =
      pure (EvmYul.Yul.State.setLeave state) := by
  simp [exec]

end Exec

namespace ExecFor

theorem succ
    (fuel : Nat) (ctx : Context) (pre : List Stmt)
    (condition : Expr) (post body : List Stmt) (state : State) :
    execFor (fuel + 1) ctx pre condition post body state =
      match functionScope? pre with
      | none => fail state (.DuplicateDeclaration "Yul for-init function")
      | some scope =>
          (do
            let stateAfterPre ←
              execSeq fuel (ctx.withFunctionScope scope) pre state
            let stateAfterLoop ←
              match stateAfterPre with
              | .Ok _ _ =>
                  loop fuel (ctx.withFunctionScope scope)
                    condition post body stateAfterPre
              | .OutOfFuel => pure stateAfterPre
              | .Checkpoint _ => pure stateAfterPre
            pure (stateAfterLoop.restrictStoreTo state.store)) := by
  simp [execFor]

end ExecFor

namespace Loop

theorem zero
    (ctx : Context) (condition : Expr) (post body : List Stmt)
    (state : State) :
    loop 0 ctx condition post body state = fail state .OutOfFuel := by
  simp [loop]

theorem one
    (ctx : Context) (condition : Expr) (post body : List Stmt)
    (state : State) :
    loop 1 ctx condition post body state = fail state .OutOfFuel := by
  simp [loop]

theorem succ_succ
    (fuel : Nat) (ctx : Context) (condition : Expr)
    (post body : List Stmt) (state : State) :
    loop (fuel + 1 + 1) ctx condition post body state =
      (do
        let result ←
          eval fuel ctx condition (EvmYul.Yul.State.mkOk state)
        if result.2 = ⟨0⟩ then
          pure (result.1.overwrite? state)
        else
          let stateAfterBody ← execBlock fuel ctx body result.1
          match stateAfterBody with
          | .OutOfFuel =>
              pure (stateAfterBody.overwrite? state)
          | .Checkpoint (.Break _ _) =>
              pure (stateAfterBody.reviveJump.overwrite? state)
          | .Checkpoint (.Leave _ _) =>
              pure (stateAfterBody.overwrite? state)
          | .Checkpoint (.Continue _ _)
          | .Ok _ _ =>
              let stateAfterPost ←
                execBlock fuel ctx post stateAfterBody.reviveJump
              let sourceAfterPost := stateAfterPost.overwrite? state
              match stateAfterPost with
              | .OutOfFuel => pure sourceAfterPost
              | .Checkpoint (.Leave _ _) => pure sourceAfterPost
              | _ =>
                  let stateAfterLoop ←
                    loop fuel ctx condition post body sourceAfterPost
                  pure (stateAfterLoop.overwrite? state)) := by
  simp [loop]

end Loop

end SourceSemantics
end Raw
end RawAst
end Solidity
end EvmCompiler
