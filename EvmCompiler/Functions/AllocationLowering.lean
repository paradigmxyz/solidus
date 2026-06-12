import EvmCompiler.Functions.MixedAllocation
import EvmCompiler.Functions.SourceSemantics
import EvmCompiler.Compiler.AllocatedTypedCfg

namespace EvmCompiler
namespace Functions
namespace AllocationLowering

open Locals.Allocation

abbrev SlotSet := MixedAllocation.SlotSet

structure State where
  allocation : AllocationSupport.CompileState
  layout : Locals.Layout
  deriving DecidableEq, Repr

structure Ctx where
  functions : List AllocationSupport.FunSlots
  frameConfig? : Option AllocationSupport.ScratchFrameConfig
  frameName : Name
  stackSlots : SlotSet
  root : ScopeId
  scratchBindings : List (Name × Nat)
  frameFunctions : List Name

def isStackSlot (ctx : Ctx) (slot : Nat) : Bool :=
  decide (slot ∈ ctx.stackSlots)

def frameDepth? (ctx : Ctx) (state : State) : Option Nat := do
  let depth ← Locals.Layout.lookupDepth? ctx.frameName state.layout
  some (depth - 1)

def exprSeqOne (expr : Locals.Expr 1) : Locals.ExprSeq 1 := by
  simpa using Locals.ExprSeq.cons expr Locals.ExprSeq.nil

def exprSeqTwo (left right : Locals.Expr 1) : Locals.ExprSeq 2 := by
  simpa using
    Locals.ExprSeq.cons left
      (Locals.ExprSeq.cons right Locals.ExprSeq.nil)

def scratchAddressExpr (frameName : Name) (slot : Nat) : Locals.Expr 1 :=
  .prim .add
    (exprSeqTwo (.var frameName) (.lit (AllocationSupport.slotOffset slot)))

def scratchLoadExpr (frameName : Name) (slot : Nat) : Locals.Expr 1 :=
  .prim .mload (exprSeqOne (scratchAddressExpr frameName slot))

def scratchStoreExpr (frameName : Name) (slot : Nat)
    (value : Locals.Expr 1) : Locals.Expr 0 :=
  .prim .mstore
    (exprSeqTwo value (scratchAddressExpr frameName slot))

mutual
  def lowerExpr (ctx : Ctx) (state : State) {results : Nat} :
      Expr results → Option (Locals.Expr results)
    | .lit value => some (.lit value)
    | .var name => do
        let slot ← AllocationSupport.lookupSlot? name state.allocation.env
        if isStackSlot ctx slot then
          some (.var name)
        else
          if ctx.frameName ∈ state.layout then
            some (scratchLoadExpr ctx.frameName slot)
          else
            none
    | .code code => some (.code code)
    | .prim op args => do
        let lowered ← lowerExprSeq ctx state args
        some (.prim op lowered)

  def lowerExprSeq (ctx : Ctx) (state : State) {results : Nat} :
      Locals.ExprSeq results → Option (Locals.ExprSeq results)
    | .nil => some .nil
    | .cons head tail => do
        let loweredHead ← lowerExpr ctx state head
        let loweredTail ← lowerExprSeq ctx state tail
        some (.cons loweredHead loweredTail)
end

theorem lowerExpr_var_scratch
    {ctx : Ctx} {state : State} {name : Name} {slot : Nat}
    (hSlot :
      AllocationSupport.lookupSlot? name state.allocation.env =
        some slot)
    (hStack : isStackSlot ctx slot = false)
    (hFrame : ctx.frameName ∈ state.layout) :
    lowerExpr ctx state (.var name) =
      some (scratchLoadExpr ctx.frameName slot) := by
  simp [lowerExpr, hSlot, hStack, hFrame]

theorem scratchLoadExpr_compileCode
    {frameName : Name} {slot offset depth : Nat}
    {ctx : Locals.Ctx} {op : Structured.BasicOp}
    (hDepth :
      Locals.Layout.lookupDepth? frameName ctx.layout =
        some depth)
    (hDup :
      Locals.StackOp.dup? (offset + depth) = some op) :
    Locals.Expr.compileCode ctx offset
        (scratchLoadExpr frameName slot) =
      some
        [ .op op,
          .push (AllocationSupport.slotOffset slot),
          .op .add,
          .op .mload ] := by
  simp [scratchLoadExpr, scratchAddressExpr, exprSeqOne, exprSeqTwo,
    Locals.Expr.compileCode, Locals.ExprSeq.compileCode, hDepth, hDup]

theorem scratchStoreExpr_compileCode
    {frameName : Name} {slot offset depth : Nat}
    {ctx : Locals.Ctx} {value : Locals.Expr 1}
    {valueCode : Structured.Code} {op : Structured.BasicOp}
    (hValue :
      Locals.Expr.compileCode ctx offset value = some valueCode)
    (hDepth :
      Locals.Layout.lookupDepth? frameName ctx.layout =
        some depth)
    (hDup :
      Locals.StackOp.dup? (offset + 1 + depth) = some op) :
    Locals.Expr.compileCode ctx offset
        (scratchStoreExpr frameName slot value) =
      some
        (valueCode ++
          [ .op op,
            .push (AllocationSupport.slotOffset slot),
            .op .add,
            .op .mstore ]) := by
  simp [scratchStoreExpr, scratchAddressExpr, exprSeqTwo,
    Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
    hValue, hDepth, hDup]

def lowerExprList (ctx : Ctx) (state : State) :
    List (Expr 1) → Option (List (Locals.Expr 1))
  | [] => some []
  | expr :: rest => do
      let lowered ← lowerExpr ctx state expr
      let tail ← lowerExprList ctx state rest
      some (lowered :: tail)

def exprSeqOfList : (exprs : List (Locals.Expr 1)) →
    Locals.ExprSeq exprs.length
  | [] => .nil
  | expr :: rest => by
      simpa [Nat.add_comm] using
        Locals.ExprSeq.cons expr (exprSeqOfList rest)

def eraseName (name : Name) (layout : Locals.Layout) : Locals.Layout :=
  layout.filter fun candidate => candidate != name

def bindEntryLayout (layout : Locals.Layout) : Locals.Stmt :=
  .expr
    (Locals.Expr.code (results := 0)
      [Structured.BasicInstr.bindLocals 0 layout])

def bindScratchBindings (baseDepth : Nat)
    (bindings : List (Name × Nat)) : Locals.Stmt :=
  .expr
    (Locals.Expr.code (results := 0)
      (AllocationSupport.bindScratchBindingsCode baseDepth bindings))

def frameExpr
    (config : AllocationSupport.ScratchFrameConfig) : Locals.Expr 1 :=
  .code (AllocationSupport.scratchFrameAcquireCode config)

def splitPrelude : List Stmt → List Locals.Stmt × List Stmt
  | [] => ([], [])
  | stmt :: rest =>
      match AllocationSupport.compilePreludeStmt? stmt with
      | some (.code code) =>
          let (loweredPrefix, tail) := splitPrelude rest
          (.expr (Locals.Expr.code (results := 0) code) ::
              loweredPrefix,
            tail)
      | _ => ([], stmt :: rest)

def lowerScratchParam (ctx : Ctx) (name : Name) (slot : Nat)
    (layout : Locals.Layout) : List Locals.Stmt × Locals.Layout :=
  let target := eraseName name layout
  ([ .expr (scratchStoreExpr ctx.frameName slot (.var name)),
     .promoteName name,
     .cleanupTo target ],
   target)

def lowerParams (ctx : Ctx) :
    List (Name × Nat) → Locals.Layout →
      List Locals.Stmt × Locals.Layout
  | [], layout => ([], layout)
  | (name, slot) :: rest, layout =>
      if isStackSlot ctx slot then
        lowerParams ctx rest layout
      else
        let (head, nextLayout) :=
          lowerScratchParam ctx name slot layout
        let (tail, finalLayout) :=
          lowerParams ctx rest nextLayout
        (head ++ tail, finalLayout)

def lowerReturns (ctx : Ctx) :
    List (Name × Nat) → Locals.Layout →
      List Locals.Stmt × Locals.Layout
  | [], layout => ([], layout)
  | (name, slot) :: rest, layout =>
      let (head, nextLayout) :=
        if isStackSlot ctx slot then
          ([Locals.Stmt.let_ name (.lit AllocationSupport.zeroWord)],
            name :: layout)
        else
          ([Locals.Stmt.expr
              (scratchStoreExpr ctx.frameName slot
                (.lit AllocationSupport.zeroWord))],
            layout)
      let (tail, finalLayout) :=
        lowerReturns ctx rest nextLayout
      (head ++ tail, finalLayout)

def lowerReturnExprs (ctx : Ctx) (state : State)
    (names : List Name) : Option (Locals.ExprSeq names.length) :=
  lowerExprSeq ctx state (Functions.Lower.returnExprs names)

def stackAssignTopCode? (layout : Locals.Layout)
    (remaining : Nat) (name : Name) : Option Structured.Code := do
  let depth ← Locals.Layout.lookupDepth? name layout
  let swap ← Locals.StackOp.swap? (remaining + depth)
  some
    [ Structured.BasicInstr.op swap,
      Structured.BasicInstr.op .pop ]

def scratchAssignTopCode? (ctx : Ctx) (state : State)
    (remaining slot : Nat) : Option Structured.Code := do
  let frameDepth ← frameDepth? ctx state
  AllocationSupport.storeTopSlotCode?
    (remaining + frameDepth + 1) slot

def lowerCallTargetsCode? (ctx : Ctx) (state : State) :
    List Name → Nat → Option Structured.Code
  | [], _valuesAbove => some []
  | name :: rest, valuesAbove => do
      let slot ←
        AllocationSupport.lookupSlot? name state.allocation.env
      let head ←
        if isStackSlot ctx slot then
          stackAssignTopCode? state.layout (valuesAbove - 1) name
        else
          scratchAssignTopCode? ctx state (valuesAbove - 1) slot
      let tail ←
        lowerCallTargetsCode? ctx state rest (valuesAbove - 1)
      some (head ++ tail)

def scopeRoot : ScopeId → ScopeId
  | .main => .main
  | .function name => .function name
  | .lexical parent _ => scopeRoot parent

def scopedStates
    (recipe : AllocationSupport.AllocationRecipe) :
    List AllocationSupport.ScopedAllocation :=
  { scope := .main, state := recipe.main } ::
    recipe.functions ++ recipe.lexicalScopes

def scratchBindingsForRoot
    (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (root : ScopeId) : List (Name × Nat) :=
  ((scopedStates recipe).filterMap fun entry =>
      if scopeRoot entry.scope = root then
        some
          (entry.state.env.filter fun binding =>
            binding.2 ∉ stackSlots)
      else
        none).flatten.eraseDups

def rootNeedsFrame (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (root : ScopeId) : Bool :=
  !(scratchBindingsForRoot recipe stackSlots root).isEmpty

def functionNeedsFrame (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (name : Name) : Bool :=
  rootNeedsFrame recipe stackSlots (.function name)

def frameFunctions (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) : List Name :=
  recipe.functionSlots.filterMap fun fn =>
    if functionNeedsFrame recipe stackSlots fn.name then
      some fn.name
    else
      none

mutual
  def lowerBlockOpen (ctx : Ctx) (returns : List Name)
      (state : State) (block : Block) :
      Option (Locals.Block × State) :=
    match block with
    | ⟨stmts⟩ => do
        let (lowered, final) ← lowerStmtList ctx returns state stmts
        some ({ stmts := lowered }, final)

  def lowerBlockScoped (ctx : Ctx) (returns : List Name)
      (state : State) (block : Block) :
      Option (Locals.Block × State) := do
    let (lowered, final) ← lowerBlockOpen ctx returns state block
    some
      (lowered,
        { allocation :=
            { env := state.allocation.env
              nextSlot := final.allocation.nextSlot }
          layout := state.layout })

  def lowerStmtList (ctx : Ctx) (returns : List Name)
      (state : State) :
      List Stmt → Option (List Locals.Stmt × State)
    | [] => some ([], state)
    | stmt :: rest => do
        let (head, next) ← lowerStmt ctx returns state stmt
        let (tail, final) ← lowerStmtList ctx returns next rest
        some (head ++ tail, final)

  def lowerCases (ctx : Ctx) (returns : List Name)
      (state : State) :
      List (Word × Block) →
        Option (List (Word × Locals.Block) × State)
    | [] => some ([], state)
    | (value, body) :: rest => do
        let (loweredBody, afterBody) ←
          lowerBlockScoped ctx returns state body
        let (loweredRest, final) ←
          lowerCases ctx returns afterBody rest
        some ((value, loweredBody) :: loweredRest, final)

  def lowerDefault (ctx : Ctx) (returns : List Name)
      (state : State) :
      Option Block → Option (Option Locals.Block × State)
    | none => some (none, state)
    | some body => do
        let (lowered, final) ← lowerBlockScoped ctx returns state body
        some (some lowered, final)

  def lowerStmt (ctx : Ctx) (returns : List Name)
      (state : State) :
      Stmt → Option (List Locals.Stmt × State)
    | .expr expr => do
        let lowered ← lowerExpr ctx state expr
        some ([.expr lowered], state)
    | .let_ name value => do
        let lowered ← lowerExpr ctx state value
        let (slot, allocation) :=
          AllocationSupport.allocateName name state.allocation
        if isStackSlot ctx slot then
          some
            ([.let_ name lowered],
              { allocation := allocation
                layout := name :: state.layout })
        else
          if ctx.frameName ∈ state.layout then
            some
              ([.expr (scratchStoreExpr ctx.frameName slot lowered)],
                { state with allocation := allocation })
          else
            none
    | .assign name value => do
        let slot ←
          AllocationSupport.lookupSlot? name state.allocation.env
        let lowered ← lowerExpr ctx state value
        if isStackSlot ctx slot then
          some ([.assign name lowered], state)
        else
          if ctx.frameName ∈ state.layout then
            some
              ([.expr (scratchStoreExpr ctx.frameName slot lowered)],
                state)
          else
            none
    | .block body => do
        let (lowered, final) ←
          lowerBlockScoped ctx returns state body
        some ([.block lowered], final)
    | .if_ cond body => do
        let loweredCond ← lowerExpr ctx state cond
        let (loweredBody, final) ←
          lowerBlockScoped ctx returns state body
        some ([.if_ loweredCond loweredBody], final)
    | .switch scrutinee cases defaultBody => do
        let loweredScrutinee ← lowerExpr ctx state scrutinee
        let (loweredCases, afterCases) ←
          lowerCases ctx returns state cases
        let (loweredDefault, final) ←
          lowerDefault ctx returns afterCases defaultBody
        some
          ([.switch loweredScrutinee loweredCases loweredDefault], final)
    | .for_ init cond post body => do
        let (loweredInit, loopState) ←
          lowerBlockOpen ctx returns state init
        let loweredCond ← lowerExpr ctx loopState cond
        let (loweredPost, afterPost) ←
          lowerBlockScoped ctx returns loopState post
        let (loweredBody, afterBody) ←
          lowerBlockScoped ctx returns afterPost body
        some
          ([.for_ loweredInit loweredCond loweredPost loweredBody],
            { allocation :=
                { env := state.allocation.env
                  nextSlot := afterBody.allocation.nextSlot }
              layout := state.layout })
    | .brk => some ([.brk], state)
    | .cont => some ([.cont], state)
    | .leave => do
        let values ← lowerReturnExprs ctx state returns
        some ([.exprs values, .leave], state)
    | .call targets functionName args => do
        let fn ← AllocationSupport.lookupFun? functionName ctx.functions
        if args.length = fn.params.length then pure () else none
        if targets.length = fn.returns.length then pure () else none
        if targets.Nodup then pure () else none
        let loweredArgs ← lowerExprList ctx state args
        let usesFrame := functionName ∈ ctx.frameFunctions
        let callArgs ←
          if usesFrame then do
            let frameConfig ← ctx.frameConfig?
            some (frameExpr frameConfig :: loweredArgs)
          else
            some loweredArgs
        let stores ←
          lowerCallTargetsCode? ctx state targets.reverse targets.length
        let release ←
          if usesFrame then do
            let frameConfig ← ctx.frameConfig?
            some
              [ .expr
                  (Locals.Expr.code (results := 0)
                    (AllocationSupport.scratchFrameReleaseCode frameConfig)) ]
          else
            some []
        some
          ([ .exprs (exprSeqOfList callArgs),
             .call functionName,
             .expr (Locals.Expr.code (results := 0) stores) ] ++ release,
           state)
    | .terminal kind => some ([.terminal kind], state)
    | .terminalArgs kind args => do
        let lowered ← lowerExprSeq ctx state args
        some ([.terminalArgs kind lowered], state)
end

/--
Successful lowering of a source `if` exposes only the adjacent expression and
scoped-block lowerers owned by this pass.
-/
theorem lowerStmt_if_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {cond : Expr 1} {body : Block}
    {loweredStmts : List Locals.Stmt}
    (hLower :
      lowerStmt ctx returns state (.if_ cond body) =
        some (loweredStmts, final)) :
    ∃ loweredCond loweredBody,
      lowerExpr ctx state cond = some loweredCond ∧
      lowerBlockScoped ctx returns state body =
        some (loweredBody, final) ∧
      loweredStmts = [.if_ loweredCond loweredBody] := by
  cases hCond : lowerExpr ctx state cond with
  | none =>
      simp [lowerStmt, hCond] at hLower
  | some loweredCond =>
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerStmt, hCond, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨loweredBody, bodyFinal⟩
          simp [lowerStmt, hCond, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨loweredCond, loweredBody, rfl, rfl, rfl⟩

/--
Successful lowering of a source `switch` exposes only the adjacent expression,
case-list, and default lowerers owned by this pass.
-/
theorem lowerStmt_switch_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {scrutinee : Expr 1}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {loweredStmts : List Locals.Stmt}
    (hLower :
      lowerStmt ctx returns state
          (.switch scrutinee cases defaultBody) =
        some (loweredStmts, final)) :
    ∃ loweredScrutinee loweredCases afterCases loweredDefault,
      lowerExpr ctx state scrutinee = some loweredScrutinee ∧
      lowerCases ctx returns state cases =
        some (loweredCases, afterCases) ∧
      lowerDefault ctx returns afterCases defaultBody =
        some (loweredDefault, final) ∧
      loweredStmts =
        [.switch loweredScrutinee loweredCases loweredDefault] := by
  cases hScrutinee : lowerExpr ctx state scrutinee with
  | none =>
      simp [lowerStmt, hScrutinee] at hLower
  | some loweredScrutinee =>
      cases hCases : lowerCases ctx returns state cases with
      | none =>
          simp [lowerStmt, hScrutinee, hCases] at hLower
      | some casesResult =>
          rcases casesResult with ⟨loweredCases, afterCases⟩
          cases hDefault :
              lowerDefault ctx returns afterCases defaultBody with
          | none =>
              simp [lowerStmt, hScrutinee, hCases, hDefault] at hLower
          | some defaultResult =>
              rcases defaultResult with ⟨loweredDefault, defaultFinal⟩
              simp [lowerStmt, hScrutinee, hCases, hDefault] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                ⟨loweredScrutinee, loweredCases, afterCases,
                  loweredDefault, rfl, rfl, hDefault, rfl⟩

/--
Successful lowering of a source `for` exposes the adjacent initializer,
condition, post, and body lowerers plus the common restored outer state.
-/
theorem lowerStmt_for_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {init : Block} {cond : Expr 1} {post body : Block}
    {loweredStmts : List Locals.Stmt}
    (hLower :
      lowerStmt ctx returns state (.for_ init cond post body) =
        some (loweredStmts, final)) :
    ∃ loweredInit loopState loweredCond loweredPost afterPost
        loweredBody afterBody,
      lowerBlockOpen ctx returns state init =
        some (loweredInit, loopState) ∧
      lowerExpr ctx loopState cond = some loweredCond ∧
      lowerBlockScoped ctx returns loopState post =
        some (loweredPost, afterPost) ∧
      lowerBlockScoped ctx returns afterPost body =
        some (loweredBody, afterBody) ∧
      loweredStmts =
        [.for_ loweredInit loweredCond loweredPost loweredBody] ∧
      final =
        { allocation :=
            { env := state.allocation.env
              nextSlot := afterBody.allocation.nextSlot }
          layout := state.layout } := by
  cases hInit : lowerBlockOpen ctx returns state init with
  | none =>
      simp [lowerStmt, hInit] at hLower
  | some initResult =>
      rcases initResult with ⟨loweredInit, loopState⟩
      cases hCond : lowerExpr ctx loopState cond with
      | none =>
          simp [lowerStmt, hInit, hCond] at hLower
      | some loweredCond =>
          cases hPost : lowerBlockScoped ctx returns loopState post with
          | none =>
              simp [lowerStmt, hInit, hCond, hPost] at hLower
          | some postResult =>
              rcases postResult with ⟨loweredPost, afterPost⟩
              cases hBody :
                  lowerBlockScoped ctx returns afterPost body with
              | none =>
                  simp [lowerStmt, hInit, hCond, hPost, hBody] at hLower
              | some bodyResult =>
                  rcases bodyResult with ⟨loweredBody, afterBody⟩
                  simp [lowerStmt, hInit, hCond, hPost, hBody] at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  exact
                    ⟨loweredInit, loopState, loweredCond,
                      loweredPost, afterPost, loweredBody, afterBody,
                      rfl, hCond, hPost, hBody, rfl, rfl⟩

/--
Successful call lowering exposes the source function lookup, arity checks,
argument lowering, return stores, and optional scratch-frame protocol.
-/
theorem lowerStmt_call_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {targets : List Name} {functionName : Name}
    {args : List (Expr 1)}
    {loweredStmts : List Locals.Stmt}
    (hLower :
      lowerStmt ctx returns state (.call targets functionName args) =
        some (loweredStmts, final)) :
    ∃ fn loweredArgs callArgs stores release,
      AllocationSupport.lookupFun? functionName ctx.functions = some fn ∧
      args.length = fn.params.length ∧
      targets.length = fn.returns.length ∧
      targets.Nodup ∧
      lowerExprList ctx state args = some loweredArgs ∧
      (if functionName ∈ ctx.frameFunctions then do
          let frameConfig ← ctx.frameConfig?
          some (frameExpr frameConfig :: loweredArgs)
        else
          some loweredArgs) =
        some callArgs ∧
      lowerCallTargetsCode? ctx state targets.reverse targets.length =
        some stores ∧
      (if functionName ∈ ctx.frameFunctions then do
          let frameConfig ← ctx.frameConfig?
          some
            [ .expr
                (Locals.Expr.code (results := 0)
                  (AllocationSupport.scratchFrameReleaseCode frameConfig)) ]
        else
          some []) =
        some release ∧
      loweredStmts =
        ([ .exprs (exprSeqOfList callArgs),
           .call functionName,
           .expr (Locals.Expr.code (results := 0) stores) ] ++ release) ∧
      final = state := by
  cases hFind :
      AllocationSupport.lookupFun? functionName ctx.functions with
  | none =>
      simp [lowerStmt, hFind] at hLower
  | some fn =>
      by_cases hArgsLength : args.length = fn.params.length
      · by_cases hTargetsLength : targets.length = fn.returns.length
        · by_cases hTargets : targets.Nodup
          · cases hArgs : lowerExprList ctx state args with
            | none =>
                simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
                  hTargets, hArgs] at hLower
            | some loweredArgs =>
                by_cases hFrame :
                    functionName ∈ ctx.frameFunctions
                · cases hConfig : ctx.frameConfig? with
                  | none =>
                      simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
                        hTargets, hArgs, hFrame, hConfig] at hLower
                  | some frameConfig =>
                      cases hStores :
                          lowerCallTargetsCode? ctx state targets.reverse
                            fn.returns.length with
                      | none =>
                          simp [lowerStmt, hFind, hArgsLength,
                            hTargetsLength, hTargets, hArgs, hFrame,
                            hConfig, hStores] at hLower
                      | some stores =>
                          simp [lowerStmt, hFind, hArgsLength,
                            hTargetsLength, hTargets, hArgs, hFrame,
                            hConfig, hStores] at hLower
                          rcases hLower with ⟨rfl, rfl⟩
                          exact
                            ⟨fn, loweredArgs,
                              frameExpr frameConfig :: loweredArgs, stores,
                              [ .expr
                                  (Locals.Expr.code (results := 0)
                                    (AllocationSupport.scratchFrameReleaseCode
                                      frameConfig)) ],
                              rfl, hArgsLength, hTargetsLength, hTargets,
                              rfl, by simp [hFrame],
                              by simpa [hTargetsLength] using hStores,
                              by simp [hFrame], rfl, rfl⟩
                · cases hStores :
                      lowerCallTargetsCode? ctx state targets.reverse
                        fn.returns.length with
                  | none =>
                      simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
                        hTargets, hArgs, hFrame, hStores] at hLower
                  | some stores =>
                      simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
                        hTargets, hArgs, hFrame, hStores] at hLower
                      rcases hLower with ⟨rfl, rfl⟩
                      exact
                        ⟨fn, loweredArgs, loweredArgs, stores, [],
                          rfl, hArgsLength, hTargetsLength, hTargets,
                          rfl, by simp [hFrame],
                          by simpa [hTargetsLength] using hStores,
                          by simp [hFrame], rfl, rfl⟩
          · simp [lowerStmt, hFind, hArgsLength, hTargetsLength,
              hTargets] at hLower
        · simp [lowerStmt, hFind, hArgsLength, hTargetsLength] at hLower
      · simp [lowerStmt, hFind, hArgsLength] at hLower

/--
Case/default lowering preserves the absence of a selected source branch.
-/
theorem lowerSwitch_select_none
    {ctx : Ctx} {returns : List Name}
    {state afterCases final : State}
    {value : Word}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {loweredCases : List (Word × Locals.Block)}
    {loweredDefault : Option Locals.Block}
    (hCases :
      lowerCases ctx returns state cases =
        some (loweredCases, afterCases))
    (hDefault :
      lowerDefault ctx returns afterCases defaultBody =
        some (loweredDefault, final))
    (hSelect :
      Source.Switch.select value cases defaultBody = none) :
    Locals.Source.Switch.select value loweredCases loweredDefault = none := by
  induction cases generalizing state afterCases loweredCases with
  | nil =>
      simp [lowerCases] at hCases
      rcases hCases with ⟨rfl, rfl⟩
      cases defaultBody with
      | none =>
          simp [lowerDefault] at hDefault
          rcases hDefault with ⟨rfl, rfl⟩
          rfl
      | some body =>
          simp [Source.Switch.select] at hSelect
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerCases, hBody] at hCases
      | some bodyResult =>
          rcases bodyResult with ⟨loweredBody, afterBody⟩
          cases hRest :
              lowerCases ctx returns afterBody rest with
          | none =>
              simp [lowerCases, hBody, hRest] at hCases
          | some restResult =>
              rcases restResult with ⟨loweredRest, restFinal⟩
              simp [lowerCases, hBody, hRest] at hCases
              rcases hCases with ⟨rfl, rfl⟩
              by_cases hMatch : caseValue = value
              · simp [Source.Switch.select, hMatch] at hSelect
              · have hTailSelect :
                    Source.Switch.select
                        value rest defaultBody =
                      none := by
                  simpa [Source.Switch.select, hMatch] using hSelect
                have hLoweredTail :=
                  ih hRest hDefault hTailSelect
                simpa [Locals.Source.Switch.select, hMatch] using
                  hLoweredTail

/--
Case/default lowering preserves a selected source branch and exposes the
ordinary scoped-body lowering that produced its Locals counterpart.

Earlier unselected cases may advance the fresh-slot cursor, but scoped lowering
preserves the incoming allocation environment and concrete layout. Those are
the only lowering-state components needed to transport a statement-boundary
activation invariant to the selected body.
-/
theorem lowerSwitch_select_some
    {ctx : Ctx} {returns : List Name}
    {state afterCases final : State}
    {value : Word}
    {cases : List (Word × Block)}
    {defaultBody : Option Block}
    {selected : Block}
    {loweredCases : List (Word × Locals.Block)}
    {loweredDefault : Option Locals.Block}
    (hCases :
      lowerCases ctx returns state cases =
        some (loweredCases, afterCases))
    (hDefault :
      lowerDefault ctx returns afterCases defaultBody =
        some (loweredDefault, final))
    (hSelect :
      Source.Switch.select value cases defaultBody = some selected) :
    ∃ selectedLowered selectedStart selectedFinal,
      Locals.Source.Switch.select value loweredCases loweredDefault =
          some selectedLowered ∧
        lowerBlockScoped ctx returns selectedStart selected =
          some (selectedLowered, selectedFinal) ∧
        selectedStart.allocation.env = state.allocation.env ∧
        selectedStart.layout = state.layout := by
  induction cases generalizing state afterCases loweredCases with
  | nil =>
      simp [lowerCases] at hCases
      rcases hCases with ⟨rfl, rfl⟩
      cases defaultBody with
      | none =>
          simp [Source.Switch.select] at hSelect
      | some body =>
          simp [Source.Switch.select] at hSelect
          subst selected
          cases hBody :
              lowerBlockScoped ctx returns state body with
          | none =>
              simp [lowerDefault, hBody] at hDefault
          | some bodyResult =>
              rcases bodyResult with ⟨loweredBody, bodyFinal⟩
              simp [lowerDefault, hBody] at hDefault
              rcases hDefault with ⟨rfl, rfl⟩
              exact
                ⟨loweredBody, state, bodyFinal,
                  rfl, hBody, rfl, rfl⟩
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerCases, hBody] at hCases
      | some bodyResult =>
          rcases bodyResult with ⟨loweredBody, afterBody⟩
          cases hRest :
              lowerCases ctx returns afterBody rest with
          | none =>
              simp [lowerCases, hBody, hRest] at hCases
          | some restResult =>
              rcases restResult with ⟨loweredRest, restFinal⟩
              simp [lowerCases, hBody, hRest] at hCases
              rcases hCases with ⟨rfl, rfl⟩
              by_cases hMatch : caseValue = value
              · simp [Source.Switch.select, hMatch] at hSelect
                subst selected
                exact
                  ⟨loweredBody, state, afterBody,
                    by simp [Locals.Source.Switch.select, hMatch],
                    hBody, rfl, rfl⟩
              · have hTailSelect :
                    Source.Switch.select value rest defaultBody =
                      some selected := by
                  simpa [Source.Switch.select, hMatch] using hSelect
                obtain
                    ⟨selectedLowered, selectedStart, selectedFinal,
                      hLoweredSelect, hSelectedBody,
                      hSelectedEnv, hSelectedLayout⟩ :=
                  ih hRest hDefault hTailSelect
                have hBodyShape :
                    afterBody.allocation.env =
                        state.allocation.env ∧
                      afterBody.layout = state.layout := by
                  unfold lowerBlockScoped at hBody
                  cases hOpen :
                      lowerBlockOpen ctx returns state body with
                  | none =>
                      simp [hOpen] at hBody
                  | some openResult =>
                      rcases openResult with
                        ⟨loweredOpen, openFinal⟩
                      simp [hOpen] at hBody
                      rcases hBody with ⟨rfl, rfl⟩
                      exact ⟨rfl, rfl⟩
                exact
                  ⟨selectedLowered, selectedStart, selectedFinal,
                    by
                      simpa [Locals.Source.Switch.select, hMatch] using
                        hLoweredSelect,
                    hSelectedBody,
                    hSelectedEnv.trans hBodyShape.1,
                    hSelectedLayout.trans hBodyShape.2⟩

/--
The part of lowering-state evolution visible at an open source-block boundary.

New stack locals form a removable prefix of the incoming Locals layout, while
lookups for names already in the source scope retain their allocation slots.
-/
def StateExtends
    (live : List Name) (before after : State) : Prop :=
  ∃ dropped : List Name,
    after.layout = dropped ++ before.layout ∧
      (∀ name, name ∈ dropped → name ∉ live) ∧
      ∀ name,
        name ∈ live →
        AllocationSupport.lookupSlot? name after.allocation.env =
          AllocationSupport.lookupSlot? name before.allocation.env

namespace StateExtends

theorem of_shape
    {live : List Name} {before after : State}
    (hLayout : after.layout = before.layout)
    (hSlots : after.allocation.env = before.allocation.env) :
    StateExtends live before after := by
  refine ⟨[], by simpa using hLayout, ?_, ?_⟩
  · simp
  · intro name _hLive
    rw [hSlots]

theorem trans
    {beforeLive afterLive : List Name}
    {before middle after : State}
    (hHead : StateExtends beforeLive before middle)
    (hTail : StateExtends afterLive middle after)
    (hSubset : ∀ name, name ∈ beforeLive → name ∈ afterLive) :
    StateExtends beforeLive before after := by
  rcases hHead with
    ⟨headDropped, hHeadLayout, hHeadFresh, hHeadSlots⟩
  rcases hTail with
    ⟨tailDropped, hTailLayout, hTailFresh, hTailSlots⟩
  refine
    ⟨tailDropped ++ headDropped, ?_, ?_, ?_⟩
  · rw [hTailLayout, hHeadLayout, List.append_assoc]
  · intro name hDropped hLive
    simp only [List.mem_append] at hDropped
    cases hDropped with
    | inl hTailDropped =>
        exact hTailFresh name hTailDropped (hSubset name hLive)
    | inr hHeadDropped =>
        exact hHeadFresh name hHeadDropped hLive
  · intro name hLive
    exact (hTailSlots name (hSubset name hLive)).trans
      (hHeadSlots name hLive)

end StateExtends

theorem lowerBlockScoped_state_shape
    {ctx : Ctx} {returns : List Name}
    {state final : State} {block : Block}
    {lowered : Locals.Block}
    (hLower :
      lowerBlockScoped ctx returns state block =
        some (lowered, final)) :
    final.allocation.env = state.allocation.env ∧
      final.layout = state.layout := by
  unfold lowerBlockScoped at hLower
  cases hOpen : lowerBlockOpen ctx returns state block with
  | none =>
      simp [hOpen] at hLower
  | some result =>
      rcases result with ⟨body, bodyFinal⟩
      simp [hOpen] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

/--
Successful scoped lowering exposes its ordinary open-block lowering state.
The scoped result restores the incoming environment and layout while retaining
only the fresh-slot cursor reached by the open body.
-/
theorem lowerBlockScoped_components
    {ctx : Ctx} {returns : List Name}
    {state final : State} {block : Block}
    {lowered : Locals.Block}
    (hLower :
      lowerBlockScoped ctx returns state block =
        some (lowered, final)) :
    ∃ openFinal,
      lowerBlockOpen ctx returns state block =
        some (lowered, openFinal) ∧
      final.allocation.env = state.allocation.env ∧
      final.allocation.nextSlot = openFinal.allocation.nextSlot ∧
      final.layout = state.layout := by
  unfold lowerBlockScoped at hLower
  cases hOpen : lowerBlockOpen ctx returns state block with
  | none =>
      simp [hOpen] at hLower
  | some result =>
      rcases result with ⟨body, bodyFinal⟩
      simp [hOpen] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨bodyFinal, rfl, rfl, rfl, rfl⟩

theorem lowerCases_state_shape
    {ctx : Ctx} {returns : List Name} :
    ∀ {state final : State}
      {cases : List (Word × Block)}
      {lowered : List (Word × Locals.Block)},
      lowerCases ctx returns state cases = some (lowered, final) →
        final.allocation.env = state.allocation.env ∧
          final.layout = state.layout := by
  intro state final cases lowered hLower
  induction cases generalizing state final lowered with
  | nil =>
      simp [lowerCases] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | cons head rest ih =>
      rcases head with ⟨value, body⟩
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerCases, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨loweredBody, afterBody⟩
          cases hRest :
              lowerCases ctx returns afterBody rest with
          | none =>
              simp [lowerCases, hBody, hRest] at hLower
          | some restResult =>
              rcases restResult with ⟨loweredRest, restFinal⟩
              simp [lowerCases, hBody, hRest] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hBodyShape :=
                lowerBlockScoped_state_shape hBody
              have hRestShape := ih hRest
              exact
                ⟨hRestShape.1.trans hBodyShape.1,
                  hRestShape.2.trans hBodyShape.2⟩

theorem lowerDefault_state_shape
    {ctx : Ctx} {returns : List Name}
    {state final : State} {body : Option Block}
    {lowered : Option Locals.Block}
    (hLower :
      lowerDefault ctx returns state body =
        some (lowered, final)) :
    final.allocation.env = state.allocation.env ∧
      final.layout = state.layout := by
  cases body with
  | none =>
      simp [lowerDefault] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | some body =>
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerDefault, hBody] at hLower
      | some result =>
          rcases result with ⟨loweredBody, bodyFinal⟩
          simp [lowerDefault, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact lowerBlockScoped_state_shape hBody

theorem mem_stmt_outEnv
    {live : List Name} {stmt : Stmt} {name : Name}
    (hLive : name ∈ live) :
    name ∈ Scope.Stmt.outEnv live stmt := by
  cases stmt <;> simp [Scope.Stmt.outEnv, hLive]

/--
Successful lowering of one well-scoped statement preserves incoming allocation
slots and extends the Locals layout only by stack declarations introduced by
that statement.
-/
theorem lowerStmt_stateExtends
    {ctx : Ctx} {returns live : List Name}
    {state final : State} {stmt : Stmt}
    {lowered : List Locals.Stmt}
    (hScoped : Scope.Stmt.Scoped live stmt)
    (hLower :
      lowerStmt ctx returns state stmt =
        some (lowered, final)) :
    StateExtends live state final := by
  cases stmt with
  | expr expr =>
      cases hExpr : lowerExpr ctx state expr with
      | none =>
          simp [lowerStmt, hExpr] at hLower
      | some loweredExpr =>
          simp [lowerStmt, hExpr] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact StateExtends.of_shape rfl rfl
  | let_ name value =>
      have hFresh : name ∉ live := hScoped.1
      cases hValue : lowerExpr ctx state value with
      | none =>
          simp [lowerStmt, hValue] at hLower
      | some loweredValue =>
          by_cases hStack :
              isStackSlot ctx state.allocation.nextSlot = true
          · simp [lowerStmt, hValue, AllocationSupport.allocateName,
              hStack] at hLower
            rcases hLower with ⟨rfl, rfl⟩
            refine ⟨[name], rfl, ?_, ?_⟩
            · intro declared hDeclared
              simp only [List.mem_singleton] at hDeclared
              subst declared
              exact hFresh
            · intro existing hExisting
              have hNe : name ≠ existing := by
                intro hEq
                subst existing
                exact hFresh hExisting
              simp [AllocationSupport.lookupSlot?, hNe]
          · have hStackFalse :
                isStackSlot ctx state.allocation.nextSlot = false :=
              Bool.eq_false_of_not_eq_true hStack
            by_cases hFrame : ctx.frameName ∈ state.layout
            · simp [lowerStmt, hValue, AllocationSupport.allocateName,
                hStackFalse, hFrame] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              refine ⟨[], rfl, ?_, ?_⟩
              · simp
              · intro existing hExisting
                have hNe : name ≠ existing := by
                  intro hEq
                  subst existing
                  exact hFresh hExisting
                simp [AllocationSupport.lookupSlot?, hNe]
            · simp [lowerStmt, hValue, AllocationSupport.allocateName,
                hStackFalse, hFrame] at hLower
  | assign name value =>
      cases hSlot :
          AllocationSupport.lookupSlot?
            name state.allocation.env with
      | none =>
          simp [lowerStmt, hSlot] at hLower
      | some slot =>
          cases hValue : lowerExpr ctx state value with
          | none =>
              simp [lowerStmt, hSlot, hValue] at hLower
          | some loweredValue =>
              by_cases hStack : isStackSlot ctx slot = true
              · simp [lowerStmt, hSlot, hValue, hStack] at hLower
                rcases hLower with ⟨rfl, rfl⟩
                exact StateExtends.of_shape rfl rfl
              · have hStackFalse :
                    isStackSlot ctx slot = false :=
                  Bool.eq_false_of_not_eq_true hStack
                by_cases hFrame : ctx.frameName ∈ state.layout
                · simp [lowerStmt, hSlot, hValue, hStackFalse, hFrame]
                    at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  exact StateExtends.of_shape rfl rfl
                · simp [lowerStmt, hSlot, hValue, hStackFalse, hFrame]
                    at hLower
  | block body =>
      cases hBody :
          lowerBlockScoped ctx returns state body with
      | none =>
          simp [lowerStmt, hBody] at hLower
      | some result =>
          rcases result with ⟨loweredBody, bodyFinal⟩
          simp [lowerStmt, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          have hShape := lowerBlockScoped_state_shape hBody
          exact StateExtends.of_shape hShape.2 hShape.1
  | if_ cond body =>
      cases hCond : lowerExpr ctx state cond with
      | none =>
          simp [lowerStmt, hCond] at hLower
      | some loweredCond =>
          cases hBody :
              lowerBlockScoped ctx returns state body with
          | none =>
              simp [lowerStmt, hCond, hBody] at hLower
          | some result =>
              rcases result with ⟨loweredBody, bodyFinal⟩
              simp [lowerStmt, hCond, hBody] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hShape := lowerBlockScoped_state_shape hBody
              exact StateExtends.of_shape hShape.2 hShape.1
  | switch scrutinee cases defaultBody =>
      cases hScrutinee : lowerExpr ctx state scrutinee with
      | none =>
          simp [lowerStmt, hScrutinee] at hLower
      | some loweredScrutinee =>
          cases hCases :
              lowerCases ctx returns state cases with
          | none =>
              simp [lowerStmt, hScrutinee, hCases] at hLower
          | some casesResult =>
              rcases casesResult with ⟨loweredCases, afterCases⟩
              cases hDefault :
                  lowerDefault ctx returns afterCases defaultBody with
              | none =>
                  simp [lowerStmt, hScrutinee, hCases, hDefault] at hLower
              | some defaultResult =>
                  rcases defaultResult with
                    ⟨loweredDefault, defaultFinal⟩
                  simp [lowerStmt, hScrutinee, hCases, hDefault] at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  have hCasesShape := lowerCases_state_shape hCases
                  have hDefaultShape :=
                    lowerDefault_state_shape hDefault
                  exact
                    StateExtends.of_shape
                      (hDefaultShape.2.trans hCasesShape.2)
                      (hDefaultShape.1.trans hCasesShape.1)
  | for_ init cond post body =>
      cases hInit :
          lowerBlockOpen ctx returns state init with
      | none =>
          simp [lowerStmt, hInit] at hLower
      | some initResult =>
          rcases initResult with ⟨loweredInit, loopState⟩
          cases hCond : lowerExpr ctx loopState cond with
          | none =>
              simp [lowerStmt, hInit, hCond] at hLower
          | some loweredCond =>
              cases hPost :
                  lowerBlockScoped ctx returns loopState post with
              | none =>
                  simp [lowerStmt, hInit, hCond, hPost] at hLower
              | some postResult =>
                  rcases postResult with ⟨loweredPost, afterPost⟩
                  cases hBody :
                      lowerBlockScoped ctx returns afterPost body with
                  | none =>
                      simp [lowerStmt, hInit, hCond, hPost, hBody] at hLower
                  | some bodyResult =>
                      rcases bodyResult with ⟨loweredBody, afterBody⟩
                      simp [lowerStmt, hInit, hCond, hPost, hBody] at hLower
                      rcases hLower with ⟨rfl, rfl⟩
                      exact StateExtends.of_shape rfl rfl
  | brk =>
      simp [lowerStmt] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact StateExtends.of_shape rfl rfl
  | cont =>
      simp [lowerStmt] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact StateExtends.of_shape rfl rfl
  | leave =>
      cases hValues :
          lowerReturnExprs ctx state returns with
      | none =>
          simp [lowerStmt, hValues] at hLower
      | some values =>
          simp [lowerStmt, hValues] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact StateExtends.of_shape rfl rfl
  | call targets functionName args =>
      cases hFunction :
          AllocationSupport.lookupFun?
            functionName ctx.functions with
      | none =>
          simp [lowerStmt, hFunction] at hLower
      | some fn =>
          by_cases hArgsLength : args.length = fn.params.length
          · by_cases hTargetsLength :
                targets.length = fn.returns.length
            · by_cases hTargetsNodup : targets.Nodup
              · cases hArgs :
                    lowerExprList ctx state args with
                | none =>
                    simp [lowerStmt, hFunction, hArgsLength,
                      hTargetsLength, hTargetsNodup, hArgs] at hLower
                | some loweredArgs =>
                    by_cases hUsesFrame :
                        functionName ∈ ctx.frameFunctions
                    · cases hConfig : ctx.frameConfig? with
                      | none =>
                          simp [lowerStmt, hFunction, hArgsLength,
                            hTargetsLength, hTargetsNodup, hArgs,
                            hUsesFrame, hConfig] at hLower
                      | some frameConfig =>
                          cases hStores :
                              lowerCallTargetsCode? ctx state
                                targets.reverse targets.length with
                          | none =>
                              have hStores' :
                                  lowerCallTargetsCode? ctx state
                                      targets.reverse fn.returns.length =
                                    none := by
                                simpa [hTargetsLength] using hStores
                              simp [lowerStmt, hFunction, hArgsLength,
                                hTargetsLength, hTargetsNodup, hArgs,
                                hUsesFrame, hConfig, hStores'] at hLower
                          | some stores =>
                              have hStores' :
                                  lowerCallTargetsCode? ctx state
                                      targets.reverse fn.returns.length =
                                    some stores := by
                                simpa [hTargetsLength] using hStores
                              simp [lowerStmt, hFunction, hArgsLength,
                                hTargetsLength, hTargetsNodup, hArgs,
                                hUsesFrame, hConfig, hStores'] at hLower
                              rcases hLower with ⟨rfl, rfl⟩
                              exact StateExtends.of_shape rfl rfl
                    · cases hStores :
                          lowerCallTargetsCode? ctx state
                            targets.reverse targets.length with
                      | none =>
                          have hStores' :
                              lowerCallTargetsCode? ctx state
                                  targets.reverse fn.returns.length =
                                none := by
                            simpa [hTargetsLength] using hStores
                          simp [lowerStmt, hFunction, hArgsLength,
                            hTargetsLength, hTargetsNodup, hArgs,
                            hUsesFrame, hStores'] at hLower
                      | some stores =>
                          have hStores' :
                              lowerCallTargetsCode? ctx state
                                  targets.reverse fn.returns.length =
                                some stores := by
                            simpa [hTargetsLength] using hStores
                          simp [lowerStmt, hFunction, hArgsLength,
                            hTargetsLength, hTargetsNodup, hArgs,
                            hUsesFrame, hStores'] at hLower
                          rcases hLower with ⟨rfl, rfl⟩
                          exact StateExtends.of_shape rfl rfl
              · simp [lowerStmt, hFunction, hArgsLength,
                  hTargetsLength, hTargetsNodup] at hLower
            · simp [lowerStmt, hFunction, hArgsLength,
                hTargetsLength] at hLower
          · simp [lowerStmt, hFunction, hArgsLength] at hLower
  | terminal kind =>
      simp [lowerStmt] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact StateExtends.of_shape rfl rfl
  | terminalArgs kind args =>
      cases hArgs : lowerExprSeq ctx state args with
      | none =>
          simp [lowerStmt, hArgs] at hLower
      | some loweredArgs =>
          simp [lowerStmt, hArgs] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact StateExtends.of_shape rfl rfl

/--
Successful lowering of a well-scoped statement list preserves every incoming
allocation slot and records the exact removable stack-local prefix.
-/
theorem lowerStmtList_stateExtends
    {ctx : Ctx} {returns live : List Name}
    {state final : State} {stmts : List Stmt}
    {lowered : List Locals.Stmt}
    (hScoped : Scope.StmtList.Scoped live stmts)
    (hLower :
      lowerStmtList ctx returns state stmts =
        some (lowered, final)) :
    StateExtends live state final := by
  induction stmts generalizing live state final lowered with
  | nil =>
      simp [lowerStmtList] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact StateExtends.of_shape rfl rfl
  | cons stmt rest ih =>
      have hHeadScoped : Scope.Stmt.Scoped live stmt := hScoped.1
      have hTailScoped :
          Scope.StmtList.Scoped (Scope.Stmt.outEnv live stmt) rest :=
        hScoped.2
      cases hHead :
          lowerStmt ctx returns state stmt with
      | none =>
          simp [lowerStmtList, hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, next⟩
          cases hTail :
              lowerStmtList ctx returns next rest with
          | none =>
              simp [lowerStmtList, hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailFinal⟩
              simp [lowerStmtList, hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                (lowerStmt_stateExtends hHeadScoped hHead).trans
                  (ih hTailScoped hTail)
                  (fun name hLive => mem_stmt_outEnv hLive)

/--
The real open-block lowerer supplies the lexical layout and slot facts consumed
by observer-preserving cleanup.
-/
theorem lowerBlockOpen_stateExtends
    {ctx : Ctx} {returns live : List Name}
    {state final : State} {block : Block}
    {lowered : Locals.Block}
    (hScoped : Scope.Block.Scoped live block)
    (hLower :
      lowerBlockOpen ctx returns state block =
        some (lowered, final)) :
    StateExtends live state final := by
  rcases block with ⟨stmts⟩
  cases hList :
      lowerStmtList ctx returns state stmts with
  | none =>
      simp [lowerBlockOpen, hList] at hLower
  | some result =>
      rcases result with ⟨loweredStmts, listFinal⟩
      simp [lowerBlockOpen, hList] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact lowerStmtList_stateExtends hScoped hList

/--
Successful open-block lowering of a nonempty block decomposes through the
ordinary statement lowerer and the recursively lowered tail.
-/
theorem lowerBlockOpen_cons_components
    {ctx : Ctx} {returns : List Name}
    {state final : State}
    {stmt : Stmt} {rest : List Stmt}
    {lowered : Locals.Block}
    (hLower :
      lowerBlockOpen ctx returns state { stmts := stmt :: rest } =
        some (lowered, final)) :
    ∃ head next tail,
      lowerStmt ctx returns state stmt = some (head, next) ∧
      lowerBlockOpen ctx returns next { stmts := rest } =
        some ({ stmts := tail }, final) ∧
      lowered.stmts = head ++ tail := by
  cases hHead : lowerStmt ctx returns state stmt with
  | none =>
      simp [lowerBlockOpen, lowerStmtList, hHead] at hLower
  | some headResult =>
      rcases headResult with ⟨head, next⟩
      cases hTail :
          lowerStmtList ctx returns next rest with
      | none =>
          simp [lowerBlockOpen, lowerStmtList, hHead, hTail] at hLower
      | some tailResult =>
          rcases tailResult with ⟨tail, tailFinal⟩
          simp [lowerBlockOpen, lowerStmtList, hHead, hTail] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact
            ⟨head, next, tail, rfl,
              by simp [lowerBlockOpen, hTail], rfl⟩

def lowerFunction? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig)
    (state : AllocationSupport.CompileState) (fn : FunDef) :
    Option (Locals.Proc × AllocationSupport.CompileState) := do
  let slots ← AllocationSupport.lookupFun? fn.name recipe.functionSlots
  let root := ScopeId.function fn.name
  let scratchBindings :=
    scratchBindingsForRoot recipe stackSlots root
  let needsFrame := !scratchBindings.isEmpty
  let entryLayout :=
    fn.params.reverse ++ if needsFrame then [frameName] else []
  let ctx : Ctx :=
    { functions := recipe.functionSlots
      frameConfig? := frameConfig?
      frameName := frameName
      stackSlots := stackSlots
      root := root
      scratchBindings := scratchBindings
      frameFunctions := frameFunctions recipe stackSlots }
  let markers :=
    [bindEntryLayout entryLayout] ++
      if needsFrame then
        [bindScratchBindings fn.params.length scratchBindings]
      else
        []
  let (paramPrelude, paramLayout) :=
    lowerParams ctx slots.params entryLayout
  let (returnPrelude, bodyLayout) :=
    lowerReturns ctx slots.returns paramLayout
  let bodyStart : State :=
    { allocation :=
        { env := AllocationSupport.functionEnv slots
          nextSlot := state.nextSlot }
      layout := bodyLayout }
  let (body, final) ←
    lowerBlockOpen ctx fn.returns bodyStart fn.body
  let returnValues ← lowerReturnExprs ctx final fn.returns
  let fullBody : Locals.Block :=
    { stmts :=
        markers ++ paramPrelude ++ returnPrelude ++ body.stmts ++
          [.exprs returnValues] }
  some
    ({ name := fn.name
       argc := fn.params.length + if needsFrame then 1 else 0
       retc := fn.returns.length
       entryLayout := entryLayout
       body := fullBody },
     { env := state.env
       nextSlot := final.allocation.nextSlot })

def lowerFunctions? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig) :
    AllocationSupport.CompileState → List FunDef →
      Option (List Locals.Proc × AllocationSupport.CompileState)
  | state, [] => some ([], state)
  | state, fn :: rest => do
      let (proc, next) ←
        lowerFunction? recipe stackSlots frameName frameConfig? state fn
      let (tail, final) ←
        lowerFunctions? recipe stackSlots frameName frameConfig? next rest
      some (proc :: tail, final)

def lowerMain? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (frameConfig? : Option AllocationSupport.ScratchFrameConfig)
    (state : AllocationSupport.CompileState)
    (body : Block) : Option (Locals.Block × State) := do
  let root := ScopeId.main
  let scratchBindings :=
    scratchBindingsForRoot recipe stackSlots root
  let needsFrame := !scratchBindings.isEmpty
  let ctx : Ctx :=
    { functions := recipe.functionSlots
      frameConfig? := frameConfig?
      frameName := frameName
      stackSlots := stackSlots
      root := root
      scratchBindings := scratchBindings
      frameFunctions := frameFunctions recipe stackSlots }
  let needsAllocator :=
    needsFrame || !(frameFunctions recipe stackSlots).isEmpty
  let allocatorPrelude ←
    if needsAllocator then do
      let frameConfig ← frameConfig?
      some
        [ .expr
            (Locals.Expr.code (results := 0)
              (AllocationSupport.scratchAllocatorInitCode frameConfig)) ]
    else
      some []
  let framePrelude ←
    if needsFrame then do
      let frameConfig ← frameConfig?
      some
        [ Locals.Stmt.let_ frameName (frameExpr frameConfig),
          bindScratchBindings 0 scratchBindings ]
    else
      some []
  let prelude := allocatorPrelude ++ framePrelude
  let start : State :=
    { allocation := state
      layout := if needsFrame then [frameName] else [] }
  let (sourcePrelude, rest) := splitPrelude body.stmts
  let (lowered, final) ←
    lowerBlockOpen ctx [] start { stmts := rest }
  some
    ({ stmts := sourcePrelude ++ prelude ++ lowered.stmts },
      final)

def lowerToLocals? (recipe : AllocationSupport.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (program : Program) : Option Locals.Program := do
  let frameConfig? :=
    AllocationSupport.scratchFrameConfig?
      program.memoryContract recipe.frameWords
  let (procs, stateAfterFunctions) ←
    lowerFunctions? recipe stackSlots frameName frameConfig?
      recipe.stateAfterSignatures program.functions
  if stateAfterFunctions = recipe.stateAfterFunctions then pure () else none
  let mainStart : AllocationSupport.CompileState :=
    { env := [], nextSlot := stateAfterFunctions.nextSlot }
  let (main, final) ←
    lowerMain? recipe stackSlots frameName frameConfig? mainStart program.body
  if final.allocation = recipe.main then
    some { procs := procs, body := main }
  else
    none

def allSourceNames (program : Program) : List Name :=
  let functionNames :=
    program.functions.flatMap fun fn =>
      fn.name :: fn.params ++ fn.returns
  functionNames ++
    (AllocationSupport.planRecipeCore? program).toList.flatMap fun recipe =>
      (scopedStates recipe).flatMap fun entry =>
        entry.state.env.map Prod.fst

def freshFrameName (program : Program) : Option Name :=
  let names := allSourceNames program
  (List.range (names.length + 1)).findSome? fun index =>
    let candidate := "__evm_compiler_scratch_frame_" ++ toString index
    if candidate ∈ names then none else some candidate

structure SlotOccurrence where
  scope : ScopeId
  name : Name
  slot : Nat

def slotOccurrences
    (recipe : AllocationSupport.AllocationRecipe) :
    List SlotOccurrence :=
  (scopedStates recipe).flatMap fun entry =>
    entry.state.env.map fun binding =>
      { scope := entry.scope
        name := binding.1
        slot := binding.2 }

def bindingLocation? (allocation : ProgramPlan)
    (scope : ScopeId) (name : Name) : Option LocalLocation := do
  let plan ← allocation.find? scope
  plan.location? name

def inferSlotStack? (allocation : ProgramPlan)
    (occurrences : List SlotOccurrence) (slot : Nat) : Option Bool := do
  let occurrence ←
    occurrences.find? fun candidate => decide (candidate.slot = slot)
  let location ←
    bindingLocation? allocation occurrence.scope occurrence.name
  match location with
  | .stack _ => some true
  | .scratch scratchSlot =>
      if scratchSlot = slot then some false else none

def inferStackSlots? (recipe : AllocationSupport.AllocationRecipe)
    (allocation : ProgramPlan) : Option SlotSet :=
  let occurrences := slotOccurrences recipe
  (List.range recipe.frameWords).filterM fun slot =>
    inferSlotStack? allocation occurrences slot

def compatiblePlan? (allocation : ProgramPlan)
    (program : Program) :
    Option (AllocationSupport.AllocationRecipe × SlotSet) := do
  let recipe ← AllocationSupport.planRecipeCore? program
  let stackSlots ← inferStackSlots? recipe allocation
  if stackSlots.Nodup then pure () else none
  if MixedAllocation.AllocationRecipe.executable?
      recipe stackSlots program then
    pure ()
  else
    none
  if MixedAllocation.AllocationRecipe.toMixedProgramPlan
      recipe stackSlots program.memoryContract = allocation then
    some (recipe, stackSlots)
  else
    none

def Compatible (allocation : ProgramPlan) (program : Program) : Prop :=
  (compatiblePlan? allocation program).isSome = true

theorem compatiblePlan?_eq_some_exact
    {allocation : ProgramPlan} {program : Program}
    {recipe : AllocationSupport.AllocationRecipe}
    {stackSlots : SlotSet}
    (hCompatible :
      compatiblePlan? allocation program =
        some (recipe, stackSlots)) :
    AllocationSupport.planRecipeCore? program = some recipe ∧
      inferStackSlots? recipe allocation = some stackSlots ∧
      stackSlots.Nodup ∧
      MixedAllocation.AllocationRecipe.executable?
          recipe stackSlots program = true ∧
      MixedAllocation.AllocationRecipe.toMixedProgramPlan
          recipe stackSlots program.memoryContract = allocation := by
  unfold compatiblePlan? at hCompatible
  cases hRecipe : AllocationSupport.planRecipeCore? program with
  | none =>
      simp [hRecipe] at hCompatible
  | some plannedRecipe =>
      cases hSlots :
          inferStackSlots? plannedRecipe allocation with
      | none =>
          simp [hRecipe, hSlots] at hCompatible
      | some plannedSlots =>
          by_cases hNodup : plannedSlots.Nodup
          · by_cases hExecutable :
                MixedAllocation.AllocationRecipe.executable?
                    plannedRecipe plannedSlots program = true
            · by_cases hExact :
                  MixedAllocation.AllocationRecipe.toMixedProgramPlan
                      plannedRecipe plannedSlots
                        program.memoryContract = allocation
              · simp
                  [hRecipe, hSlots, hNodup, hExecutable, hExact]
                  at hCompatible
                rcases hCompatible with ⟨rfl, rfl⟩
                exact
                  ⟨rfl, hSlots, hNodup, hExecutable, hExact⟩
              · simp
                  [hRecipe, hSlots, hNodup, hExecutable, hExact]
                  at hCompatible
            · simp [hRecipe, hSlots, hNodup, hExecutable] at hCompatible
          · simp [hRecipe, hSlots, hNodup] at hCompatible

theorem compatible_witness
    {allocation : ProgramPlan} {program : Program}
    (hCompatible : Compatible allocation program) :
    ∃ recipe stackSlots,
      AllocationSupport.planRecipeCore? program = some recipe ∧
        inferStackSlots? recipe allocation = some stackSlots ∧
        stackSlots.Nodup ∧
        MixedAllocation.AllocationRecipe.executable?
            recipe stackSlots program = true ∧
        MixedAllocation.AllocationRecipe.toMixedProgramPlan
            recipe stackSlots program.memoryContract = allocation := by
  unfold Compatible at hCompatible
  cases hPlan : compatiblePlan? allocation program with
  | none =>
      simp [hPlan] at hCompatible
  | some validated =>
      rcases validated with ⟨recipe, stackSlots⟩
      exact
        ⟨recipe, stackSlots,
          compatiblePlan?_eq_some_exact hPlan⟩

def validatePlan? (allocation : ProgramPlan)
    (program : Program) :
    Option (AllocationSupport.AllocationRecipe × SlotSet) := do
  if allocation.wellFormed? then pure () else none
  if allocation.MemoryAuthorized program.memoryContract then
    pure ()
  else
    none
  compatiblePlan? allocation program

theorem validatePlan?_sound
    {allocation : ProgramPlan} {program : Program}
    {validated : AllocationSupport.AllocationRecipe × SlotSet}
    (hValidate :
      validatePlan? allocation program = some validated) :
    allocation.WellFormed ∧ Compatible allocation program := by
  unfold validatePlan? at hValidate
  by_cases hWF : allocation.wellFormed? = true
  · by_cases hAuthorized :
        allocation.MemoryAuthorized program.memoryContract
    · have hCompatible :
          compatiblePlan? allocation program = some validated := by
        simpa [hWF, hAuthorized] using hValidate
      exact
        ⟨Locals.Allocation.ProgramPlan.wellFormed_of_check hWF,
          by simp [Compatible, hCompatible]⟩
    · simp [hWF, hAuthorized] at hValidate
  · simp [hWF] at hValidate

theorem validatePlan?_memoryAuthorized
    {allocation : ProgramPlan} {program : Program}
    {validated : AllocationSupport.AllocationRecipe × SlotSet}
    (hValidate :
      validatePlan? allocation program = some validated) :
    allocation.MemoryAuthorized program.memoryContract := by
  unfold validatePlan? at hValidate
  by_cases hWF : allocation.wellFormed? = true
  · by_cases hAuthorized :
        allocation.MemoryAuthorized program.memoryContract
    · exact hAuthorized
    · simp [hWF, hAuthorized] at hValidate
  · simp [hWF] at hValidate

def lowerLocalsFromAllocation? (allocation : ProgramPlan)
    (program : Program) : Option Locals.Program := do
  let (recipe, stackSlots) ← validatePlan? allocation program
  let frameName ← freshFrameName program
  lowerToLocals? recipe stackSlots frameName program

theorem lowerLocalsFromAllocation?_contract
    {allocation : ProgramPlan} {program : Program}
    {locals : Locals.Program}
    (hLower :
      lowerLocalsFromAllocation? allocation program = some locals) :
    allocation.WellFormed ∧ Compatible allocation program := by
  unfold lowerLocalsFromAllocation? at hLower
  cases hValidate : validatePlan? allocation program with
  | none =>
      simp [hValidate] at hLower
  | some validated =>
      exact validatePlan?_sound hValidate

theorem lowerLocalsFromAllocation?_memoryAuthorized
    {allocation : ProgramPlan} {program : Program}
    {locals : Locals.Program}
    (hLower :
      lowerLocalsFromAllocation? allocation program = some locals) :
    allocation.MemoryAuthorized program.memoryContract := by
  unfold lowerLocalsFromAllocation? at hLower
  cases hValidate : validatePlan? allocation program with
  | none =>
      simp [hValidate] at hLower
  | some validated =>
      exact validatePlan?_memoryAuthorized hValidate

def lowerExpressionsFromAllocation? (allocation : ProgramPlan)
    (program : Program) : Option Expressions.Program := do
  let locals ← lowerLocalsFromAllocation? allocation program
  locals.toExpressions?

theorem lowerExpressionsFromAllocation?_contract
    {allocation : ProgramPlan} {program : Program}
    {expressions : Expressions.Program}
    (hLower :
      lowerExpressionsFromAllocation? allocation program =
        some expressions) :
    allocation.WellFormed ∧ Compatible allocation program := by
  unfold lowerExpressionsFromAllocation? at hLower
  cases hLocals :
      lowerLocalsFromAllocation? allocation program with
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      exact lowerLocalsFromAllocation?_contract hLocals

theorem lowerExpressionsFromAllocation?_memoryAuthorized
    {allocation : ProgramPlan} {program : Program}
    {expressions : Expressions.Program}
    (hLower :
      lowerExpressionsFromAllocation? allocation program =
        some expressions) :
    allocation.MemoryAuthorized program.memoryContract := by
  unfold lowerExpressionsFromAllocation? at hLower
  cases hLocals :
      lowerLocalsFromAllocation? allocation program with
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      exact lowerLocalsFromAllocation?_memoryAuthorized hLocals

def allocationLowerer :
    Locals.Allocation.Lowerer Program Expressions.Program where
  lower? program allocation :=
    lowerExpressionsFromAllocation? allocation program

def compileAllocated? (allocation : ProgramPlan)
    (program : Program) :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let expressions ←
    lowerExpressionsFromAllocation? allocation program
  let cfg ←
    Structured.TypedCfgCompiler.lowerWithProcEntryShapes?
      expressions.toStructured []
  (Compiler.AllocatedTypedCfg.Program.ofAllocation
    allocation cfg).compileCertified?

namespace Examples

def mixedWideExpressions : Option Expressions.Program := do
  let allocation ← MixedAllocation.Examples.mixedWidePlan
  lowerExpressionsFromAllocation? allocation
    MixedAllocation.Examples.wideProgram

def mixedWideAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ← MixedAllocation.Examples.mixedWidePlan
  compileAllocated? allocation MixedAllocation.Examples.wideProgram

def mixedCallProgram : Program :=
  { functions :=
      [{ name := "sum"
         params := ["x", "y"]
         returns := ["result"]
         body :=
           { stmts :=
               [.assign "result"
                  (.prim .add
                    (exprSeqTwo (.var "x") (.var "y")))] } }]
    body :=
      { stmts :=
          [ .let_ "out" (.lit AllocationSupport.zeroWord),
            .call ["out"] "sum"
              [ .lit (AllocationSupport.word 2),
                .lit (AllocationSupport.word 3) ] ] } }

def mixedCallPlan : Option ProgramPlan :=
  MixedAllocation.planAllocation? 4 [0, 3] mixedCallProgram

def mixedCallExpressions : Option Expressions.Program := do
  let allocation ← mixedCallPlan
  lowerExpressionsFromAllocation? allocation mixedCallProgram

def mixedCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ← mixedCallPlan
  compileAllocated? allocation mixedCallProgram

def allStackCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllStack? mixedCallProgram
  compileAllocated? allocation mixedCallProgram

def allScratchCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllocation? 4 [] mixedCallProgram
  compileAllocated? allocation mixedCallProgram

def twoReturnCallProgram : Program :=
  { functions :=
      [{ name := "pair"
         params := ["x"]
         returns := ["first", "second"]
         body :=
           { stmts :=
               [ .assign "first" (.var "x"),
                 .assign "second"
                   (.prim .add
                     (exprSeqTwo
                       (.var "x")
                       (.lit (AllocationSupport.word 1)))) ] } }]
    body :=
      { stmts :=
          [ .let_ "left" (.lit AllocationSupport.zeroWord),
            .let_ "right" (.lit AllocationSupport.zeroWord),
            .call ["left", "right"] "pair"
              [.lit (AllocationSupport.word 7)] ] } }

def twoReturnCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllocation? 5 [] twoReturnCallProgram
  compileAllocated? allocation twoReturnCallProgram

def alterMainScratchWords (allocation : ProgramPlan) : ProgramPlan :=
  { scopes :=
      allocation.scopes.map fun scope =>
        if scope.scope = .main then
          { scope with
            allocation :=
              { scope.allocation with
                scratchRegion? :=
                  some
                    { base := .freeMemoryPointer
                      words := scope.allocation.scratchSlots.length + 1 } } }
        else
          scope }

def alteredMixedWideRejected : Bool :=
  match MixedAllocation.Examples.mixedWidePlan with
  | none => false
  | some allocation =>
      (lowerExpressionsFromAllocation?
        (alterMainScratchWords allocation)
        MixedAllocation.Examples.wideProgram).isNone

def foreignPlanRejected : Bool :=
  match MixedAllocation.Examples.mixedWidePlan with
  | none => false
  | some allocation =>
      (lowerExpressionsFromAllocation?
        allocation mixedCallProgram).isNone

end Examples

end AllocationLowering
end Functions
end EvmCompiler
