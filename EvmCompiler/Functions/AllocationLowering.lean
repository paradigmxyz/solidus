import EvmCompiler.Functions.MixedAllocation
import EvmCompiler.Compiler.AllocatedTypedCfg

namespace EvmCompiler
namespace Functions
namespace AllocationLowering

open Locals.Allocation

abbrev SlotSet := MixedAllocation.SlotSet

structure State where
  allocation : ScratchFrameSpill.CompileState
  layout : Locals.Layout
  deriving DecidableEq, Repr

structure Ctx where
  functions : List ScratchFrameSpill.FunSlots
  frameWords : Nat
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
    (exprSeqTwo (.var frameName) (.lit (ScratchFrameSpill.slotOffset slot)))

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
        let slot ← ScratchFrameSpill.lookupSlot? name state.allocation.env
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
      (ScratchFrameSpill.bindScratchBindingsCode baseDepth bindings))

def frameExpr (words : Nat) : Locals.Expr 1 :=
  .code (ScratchFrameSpill.frameInitCode words)

def splitPrelude : List Stmt → List Locals.Stmt × List Stmt
  | [] => ([], [])
  | stmt :: rest =>
      match ScratchFrameSpill.compilePreludeStmt? stmt with
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
          ([Locals.Stmt.let_ name (.lit ScratchFrameSpill.zeroWord)],
            name :: layout)
        else
          ([Locals.Stmt.expr
              (scratchStoreExpr ctx.frameName slot
                (.lit ScratchFrameSpill.zeroWord))],
            layout)
      let (tail, finalLayout) :=
        lowerReturns ctx rest nextLayout
      (head ++ tail, finalLayout)

def lowerReturnExprs (ctx : Ctx) (state : State) :
    List Name → Option (List (Locals.Expr 1))
  | [] => some []
  | name :: rest => do
      let head ← lowerExpr ctx state (.var name)
      let tail ← lowerReturnExprs ctx state rest
      some (head :: tail)

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
  ScratchFrameSpill.storeTopSlotCode?
    (remaining + frameDepth + 1) slot

def lowerCallTargetsCode? (ctx : Ctx) (state : State) :
    List Name → Nat → Option Structured.Code
  | [], _valuesAbove => some []
  | name :: rest, valuesAbove => do
      let slot ←
        ScratchFrameSpill.lookupSlot? name state.allocation.env
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
    (recipe : ScratchFrameSpill.AllocationRecipe) :
    List ScratchFrameSpill.ScopedAllocation :=
  { scope := .main, state := recipe.main } ::
    recipe.functions ++ recipe.lexicalScopes

def scratchBindingsForRoot
    (recipe : ScratchFrameSpill.AllocationRecipe)
    (stackSlots : SlotSet) (root : ScopeId) : List (Name × Nat) :=
  ((scopedStates recipe).filterMap fun entry =>
      if scopeRoot entry.scope = root then
        some
          (entry.state.env.filter fun binding =>
            binding.2 ∉ stackSlots)
      else
        none).flatten.eraseDups

def rootNeedsFrame (recipe : ScratchFrameSpill.AllocationRecipe)
    (stackSlots : SlotSet) (root : ScopeId) : Bool :=
  !(scratchBindingsForRoot recipe stackSlots root).isEmpty

def functionNeedsFrame (recipe : ScratchFrameSpill.AllocationRecipe)
    (stackSlots : SlotSet) (name : Name) : Bool :=
  rootNeedsFrame recipe stackSlots (.function name)

def frameFunctions (recipe : ScratchFrameSpill.AllocationRecipe)
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
          ScratchFrameSpill.allocateName name state.allocation
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
          ScratchFrameSpill.lookupSlot? name state.allocation.env
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
        some ([.exprs (exprSeqOfList values), .leave], state)
    | .call targets functionName args => do
        let fn ← ScratchFrameSpill.lookupFun? functionName ctx.functions
        if args.length = fn.params.length then pure () else none
        if targets.length = fn.returns.length then pure () else none
        if targets.Nodup then pure () else none
        let loweredArgs ← lowerExprList ctx state args
        let callArgs :=
          if functionName ∈ ctx.frameFunctions then
            frameExpr ctx.frameWords :: loweredArgs
          else
            loweredArgs
        let stores ←
          lowerCallTargetsCode? ctx state targets.reverse targets.length
        some
          ([ .exprs (exprSeqOfList callArgs),
             .call functionName,
             .expr (Locals.Expr.code (results := 0) stores) ],
           state)
    | .terminal kind => some ([.terminal kind], state)
    | .terminalArgs kind args => do
        let lowered ← lowerExprSeq ctx state args
        some ([.terminalArgs kind lowered], state)
end

def lowerFunction? (recipe : ScratchFrameSpill.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (state : ScratchFrameSpill.CompileState) (fn : FunDef) :
    Option (Locals.Proc × ScratchFrameSpill.CompileState) := do
  let slots ← ScratchFrameSpill.lookupFun? fn.name recipe.functionSlots
  let root := ScopeId.function fn.name
  let scratchBindings :=
    scratchBindingsForRoot recipe stackSlots root
  let needsFrame := !scratchBindings.isEmpty
  let entryLayout :=
    fn.params.reverse ++ if needsFrame then [frameName] else []
  let ctx : Ctx :=
    { functions := recipe.functionSlots
      frameWords := recipe.frameWords
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
        { env := ScratchFrameSpill.functionEnv slots
          nextSlot := state.nextSlot }
      layout := bodyLayout }
  let (body, final) ←
    lowerBlockOpen ctx fn.returns bodyStart fn.body
  let returnValues ← lowerReturnExprs ctx final fn.returns
  let fullBody : Locals.Block :=
    { stmts :=
        markers ++ paramPrelude ++ returnPrelude ++ body.stmts ++
          [.exprs (exprSeqOfList returnValues)] }
  some
    ({ name := fn.name
       argc := fn.params.length + if needsFrame then 1 else 0
       retc := fn.returns.length
       entryLayout := entryLayout
       body := fullBody },
     { env := state.env
       nextSlot := final.allocation.nextSlot })

def lowerFunctions? (recipe : ScratchFrameSpill.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name) :
    ScratchFrameSpill.CompileState → List FunDef →
      Option (List Locals.Proc × ScratchFrameSpill.CompileState)
  | state, [] => some ([], state)
  | state, fn :: rest => do
      let (proc, next) ←
        lowerFunction? recipe stackSlots frameName state fn
      let (tail, final) ←
        lowerFunctions? recipe stackSlots frameName next rest
      some (proc :: tail, final)

def lowerMain? (recipe : ScratchFrameSpill.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (state : ScratchFrameSpill.CompileState)
    (body : Block) : Option (Locals.Block × State) := do
  let root := ScopeId.main
  let scratchBindings :=
    scratchBindingsForRoot recipe stackSlots root
  let needsFrame := !scratchBindings.isEmpty
  let ctx : Ctx :=
    { functions := recipe.functionSlots
      frameWords := recipe.frameWords
      frameName := frameName
      stackSlots := stackSlots
      root := root
      scratchBindings := scratchBindings
      frameFunctions := frameFunctions recipe stackSlots }
  let prelude :=
    if needsFrame then
      [ Locals.Stmt.let_ frameName (frameExpr recipe.frameWords),
        bindScratchBindings 0 scratchBindings ]
    else
      []
  let start : State :=
    { allocation := state
      layout := if needsFrame then [frameName] else [] }
  let (sourcePrelude, rest) := splitPrelude body.stmts
  let (lowered, final) ←
    lowerBlockOpen ctx [] start { stmts := rest }
  some
    ({ stmts := sourcePrelude ++ prelude ++ lowered.stmts },
      final)

def lowerToLocals? (recipe : ScratchFrameSpill.AllocationRecipe)
    (stackSlots : SlotSet) (frameName : Name)
    (program : Program) : Option Locals.Program := do
  let (procs, stateAfterFunctions) ←
    lowerFunctions? recipe stackSlots frameName
      recipe.stateAfterSignatures program.functions
  if stateAfterFunctions = recipe.stateAfterFunctions then pure () else none
  let mainStart : ScratchFrameSpill.CompileState :=
    { env := [], nextSlot := stateAfterFunctions.nextSlot }
  let (main, final) ←
    lowerMain? recipe stackSlots frameName mainStart program.body
  if final.allocation = recipe.main then
    some { procs := procs, body := main }
  else
    none

def allSourceNames (program : Program) : List Name :=
  let functionNames :=
    program.functions.flatMap fun fn =>
      fn.name :: fn.params ++ fn.returns
  functionNames ++
    (ScratchFrameSpill.planRecipeCore? program).toList.flatMap fun recipe =>
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
    (recipe : ScratchFrameSpill.AllocationRecipe) :
    List SlotOccurrence :=
  (scopedStates recipe).flatMap fun entry =>
    entry.state.env.map fun binding =>
      { scope := entry.scope
        name := binding.1
        slot := binding.2 }

def bindingLocation? (allocation : ProgramPlan)
    (scope : ScopeId) (name : Name) : Option LocalLocation := do
  let plan ← allocation.find? scope
  (plan.bindings.find? fun binding =>
    decide (binding.1 = name)).map Prod.snd

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

def inferStackSlots? (recipe : ScratchFrameSpill.AllocationRecipe)
    (allocation : ProgramPlan) : Option SlotSet :=
  let occurrences := slotOccurrences recipe
  (List.range recipe.frameWords).filterM fun slot =>
    inferSlotStack? allocation occurrences slot

def lowerLocalsFromAllocation? (allocation : ProgramPlan)
    (program : Program) : Option Locals.Program := do
  let recipe ← ScratchFrameSpill.planRecipeCore? program
  let stackSlots ← inferStackSlots? recipe allocation
  if MixedAllocation.AllocationRecipe.toMixedProgramPlan
      recipe stackSlots = allocation then
    let frameName ← freshFrameName program
    lowerToLocals? recipe stackSlots frameName program
  else
    none

def lowerExpressionsFromAllocation? (allocation : ProgramPlan)
    (program : Program) : Option Expressions.Program := do
  let locals ← lowerLocalsFromAllocation? allocation program
  locals.toExpressions?

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

example : mixedWideExpressions.isSome = true := by
  native_decide

def mixedWideAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ← MixedAllocation.Examples.mixedWidePlan
  compileAllocated? allocation MixedAllocation.Examples.wideProgram

example : mixedWideAllocated.isSome = true := by
  native_decide

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
          [ .let_ "out" (.lit ScratchFrameSpill.zeroWord),
            .call ["out"] "sum"
              [ .lit (ScratchFrameSpill.word 2),
                .lit (ScratchFrameSpill.word 3) ] ] } }

def mixedCallPlan : Option ProgramPlan :=
  MixedAllocation.planAllocation? 4 [0, 3] mixedCallProgram

def mixedCallExpressions : Option Expressions.Program := do
  let allocation ← mixedCallPlan
  lowerExpressionsFromAllocation? allocation mixedCallProgram

example : mixedCallExpressions.isSome = true := by
  native_decide

def mixedCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ← mixedCallPlan
  compileAllocated? allocation mixedCallProgram

example : mixedCallAllocated.isSome = true := by
  native_decide

def allStackCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllStack? mixedCallProgram
  compileAllocated? allocation mixedCallProgram

example : allStackCallAllocated.isSome = true := by
  native_decide

def allScratchCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllocation? 4 [] mixedCallProgram
  compileAllocated? allocation mixedCallProgram

example : allScratchCallAllocated.isSome = true := by
  native_decide

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
                       (.lit (ScratchFrameSpill.word 1)))) ] } }]
    body :=
      { stmts :=
          [ .let_ "left" (.lit ScratchFrameSpill.zeroWord),
            .let_ "right" (.lit ScratchFrameSpill.zeroWord),
            .call ["left", "right"] "pair"
              [.lit (ScratchFrameSpill.word 7)] ] } }

def twoReturnCallAllocated :
    Option Compiler.AllocatedTypedCfg.CertifiedArtifact := do
  let allocation ←
    MixedAllocation.planAllocation? 5 [] twoReturnCallProgram
  compileAllocated? allocation twoReturnCallProgram

example : twoReturnCallAllocated.isSome = true := by
  native_decide

end Examples

end AllocationLowering
end Functions
end EvmCompiler
