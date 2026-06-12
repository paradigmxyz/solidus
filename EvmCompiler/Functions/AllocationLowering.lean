import EvmCompiler.Functions.MixedAllocation
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
        some ([.exprs (exprSeqOfList values), .leave], state)
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
          [.exprs (exprSeqOfList returnValues)] }
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
