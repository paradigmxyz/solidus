import EvmCompiler.Functions.AllocationInteractionTerminal

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCursor

open AllocationInteractionRelation

/-- Checked global outputs of the existing allocation validator and lowerer. -/
structure Compilation
    (allocation : Locals.Allocation.ProgramPlan)
    (program : Functions.Program)
    (expressions : Expressions.Program) where
  recipe : AllocationSupport.AllocationRecipe
  stackSlots : MixedAllocation.SlotSet
  frameName : Locals.Name
  validate :
    AllocationLowering.validatePlan? allocation program =
      some (recipe, stackSlots)
  fresh : AllocationLowering.freshFrameName program = some frameName
  lower :
    AllocationLowering.lowerExpressionsFromAllocation? allocation program =
      some expressions

theorem Compilation.of_lowering
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (hLower :
      AllocationLowering.lowerExpressionsFromAllocation?
          allocation program =
        some expressions) :
    Nonempty (Compilation allocation program expressions) := by
  have hWhole := hLower
  unfold AllocationLowering.lowerExpressionsFromAllocation? at hLower
  cases hLocals :
      AllocationLowering.lowerLocalsFromAllocation? allocation program with
  | none => simp [hLocals] at hLower
  | some locals =>
      unfold AllocationLowering.lowerLocalsFromAllocation? at hLocals
      cases hValidate : AllocationLowering.validatePlan? allocation program with
      | none => simp [hValidate] at hLocals
      | some validated =>
          rcases validated with ⟨recipe, stackSlots⟩
          cases hFresh : AllocationLowering.freshFrameName program with
          | none => simp [hValidate, hFresh] at hLocals
          | some frameName =>
              exact
                ⟨{ recipe := recipe
                   stackSlots := stackSlots
                   frameName := frameName
                   validate := hValidate
                   fresh := hFresh
                   lower := hWhole }⟩

def Compilation.frameConfig?
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions) :
    Option AllocationSupport.ScratchFrameConfig :=
  AllocationSupport.scratchFrameConfig?
    program.memoryContract compilation.recipe.frameWords

def Compilation.lowerCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    (root : Locals.Allocation.ScopeId)
    (scratchBindings : List (Locals.Name × Nat)) :
    AllocationLowering.Ctx :=
  { functions := compilation.recipe.functionSlots
    frameConfig? := compilation.frameConfig?
    frameName := compilation.frameName
    stackSlots := compilation.stackSlots
    root := root
    scratchBindings := scratchBindings
    frameFunctions :=
      AllocationLowering.frameFunctions
        compilation.recipe compilation.stackSlots }

structure Compilation.CtxShared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    (ctx : AllocationLowering.Ctx) : Prop where
  functions : ctx.functions = compilation.recipe.functionSlots
  frameConfig : ctx.frameConfig? = compilation.frameConfig?
  frameName : ctx.frameName = compilation.frameName
  stackSlots : ctx.stackSlots = compilation.stackSlots
  frameFunctions :
    ctx.frameFunctions =
      AllocationLowering.frameFunctions
        compilation.recipe compilation.stackSlots

theorem Compilation.lowerCtx_shared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    (root : Locals.Allocation.ScopeId)
    (scratchBindings : List (Locals.Name × Nat)) :
    compilation.CtxShared (compilation.lowerCtx root scratchBindings) := by
  constructor <;> rfl

/-- Runtime-live names agree with the already-planned allocation prefix. -/
def ActiveEnv
    (slots : AllocationSupport.FunSlots)
    (env : AllocationSupport.SlotEnv)
    (live : List Functions.Name) : Prop :=
  ∃ locals,
    env = locals ++ AllocationSupport.functionEnv slots ∧
      live =
        locals.map Prod.fst ++
          (slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse

namespace ActiveEnv

theorem after_planStmt
    {slots : AllocationSupport.FunSlots}
    {scope : Locals.Allocation.ScopeId}
    {planning : AllocationSupport.PlanningState}
    {live : List Functions.Name} {stmt : Functions.Stmt}
    (hActive : ActiveEnv slots planning.allocation.env live) :
    ActiveEnv slots
      (AllocationSupport.planStmt scope planning stmt).allocation.env
      (Functions.Scope.Stmt.outEnv live stmt) := by
  rcases hActive with ⟨locals, hEnv, hLive⟩
  cases stmt with
  | let_ name value =>
      refine ⟨(name, planning.allocation.nextSlot) :: locals, ?_, ?_⟩
      · simp [AllocationSupport.planStmt_allocation_env, hEnv]
      · simp [Functions.Scope.Stmt.outEnv, hLive, List.append_assoc]
  | expr expr | assign name value | block body | if_ cond body
  | switch scrutinee cases defaultBody | for_ init cond post body
  | brk | cont | leave | call targets functionName args
  | terminal kind | terminalArgs kind args =>
      refine ⟨locals, ?_, ?_⟩
      · simpa [AllocationSupport.planStmt_allocation_env] using hEnv
      · simpa [Functions.Scope.Stmt.outEnv] using hLive

theorem after_planStmtList
    {slots : AllocationSupport.FunSlots}
    {scope : Locals.Allocation.ScopeId}
    {planning : AllocationSupport.PlanningState}
    {live : List Functions.Name} {stmts : List Functions.Stmt}
    (hActive : ActiveEnv slots planning.allocation.env live) :
    ActiveEnv slots
      (AllocationSupport.planStmtList scope planning stmts).allocation.env
      (Functions.Scope.StmtList.outEnv live stmts) := by
  induction stmts generalizing planning live with
  | nil =>
      simpa [AllocationSupport.planStmtList,
        Functions.Scope.StmtList.outEnv] using hActive
  | cons stmt rest ih =>
      simpa [AllocationSupport.planStmtList,
        Functions.Scope.StmtList.outEnv] using
        ih (hActive.after_planStmt (scope := scope) (stmt := stmt))

theorem after_planBlockOpen
    {slots : AllocationSupport.FunSlots}
    {scope : Locals.Allocation.ScopeId}
    {planning : AllocationSupport.PlanningState}
    {live : List Functions.Name} {block : Functions.Block}
    (hActive : ActiveEnv slots planning.allocation.env live) :
    ActiveEnv slots
      (AllocationSupport.planBlockOpen scope planning block).allocation.env
      (Functions.Scope.Block.outEnv live block) := by
  rcases block with ⟨stmts⟩
  simpa [AllocationSupport.planBlockOpen,
    Functions.Scope.Block.outEnv] using
    hActive.after_planStmtList (scope := scope) (stmts := stmts)

end ActiveEnv

/-- Static pass-owned root consumed by recursive statement preservation. -/
structure RootArtifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions) where
  functionRoot? : Option Functions.Name
  rootScope : Locals.Allocation.ScopeId
  slots : AllocationSupport.FunSlots
  returns : List Functions.Name
  sourceBlock : Functions.Block
  startState : AllocationLowering.State
  startLocals : Locals.Ctx
  planning : AllocationSupport.PlanningState
  planningAllocation : planning.allocation = startState.allocation
  rootScopeOwner :
    MixedAllocation.AllocationRecipe.functionRoot? rootScope = functionRoot?
  plan : Locals.Allocation.Plan
  planWF : plan.WellFormed
  finalState : AllocationLowering.State
  finalLocals : Locals.Ctx
  planEq :
    plan =
      MixedAllocation.allocationOfState
        program.memoryContract compilation.recipe.frameWords
        (MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots rootScope
          finalState.allocation)
        finalState.allocation
  finalFrameFresh :
    compilation.frameName ∉ finalState.allocation.env.map Prod.fst
  lexicalFrameFresh :
    ∀ entry, entry ∈ compilation.recipe.lexicalScopes →
      compilation.frameName ∉ entry.state.env.map Prod.fst
  scopeStackEntries :
    ∀ {scope : Locals.Allocation.ScopeId}
      {state : AllocationSupport.CompileState}
      {added : AllocationSupport.SlotEnv},
      MixedAllocation.AllocationRecipe.functionRoot? scope = functionRoot? →
        state.env = added ++ AllocationSupport.functionEnv slots →
        MixedAllocation.AllocationRecipe.stackEntriesForScope
            compilation.recipe compilation.stackSlots scope state =
          MixedAllocation.stackEntries compilation.stackSlots added ++
            MixedAllocation.stackEntries compilation.stackSlots
              slots.returns.reverse ++
            MixedAllocation.stackEntries compilation.stackSlots
              slots.params.reverse
  plannedFinal :
    (AllocationSupport.planBlockOpen rootScope planning sourceBlock).allocation =
      finalState.allocation
  plannedScopes :
    ∀ entry,
      entry ∈
          (AllocationSupport.planBlockOpen rootScope planning sourceBlock).scopes →
        entry ∈ compilation.recipe.lexicalScopes
  lowered : Locals.Block
  compiled : List Expressions.Stmt
  lowerCtx : AllocationLowering.Ctx
  lowerCtxShared : compilation.CtxShared lowerCtx
  lower :
    AllocationLowering.lowerBlockOpen lowerCtx returns
        startState sourceBlock =
      some (lowered, finalState)
  compile :
    Locals.Block.compileOpen startLocals lowered =
      some (compiled, finalLocals)
  sourceScoped :
    Functions.Scope.Block.Scoped
      ((slots.returns.map Prod.fst).reverse ++
        (slots.params.map Prod.fst).reverse)
      sourceBlock
  activeEnv :
    ActiveEnv slots planning.allocation.env
      ((slots.returns.map Prod.fst).reverse ++
        (slots.params.map Prod.fst).reverse)

/-- Exact static cursor for one recursively compiled source block. -/
structure CoreCursor
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    (root : RootArtifact compilation)
    (scope : Locals.Allocation.ScopeId)
    (live : List Functions.Name)
    (sourceBlock : Functions.Block)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) where
  planning : AllocationSupport.PlanningState
  planningAllocation : planning.allocation = lowerState.allocation
  scopeRoot :
    MixedAllocation.AllocationRecipe.functionRoot? scope = root.functionRoot?
  plan : Locals.Allocation.Plan
  planWF : plan.WellFormed
  finalState : AllocationLowering.State
  finalLocals : Locals.Ctx
  planEq :
    plan =
      MixedAllocation.allocationOfState
        program.memoryContract compilation.recipe.frameWords
        (MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots scope finalState.allocation)
        finalState.allocation
  finalFrameFresh :
    compilation.frameName ∉ finalState.allocation.env.map Prod.fst
  plannedFinal :
    (AllocationSupport.planBlockOpen scope planning sourceBlock).allocation =
      finalState.allocation
  plannedScopes :
    ∀ entry,
      entry ∈
          (AllocationSupport.planBlockOpen scope planning sourceBlock).scopes →
        entry ∈ compilation.recipe.lexicalScopes
  lowered : Locals.Block
  compiled : List Expressions.Stmt
  lower :
    AllocationLowering.lowerBlockOpen root.lowerCtx root.returns
        lowerState sourceBlock =
      some (lowered, finalState)
  compile :
    Locals.Block.compileOpen localsCtx lowered =
      some (compiled, finalLocals)
  sourceScoped : Functions.Scope.Block.Scoped live sourceBlock
  activeEnv : ActiveEnv root.slots planning.allocation.env live

def RootArtifact.cursor
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    (root : RootArtifact compilation) :
    CoreCursor root root.rootScope
      ((root.slots.returns.map Prod.fst).reverse ++
        (root.slots.params.map Prod.fst).reverse)
      root.sourceBlock root.startState root.startLocals :=
  { planning := root.planning
    planningAllocation := root.planningAllocation
    scopeRoot := root.rootScopeOwner
    plan := root.plan
    planWF := root.planWF
    finalState := root.finalState
    finalLocals := root.finalLocals
    planEq := root.planEq
    finalFrameFresh := root.finalFrameFresh
    plannedFinal := root.plannedFinal
    plannedScopes := root.plannedScopes
    lowered := root.lowered
    compiled := root.compiled
    lower := root.lower
    compile := root.compile
    sourceScoped := root.sourceScoped
    activeEnv := root.activeEnv }

theorem CoreCursor.cons
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        lowerState localsCtx) :
    ∃ afterState afterLocals headLower headCode,
      ∃ tailCursor :
        CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
          { stmts := rest } afterState afterLocals,
      tailCursor.planning =
          AllocationSupport.planStmt scope cursor.planning stmt ∧
      tailCursor.plan = cursor.plan ∧
      tailCursor.finalState = cursor.finalState ∧
      tailCursor.finalLocals = cursor.finalLocals ∧
      AllocationLowering.lowerStmt root.lowerCtx root.returns
          lowerState stmt = some (headLower, afterState) ∧
      Locals.Block.compileOpen localsCtx { stmts := headLower } =
        some (headCode, afterLocals) ∧
      cursor.lowered.stmts = headLower ++ tailCursor.lowered.stmts ∧
      cursor.compiled = headCode ++ tailCursor.compiled ∧
      Functions.Scope.Stmt.Scoped live stmt := by
  obtain ⟨headLower, afterState, tailLower,
      hHeadLower, hTailLower, hLowered⟩ :=
    AllocationLowering.lowerBlockOpen_cons_components cursor.lower
  have hLoweredBlock :
      cursor.lowered = { stmts := headLower ++ tailLower } := by
    cases hCursorLowered : cursor.lowered with
    | mk stmts =>
        have hStmts : stmts = headLower ++ tailLower := by
          simpa [hCursorLowered] using hLowered
        cases hStmts
        rfl
  have hCompile :
      Locals.Block.compileOpen localsCtx
          { stmts := headLower ++ tailLower } =
        some (cursor.compiled, cursor.finalLocals) := by
    have hCompile' := cursor.compile
    rw [hLoweredBlock] at hCompile'
    exact hCompile'
  obtain ⟨headCode, afterLocals, tailCode,
      hHeadCompile, hTailCompile, hCompiled⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hScoped :
      Functions.Scope.Stmt.Scoped live stmt ∧
        Functions.Scope.StmtList.Scoped
          (Functions.Scope.Stmt.outEnv live stmt) rest := by
    simpa [Functions.Scope.Block.Scoped,
      Functions.Scope.StmtList.Scoped] using cursor.sourceScoped
  let tailCursor :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals :=
    { planning := AllocationSupport.planStmt scope cursor.planning stmt
      planningAllocation :=
        AllocationLowering.lowerStmt_allocation_eq_planStmt
          stmt scope cursor.planning root.lowerCtx root.returns
          lowerState afterState headLower cursor.planningAllocation hHeadLower
      scopeRoot := cursor.scopeRoot
      plan := cursor.plan
      planWF := cursor.planWF
      finalState := cursor.finalState
      finalLocals := cursor.finalLocals
      planEq := cursor.planEq
      finalFrameFresh := cursor.finalFrameFresh
      plannedFinal := by
        simpa [AllocationSupport.planBlockOpen,
          AllocationSupport.planStmtList] using cursor.plannedFinal
      plannedScopes := by
        intro entry hEntry
        apply cursor.plannedScopes entry
        simpa [AllocationSupport.planBlockOpen,
          AllocationSupport.planStmtList] using hEntry
      lowered := { stmts := tailLower }
      compiled := tailCode
      lower := hTailLower
      compile := hTailCompile
      sourceScoped := by
        simpa [Functions.Scope.Block.Scoped] using hScoped.2
      activeEnv := cursor.activeEnv.after_planStmt }
  exact
    ⟨afterState, afterLocals, headLower, headCode, tailCursor,
      rfl, rfl, rfl, rfl, hHeadLower, hHeadCompile, hLowered, hCompiled,
      hScoped.1⟩

def CoreCursor.finished
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId} {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    (cursor : CoreCursor root scope live sourceBlock lowerState localsCtx) :
    CoreCursor root scope (Functions.Scope.Block.outEnv live sourceBlock)
      { stmts := [] } cursor.finalState cursor.finalLocals := by
  let finalPlanning :=
    AllocationSupport.planBlockOpen scope cursor.planning sourceBlock
  have hFinalActive :
      ActiveEnv root.slots finalPlanning.allocation.env
        (Functions.Scope.Block.outEnv live sourceBlock) :=
    cursor.activeEnv.after_planBlockOpen
  exact
    { planning := finalPlanning
      planningAllocation := cursor.plannedFinal
      scopeRoot := cursor.scopeRoot
      plan := cursor.plan
      planWF := cursor.planWF
      finalState := cursor.finalState
      finalLocals := cursor.finalLocals
      planEq := cursor.planEq
      finalFrameFresh := cursor.finalFrameFresh
      plannedFinal := by
        simpa [finalPlanning, AllocationSupport.planBlockOpen,
          AllocationSupport.planStmtList] using cursor.plannedFinal
      plannedScopes := by
        intro entry hEntry
        apply cursor.plannedScopes entry
        simpa [finalPlanning, AllocationSupport.planBlockOpen,
          AllocationSupport.planStmtList] using hEntry
      lowered := { stmts := [] }
      compiled := []
      lower := by
        simp [AllocationLowering.lowerBlockOpen,
          AllocationLowering.lowerStmtList]
      compile := by simp [Locals.Block.compileOpen]
      sourceScoped := by
        simp [Functions.Scope.Block.Scoped,
          Functions.Scope.StmtList.Scoped]
      activeEnv := hFinalActive }

end AllocationInteractionCursor
end Functions
end EvmCompiler
