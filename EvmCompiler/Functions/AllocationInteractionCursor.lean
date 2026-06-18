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
      ∀ name,
        name ∈ live ↔
          name ∈
            locals.map Prod.fst ++
              (slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse

namespace ActiveEnv

/-- Active allocation environments depend only on live-name membership. -/
theorem transport_live
    {slots : AllocationSupport.FunSlots}
    {env : AllocationSupport.SlotEnv}
    {before after : List Functions.Name}
    (hActive : ActiveEnv slots env before)
    (hLive : ∀ name, name ∈ before ↔ name ∈ after) :
    ActiveEnv slots env after := by
  rcases hActive with ⟨locals, hEnv, hBefore⟩
  exact ⟨locals, hEnv, fun name => (hLive name).symm.trans (hBefore name)⟩

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
      · intro localName
        simp [Functions.Scope.Stmt.outEnv, hLive, List.append_assoc]
  | expr expr | assign name value | block body | if_ cond body
  | switch scrutinee cases defaultBody | for_ init cond post body
  | brk | cont | leave | call targets functionName args
  | terminal kind | terminalArgs kind args =>
      refine ⟨locals, ?_, ?_⟩
      · simpa [AllocationSupport.planStmt_allocation_env] using hEnv
      · intro localName
        simpa [Functions.Scope.Stmt.outEnv] using hLive localName

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

/-- Exact parent endpoint equalities retained by a decomposed tail cursor. -/
structure ExactTail
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals) : Prop where
  plan : tail.plan = cursor.plan
  finalState : tail.finalState = cursor.finalState
  finalLocals : tail.finalLocals = cursor.finalLocals
  compiled : ∃ headCode, cursor.compiled = headCode ++ tail.compiled

namespace ExactTail

/-- An exact residual cursor preserves every non-layout control destination.
Both compiler runs reach the same final Locals context, so their ordinary
same-control facts compose through that shared endpoint. -/
theorem locals_sameControl
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hExact : ExactTail cursor tail) :
    Locals.Ctx.SameControl beforeLocals afterLocals := by
  have hHead := Locals.Block.compileOpen_sameControl cursor.compile
  have hTail := Locals.Block.compileOpen_sameControl tail.compile
  rw [hExact.finalLocals] at hTail
  exact hHead.trans hTail.symm

end ExactTail

/-- Static transport facts supplied by one successful source statement. -/
structure StepTransport
    (beforeState afterState : AllocationLowering.State)
    (beforeLocals afterLocals : Locals.Ctx)
    (beforeLive : List Functions.Name)
    (stmt : Functions.Stmt) : Prop where
  state :
    AllocationLowering.StateExtends beforeLive beforeState afterState
  locals : Locals.Ctx.SameControl beforeLocals afterLocals
  live :
    ∀ name, name ∈ beforeLive →
      name ∈ Functions.Scope.Stmt.outEnv beforeLive stmt

theorem StepTransport.of_compilers
    {lowerCtx : AllocationLowering.Ctx}
    {returns beforeLive : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {stmt : Functions.Stmt}
    {lowered : List Locals.Stmt}
    {compiled : List Expressions.Stmt}
    (hScoped : Functions.Scope.Stmt.Scoped beforeLive stmt)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState stmt =
        some (lowered, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := lowered } =
        some (compiled, afterLocals)) :
    StepTransport beforeState afterState beforeLocals afterLocals
      beforeLive stmt :=
  { state := AllocationLowering.lowerStmt_stateExtends hScoped hLower
    locals := Locals.Block.compileOpen_sameControl hCompile
    live := fun _ hName => Functions.Scope.Stmt.mem_outEnv hName }

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

/-- A compiler cursor depends on the live environment only extensionally. -/
def CoreCursor.transport_live
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {before after : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope before sourceBlock lowerState localsCtx)
    (hLive : ∀ name, name ∈ before ↔ name ∈ after) :
    CoreCursor root scope after sourceBlock lowerState localsCtx :=
  { cursor with
    sourceScoped :=
      Functions.Scope.Block.Scoped.of_env_equiv hLive cursor.sourceScoped
    activeEnv := cursor.activeEnv.transport_live hLive }

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

/-- Static placement selected for one declaration by the validated plan. -/
inductive DeclarationPlacement
    (lowerCtx : AllocationLowering.Ctx)
    (beforeState : AllocationLowering.State)
    (plan : Locals.Allocation.Plan)
    (beforeLive : List Functions.Name)
    (name : Functions.Name) : Prop where
  | stack
      (slot planDepth : Nat)
      (hSlot : slot = beforeState.allocation.nextSlot)
      (hStack :
        AllocationLowering.isStackSlot lowerCtx slot = true)
      (hLocation : plan.location? name = some (.stack planDepth))
      (hOrder :
        currentStackOrder plan (name :: beforeLive) =
          name :: currentStackOrder plan beforeLive) :
      DeclarationPlacement lowerCtx beforeState plan beforeLive name
  | scratch
      (slot : Nat)
      (hSlot : slot = beforeState.allocation.nextSlot)
      (hStack :
        AllocationLowering.isStackSlot lowerCtx slot = false)
      (hLocation : plan.location? name = some (.scratch slot))
      (hOrder :
        currentStackOrder plan (name :: beforeLive) =
          currentStackOrder plan beforeLive) :
      DeclarationPlacement lowerCtx beforeState plan beforeLive name

theorem CoreCursor.headScoped
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        lowerState localsCtx) :
    Functions.Scope.Stmt.Scoped live stmt := by
  simpa [Functions.Scope.Block.Scoped,
    Functions.Scope.StmtList.Scoped] using cursor.sourceScoped.1

/-- The final planner environment extends the environment at this cursor. -/
theorem CoreCursor.final_env_extension
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx) :
    ∃ added,
      cursor.finalState.allocation.env =
        added ++ lowerState.allocation.env := by
  obtain ⟨added, hEnv⟩ :=
    AllocationSupport.planBlockOpen_env_extension
      scope cursor.planning sourceBlock
  refine ⟨added, ?_⟩
  calc
    cursor.finalState.allocation.env =
        (AllocationSupport.planBlockOpen
          scope cursor.planning sourceBlock).allocation.env :=
      congrArg AllocationSupport.CompileState.env cursor.plannedFinal.symm
    _ = added ++ cursor.planning.allocation.env := hEnv
    _ = added ++ lowerState.allocation.env := by
      rw [cursor.planningAllocation]

/-- A binding visible at the cursor keeps its slot in the final plan state. -/
theorem CoreCursor.bodyFinal_lookup_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    {localName : Functions.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          localName lowerState.allocation.env =
        some slot) :
    AllocationSupport.lookupSlot?
        localName cursor.finalState.allocation.env =
      some slot := by
  obtain ⟨added, hEnv⟩ := cursor.final_env_extension
  have hMemCurrent :
      (localName, slot) ∈ lowerState.allocation.env :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
  have hMemEntry :
      (localName, slot) ∈ cursor.finalState.allocation.env := by
    rw [hEnv]
    exact List.mem_append_right added hMemCurrent
  have hEntryNodup :
      (cursor.finalState.allocation.env.map Prod.fst).Nodup := by
    have hScopeNodup := cursor.planWF.2.1
    simpa [cursor.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  exact
    AllocationSupport.lookupSlot?_eq_some_of_mem
      hEntryNodup hMemEntry

/-- Every source-live name at a cursor has a checked lowering slot. -/
theorem CoreCursor.lookupSlot_of_live
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    {localName : Functions.Name}
    (hLive : localName ∈ live) :
    ∃ slot,
      AllocationSupport.lookupSlot?
          localName lowerState.allocation.env =
        some slot := by
  rcases cursor.activeEnv with ⟨locals, hCurrent, hLiveEq⟩
  have hNamePlanning :
      localName ∈ cursor.planning.allocation.env.map Prod.fst := by
    rw [hCurrent]
    rw [hLiveEq] at hLive
    simpa [AllocationSupport.functionEnv, List.map_append] using hLive
  obtain ⟨binding, hBinding, hName⟩ :=
    List.mem_map.mp hNamePlanning
  rcases binding with ⟨candidate, slot⟩
  simp only at hName
  subst candidate
  have hBindingLower :
      (localName, slot) ∈ lowerState.allocation.env := by
    have hEnv :
        cursor.planning.allocation.env =
          lowerState.allocation.env :=
      congrArg AllocationSupport.CompileState.env
        cursor.planningAllocation
    rw [← hEnv]
    exact hBinding
  obtain ⟨added, hFinal⟩ := cursor.final_env_extension
  have hFinalNodup :
      (cursor.finalState.allocation.env.map Prod.fst).Nodup := by
    have hScopeNodup := cursor.planWF.2.1
    simpa [cursor.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  have hLowerNodup :
      (lowerState.allocation.env.map Prod.fst).Nodup := by
    rw [hFinal, List.map_append] at hFinalNodup
    exact (List.nodup_append.mp hFinalNodup).2.1
  exact
    ⟨slot,
      AllocationSupport.lookupSlot?_eq_some_of_mem
        hLowerNodup hBindingLower⟩

theorem CoreCursor.frameName_not_mem_live
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx) :
    compilation.frameName ∉ live := by
  intro hFrame
  obtain ⟨slot, hLookup⟩ := cursor.lookupSlot_of_live hFrame
  have hMemCurrent :
      (compilation.frameName, slot) ∈ lowerState.allocation.env :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
  obtain ⟨added, hFinal⟩ := cursor.final_env_extension
  apply cursor.finalFrameFresh
  rw [hFinal, List.map_append]
  exact
    List.mem_append_right _
      (List.mem_map.mpr
        ⟨(compilation.frameName, slot), hMemCurrent, rfl⟩)

theorem CoreCursor.frameName_not_mem_currentStackOrder
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx) :
    compilation.frameName ∉
      currentStackOrder cursor.plan live := by
  intro hFrame
  exact
    cursor.frameName_not_mem_live
      (mem_live_of_mem_currentStackOrder hFrame)

/-- Recover the exact runtime stack order at the cursor position. -/
theorem CoreCursor.currentStackOrder_of_active
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (locals : AllocationSupport.SlotEnv)
    (hCurrent :
      cursor.planning.allocation.env =
        locals ++ AllocationSupport.functionEnv root.slots)
    (hLive :
      ∀ name,
        name ∈ live ↔
          name ∈
            locals.map Prod.fst ++
              (root.slots.returns.map Prod.fst).reverse ++
              (root.slots.params.map Prod.fst).reverse) :
    currentStackOrder cursor.plan live =
      MixedAllocation.stackOrder compilation.stackSlots locals ++
        MixedAllocation.stackOrder compilation.stackSlots
          root.slots.returns.reverse ++
        MixedAllocation.stackOrder compilation.stackSlots
          root.slots.params.reverse := by
  have hOrderLive := currentStackOrder_congr (plan := cursor.plan) hLive
  obtain ⟨future, hFinal⟩ := cursor.final_env_extension
  have hPlanningLower :
      cursor.planning.allocation.env =
        lowerState.allocation.env :=
    congrArg AllocationSupport.CompileState.env
      cursor.planningAllocation
  have hLowerCurrent :
      lowerState.allocation.env =
        locals ++ AllocationSupport.functionEnv root.slots :=
    hPlanningLower.symm.trans hCurrent
  have hFinalExtension :
      cursor.finalState.allocation.env =
        (future ++ locals) ++
          AllocationSupport.functionEnv root.slots := by
    rw [hFinal, hLowerCurrent, List.append_assoc]
  have hFinalEnv :
      cursor.finalState.allocation.env =
        future ++ locals ++ root.slots.returns ++
          root.slots.params := by
    simpa [AllocationSupport.functionEnv, List.append_assoc] using
      hFinalExtension
  have hEntries :
      MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots scope
          cursor.finalState.allocation =
        MixedAllocation.stackEntries compilation.stackSlots
            (future ++ locals) ++
          MixedAllocation.stackEntries compilation.stackSlots
            root.slots.returns.reverse ++
          MixedAllocation.stackEntries compilation.stackSlots
            root.slots.params.reverse := by
    exact root.scopeStackEntries cursor.scopeRoot hFinalExtension
  have hEntryNodup :
      (cursor.finalState.allocation.env.map Prod.fst).Nodup := by
    have hScopeNodup := cursor.planWF.2.1
    simpa [cursor.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  have hOrder :=
    MixedAllocation.allocationOfState_active_stack_filter
      (contract := program.memoryContract)
      (frameWords := compilation.recipe.frameWords)
      (stackSlots := compilation.stackSlots)
      (state := cursor.finalState.allocation)
      (future := future) (locals := locals)
      (returns := root.slots.returns)
      (params := root.slots.params)
      hFinalEnv hEntryNodup
  rw [hOrderLive, cursor.planEq]
  unfold currentStackOrder
  rw [hEntries]
  exact hOrder

theorem CoreCursor.currentStackOrder
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx) :
    ∃ locals,
      cursor.planning.allocation.env =
          locals ++ AllocationSupport.functionEnv root.slots ∧
        (∀ name,
          name ∈ live ↔
            name ∈
              locals.map Prod.fst ++
                (root.slots.returns.map Prod.fst).reverse ++
                (root.slots.params.map Prod.fst).reverse) ∧
        currentStackOrder cursor.plan live =
          MixedAllocation.stackOrder compilation.stackSlots locals ++
            MixedAllocation.stackOrder compilation.stackSlots
              root.slots.returns.reverse ++
            MixedAllocation.stackOrder compilation.stackSlots
              root.slots.params.reverse := by
  rcases cursor.activeEnv with ⟨locals, hCurrent, hLive⟩
  exact
    ⟨locals, hCurrent, hLive,
      cursor.currentStackOrder_of_active locals hCurrent hLive⟩

private theorem CoreCursor.location_stack_of_lookup_aux
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    {localName : Functions.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          localName lowerState.allocation.env =
        some slot)
    (hStack :
      AllocationLowering.isStackSlot root.lowerCtx slot = true) :
    ∃ depth,
      cursor.plan.location? localName = some (.stack depth) := by
  have hFinalLookup := cursor.bodyFinal_lookup_of_lookup hLookup
  have hFinalMem :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hFinalLookup
  have hNodup :
      (cursor.finalState.allocation.env.map Prod.fst).Nodup := by
    have hScopeNodup := cursor.planWF.2.1
    simpa [cursor.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  rcases cursor.activeEnv with ⟨locals, hCurrent, _hLive⟩
  obtain ⟨future, hFinal⟩ := cursor.final_env_extension
  have hPlanningLower :
      cursor.planning.allocation.env = lowerState.allocation.env :=
    congrArg AllocationSupport.CompileState.env
      cursor.planningAllocation
  have hFinalExtension :
      cursor.finalState.allocation.env =
        (future ++ locals) ++
          AllocationSupport.functionEnv root.slots := by
    rw [hFinal, ← hPlanningLower, hCurrent, List.append_assoc]
  have hEntry :
      (localName, slot) ∈
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots scope
          cursor.finalState.allocation := by
    rw [root.scopeStackEntries cursor.scopeRoot hFinalExtension]
    rw [hFinalExtension] at hFinalMem
    have hSlot : slot ∈ compilation.stackSlots := by
      have hSlotCtx :=
        (AllocationLowering.isStackSlot_eq_true_iff
          root.lowerCtx slot).mp hStack
      rwa [root.lowerCtxShared.stackSlots] at hSlotCtx
    rcases List.mem_append.mp hFinalMem with hAdded | hSignature
    · exact
        List.mem_append_left _
          (List.mem_append_left _
            (MixedAllocation.mem_stackEntries_iff.mpr
              ⟨hAdded, hSlot⟩))
    · rcases List.mem_append.mp hSignature with hReturn | hParam
      · exact
          List.mem_append_left _
            (List.mem_append_right _
              (MixedAllocation.mem_stackEntries_iff.mpr
                ⟨by simpa using hReturn, hSlot⟩))
      · exact
          List.mem_append_right _
            (MixedAllocation.mem_stackEntries_iff.mpr
              ⟨by simpa using hParam, hSlot⟩)
  rw [cursor.planEq]
  exact
    MixedAllocation.allocationOfState_location_stack_of_entry
      hNodup hFinalMem hEntry

private theorem CoreCursor.location_scratch_of_lookup_aux
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    {localName : Functions.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          localName lowerState.allocation.env =
        some slot)
    (hScratch :
      AllocationLowering.isStackSlot root.lowerCtx slot = false) :
    cursor.plan.location? localName = some (.scratch slot) := by
  have hFinalLookup := cursor.bodyFinal_lookup_of_lookup hLookup
  have hFinalMem :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hFinalLookup
  have hNodup :
      (cursor.finalState.allocation.env.map Prod.fst).Nodup := by
    have hScopeNodup := cursor.planWF.2.1
    simpa [cursor.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  have hNotEntry :
      (localName, slot) ∉
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots scope
          cursor.finalState.allocation := by
    have hSlot : slot ∉ compilation.stackSlots := by
      have hSlotCtx :=
        (AllocationLowering.isStackSlot_eq_false_iff
          root.lowerCtx slot).mp hScratch
      rwa [root.lowerCtxShared.stackSlots] at hSlotCtx
    exact
      MixedAllocation.AllocationRecipe.not_mem_stackEntriesForScope_of_slot_not_mem
        hSlot
  rw [cursor.planEq]
  exact
    MixedAllocation.allocationOfState_location_scratch_of_not_entry
      hNodup hFinalMem hNotEntry

theorem CoreCursor.location_stack_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    {localName : Functions.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          localName lowerState.allocation.env =
        some slot)
    (hStack :
      AllocationLowering.isStackSlot root.lowerCtx slot = true) :
    ∃ depth,
      cursor.plan.location? localName = some (.stack depth) := by
  exact cursor.location_stack_of_lookup_aux hLookup hStack

theorem CoreCursor.location_scratch_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    {localName : Functions.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          localName lowerState.allocation.env =
        some slot)
    (hScratch :
      AllocationLowering.isStackSlot root.lowerCtx slot = false) :
    cursor.plan.location? localName = some (.scratch slot) := by
  exact cursor.location_scratch_of_lookup_aux hLookup hScratch

/-- Cursors with the same live environment agree on every live binding. -/
theorem CoreCursor.planAgreesOn
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {leftScope rightScope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {leftBlock rightBlock : Functions.Block}
    {leftState rightState : AllocationLowering.State}
    {leftLocals rightLocals : Locals.Ctx}
    (left :
      CoreCursor root leftScope live leftBlock leftState leftLocals)
    (right :
      CoreCursor root rightScope live rightBlock rightState rightLocals)
    (hEnv :
      leftState.allocation.env = rightState.allocation.env) :
    PlanAgreesOn left.plan right.plan live := by
  rcases left.activeEnv with ⟨locals, hLeftEnv, hLive⟩
  have hLeftPlanning :
      left.planning.allocation.env =
        leftState.allocation.env :=
    congrArg AllocationSupport.CompileState.env
      left.planningAllocation
  have hRightPlanning :
      right.planning.allocation.env =
        rightState.allocation.env :=
    congrArg AllocationSupport.CompileState.env
      right.planningAllocation
  have hRightEnv :
      right.planning.allocation.env =
        locals ++ AllocationSupport.functionEnv root.slots := by
    calc
      right.planning.allocation.env =
          rightState.allocation.env := hRightPlanning
      _ = leftState.allocation.env := hEnv.symm
      _ = left.planning.allocation.env := hLeftPlanning.symm
      _ =
          locals ++ AllocationSupport.functionEnv root.slots :=
        hLeftEnv
  refine ⟨?_, ?_⟩
  · exact
      (left.currentStackOrder_of_active locals hLeftEnv hLive).trans
        (right.currentStackOrder_of_active
          locals hRightEnv hLive).symm
  · intro localName hLocalLive
    obtain ⟨slot, hLookup⟩ :=
      left.lookupSlot_of_live hLocalLive
    by_cases hStack :
        AllocationLowering.isStackSlot root.lowerCtx slot = true
    · obtain ⟨leftDepth, hLeftLocation⟩ :=
        left.location_stack_of_lookup hLookup hStack
      have hRightLookup :
          AllocationSupport.lookupSlot?
              localName rightState.allocation.env =
            some slot := by
        simpa [hEnv] using hLookup
      obtain ⟨rightDepth, hRightLocation⟩ :=
        right.location_stack_of_lookup hRightLookup hStack
      exact
        ⟨.stack leftDepth, .stack rightDepth,
          hLeftLocation, hRightLocation,
          .stack leftDepth rightDepth⟩
    · have hScratch :
          AllocationLowering.isStackSlot root.lowerCtx slot = false :=
        Bool.eq_false_of_not_eq_true hStack
      have hLeftLocation :=
        left.location_scratch_of_lookup hLookup hScratch
      have hRightLookup :
          AllocationSupport.lookupSlot?
              localName rightState.allocation.env =
            some slot := by
        simpa [hEnv] using hLookup
      have hRightLocation :=
        right.location_scratch_of_lookup hRightLookup hScratch
      exact
        ⟨.scratch slot, .scratch slot,
          hLeftLocation, hRightLocation, .scratch slot⟩

theorem CoreCursor.scratch_bound_of_location
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    {localName : Locals.Name} {slot : Nat}
    (hLocation :
      cursor.plan.location? localName = some (.scratch slot)) :
    slot < compilation.recipe.frameWords := by
  rw [cursor.planEq] at hLocation
  have hWF :
      (MixedAllocation.allocationOfState
        program.memoryContract compilation.recipe.frameWords
        (MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots scope
          cursor.finalState.allocation)
        cursor.finalState.allocation).WellFormed := by
    rw [← cursor.planEq]
    exact cursor.planWF
  exact
    MixedAllocation.allocationOfState_scratch_bound_of_wellFormed
      hWF hLocation

/-- Classify a declaration from its adjacent canonical cursor positions. -/
theorem CoreCursor.declarationPlacement
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {lowerState afterState : AllocationLowering.State}
    {localsCtx afterLocals : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .let_ name value :: rest } lowerState localsCtx)
    (tail :
      CoreCursor root scope (name :: live)
        { stmts := rest } afterState afterLocals)
    (hPlanning :
      tail.planning =
        AllocationSupport.planStmt scope cursor.planning
          (.let_ name value))
    (hPlan : tail.plan = cursor.plan) :
    DeclarationPlacement root.lowerCtx lowerState cursor.plan
      live name := by
  rcases cursor.currentStackOrder with
    ⟨locals, hCurrentEnv, hCurrentLive, hCurrentOrder⟩
  have hNext :
      cursor.planning.allocation.nextSlot =
        lowerState.allocation.nextSlot :=
    congrArg AllocationSupport.CompileState.nextSlot
      cursor.planningAllocation
  have hTailEnv :
      tail.planning.allocation.env =
      ((name, cursor.planning.allocation.nextSlot) :: locals) ++
        AllocationSupport.functionEnv root.slots := by
    calc
      tail.planning.allocation.env =
          (AllocationSupport.planStmt scope cursor.planning
            (.let_ name value)).allocation.env := by rw [hPlanning]
      _ =
          (name, cursor.planning.allocation.nextSlot) ::
            cursor.planning.allocation.env := by
              rw [AllocationSupport.planStmt_allocation_env]
      _ =
          ((name, cursor.planning.allocation.nextSlot) :: locals) ++
            AllocationSupport.functionEnv root.slots := by
              simp [hCurrentEnv]
  have hTailLive :
      ∀ localName,
        localName ∈ name :: live ↔
          localName ∈
            (((name, cursor.planning.allocation.nextSlot) :: locals).map
                Prod.fst) ++
              (root.slots.returns.map Prod.fst).reverse ++
              (root.slots.params.map Prod.fst).reverse := by
    intro localName
    simp [hCurrentLive]
  have hTailOrder :=
    tail.currentStackOrder_of_active
      ((name, cursor.planning.allocation.nextSlot) :: locals)
      hTailEnv hTailLive
  rw [hPlan] at hTailOrder
  have hLookupPlanning :
      AllocationSupport.lookupSlot? name
          tail.planning.allocation.env =
        some cursor.planning.allocation.nextSlot := by
    rw [hPlanning, AllocationSupport.planStmt_allocation_env]
    simp [AllocationSupport.lookupSlot?]
  have hLookupAfter :
      AllocationSupport.lookupSlot? name afterState.allocation.env =
        some lowerState.allocation.nextSlot := by
    rw [← tail.planningAllocation, ← hNext]
    exact hLookupPlanning
  cases hStack :
      AllocationLowering.isStackSlot root.lowerCtx
        lowerState.allocation.nextSlot with
  | true =>
      obtain ⟨planDepth, hLocation⟩ :=
        tail.location_stack_of_lookup_aux hLookupAfter hStack
      rw [hPlan] at hLocation
      have hSlotMem :
          lowerState.allocation.nextSlot ∈ compilation.stackSlots := by
        simpa [root.lowerCtxShared.stackSlots] using
          (AllocationLowering.isStackSlot_eq_true_iff
            root.lowerCtx lowerState.allocation.nextSlot).mp hStack
      have hConsOrder :
          MixedAllocation.stackOrder compilation.stackSlots
              ((name, lowerState.allocation.nextSlot) :: locals) =
            name ::
              MixedAllocation.stackOrder compilation.stackSlots locals := by
        simp [MixedAllocation.stackOrder, MixedAllocation.stackEntries,
          hSlotMem]
      refine .stack lowerState.allocation.nextSlot planDepth rfl hStack
        hLocation ?_
      calc
        AllocationInteractionRelation.currentStackOrder
            cursor.plan (name :: live) =
            MixedAllocation.stackOrder compilation.stackSlots
                ((name, cursor.planning.allocation.nextSlot) :: locals) ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse := hTailOrder
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                ((name, lowerState.allocation.nextSlot) :: locals) ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse := by rw [hNext]
        _ =
            name ::
              (MixedAllocation.stackOrder compilation.stackSlots locals ++
                MixedAllocation.stackOrder compilation.stackSlots
                    root.slots.returns.reverse ++
                MixedAllocation.stackOrder compilation.stackSlots
                    root.slots.params.reverse) := by
          rw [hConsOrder]
          simp [List.append_assoc]
        _ = name ::
            AllocationInteractionRelation.currentStackOrder
              cursor.plan live := by
          rw [hCurrentOrder]
  | false =>
      have hLocation :=
        tail.location_scratch_of_lookup_aux hLookupAfter hStack
      rw [hPlan] at hLocation
      have hSlotNotMem :
          lowerState.allocation.nextSlot ∉ compilation.stackSlots := by
        simpa [root.lowerCtxShared.stackSlots] using
          (AllocationLowering.isStackSlot_eq_false_iff
            root.lowerCtx lowerState.allocation.nextSlot).mp hStack
      have hConsOrder :
          MixedAllocation.stackOrder compilation.stackSlots
              ((name, lowerState.allocation.nextSlot) :: locals) =
            MixedAllocation.stackOrder compilation.stackSlots locals := by
        simp [MixedAllocation.stackOrder, MixedAllocation.stackEntries,
          hSlotNotMem]
      refine .scratch lowerState.allocation.nextSlot rfl hStack
        hLocation ?_
      calc
        AllocationInteractionRelation.currentStackOrder
            cursor.plan (name :: live) =
            MixedAllocation.stackOrder compilation.stackSlots
                ((name, cursor.planning.allocation.nextSlot) :: locals) ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse := hTailOrder
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                ((name, lowerState.allocation.nextSlot) :: locals) ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse := by rw [hNext]
        _ =
            MixedAllocation.stackOrder compilation.stackSlots locals ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse := by rw [hConsOrder]
        _ = AllocationInteractionRelation.currentStackOrder
            cursor.plan live := hCurrentOrder.symm

/-- Construct the exact post-declaration context selected by the real pass. -/
theorem CoreCursor.letContext
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {beforeMode : ActivationMode}
    {lowered : List Locals.Stmt}
    {compiled : List Expressions.Stmt}
    (cursor :
      CoreCursor root scope live
        { stmts := .let_ name value :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (name :: live)
        { stmts := rest } afterState afterLocals)
    (hPlanning :
      tail.planning =
        AllocationSupport.planStmt scope cursor.planning
          (.let_ name value))
    (hPlan : tail.plan = cursor.plan)
    (hBefore :
      AllocationContext.ActivationExprContext
        root.lowerCtx beforeState beforeLocals cursor.plan
        live beforeMode)
    (hLower :
      AllocationLowering.lowerStmt root.lowerCtx root.returns
          beforeState (.let_ name value) =
        some (lowered, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := lowered } =
        some (compiled, afterLocals)) :
    ∃ afterMode,
      AllocationContext.ActivationExprContext
          root.lowerCtx afterState afterLocals cursor.plan
          (name :: live) afterMode ∧
        AllocationContext.DeclarationModeTransition
          cursor.plan name beforeMode afterMode := by
  have hPlacement := cursor.declarationPlacement tail hPlanning hPlan
  have hNameFrame : name ≠ root.lowerCtx.frameName := by
    intro hEq
    apply tail.frameName_not_mem_live
    simp [hEq, root.lowerCtxShared.frameName]
  have hAfterSlot :
      ∀ localName, localName ∈ name :: live →
        ∃ slot,
          AllocationSupport.lookupSlot?
              localName afterState.allocation.env =
            some slot :=
    fun localName hLive => tail.lookupSlot_of_live hLive
  have hAfterStackLocation :
      ∀ localName slot,
        localName ∈ name :: live →
        AllocationSupport.lookupSlot?
            localName afterState.allocation.env =
          some slot →
        AllocationLowering.isStackSlot root.lowerCtx slot = true →
        ∃ planDepth,
          cursor.plan.location? localName =
            some (.stack planDepth) := by
    intro localName slot _hLive hLookup hStack
    have hLocation := tail.location_stack_of_lookup hLookup hStack
    rw [hPlan] at hLocation
    exact hLocation
  have hAfterScratchLocation :
      ∀ localName slot,
        localName ∈ name :: live →
        AllocationSupport.lookupSlot?
            localName afterState.allocation.env =
          some slot →
        AllocationLowering.isStackSlot root.lowerCtx slot = false →
        cursor.plan.location? localName = some (.scratch slot) := by
    intro localName slot _hLive hLookup hScratch
    have hLocation := tail.location_scratch_of_lookup hLookup hScratch
    rw [hPlan] at hLocation
    exact hLocation
  cases hPlacement with
  | stack slot planDepth hSlot hStack hLocation hOrder =>
      subst slot
      cases hLowerValue :
          AllocationLowering.lowerExpr root.lowerCtx beforeState value with
      | none =>
          simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
      | some loweredValue =>
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          cases hValueCode :
              Locals.Expr.compileCode beforeLocals 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hValueCode] at hCompile
          | some valueCode =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.codeStmt, hValueCode] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              cases hBefore with
              | stack hBeforeStack =>
                  have hAfterOnly :
                      LiveStackOnly cursor.plan (name :: live) := by
                    intro localName scratchSlot hLive hScratchLocation
                    rcases List.mem_cons.mp hLive with hHead | hTail
                    · subst localName
                      rw [hLocation] at hScratchLocation
                      simp at hScratchLocation
                    · exact
                        hBeforeStack.liveStackOnly
                          localName scratchSlot hTail hScratchLocation
                  have hAfterLocation :
                      ∀ localName, localName ∈ name :: live →
                        ∃ planDepth,
                          cursor.plan.location? localName =
                            some (.stack planDepth) := by
                    intro localName hLive
                    obtain ⟨localSlot, hLookup⟩ :=
                      hAfterSlot localName hLive
                    by_cases hLocalStack :
                        AllocationLowering.isStackSlot
                          root.lowerCtx localSlot = true
                    · exact
                        hAfterStackLocation localName localSlot hLive
                          hLookup hLocalStack
                    · have hLocalScratch :
                          AllocationLowering.isStackSlot
                              root.lowerCtx localSlot =
                            false :=
                        Bool.eq_false_of_not_eq_true hLocalStack
                      have hScratchLocation :=
                        hAfterScratchLocation localName localSlot hLive
                          hLookup hLocalScratch
                      exact
                        False.elim
                          (hAfterOnly localName localSlot hLive
                            hScratchLocation)
                  refine ⟨.stack, ?_, .stack planDepth hLocation⟩
                  apply
                    AllocationContext.ActivationExprContext.stack_of_layout
                      cursor.planWF
                  · simp [Locals.Ctx.withLayout, hBeforeStack.layout]
                  · simpa [hBeforeStack.stackOrder] using hOrder
                  · simp [Ne.symm hNameFrame, hBeforeStack.frameAbsent]
                  · exact hAfterOnly
                  · exact hAfterLocation
                  · exact hAfterSlot
              | @scratch frameDepth frameWords hBeforeScratch =>
                  refine
                    ⟨.scratch (frameDepth + 1) frameWords, ?_,
                      .stack planDepth hLocation⟩
                  apply
                    AllocationContext.ActivationExprContext.scratch_of_layout
                      cursor.planWF
                  · simp [Locals.Ctx.withLayout, hBeforeScratch.layout]
                  · rw [hBeforeScratch.bodyLayout]
                    simp [hOrder]
                  · rw [hOrder]
                    simp [hBeforeScratch.currentStackOrder_length]
                  · have hFrame :=
                      tail.frameName_not_mem_currentStackOrder
                    rw [hPlan] at hFrame
                    simpa [root.lowerCtxShared.frameName] using hFrame
                  · exact hAfterSlot
                  · exact hAfterStackLocation
                  · exact hAfterScratchLocation
  | scratch slot hSlot hStack hLocation hOrder =>
      subst slot
      cases hBefore with
      | stack hBeforeStack =>
          cases hLowerValue :
              AllocationLowering.lowerExpr
                root.lowerCtx beforeState value with
          | none =>
              simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
          | some loweredValue =>
              simp [AllocationLowering.lowerStmt, hLowerValue,
                AllocationSupport.allocateName, hStack,
                hBeforeStack.frameAbsent] at hLower
      | @scratch frameDepth frameWords hBeforeScratch =>
          cases hLowerValue :
              AllocationLowering.lowerExpr
                root.lowerCtx beforeState value with
          | none =>
              simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
          | some loweredValue =>
              have hFrameMember :
                  root.lowerCtx.frameName ∈ beforeState.layout :=
                Locals.Layout.mem_of_lookupDepth?_eq_some
                  hBeforeScratch.frame
              simp [AllocationLowering.lowerStmt, hLowerValue,
                AllocationSupport.allocateName, hStack,
                hFrameMember] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              cases hValueCode :
                  Locals.Expr.compileCode beforeLocals 0 loweredValue with
              | none =>
                  have hFrameLocals :
                      Locals.Layout.lookupDepth?
                          root.lowerCtx.frameName beforeLocals.layout =
                        some (frameDepth + 1) := by
                    rw [hBeforeScratch.layout]
                    exact hBeforeScratch.frame
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    AllocationLowering.scratchStoreExpr,
                    AllocationLowering.scratchAddressExpr,
                    AllocationLowering.exprSeqTwo,
                    Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                    hValueCode, hFrameLocals] at hCompile
              | some valueCode =>
                  have hFrameLocals :
                      Locals.Layout.lookupDepth?
                          root.lowerCtx.frameName beforeLocals.layout =
                        some (frameDepth + 1) := by
                    rw [hBeforeScratch.layout]
                    exact hBeforeScratch.frame
                  cases hDup :
                      Locals.StackOp.dup? (frameDepth + 2) with
                  | none =>
                      have hDup' :
                          Locals.StackOp.dup?
                              (1 + (frameDepth + 1)) = none := by
                        simpa [Nat.add_assoc, Nat.add_comm,
                          Nat.add_left_comm] using hDup
                      simp [Locals.Block.compileOpen,
                        Locals.Stmt.compile,
                        AllocationLowering.scratchStoreExpr,
                        AllocationLowering.scratchAddressExpr,
                        AllocationLowering.exprSeqTwo,
                        Locals.Expr.compileCode,
                        Locals.ExprSeq.compileCode,
                        hValueCode, hFrameLocals, hDup'] at hCompile
                  | some op =>
                      have hDup' :
                          Locals.StackOp.dup?
                              (1 + (frameDepth + 1)) = some op := by
                        simpa [Nat.add_assoc, Nat.add_comm,
                          Nat.add_left_comm] using hDup
                      have hStoreCode :=
                        AllocationLowering.scratchStoreExpr_compileCode
                          (frameName := root.lowerCtx.frameName)
                          (slot := beforeState.allocation.nextSlot)
                          (offset := 0) hValueCode hFrameLocals hDup'
                      simp only [Locals.Block.compileOpen,
                        Locals.Stmt.compile] at hCompile
                      rw [hStoreCode] at hCompile
                      simp [Locals.codeStmt] at hCompile
                      rcases hCompile with ⟨rfl, rfl⟩
                      refine
                        ⟨.scratch frameDepth frameWords, ?_,
                          .scratch frameDepth frameWords
                            beforeState.allocation.nextSlot hLocation⟩
                      apply
                        AllocationContext.ActivationExprContext.scratch_of_layout
                          cursor.planWF
                      · exact hBeforeScratch.layout
                      · rw [hOrder]
                        exact hBeforeScratch.bodyLayout
                      · rw [hOrder]
                        exact
                          hBeforeScratch.currentStackOrder_length.symm
                      · have hFrame :=
                          tail.frameName_not_mem_currentStackOrder
                        rw [hPlan] at hFrame
                        simpa [root.lowerCtxShared.frameName] using hFrame
                      · exact hAfterSlot
                      · exact hAfterStackLocation
                      · exact hAfterScratchLocation

/-- Build a cursor from any validated lexical planner entry. -/
theorem CoreCursor.lexicalOfPlanState
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {cursorLive nestedLive : List Functions.Name}
    {sourceBlock body : Functions.Block}
    {cursorLowerState lowerState openFinal : AllocationLowering.State}
    {planState : AllocationSupport.CompileState}
    {cursorLocalsCtx nestedLocalsCtx bodyLocals : Locals.Ctx}
    {lowered : Locals.Block}
    {bodyCode : List Expressions.Stmt}
    (_cursor :
      CoreCursor root scope cursorLive sourceBlock cursorLowerState
        cursorLocalsCtx)
    (lexicalScope : Locals.Allocation.ScopeId)
    (planning : AllocationSupport.PlanningState)
    (hPlanningAllocation :
      planning.allocation = lowerState.allocation)
    (hScopeRoot :
      MixedAllocation.AllocationRecipe.functionRoot? lexicalScope =
        root.functionRoot?)
    (hEntryRecipe :
      ({ scope := lexicalScope
         state := planState } :
        AllocationSupport.ScopedAllocation) ∈
        compilation.recipe.lexicalScopes)
    (hPlanEnv : planState.env = openFinal.allocation.env)
    (hInnerScopes :
      ∀ entry,
        entry ∈
            (AllocationSupport.planBlockOpen
              lexicalScope planning body).scopes →
          entry ∈ compilation.recipe.lexicalScopes)
    (hLower :
      AllocationLowering.lowerBlockOpen root.lowerCtx root.returns
          lowerState body =
        some (lowered, openFinal))
    (hCompile :
      Locals.Block.compileOpen nestedLocalsCtx lowered =
        some (bodyCode, bodyLocals))
    (hScoped : Functions.Scope.Block.Scoped nestedLive body)
    (hActiveEnv :
      ActiveEnv root.slots planning.allocation.env nestedLive) :
    ∃ nested :
        CoreCursor root lexicalScope nestedLive body lowerState
          nestedLocalsCtx,
      nested.lowered = lowered ∧
        nested.finalState = openFinal ∧
        nested.compiled = bodyCode ∧
        nested.finalLocals = bodyLocals := by
  let scopeEntry : AllocationSupport.ScopedAllocation :=
    { scope := lexicalScope
      state := planState }
  have hPlannedOpen :
      (AllocationSupport.planBlockOpen
        lexicalScope planning body).allocation =
        openFinal.allocation := by
    exact
      AllocationLowering.lowerBlockOpen_allocation_eq_planBlockOpen
        body lexicalScope planning root.lowerCtx root.returns
        lowerState openFinal lowered hPlanningAllocation hLower
  let plan :=
    MixedAllocation.allocationOfState
      program.memoryContract compilation.recipe.frameWords
      (MixedAllocation.AllocationRecipe.stackEntriesForScope
        compilation.recipe compilation.stackSlots lexicalScope planState)
      planState
  have hFind : allocation.find? lexicalScope = some plan := by
    have hEntryFind :=
      AllocationLowering.validatePlan?_lexical_entry_plan
        compilation.validate hEntryRecipe
    simpa [scopeEntry, plan] using hEntryFind
  have hPlanWF : plan.WellFormed :=
    Locals.Allocation.ProgramPlan.wellFormed_of_find?_eq_some
      (AllocationLowering.validatePlan?_sound compilation.validate).1
      hFind
  have hEntries :
      MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots lexicalScope planState =
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots lexicalScope
            openFinal.allocation :=
    MixedAllocation.AllocationRecipe.stackEntriesForScope_eq_of_env_eq
      hPlanEnv
  have hPlanEq :
      plan =
        MixedAllocation.allocationOfState
          program.memoryContract compilation.recipe.frameWords
          (MixedAllocation.AllocationRecipe.stackEntriesForScope
            compilation.recipe compilation.stackSlots lexicalScope
            openFinal.allocation)
          openFinal.allocation := by
    exact
      MixedAllocation.allocationOfState_eq_of_env_eq
        hEntries hPlanEnv
  let nested :
      CoreCursor root lexicalScope nestedLive body lowerState
        nestedLocalsCtx :=
    { planning := planning
      planningAllocation := hPlanningAllocation
      scopeRoot := hScopeRoot
      plan := plan
      planWF := hPlanWF
      finalState := openFinal
      finalLocals := bodyLocals
      planEq := hPlanEq
      finalFrameFresh := by
        have hFresh := root.lexicalFrameFresh _ hEntryRecipe
        rw [hPlanEnv] at hFresh
        simpa [scopeEntry] using hFresh
      plannedFinal := hPlannedOpen
      plannedScopes := hInnerScopes
      lowered := lowered
      compiled := bodyCode
      lower := hLower
      compile := hCompile
      sourceScoped := hScoped
      activeEnv := hActiveEnv }
  exact ⟨nested, rfl, rfl, rfl, rfl⟩

/-- Build a cursor whose lexical entry is the open block endpoint. -/
theorem CoreCursor.lexical
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {cursorLive nestedLive : List Functions.Name}
    {sourceBlock body : Functions.Block}
    {cursorLowerState lowerState openFinal : AllocationLowering.State}
    {cursorLocalsCtx nestedLocalsCtx bodyLocals : Locals.Ctx}
    {lowered : Locals.Block}
    {bodyCode : List Expressions.Stmt}
    (cursor :
      CoreCursor root scope cursorLive sourceBlock cursorLowerState
        cursorLocalsCtx)
    (lexicalScope : Locals.Allocation.ScopeId)
    (planning : AllocationSupport.PlanningState)
    (hPlanningAllocation :
      planning.allocation = lowerState.allocation)
    (hScopeRoot :
      MixedAllocation.AllocationRecipe.functionRoot? lexicalScope =
        root.functionRoot?)
    (hEntryRecipe :
      ({ scope := lexicalScope
         state :=
           (AllocationSupport.planBlockOpen
             lexicalScope planning body).allocation } :
        AllocationSupport.ScopedAllocation) ∈
        compilation.recipe.lexicalScopes)
    (hInnerScopes :
      ∀ entry,
        entry ∈
            (AllocationSupport.planBlockOpen
              lexicalScope planning body).scopes →
          entry ∈ compilation.recipe.lexicalScopes)
    (hLower :
      AllocationLowering.lowerBlockOpen root.lowerCtx root.returns
          lowerState body =
        some (lowered, openFinal))
    (hCompile :
      Locals.Block.compileOpen nestedLocalsCtx lowered =
        some (bodyCode, bodyLocals))
    (hScoped : Functions.Scope.Block.Scoped nestedLive body)
    (hActiveEnv :
      ActiveEnv root.slots planning.allocation.env nestedLive) :
    ∃ nested :
        CoreCursor root lexicalScope nestedLive body lowerState
          nestedLocalsCtx,
      nested.lowered = lowered ∧
        nested.finalState = openFinal ∧
        nested.compiled = bodyCode ∧
        nested.finalLocals = bodyLocals :=
  cursor.lexicalOfPlanState lexicalScope planning
    hPlanningAllocation hScopeRoot hEntryRecipe
    (by
      exact congrArg AllocationSupport.CompileState.env
        (AllocationLowering.lowerBlockOpen_allocation_eq_planBlockOpen
          body lexicalScope planning root.lowerCtx root.returns
          lowerState openFinal lowered hPlanningAllocation hLower))
    hInnerScopes hLower hCompile hScoped hActiveEnv

/-- Build the cursor for one immediate compiler-scoped source block. -/
theorem CoreCursor.scoped
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {body : Functions.Block}
    {lowerState scopedFinal : AllocationLowering.State}
    {localsCtx bodyLocals : Locals.Ctx}
    {lowered : Locals.Block}
    {bodyCode : List Expressions.Stmt}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        lowerState localsCtx)
    (hPlanning :
      AllocationSupport.planStmt scope cursor.planning stmt =
        AllocationSupport.planBlockScoped scope cursor.planning body)
    (hLower :
      AllocationLowering.lowerBlockScoped root.lowerCtx root.returns
          lowerState body =
        some (lowered, scopedFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx lowered =
        some (bodyCode, bodyLocals))
    (hScoped : Functions.Scope.Block.Scoped live body) :
    ∃ nested :
        CoreCursor root (.lexical scope cursor.planning.nextScope)
          live body lowerState localsCtx,
      nested.compiled = bodyCode ∧
        nested.finalLocals = bodyLocals := by
  obtain ⟨openFinal, hOpen, _hScopedEnv, _hScopedNext,
      _hScopedLayout⟩ :=
    AllocationLowering.lowerBlockScoped_components hLower
  let lexicalScope : Locals.Allocation.ScopeId :=
    .lexical scope cursor.planning.nextScope
  let entered : AllocationSupport.PlanningState :=
    { cursor.planning with
      nextScope := cursor.planning.nextScope + 1 }
  let scopeEntry : AllocationSupport.ScopedAllocation :=
    { scope := lexicalScope
      state :=
        (AllocationSupport.planBlockOpen
          lexicalScope entered body).allocation }
  have hEntryHead :
      scopeEntry ∈
        (AllocationSupport.planStmt
          scope cursor.planning stmt).scopes := by
    rw [hPlanning]
    exact
      AllocationSupport.planBlockScoped_entry_mem
        body scope cursor.planning
  have hEntryFinal :
      scopeEntry ∈
        (AllocationSupport.planBlockOpen scope cursor.planning
          { stmts := stmt :: rest }).scopes := by
    simp only [AllocationSupport.planBlockOpen,
      AllocationSupport.planStmtList]
    exact
      AllocationSupport.mem_planStmtList_scopes_of_mem
        rest scope
        (AllocationSupport.planStmt scope cursor.planning stmt)
        hEntryHead
  have hEntryRecipe :
      scopeEntry ∈ compilation.recipe.lexicalScopes :=
    cursor.plannedScopes scopeEntry hEntryFinal
  have hInnerScopes :
      ∀ entry,
        entry ∈
            (AllocationSupport.planBlockOpen
              lexicalScope entered body).scopes →
          entry ∈ compilation.recipe.lexicalScopes := by
    intro entry hEntry
    have hScopedEntry :
        entry ∈
          (AllocationSupport.planBlockScoped
            scope cursor.planning body).scopes :=
      AllocationSupport.mem_planBlockScoped_scopes_of_open_mem
        body scope cursor.planning hEntry
    have hHeadEntry :
        entry ∈
          (AllocationSupport.planStmt
            scope cursor.planning stmt).scopes := by
      rw [hPlanning]
      exact hScopedEntry
    apply cursor.plannedScopes entry
    simp only [AllocationSupport.planBlockOpen,
      AllocationSupport.planStmtList]
    exact
      AllocationSupport.mem_planStmtList_scopes_of_mem
        rest scope
        (AllocationSupport.planStmt scope cursor.planning stmt)
        hHeadEntry
  obtain ⟨nested, _hLowered, _hFinalState, hCode, hLocals⟩ :=
    cursor.lexical lexicalScope entered
      (by simpa [entered] using cursor.planningAllocation)
      (by
        simpa [lexicalScope,
          MixedAllocation.AllocationRecipe.functionRoot?] using
          cursor.scopeRoot)
      (by simpa [scopeEntry] using hEntryRecipe)
      hInnerScopes hOpen hCompile hScoped
      (by simpa [entered] using cursor.activeEnv)
  exact ⟨nested, hCode, hLocals⟩

/-- Decompose a lexical block into its body cursor and exact outer tail. -/
theorem CoreCursor.blockCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .block body :: rest } lowerState localsCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetBlock : Expressions.Block,
      ∃ bodyCursor :
        CoreCursor root (.lexical scope cursor.planning.nextScope)
          live body lowerState localsCtx,
        cursor.compiled = headCode ++ tail.compiled ∧
          headCode = targetBlock.stmts ∧
          Locals.finishScoped
              localsCtx bodyCursor.finalLocals bodyCursor.compiled =
            some targetBlock ∧
          afterState.allocation.env =
            lowerState.allocation.env ∧
          afterState.layout = lowerState.layout ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.block body) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScopedStmt⟩ :=
    cursor.cons
  obtain ⟨loweredBody, hLowerBody, hHeadLower⟩ :=
    AllocationLowering.lowerStmt_block_components hLower
  have hHeadCompile := hCompile
  rw [hHeadLower] at hCompile
  have hStmtCompile :=
    Locals.Block.compileOpen_single_components hCompile
  obtain
      ⟨bodyCode, bodyLocals, targetBlock,
        hBodyCompile, hFinish, hHeadCode, hAfterLocals⟩ :=
    Locals.Stmt.compile_block_components hStmtCompile
  have hBodyScoped :
      Functions.Scope.Block.Scoped live body := by
    simpa [Functions.Scope.Stmt.Scoped] using hScopedStmt
  have hBodyCursor :=
    cursor.scoped
      (stmt := .block body)
      (body := body)
      (by simp [AllocationSupport.planStmt])
      hLowerBody hBodyCompile hBodyScoped
  rcases hBodyCursor with
    ⟨bodyCursor, hBodyCode, hBodyLocals⟩
  have hAfterShape :=
    AllocationLowering.lowerBlockScoped_state_shape hLowerBody
  cases hAfterLocals
  refine
    ⟨afterState, headCode, tail, targetBlock, bodyCursor,
      hCompiled, hHeadCode, ?_, hAfterShape.1, hAfterShape.2,
      StepTransport.of_compilers hScopedStmt hLower hHeadCompile,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩
  rw [hBodyCode, hBodyLocals]
  exact hFinish

/-- Decompose an `if` into its condition, body cursor, and exact tail. -/
theorem CoreCursor.ifCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx) :
    ∃ afterState headLower headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ loweredCond condCode targetBody,
      ∃ bodyCursor :
        CoreCursor root (.lexical scope cursor.planning.nextScope)
          live body lowerState localsCtx,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationLowering.lowerStmt root.lowerCtx root.returns
              lowerState (.if_ cond body) =
            some (headLower, afterState) ∧
          Locals.Block.compileOpen localsCtx { stmts := headLower } =
            some (headCode, localsCtx) ∧
          headCode =
            [Expressions.Stmt.if_
              (Expressions.Expr.code condCode) targetBody] ∧
          AllocationLowering.lowerExpr root.lowerCtx lowerState cond =
            some loweredCond ∧
          Locals.Expr.compileCode localsCtx 0 loweredCond =
            some condCode ∧
          Locals.finishScoped
              localsCtx bodyCursor.finalLocals bodyCursor.compiled =
            some targetBody ∧
          afterState.allocation.env =
            lowerState.allocation.env ∧
          afterState.layout = lowerState.layout ∧
          Functions.Scope.ExprScoped live cond ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScopedStmt⟩ :=
    cursor.cons
  obtain
      ⟨loweredCond, loweredBody, hLowerCond, hLowerBody, hHeadLower⟩ :=
    AllocationLowering.lowerStmt_if_components hLower
  have hHeadCompile := hCompile
  rw [hHeadLower] at hCompile
  obtain
      ⟨condCode, bodyCode, bodyLocals, targetBody,
        hCompileCond, hCompileBody, hFinish, hHeadCode,
        hAfterLocals⟩ :=
    Locals.Block.compileOpen_single_if_components hCompile
  have hScoped :
      Functions.Scope.ExprScoped live cond ∧
        Functions.Scope.Block.Scoped live body := by
    simpa [Functions.Scope.Stmt.Scoped] using hScopedStmt
  obtain ⟨bodyCursor, hBodyCode, hBodyLocals⟩ :=
    cursor.scoped
      (stmt := .if_ cond body)
      (body := body)
      (by simp [AllocationSupport.planStmt])
      hLowerBody hCompileBody hScoped.2
  have hAfterShape :=
    AllocationLowering.lowerBlockScoped_state_shape hLowerBody
  cases hAfterLocals
  refine
    ⟨afterState, headLower, headCode, tail, loweredCond, condCode,
      targetBody, bodyCursor, hCompiled, hLower, ?_, hHeadCode, hLowerCond,
      hCompileCond, ?_, hAfterShape.1, hAfterShape.2, hScoped.1,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩
  · simpa using hHeadCompile
  rw [hBodyCode, hBodyLocals]
  exact hFinish

/-- Compiler-owned adjacent components of one source `switch`. -/
structure CoreCursor.SwitchComponents
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (afterState : AllocationLowering.State)
    (headLower : List Locals.Stmt)
    (headCode : List Expressions.Stmt)
    (tail :
      CoreCursor root scope live { stmts := rest } afterState localsCtx)
    (loweredScrutinee : Locals.Expr 1)
    (loweredCases : List (Word × Locals.Block))
    (afterCases : AllocationLowering.State)
    (loweredDefault : Option Locals.Block)
    (scrutineeCode : Structured.Code)
    (compiledCases : List (Word × Expressions.Block))
    (compiledDefault : Option Expressions.Block) : Prop where
  compiled : cursor.compiled = headCode ++ tail.compiled
  lower :
    AllocationLowering.lowerStmt root.lowerCtx root.returns lowerState
        (.switch scrutinee cases defaultBody) =
      some (headLower, afterState)
  compile :
    Locals.Block.compileOpen localsCtx { stmts := headLower } =
      some (headCode, localsCtx)
  lowerHead :
    headLower =
      [.switch loweredScrutinee loweredCases loweredDefault]
  lowerScrutinee :
    AllocationLowering.lowerExpr root.lowerCtx lowerState scrutinee =
      some loweredScrutinee
  lowerCases :
    AllocationLowering.lowerCases root.lowerCtx root.returns lowerState cases =
      some (loweredCases, afterCases)
  lowerDefault :
    AllocationLowering.lowerDefault root.lowerCtx root.returns afterCases
        defaultBody =
      some (loweredDefault, afterState)
  codeHead :
    headCode =
      [.switch (.code scrutineeCode) compiledCases compiledDefault]
  compileScrutinee :
    Locals.Expr.compileCode localsCtx 0 loweredScrutinee =
      some scrutineeCode
  compileCases :
    Locals.CaseList.compile localsCtx loweredCases = some compiledCases
  compileDefault :
    Locals.Default.compile localsCtx loweredDefault = some compiledDefault
  afterEnv : afterState.allocation.env = lowerState.allocation.env
  afterLayout : afterState.layout = lowerState.layout
  scrutineeScoped : Functions.Scope.ExprScoped live scrutinee
  casesScoped : Functions.Scope.CaseList.Scoped live cases
  defaultScoped : Functions.Scope.Default.Scoped live defaultBody
  exactTail : ExactTail cursor tail

/-- Decompose a `switch` through the real lowerer and Locals compiler. -/
theorem CoreCursor.switchCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx) :
    ∃ afterState headLower headCode,
    ∃ tail :
      CoreCursor root scope live { stmts := rest } afterState localsCtx,
    ∃ loweredScrutinee loweredCases afterCases loweredDefault,
    ∃ scrutineeCode compiledCases compiledDefault,
      SwitchComponents cursor afterState headLower headCode tail
        loweredScrutinee loweredCases afterCases loweredDefault
        scrutineeCode compiledCases compiledDefault := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScopedStmt⟩ :=
    cursor.cons
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        hLowerScrutinee, hLowerCases, hLowerDefault, hHeadLower⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  have hHeadCompile := hCompile
  rw [hHeadLower] at hCompile
  obtain
      ⟨scrutineeCode, compiledCases, compiledDefault,
        hCompileScrutinee, hCompileCases, hCompileDefault,
        hHeadCode, hAfterLocals⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  have hScoped :
      Functions.Scope.ExprScoped live scrutinee ∧
        Functions.Scope.CaseList.Scoped live cases ∧
        Functions.Scope.Default.Scoped live defaultBody := by
    simpa [Functions.Scope.Stmt.Scoped] using hScopedStmt
  have hCasesShape :=
    AllocationLowering.lowerCases_state_shape hLowerCases
  have hDefaultShape :=
    AllocationLowering.lowerDefault_state_shape hLowerDefault
  cases hAfterLocals
  exact
    ⟨afterState, headLower, headCode, tail, loweredScrutinee,
      loweredCases, afterCases, loweredDefault, scrutineeCode,
      compiledCases, compiledDefault,
    { compiled := hCompiled
      lower := hLower
      compile := hHeadCompile
      lowerHead := hHeadLower
      lowerScrutinee := hLowerScrutinee
      lowerCases := hLowerCases
      lowerDefault := hLowerDefault
      codeHead := hHeadCode
      compileScrutinee := hCompileScrutinee
      compileCases := hCompileCases
      compileDefault := hCompileDefault
      afterEnv := hDefaultShape.1.trans hCasesShape.1
      afterLayout := hDefaultShape.2.trans hCasesShape.2
      scrutineeScoped := hScoped.1
      casesScoped := hScoped.2.1
      defaultScoped := hScoped.2.2
      exactTail :=
        ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩ }⟩

/-- Lift an already-selected switch planner entry into a lexical cursor. -/
theorem CoreCursor.switchSelectedCursorOfComponents
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {selected : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState selectedStart bodyFinal : AllocationLowering.State}
    {localsCtx bodyLocals : Locals.Ctx}
    {selectedPlanning : AllocationSupport.PlanningState}
    {selectedLowered : Locals.Block}
    {selectedCode : List Expressions.Stmt}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hSelectedPlanning :
      selectedPlanning.allocation = selectedStart.allocation)
    (hSelectedEnv :
      selectedStart.allocation.env = lowerState.allocation.env)
    (hSelectedEntry :
      ({ scope := .lexical scope selectedPlanning.nextScope
         state :=
           (AllocationSupport.planBlockOpen
             (.lexical scope selectedPlanning.nextScope)
             { selectedPlanning with
               nextScope := selectedPlanning.nextScope + 1 }
             selected).allocation } :
        AllocationSupport.ScopedAllocation) ∈
        (AllocationSupport.planDefault scope
          (AllocationSupport.planCases scope cursor.planning cases)
          defaultBody).scopes)
    (hSelectedInner :
      ∀ entry,
        entry ∈
            (AllocationSupport.planBlockOpen
              (.lexical scope selectedPlanning.nextScope)
              { selectedPlanning with
                nextScope := selectedPlanning.nextScope + 1 }
              selected).scopes →
          entry ∈
            (AllocationSupport.planDefault scope
              (AllocationSupport.planCases scope cursor.planning cases)
              defaultBody).scopes)
    (hLowerBody :
      AllocationLowering.lowerBlockOpen root.lowerCtx root.returns
          selectedStart selected =
        some (selectedLowered, bodyFinal))
    (hCompileSelected :
      Locals.Block.compileOpen localsCtx selectedLowered =
        some (selectedCode, bodyLocals))
    (hSelectedScoped :
      Functions.Scope.Block.Scoped live selected) :
    ∃ bodyCursor :
        CoreCursor root
          (.lexical scope selectedPlanning.nextScope)
          live selected selectedStart localsCtx,
      bodyCursor.lowered = selectedLowered ∧
        bodyCursor.finalState = bodyFinal ∧
        bodyCursor.compiled = selectedCode ∧
        bodyCursor.finalLocals = bodyLocals := by
  let lexicalScope : Locals.Allocation.ScopeId :=
    .lexical scope selectedPlanning.nextScope
  let entered : AllocationSupport.PlanningState :=
    { selectedPlanning with
      nextScope := selectedPlanning.nextScope + 1 }
  let scopeEntry : AllocationSupport.ScopedAllocation :=
    { scope := lexicalScope
      state :=
        (AllocationSupport.planBlockOpen
          lexicalScope entered selected).allocation }
  have hEntryHead :
      scopeEntry ∈
        (AllocationSupport.planStmt scope cursor.planning
          (.switch scrutinee cases defaultBody)).scopes := by
    simpa [AllocationSupport.planStmt, scopeEntry, lexicalScope,
      entered] using hSelectedEntry
  have hEntryFinal :
      scopeEntry ∈
        (AllocationSupport.planBlockOpen scope cursor.planning
          { stmts :=
              .switch scrutinee cases defaultBody :: rest }).scopes := by
    simp only [AllocationSupport.planBlockOpen,
      AllocationSupport.planStmtList]
    exact
      AllocationSupport.mem_planStmtList_scopes_of_mem
        rest scope
        (AllocationSupport.planStmt scope cursor.planning
          (.switch scrutinee cases defaultBody))
        hEntryHead
  have hEntryRecipe :
      scopeEntry ∈ compilation.recipe.lexicalScopes :=
    cursor.plannedScopes scopeEntry hEntryFinal
  have hInnerScopes :
      ∀ entry,
        entry ∈
            (AllocationSupport.planBlockOpen
              lexicalScope entered selected).scopes →
          entry ∈ compilation.recipe.lexicalScopes := by
    intro entry hEntry
    have hSwitchEntry :
        entry ∈
          (AllocationSupport.planStmt scope cursor.planning
            (.switch scrutinee cases defaultBody)).scopes := by
      simpa [AllocationSupport.planStmt, lexicalScope, entered] using
        hSelectedInner entry hEntry
    apply cursor.plannedScopes entry
    simp only [AllocationSupport.planBlockOpen,
      AllocationSupport.planStmtList]
    exact
      AllocationSupport.mem_planStmtList_scopes_of_mem
        rest scope
        (AllocationSupport.planStmt scope cursor.planning
          (.switch scrutinee cases defaultBody))
        hSwitchEntry
  have hSelectedActive :
      ActiveEnv root.slots selectedPlanning.allocation.env live := by
    rcases cursor.activeEnv with ⟨locals, hEnv, hLive⟩
    refine ⟨locals, ?_, hLive⟩
    calc
      selectedPlanning.allocation.env =
          selectedStart.allocation.env :=
        congrArg AllocationSupport.CompileState.env hSelectedPlanning
      _ = lowerState.allocation.env := hSelectedEnv
      _ = cursor.planning.allocation.env :=
        (congrArg AllocationSupport.CompileState.env
          cursor.planningAllocation).symm
      _ =
          locals ++ AllocationSupport.functionEnv root.slots := hEnv
  exact
    cursor.lexical lexicalScope entered
      (by simpa [entered] using hSelectedPlanning)
      (by
        simpa [lexicalScope,
          MixedAllocation.AllocationRecipe.functionRoot?] using
          cursor.scopeRoot)
      (by simpa [scopeEntry] using hEntryRecipe)
      hInnerScopes hLowerBody hCompileSelected hSelectedScoped
      (by simpa [entered] using hSelectedActive)

/-- Decompose a semantically selected switch branch and preserve its tail. -/
theorem CoreCursor.switchSelectedCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {selected : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody =
        some selected) :
    ∃ afterState headLower headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ scrutineeCode compiledCases compiledDefault,
      ∃ selectedStart,
      ∃ selectedPlanning : AllocationSupport.PlanningState,
      ∃ selectedTarget : Expressions.Block,
      ∃ bodyCursor :
        CoreCursor root
          (.lexical scope selectedPlanning.nextScope)
          live selected selectedStart localsCtx,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationLowering.lowerStmt root.lowerCtx root.returns
              lowerState (.switch scrutinee cases defaultBody) =
            some (headLower, afterState) ∧
          Locals.Block.compileOpen localsCtx { stmts := headLower } =
            some (headCode, localsCtx) ∧
          headCode =
            [.switch (.code scrutineeCode) compiledCases compiledDefault] ∧
          Expressions.EffectSemantics.Switch.select value compiledCases
              compiledDefault =
            some selectedTarget ∧
          Locals.finishScoped localsCtx bodyCursor.finalLocals
              bodyCursor.compiled =
            some selectedTarget ∧
          selectedStart.allocation.env = lowerState.allocation.env ∧
          selectedStart.layout = lowerState.layout ∧
          afterState.allocation.env = lowerState.allocation.env ∧
          afterState.layout = lowerState.layout ∧
          Functions.Scope.ExprScoped live scrutinee ∧
          Functions.Scope.Block.Scoped live selected ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hTailPlanning, hTailPlan, hTailFinalState, hTailFinalLocals,
        hLower, hCompile, _hLowered, hCompiled, hScopedStmt⟩ :=
    cursor.cons
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        _hLowerScrutinee, hLowerCases, hLowerDefault, hHeadLower⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  obtain
      ⟨selectedLowered, selectedStart, selectedScopedFinal,
        selectedPlanning, hLoweredSelect, hLowerSelected,
        hSelectedPlanning, hSelectedEnv, hSelectedLayout,
        hSelectedEntry, hSelectedInner⟩ :=
    AllocationLowering.lowerSwitch_select_some_planning
      cursor.planningAllocation hLowerCases hLowerDefault hSelect
  obtain
      ⟨openFinal, hLowerBody, _hScopedEnv, _hScopedNext,
        _hScopedLayout⟩ :=
    AllocationLowering.lowerBlockScoped_components hLowerSelected
  have hHeadCompile := hCompile
  rw [hHeadLower] at hCompile
  obtain
      ⟨scrutineeCode, compiledCases, compiledDefault,
        _hCompileScrutinee, hCompileCases, hCompileDefault,
        hHeadCode, hAfterLocals⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  have hSelectedRel :=
    Locals.InteractionPreservation.Stmt.SwitchCompile.selectedRel_of_compile
      localsCtx value hCompileCases hCompileDefault
  rw [hLoweredSelect] at hSelectedRel
  obtain
      ⟨selectedTarget, selectedCode, selectedLocals, hTargetSelect,
        hCompileSelected, hFinishSelected⟩ :=
    hSelectedRel.some_parts
  have hScoped :
      Functions.Scope.ExprScoped live scrutinee ∧
        Functions.Scope.CaseList.Scoped live cases ∧
        Functions.Scope.Default.Scoped live defaultBody := by
    simpa [Functions.Scope.Stmt.Scoped] using hScopedStmt
  have hSelectedScoped :
      Functions.Scope.Block.Scoped live selected :=
    Functions.Source.Switch.scoped_of_select_some
      hScoped.2.1 hScoped.2.2 hSelect
  obtain
      ⟨bodyCursor, _hBodyLowered, _hBodyFinal, hBodyCode,
        hBodyLocals⟩ :=
    cursor.switchSelectedCursorOfComponents
      hSelectedPlanning hSelectedEnv hSelectedEntry hSelectedInner
      hLowerBody hCompileSelected hSelectedScoped
  have hCasesShape :=
    AllocationLowering.lowerCases_state_shape hLowerCases
  have hDefaultShape :=
    AllocationLowering.lowerDefault_state_shape hLowerDefault
  cases hAfterLocals
  refine
    ⟨afterState, headLower, headCode, tail, scrutineeCode,
      compiledCases, compiledDefault, selectedStart, selectedPlanning,
      selectedTarget, bodyCursor, hCompiled, hLower,
      hHeadCompile, hHeadCode, hTargetSelect, ?_, hSelectedEnv,
      hSelectedLayout,
      hDefaultShape.1.trans hCasesShape.1,
      hDefaultShape.2.trans hCasesShape.2, hScoped.1,
      hSelectedScoped,
      ⟨hTailPlan, hTailFinalState, hTailFinalLocals,
        ⟨headCode, hCompiled⟩⟩⟩
  rw [hBodyCode, hBodyLocals]
  exact hFinishSelected

/-- Decompose a `for` into its loop-scope, post/body cursors, and tail. -/
theorem CoreCursor.forCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx) :
    ∃ afterState headLower headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest } afterState localsCtx,
      ∃ loopState afterPost afterBody : AllocationLowering.State,
      ∃ initLocals _postLocals _bodyLocals : Locals.Ctx,
      ∃ loweredCond condCode compiledPost compiledBody cleanup,
      let loopLive := Functions.Scope.Block.outEnv live init
      let loopScope :=
        Locals.Allocation.ScopeId.lexical scope cursor.planning.nextScope
      let entered : AllocationSupport.PlanningState :=
        { cursor.planning with
          nextScope := cursor.planning.nextScope + 1 }
      let initPlanning :=
        AllocationSupport.planBlockOpen loopScope entered init
      let postPlanning :=
        AllocationSupport.planBlockScoped loopScope initPlanning post
      ∃ initCursor :
          CoreCursor root loopScope live init lowerState
            localsCtx.withoutLoopControl,
      ∃ postCursor :
          CoreCursor root
            (.lexical loopScope initPlanning.nextScope)
            loopLive post loopState initLocals.withoutLoopControl,
      ∃ bodyCursor :
          CoreCursor root
            (.lexical loopScope postPlanning.nextScope)
            loopLive body afterPost
              (initLocals.withLoopControl initLocals.layout.length),
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationLowering.lowerStmt root.lowerCtx root.returns
              lowerState (.for_ init cond post body) =
            some (headLower, afterState) ∧
          Locals.Block.compileOpen localsCtx { stmts := headLower } =
            some (headCode, localsCtx) ∧
          initCursor.finalState = loopState ∧
          initCursor.finalLocals = initLocals ∧
          AllocationLowering.lowerExpr root.lowerCtx loopState cond =
            some loweredCond ∧
          Locals.Expr.compileCode initLocals 0 loweredCond =
            some condCode ∧
          AllocationLowering.lowerBlockScoped root.lowerCtx root.returns
              loopState post =
            some (postCursor.lowered, afterPost) ∧
          Locals.finishScoped initLocals.withoutLoopControl
              postCursor.finalLocals postCursor.compiled =
            some compiledPost ∧
          AllocationLowering.lowerBlockScoped root.lowerCtx root.returns
              afterPost body =
            some (bodyCursor.lowered, afterBody) ∧
          Locals.finishScoped
              (initLocals.withLoopControl initLocals.layout.length)
              bodyCursor.finalLocals bodyCursor.compiled =
            some compiledBody ∧
          initLocals.cleanupTo? localsCtx.layout.length = some cleanup ∧
          headCode =
            [Expressions.Stmt.for_
              { stmts := initCursor.compiled }
              (Expressions.Expr.code condCode)
              compiledPost compiledBody] ++
              Locals.codeStmt cleanup ∧
          afterState =
            { allocation :=
                { env := lowerState.allocation.env
                  nextSlot := afterBody.allocation.nextSlot }
              layout := lowerState.layout } ∧
          Functions.Scope.ExprScoped loopLive cond ∧
          Functions.Scope.Block.Scoped loopLive post ∧
          Functions.Scope.Block.Scoped loopLive body ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.for_ init cond post body) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hTailPlanning, hTailPlan, hTailFinalState, hTailFinalLocals,
        hLower, hCompile, _hLowered, hCompiled, hScopedStmt⟩ :=
    cursor.cons
  obtain
      ⟨loweredInit, loopState, loweredCond, loweredPost, afterPost,
        loweredBody, afterBody, hLowerInit, hLowerCond, hLowerPost,
        hLowerBody, hHeadLower, hAfterState, hPlanningComponents⟩ :=
    AllocationLowering.lowerStmt_for_planning_components
      (current := scope) cursor.planningAllocation hLower
  let loopLive := Functions.Scope.Block.outEnv live init
  let loopScope :=
    Locals.Allocation.ScopeId.lexical scope cursor.planning.nextScope
  let entered : AllocationSupport.PlanningState :=
    { cursor.planning with
      nextScope := cursor.planning.nextScope + 1 }
  let initPlanning :=
    AllocationSupport.planBlockOpen loopScope entered init
  let postPlanning :=
    AllocationSupport.planBlockScoped loopScope initPlanning post
  let bodyPlanning :=
    AllocationSupport.planBlockScoped loopScope postPlanning body
  have hPlanningComponents' :
      initPlanning.allocation = loopState.allocation ∧
        postPlanning.allocation = afterPost.allocation ∧
        bodyPlanning.allocation = afterBody.allocation := by
    simpa [loopScope, entered, initPlanning, postPlanning,
      bodyPlanning] using hPlanningComponents
  have hInitPlanning := hPlanningComponents'.1
  have hPostPlanning := hPlanningComponents'.2.1
  have hBodyPlanning := hPlanningComponents'.2.2
  have hHeadCompile := hCompile
  rw [hHeadLower] at hCompile
  obtain
      ⟨initCode, initLocals, condCode,
        postCode, postLocals, compiledPost,
        bodyCode, bodyLocals, compiledBody, cleanup,
        hCompileInit, hCompileCond, hCompilePost, hFinishPost,
        hCompileBody, hFinishBody, hCleanup, hHeadCode,
        hAfterLocals⟩ :=
    Locals.Block.compileOpen_single_for_components hCompile
  have hScoped :
      Functions.Scope.Block.Scoped live init ∧
        Functions.Scope.ExprScoped loopLive cond ∧
        Functions.Scope.Block.Scoped loopLive post ∧
        Functions.Scope.Block.Scoped loopLive body := by
    simpa [Functions.Scope.Stmt.Scoped, loopLive] using hScopedStmt
  have hPostShape :=
    AllocationLowering.lowerBlockScoped_state_shape hLowerPost
  have hBodyShape :=
    AllocationLowering.lowerBlockScoped_state_shape hLowerBody
  obtain ⟨postAdded, hPostScopes⟩ :=
    AllocationSupport.planBlockScoped_scopes_extension
      post loopScope initPlanning
  obtain ⟨bodyAdded, hBodyScopes⟩ :=
    AllocationSupport.planBlockScoped_scopes_extension
      body loopScope postPlanning
  let loopEntry : AllocationSupport.ScopedAllocation :=
    { scope := loopScope
      state := bodyPlanning.allocation }
  have hHeadLoopEntry :
      loopEntry ∈
        (AllocationSupport.planStmt scope cursor.planning
          (.for_ init cond post body)).scopes := by
    simp [AllocationSupport.planStmt, loopEntry, loopScope, entered,
      initPlanning, postPlanning, bodyPlanning]
  have hHeadBodyScope :
      ∀ entry,
        entry ∈ bodyPlanning.scopes →
          entry ∈
            (AllocationSupport.planStmt scope cursor.planning
              (.for_ init cond post body)).scopes := by
    intro entry hEntry
    simp [AllocationSupport.planStmt, loopScope, entered,
      initPlanning, postPlanning, bodyPlanning, hEntry]
  have hHeadScopeRecipe :
      ∀ entry,
        entry ∈
            (AllocationSupport.planStmt scope cursor.planning
              (.for_ init cond post body)).scopes →
          entry ∈ compilation.recipe.lexicalScopes := by
    intro entry hEntry
    apply cursor.plannedScopes entry
    simp only [AllocationSupport.planBlockOpen,
      AllocationSupport.planStmtList]
    exact
      AllocationSupport.mem_planStmtList_scopes_of_mem
        rest scope
        (AllocationSupport.planStmt scope cursor.planning
          (.for_ init cond post body))
        hEntry
  have hLoopEntryRecipe :
      loopEntry ∈ compilation.recipe.lexicalScopes :=
    hHeadScopeRecipe loopEntry hHeadLoopEntry
  have hBodyScopesRecipe :
      ∀ entry,
        entry ∈ bodyPlanning.scopes →
          entry ∈ compilation.recipe.lexicalScopes :=
    fun entry hEntry =>
      hHeadScopeRecipe entry (hHeadBodyScope entry hEntry)
  have hInitScopesRecipe :
      ∀ entry,
        entry ∈ initPlanning.scopes →
          entry ∈ compilation.recipe.lexicalScopes := by
    intro entry hEntry
    apply hBodyScopesRecipe entry
    rw [hBodyScopes, hPostScopes]
    simp [hEntry]
  have hPostScopesRecipe :
      ∀ entry,
        entry ∈
            (AllocationSupport.planBlockOpen
              (.lexical loopScope initPlanning.nextScope)
              { initPlanning with
                nextScope := initPlanning.nextScope + 1 }
              post).scopes →
          entry ∈ compilation.recipe.lexicalScopes := by
    intro entry hEntry
    apply hBodyScopesRecipe entry
    rw [hBodyScopes]
    exact
      List.mem_append_right bodyAdded
        (AllocationSupport.mem_planBlockScoped_scopes_of_open_mem
          post loopScope initPlanning hEntry)
  have hBodyInnerScopesRecipe :
      ∀ entry,
        entry ∈
            (AllocationSupport.planBlockOpen
              (.lexical loopScope postPlanning.nextScope)
              { postPlanning with
                nextScope := postPlanning.nextScope + 1 }
              body).scopes →
          entry ∈ compilation.recipe.lexicalScopes := by
    intro entry hEntry
    exact
      hBodyScopesRecipe entry
        (AllocationSupport.mem_planBlockScoped_scopes_of_open_mem
          body loopScope postPlanning hEntry)
  have hLoopPlanEnv :
      bodyPlanning.allocation.env = loopState.allocation.env := by
    calc
      bodyPlanning.allocation.env = afterBody.allocation.env :=
        congrArg AllocationSupport.CompileState.env hBodyPlanning
      _ = afterPost.allocation.env := hBodyShape.1
      _ = loopState.allocation.env := hPostShape.1
  have hEnteredActive :
      ActiveEnv root.slots entered.allocation.env live := by
    simpa [entered] using cursor.activeEnv
  have hInitActive :
      ActiveEnv root.slots initPlanning.allocation.env loopLive := by
    simpa [initPlanning, loopLive] using
      hEnteredActive.after_planBlockOpen
        (scope := loopScope) (block := init)
  have hPostActive :
      ActiveEnv root.slots postPlanning.allocation.env loopLive := by
    rw [congrArg AllocationSupport.CompileState.env hPostPlanning,
      hPostShape.1,
      ← congrArg AllocationSupport.CompileState.env hInitPlanning]
    exact hInitActive
  obtain
      ⟨initCursor, _hInitLowered, hInitFinal, hInitCode,
        hInitLocals⟩ :=
    cursor.lexicalOfPlanState loopScope entered
      (by simpa [entered] using cursor.planningAllocation)
      (by
        simpa [loopScope,
          MixedAllocation.AllocationRecipe.functionRoot?] using
          cursor.scopeRoot)
      (by simpa [loopEntry] using hLoopEntryRecipe)
      hLoopPlanEnv hInitScopesRecipe hLowerInit hCompileInit hScoped.1
      hEnteredActive
  obtain
      ⟨postOpenFinal, hPostOpen, _hPostEnv, _hPostNext,
        _hPostLayout⟩ :=
    AllocationLowering.lowerBlockScoped_components hLowerPost
  let postScope :=
    Locals.Allocation.ScopeId.lexical loopScope initPlanning.nextScope
  let postEntered : AllocationSupport.PlanningState :=
    { initPlanning with
      nextScope := initPlanning.nextScope + 1 }
  let postEntry : AllocationSupport.ScopedAllocation :=
    { scope := postScope
      state :=
        (AllocationSupport.planBlockOpen
          postScope postEntered post).allocation }
  have hPostEntryRecipe :
      postEntry ∈ compilation.recipe.lexicalScopes := by
    apply hBodyScopesRecipe postEntry
    rw [hBodyScopes]
    exact
      List.mem_append_right bodyAdded
        (by
          simpa [postEntry, postScope, postEntered] using
            AllocationSupport.planBlockScoped_entry_mem
              post loopScope initPlanning)
  obtain
      ⟨postCursor, hPostCursorLowered, _hPostFinal, hPostCode,
        hPostLocals⟩ :=
    cursor.lexical postScope postEntered
      (by simpa [postEntered] using hInitPlanning)
      (by
        simpa [postScope, loopScope,
          MixedAllocation.AllocationRecipe.functionRoot?] using
          cursor.scopeRoot)
      (by simpa [postEntry, postScope, postEntered] using hPostEntryRecipe)
      (by simpa [postScope, postEntered] using hPostScopesRecipe)
      hPostOpen hCompilePost hScoped.2.2.1
      (by simpa [postEntered] using hInitActive)
  obtain
      ⟨bodyOpenFinal, hBodyOpen, _hBodyEnv, _hBodyNext,
        _hBodyLayout⟩ :=
    AllocationLowering.lowerBlockScoped_components hLowerBody
  let bodyScope :=
    Locals.Allocation.ScopeId.lexical loopScope postPlanning.nextScope
  let bodyEntered : AllocationSupport.PlanningState :=
    { postPlanning with
      nextScope := postPlanning.nextScope + 1 }
  let bodyEntry : AllocationSupport.ScopedAllocation :=
    { scope := bodyScope
      state :=
        (AllocationSupport.planBlockOpen
          bodyScope bodyEntered body).allocation }
  have hBodyEntryRecipe :
      bodyEntry ∈ compilation.recipe.lexicalScopes :=
    hBodyScopesRecipe bodyEntry
      (by
        simpa [bodyEntry, bodyScope, bodyEntered] using
          AllocationSupport.planBlockScoped_entry_mem
            body loopScope postPlanning)
  obtain
      ⟨bodyCursor, hBodyCursorLowered, _hBodyFinal, hBodyCode,
        hBodyLocals⟩ :=
    cursor.lexical bodyScope bodyEntered
      (by simpa [bodyEntered] using hPostPlanning)
      (by
        simpa [bodyScope, loopScope,
          MixedAllocation.AllocationRecipe.functionRoot?] using
          cursor.scopeRoot)
      (by simpa [bodyEntry, bodyScope, bodyEntered] using hBodyEntryRecipe)
      (by simpa [bodyScope, bodyEntered] using hBodyInnerScopesRecipe)
      hBodyOpen hCompileBody hScoped.2.2.2
      (by simpa [bodyEntered] using hPostActive)
  cases hAfterLocals
  refine
    ⟨afterState, headLower, headCode, tail, loopState, afterPost,
      afterBody, initLocals, postLocals, bodyLocals, loweredCond,
      condCode, compiledPost, compiledBody, cleanup, initCursor,
      postCursor, bodyCursor, hCompiled, hLower, ?_, hInitFinal,
      hInitLocals, hLowerCond, hCompileCond, ?_, ?_, ?_, ?_,
      hCleanup, ?_, hAfterState, hScoped.2.1, hScoped.2.2.1,
      hScoped.2.2.2,
      StepTransport.of_compilers hScopedStmt hLower hHeadCompile,
      ⟨hTailPlan, hTailFinalState, hTailFinalLocals,
        ⟨headCode, hCompiled⟩⟩⟩
  · rw [hHeadLower]
    exact hCompile
  · rw [hPostCursorLowered]
    exact hLowerPost
  · rw [hPostCode, hPostLocals]
    exact hFinishPost
  · rw [hBodyCursorLowered]
    exact hLowerBody
  · rw [hBodyCode, hBodyLocals]
    exact hFinishBody
  · rw [hInitCode, hHeadCode]

/-- Stable compiler-owned decomposition consumed by adjacent `for` proofs. -/
structure CoreCursor.ForComponents
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx) where
  afterState : AllocationLowering.State
  headLower : List Locals.Stmt
  headCode : List Expressions.Stmt
  tail : CoreCursor root scope live { stmts := rest } afterState localsCtx
  loopState : AllocationLowering.State
  afterPost : AllocationLowering.State
  afterBody : AllocationLowering.State
  initLocals : Locals.Ctx
  postLocals : Locals.Ctx
  bodyLocals : Locals.Ctx
  loweredCond : Locals.Expr 1
  condCode : Structured.Code
  compiledPost : Expressions.Block
  compiledBody : Expressions.Block
  cleanup : Structured.Code
  initScope : Locals.Allocation.ScopeId
  postScope : Locals.Allocation.ScopeId
  bodyScope : Locals.Allocation.ScopeId
  loopLive : List Functions.Name
  loopLive_eq : loopLive = Functions.Scope.Block.outEnv live init
  initCursor :
    CoreCursor root initScope live init lowerState
      localsCtx.withoutLoopControl
  postCursor :
    CoreCursor root postScope loopLive post loopState
      initLocals.withoutLoopControl
  bodyCursor :
    CoreCursor root bodyScope loopLive body afterPost
      (initLocals.withLoopControl initLocals.layout.length)
  postPlanAgree : PlanAgreesOn postCursor.plan initCursor.plan loopLive
  bodyPlanAgree : PlanAgreesOn bodyCursor.plan initCursor.plan loopLive
  compiled : cursor.compiled = headCode ++ tail.compiled
  lower :
    AllocationLowering.lowerStmt root.lowerCtx root.returns lowerState
      (.for_ init cond post body) = some (headLower, afterState)
  compile :
    Locals.Block.compileOpen localsCtx { stmts := headLower } =
      some (headCode, localsCtx)
  initFinalState : initCursor.finalState = loopState
  initFinalLocals : initCursor.finalLocals = initLocals
  lowerCond :
    AllocationLowering.lowerExpr root.lowerCtx loopState cond =
      some loweredCond
  compileCond :
    Locals.Expr.compileCode initLocals 0 loweredCond = some condCode
  lowerPost :
    AllocationLowering.lowerBlockScoped root.lowerCtx root.returns
      loopState post = some (postCursor.lowered, afterPost)
  finishPost :
    Locals.finishScoped initLocals.withoutLoopControl
      postCursor.finalLocals postCursor.compiled = some compiledPost
  lowerBody :
    AllocationLowering.lowerBlockScoped root.lowerCtx root.returns
      afterPost body = some (bodyCursor.lowered, afterBody)
  finishBody :
    Locals.finishScoped
      (initLocals.withLoopControl initLocals.layout.length)
      bodyCursor.finalLocals bodyCursor.compiled = some compiledBody
  cleanupTo :
    initLocals.cleanupTo? localsCtx.layout.length = some cleanup
  headCode_eq :
    headCode =
      [Expressions.Stmt.for_
        { stmts := initCursor.compiled }
        (.code condCode) compiledPost compiledBody] ++
        Locals.codeStmt cleanup
  afterState_eq :
    afterState =
      { allocation :=
          { env := lowerState.allocation.env
            nextSlot := afterBody.allocation.nextSlot }
        layout := lowerState.layout }
  condScoped : Functions.Scope.ExprScoped loopLive cond
  postScoped : Functions.Scope.Block.Scoped loopLive post
  bodyScoped : Functions.Scope.Block.Scoped loopLive body
  step :
    StepTransport lowerState afterState localsCtx localsCtx live
      (.for_ init cond post body)
  exactTail : ExactTail cursor tail

/-- Construct the stable `for` artifact solely from the ordinary compiler. -/
theorem CoreCursor.forComponents
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx) :
    Nonempty cursor.ForComponents := by
  obtain
      ⟨afterState, headLower, headCode, tail,
        loopState, afterPost, afterBody,
        initLocals, postLocals, bodyLocals,
        loweredCond, condCode, compiledPost, compiledBody, cleanup,
        initCursor, postCursor, bodyCursor,
        hCompiled, hLower, hCompile,
        hInitFinalState, hInitFinalLocals,
        hLowerCond, hCompileCond, hLowerPost, hFinishPost,
        hLowerBody, hFinishBody, hCleanup, hHeadCode, hAfterState,
        hCondScoped, hPostScoped, hBodyScoped, hStep, hExact⟩ :=
    cursor.forCursors
  let loopLive := Functions.Scope.Block.outEnv live init
  have hPostShape :=
    AllocationLowering.lowerBlockScoped_state_shape hLowerPost
  have hPostPlanAgree :
      PlanAgreesOn postCursor.plan initCursor.plan loopLive := by
    apply postCursor.planAgreesOn initCursor.finished
    rw [hInitFinalState]
  have hBodyPlanAgree :
      PlanAgreesOn bodyCursor.plan initCursor.plan loopLive := by
    apply bodyCursor.planAgreesOn initCursor.finished
    rw [hInitFinalState]
    exact hPostShape.1
  exact ⟨{
    afterState := afterState
    headLower := headLower
    headCode := headCode
    tail := tail
    loopState := loopState
    afterPost := afterPost
    afterBody := afterBody
    initLocals := initLocals
    postLocals := postLocals
    bodyLocals := bodyLocals
    loweredCond := loweredCond
    condCode := condCode
    compiledPost := compiledPost
    compiledBody := compiledBody
    cleanup := cleanup
    initScope := _
    postScope := _
    bodyScope := _
    loopLive := loopLive
    loopLive_eq := rfl
    initCursor := initCursor
    postCursor := postCursor
    bodyCursor := bodyCursor
    postPlanAgree := hPostPlanAgree
    bodyPlanAgree := hBodyPlanAgree
    compiled := hCompiled
    lower := hLower
    compile := hCompile
    initFinalState := hInitFinalState
    initFinalLocals := hInitFinalLocals
    lowerCond := hLowerCond
    compileCond := hCompileCond
    lowerPost := hLowerPost
    finishPost := hFinishPost
    lowerBody := hLowerBody
    finishBody := hFinishBody
    cleanupTo := hCleanup
    headCode_eq := hHeadCode
    afterState_eq := hAfterState
    condScoped := hCondScoped
    postScoped := hPostScoped
    bodyScoped := hBodyScoped
    step := hStep
    exactTail := hExact }⟩

/-- Canonical internal `for` artifact selected from checked decomposition. -/
noncomputable def CoreCursor.forArtifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block}
    {cond : Functions.Expr 1}
    {post body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        lowerState localsCtx) :
    cursor.ForComponents :=
  Classical.choice cursor.forComponents

end AllocationInteractionCursor
end Functions
end EvmCompiler
