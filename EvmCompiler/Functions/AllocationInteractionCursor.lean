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
      live =
        locals.map Prod.fst ++
          (root.slots.returns.map Prod.fst).reverse ++
          (root.slots.params.map Prod.fst).reverse) :
    currentStackOrder cursor.plan live =
      MixedAllocation.stackOrder compilation.stackSlots locals ++
        MixedAllocation.stackOrder compilation.stackSlots
          root.slots.returns.reverse ++
        MixedAllocation.stackOrder compilation.stackSlots
          root.slots.params.reverse := by
  subst live
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
  rw [cursor.planEq]
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
        live =
          locals.map Prod.fst ++
            (root.slots.returns.map Prod.fst).reverse ++
            (root.slots.params.map Prod.fst).reverse ∧
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
      name :: live =
        (((name, cursor.planning.allocation.nextSlot) :: locals).map
            Prod.fst) ++
          (root.slots.returns.map Prod.fst).reverse ++
          (root.slots.params.map Prod.fst).reverse := by
    calc
      name :: live =
          name ::
            (locals.map Prod.fst ++
              (root.slots.returns.map Prod.fst).reverse ++
              (root.slots.params.map Prod.fst).reverse) :=
        congrArg (List.cons name) hCurrentLive
      _ =
          (((name, cursor.planning.allocation.nextSlot) :: locals).map
              Prod.fst) ++
            (root.slots.returns.map Prod.fst).reverse ++
            (root.slots.params.map Prod.fst).reverse := rfl
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

end AllocationInteractionCursor
end Functions
end EvmCompiler
