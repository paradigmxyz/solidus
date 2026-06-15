import EvmCompiler.Functions.AllocationObserverCall
import EvmCompiler.Functions.AllocationObserverLoop
import EvmCompiler.Functions.AllocationObserverOutcome
import EvmCompiler.Functions.AllocationObserverSwitch

namespace EvmCompiler
namespace Functions
namespace AllocationObserverForward

open AllocationObserverRelation

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

/--
The compiler-owned global data shared by the main body and every function
activation in one allocation lowering.

This structure contains only deterministic outputs of the existing validator
and compiler. It is constructed from the public lowering equation below and
is never a caller-supplied certificate at the eventual public boundary.
-/
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
  fresh :
    AllocationLowering.freshFrameName program = some frameName
  lower :
    AllocationLowering.lowerExpressionsFromAllocation?
        allocation program =
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
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      unfold AllocationLowering.lowerLocalsFromAllocation? at hLocals
      cases hValidate :
          AllocationLowering.validatePlan? allocation program with
      | none =>
          simp [hValidate] at hLocals
      | some validated =>
          rcases validated with ⟨recipe, stackSlots⟩
          cases hFresh :
              AllocationLowering.freshFrameName program with
          | none =>
              simp [hValidate, hFresh] at hLocals
          | some frameName =>
              exact
                ⟨{ recipe := recipe
                   stackSlots := stackSlots
                   frameName := frameName
                   validate := hValidate
                   fresh := hFresh
                   lower := hWhole }⟩

/--
Recover the whole compiler invocation from any compiler-selected callee
artifact. The artifact carries the original lowering equation, so recursive
call proofs do not accept a second generated compilation witness.
-/
def Compilation.ofSelected
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    Compilation allocation program expressions :=
  { recipe := artifact.recipe
    stackSlots := artifact.stackSlots
    frameName := artifact.frameName
    validate := artifact.validate
    fresh := artifact.fresh
    lower := artifact.wholeLower }

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

/--
The global portion of an allocation-lowering context. Roots and scratch
bindings vary by activation; these fields must remain identical throughout one
whole-program lowering.
-/
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
    compilation.CtxShared
      (compilation.lowerCtx root scratchBindings) := by
  constructor <;> rfl

theorem Compilation.selectedCallee
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (hFind :
      Functions.Source.FunList.find? name program.functions = some fn) :
    Nonempty
      (AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :=
  AllocationObserverCall.SelectedCallee.of_lowering
    compilation.lower hFind

theorem Compilation.selected_agrees
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    artifact.recipe = compilation.recipe ∧
      artifact.stackSlots = compilation.stackSlots ∧
      artifact.frameName = compilation.frameName := by
  have hValidated :
      (artifact.recipe, artifact.stackSlots) =
        (compilation.recipe, compilation.stackSlots) :=
    Option.some.inj (artifact.validate.symm.trans compilation.validate)
  have hFrameName :
      artifact.frameName = compilation.frameName :=
    Option.some.inj (artifact.fresh.symm.trans compilation.fresh)
  exact
    ⟨congrArg Prod.fst hValidated,
      congrArg Prod.snd hValidated, hFrameName⟩

theorem Compilation.selected_lowerCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    artifact.lowerCtx =
      compilation.lowerCtx artifact.root artifact.scratchBindings := by
  obtain ⟨hRecipe, hSlots, hFrameName⟩ :=
    compilation.selected_agrees artifact
  simp [AllocationObserverCall.SelectedCallee.Artifact.lowerCtx,
    Compilation.lowerCtx, Compilation.frameConfig?,
    hRecipe, hSlots, hFrameName]

theorem Compilation.selected_shared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    compilation.CtxShared artifact.lowerCtx := by
  rw [compilation.selected_lowerCtx artifact]
  exact
    compilation.lowerCtx_shared artifact.root artifact.scratchBindings

theorem Compilation.call_needsFrame_iff
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {callerCtx : AllocationLowering.Ctx}
    (hCaller : compilation.CtxShared callerCtx)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    name ∈ callerCtx.frameFunctions ↔ artifact.needsFrame = true := by
  obtain ⟨hRecipe, hSlots, _hFrameName⟩ :=
    compilation.selected_agrees artifact
  rw [hCaller.frameFunctions]
  simpa [hRecipe, hSlots] using artifact.mem_frameFunctions_iff

theorem Compilation.selected_frameWords_pos
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn)
    (hNeedsFrame : artifact.needsFrame = true) :
    0 < compilation.recipe.frameWords := by
  obtain ⟨hRecipe, hSlots, _hFrameName⟩ :=
    compilation.selected_agrees artifact
  have hBindings :
      artifact.scratchBindings =
        AllocationLowering.scratchBindingsForRoot
          compilation.recipe compilation.stackSlots artifact.root := by
    simp [AllocationObserverCall.SelectedCallee.Artifact.scratchBindings,
      hRecipe, hSlots]
  have hRootNeeds :
      AllocationLowering.rootNeedsFrame
          compilation.recipe compilation.stackSlots artifact.root =
        true := by
    unfold AllocationLowering.rootNeedsFrame
    rw [← hBindings]
    exact hNeedsFrame
  exact
    AllocationLowering.frameWords_pos_of_validate_of_rootNeedsFrame
      compilation.validate hRootNeeds

theorem Compilation.selected_config_frameWords_pos
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn)
    {config : Frame.Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hNeedsFrame : artifact.needsFrame = true) :
    0 < config.frameWords := by
  obtain
      ⟨_reservation, _hReservation, _hAllocator, _hFirst, _hLimit,
        hWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  rw [hWords]
  exact compilation.selected_frameWords_pos artifact hNeedsFrame

namespace BodyCursor

/--
The allocation environment at a recursive function-body position consists of
the declarations already executed in the open body followed by the fixed
function signature. The source scope lists those declarations in the same
front-to-back order, followed by the runtime return/parameter order.
-/
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
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    (hActive : ActiveEnv slots planning.allocation.env live) :
    ActiveEnv slots
      (AllocationSupport.planStmt scope planning stmt).allocation.env
      (Functions.Scope.Stmt.outEnv live stmt) := by
  rcases hActive with ⟨locals, hEnv, hLive⟩
  cases stmt with
  | let_ name value =>
      refine
        ⟨(name, planning.allocation.nextSlot) :: locals, ?_, ?_⟩
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
    {live : List Functions.Name}
    {stmts : List Functions.Stmt}
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
    {live : List Functions.Name}
    {block : Functions.Block}
    (hActive : ActiveEnv slots planning.allocation.env live) :
    ActiveEnv slots
      (AllocationSupport.planBlockOpen scope planning block).allocation.env
      (Functions.Scope.Block.outEnv live block) := by
  rcases block with ⟨stmts⟩
  simpa [AllocationSupport.planBlockOpen,
    Functions.Scope.Block.outEnv] using
    hActive.after_planStmtList (scope := scope) (stmts := stmts)

end ActiveEnv

/--
Pass-owned description of one recursively lowered source root.

This is the owner-neutral boundary consumed by the recursive observer proof.
Selected functions and the distinguished main body both provide this artifact
from their existing allocation-lowering and Locals-compilation results.
-/
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
  planningAllocation :
    planning.allocation = startState.allocation
  rootScopeOwner :
    MixedAllocation.AllocationRecipe.functionRoot? rootScope =
      functionRoot?
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
    ∀ entry,
      entry ∈ compilation.recipe.lexicalScopes →
        compilation.frameName ∉ entry.state.env.map Prod.fst
  scopeStackEntries :
    ∀ {scope : Locals.Allocation.ScopeId}
      {state : AllocationSupport.CompileState}
      {added : AllocationSupport.SlotEnv},
      MixedAllocation.AllocationRecipe.functionRoot? scope =
          functionRoot? →
        state.env =
          added ++ AllocationSupport.functionEnv slots →
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
  lowerCtxShared :
    compilation.CtxShared lowerCtx
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

/--
Owner-neutral recursive cursor. It contains exactly the static planner,
lowering, and Locals-compilation evidence needed by the statement dispatcher.
-/
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
  planningAllocation :
    planning.allocation = lowerState.allocation
  scopeRoot :
    MixedAllocation.AllocationRecipe.functionRoot? scope =
      root.functionRoot?
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
  activeEnv :
    ActiveEnv root.slots planning.allocation.env live

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

/--
Static placement change for one declaration in an open function body.

This is derived from the real planner and final allocation plan. It contains
no emitted-code premise and is the exact information needed to construct the
post-declaration activation context.
-/
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
      (hLocation :
        plan.location? name = some (.stack planDepth))
      (hOrder :
        AllocationObserverRelation.currentStackOrder
            plan (name :: beforeLive) =
          name ::
            AllocationObserverRelation.currentStackOrder plan beforeLive) :
      DeclarationPlacement lowerCtx beforeState plan beforeLive name
  | scratch
      (slot : Nat)
      (hSlot : slot = beforeState.allocation.nextSlot)
      (hStack :
        AllocationLowering.isStackSlot lowerCtx slot = false)
      (hLocation :
        plan.location? name = some (.scratch slot))
      (hOrder :
        AllocationObserverRelation.currentStackOrder
            plan (name :: beforeLive) =
          AllocationObserverRelation.currentStackOrder plan beforeLive) :
      DeclarationPlacement lowerCtx beforeState plan beforeLive name

/--
One recursive open-block segment inside a compiler-selected function.

The cursor owns the actual source block, its allocation-lowered/Locals-compiled
artifact, and explicit segment end states.  The end allocation is proved to
embed in the selected function's final plan, so the same cursor type represents
the root body, a remaining tail, or a nested control-flow body.
-/
structure Cursor
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (scope : Locals.Allocation.ScopeId)
    (live : List Functions.Name)
    (sourceBlock : Functions.Block)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) where
  planning : AllocationSupport.PlanningState
  planningAllocation :
    planning.allocation = lowerState.allocation
  scopeRoot :
    MixedAllocation.AllocationRecipe.functionRoot? scope =
      some fn.name
  plan : Locals.Allocation.Plan
  planWF : plan.WellFormed
  finalState : AllocationLowering.State
  finalLocals : Locals.Ctx
  planEq :
    plan =
      MixedAllocation.allocationOfState
        program.memoryContract artifact.recipe.frameWords
        (MixedAllocation.AllocationRecipe.stackEntriesForScope
          artifact.recipe artifact.stackSlots scope finalState.allocation)
        finalState.allocation
  finalFrameFresh :
    artifact.frameName ∉ finalState.allocation.env.map Prod.fst
  plannedFinal :
    (AllocationSupport.planBlockOpen scope planning sourceBlock).allocation =
      finalState.allocation
  plannedScopes :
    ∀ entry,
      entry ∈
          (AllocationSupport.planBlockOpen scope planning sourceBlock).scopes →
        entry ∈ artifact.recipe.lexicalScopes
  lowered : Locals.Block
  compiled : List Expressions.Stmt
  lower :
    AllocationLowering.lowerBlockOpen artifact.lowerCtx fn.returns
        lowerState sourceBlock =
      some (lowered, finalState)
  compile :
    Locals.Block.compileOpen localsCtx lowered =
      some (compiled, finalLocals)
  sourceScoped : Functions.Scope.Block.Scoped live sourceBlock
  activeEnv :
    ActiveEnv artifact.slots planning.allocation.env live

/--
The exact remaining cursor returned by one head-step decomposition.

This small pass-owned artifact lets dispatcher-facing theorems retain the
parent cursor's allocation plan and compiler endpoints without exposing the
lowering equations themselves at the recursive theorem boundary.
-/
structure ExactTail
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
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

def Cursor.root
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hScoped :
      Functions.Scope.Block.Scoped
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        fn.body) :
    Cursor prepared (.function fn.name)
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      fn.body artifact.bodyStart prepared.returnCtx :=
  { planning :=
      { allocation := artifact.bodyStart.allocation
        nextScope := 0
        scopes := [] }
    planningAllocation := rfl
    scopeRoot := rfl
    plan := prepared.plan
    planWF := prepared.planWF
    finalState := prepared.bodyFinal
    finalLocals := prepared.bodyCtx
    planEq := by
      rw [prepared.planEq, artifact.planEntryScope, prepared.bodyPlan]
    finalFrameFresh := by
      rw [← prepared.bodyPlan]
      exact artifact.frameName_not_mem_planEntry_env
    plannedFinal := by
      calc
        (AllocationSupport.planBlockOpen (.function fn.name)
            {
              allocation := artifact.bodyStart.allocation
              nextScope := 0
              scopes := []
            }
            fn.body).allocation =
            artifact.planEntry.state := by
          simpa [AllocationObserverCall.SelectedCallee.Artifact.bodyStart] using
            artifact.planEntryState.symm
        _ = prepared.bodyFinal.allocation := prepared.bodyPlan
    plannedScopes := by
      simpa [AllocationObserverCall.SelectedCallee.Artifact.bodyStart] using
        artifact.bodyScopesMem
    lowered := prepared.body
    compiled := prepared.bodyCode
    lower := prepared.lowerBody
    compile := prepared.compileBody
    sourceScoped := hScoped
    activeEnv := by
      refine ⟨[], ?_, ?_⟩
      · simp [AllocationObserverCall.SelectedCallee.Artifact.bodyStart]
      · simp }

/--
Embed the existing selected-function artifact into the owner-neutral recursive
root interface. This theorem is the compatibility boundary used while the
dispatcher migrates from function-specific cursors.
-/
def RootArtifact.ofSelected
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn)
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hScoped :
      Functions.Scope.Block.Scoped
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        fn.body) :
    RootArtifact (Compilation.ofSelected artifact) :=
  { functionRoot? := some fn.name
    rootScope := .function fn.name
    slots := artifact.slots
    returns := fn.returns
    sourceBlock := fn.body
    startState := artifact.bodyStart
    startLocals := prepared.returnCtx
    planning :=
      { allocation := artifact.bodyStart.allocation
        nextScope := 0
        scopes := [] }
    planningAllocation := rfl
    rootScopeOwner := rfl
    plan := prepared.plan
    planWF := prepared.planWF
    finalState := prepared.bodyFinal
    finalLocals := prepared.bodyCtx
    planEq := by
      rw [prepared.planEq, artifact.planEntryScope, prepared.bodyPlan]
      simp [Compilation.ofSelected]
    finalFrameFresh := by
      rw [← prepared.bodyPlan]
      exact artifact.frameName_not_mem_planEntry_env
    lexicalFrameFresh := by
      intro entry hEntry
      simpa [Compilation.ofSelected] using
        artifact.frameName_not_mem_lexical_entry_env hEntry
    scopeStackEntries := by
      intro scope state added hRoot hEnv
      exact
        MixedAllocation.AllocationRecipe.stackEntriesForScope_of_functionRoot_env_extension
          hRoot artifact.slotsLookup hEnv
    plannedFinal := by
      calc
        (AllocationSupport.planBlockOpen (.function fn.name)
            {
              allocation := artifact.bodyStart.allocation
              nextScope := 0
              scopes := []
            }
            fn.body).allocation =
            artifact.planEntry.state := by
          simpa [AllocationObserverCall.SelectedCallee.Artifact.bodyStart] using
            artifact.planEntryState.symm
        _ = prepared.bodyFinal.allocation := prepared.bodyPlan
    plannedScopes := by
      simpa [AllocationObserverCall.SelectedCallee.Artifact.bodyStart] using
        artifact.bodyScopesMem
    lowered := prepared.body
    compiled := prepared.bodyCode
    lowerCtx := artifact.lowerCtx
    lowerCtxShared :=
      (Compilation.ofSelected artifact).selected_shared artifact
    lower := prepared.lowerBody
    compile := prepared.compileBody
    sourceScoped := hScoped
    activeEnv := by
      refine ⟨[], ?_, ?_⟩
      · simp [AllocationObserverCall.SelectedCallee.Artifact.bodyStart]
      · simp }

def Cursor.toCore
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hScoped :
      Functions.Scope.Block.Scoped
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        fn.body)
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      Cursor prepared scope live sourceBlock lowerState localsCtx) :
    CoreCursor (RootArtifact.ofSelected artifact prepared hScoped)
      scope live sourceBlock lowerState localsCtx :=
  { planning := cursor.planning
    planningAllocation := cursor.planningAllocation
    scopeRoot := cursor.scopeRoot
    plan := cursor.plan
    planWF := cursor.planWF
    finalState := cursor.finalState
    finalLocals := cursor.finalLocals
    planEq := by
      simpa [Compilation.ofSelected] using cursor.planEq
    finalFrameFresh := cursor.finalFrameFresh
    plannedFinal := cursor.plannedFinal
    plannedScopes := cursor.plannedScopes
    lowered := cursor.lowered
    compiled := cursor.compiled
    lower := cursor.lower
    compile := cursor.compile
    sourceScoped := cursor.sourceScoped
    activeEnv := cursor.activeEnv }

/--
Decompose one owner-neutral nonempty cursor through the real statement lowerer
and Locals compiler.
-/
theorem CoreCursor.cons
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
          lowerState stmt =
        some (headLower, afterState) ∧
      Locals.Block.compileOpen localsCtx { stmts := headLower } =
        some (headCode, afterLocals) ∧
      cursor.lowered.stmts =
        headLower ++ tailCursor.lowered.stmts ∧
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
  obtain
      ⟨headCode, afterLocals, tailCode,
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
    { planning :=
        AllocationSupport.planStmt scope cursor.planning stmt
      planningAllocation :=
        AllocationLowering.lowerStmt_allocation_eq_planStmt
          stmt scope cursor.planning root.lowerCtx root.returns
          lowerState afterState headLower cursor.planningAllocation
          hHeadLower
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
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx) :
    CoreCursor root scope
      (Functions.Scope.Block.outEnv live sourceBlock)
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
      compile := by
        simp [Locals.Block.compileOpen]
      sourceScoped := by
        simp [Functions.Scope.Block.Scoped,
          Functions.Scope.StmtList.Scoped]
      activeEnv := hFinalActive }

/--
Decompose a nonempty recursive cursor through the real statement lowerer and
Locals compiler, retaining a cursor for the exact remaining tail.
-/
theorem Cursor.cons
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      Cursor prepared scope live { stmts := stmt :: rest }
        lowerState localsCtx) :
    ∃ afterState afterLocals headLower headCode,
      ∃ tailCursor :
        Cursor prepared scope (Functions.Scope.Stmt.outEnv live stmt)
          { stmts := rest } afterState afterLocals,
      tailCursor.planning =
          AllocationSupport.planStmt scope cursor.planning stmt ∧
      tailCursor.plan = cursor.plan ∧
      tailCursor.finalState = cursor.finalState ∧
      tailCursor.finalLocals = cursor.finalLocals ∧
      AllocationLowering.lowerStmt artifact.lowerCtx fn.returns
          lowerState stmt =
        some (headLower, afterState) ∧
      Locals.Block.compileOpen localsCtx { stmts := headLower } =
        some (headCode, afterLocals) ∧
      cursor.lowered.stmts =
        headLower ++ tailCursor.lowered.stmts ∧
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
  obtain
      ⟨headCode, afterLocals, tailCode,
        hHeadCompile, hTailCompile, hCompiled⟩ :=
    Locals.Block.compileOpen_append_components hCompile
  have hScoped :
      Functions.Scope.Stmt.Scoped live stmt ∧
        Functions.Scope.StmtList.Scoped
          (Functions.Scope.Stmt.outEnv live stmt) rest := by
    simpa [Functions.Scope.Block.Scoped,
      Functions.Scope.StmtList.Scoped] using cursor.sourceScoped
  let tailCursor :
      Cursor prepared scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals :=
    { planning :=
        AllocationSupport.planStmt scope cursor.planning stmt
      planningAllocation :=
        AllocationLowering.lowerStmt_allocation_eq_planStmt
          stmt scope cursor.planning artifact.lowerCtx fn.returns
          lowerState afterState headLower cursor.planningAllocation
          hHeadLower
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

/--
Advance a synchronized open-block cursor to its empty final tail.

The final tail retains the original scope-owned allocation plan while exposing
the exact outgoing source live set, allocation state, and Locals context. This
is the pass-owned bridge used when a later lexical component starts after an
entire initializer block.
-/
def Cursor.finished
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      Cursor prepared scope live sourceBlock lowerState localsCtx) :
    Cursor prepared scope
      (Functions.Scope.Block.outEnv live sourceBlock)
      { stmts := [] } cursor.finalState cursor.finalLocals := by
  let finalPlanning :=
    AllocationSupport.planBlockOpen scope cursor.planning sourceBlock
  have hFinalActive :
      ActiveEnv artifact.slots finalPlanning.allocation.env
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
      compile := by
        simp [Locals.Block.compileOpen]
      sourceScoped := by
        simp [Functions.Scope.Block.Scoped,
          Functions.Scope.StmtList.Scoped]
      activeEnv := hFinalActive }

/--
Static compiler transport supplied by one successful source statement.

This is the dispatcher-facing part of `Cursor.cons`: allocation slots for
incoming live names are preserved, Locals control destinations are unchanged,
and every incoming source name remains live after the statement.
-/
structure StepTransport
    (beforeState afterState : AllocationLowering.State)
    (beforeLocals afterLocals : Locals.Ctx)
    (beforeLive : List Functions.Name)
    (stmt : Functions.Stmt) : Prop where
  state :
    AllocationLowering.StateExtends beforeLive beforeState afterState
  locals :
    Locals.Ctx.SameControl beforeLocals afterLocals
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
  { state :=
      AllocationLowering.lowerStmt_stateExtends hScoped hLower
    locals :=
      Locals.Block.compileOpen_sameControl hCompile
    live := fun _ hName => Functions.Scope.Stmt.mem_outEnv hName }

theorem CoreCursor.headScoped
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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

/--
Construct a synchronized cursor from any checked lexical planner entry owned
by the selected function artifact.

Switch cases and loop components are not necessarily the first lexical child
of their enclosing statement, so this is the stable constructor beneath all
control-specific cursor decompositions.
-/
theorem CoreCursor.lexicalOfPlanState
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {cursorLive nestedLive : List Functions.Name}
    {sourceBlock : Functions.Block}
    {body : Functions.Block}
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
    (hPlanEnv :
      planState.env = openFinal.allocation.env)
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
  have hFind :
      allocation.find? lexicalScope = some plan := by
    have hEntryFind :=
      AllocationLowering.validatePlan?_lexical_entry_plan
        compilation.validate hEntryRecipe
    simpa [scopeEntry, plan] using
      hEntryFind
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
        have hFresh :=
          root.lexicalFrameFresh _ hEntryRecipe
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

/--
Construct a lexical cursor whose validated scope entry is the exact endpoint
of the open block.
-/
theorem CoreCursor.lexical
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {cursorLive nestedLive : List Functions.Name}
    {sourceBlock : Functions.Block}
    {body : Functions.Block}
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

/--
Construct a synchronized cursor for one immediate compiler-scoped source
block.
-/
theorem CoreCursor.scoped
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
  obtain
      ⟨openFinal, hOpen, _hScopedEnv, _hScopedNext, _hScopedLayout⟩ :=
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
  obtain
      ⟨nested, _hLowered, _hFinalState, hCode, hLocals⟩ :=
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

/--
Decompose a lexical block statement into its scope-owned body cursor and the
outer tail cursor, retaining the compiler-emitted scoped cleanup block.
-/
theorem CoreCursor.blockCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩
  rw [hBodyCode, hBodyLocals]
  exact hFinish

/--
Decompose an `if` statement into its condition compiler artifacts, exact
scope-owned body cursor, and outer tail cursor.

Both runtime branches share this compiler decomposition; only the canonical
source condition result determines whether the nested cursor is executed.
-/
theorem CoreCursor.ifCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
          AllocationLowering.lowerExpr
              root.lowerCtx lowerState cond =
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
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩
  · simpa using hHeadCompile
  rw [hBodyCode, hBodyLocals]
  exact hFinish

/--
Decompose a `switch` statement through the real allocation lowerer and Locals
compiler, retaining the exact outer tail cursor.

This common decomposition is enough for the no-selected-body branch. Selected
branches additionally construct a lexical cursor for the chosen case/default.
-/
theorem CoreCursor.switchCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationLowering.lowerStmt root.lowerCtx root.returns
              lowerState (.switch scrutinee cases defaultBody) =
            some (headLower, afterState) ∧
          Locals.Block.compileOpen localsCtx { stmts := headLower } =
            some (headCode, localsCtx) ∧
          afterState.allocation.env =
            lowerState.allocation.env ∧
          afterState.layout = lowerState.layout ∧
          Functions.Scope.ExprScoped live scrutinee ∧
          Functions.Scope.CaseList.Scoped live cases ∧
          Functions.Scope.Default.Scoped live defaultBody ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScopedStmt⟩ :=
    cursor.cons
  obtain
      ⟨_loweredScrutinee, _loweredCases, afterCases, _loweredDefault,
        _hLowerScrutinee, hLowerCases, hLowerDefault, hHeadLower⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  have hHeadCompile := hCompile
  rw [hHeadLower] at hCompile
  obtain
      ⟨_scrutineeCode, _compiledCases, _compiledDefault,
        _hCompileScrutinee, _hCompileCases, _hCompileDefault,
        _hHeadCode, hAfterLocals⟩ :=
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
    ⟨afterState, headLower, headCode, tail, hCompiled, hLower,
      hHeadCompile, hDefaultShape.1.trans hCasesShape.1,
      hDefaultShape.2.trans hCasesShape.2,
      hScoped.1, hScoped.2.1, hScoped.2.2,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/--
Construct the exact selected `switch` lexical cursor from pass-owned planning,
lowering, and compilation components.

This is the common bridge used by regular and abrupt selected-body outcomes.
-/
theorem CoreCursor.switchSelectedCursorOfComponents
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
          locals ++ AllocationSupport.functionEnv root.slots :=
        hEnv
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

/--
Decompose a selected `switch` branch into its exact planner-owned lexical body
cursor and the outer tail cursor.

Case traversal remains owned by allocation lowering. This theorem only lifts
the selected planner entry into the enclosing cursor's validated recipe and
packages the already-selected Locals compilation.
-/
theorem CoreCursor.switchSelectedCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
          Locals.finishScoped localsCtx bodyCursor.finalLocals
              bodyCursor.compiled =
            some selectedTarget ∧
          selectedStart.allocation.env =
            lowerState.allocation.env ∧
          afterState.allocation.env =
            lowerState.allocation.env ∧
          afterState.layout = lowerState.layout ∧
          Functions.Scope.ExprScoped live scrutinee ∧
          Functions.Scope.Block.Scoped live selected := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hTailPlanning, _hTailPlan, _hTailFinalState, _hTailFinalLocals,
        hLower, hCompile, _hLowered, hCompiled, hScopedStmt⟩ :=
    cursor.cons
  obtain
      ⟨loweredScrutinee, loweredCases, afterCases, loweredDefault,
        _hLowerScrutinee, hLowerCases, hLowerDefault, hHeadLower⟩ :=
    AllocationLowering.lowerStmt_switch_components hLower
  obtain
      ⟨selectedLowered, selectedStart, selectedScopedFinal,
        selectedPlanning, hLoweredSelect, hLowerSelected,
        hSelectedPlanning, hSelectedEnv, _hSelectedLayout,
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
      ⟨_scrutineeCode, compiledCases, compiledDefault,
        _hCompileScrutinee, hCompileCases, hCompileDefault,
        _hHeadCode, hAfterLocals⟩ :=
    Locals.Block.compileOpen_single_switch_components hCompile
  obtain
      ⟨selectedTarget, selectedCode, selectedLocals,
        _hTargetSelect, hCompileSelected, hFinishSelected⟩ :=
    Locals.Switch.select_some_of_compile
      hCompileCases hCompileDefault hLoweredSelect
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
    ⟨afterState, headLower, headCode, tail, selectedStart,
      selectedPlanning, selectedTarget, bodyCursor, hCompiled, hLower,
      hHeadCompile, ?_, hSelectedEnv,
      hDefaultShape.1.trans hCasesShape.1,
      hDefaultShape.2.trans hCasesShape.2, hScoped.1,
      hSelectedScoped⟩
  rw [hBodyCode, hBodyLocals]
  exact hFinishSelected

/--
Decompose a `for` statement into the exact loop-scope initializer cursor,
lexical post/body cursors, condition code, and outer tail cursor.

The validated loop plan is recorded after planning the scoped post and body.
Those scoped blocks preserve the loop environment while advancing fresh slots,
so the initializer cursor uses `lexicalOfPlanState` to separate its runtime
endpoint from the scope-plan endpoint.
-/
theorem CoreCursor.forCursors
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
      ∃ initLocals postLocals bodyLocals : Locals.Ctx,
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
          AllocationLowering.lowerExpr
              root.lowerCtx loopState cond =
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
      (by
        simpa [postEntered] using hInitPlanning)
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
      (by
        simpa [bodyEntered] using hPostPlanning)
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
      ⟨hTailPlan, hTailFinalState, hTailFinalLocals⟩⟩
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

theorem CoreCursor.final_env_extension
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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

/--
Every binding visible at a cursor position has the same slot in the selected
function's final lowered body state.
-/
theorem CoreCursor.bodyFinal_lookup_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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

/--
Every source-live name at a cursor position has a checked slot in the current
lowering environment.
-/
theorem CoreCursor.lookupSlot_of_live
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx) :
    compilation.frameName ∉
      AllocationObserverRelation.currentStackOrder cursor.plan live := by
  intro hFrame
  exact
    cursor.frameName_not_mem_live
      (AllocationObserverRelation.mem_live_of_mem_currentStackOrder hFrame)

/--
Recover the exact runtime stack order at a recursive body position from the
cursor's scope-owned allocation plan. Future declarations are filtered out;
only already active locals and the fixed function signature remain.
-/
theorem CoreCursor.currentStackOrder_of_active
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    AllocationObserverRelation.currentStackOrder cursor.plan live =
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
  unfold AllocationObserverRelation.currentStackOrder
  rw [hEntries]
  exact hOrder

theorem CoreCursor.currentStackOrder
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
        AllocationObserverRelation.currentStackOrder cursor.plan live =
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
            (MixedAllocation.mem_stackEntries_iff.mpr ⟨hAdded, hSlot⟩))
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    have hSlot :
        slot ∉ compilation.stackSlots := by
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

/--
Classify a declaration from adjacent cursor positions. The selected final plan
decides stack versus scratch placement, while the active-environment theorem
proves the corresponding dynamic stack-order change.
-/
theorem CoreCursor.declarationPlacement
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
        simpa
          [root.lowerCtxShared.stackSlots]
          using
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
        AllocationObserverRelation.currentStackOrder
            cursor.plan (name :: live) =
            MixedAllocation.stackOrder compilation.stackSlots
                ((name, cursor.planning.allocation.nextSlot) :: locals) ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse :=
          hTailOrder
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                ((name, lowerState.allocation.nextSlot) :: locals) ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse := by
          rw [hNext]
        _ =
            name ::
              (MixedAllocation.stackOrder compilation.stackSlots locals ++
                MixedAllocation.stackOrder compilation.stackSlots
                    root.slots.returns.reverse ++
                MixedAllocation.stackOrder compilation.stackSlots
                    root.slots.params.reverse) := by
          rw [hConsOrder]
          simp [List.append_assoc]
        _ =
            name ::
              AllocationObserverRelation.currentStackOrder
                cursor.plan live := by
          rw [hCurrentOrder]
  | false =>
      have hLocation :=
        tail.location_scratch_of_lookup_aux hLookupAfter hStack
      rw [hPlan] at hLocation
      have hSlotNotMem :
          lowerState.allocation.nextSlot ∉ compilation.stackSlots := by
        simpa
          [root.lowerCtxShared.stackSlots]
          using
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
        AllocationObserverRelation.currentStackOrder
            cursor.plan (name :: live) =
            MixedAllocation.stackOrder compilation.stackSlots
                ((name, cursor.planning.allocation.nextSlot) :: locals) ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse :=
          hTailOrder
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                ((name, lowerState.allocation.nextSlot) :: locals) ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse := by
          rw [hNext]
        _ =
            MixedAllocation.stackOrder compilation.stackSlots locals ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                  root.slots.params.reverse := by
          rw [hConsOrder]
        _ =
            AllocationObserverRelation.currentStackOrder
              cursor.plan live := hCurrentOrder.symm

theorem CoreCursor.location_stack_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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

/--
Two synchronized cursors beginning at the same source environment agree on
the realization of every currently live binding.

The cursors may own different lexical scope plans and different remaining
blocks. Stack depths are therefore allowed to differ, while the runtime stack
order and every scratch slot agree exactly.
-/
theorem CoreCursor.planAgreesOn
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    AllocationObserverRelation.PlanAgreesOn
      left.plan right.plan live := by
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
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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

/--
Construct the exact post-declaration compiler context from adjacent body
cursors and the real allocation/Locals compiler equations.

The theorem is representation-neutral: stack declarations advance the scratch
frame depth when present, while scratch declarations require and preserve the
existing frame-backed mode.
-/
theorem CoreCursor.letContext
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
      AllocationObserverContext.ActivationExprContext
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
      AllocationObserverContext.ActivationExprContext
          root.lowerCtx afterState afterLocals cursor.plan
          (name :: live) afterMode ∧
        AllocationObserverStatement.LetLeaf.ModeTransition
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
                    AllocationObserverContext.ActivationExprContext.stack_of_layout
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
                    AllocationObserverContext.ActivationExprContext.scratch_of_layout
                      cursor.planWF
                  · simp [Locals.Ctx.withLayout,
                      hBeforeScratch.layout]
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
                              (1 + (frameDepth + 1)) =
                            none := by
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
                              (1 + (frameDepth + 1)) =
                            some op := by
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
                        AllocationObserverContext.ActivationExprContext.scratch_of_layout
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

/-- Preserve the empty synchronized body cursor. -/
theorem CoreCursor.nilRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := [] } lowerState localsCtx)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target) :
    AllocationObserverOutcome.BlockRuntimeResult
      program.memoryContract config allocatorDepth transcript
      root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
      root.returns live frameBase mode program sourceCtx
      { stmts := [] } source expressions.toStructured
      { stmts :=
          Expressions.StmtList.toStructured cursor.compiled }
      target
      (Functions.Source.Effectful.Outcome.regular source)
      (Structured.EffectSemantics.Outcome.regular target)
      sourceCtx := by
  have hLower := cursor.lower
  simp [AllocationLowering.lowerBlockOpen,
    AllocationLowering.lowerStmtList] at hLower
  obtain ⟨hLowered, hFinalState⟩ := hLower
  have hCompile := cursor.compile
  rw [← hLowered] at hCompile
  simp [Locals.Block.compileOpen] at hCompile
  obtain ⟨hCompiled, hFinalLocals⟩ := hCompile
  simpa [hFinalState, hFinalLocals, hCompiled,
    Expressions.StmtList.toStructured] using
    (AllocationObserverOutcome.BlockRuntimeResult.nil hInvariant)

/--
Compose a regular statement result with the recursively preserved exact tail
cursor.

The endpoint equalities come from `Cursor.cons`; this theorem is the only place
the source-fuel dispatcher transports the tail's compiler-owned final
allocation and Locals contexts back to the parent cursor.
-/
theorem CoreCursor.consRegularRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive finalLive : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {initialMode midMode : ActivationMode}
    {sourceCtx midCtx finalCtx : Functions.Source.Ctx}
    {source sourceMid :
      Functions.ObserverSemantics.State transcript}
    {target targetMid : Structured.ObserverSemantics.State transcript}
    {headCode : List Expressions.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope afterLive { stmts := rest }
        afterState afterLocals)
    (hTailPlan : tail.plan = cursor.plan)
    (hTailFinalState : tail.finalState = cursor.finalState)
    (hTailFinalLocals : tail.finalLocals = cursor.finalLocals)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hHead :
      AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        root.lowerCtx afterState afterLocals cursor.plan afterLive
        frameBase initialMode midMode program sourceCtx stmt source
        expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceMid targetMid midCtx)
    (hControl : AllocationObserverOutcome.SameControl sourceCtx midCtx)
    (hTail :
      AllocationObserverOutcome.BlockRuntimeResult
        program.memoryContract config allocatorDepth transcript
        root.lowerCtx tail.finalState tail.finalLocals tail.plan
        root.returns finalLive frameBase midMode program midCtx
        { stmts := rest } sourceMid expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured tail.compiled }
        targetMid sourceOutcome targetOutcome finalCtx) :
    AllocationObserverOutcome.BlockRuntimeResult
      program.memoryContract config allocatorDepth transcript
      root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
      root.returns finalLive frameBase initialMode program sourceCtx
      { stmts := stmt :: rest } source expressions.toStructured
      { stmts :=
          Expressions.StmtList.toStructured cursor.compiled }
      target sourceOutcome targetOutcome finalCtx := by
  rw [hTailPlan, hTailFinalState, hTailFinalLocals] at hTail
  rw [hCompiled, Expressions.StmtList.toStructured_append]
  exact
    AllocationObserverOutcome.BlockRuntimeResult.cons_regular
      hHead hControl hTail

/--
Compose an abrupt statement result with its statically compiled but
dynamically unreachable tail.
-/
theorem CoreCursor.consNonregularRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live finalLive : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {initialMode finalMode : ActivationMode}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {headCode tailCode : List Expressions.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (hCompiled : cursor.compiled = headCode ++ tailCode)
    (hHead :
      AllocationObserverOutcome.NonregularStmtRuntimeForward
        program.memoryContract config allocatorDepth transcript
        cursor.plan
        (AllocationObserverOutcome.outcomeLive
          root.returns finalLive sourceCtx sourceOutcome.mode)
        frameBase initialMode finalMode program sourceCtx stmt source
        expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceOutcome targetOutcome stmtCtx) :
    AllocationObserverOutcome.BlockRuntimeResult
      program.memoryContract config allocatorDepth transcript
      root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
      root.returns finalLive frameBase initialMode program sourceCtx
      { stmts := stmt :: rest } source expressions.toStructured
      { stmts :=
          Expressions.StmtList.toStructured cursor.compiled }
      target sourceOutcome targetOutcome sourceCtx := by
  rw [hCompiled, Expressions.StmtList.toStructured_append]
  exact
    AllocationObserverOutcome.BlockRuntimeResult.cons_nonregular hHead

/--
Preserve the empty synchronized body cursor under the compiler-selected
resource mode.
-/
theorem CoreCursor.nilResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {resource : AllocationObserverRelation.Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := [] } lowerState localsCtx)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode source target) :
    AllocationObserverOutcome.BlockResourceResult
      program.memoryContract resource allocatorDepth transcript
      root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
      root.returns live frameBase mode program sourceCtx
      { stmts := [] } source expressions.toStructured
      { stmts :=
          Expressions.StmtList.toStructured cursor.compiled }
      target
      (Functions.Source.Effectful.Outcome.regular source)
      (Structured.EffectSemantics.Outcome.regular target)
      sourceCtx := by
  have hLower := cursor.lower
  simp [AllocationLowering.lowerBlockOpen,
    AllocationLowering.lowerStmtList] at hLower
  obtain ⟨hLowered, hFinalState⟩ := hLower
  have hCompile := cursor.compile
  rw [← hLowered] at hCompile
  simp [Locals.Block.compileOpen] at hCompile
  obtain ⟨hCompiled, hFinalLocals⟩ := hCompile
  simpa [hFinalState, hFinalLocals, hCompiled,
    Expressions.StmtList.toStructured] using
    (AllocationObserverOutcome.BlockResourceResult.nil hInvariant)

/--
Compose a resource-indexed regular statement result with its exact
recursively preserved tail cursor.
-/
theorem CoreCursor.consRegularResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive finalLive : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {resource : AllocationObserverRelation.Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {initialMode midMode : ActivationMode}
    {sourceCtx midCtx finalCtx : Functions.Source.Ctx}
    {source sourceMid :
      Functions.ObserverSemantics.State transcript}
    {target targetMid : Structured.ObserverSemantics.State transcript}
    {headCode : List Expressions.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope afterLive { stmts := rest }
        afterState afterLocals)
    (hTailPlan : tail.plan = cursor.plan)
    (hTailFinalState : tail.finalState = cursor.finalState)
    (hTailFinalLocals : tail.finalLocals = cursor.finalLocals)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hHead :
      AllocationObserverStatement.Sequence.RegularStmtResourceInvariantForward
        program.memoryContract resource allocatorDepth transcript
        root.lowerCtx afterState afterLocals cursor.plan afterLive
        frameBase initialMode midMode program sourceCtx stmt source
        expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceMid targetMid midCtx)
    (hControl : AllocationObserverOutcome.SameControl sourceCtx midCtx)
    (hTail :
      AllocationObserverOutcome.BlockResourceResult
        program.memoryContract resource allocatorDepth transcript
        root.lowerCtx tail.finalState tail.finalLocals tail.plan
        root.returns finalLive frameBase midMode program midCtx
        { stmts := rest } sourceMid expressions.toStructured
        { stmts :=
            Expressions.StmtList.toStructured tail.compiled }
        targetMid sourceOutcome targetOutcome finalCtx) :
    AllocationObserverOutcome.BlockResourceResult
      program.memoryContract resource allocatorDepth transcript
      root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
      root.returns finalLive frameBase initialMode program sourceCtx
      { stmts := stmt :: rest } source expressions.toStructured
      { stmts :=
          Expressions.StmtList.toStructured cursor.compiled }
      target sourceOutcome targetOutcome finalCtx := by
  rw [hTailPlan, hTailFinalState, hTailFinalLocals] at hTail
  rw [hCompiled, Expressions.StmtList.toStructured_append]
  exact
    AllocationObserverOutcome.BlockResourceResult.cons_regular
      hHead hControl hTail

/--
Compose a resource-indexed abrupt statement result with its statically
compiled but dynamically unreachable tail.
-/
theorem CoreCursor.consNonregularResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live finalLive : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {resource : AllocationObserverRelation.Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {initialMode finalMode : ActivationMode}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {headCode tailCode : List Expressions.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (hCompiled : cursor.compiled = headCode ++ tailCode)
    (hHead :
      AllocationObserverOutcome.NonregularStmtResourceForward
        program.memoryContract resource allocatorDepth transcript cursor.plan
        (AllocationObserverOutcome.outcomeLive
          root.returns finalLive sourceCtx sourceOutcome.mode)
        frameBase initialMode finalMode program sourceCtx stmt source
        expressions.toStructured target
        (Expressions.StmtList.toStructured headCode)
        sourceOutcome targetOutcome stmtCtx) :
    AllocationObserverOutcome.BlockResourceResult
      program.memoryContract resource allocatorDepth transcript
      root.lowerCtx cursor.finalState cursor.finalLocals cursor.plan
      root.returns finalLive frameBase initialMode program sourceCtx
      { stmts := stmt :: rest } source expressions.toStructured
      { stmts :=
          Expressions.StmtList.toStructured cursor.compiled }
      target sourceOutcome targetOutcome sourceCtx := by
  rw [hCompiled, Expressions.StmtList.toStructured_append]
  exact
    AllocationObserverOutcome.BlockResourceResult.cons_nonregular hHead

/- Preserve one expression statement directly from a synchronized body cursor. -/
theorem CoreCursor.exprRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {expr : Functions.Expr 0}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .expr expr :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript expr source sourceFinal values)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.expr expr) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular sourceFinal)
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport beforeState afterState beforeLocals afterLocals
            live (.expr expr) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.expr_of_compilers
      hConfig hSafe hScoped hInvariant hLower hCompile
  exact
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .regular hForward (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers hScoped hLower hCompile,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/--
Preserve one assignment directly from a synchronized body cursor.
-/
theorem CoreCursor.assignRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .assign name valueExpr :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript valueExpr
        source sourceAfterValue [value])
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.assign name valueExpr) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).withVars
                sourceAfterValue
                (Locals.Source.Store.insert
                  ((Functions.ObserverSemantics.stateModel transcript).vars
                    sourceAfterValue)
                  name value)))
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport beforeState afterState beforeLocals afterLocals
            live (.assign name valueExpr) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  have hContains :
      Locals.Source.Store.contains
          ((Functions.ObserverSemantics.stateModel transcript).vars source)
          name =
        true := by
    change Locals.Source.Store.contains source.source.vars name = true
    obtain ⟨old, hOld⟩ :=
      hInvariant.activation.defined name hScoped.1
    simp [Locals.Source.Store.contains, hOld]
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.assign_of_compilers
      hConfig hContains hSafe hScoped.2 hScoped.1 hInvariant hLower hCompile
  exact
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .regular hForward (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers hScoped hLower hCompile,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/--
Preserve one source `let` directly from a synchronized body cursor.

The theorem consumes only the canonical safe expression evaluation, the real
allocation/Locals compiler artifacts owned by the cursor, and the activation
runtime invariant.  It returns the exact tail cursor needed by block
recursion, without exposing generated declaration evidence.
-/
theorem CoreCursor.letRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .let_ name valueExpr :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript valueExpr
        source sourceAfterValue [value])
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope (name :: live)
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns (name :: live) frameBase beforeMode program
            sourceCtx (.let_ name valueExpr) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).insert
                sourceAfterValue name value))
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            { sourceCtx with scope := name :: sourceCtx.scope } ∧
          StepTransport beforeState afterState beforeLocals afterLocals
            live (.let_ name valueExpr) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨afterMode, hAfter, hMode⟩ :=
    cursor.letContext tail hPlanning hPlan hInvariant.activation.compiler
      hLower hCompile
  have hNameFrame : name ≠ root.lowerCtx.frameName := by
    intro hEq
    apply tail.frameName_not_mem_live
    simp [Functions.Scope.Stmt.outEnv, hEq,
      root.lowerCtxShared.frameName]
  have hScratchBound :
      ∀ frameDepth frameWords slot,
        beforeMode = .scratch frameDepth frameWords →
        cursor.plan.location? name = some (.scratch slot) →
        slot < frameWords := by
    intro frameDepth frameWords slot hBeforeMode hLocation
    have hOwned := hInvariant.frame
    rw [hBeforeMode] at hOwned
    cases hOwned with
    | scratch _ hWords =>
        obtain
            ⟨_reservation, _hReservation, _hAllocator, _hFirst, _hLimit,
              hConfigWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
          AllocationSupport.scratchFrameConfig?_sound hConfig
        calc
          slot < compilation.recipe.frameWords :=
            cursor.scratch_bound_of_location hLocation
          _ = config.frameWords := hConfigWords.symm
          _ = frameWords := hWords.symm
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.let_of_compilers
      hConfig hSafe hAfter hMode hScoped.2 rfl
        hNameFrame hScratchBound hInvariant hLower hCompile
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .regular hForward ?_,
      StepTransport.of_compilers hScoped hLower hCompile,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩
  exact ⟨rfl, rfl, rfl⟩

/--
Preserve one expression statement in a compiler-selected stack-only
activation.
-/
theorem CoreCursor.exprStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {expr : Functions.Expr 0}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .expr expr :: rest }
        beforeState beforeLocals)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript expr source sourceFinal values)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.expr expr) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular sourceFinal)
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport beforeState afterState beforeLocals afterLocals
            live (.expr expr) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtInvariantForward.expr_of_compilers
      hSafe hScoped hInvariant.activation hLower hCompile
  exact
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled,
      .regular (hForward.toStackResource hInvariant.owned)
        (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers hScoped hLower hCompile,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/--
Preserve one assignment in a compiler-selected stack-only activation.
-/
theorem CoreCursor.assignStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .assign name valueExpr :: rest }
        beforeState beforeLocals)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript valueExpr source
        sourceAfterValue [value])
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.assign name valueExpr) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).withVars
                sourceAfterValue
                (Locals.Source.Store.insert
                  ((Functions.ObserverSemantics.stateModel transcript).vars
                    sourceAfterValue)
                  name value)))
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport beforeState afterState beforeLocals afterLocals
            live (.assign name valueExpr) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  have hContains :
      Locals.Source.Store.contains
          ((Functions.ObserverSemantics.stateModel transcript).vars source)
          name =
        true := by
    change Locals.Source.Store.contains source.source.vars name = true
    obtain ⟨old, hOld⟩ :=
      hInvariant.activation.defined name hScoped.1
    simp [Locals.Source.Store.contains, hOld]
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtInvariantForward.assign_of_compilers
      hContains hSafe hScoped.2 hScoped.1 hInvariant.activation
      hLower hCompile
  exact
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled,
      .regular (hForward.toStackResource hInvariant.owned)
        (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers hScoped hLower hCompile,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/--
Preserve one declaration in a compiler-selected stack-only activation.
-/
theorem CoreCursor.letStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {valueExpr : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .let_ name valueExpr :: rest }
        beforeState beforeLocals)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript valueExpr source
        sourceAfterValue [value])
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope (name :: live)
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns (name :: live) frameBase beforeMode program
            sourceCtx (.let_ name valueExpr) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).insert
                sourceAfterValue name value))
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            { sourceCtx with scope := name :: sourceCtx.scope } ∧
          StepTransport beforeState afterState beforeLocals afterLocals
            live (.let_ name valueExpr) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨afterMode, hAfter, hMode⟩ :=
    cursor.letContext tail hPlanning hPlan
      hInvariant.activation.compiler hLower hCompile
  have hNameFrame : name ≠ root.lowerCtx.frameName := by
    intro hEq
    apply tail.frameName_not_mem_live
    simp [Functions.Scope.Stmt.outEnv, hEq,
      root.lowerCtxShared.frameName]
  have hScratchBound :
      ∀ frameDepth frameWords slot,
        beforeMode = .scratch frameDepth frameWords →
        cursor.plan.location? name = some (.scratch slot) →
        slot < frameWords := by
    intro frameDepth frameWords slot hBeforeMode _hLocation
    rw [hBeforeMode] at hInvariant
    cases hInvariant.owned
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtInvariantForward.let_of_compilers
      hSafe hAfter hMode hScoped.2 rfl hNameFrame hScratchBound
      hInvariant.activation hLower hCompile
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled,
      .regular (hForward.toStackResource hInvariant.owned) ?_,
      StepTransport.of_compilers hScoped hLower hCompile,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩
  exact ⟨rfl, rfl, rfl⟩

/--
Preserve one source `break` directly from a synchronized body cursor.

The destination transition is static pass-owned data. The source-fuel
dispatcher will derive it from the enclosing loop destination invariant.
-/
theorem CoreCursor.brkRuntimeResultExact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth targetDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .brk :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : beforeLocals.breakDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase beforeMode program sourceCtx
            .brk source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.brk
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                afterLive source))
            (Structured.EffectSemantics.Outcome.brk targetFinal)
            sourceCtx ∧
          AllocationObserverRelation.ActivationStateRel
            program.memoryContract cursor.plan afterLive 0 frameBase afterMode
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source)
            targetFinal ∧
          targetFinal.source.evm.stack.length = targetDepth ∧
          targetFinal.source.evm.toMachineState =
            target.source.evm.toMachineState ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hTailFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  obtain
      ⟨targetFinal, hForward, hState, hFinalStack, hMachine⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.brk_of_invariant_exact
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hSourceScope hTargetDepth hTransition hInvariant hLower hCompile
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := afterMode) ?_,
      hState, hFinalStack, hMachine,
      ⟨hPlan, hTailFinalState, hFinalLocals⟩⟩
  simpa [AllocationObserverOutcome.outcomeLive, hSourceScope] using hForward

theorem CoreCursor.brkRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth targetDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .brk :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : beforeLocals.breakDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase beforeMode program sourceCtx
            .brk source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.brk
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                afterLive source))
            (Structured.EffectSemantics.Outcome.brk targetFinal)
            sourceCtx ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headCode, tail, targetFinal,
        hCompiled, hRuntime, _hState, _hStack, _hMachine, hExact⟩ :=
    cursor.brkRuntimeResultExact hSourceScope hTargetDepth hTransition hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, hRuntime, hExact⟩

/--
Preserve one source `break` in a compiler-selected stack-only activation,
retaining the exact canonical control destination facts.
-/
theorem CoreCursor.brkStackResourceResultExact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth targetDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .brk :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : beforeLocals.breakDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase beforeMode program sourceCtx
            .brk source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.brk
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                afterLive source))
            (Structured.EffectSemantics.Outcome.brk targetFinal)
            sourceCtx ∧
          AllocationObserverRelation.ActivationStateRel
            program.memoryContract cursor.plan afterLive 0 frameBase afterMode
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source)
            targetFinal ∧
          targetFinal.source.evm.stack.length = targetDepth ∧
          targetFinal.source.evm.toMachineState =
            target.source.evm.toMachineState ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hTailFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  obtain
      ⟨targetFinal, hForward, hState, hFinalStack, hMachine⟩ :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.brk_of_invariant_exact
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hSourceScope hTargetDepth hTransition hInvariant.activation
      hLower hCompile
  have hAfterMode : afterMode = .stack :=
    hTransition.sameFrame.right_eq_stack_of_left_eq_stack hInvariant.owned
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := afterMode) ?_,
      hState, hFinalStack, hMachine,
      ⟨hPlan, hTailFinalState, hFinalLocals⟩⟩
  simpa [AllocationObserverOutcome.outcomeLive, hSourceScope] using
    hForward.toStackResource
      (allocatorDepth := allocatorDepth) hInvariant.owned hAfterMode

/--
Preserve one source `continue` directly from a synchronized body cursor.
-/
theorem CoreCursor.contRuntimeResultExact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth targetDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .cont :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : beforeLocals.continueDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase beforeMode program sourceCtx
            .cont source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.cont
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                afterLive source))
            (Structured.EffectSemantics.Outcome.cont targetFinal)
            sourceCtx ∧
          AllocationObserverRelation.ActivationStateRel
            program.memoryContract cursor.plan afterLive 0 frameBase afterMode
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source)
            targetFinal ∧
          targetFinal.source.evm.stack.length = targetDepth ∧
          targetFinal.source.evm.toMachineState =
            target.source.evm.toMachineState ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hTailFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  obtain
      ⟨targetFinal, hForward, hState, hFinalStack, hMachine⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.cont_of_invariant_exact
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hSourceScope hTargetDepth hTransition hInvariant hLower hCompile
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := afterMode) ?_,
      hState, hFinalStack, hMachine,
      ⟨hPlan, hTailFinalState, hFinalLocals⟩⟩
  simpa [AllocationObserverOutcome.outcomeLive, hSourceScope] using hForward

theorem CoreCursor.contRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth targetDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .cont :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : beforeLocals.continueDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase beforeMode program sourceCtx
            .cont source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.cont
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                afterLive source))
            (Structured.EffectSemantics.Outcome.cont targetFinal)
            sourceCtx ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headCode, tail, targetFinal,
        hCompiled, hRuntime, _hState, _hStack, _hMachine, hExact⟩ :=
    cursor.contRuntimeResultExact hSourceScope hTargetDepth hTransition
      hInvariant
  exact
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, hRuntime, hExact⟩

/--
Preserve one source `continue` in a compiler-selected stack-only activation,
retaining the exact canonical control destination facts.
-/
theorem CoreCursor.contStackResourceResultExact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth targetDepth frameBase : Nat}
    {transcript : Trace}
    {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .cont :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : beforeLocals.continueDepth? = some targetDepth)
    (hTransition :
      AllocationObserverCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase beforeMode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase beforeMode program sourceCtx
            .cont source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.cont
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                afterLive source))
            (Structured.EffectSemantics.Outcome.cont targetFinal)
            sourceCtx ∧
          AllocationObserverRelation.ActivationStateRel
            program.memoryContract cursor.plan afterLive 0 frameBase afterMode
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source)
            targetFinal ∧
          targetFinal.source.evm.stack.length = targetDepth ∧
          targetFinal.source.evm.toMachineState =
            target.source.evm.toMachineState ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hTailFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  obtain
      ⟨targetFinal, hForward, hState, hFinalStack, hMachine⟩ :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.cont_of_invariant_exact
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hSourceScope hTargetDepth hTransition hInvariant.activation
      hLower hCompile
  have hAfterMode : afterMode = .stack :=
    hTransition.sameFrame.right_eq_stack_of_left_eq_stack hInvariant.owned
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := afterMode) ?_,
      hState, hFinalStack, hMachine,
      ⟨hPlan, hTailFinalState, hFinalLocals⟩⟩
  simpa [AllocationObserverOutcome.outcomeLive, hSourceScope] using
    hForward.toStackResource
      (allocatorDepth := allocatorDepth) hInvariant.owned hAfterMode

/--
Preserve one source `leave` directly from a synchronized body cursor.
-/
theorem CoreCursor.leaveRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live functionScope : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .leave :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hTargetDepth : beforeLocals.leaveDepth? = some 0)
    (hRetc : beforeLocals.leaveRetc = root.returns.length)
    (hReturnFrame : target.source.returns ≠ [])
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            .leave source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.leave
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                functionScope source))
            (Structured.EffectSemantics.Outcome.leave targetFinal)
            sourceCtx ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.leave_of_invariant
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hConfig hSourceScope hControl.returnsLive
      (hControl.leaveScope functionScope hSourceScope)
      hTargetDepth hRetc hReturnFrame hInvariant hLower hCompile
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := mode) ?_,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩
  simpa [AllocationObserverOutcome.outcomeLive] using hForward

/--
Preserve one source `leave` in a compiler-selected stack-only activation.
-/
theorem CoreCursor.leaveStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live functionScope : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .leave :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hTargetDepth : beforeLocals.leaveDepth? = some 0)
    (hRetc : beforeLocals.leaveRetc = root.returns.length)
    (hReturnFrame : target.source.returns ≠ [])
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            .leave source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.leave
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                functionScope source))
            (Structured.EffectSemantics.Outcome.leave targetFinal)
            sourceCtx ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.leave_of_invariant
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hSourceScope hControl.returnsLive
      (hControl.leaveScope functionScope hSourceScope)
      hTargetDepth hRetc hReturnFrame hInvariant.activation hLower hCompile
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := mode) ?_,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩
  simpa [AllocationObserverOutcome.outcomeLive, hSourceScope] using
    hForward.toStackResource
      (allocatorDepth := allocatorDepth) hInvariant.owned hInvariant.owned

/--
Preserve one terminal-with-arguments statement directly from a synchronized
body cursor.
-/
theorem CoreCursor.terminalArgsRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source afterArgs sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .terminalArgs kind args :: rest }
        beforeState beforeLocals)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hArgs :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        program.memoryContract transcript args source afterArgs values)
    (hMemory :
      AllocationObserverSafety.TerminalMemorySafe
        program.memoryContract kind values)
    (hTerminal :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind afterArgs values =
        .ok sourceFinal)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.terminalArgs kind args) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
            (Structured.EffectSemantics.Outcome.halt kind targetFinal)
            sourceCtx ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.terminalArgs_of_invariant
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hConfig hArgs hMemory hTerminal hScoped hInvariant hLower hCompile
  exact
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := mode) hForward,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/--
Preserve one terminal-with-arguments statement in a compiler-selected
stack-only activation.
-/
theorem CoreCursor.terminalArgsStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source afterArgs sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .terminalArgs kind args :: rest }
        beforeState beforeLocals)
    (hArgs :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        program.memoryContract transcript args source afterArgs values)
    (hMemory :
      AllocationObserverSafety.TerminalMemorySafe
        program.memoryContract kind values)
    (hTerminal :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind afterArgs values =
        .ok sourceFinal)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.terminalArgs kind args) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
            (Structured.EffectSemantics.Outcome.halt kind targetFinal)
            sourceCtx ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.terminalArgs_of_compilers
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hArgs hMemory hTerminal hInvariant.activation.compiler hScoped hLower
      hCompile hInvariant.activation.state
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := mode) ?_,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩
  simpa [AllocationObserverOutcome.outcomeLive] using
    hForward.toStackResource
      (allocatorDepth := allocatorDepth) hInvariant.owned hInvariant.owned

/--
Preserve one plain terminal statement, including the compiler-emitted cleanup
of every dead local stack slot.
-/
theorem CoreCursor.terminalRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .terminal kind :: rest }
        beforeState beforeLocals)
    (hMemory :
      AllocationObserverSafety.TerminalMemorySafe
        program.memoryContract kind [])
    (hTerminal :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind source [] =
        .ok sourceFinal)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.terminal kind) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
            (Structured.EffectSemantics.Outcome.halt kind targetFinal)
            sourceCtx ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.terminal_of_invariant
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hMemory hTerminal hInvariant hLower hCompile
  exact
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := mode) hForward,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩

/--
Preserve one plain terminal statement in a compiler-selected stack-only
activation.
-/
theorem CoreCursor.terminalStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (cursor :
      CoreCursor root scope live
        { stmts := .terminal kind :: rest }
        beforeState beforeLocals)
    (hMemory :
      AllocationObserverSafety.TerminalMemorySafe
        program.memoryContract kind [])
    (hTerminal :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind source [] =
        .ok sourceFinal)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        beforeState beforeLocals cursor.plan live frameBase mode
        source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState afterLocals,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState afterLocals cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.terminal kind) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
            (Structured.EffectSemantics.Outcome.halt kind targetFinal)
            sourceCtx ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ :=
    cursor.cons
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.terminal_of_invariant
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hMemory hTerminal hInvariant.activation hLower hCompile
  refine
    ⟨afterState, afterLocals, headCode, tail, targetFinal,
      hCompiled, .nonregular (finalMode := mode) ?_,
      ⟨hPlan, hFinalState, hFinalLocals⟩⟩
  simpa [AllocationObserverOutcome.outcomeLive] using
    hForward.toStackResource
      (allocatorDepth := allocatorDepth) hInvariant.owned hInvariant.owned

/--
Preserve the false branch of one synchronized `if` cursor.

The nested body cursor is still constructed from the real passes, but the
canonical source condition proves it unreachable.
-/
theorem CoreCursor.ifFalseRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterCond :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript cond source sourceAfterCond [value])
    (hFalse : value = EvmYul.UInt256.ofNat 0)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.if_ cond body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular sourceAfterCond)
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.if_ cond body) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, headLower, headCode, tail, _loweredCond, _condCode,
        _targetBody, _bodyCursor, hCompiled, hLower, hCompile, _hHeadCode,
        _hLowerCond, _hCompileCond, _hFinish, _hAfterEnv, _hAfterLayout,
        hCondScoped, hExact⟩ :=
    cursor.ifCursors
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.if_false_of_components
      hConfig hSafe hFalse hCondScoped hInvariant hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetFinal, hCompiled,
      .regular hForward (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact⟩

/--
Preserve the false branch of one synchronized `if` in a compiler-selected
stack-only activation.
-/
theorem CoreCursor.ifFalseStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterCond :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript cond source sourceAfterCond [value])
    (hFalse : value = EvmYul.UInt256.ofNat 0)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.if_ cond body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular sourceAfterCond)
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.if_ cond body) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, headLower, headCode, tail, _loweredCond, _condCode,
        _targetBody, _bodyCursor, hCompiled, hLower, hCompile, _hHeadCode,
        _hLowerCond, _hCompileCond, _hFinish, _hAfterEnv, _hAfterLayout,
        hCondScoped, hExact⟩ :=
    cursor.ifCursors
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtInvariantForward.if_false_of_components
      hSafe hFalse hCondScoped hInvariant.activation hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetFinal, hCompiled,
      .regular (hForward.toStackResource hInvariant.owned)
        (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact⟩

/--
Preserve the true branch of one synchronized `if` whose lexical body returns
regularly.
-/
theorem CoreCursor.ifTrueRegularRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceAfterCond sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript cond source sourceAfterCond [value])
    (hTrue :
      (value != EvmYul.UInt256.ofNat 0) = true)
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ bodyCursor :
          CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx,
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth root.lowerCtx
              lowerState localsCtx bodyCursor.plan live frameBase mode
              sourceAfterCond targetBodyStart →
          targetBodyStart.source.returns = target.source.returns →
          ∃ targetBodyFinal,
            AllocationObserverOutcome.BlockRuntimeResult
              program.memoryContract config allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live body)
              frameBase mode program sourceCtx body sourceAfterCond
              expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart
              (Functions.Source.Effectful.Outcome.regular sourceBodyFinal)
              (Structured.EffectSemantics.Outcome.regular targetBodyFinal)
              finalCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.if_ cond body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                live sourceBodyFinal))
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.if_ cond body) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, headLower, headCode, tail, _loweredCond,
        _condCode, _targetBody, bodyCursor, hCompiled, hLower,
        hCompile, _hHeadCode, _hLowerCond, _hCompileCond, _hFinish,
        _hAfterEnv, _hAfterLayout, hCondScoped, hExact⟩ :=
    cursor.ifCursors
  have hPlanAgree :
      AllocationObserverRelation.PlanAgreesOn
        bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.if_true_of_components
      (bodyPlan := bodyCursor.plan)
      (bodyLive := Functions.Scope.Block.outEnv live body)
      (sourceBodyFinal := sourceBodyFinal)
      (finalCtx := finalCtx)
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hConfig hSafe hTrue hCondScoped bodyCursor.sourceScoped
      hSourceScope
      (fun name hName =>
        Functions.Scope.Block.mem_outEnv hName)
      hInvariant
      (by
        intro loweredBody bodyLowerState bodyCode bodyLocals
          targetAfterCond hLowerBody hCompileBody hCondInvariant hReturns
        have hLowerEq :
            (loweredBody, bodyLowerState) =
              (bodyCursor.lowered, bodyCursor.finalState) :=
          Option.some.inj (hLowerBody.symm.trans bodyCursor.lower)
        cases hLowerEq
        have hCompileEq :
            (bodyCode, bodyLocals) =
              (bodyCursor.compiled, bodyCursor.finalLocals) :=
          Option.some.inj (hCompileBody.symm.trans bodyCursor.compile)
        cases hCompileEq
        have hBodyInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx lowerState localsCtx bodyCursor.plan
              live frameBase mode sourceAfterCond targetAfterCond :=
          hCondInvariant.transport_plan
            bodyCursor.planWF hPlanAgree.symm
        obtain ⟨targetBodyFinal, hBodyResult⟩ :=
          hBody bodyCursor hBodyInvariant hReturns
        cases hBodyResult with
        | @regular _ _ finalMode _ hBodyForward _hControl =>
            exact ⟨targetBodyFinal, finalMode, hBodyForward⟩
        | nonregular hMode _hBodyForward =>
            exact False.elim (hMode rfl))
      hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetFinal, hCompiled,
      .regular hForward (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact⟩

/--
Preserve the true branch of one synchronized `if` whose lexical body returns
regularly in a compiler-selected stack-only activation.
-/
theorem CoreCursor.ifTrueRegularStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceAfterCond sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript cond source sourceAfterCond [value])
    (hTrue :
      (value != EvmYul.UInt256.ofNat 0) = true)
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ bodyCursor :
          CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx,
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationResourceInvariant
              .stackOnly program.memoryContract allocatorDepth root.lowerCtx
              lowerState localsCtx bodyCursor.plan live frameBase mode
              sourceAfterCond targetBodyStart →
          targetBodyStart.source.returns = target.source.returns →
          ∃ targetBodyFinal,
            AllocationObserverOutcome.BlockResourceResult
              program.memoryContract .stackOnly allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live body)
              frameBase mode program sourceCtx body sourceAfterCond
              expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart
              (Functions.Source.Effectful.Outcome.regular sourceBodyFinal)
              (Structured.EffectSemantics.Outcome.regular targetBodyFinal)
              finalCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.if_ cond body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                live sourceBodyFinal))
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.if_ cond body) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, headLower, headCode, tail, _loweredCond,
        _condCode, _targetBody, bodyCursor, hCompiled, hLower,
        hCompile, _hHeadCode, _hLowerCond, _hCompileCond, _hFinish,
        _hAfterEnv, _hAfterLayout, hCondScoped, hExact⟩ :=
    cursor.ifCursors
  have hPlanAgree :
      AllocationObserverRelation.PlanAgreesOn
        bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtInvariantForward.if_true_of_components
      (bodyPlan := bodyCursor.plan)
      (bodyLive := Functions.Scope.Block.outEnv live body)
      (sourceBodyFinal := sourceBodyFinal)
      (finalCtx := finalCtx)
      (sourceProgram := program)
      (targetProgram := expressions.toStructured)
      hSafe hTrue hCondScoped bodyCursor.sourceScoped hSourceScope
      (fun name hName =>
        Functions.Scope.Block.mem_outEnv hName)
      hInvariant.activation
      (by
        intro loweredBody bodyLowerState bodyCode bodyLocals
          targetAfterCond hLowerBody hCompileBody hCondInvariant hReturns
        have hLowerEq :
            (loweredBody, bodyLowerState) =
              (bodyCursor.lowered, bodyCursor.finalState) :=
          Option.some.inj (hLowerBody.symm.trans bodyCursor.lower)
        cases hLowerEq
        have hCompileEq :
            (bodyCode, bodyLocals) =
              (bodyCursor.compiled, bodyCursor.finalLocals) :=
          Option.some.inj (hCompileBody.symm.trans bodyCursor.compile)
        cases hCompileEq
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx lowerState localsCtx
              bodyCursor.plan live frameBase mode sourceAfterCond
              targetAfterCond :=
          hCondInvariant.transport_plan
            bodyCursor.planWF hPlanAgree.symm
        obtain ⟨targetBodyFinal, hBodyResult⟩ :=
          hBody bodyCursor
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              (allocatorDepth := allocatorDepth)
              hBodyInvariant hInvariant.owned)
            hReturns
        cases hBodyResult with
        | @regular _ _ finalMode _ hBodyForward _hControl =>
            exact ⟨targetBodyFinal, finalMode, hBodyForward.toInvariant⟩
        | nonregular hMode _hBodyForward =>
            exact False.elim (hMode rfl))
      hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetFinal, hCompiled,
      .regular (hForward.toStackResource hInvariant.owned)
        (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact⟩

/--
Preserve the true branch of one synchronized `if` whose lexical body exits
nonregularly.
-/
theorem CoreCursor.ifTrueNonregularRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterCond :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {P :
      Structured.ObserverSemantics.Outcome (transcript := transcript) → Prop}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript cond source sourceAfterCond [value])
    (hTrue :
      (value != EvmYul.UInt256.ofNat 0) = true)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ bodyCursor :
          CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx,
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth root.lowerCtx
              lowerState localsCtx bodyCursor.plan live frameBase mode
              sourceAfterCond targetBodyStart →
          targetBodyStart.source.returns = target.source.returns →
          ∃ targetBodyOutcome bodyCtx,
            AllocationObserverOutcome.BlockRuntimeResult
              program.memoryContract config allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live body)
              frameBase mode program sourceCtx body sourceAfterCond
              expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart sourceOutcome targetBodyOutcome bodyCtx ∧
            P targetBodyOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.if_ cond body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.if_ cond body) ∧
          ExactTail cursor tail ∧
          P targetOutcome := by
  obtain
      ⟨afterState, headLower, headCode, tail, _loweredCond,
        _condCode, _targetBody, bodyCursor, hCompiled, hLower,
        hCompile, _hHeadCode, _hLowerCond, _hCompileCond, _hFinish,
        _hAfterEnv, _hAfterLayout, hCondScoped, hExact⟩ :=
    cursor.ifCursors
  have hPlanAgree :
      AllocationObserverRelation.PlanAgreesOn
        bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  obtain ⟨targetOutcome, _finalMode, hForward, hP⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.if_true_of_components
      hConfig hSafe hTrue hMode hCondScoped bodyCursor.sourceScoped
      hInvariant
      (by
        intro loweredBody bodyLowerState bodyCode bodyLocals
          targetAfterCond hLowerBody hCompileBody hCondInvariant hReturns
        have hLowerEq :
            (loweredBody, bodyLowerState) =
              (bodyCursor.lowered, bodyCursor.finalState) :=
          Option.some.inj (hLowerBody.symm.trans bodyCursor.lower)
        cases hLowerEq
        have hCompileEq :
            (bodyCode, bodyLocals) =
              (bodyCursor.compiled, bodyCursor.finalLocals) :=
          Option.some.inj (hCompileBody.symm.trans bodyCursor.compile)
        cases hCompileEq
        have hBodyInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx lowerState localsCtx bodyCursor.plan
              live frameBase mode sourceAfterCond targetAfterCond :=
          hCondInvariant.transport_plan
            bodyCursor.planWF hPlanAgree.symm
        obtain
            ⟨recursiveTargetOutcome, recursiveBodyCtx,
              hBodyResult, hBodyP⟩ :=
          hBody bodyCursor hBodyInvariant hReturns
        cases hBodyResult with
        | regular _hBodyForward _hControl =>
            exact False.elim (hMode rfl)
        | nonregular _bodyMode hBodyForward =>
            have hBodyForward' := hBodyForward
            rcases hBodyForward with
              ⟨_sourceFuel, _targetFuel, _hSourceRun, _hTargetRun,
                hBodyOutcomeRel, _hSame, _hEffect⟩
            have hOuterOutcomeRel :=
              AllocationObserverOutcome.transport_nonregular_outcome_plan
                hBodyOutcomeRel hMode hPlanAgree hControl
            exact
              ⟨bodyCursor.plan, _, recursiveTargetOutcome,
                recursiveBodyCtx, hBodyForward', hOuterOutcomeRel,
                hBodyP⟩)
      hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetOutcome, hCompiled,
      .nonregular hForward,
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact, hP⟩

/--
Preserve the true branch of one synchronized `if` whose lexical body exits
nonregularly in a compiler-selected stack-only activation.
-/
theorem CoreCursor.ifTrueNonregularStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterCond :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {P :
      Structured.ObserverSemantics.Outcome (transcript := transcript) → Prop}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript cond source sourceAfterCond [value])
    (hTrue :
      (value != EvmYul.UInt256.ofNat 0) = true)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ bodyCursor :
          CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx,
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationResourceInvariant
              .stackOnly program.memoryContract allocatorDepth root.lowerCtx
              lowerState localsCtx bodyCursor.plan live frameBase mode
              sourceAfterCond targetBodyStart →
          targetBodyStart.source.returns = target.source.returns →
          ∃ targetBodyOutcome bodyCtx,
            AllocationObserverOutcome.BlockResourceResult
              program.memoryContract .stackOnly allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live body)
              frameBase mode program sourceCtx body sourceAfterCond
              expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart sourceOutcome targetBodyOutcome bodyCtx ∧
            P targetBodyOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.if_ cond body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.if_ cond body) ∧
          ExactTail cursor tail ∧
          P targetOutcome := by
  obtain
      ⟨afterState, headLower, headCode, tail, _loweredCond,
        _condCode, _targetBody, bodyCursor, hCompiled, hLower,
        hCompile, _hHeadCode, _hLowerCond, _hCompileCond, _hFinish,
        _hAfterEnv, _hAfterLayout, hCondScoped, hExact⟩ :=
    cursor.ifCursors
  have hPlanAgree :
      AllocationObserverRelation.PlanAgreesOn
        bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  obtain ⟨targetOutcome, finalMode, hForward, hFinalStack, hP⟩ :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.if_true_of_components
      (P := fun finalMode targetOutcome =>
        finalMode = .stack ∧ P targetOutcome)
      hSafe hTrue hMode hCondScoped hInvariant.activation
      (by
        intro loweredBody bodyLowerState bodyCode bodyLocals
          targetAfterCond hLowerBody hCompileBody hCondInvariant hReturns
        have hLowerEq :
            (loweredBody, bodyLowerState) =
              (bodyCursor.lowered, bodyCursor.finalState) :=
          Option.some.inj (hLowerBody.symm.trans bodyCursor.lower)
        cases hLowerEq
        have hCompileEq :
            (bodyCode, bodyLocals) =
              (bodyCursor.compiled, bodyCursor.finalLocals) :=
          Option.some.inj (hCompileBody.symm.trans bodyCursor.compile)
        cases hCompileEq
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx lowerState localsCtx
              bodyCursor.plan live frameBase mode sourceAfterCond
              targetAfterCond :=
          hCondInvariant.transport_plan
            bodyCursor.planWF hPlanAgree.symm
        obtain
            ⟨recursiveTargetOutcome, recursiveBodyCtx,
              hBodyResult, hBodyP⟩ :=
          hBody bodyCursor
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              (allocatorDepth := allocatorDepth)
              hBodyInvariant hInvariant.owned)
            hReturns
        cases hBodyResult with
        | regular _hBodyForward _hControl =>
            exact False.elim (hMode rfl)
        | @nonregular _ _ bodyFinalMode _ _ hBodyForward =>
            rcases hBodyForward with
              ⟨sourceFuel, targetFuel, hSourceRun, hTargetRun,
                hBodyOutcomeRel, hSame, _hEffect⟩
            have hOuterOutcomeRel :=
              AllocationObserverOutcome.transport_nonregular_outcome_plan
                hBodyOutcomeRel hMode hPlanAgree hControl
            exact
              ⟨bodyCursor.plan, bodyFinalMode, recursiveTargetOutcome,
                recursiveBodyCtx,
                ⟨sourceFuel, targetFuel, hSourceRun, hTargetRun,
                  hBodyOutcomeRel⟩,
                hOuterOutcomeRel,
                hSame.right_eq_stack_of_left_eq_stack hInvariant.owned,
                hBodyP⟩)
      hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetOutcome, hCompiled,
      .nonregular
        (hForward.toStackResource
          (allocatorDepth := allocatorDepth)
          hInvariant.owned hFinalStack),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact, hP⟩

/--
Dispatcher-facing preservation for one synchronized `if`.
-/
theorem CoreCursor.ifRuntimeResultOfSafeRun
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1) (.if_ cond body) source =
        .ok (sourceOutcome, sourceCtx))
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ {sourceAfterCond :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        (bodyCursor :
          CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx),
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program sourceCtx sourceFuel body sourceAfterCond =
          .ok (bodyOutcome, bodyCtx) →
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth root.lowerCtx
              lowerState localsCtx bodyCursor.plan live frameBase mode
              sourceAfterCond targetBodyStart →
          ∃ targetBodyOutcome,
            AllocationObserverOutcome.BlockRuntimeResult
              program.memoryContract config allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live body)
              frameBase mode program sourceCtx body sourceAfterCond
              expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart bodyOutcome targetBodyOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.if_ cond body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.if_ cond body) ∧
          ExactTail cursor tail := by
  rcases
      Functions.Source.Effectful.Stmt.run_if_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hFalse | hTrue
  · rcases hFalse with
      ⟨sourceAfterCond, hCond, hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain ⟨value, hSafe, hValue⟩ :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
        hCond
    have hZero : value = EvmYul.UInt256.ofNat 0 := by
      by_contra hNe
      have hNonzero :
          (value != EvmYul.UInt256.ofNat 0) = true :=
        TypedCfg.Preservation.uint256_bne_zero_of_ne value hNe
      rw [hNonzero] at hValue
      contradiction
    obtain
        ⟨afterState, headCode, tail, targetFinal, hCompiled,
          hResult, hTransport, hExact⟩ :=
      cursor.ifFalseRuntimeResult
        (sourceCtx := sourceCtx) hConfig hSafe hZero hInvariant
    exact
      ⟨afterState, headCode, tail,
        Structured.EffectSemantics.Outcome.regular targetFinal,
        hCompiled, hResult, hTransport, hExact⟩
  · rcases hTrue with
      ⟨sourceAfterCond, bodyOutcome, hCond, hScoped,
        hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain ⟨value, hSafe, hValue⟩ :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
        hCond
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program hScoped with
      hRegular | hNonregular
    · rcases hRegular with
        ⟨sourceBodyFinal, bodyCtx, hBodyRun, hBodyOutcome⟩
      subst bodyOutcome
      have hRestrict :
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
              sourceCtx.scope sourceBodyFinal =
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceBodyFinal :=
        Locals.Source.Effectful.StateModel.restrictTo_congr
          (Functions.ObserverSemantics.stateModel transcript)
          hSourceScope
      rw [hRestrict]
      obtain
          ⟨afterState, headCode, tail, targetFinal, hCompiled,
            hResult, hTransport, hExact⟩ :=
        cursor.ifTrueRegularRuntimeResult
          (sourceBodyFinal := sourceBodyFinal)
          (finalCtx := bodyCtx)
          hConfig hSafe hValue hSourceScope hInvariant
          (by
            intro bodyCursor targetBodyStart hBodyInvariant _hReturns
            obtain ⟨targetBodyOutcome, hBodyResult⟩ :=
              hBody bodyCursor hBodyRun hBodyInvariant
            cases hBodyResult with
            | regular hBodyForward hBodyControl =>
                exact ⟨_, .regular hBodyForward hBodyControl⟩
            | nonregular hMode _hBodyForward =>
                exact False.elim (hMode rfl))
      exact
        ⟨afterState, headCode, tail,
          Structured.EffectSemantics.Outcome.regular targetFinal,
          hCompiled, hResult, hTransport, hExact⟩
    · rcases hNonregular with
        ⟨openOutcome, bodyCtx, hBodyRun, hMode, hBodyOutcome⟩
      subst bodyOutcome
      obtain
          ⟨afterState, headCode, tail, targetOutcome, hCompiled,
            hRuntime, hTransport, hExact, _hDecoration⟩ :=
        cursor.ifTrueNonregularRuntimeResult (P := fun _ => True)
          hConfig hSafe hValue hMode hControl hInvariant
          (by
            intro bodyCursor targetBodyStart hBodyInvariant _hReturns
            obtain ⟨targetBodyOutcome, hBodyResult⟩ :=
              hBody bodyCursor hBodyRun hBodyInvariant
            exact ⟨targetBodyOutcome, bodyCtx, hBodyResult, trivial⟩)
      exact
        ⟨afterState, headCode, tail, targetOutcome, hCompiled,
          hRuntime, hTransport, hExact⟩

/--
Dispatcher-facing stack-only preservation for one synchronized `if`.
-/
theorem CoreCursor.ifStackResourceResultOfSafeRun
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      CoreCursor root scope live
        { stmts := .if_ cond body :: rest } lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1) (.if_ cond body) source =
        .ok (sourceOutcome, sourceCtx))
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ {sourceAfterCond :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        (bodyCursor :
          CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx),
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program sourceCtx sourceFuel body sourceAfterCond =
          .ok (bodyOutcome, bodyCtx) →
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationResourceInvariant
              .stackOnly program.memoryContract allocatorDepth root.lowerCtx
              lowerState localsCtx bodyCursor.plan live frameBase mode
              sourceAfterCond targetBodyStart →
          ∃ targetBodyOutcome,
            AllocationObserverOutcome.BlockResourceResult
              program.memoryContract .stackOnly allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live body)
              frameBase mode program sourceCtx body sourceAfterCond
              expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart bodyOutcome targetBodyOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.if_ cond body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.if_ cond body) ∧
          ExactTail cursor tail := by
  rcases
      Functions.Source.Effectful.Stmt.run_if_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hFalse | hTrue
  · rcases hFalse with
      ⟨sourceAfterCond, hCond, hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain ⟨value, hSafe, hValue⟩ :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
        hCond
    have hZero : value = EvmYul.UInt256.ofNat 0 := by
      by_contra hNe
      have hNonzero :
          (value != EvmYul.UInt256.ofNat 0) = true :=
        TypedCfg.Preservation.uint256_bne_zero_of_ne value hNe
      rw [hNonzero] at hValue
      contradiction
    obtain
        ⟨afterState, headCode, tail, targetFinal, hCompiled,
          hResult, hTransport, hExact⟩ :=
      cursor.ifFalseStackResourceResult
        (sourceCtx := sourceCtx) hSafe hZero hInvariant
    exact
      ⟨afterState, headCode, tail,
        Structured.EffectSemantics.Outcome.regular targetFinal,
        hCompiled, hResult, hTransport, hExact⟩
  · rcases hTrue with
      ⟨sourceAfterCond, bodyOutcome, hCond, hScoped,
        hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain ⟨value, hSafe, hValue⟩ :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalCondition
        hCond
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program hScoped with
      hRegular | hNonregular
    · rcases hRegular with
        ⟨sourceBodyFinal, bodyCtx, hBodyRun, hBodyOutcome⟩
      subst bodyOutcome
      have hRestrict :
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
              sourceCtx.scope sourceBodyFinal =
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceBodyFinal :=
        Locals.Source.Effectful.StateModel.restrictTo_congr
          (Functions.ObserverSemantics.stateModel transcript)
          hSourceScope
      rw [hRestrict]
      obtain
          ⟨afterState, headCode, tail, targetFinal, hCompiled,
            hResult, hTransport, hExact⟩ :=
        cursor.ifTrueRegularStackResourceResult
          (sourceBodyFinal := sourceBodyFinal)
          (finalCtx := bodyCtx)
          hSafe hValue hSourceScope hInvariant
          (by
            intro bodyCursor targetBodyStart hBodyInvariant _hReturns
            obtain ⟨targetBodyOutcome, hBodyResult⟩ :=
              hBody bodyCursor hBodyRun hBodyInvariant
            cases hBodyResult with
            | regular hBodyForward hBodyControl =>
                exact ⟨_, .regular hBodyForward hBodyControl⟩
            | nonregular hMode _hBodyForward =>
                exact False.elim (hMode rfl))
      exact
        ⟨afterState, headCode, tail,
          Structured.EffectSemantics.Outcome.regular targetFinal,
          hCompiled, hResult, hTransport, hExact⟩
    · rcases hNonregular with
        ⟨openOutcome, bodyCtx, hBodyRun, hMode, hBodyOutcome⟩
      subst bodyOutcome
      obtain
          ⟨afterState, headCode, tail, targetOutcome, hCompiled,
            hRuntime, hTransport, hExact, _hDecoration⟩ :=
        cursor.ifTrueNonregularStackResourceResult (P := fun _ => True)
          hSafe hValue hMode hControl hInvariant
          (by
            intro bodyCursor targetBodyStart hBodyInvariant _hReturns
            obtain ⟨targetBodyOutcome, hBodyResult⟩ :=
              hBody bodyCursor hBodyRun hBodyInvariant
            exact ⟨targetBodyOutcome, bodyCtx, hBodyResult, trivial⟩)
      exact
        ⟨afterState, headCode, tail, targetOutcome, hCompiled,
          hRuntime, hTransport, hExact⟩

/--
Preserve a synchronized `switch` whose canonical source selection finds no
case or default body.
-/
theorem CoreCursor.switchNoneRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterScrutinee :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript scrutinee source
        sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = none)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.switch scrutinee cases defaultBody) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              sourceAfterScrutinee)
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.switch scrutinee cases defaultBody) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, headLower, headCode, tail, hCompiled, hLower,
        hCompile, _hAfterEnv, _hAfterLayout, hScrutineeScoped,
        _hCasesScoped, _hDefaultScoped, hExact⟩ :=
    cursor.switchCursors
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.switch_none_of_components
      hConfig hSafe hSelect hScrutineeScoped hInvariant hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetFinal, hCompiled,
      .regular hForward (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact⟩

/--
Preserve a synchronized stack-only `switch` whose source selection finds no
case or default body.
-/
theorem CoreCursor.switchNoneStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterScrutinee :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript scrutinee source
        sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody = none)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.switch scrutinee cases defaultBody) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              sourceAfterScrutinee)
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.switch scrutinee cases defaultBody) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, headLower, headCode, tail, hCompiled, hLower,
        hCompile, _hAfterEnv, _hAfterLayout, hScrutineeScoped,
        _hCasesScoped, _hDefaultScoped, hExact⟩ :=
    cursor.switchCursors
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtInvariantForward.switch_none_of_components
      hSafe hSelect hScrutineeScoped hInvariant.activation hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetFinal, hCompiled,
      .regular (hForward.toStackResource hInvariant.owned)
        (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact⟩

/--
Preserve a synchronized `switch` whose selected lexical body returns
regularly.

The recursive hypothesis is stated only for the selected pass-owned cursor.
Plan agreement transports the post-scrutinee runtime invariant from the outer
switch plan to that lexical plan before recursion.
-/
theorem CoreCursor.switchSomeRegularRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceAfterScrutinee sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript scrutinee source
        sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody =
        some selected)
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ {selectedStart}
        {selectedPlanning : AllocationSupport.PlanningState}
        (bodyCursor :
          CoreCursor root
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx)
        {targetBodyStart :
          Structured.ObserverSemantics.State transcript},
        AllocationLowering.StateExtends live lowerState selectedStart →
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config allocatorDepth root.lowerCtx
            selectedStart localsCtx bodyCursor.plan live frameBase mode
            sourceAfterScrutinee targetBodyStart →
        targetBodyStart.source.returns = target.source.returns →
        ∃ targetBodyFinal,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx bodyCursor.finalState
            bodyCursor.finalLocals bodyCursor.plan root.returns
            (Functions.Scope.Block.outEnv live selected)
            frameBase mode program sourceCtx selected
            sourceAfterScrutinee expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured bodyCursor.compiled }
            targetBodyStart
            (Functions.Source.Effectful.Outcome.regular sourceBodyFinal)
            (Structured.EffectSemantics.Outcome.regular targetBodyFinal)
            finalCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.switch scrutinee cases defaultBody) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                live sourceBodyFinal))
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.switch scrutinee cases defaultBody) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, headLower, headCode, tail, hCompiled, hLower,
        hCompile, _hAfterEnv, _hAfterLayout, hScrutineeScoped,
        hCasesScoped, hDefaultScoped, hExact⟩ :=
    cursor.switchCursors
  have hSelectedScoped :
      Functions.Scope.Block.Scoped live selected :=
    Functions.Source.Switch.scoped_of_select_some
      hCasesScoped hDefaultScoped hSelect
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.switch_some_of_components
      (current := scope)
      (planning := cursor.planning)
      cursor.planningAllocation hConfig hSafe hSelect
      hScrutineeScoped hSelectedScoped
      hSourceScope
      hInvariant
      (by
        intro selectedLowered selectedBodyStart bodyLowerState
          selectedPlanning bodyCode bodyLocals targetBodyStart
          hSelectedPlanning hSelectedEnv hSelectedExtends
          hSelectedEntry hSelectedInner
          hLowerBody hCompileBody hSelectedInvariant hReturns
        obtain
            ⟨bodyCursor, _hBodyLowered, hBodyFinal, hBodyCode,
              hBodyLocals⟩ :=
          cursor.switchSelectedCursorOfComponents
            hSelectedPlanning hSelectedEnv hSelectedEntry hSelectedInner
            hLowerBody hCompileBody hSelectedScoped
        have hPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              bodyCursor.plan cursor.plan live :=
          bodyCursor.planAgreesOn cursor hSelectedEnv
        have hBodyInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx selectedBodyStart localsCtx bodyCursor.plan
              live frameBase mode sourceAfterScrutinee
              targetBodyStart :=
          hSelectedInvariant.transport_plan
            bodyCursor.planWF hPlanAgree.symm
        obtain ⟨targetBodyFinal, hBodyResult⟩ :=
          hBody bodyCursor hSelectedExtends hBodyInvariant hReturns
        cases hBodyResult with
        | @regular _ _ finalMode _ hBodyForward _hControl =>
            refine
              ⟨bodyCursor.plan, finalMode, targetBodyFinal, ?_⟩
            simpa [hBodyFinal, hBodyCode, hBodyLocals] using
              hBodyForward
        | nonregular hMode _hBodyForward =>
            exact False.elim (hMode rfl))
      hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetFinal, hCompiled,
      .regular hForward (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact⟩

/--
Preserve a synchronized stack-only `switch` whose selected lexical body
returns regularly.
-/
theorem CoreCursor.switchSomeRegularStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source sourceAfterScrutinee sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript scrutinee source
        sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody =
        some selected)
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ {selectedStart}
        {selectedPlanning : AllocationSupport.PlanningState}
        (bodyCursor :
          CoreCursor root
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx)
        {targetBodyStart :
          Structured.ObserverSemantics.State transcript},
        AllocationLowering.StateExtends live lowerState selectedStart →
        AllocationObserverContext.ActivationResourceInvariant
            .stackOnly program.memoryContract allocatorDepth root.lowerCtx
            selectedStart localsCtx bodyCursor.plan live frameBase mode
            sourceAfterScrutinee targetBodyStart →
        targetBodyStart.source.returns = target.source.returns →
        ∃ targetBodyFinal,
          AllocationObserverOutcome.BlockResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx bodyCursor.finalState
            bodyCursor.finalLocals bodyCursor.plan root.returns
            (Functions.Scope.Block.outEnv live selected)
            frameBase mode program sourceCtx selected
            sourceAfterScrutinee expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured bodyCursor.compiled }
            targetBodyStart
            (Functions.Source.Effectful.Outcome.regular sourceBodyFinal)
            (Structured.EffectSemantics.Outcome.regular targetBodyFinal)
            finalCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetFinal,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.switch scrutinee cases defaultBody) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            (Functions.Source.Effectful.Outcome.regular
              ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                live sourceBodyFinal))
            (Structured.EffectSemantics.Outcome.regular targetFinal)
            sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.switch scrutinee cases defaultBody) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, headLower, headCode, tail, hCompiled, hLower,
        hCompile, _hAfterEnv, _hAfterLayout, hScrutineeScoped,
        hCasesScoped, hDefaultScoped, hExact⟩ :=
    cursor.switchCursors
  have hSelectedScoped :
      Functions.Scope.Block.Scoped live selected :=
    Functions.Source.Switch.scoped_of_select_some
      hCasesScoped hDefaultScoped hSelect
  obtain ⟨targetFinal, hForward⟩ :=
    AllocationObserverStatement.Sequence.RegularStmtInvariantForward.switch_some_of_components
      (current := scope)
      (planning := cursor.planning)
      cursor.planningAllocation hSafe hSelect
      hScrutineeScoped hSelectedScoped hSourceScope
      hInvariant.activation
      (by
        intro selectedLowered selectedBodyStart bodyLowerState
          selectedPlanning bodyCode bodyLocals targetBodyStart
          hSelectedPlanning hSelectedEnv hSelectedExtends
          hSelectedEntry hSelectedInner
          hLowerBody hCompileBody hSelectedInvariant hReturns
        obtain
            ⟨bodyCursor, _hBodyLowered, hBodyFinal, hBodyCode,
              hBodyLocals⟩ :=
          cursor.switchSelectedCursorOfComponents
            hSelectedPlanning hSelectedEnv hSelectedEntry hSelectedInner
            hLowerBody hCompileBody hSelectedScoped
        have hPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              bodyCursor.plan cursor.plan live :=
          bodyCursor.planAgreesOn cursor hSelectedEnv
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx selectedBodyStart
              localsCtx bodyCursor.plan live frameBase mode
              sourceAfterScrutinee targetBodyStart :=
          hSelectedInvariant.transport_plan
            bodyCursor.planWF hPlanAgree.symm
        obtain ⟨targetBodyFinal, hBodyResult⟩ :=
          hBody bodyCursor hSelectedExtends
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              (allocatorDepth := allocatorDepth)
              hBodyInvariant hInvariant.owned)
            hReturns
        cases hBodyResult with
        | @regular _ _ finalMode _ hBodyForward _hControl =>
            refine
              ⟨bodyCursor.plan, finalMode, targetBodyFinal, ?_⟩
            simpa [hBodyFinal, hBodyCode, hBodyLocals] using
              hBodyForward.toInvariant
        | nonregular hMode _hBodyForward =>
            exact False.elim (hMode rfl))
      hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetFinal, hCompiled,
      .regular (hForward.toStackResource hInvariant.owned)
        (AllocationObserverOutcome.SameControl.refl _),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact⟩

/--
Preserve a synchronized `switch` whose selected lexical body exits
nonregularly.
-/
theorem CoreCursor.switchSomeNonregularRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterScrutinee :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {P :
      Structured.ObserverSemantics.Outcome (transcript := transcript) → Prop}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript scrutinee source
        sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody =
        some selected)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ {selectedStart}
        {selectedPlanning : AllocationSupport.PlanningState}
        (bodyCursor :
          CoreCursor root
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx)
        {targetBodyStart :
          Structured.ObserverSemantics.State transcript},
        AllocationLowering.StateExtends live lowerState selectedStart →
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config allocatorDepth root.lowerCtx
            selectedStart localsCtx bodyCursor.plan live frameBase mode
            sourceAfterScrutinee targetBodyStart →
        targetBodyStart.source.returns = target.source.returns →
        ∃ targetOutcome finalCtx,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx bodyCursor.finalState
            bodyCursor.finalLocals bodyCursor.plan root.returns
            (Functions.Scope.Block.outEnv live selected)
            frameBase mode program sourceCtx selected
            sourceAfterScrutinee expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured bodyCursor.compiled }
            targetBodyStart sourceOutcome targetOutcome finalCtx ∧
          P targetOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.switch scrutinee cases defaultBody) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.switch scrutinee cases defaultBody) ∧
          ExactTail cursor tail ∧
          P targetOutcome := by
  obtain
      ⟨afterState, headLower, headCode, tail, hCompiled, hLower,
        hCompile, _hAfterEnv, _hAfterLayout, hScrutineeScoped,
        hCasesScoped, hDefaultScoped, hExact⟩ :=
    cursor.switchCursors
  have hSelectedScoped :
      Functions.Scope.Block.Scoped live selected :=
    Functions.Source.Switch.scoped_of_select_some
      hCasesScoped hDefaultScoped hSelect
  obtain ⟨targetOutcome, _finalMode, hForward, hP⟩ :=
    AllocationObserverOutcome.NonregularStmtRuntimeForward.switch_some_of_components
      (current := scope)
      (planning := cursor.planning)
      cursor.planningAllocation hConfig hSafe hSelect hMode
      hScrutineeScoped hSelectedScoped hInvariant
      (by
        intro selectedLowered selectedBodyStart bodyLowerState
          selectedPlanning bodyCode bodyLocals targetBodyStart
          hSelectedPlanning hSelectedEnv hSelectedExtends
          hSelectedEntry hSelectedInner
          hLowerBody hCompileBody hSelectedInvariant hReturns
        obtain
            ⟨bodyCursor, hBodyLowered, hBodyFinal, hBodyCode,
              hBodyLocals⟩ :=
          cursor.switchSelectedCursorOfComponents
            hSelectedPlanning hSelectedEnv hSelectedEntry hSelectedInner
            hLowerBody hCompileBody hSelectedScoped
        have hPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              bodyCursor.plan cursor.plan live :=
          bodyCursor.planAgreesOn cursor hSelectedEnv
        have hBodyInvariant :
            AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth
              root.lowerCtx selectedBodyStart localsCtx bodyCursor.plan
              live frameBase mode sourceAfterScrutinee
              targetBodyStart :=
          hSelectedInvariant.transport_plan
            bodyCursor.planWF hPlanAgree.symm
        obtain
          ⟨recursiveTargetOutcome, recursiveFinalCtx,
              hBodyResult, hBodyP⟩ :=
          hBody bodyCursor hSelectedExtends hBodyInvariant hReturns
        cases hBodyResult with
        | regular _hBodyForward _hControl =>
            exact False.elim (hMode rfl)
        | nonregular _bodyMode hBodyForward =>
            have hBodyForward' := hBodyForward
            rcases hBodyForward with
              ⟨sourceFuel, targetFuel, hSourceRun, hTargetRun,
                hBodyOutcomeRel, hSame, hEffect⟩
            have hOuterOutcomeRel :=
              AllocationObserverOutcome.transport_nonregular_outcome_plan
                hBodyOutcomeRel hMode hPlanAgree hControl
            refine
              ⟨bodyCursor.plan, _, recursiveTargetOutcome,
                recursiveFinalCtx, ?_, hOuterOutcomeRel, hBodyP⟩
            simpa [hBodyLowered, hBodyFinal, hBodyCode, hBodyLocals] using
              hBodyForward')
      hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetOutcome, hCompiled,
      .nonregular hForward,
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact, hP⟩

/--
Preserve a synchronized stack-only `switch` whose selected lexical body exits
nonregularly.
-/
theorem CoreCursor.switchSomeNonregularStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
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
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source sourceAfterScrutinee :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {P :
      Structured.ObserverSemantics.Outcome (transcript := transcript) → Prop}
    {value : Word}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        program.memoryContract transcript scrutinee source
        sourceAfterScrutinee [value])
    (hSelect :
      Functions.Source.Switch.select value cases defaultBody =
        some selected)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ {selectedStart}
        {selectedPlanning : AllocationSupport.PlanningState}
        (bodyCursor :
          CoreCursor root
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx)
        {targetBodyStart :
          Structured.ObserverSemantics.State transcript},
        AllocationLowering.StateExtends live lowerState selectedStart →
        AllocationObserverContext.ActivationResourceInvariant
            .stackOnly program.memoryContract allocatorDepth root.lowerCtx
            selectedStart localsCtx bodyCursor.plan live frameBase mode
            sourceAfterScrutinee targetBodyStart →
        targetBodyStart.source.returns = target.source.returns →
        ∃ targetOutcome finalCtx,
          AllocationObserverOutcome.BlockResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx bodyCursor.finalState
            bodyCursor.finalLocals bodyCursor.plan root.returns
            (Functions.Scope.Block.outEnv live selected)
            frameBase mode program sourceCtx selected
            sourceAfterScrutinee expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured bodyCursor.compiled }
            targetBodyStart sourceOutcome targetOutcome finalCtx ∧
          P targetOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.switch scrutinee cases defaultBody) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.switch scrutinee cases defaultBody) ∧
          ExactTail cursor tail ∧
          P targetOutcome := by
  obtain
      ⟨afterState, headLower, headCode, tail, hCompiled, hLower,
        hCompile, _hAfterEnv, _hAfterLayout, hScrutineeScoped,
        hCasesScoped, hDefaultScoped, hExact⟩ :=
    cursor.switchCursors
  have hSelectedScoped :
      Functions.Scope.Block.Scoped live selected :=
    Functions.Source.Switch.scoped_of_select_some
      hCasesScoped hDefaultScoped hSelect
  obtain
      ⟨targetOutcome, finalMode, hForward, hFinalStack, hP⟩ :=
    AllocationObserverStatement.Sequence.NonregularStmtForward.switch_some_of_components
      (current := scope)
      (planning := cursor.planning)
      (P := fun finalMode targetOutcome =>
        finalMode = .stack ∧ P targetOutcome)
      cursor.planningAllocation hSafe hSelect hMode
      hScrutineeScoped hInvariant.activation
      (by
        intro selectedLowered selectedBodyStart bodyLowerState
          selectedPlanning bodyCode bodyLocals targetBodyStart
          hSelectedPlanning hSelectedEnv hSelectedExtends
          hSelectedEntry hSelectedInner
          hLowerBody hCompileBody hSelectedInvariant hReturns
        obtain
            ⟨bodyCursor, hBodyLowered, hBodyFinal, hBodyCode,
              hBodyLocals⟩ :=
          cursor.switchSelectedCursorOfComponents
            hSelectedPlanning hSelectedEnv hSelectedEntry hSelectedInner
            hLowerBody hCompileBody hSelectedScoped
        have hPlanAgree :
            AllocationObserverRelation.PlanAgreesOn
              bodyCursor.plan cursor.plan live :=
          bodyCursor.planAgreesOn cursor hSelectedEnv
        have hBodyInvariant :
            AllocationObserverContext.ActivationInvariant
              program.memoryContract root.lowerCtx selectedBodyStart
              localsCtx bodyCursor.plan live frameBase mode
              sourceAfterScrutinee targetBodyStart :=
          hSelectedInvariant.transport_plan
            bodyCursor.planWF hPlanAgree.symm
        obtain
            ⟨recursiveTargetOutcome, recursiveFinalCtx,
              hBodyResult, hBodyP⟩ :=
          hBody bodyCursor hSelectedExtends
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              (allocatorDepth := allocatorDepth)
              hBodyInvariant hInvariant.owned)
            hReturns
        cases hBodyResult with
        | regular _hBodyForward _hControl =>
            exact False.elim (hMode rfl)
        | @nonregular _ _ bodyFinalMode _ _ hBodyForward =>
            rcases hBodyForward with
              ⟨sourceFuel, targetFuel, hSourceRun, hTargetRun,
                hBodyOutcomeRel, hSame, _hEffect⟩
            have hOuterOutcomeRel :=
              AllocationObserverOutcome.transport_nonregular_outcome_plan
                hBodyOutcomeRel hMode hPlanAgree hControl
            refine
              ⟨bodyCursor.plan, bodyFinalMode, recursiveTargetOutcome,
                recursiveFinalCtx, ?_, hOuterOutcomeRel,
                hSame.right_eq_stack_of_left_eq_stack hInvariant.owned,
                hBodyP⟩
            simpa [hBodyLowered, hBodyFinal, hBodyCode, hBodyLocals] using
              (show
                AllocationObserverStatement.Sequence.BlockForward
                  program.memoryContract transcript bodyCursor.plan
                  (AllocationObserverOutcome.outcomeLive root.returns
                    (Functions.Scope.Block.outEnv live selected)
                    sourceCtx sourceOutcome.mode)
                  frameBase bodyFinalMode program sourceCtx selected
                  sourceAfterScrutinee expressions.toStructured
                  { stmts :=
                      Expressions.StmtList.toStructured
                        bodyCursor.compiled }
                  targetBodyStart sourceOutcome recursiveTargetOutcome
                  recursiveFinalCtx
                from
                  ⟨sourceFuel, targetFuel, hSourceRun, hTargetRun,
                    hBodyOutcomeRel⟩))
      hLower hCompile
  exact
    ⟨afterState, headCode, tail, targetOutcome, hCompiled,
      .nonregular
        (hForward.toStackResource
          (allocatorDepth := allocatorDepth)
          hInvariant.owned hFinalStack),
      StepTransport.of_compilers cursor.headScoped hLower hCompile,
      hExact, hP⟩

/--
Dispatcher-facing preservation for one synchronized `switch`.

The canonical guarded source run determines whether no body is selected or the
selected scoped body returns regularly or abruptly. Recursive proof work is
delegated only for the selected body's exact open-block run; all compiler and
allocation evidence remains owned by the existing cursor adapters.
-/
theorem CoreCursor.switchRuntimeResultOfSafeRun
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1)
          (.switch scrutinee cases defaultBody) source =
        .ok (sourceOutcome, sourceCtx))
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ {selected : Functions.Block}
        {sourceAfterScrutinee :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        {selectedStart : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        (bodyCursor :
          CoreCursor root
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx),
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program sourceCtx sourceFuel selected sourceAfterScrutinee =
          .ok (bodyOutcome, bodyCtx) →
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationRuntimeInvariant
              program.memoryContract config allocatorDepth root.lowerCtx
              selectedStart localsCtx bodyCursor.plan live frameBase mode
              sourceAfterScrutinee targetBodyStart →
          ∃ targetBodyOutcome,
            AllocationObserverOutcome.BlockRuntimeResult
              program.memoryContract config allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live selected)
              frameBase mode program sourceCtx selected
              sourceAfterScrutinee expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart bodyOutcome targetBodyOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.switch scrutinee cases defaultBody) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.switch scrutinee cases defaultBody) ∧
          ExactTail cursor tail := by
  rcases
      Functions.Source.Effectful.Stmt.run_switch_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hNone | hSome
  · rcases hNone with
      ⟨sourceAfterScrutinee, value, hScrutinee, hSelect,
        hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain
        ⟨afterState, headCode, tail, targetFinal, hCompiled,
          hResult, hTransport, hExact⟩ :=
      cursor.switchNoneRuntimeResult
        (sourceCtx := sourceCtx) hConfig
        (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
          hScrutinee)
        hSelect hInvariant
    exact
      ⟨afterState, headCode, tail,
        Structured.EffectSemantics.Outcome.regular targetFinal,
        hCompiled, hResult, hTransport, hExact⟩
  · rcases hSome with
      ⟨sourceAfterScrutinee, value, selected, bodyOutcome,
        hScrutinee, hSelect, hScoped, hOutcome, _hCtx⟩
    subst sourceOutcome
    have hSafe :
        AllocationObserverSafety.Expr.MemorySafeEval
          program.memoryContract transcript scrutinee source
          sourceAfterScrutinee [value] :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
        hScrutinee
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program hScoped with
      hRegular | hNonregular
    · rcases hRegular with
        ⟨sourceBodyFinal, bodyCtx, hBodyRun, hBodyOutcome⟩
      subst bodyOutcome
      have hRestrict :
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
              sourceCtx.scope sourceBodyFinal =
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceBodyFinal :=
        Locals.Source.Effectful.StateModel.restrictTo_congr
          (Functions.ObserverSemantics.stateModel transcript)
          hSourceScope
      rw [hRestrict]
      obtain
          ⟨afterState, headCode, tail, targetFinal, hCompiled,
            hResult, hTransport, hExact⟩ :=
        cursor.switchSomeRegularRuntimeResult
          (sourceBodyFinal := sourceBodyFinal)
          (finalCtx := bodyCtx)
          hConfig hSafe hSelect hSourceScope hInvariant
          (by
            intro selectedStart selectedPlanning bodyCursor
              targetBodyStart _hSelectedExtends hBodyInvariant _hReturns
            obtain ⟨targetBodyOutcome, hBodyResult⟩ :=
              hBody bodyCursor hBodyRun hBodyInvariant
            cases hBodyResult with
            | regular hBodyForward hBodyControl =>
                exact ⟨_, .regular hBodyForward hBodyControl⟩
            | nonregular hMode _hBodyForward =>
                exact False.elim (hMode rfl))
      exact
        ⟨afterState, headCode, tail,
          Structured.EffectSemantics.Outcome.regular targetFinal,
          hCompiled, hResult, hTransport, hExact⟩
    · rcases hNonregular with
        ⟨openOutcome, bodyCtx, hBodyRun, hMode, hBodyOutcome⟩
      subst bodyOutcome
      obtain
          ⟨afterState, headCode, tail, targetOutcome, hCompiled,
            hRuntime, hTransport, hExact, _hDecoration⟩ :=
        cursor.switchSomeNonregularRuntimeResult (P := fun _ => True)
          hConfig hSafe hSelect hMode hControl hInvariant
          (by
            intro selectedStart selectedPlanning bodyCursor targetBodyStart
              _hSelectedExtends hBodyInvariant _hReturns
            obtain ⟨targetBodyOutcome, hBodyResult⟩ :=
              hBody bodyCursor hBodyRun hBodyInvariant
            exact ⟨targetBodyOutcome, bodyCtx, hBodyResult, trivial⟩)
      exact
        ⟨afterState, headCode, tail, targetOutcome, hCompiled,
          hRuntime, hTransport, hExact⟩

/--
Dispatcher-facing stack-only preservation for one synchronized `switch`.
-/
theorem CoreCursor.switchStackResourceResultOfSafeRun
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 1)
          (.switch scrutinee cases defaultBody) source =
        .ok (sourceOutcome, sourceCtx))
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ {selected : Functions.Block}
        {sourceAfterScrutinee :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx : Functions.Source.Ctx}
        {selectedStart : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        (bodyCursor :
          CoreCursor root
            (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart localsCtx),
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program sourceCtx sourceFuel selected sourceAfterScrutinee =
          .ok (bodyOutcome, bodyCtx) →
        ∀ {targetBodyStart :
            Structured.ObserverSemantics.State transcript},
          AllocationObserverContext.ActivationResourceInvariant
              .stackOnly program.memoryContract allocatorDepth root.lowerCtx
              selectedStart localsCtx bodyCursor.plan live frameBase mode
              sourceAfterScrutinee targetBodyStart →
          ∃ targetBodyOutcome,
            AllocationObserverOutcome.BlockResourceResult
              program.memoryContract .stackOnly allocatorDepth transcript
              root.lowerCtx bodyCursor.finalState
              bodyCursor.finalLocals bodyCursor.plan root.returns
              (Functions.Scope.Block.outEnv live selected)
              frameBase mode program sourceCtx selected
              sourceAfterScrutinee expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
              targetBodyStart bodyOutcome targetBodyOutcome bodyCtx) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.switch scrutinee cases defaultBody) source
            expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.switch scrutinee cases defaultBody) ∧
          ExactTail cursor tail := by
  rcases
      Functions.Source.Effectful.Stmt.run_switch_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hNone | hSome
  · rcases hNone with
      ⟨sourceAfterScrutinee, value, hScrutinee, hSelect,
        hOutcome, _hCtx⟩
    subst sourceOutcome
    obtain
        ⟨afterState, headCode, tail, targetFinal, hCompiled,
          hResult, hTransport, hExact⟩ :=
      cursor.switchNoneStackResourceResult
        (sourceCtx := sourceCtx)
        (AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
          hScrutinee)
        hSelect hInvariant
    exact
      ⟨afterState, headCode, tail,
        Structured.EffectSemantics.Outcome.regular targetFinal,
        hCompiled, hResult, hTransport, hExact⟩
  · rcases hSome with
      ⟨sourceAfterScrutinee, value, selected, bodyOutcome,
        hScrutinee, hSelect, hScoped, hOutcome, _hCtx⟩
    subst sourceOutcome
    have hSafe :
        AllocationObserverSafety.Expr.MemorySafeEval
          program.memoryContract transcript scrutinee source
          sourceAfterScrutinee [value] :=
      AllocationObserverSafety.Expr.MemorySafeEval.of_safe_evalOne
        hScrutinee
    rcases
        Functions.Source.Effectful.Block.runScoped_cases
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program hScoped with
      hRegular | hNonregular
    · rcases hRegular with
        ⟨sourceBodyFinal, bodyCtx, hBodyRun, hBodyOutcome⟩
      subst bodyOutcome
      have hRestrict :
          (Functions.ObserverSemantics.stateModel transcript).restrictTo
              sourceCtx.scope sourceBodyFinal =
            (Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceBodyFinal :=
        Locals.Source.Effectful.StateModel.restrictTo_congr
          (Functions.ObserverSemantics.stateModel transcript)
          hSourceScope
      rw [hRestrict]
      obtain
          ⟨afterState, headCode, tail, targetFinal, hCompiled,
            hResult, hTransport, hExact⟩ :=
        cursor.switchSomeRegularStackResourceResult
          (sourceBodyFinal := sourceBodyFinal)
          (finalCtx := bodyCtx)
          hSafe hSelect hSourceScope hInvariant
          (by
            intro selectedStart selectedPlanning bodyCursor
              targetBodyStart _hSelectedExtends hBodyInvariant _hReturns
            obtain ⟨targetBodyOutcome, hBodyResult⟩ :=
              hBody bodyCursor hBodyRun hBodyInvariant
            cases hBodyResult with
            | regular hBodyForward hBodyControl =>
                exact ⟨_, .regular hBodyForward hBodyControl⟩
            | nonregular hMode _hBodyForward =>
                exact False.elim (hMode rfl))
      exact
        ⟨afterState, headCode, tail,
          Structured.EffectSemantics.Outcome.regular targetFinal,
          hCompiled, hResult, hTransport, hExact⟩
    · rcases hNonregular with
        ⟨openOutcome, bodyCtx, hBodyRun, hMode, hBodyOutcome⟩
      subst bodyOutcome
      obtain
          ⟨afterState, headCode, tail, targetOutcome, hCompiled,
            hResource, hTransport, hExact, _hDecoration⟩ :=
        cursor.switchSomeNonregularStackResourceResult
          (P := fun _ => True)
          hSafe hSelect hMode hControl hInvariant
          (by
            intro selectedStart selectedPlanning bodyCursor targetBodyStart
              _hSelectedExtends hBodyInvariant _hReturns
            obtain ⟨targetBodyOutcome, hBodyResult⟩ :=
              hBody bodyCursor hBodyRun hBodyInvariant
            exact ⟨targetBodyOutcome, bodyCtx, hBodyResult, trivial⟩)
      exact
        ⟨afterState, headCode, tail, targetOutcome, hCompiled,
          hResource, hTransport, hExact⟩

/--
Preserve one lexical block statement from its synchronized outer cursor and
one recursive result for the generated scope-owned body cursor.

Regular bodies execute the compiler-emitted lexical cleanup and return to the
outer plan. Abrupt bodies skip that unreachable cleanup and use checked cursor
plan agreement on the source control destination.
-/
theorem CoreCursor.blockRuntimeResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx bodyCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {bodyOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {P :
      Structured.ObserverSemantics.Outcome (transcript := transcript) → Prop}
    (cursor :
      CoreCursor root scope live
        { stmts := .block body :: rest } lowerState localsCtx)
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ bodyCursor :
          CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx,
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx bodyCursor.finalState
            bodyCursor.finalLocals bodyCursor.plan root.returns
            (Functions.Scope.Block.outEnv live body)
            frameBase mode program sourceCtx body source
            expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
            target bodyOutcome targetOutcome bodyCtx ∧
          P targetOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ sourceOutcome targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtRuntimeResult
            program.memoryContract config allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.block body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.block body) ∧
          ExactTail cursor tail ∧
          (bodyOutcome.mode = .regular →
            sourceOutcome =
              Functions.Source.Effectful.Outcome.regular
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  live bodyOutcome.state)) ∧
          (bodyOutcome.mode ≠ .regular →
            sourceOutcome = bodyOutcome) ∧
          (sourceOutcome.mode ≠ .regular →
            P targetOutcome) := by
  obtain
      ⟨afterState, headCode, tail, targetBlock, bodyCursor,
        hCompiled, hHeadCode, hFinish, hAfterEnv, hAfterLayout,
        hTransport, hExact⟩ :=
    cursor.blockCursors
  subst headCode
  obtain ⟨targetOutcome, hBodyResult, hP⟩ :=
    hBody bodyCursor
  have hPlanAgree :
      AllocationObserverRelation.PlanAgreesOn
        bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  cases hBodyResult with
  | @regular sourceFinal targetBodyFinal finalMode finalCtx
      hBodyForward hBodyControl =>
      obtain ⟨targetFinal, hStmtForward⟩ :=
        AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward.block_of_components
          hBodyForward hSourceScope
          (fun name hName =>
            Functions.Scope.Block.mem_outEnv hName)
          bodyCursor.sourceScoped hInvariant bodyCursor.lower
          bodyCursor.compile hFinish
      have hStmtForward' :=
        hStmtForward.transport_lower_state hAfterEnv hAfterLayout
      exact
        ⟨afterState, targetBlock.stmts, tail,
          Functions.Source.Effectful.Outcome.regular
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceFinal),
          Structured.EffectSemantics.Outcome.regular targetFinal,
          hCompiled,
          .regular hStmtForward'
            (AllocationObserverOutcome.SameControl.refl sourceCtx),
          hTransport, hExact, (fun _ => rfl),
          (fun hMode => False.elim (hMode rfl)),
          (fun hMode => False.elim (hMode rfl))⟩
  | nonregular hMode hBodyForward =>
      have hStmtForward :=
        AllocationObserverOutcome.NonregularStmtRuntimeForward.block_of_runtime
          hBodyForward hMode hPlanAgree hControl hFinish
      exact
        ⟨afterState, targetBlock.stmts, tail,
          bodyOutcome, targetOutcome, hCompiled,
          .nonregular hStmtForward, hTransport, hExact,
          (fun hRegular => False.elim (hMode hRegular)),
          (fun _ => rfl), (fun _ => hP)⟩

/--
Preserve one lexical block statement in a compiler-selected stack-only
activation.
-/
theorem CoreCursor.blockStackResourceResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {body : Functions.Block}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx bodyCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {bodyOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {P :
      Structured.ObserverSemantics.Outcome (transcript := transcript) → Prop}
    (cursor :
      CoreCursor root scope live
        { stmts := .block body :: rest } lowerState localsCtx)
    (hSourceScope :
      ∀ name, name ∈ sourceCtx.scope ↔ name ∈ live)
    (hControl :
      AllocationObserverOutcome.ControlScopesWithin
        root.returns live sourceCtx)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth root.lowerCtx
        lowerState localsCtx cursor.plan live frameBase mode
        source target)
    (hBody :
      ∀ bodyCursor :
          CoreCursor root
            (.lexical scope cursor.planning.nextScope)
            live body lowerState localsCtx,
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx bodyCursor.finalState
            bodyCursor.finalLocals bodyCursor.plan root.returns
            (Functions.Scope.Block.outEnv live body)
            frameBase mode program sourceCtx body source
            expressions.toStructured
              { stmts :=
                  Expressions.StmtList.toStructured bodyCursor.compiled }
            target bodyOutcome targetOutcome bodyCtx ∧
          P targetOutcome) :
    ∃ afterState headCode,
      ∃ tail :
        CoreCursor root scope live
          { stmts := rest } afterState localsCtx,
      ∃ sourceOutcome targetOutcome,
        cursor.compiled = headCode ++ tail.compiled ∧
          AllocationObserverOutcome.StmtResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            root.lowerCtx afterState localsCtx cursor.plan
            root.returns live frameBase mode program sourceCtx
            (.block body) source expressions.toStructured target
            (Expressions.StmtList.toStructured headCode)
            sourceOutcome targetOutcome sourceCtx ∧
          StepTransport lowerState afterState localsCtx localsCtx
            live (.block body) ∧
          ExactTail cursor tail ∧
          (bodyOutcome.mode = .regular →
            sourceOutcome =
              Functions.Source.Effectful.Outcome.regular
                ((Functions.ObserverSemantics.stateModel transcript).restrictTo
                  live bodyOutcome.state)) ∧
          (bodyOutcome.mode ≠ .regular →
            sourceOutcome = bodyOutcome) ∧
          (sourceOutcome.mode ≠ .regular →
            P targetOutcome) := by
  obtain
      ⟨afterState, headCode, tail, targetBlock, bodyCursor,
        hCompiled, hHeadCode, hFinish, hAfterEnv, hAfterLayout,
        hTransport, hExact⟩ :=
    cursor.blockCursors
  subst headCode
  obtain ⟨targetOutcome, hBodyResult, hP⟩ :=
    hBody bodyCursor
  have hPlanAgree :
      AllocationObserverRelation.PlanAgreesOn
        bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  cases hBodyResult with
  | @regular sourceFinal targetBodyFinal finalMode finalCtx
      hBodyForward hBodyControl =>
      obtain ⟨targetFinal, hStmtForward⟩ :=
        AllocationObserverStatement.Sequence.RegularStmtInvariantForward.block_of_components
          hBodyForward.toInvariant hSourceScope
          (fun name hName =>
            Functions.Scope.Block.mem_outEnv hName)
          bodyCursor.sourceScoped hInvariant.activation bodyCursor.lower
          bodyCursor.compile hFinish
      have hStmtResource :=
        hStmtForward.toStackResource
          (allocatorDepth := allocatorDepth) hInvariant.owned
      have hStmtResource' :=
        hStmtResource.transport_lower_state hAfterEnv hAfterLayout
      exact
        ⟨afterState, targetBlock.stmts, tail,
          Functions.Source.Effectful.Outcome.regular
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              live sourceFinal),
          Structured.EffectSemantics.Outcome.regular targetFinal,
          hCompiled,
          .regular hStmtResource'
            (AllocationObserverOutcome.SameControl.refl sourceCtx),
          hTransport, hExact, (fun _ => rfl),
          (fun hMode => False.elim (hMode rfl)),
          (fun hMode => False.elim (hMode rfl))⟩
  | nonregular hMode hBodyForward =>
      have hStmtForward :=
        AllocationObserverOutcome.NonregularStmtResourceForward.block_of_resource
          hBodyForward hMode hPlanAgree hControl hFinish
      exact
        ⟨afterState, targetBlock.stmts, tail,
          bodyOutcome, targetOutcome, hCompiled,
          .nonregular hStmtForward, hTransport, hExact,
          (fun hRegular => False.elim (hMode hRegular)),
          (fun _ => rfl), (fun _ => hP)⟩


end BodyCursor

namespace Callee

/--
Recover the compiler-owned entry phases and procedure shape for a selected
function whose allocation artifact requires no scratch frame.
-/
private theorem prepared_stack_entry
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hNoFrame : artifact.needsFrame = false)
    {transcript : Trace}
    {frameBase : Nat}
    {sourceBodyStart : Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase .stack sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source) :
    ∃ targetBodyStart markerFuel preludeFuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured markerFuel
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode }
        targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry) ∧
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured preludeFuel
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) }
        targetEntry
        (Structured.EffectSemantics.Outcome.regular targetBodyStart) ∧
      AllocationObserverContext.ActivationInvariant
        program.memoryContract artifact.lowerCtx artifact.bodyStart
        prepared.returnCtx prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        frameBase .stack sourceBodyStart targetBodyStart ∧
      artifact.lowerProc.toStructured.body.stmts =
        (Expressions.StmtList.toStructured prepared.markerCode ++
          Expressions.StmtList.toStructured
            (prepared.paramCode ++ prepared.returnCode)) ++
          Expressions.StmtList.toStructured prepared.bodyCode ++
          Expressions.StmtList.toStructured
            (Locals.codeStmt prepared.returnValueCode ++
              Locals.codeStmt prepared.cleanup) := by
  have hPreludeContext :
      AllocationObserverContext.FunctionPreludeContext
        artifact.lowerCtx prepared.plan artifact.recipe.frameWords
        artifact.slots artifact.entryCtx prepared.paramCtx
        prepared.returnCtx .stack := by
    simpa [prepared.mode_eq_stack_of_noFrame hNoFrame] using
      prepared.prelude
  have hBodyEnv :
      artifact.bodyStart.allocation.env =
        AllocationSupport.functionEnv artifact.slots := by
    rfl
  have hParamLayout :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      prepared.compileParams
  have hReturnLayout :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      prepared.compileReturns
  have hParamLayout' :
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryLayout).2 := by
    simpa [
      AllocationObserverCall.SelectedCallee.Artifact.entryCtx] using
      hParamLayout
  have hBodyLayout :
      artifact.bodyStart.layout = prepared.returnCtx.layout := by
    simp only [
      AllocationObserverCall.SelectedCallee.Artifact.bodyStart]
    rw [← hParamLayout', ← hReturnLayout]
  obtain
      ⟨preludeCode, targetBodyStart, preludeFuel,
        hPreludeCompile, hPreludeEval, hPreludeInvariant⟩ :=
    AllocationObserverCall.FunctionPrelude.forward_stack_invariant
      (targetProgram := expressions.toStructured)
      hPreludeContext hEntry hEntryStackLength hZero prepared.planWF
      hBodyEnv hBodyLayout hDefined
  have hExpectedPreludeCompile :=
    Locals.Block.compileOpen_append
      prepared.compileParams prepared.compileReturns
  have hPreludeCode :
      preludeCode = prepared.paramCode ++ prepared.returnCode := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (hPreludeCompile.symm.trans hExpectedPreludeCompile))
  subst preludeCode
  have hExpectedMarkers :=
    AllocationObserverCall.EntryMarkers.compileOpen
      (localsCtx := artifact.entryCtx)
      (entryLayout := artifact.entryLayout)
      (baseDepth := fn.params.length)
      (scratchBindings := artifact.scratchBindings)
      (needsFrame := artifact.needsFrame)
  have hMarkerCode :
      prepared.markerCode =
        [Expressions.Stmt.code
          [Structured.BasicInstr.bindLocals 0 artifact.entryLayout]] := by
    have hCompiled :=
      congrArg Prod.fst
        (Option.some.inj
          (prepared.compileMarkers.symm.trans hExpectedMarkers))
    simpa [hNoFrame] using hCompiled
  obtain ⟨markerFuel, hMarkerEvalRaw⟩ :=
    AllocationObserverCall.EntryMarkers.eval expressions.toStructured
      artifact.entryLayout fn.params.length artifact.scratchBindings
      artifact.needsFrame targetEntry
  have hMarkerEval :
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured markerFuel
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode }
        targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry) := by
    rw [hMarkerCode]
    simpa [hNoFrame, Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hMarkerEvalRaw
  have hProcShape :
      artifact.lowerProc.toStructured.body.stmts =
        (Expressions.StmtList.toStructured prepared.markerCode ++
          Expressions.StmtList.toStructured
            (prepared.paramCode ++ prepared.returnCode)) ++
          Expressions.StmtList.toStructured prepared.bodyCode ++
          Expressions.StmtList.toStructured
            (Locals.codeStmt prepared.returnValueCode ++
              Locals.codeStmt prepared.cleanup) := by
    have hShape :=
      congrArg Expressions.StmtList.toStructured prepared.procBody
    have hBodyStructured :
        artifact.lowerProc.body.toStructured.stmts =
          Expressions.StmtList.toStructured
            artifact.lowerProc.body.stmts := by
      cases artifact.lowerProc.body
      rfl
    change artifact.lowerProc.body.toStructured.stmts = _
    rw [hBodyStructured]
    simpa only [Expressions.StmtList.toStructured_append,
      List.append_assoc] using hShape
  exact
    ⟨targetBodyStart, markerFuel, preludeFuel, hMarkerEval,
      by simpa only [Expressions.Block.toStructured] using hPreludeEval,
      hPreludeInvariant, hProcShape⟩

/--
Construct a regularly returning selected callee in the compiler-selected
all-stack mode.
-/
theorem prepared_regular_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hNoFrame : artifact.needsFrame = false)
    {frameBase : Nat}
    {transcript : Trace}
    {sourceBodyStart sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    {returnValues : List Word}
    {bodyLive : List Functions.Name}
    {finalSourceCtx : Functions.Source.Ctx}
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase .stack sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source)
    (hReturnFrame : targetEntry.source.returns ≠ [])
    (hBody :
      ∀ {targetBodyStart : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            program.memoryContract artifact.lowerCtx artifact.bodyStart
            prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase .stack sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetBodyFinal finalMode,
          AllocationObserverStatement.Sequence.RegularBlockInvariantForward
            program.memoryContract transcript artifact.lowerCtx
            prepared.bodyFinal prepared.bodyCtx prepared.plan bodyLive
            frameBase .stack finalMode program
            (Functions.Source.Effectful.FunDef.bodyCtx fn)
            fn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart sourceBodyFinal targetBodyFinal finalSourceCtx)
    (hReturnsLive :
      ∀ returnName, returnName ∈ fn.returns →
        returnName ∈ bodyLive)
    (hReturns :
      Functions.Source.Store.lookupMany fn.returns
          sourceBodyFinal.source.vars =
        some returnValues) :
    ∃ calleeFinal fuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured fuel artifact.lowerProc.toStructured.body
        targetEntry
        (Structured.EffectSemantics.Outcome.regular calleeFinal) ∧
      calleeFinal.source.evm.stack = returnValues.reverse ∧
      sourceBodyFinal.cursor = calleeFinal.cursor ∧
      Compiler.MemoryRelation.MachineRel program.memoryContract
        sourceBodyFinal.source.shared.toMachineState
        calleeFinal.source.evm.toMachineState ∧
      sourceBodyFinal.source.shared.toState =
        calleeFinal.source.evm.toSharedState.toState ∧
      calleeFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  obtain
      ⟨targetBodyStart, markerFuel, preludeFuel, hMarkerEval,
        hPreludeEval, hPreludeInvariant, hProcShape⟩ :=
    prepared_stack_entry prepared hNoFrame hEntry hEntryStackLength
      hZero hDefined
  have hBodyReturnFrame : targetBodyStart.source.returns ≠ [] := by
    have hReturnsFrame :=
      Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
        hPreludeEval
          (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
    simp only [Structured.ObserverSemantics.Outcome.regular_state] at hReturnsFrame
    rw [hReturnsFrame]
    exact hReturnFrame
  obtain ⟨targetBodyFinal, finalMode, hBodyForward⟩ :=
    hBody hPreludeInvariant hBodyReturnFrame
  rcases hBodyForward with
    ⟨_sourceFuel, bodyFuel, _hSourceBody, hTargetBody,
      hBodyInvariant, hBodySame⟩
  have hFinalMode : finalMode = .stack :=
    hBodySame.right_eq_stack_of_left_eq_stack rfl
  subst finalMode
  obtain
      ⟨_afterValues, calleeFinal, _hValuesRun, _hCleanupRun,
        hReturnEval, hReturnedStack, hCursor, hMachine, hWorld,
        hActiveNoWrap⟩ :=
    AllocationObserverCall.FunctionReturn.forward_regular_stack
      hBodyInvariant hReturnsLive hReturns
      prepared.lowerReturnValues prepared.compileReturnValues
      prepared.compileCleanup
  obtain ⟨fuel, hEval⟩ :=
    AllocationObserverCall.RegularCallee.compose_eval
      (proc := artifact.lowerProc.toStructured)
      (markerBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode })
      (preludeBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) })
      (bodyBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.bodyCode })
      (returnBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (Locals.codeStmt prepared.returnValueCode ++
                Locals.codeStmt prepared.cleanup) })
      hProcShape hMarkerEval hPreludeEval hTargetBody hReturnEval
  exact
    ⟨calleeFinal, fuel, hEval, hReturnedStack, hCursor, hMachine,
      hWorld, hActiveNoWrap⟩

/--
Construct a selected all-stack callee whose body exits through `leave`.
-/
theorem prepared_leave_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hNoFrame : artifact.needsFrame = false)
    {frameBase : Nat}
    {transcript : Trace}
    {sourceBodyStart sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    {returnValues : List Word}
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase .stack sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source)
    (hReturnFrame : targetEntry.source.returns ≠ [])
    (hBody :
      ∀ {targetBodyStart : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            program.memoryContract artifact.lowerCtx artifact.bodyStart
            prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase .stack sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetBodyFinal finalMode bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart
            (Structured.EffectSemantics.Outcome.leave targetBodyFinal) ∧
          SameFrame .stack finalMode ∧
          LeaveStateRel program.memoryContract fn.returns
            sourceBodyFinal targetBodyFinal)
    (hReturns :
      Functions.Source.Store.lookupMany fn.returns
          sourceBodyFinal.source.vars =
        some returnValues) :
    ∃ calleeFinal fuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured fuel artifact.lowerProc.toStructured.body
        targetEntry
        (Structured.EffectSemantics.Outcome.leave calleeFinal) ∧
      calleeFinal.source.evm.stack = returnValues.reverse ∧
      sourceBodyFinal.cursor = calleeFinal.cursor ∧
      Compiler.MemoryRelation.MachineRel program.memoryContract
        sourceBodyFinal.source.shared.toMachineState
        calleeFinal.source.evm.toMachineState ∧
      sourceBodyFinal.source.shared.toState =
        calleeFinal.source.evm.toSharedState.toState ∧
      calleeFinal.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  obtain
      ⟨targetBodyStart, markerFuel, preludeFuel, hMarkerEval,
        hPreludeEval, hPreludeInvariant, hProcShape⟩ :=
    prepared_stack_entry prepared hNoFrame hEntry hEntryStackLength
      hZero hDefined
  have hBodyReturnFrame : targetBodyStart.source.returns ≠ [] := by
    have hReturnsFrame :=
      Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
        hPreludeEval
          (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
    simp only [Structured.ObserverSemantics.Outcome.regular_state] at hReturnsFrame
    rw [hReturnsFrame]
    exact hReturnFrame
  obtain
      ⟨targetBodyFinal, finalMode, bodyFuel, hTargetBody,
        hBodySame, hLeaveRel⟩ :=
    hBody hPreludeInvariant hBodyReturnFrame
  have _hFinalMode : finalMode = .stack :=
    hBodySame.right_eq_stack_of_left_eq_stack rfl
  obtain ⟨returned, hReturned, hReturnedStack⟩ :=
    hLeaveRel.values
  have hReturnedEq : returned = returnValues :=
    Option.some.inj (hReturned.symm.trans hReturns)
  subst returned
  obtain ⟨fuel, hEval⟩ :=
    AllocationObserverCall.RegularCallee.compose_nonregular_eval
      (proc := artifact.lowerProc.toStructured)
      (markerBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode })
      (preludeBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) })
      (bodyBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.bodyCode })
      (returnBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (Locals.codeStmt prepared.returnValueCode ++
                Locals.codeStmt prepared.cleanup) })
      hProcShape hMarkerEval hPreludeEval hTargetBody
      (by intro hMode; cases hMode)
  exact
    ⟨targetBodyFinal, fuel, hEval, hReturnedStack, hLeaveRel.cursor,
      hLeaveRel.shared.machine, hLeaveRel.shared.world,
      hLeaveRel.activeNoWrap⟩

/--
Construct a selected all-stack callee whose body halts.
-/
theorem prepared_halt_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hNoFrame : artifact.needsFrame = false)
    {frameBase : Nat}
    {transcript : Trace}
    {sourceBodyStart sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase .stack sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source)
    (hReturnFrame : targetEntry.source.returns ≠ [])
    (hBody :
      ∀ {targetBodyStart : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationInvariant
            program.memoryContract artifact.lowerCtx artifact.bodyStart
            prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase .stack sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetBodyFinal finalMode bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart
            (Structured.EffectSemantics.Outcome.halt kind targetBodyFinal) ∧
          SameFrame .stack finalMode ∧
          HaltStateRel program.memoryContract prepared.plan
            sourceBodyFinal targetBodyFinal) :
    ∃ calleeFinal fuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured fuel artifact.lowerProc.toStructured.body
        targetEntry
        (Structured.EffectSemantics.Outcome.halt kind calleeFinal) ∧
      HaltStateRel program.memoryContract prepared.plan
        sourceBodyFinal calleeFinal := by
  obtain
      ⟨targetBodyStart, markerFuel, preludeFuel, hMarkerEval,
        hPreludeEval, hPreludeInvariant, hProcShape⟩ :=
    prepared_stack_entry prepared hNoFrame hEntry hEntryStackLength
      hZero hDefined
  have hBodyReturnFrame : targetBodyStart.source.returns ≠ [] := by
    have hReturnsFrame :=
      Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
        hPreludeEval
          (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
    simp only [Structured.ObserverSemantics.Outcome.regular_state] at hReturnsFrame
    rw [hReturnsFrame]
    exact hReturnFrame
  obtain
      ⟨targetBodyFinal, finalMode, bodyFuel, hTargetBody,
        hBodySame, hHaltRel⟩ :=
    hBody hPreludeInvariant hBodyReturnFrame
  have _hFinalMode : finalMode = .stack :=
    hBodySame.right_eq_stack_of_left_eq_stack rfl
  obtain ⟨fuel, hEval⟩ :=
    AllocationObserverCall.RegularCallee.compose_nonregular_eval
      (proc := artifact.lowerProc.toStructured)
      (markerBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode })
      (preludeBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) })
      (bodyBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.bodyCode })
      (returnBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (Locals.codeStmt prepared.returnValueCode ++
                Locals.codeStmt prepared.cleanup) })
      hProcShape hMarkerEval hPreludeEval hTargetBody
      (by intro hMode; cases hMode)
  exact ⟨targetBodyFinal, fuel, hEval, hHaltRel⟩

/--
Construct the complete regular target execution of one compiler-selected
callee from its checked artifact and one recursive body-preservation result.

The recursive callback is private proof plumbing for the forthcoming
source-fuel theorem. All generated code, layouts, procedure lookup, preludes,
and return epilogues are supplied by `SelectedCallee.Prepared`.
-/
theorem prepared_regular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {callerDepth calleeDepth frameBase : Nat}
    {transcript : Trace}
    {sourceBodyStart sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    {returnValues : List Word}
    {bodyLive : List Functions.Name}
    {finalSourceCtx : Functions.Source.Ctx}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase prepared.mode sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source)
    (hReady : Frame.AllocatorReady config calleeDepth targetEntry)
    (hOwned :
      Frame.ActivationOwned config calleeDepth frameBase prepared.mode)
    (hReturnFrame : targetEntry.source.returns ≠ [])
    (hBody :
      ∀ {targetBodyStart : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetBodyFinal finalMode,
          AllocationObserverStatement.Sequence.RegularBlockRuntimeInvariantForward
            program.memoryContract config calleeDepth transcript
            artifact.lowerCtx prepared.bodyFinal prepared.bodyCtx
            prepared.plan bodyLive
            frameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            finalMode program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            fn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart sourceBodyFinal targetBodyFinal finalSourceCtx)
    (hReturnsLive :
      ∀ returnName, returnName ∈ fn.returns →
        returnName ∈ bodyLive)
    (hReturns :
      Functions.Source.Store.lookupMany fn.returns
          sourceBodyFinal.source.vars =
        some returnValues)
    (hProtectedBound :
      AllocationObserverCall.RegularCallee.protectedBound
          calleeDepth prepared.mode =
        callerDepth + 1) :
    ∃ calleeFinal fuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured fuel artifact.lowerProc.toStructured.body
        targetEntry
        (Structured.EffectSemantics.Outcome.regular calleeFinal) ∧
      calleeFinal.source.evm.stack = returnValues.reverse ∧
      sourceBodyFinal.cursor = calleeFinal.cursor ∧
      Compiler.MemoryRelation.MachineRel program.memoryContract
        sourceBodyFinal.source.shared.toMachineState
        calleeFinal.source.evm.toMachineState ∧
      sourceBodyFinal.source.shared.toState =
        calleeFinal.source.evm.toSharedState.toState ∧
      Frame.BoundedEffect config calleeDepth (callerDepth + 1)
        targetEntry calleeFinal := by
  have hBodyEnv :
      artifact.bodyStart.allocation.env =
        AllocationSupport.functionEnv artifact.slots := by
    rfl
  have hParamLayout :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      prepared.compileParams
  have hReturnLayout :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      prepared.compileReturns
  have hParamLayout' :
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryLayout).2 := by
    simpa [
      AllocationObserverCall.SelectedCallee.Artifact.entryCtx] using
      hParamLayout
  have hBodyLayout :
      artifact.bodyStart.layout = prepared.returnCtx.layout := by
    simp only [
      AllocationObserverCall.SelectedCallee.Artifact.bodyStart]
    rw [← hParamLayout', ← hReturnLayout]
  obtain
      ⟨preludeCode, targetBodyStart, preludeFuel,
        hPreludeCompile, hPreludeEval, hPreludeInvariant,
        hPreludeSame, hPreludeEffect⟩ :=
    AllocationObserverCall.FunctionPrelude.forward_invariant
      (targetProgram := expressions.toStructured)
      prepared.prelude hEntry hEntryStackLength hZero prepared.planWF
      (AllocationObserverCall.FunctionPrelude.SelectedCallee.Prepared.scratchAuthorized
        prepared hConfig)
      hConfig hReady hOwned
      hBodyEnv hBodyLayout hDefined
  have hExpectedPreludeCompile :=
    Locals.Block.compileOpen_append
      prepared.compileParams prepared.compileReturns
  have hPreludeCode :
      preludeCode = prepared.paramCode ++ prepared.returnCode := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (hPreludeCompile.symm.trans hExpectedPreludeCompile))
  subst preludeCode
  have hBodyReturnFrame : targetBodyStart.source.returns ≠ [] := by
    have hReturns :=
      Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
        hPreludeEval
          (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
    simp only [Structured.ObserverSemantics.Outcome.regular_state] at hReturns
    rw [hReturns]
    exact hReturnFrame
  obtain ⟨targetBodyFinal, finalMode, hBodyForward⟩ :=
    hBody hPreludeInvariant hBodyReturnFrame
  rcases hBodyForward with
    ⟨_sourceFuel, bodyFuel, _hSourceBody, hTargetBody,
      hBodyInvariant, hBodySame, hBodyEffect⟩
  obtain
      ⟨_afterValues, calleeFinal, _hValuesRun, _hCleanupRun,
        hReturnEval, hReturnedStack, hCursor, hMachine, hWorld,
        hReturnEffect⟩ :=
    AllocationObserverCall.FunctionReturn.forward_regular
      hConfig hBodyInvariant hReturnsLive hReturns
      prepared.lowerReturnValues prepared.compileReturnValues
      prepared.compileCleanup
  have hExpectedMarkers :=
    AllocationObserverCall.EntryMarkers.compileOpen
      (localsCtx := artifact.entryCtx)
      (entryLayout := artifact.entryLayout)
      (baseDepth := fn.params.length)
      (scratchBindings := artifact.scratchBindings)
      (needsFrame := artifact.needsFrame)
  have hMarkerCode :
      prepared.markerCode =
        [Expressions.Stmt.code
          [Structured.BasicInstr.bindLocals 0 artifact.entryLayout]] ++
        if artifact.needsFrame then
          [Expressions.Stmt.code
            (AllocationSupport.bindScratchBindingsCode
              fn.params.length artifact.scratchBindings)]
        else
          [] := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (prepared.compileMarkers.symm.trans hExpectedMarkers))
  obtain ⟨markerFuel, hMarkerEvalRaw⟩ :=
    AllocationObserverCall.EntryMarkers.eval expressions.toStructured
      artifact.entryLayout fn.params.length artifact.scratchBindings
      artifact.needsFrame targetEntry
  have hMarkerEval :
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured markerFuel
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode }
        targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry) := by
    rw [hMarkerCode]
    cases hNeedsFrame : artifact.needsFrame <;>
      simp [hNeedsFrame, Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] at hMarkerEvalRaw ⊢
    · exact hMarkerEvalRaw
    · exact hMarkerEvalRaw
  have hProcShape :
      artifact.lowerProc.toStructured.body.stmts =
        (Expressions.StmtList.toStructured prepared.markerCode ++
          Expressions.StmtList.toStructured
            (prepared.paramCode ++ prepared.returnCode)) ++
          Expressions.StmtList.toStructured prepared.bodyCode ++
        Expressions.StmtList.toStructured
            (Locals.codeStmt prepared.returnValueCode ++
              Locals.codeStmt prepared.cleanup) := by
    have hShape :=
      congrArg Expressions.StmtList.toStructured prepared.procBody
    have hBodyStructured :
        artifact.lowerProc.body.toStructured.stmts =
          Expressions.StmtList.toStructured
            artifact.lowerProc.body.stmts := by
      cases artifact.lowerProc.body
      rfl
    change artifact.lowerProc.body.toStructured.stmts = _
    rw [hBodyStructured]
    simpa only [Expressions.StmtList.toStructured_append,
      List.append_assoc] using hShape
  have hBodyEffect' :
      Frame.ActivationEffect config calleeDepth finalMode
        targetBodyStart targetBodyFinal :=
    hBodyEffect.mode_of_sameFrame hBodySame
  have hEntryFinalSame :
      SameFrame prepared.mode finalMode :=
    hPreludeSame.trans hBodySame
  obtain ⟨fuel, hEval, hEffect⟩ :=
    AllocationObserverCall.RegularCallee.compose
      (callerDepth := callerDepth)
      (calleeDepth := calleeDepth)
      (entryMode := prepared.mode)
      (bodyMode := finalMode)
      (proc := artifact.lowerProc.toStructured)
      (markerBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode })
      (preludeBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) })
      (bodyBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.bodyCode })
      (returnBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (Locals.codeStmt prepared.returnValueCode ++
                Locals.codeStmt prepared.cleanup) })
      hProcShape hMarkerEval
      (by
        simpa only [Expressions.Block.toStructured] using hPreludeEval)
      hTargetBody hReturnEval
      hEntryFinalSame
      hPreludeEffect hBodyEffect' hReturnEffect hProtectedBound
  exact
    ⟨calleeFinal, fuel, hEval, hReturnedStack, hCursor, hMachine,
      hWorld, hEffect⟩

/--
Construct the complete target execution of a compiler-selected callee whose
source body reaches `leave`. The callback supplies the recursively preserved
body exit; the compiler-owned regular epilogue is then proved unreachable by
`RegularCallee.compose_leave`.
-/
theorem prepared_leave
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {callerDepth calleeDepth frameBase : Nat}
    {transcript : Trace}
    {sourceBodyStart sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    {returnValues : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase prepared.mode sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source)
    (hReady : Frame.AllocatorReady config calleeDepth targetEntry)
    (hOwned :
      Frame.ActivationOwned config calleeDepth frameBase prepared.mode)
    (hReturnFrame : targetEntry.source.returns ≠ [])
    (hBody :
      ∀ {targetBodyStart : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase
            (prepared.mode.atStackDepth
            (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetBodyFinal finalMode bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart
            (Structured.EffectSemantics.Outcome.leave targetBodyFinal) ∧
          SameFrame
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            finalMode ∧
          Frame.ActivationEffect config calleeDepth
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            targetBodyStart targetBodyFinal ∧
          targetBodyFinal.source.evm.stack = returnValues.reverse ∧
          sourceBodyFinal.cursor = targetBodyFinal.cursor ∧
          Compiler.MemoryRelation.MachineRel program.memoryContract
            sourceBodyFinal.source.shared.toMachineState
            targetBodyFinal.source.evm.toMachineState ∧
          sourceBodyFinal.source.shared.toState =
            targetBodyFinal.source.evm.toSharedState.toState)
    (hProtectedBound :
      AllocationObserverCall.RegularCallee.protectedBound
          calleeDepth prepared.mode =
        callerDepth + 1) :
    ∃ calleeFinal fuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured fuel artifact.lowerProc.toStructured.body
        targetEntry
        (Structured.EffectSemantics.Outcome.leave calleeFinal) ∧
      calleeFinal.source.evm.stack = returnValues.reverse ∧
      sourceBodyFinal.cursor = calleeFinal.cursor ∧
      Compiler.MemoryRelation.MachineRel program.memoryContract
        sourceBodyFinal.source.shared.toMachineState
        calleeFinal.source.evm.toMachineState ∧
      sourceBodyFinal.source.shared.toState =
        calleeFinal.source.evm.toSharedState.toState ∧
      Frame.BoundedEffect config calleeDepth (callerDepth + 1)
        targetEntry calleeFinal := by
  have hBodyEnv :
      artifact.bodyStart.allocation.env =
        AllocationSupport.functionEnv artifact.slots := by
    rfl
  have hParamLayout :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      prepared.compileParams
  have hReturnLayout :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      prepared.compileReturns
  have hParamLayout' :
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryLayout).2 := by
    simpa [
      AllocationObserverCall.SelectedCallee.Artifact.entryCtx] using
      hParamLayout
  have hBodyLayout :
      artifact.bodyStart.layout = prepared.returnCtx.layout := by
    simp only [
      AllocationObserverCall.SelectedCallee.Artifact.bodyStart]
    rw [← hParamLayout', ← hReturnLayout]
  obtain
      ⟨preludeCode, targetBodyStart, preludeFuel,
        hPreludeCompile, hPreludeEval, hPreludeInvariant,
        hPreludeSame, hPreludeEffect⟩ :=
    AllocationObserverCall.FunctionPrelude.forward_invariant
      (targetProgram := expressions.toStructured)
      prepared.prelude hEntry hEntryStackLength hZero prepared.planWF
      (AllocationObserverCall.FunctionPrelude.SelectedCallee.Prepared.scratchAuthorized
        prepared hConfig)
      hConfig hReady hOwned hBodyEnv hBodyLayout hDefined
  have hExpectedPreludeCompile :=
    Locals.Block.compileOpen_append
      prepared.compileParams prepared.compileReturns
  have hPreludeCode :
      preludeCode = prepared.paramCode ++ prepared.returnCode := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (hPreludeCompile.symm.trans hExpectedPreludeCompile))
  subst preludeCode
  have hBodyReturnFrame : targetBodyStart.source.returns ≠ [] := by
    have hReturns :=
      Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
        hPreludeEval
          (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
    simp only [Structured.ObserverSemantics.Outcome.regular_state] at hReturns
    rw [hReturns]
    exact hReturnFrame
  obtain
      ⟨targetBodyFinal, finalMode, bodyFuel, hTargetBody,
        hBodySame, hBodyEffect, hReturnedStack, hCursor, hMachine,
        hWorld⟩ :=
    hBody hPreludeInvariant hBodyReturnFrame
  have hExpectedMarkers :=
    AllocationObserverCall.EntryMarkers.compileOpen
      (localsCtx := artifact.entryCtx)
      (entryLayout := artifact.entryLayout)
      (baseDepth := fn.params.length)
      (scratchBindings := artifact.scratchBindings)
      (needsFrame := artifact.needsFrame)
  have hMarkerCode :
      prepared.markerCode =
        [Expressions.Stmt.code
          [Structured.BasicInstr.bindLocals 0 artifact.entryLayout]] ++
        if artifact.needsFrame then
          [Expressions.Stmt.code
            (AllocationSupport.bindScratchBindingsCode
              fn.params.length artifact.scratchBindings)]
        else
          [] := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (prepared.compileMarkers.symm.trans hExpectedMarkers))
  obtain ⟨markerFuel, hMarkerEvalRaw⟩ :=
    AllocationObserverCall.EntryMarkers.eval expressions.toStructured
      artifact.entryLayout fn.params.length artifact.scratchBindings
      artifact.needsFrame targetEntry
  have hMarkerEval :
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured markerFuel
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode }
        targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry) := by
    rw [hMarkerCode]
    cases hNeedsFrame : artifact.needsFrame <;>
      simp [hNeedsFrame, Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] at hMarkerEvalRaw ⊢
    · exact hMarkerEvalRaw
    · exact hMarkerEvalRaw
  have hProcShape :
      artifact.lowerProc.toStructured.body.stmts =
        (Expressions.StmtList.toStructured prepared.markerCode ++
          Expressions.StmtList.toStructured
            (prepared.paramCode ++ prepared.returnCode)) ++
          Expressions.StmtList.toStructured prepared.bodyCode ++
          Expressions.StmtList.toStructured
            (Locals.codeStmt prepared.returnValueCode ++
              Locals.codeStmt prepared.cleanup) := by
    have hShape :=
      congrArg Expressions.StmtList.toStructured prepared.procBody
    have hBodyStructured :
        artifact.lowerProc.body.toStructured.stmts =
          Expressions.StmtList.toStructured
            artifact.lowerProc.body.stmts := by
      cases artifact.lowerProc.body
      rfl
    change artifact.lowerProc.body.toStructured.stmts = _
    rw [hBodyStructured]
    simpa only [Expressions.StmtList.toStructured_append,
      List.append_assoc] using hShape
  have hBodyEffect' :
      Frame.ActivationEffect config calleeDepth finalMode
        targetBodyStart targetBodyFinal :=
    hBodyEffect.mode_of_sameFrame hBodySame
  have hEntryFinalSame :
      SameFrame prepared.mode finalMode :=
    hPreludeSame.trans hBodySame
  obtain ⟨fuel, hEval, hEffect⟩ :=
    AllocationObserverCall.RegularCallee.compose_leave
      (callerDepth := callerDepth)
      (calleeDepth := calleeDepth)
      (entryMode := prepared.mode)
      (bodyMode := finalMode)
      (proc := artifact.lowerProc.toStructured)
      (markerBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode })
      (preludeBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) })
      (bodyBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.bodyCode })
      (returnBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (Locals.codeStmt prepared.returnValueCode ++
                Locals.codeStmt prepared.cleanup) })
      hProcShape hMarkerEval
      (by
        simpa only [Expressions.Block.toStructured] using hPreludeEval)
      hTargetBody hEntryFinalSame hPreludeEffect hBodyEffect'
      hProtectedBound
  exact
    ⟨targetBodyFinal, fuel, hEval, hReturnedStack, hCursor, hMachine,
      hWorld, hEffect⟩

/--
Construct the complete target execution of a compiler-selected callee whose
source body halts. Entry markers and the generated prelude execute normally;
the regular return epilogue is unreachable after the recursively preserved
terminal outcome.
-/
theorem prepared_halt
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {callerDepth calleeDepth frameBase : Nat}
    {transcript : Trace}
    {sourceBodyStart sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    {kind : Assembly.HaltKind}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase prepared.mode sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source)
    (hReady : Frame.AllocatorReady config calleeDepth targetEntry)
    (hOwned :
      Frame.ActivationOwned config calleeDepth frameBase prepared.mode)
    (hReturnFrame : targetEntry.source.returns ≠ [])
    (hBody :
      ∀ {targetBodyStart : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetBodyFinal finalMode bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart
            (Structured.EffectSemantics.Outcome.halt kind targetBodyFinal) ∧
          SameFrame
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            finalMode ∧
          Frame.OutcomeEffect config calleeDepth
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            targetBodyStart targetBodyFinal (.halt kind) ∧
          HaltStateRel program.memoryContract prepared.plan
            sourceBodyFinal targetBodyFinal)
    (hProtectedBound :
      AllocationObserverCall.RegularCallee.protectedBound
          calleeDepth prepared.mode =
        callerDepth + 1) :
    ∃ calleeFinal fuel finalDepth,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured fuel artifact.lowerProc.toStructured.body
        targetEntry
        (Structured.EffectSemantics.Outcome.halt kind calleeFinal) ∧
      HaltStateRel program.memoryContract prepared.plan
        sourceBodyFinal calleeFinal ∧
      Frame.BoundedEffect config finalDepth (callerDepth + 1)
        targetEntry calleeFinal := by
  have hBodyEnv :
      artifact.bodyStart.allocation.env =
        AllocationSupport.functionEnv artifact.slots := by
    rfl
  have hParamLayout :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      prepared.compileParams
  have hReturnLayout :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      prepared.compileReturns
  have hParamLayout' :
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryLayout).2 := by
    simpa [
      AllocationObserverCall.SelectedCallee.Artifact.entryCtx] using
      hParamLayout
  have hBodyLayout :
      artifact.bodyStart.layout = prepared.returnCtx.layout := by
    simp only [
      AllocationObserverCall.SelectedCallee.Artifact.bodyStart]
    rw [← hParamLayout', ← hReturnLayout]
  obtain
      ⟨preludeCode, targetBodyStart, preludeFuel,
        hPreludeCompile, hPreludeEval, hPreludeInvariant,
        hPreludeSame, hPreludeEffect⟩ :=
    AllocationObserverCall.FunctionPrelude.forward_invariant
      (targetProgram := expressions.toStructured)
      prepared.prelude hEntry hEntryStackLength hZero prepared.planWF
      (AllocationObserverCall.FunctionPrelude.SelectedCallee.Prepared.scratchAuthorized
        prepared hConfig)
      hConfig hReady hOwned hBodyEnv hBodyLayout hDefined
  have hExpectedPreludeCompile :=
    Locals.Block.compileOpen_append
      prepared.compileParams prepared.compileReturns
  have hPreludeCode :
      preludeCode = prepared.paramCode ++ prepared.returnCode := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (hPreludeCompile.symm.trans hExpectedPreludeCompile))
  subst preludeCode
  have hBodyReturnFrame : targetBodyStart.source.returns ≠ [] := by
    have hReturns :=
      Structured.ObserverSemantics.Block.Eval.returns_eq_of_nonhalting
        hPreludeEval
          (by simp [Structured.ObserverSemantics.Outcome.Nonhalting])
    simp only [Structured.ObserverSemantics.Outcome.regular_state] at hReturns
    rw [hReturns]
    exact hReturnFrame
  obtain
      ⟨targetBodyFinal, finalMode, bodyFuel, hTargetBody,
        hBodySame, hBodyEffect, hHaltRel⟩ :=
    hBody hPreludeInvariant hBodyReturnFrame
  have hExpectedMarkers :=
    AllocationObserverCall.EntryMarkers.compileOpen
      (localsCtx := artifact.entryCtx)
      (entryLayout := artifact.entryLayout)
      (baseDepth := fn.params.length)
      (scratchBindings := artifact.scratchBindings)
      (needsFrame := artifact.needsFrame)
  have hMarkerCode :
      prepared.markerCode =
        [Expressions.Stmt.code
          [Structured.BasicInstr.bindLocals 0 artifact.entryLayout]] ++
        if artifact.needsFrame then
          [Expressions.Stmt.code
            (AllocationSupport.bindScratchBindingsCode
              fn.params.length artifact.scratchBindings)]
        else
          [] := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (prepared.compileMarkers.symm.trans hExpectedMarkers))
  obtain ⟨markerFuel, hMarkerEvalRaw⟩ :=
    AllocationObserverCall.EntryMarkers.eval expressions.toStructured
      artifact.entryLayout fn.params.length artifact.scratchBindings
      artifact.needsFrame targetEntry
  have hMarkerEval :
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured markerFuel
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode }
        targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry) := by
    rw [hMarkerCode]
    cases hNeedsFrame : artifact.needsFrame <;>
      simp [hNeedsFrame, Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] at hMarkerEvalRaw ⊢
    · exact hMarkerEvalRaw
    · exact hMarkerEvalRaw
  have hProcShape :
      artifact.lowerProc.toStructured.body.stmts =
        (Expressions.StmtList.toStructured prepared.markerCode ++
          Expressions.StmtList.toStructured
            (prepared.paramCode ++ prepared.returnCode)) ++
          Expressions.StmtList.toStructured prepared.bodyCode ++
          Expressions.StmtList.toStructured
            (Locals.codeStmt prepared.returnValueCode ++
              Locals.codeStmt prepared.cleanup) := by
    have hShape :=
      congrArg Expressions.StmtList.toStructured prepared.procBody
    have hBodyStructured :
        artifact.lowerProc.body.toStructured.stmts =
          Expressions.StmtList.toStructured
            artifact.lowerProc.body.stmts := by
      cases artifact.lowerProc.body
      rfl
    change artifact.lowerProc.body.toStructured.stmts = _
    rw [hBodyStructured]
    simpa only [Expressions.StmtList.toStructured_append,
      List.append_assoc] using hShape
  have hEntryFinalSame :
      SameFrame prepared.mode finalMode :=
    hPreludeSame.trans hBodySame
  have hBodyEffect' :
      Frame.OutcomeEffect config calleeDepth finalMode
        targetBodyStart targetBodyFinal (.halt kind) :=
    hBodyEffect.mode_of_sameFrame hBodySame
  obtain ⟨finalDepth, fuel, hEval, hEffect⟩ :=
    AllocationObserverCall.RegularCallee.compose_nonregular
      (callerDepth := callerDepth)
      (calleeDepth := calleeDepth)
      (entryMode := prepared.mode)
      (bodyMode := finalMode)
      (proc := artifact.lowerProc.toStructured)
      (markerBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode })
      (preludeBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) })
      (bodyBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.bodyCode })
      (returnBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (Locals.codeStmt prepared.returnValueCode ++
                Locals.codeStmt prepared.cleanup) })
      hProcShape hMarkerEval
      (by
        simpa only [Expressions.Block.toStructured] using hPreludeEval)
      hTargetBody
      (by
        intro hMode
        cases hMode)
      hEntryFinalSame hPreludeEffect hBodyEffect' hProtectedBound
  exact
    ⟨targetBodyFinal, fuel, finalDepth, hEval, hHaltRel, hEffect⟩

end Callee

namespace Call

private theorem eval_phases
    {transcript : Trace}
    {targetProgram : Structured.Program}
    {name : Structured.Name}
    {argsCode stores : Structured.Code}
    {releaseCode : List Structured.Stmt}
    {target targetAfterArgs callFinal targetAssigned targetFinal :
      Structured.ObserverSemantics.State transcript}
    {bodyFuel releaseFuel : Nat}
    (hArgs :
      Structured.ObserverSemantics.Code.run argsCode target =
        .ok targetAfterArgs)
    (hCall :
      Structured.ObserverSemantics.Stmt.Eval targetProgram (bodyFuel + 1)
        (.call name) targetAfterArgs
        (Structured.EffectSemantics.Outcome.regular callFinal))
    (hStores :
      Structured.ObserverSemantics.Code.run stores callFinal =
        .ok targetAssigned)
    (hRelease :
      Structured.ObserverSemantics.Block.Eval targetProgram releaseFuel
        { stmts := releaseCode } targetAssigned
        (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
        { stmts :=
            [Structured.Stmt.code argsCode] ++
              [Structured.Stmt.call name] ++
              [Structured.Stmt.code stores] ++ releaseCode }
        target
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  have hArgsBlock :
      Structured.ObserverSemantics.Block.Eval targetProgram 2
        { stmts := [Structured.Stmt.code argsCode] } target
        (Structured.EffectSemantics.Outcome.regular targetAfterArgs) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hArgs)
      Structured.EffectSemantics.Block.Eval.nil
  have hCallBlock :
      Structured.ObserverSemantics.Block.Eval targetProgram (bodyFuel + 2)
        { stmts := [Structured.Stmt.call name] } targetAfterArgs
        (Structured.EffectSemantics.Outcome.regular callFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular hCall
      Structured.EffectSemantics.Block.Eval.nil
  have hStoresBlock :
      Structured.ObserverSemantics.Block.Eval targetProgram 2
        { stmts := [Structured.Stmt.code stores] } callFinal
        (Structured.EffectSemantics.Outcome.regular targetAssigned) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hStores)
      Structured.EffectSemantics.Block.Eval.nil
  obtain ⟨prefixFuel, hPrefix⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hArgsBlock hCallBlock
  obtain ⟨assignedFuel, hAssigned⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hPrefix hStoresBlock
  obtain ⟨fuel, hEval⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hAssigned hRelease
  exact ⟨fuel, by simpa [List.append_assoc] using hEval⟩

private theorem eval_halt_phases
    {transcript : Trace}
    {targetProgram : Structured.Program}
    {name : Structured.Name}
    {argsCode stores : Structured.Code}
    {releaseCode : List Structured.Stmt}
    {target targetAfterArgs targetFinal :
      Structured.ObserverSemantics.State transcript}
    {bodyFuel : Nat}
    {kind : Assembly.HaltKind}
    (hArgs :
      Structured.ObserverSemantics.Code.run argsCode target =
        .ok targetAfterArgs)
    (hCall :
      Structured.ObserverSemantics.Stmt.Eval targetProgram (bodyFuel + 1)
        (.call name) targetAfterArgs
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
        { stmts :=
            [Structured.Stmt.code argsCode] ++
              [Structured.Stmt.call name] ++
              [Structured.Stmt.code stores] ++ releaseCode }
        target
        (Structured.EffectSemantics.Outcome.halt kind targetFinal) := by
  have hArgsBlock :
      Structured.ObserverSemantics.Block.Eval targetProgram 2
        { stmts := [Structured.Stmt.code argsCode] } target
        (Structured.EffectSemantics.Outcome.regular targetAfterArgs) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hArgs)
      Structured.EffectSemantics.Block.Eval.nil
  have hCallBlock :
      Structured.ObserverSemantics.Block.Eval targetProgram (bodyFuel + 2)
        { stmts := [Structured.Stmt.call name] } targetAfterArgs
        (Structured.EffectSemantics.Outcome.halt kind targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_nonregular hCall
      (by simp)
  obtain ⟨prefixFuel, hPrefix⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hArgsBlock hCallBlock
  have hEval :=
    Structured.EffectSemantics.Block.Eval.append_nonregular
      (right :=
        [Structured.Stmt.code stores] ++ releaseCode)
      hPrefix (by simp)
  exact ⟨prefixFuel, by simpa [List.append_assoc] using hEval⟩

/--
Compose one selected source call when both caller and callee are in the
compiler-selected all-stack mode.
-/
theorem regular_stack_of_selected
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hNoFrame : artifact.needsFrame = false)
    {sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {source sourceAfterArgs sourceBodyStart sourceReturned sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {args : List (Functions.Expr 1)}
    {argValues returnValues : List Word}
    {bodyStore returnStore : Locals.Source.Store}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {bodyMode : AllocationObserverCall.StructuredCall.ReturnMode}
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx))
    (hSafeArgs :
      AllocationObserverSafety.ArgList.MemorySafeEval
        program.memoryContract transcript args source sourceAfterArgs
        argValues)
    (hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst)
          bodyStore =
        some argValues)
    (hBodyStart :
      sourceBodyStart =
        (Functions.ObserverSemantics.stateModel transcript).withSource
          sourceAfterArgs
          { shared := sourceAfterArgs.source.shared
            vars := bodyStore })
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.source.vars =
        some returnStore)
    (hFinal :
      sourceFinal =
        (Functions.ObserverSemantics.stateModel transcript).withSource
          sourceReturned
          { shared := sourceReturned.source.shared
            vars := returnStore })
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive
        (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        program.memoryContract callerCtx callerState callerLocals
        callerPlan callerLive callerFrameBase .stack source target)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hCallee :
      ∀ {targetEntry : Structured.ObserverSemantics.State transcript},
        ActivationCalleeEntryRel
            program.memoryContract prepared.plan []
            artifact.slots.params 0 .stack
            sourceBodyStart targetEntry →
        targetEntry.source.returns ≠ [] →
        targetEntry.source.evm.stack.length =
            artifact.entryCtx.layout.length →
        ∃ calleeFinal bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            artifact.lowerProc.toStructured.body targetEntry
            (bodyMode.outcome calleeFinal) ∧
          calleeFinal.source.evm.stack = returnValues.reverse ∧
          sourceReturned.cursor = calleeFinal.cursor ∧
          Compiler.MemoryRelation.MachineRel program.memoryContract
            sourceReturned.source.shared.toMachineState
            calleeFinal.source.evm.toMachineState ∧
          sourceReturned.source.shared.toState =
            calleeFinal.source.evm.toSharedState.toState ∧
          calleeFinal.source.evm.activeWords.toNat *
              MemoryContract.wordBytes <
            EvmYul.UInt256.size) :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.RegularStmtInvariantForward
        program.memoryContract transcript callerCtx callerFinalState
        callerFinalLocals callerPlan callerLive callerFrameBase .stack .stack
        program sourceCtx (.call targets name args) source
        expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceFinal targetFinal sourceCtx := by
  obtain
      ⟨slotInfo, loweredArgs, callArgs, stores, release,
        argsCode, releaseCode, hSlotLookup, hArgsLength,
        hTargetsLength, hTargetsNodup, hLowerArgs, hCallArgs,
        hStores, hRelease, hArgsCode, hReleaseCode,
        hCompiledShape, hCallerState, hCallerLocals⟩ :=
    AllocationObserverCall.CallCompiler.components hLower hCompile
  subst callerFinalState
  subst callerFinalLocals
  obtain ⟨hRecipeEq, _hSlotsEq, _hFrameNameEq⟩ :=
    compilation.selected_agrees artifact
  have hArtifactSlotLookup :
      AllocationSupport.lookupFun? name callerCtx.functions =
        some artifact.slots := by
    rw [hCallerShared.functions, ← hRecipeEq]
    simpa [artifact.sourceName] using artifact.slotsLookup
  have hSlotInfo : slotInfo = artifact.slots := by
    rw [hArtifactSlotLookup] at hSlotLookup
    exact (Option.some.inj hSlotLookup).symm
  subst slotInfo
  have hSourceOrdinary :=
    AllocationObserverSafety.SafeSemantics.stmt_run_eq hSource
  have hArgsScoped :
      ∀ arg, arg ∈ args →
        Functions.Scope.ExprScoped callerLive arg :=
    hScoped.2.2
  have hTargetsLive :
      ∀ targetName, targetName ∈ targets →
        targetName ∈ callerLive :=
    hScoped.2.1
  have hReturnLength :
      returnValues.length = artifact.lowerProc.retc := by
    rw [prepared.procRetc]
    calc
      returnValues.length = targets.length :=
        Functions.Source.Store.assignMany_length hAssign
      _ = artifact.slots.returns.length := hTargetsLength
      _ = (artifact.slots.returns.map Prod.fst).length := by simp
      _ = fn.returns.length :=
        congrArg List.length artifact.slotsMatch.2.2
  have hParamLength :
      artifact.slots.params.length = fn.params.length := by
    simpa using congrArg List.length artifact.slotsMatch.2.1
  have hCallerStackLength :
      target.source.evm.stack.length = callerLocals.layout.length :=
    hInvariant.stackLength
  have hFrame :
      name ∉ callerCtx.frameFunctions := by
    intro hMem
    have hNeedsFrame :=
      (compilation.call_needsFrame_iff hCallerShared artifact).1 hMem
    simpa [hNoFrame] using hNeedsFrame
  have hCallArgsShape : callArgs = loweredArgs := by
    simpa [hFrame] using hCallArgs.symm
  subst callArgs
  obtain
      ⟨targetAfterArgs, callerBase, hArgsRun, hArgsResult,
        hCallerRel, hCallStack, hCallerBaseStack⟩ :=
    AllocationObserverCall.PreparedArguments.stack_neutral
      hSafeArgs hArgsScoped hLowerArgs hArgsCode hInvariant
  let targetEntry :=
    AllocationObserverCall.CalleeEntry.structuredState
      targetAfterArgs argValues.reverse target.source.evm.stack
      artifact.lowerProc.retc
  have hEntry :
      ActivationCalleeEntryRel program.memoryContract prepared.plan []
        artifact.slots.params 0 .stack sourceBodyStart targetEntry := by
    rw [hBodyStart]
    have hArgsResult' :
        ActivationExprResultRel program.memoryContract callerPlan
          callerLive 0 callerFrameBase argValues.length .stack
          sourceAfterArgs target targetAfterArgs argValues := by
      simpa [hSafeArgs.values_length] using hArgsResult
    exact
      AllocationObserverCall.CalleeEntry.stack_of_arguments
        hArgsResult' hParamLookup
  have hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length := by
    change argValues.reverse.length = artifact.entryLayout.length
    simp [
      AllocationObserverCall.SelectedCallee.Artifact.entryLayout,
      hNoFrame, hArgsResult.valuesLength, hArgsLength,
      hParamLength]
  have hEntryReturnFrame : targetEntry.source.returns ≠ [] := by
    simp [targetEntry,
      AllocationObserverCall.CalleeEntry.structuredState,
      Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.withEVM, Structured.RunState.pushReturn]
  obtain
      ⟨calleeFinal, bodyFuel, hCalleeEval, hReturnedStack,
        hCursor, hMachine, hWorld, hActiveNoWrap⟩ :=
    hCallee hEntry hEntryReturnFrame hEntryStackLength
  obtain
      ⟨callFinal, targetAssigned, hCallEval, hStoresRun,
        hAssignedRel, hAssignedStackLength⟩ :=
    AllocationObserverCall.RegularCall.resume_and_writeback_stack
      hCallerRel hCallerBaseStack artifact.targetLookup
      (by simpa using hCallStack)
      (by
        change argValues.reverse.length = artifact.lowerProc.argc
        rw [prepared.procArgc]
        simp [hNoFrame, hArgsResult.valuesLength,
          hArgsLength, hParamLength])
      hCalleeEval hReturnedStack hReturnLength hCursor hMachine hWorld
      hActiveNoWrap hInvariant.compiler hInvariant.planWF
      hTargetsLive hTargetsNodup hAssign hStores
  have hAssignedDefined :
      LiveDefined callerLive
        ((Functions.ObserverSemantics.stateModel transcript).withSource
          sourceReturned
          { shared := sourceReturned.source.shared
            vars := returnStore }).source := by
    have hAfterArgsDefined :
        LiveDefined callerLive sourceAfterArgs.source :=
      hInvariant.defined.congr_vars hSafeArgs.vars_eq
    simpa [Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Locals.Source.State.withVars] using
      hAfterArgsDefined.assignMany_preserves hAssign
  have hAssignedInvariant :
      AllocationObserverContext.ActivationInvariant
        program.memoryContract callerCtx callerState callerLocals
        callerPlan callerLive callerFrameBase .stack sourceFinal
        targetAssigned := by
    refine
      { compiler := hInvariant.compiler
        planWF := hInvariant.planWF
        defined := ?_
        state := ?_
        stackLength := ?_ }
    · simpa [hFinal] using hAssignedDefined
    · simpa [hFinal] using hAssignedRel
    · exact hAssignedStackLength.trans hCallerStackLength
  have hReleaseShape : release = [] := by
    simpa [hFrame] using hRelease.symm
  subst release
  have hReleaseCodeShape : releaseCode = [] := by
    simpa [Locals.Block.compileOpen] using hReleaseCode
  have hReleaseEval :
      Structured.ObserverSemantics.Block.Eval expressions.toStructured 1
        { stmts := Expressions.StmtList.toStructured releaseCode }
        targetAssigned
        (Structured.EffectSemantics.Outcome.regular targetAssigned) := by
    rw [hReleaseCodeShape]
    exact Structured.EffectSemantics.Block.Eval.nil
  obtain ⟨targetFuel, hTargetEvalRaw⟩ :=
    eval_phases hArgsRun hCallEval hStoresRun
      (by simpa [hReleaseCodeShape] using hReleaseEval)
  have hTargetEval :
      Structured.ObserverSemantics.Block.Eval expressions.toStructured
        targetFuel
        { stmts :=
            Expressions.StmtList.toStructured compiledStmts }
        target
        (Structured.EffectSemantics.Outcome.regular targetAssigned) := by
    rw [hCompiledShape,
      Expressions.StmtList.toStructured_append,
      Expressions.StmtList.toStructured_append,
      Expressions.StmtList.toStructured_append]
    simpa [Locals.codeStmt,
      Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured,
      hReleaseCodeShape] using hTargetEvalRaw
  exact
    ⟨targetAssigned, sourceFuel, targetFuel, hSourceOrdinary,
      hTargetEval, hAssignedInvariant, SameFrame.refl .stack⟩

/--
Compose one selected all-stack source call whose callee halts.
-/
theorem halt_stack_of_selected
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    (hNoFrame : artifact.needsFrame = false)
    {sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {source sourceAfterArgs sourceBodyStart sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {args : List (Functions.Expr 1)}
    {argValues : List Word}
    {bodyStore : Locals.Source.Store}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {kind : Assembly.HaltKind}
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            sourceCtx))
    (hSafeArgs :
      AllocationObserverSafety.ArgList.MemorySafeEval
        program.memoryContract transcript args source sourceAfterArgs
        argValues)
    (hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst)
          bodyStore =
        some argValues)
    (hBodyStart :
      sourceBodyStart =
        (Functions.ObserverSemantics.stateModel transcript).withSource
          sourceAfterArgs
          { shared := sourceAfterArgs.source.shared
            vars := bodyStore })
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive
        (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        program.memoryContract callerCtx callerState callerLocals
        callerPlan callerLive callerFrameBase .stack source target)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hCallee :
      ∀ {targetEntry : Structured.ObserverSemantics.State transcript},
        ActivationCalleeEntryRel
            program.memoryContract prepared.plan []
            artifact.slots.params 0 .stack
            sourceBodyStart targetEntry →
        targetEntry.source.returns ≠ [] →
        targetEntry.source.evm.stack.length =
            artifact.entryCtx.layout.length →
        ∃ calleeFinal bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            artifact.lowerProc.toStructured.body targetEntry
            (Structured.EffectSemantics.Outcome.halt kind calleeFinal) ∧
          HaltStateRel program.memoryContract prepared.plan
            sourceFinal calleeFinal) :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.NonregularStmtForward
        program.memoryContract transcript callerPlan callerLive
        callerFrameBase .stack program sourceCtx
        (.call targets name args) source expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)
        sourceCtx := by
  obtain
      ⟨slotInfo, loweredArgs, callArgs, _stores, _release,
        argsCode, _releaseCode, hSlotLookup, hArgsLength,
        _hTargetsLength, _hTargetsNodup, hLowerArgs, hCallArgs,
        _hStores, _hRelease, hArgsCode, _hReleaseCode,
        hCompiledShape, hCallerState, hCallerLocals⟩ :=
    AllocationObserverCall.CallCompiler.components hLower hCompile
  subst callerFinalState
  subst callerFinalLocals
  obtain ⟨hRecipeEq, _hSlotsEq, _hFrameNameEq⟩ :=
    compilation.selected_agrees artifact
  have hArtifactSlotLookup :
      AllocationSupport.lookupFun? name callerCtx.functions =
        some artifact.slots := by
    rw [hCallerShared.functions, ← hRecipeEq]
    simpa [artifact.sourceName] using artifact.slotsLookup
  have hSlotInfo : slotInfo = artifact.slots := by
    rw [hArtifactSlotLookup] at hSlotLookup
    exact (Option.some.inj hSlotLookup).symm
  subst slotInfo
  have hSourceOrdinary :=
    AllocationObserverSafety.SafeSemantics.stmt_run_eq hSource
  have hArgsScoped :
      ∀ arg, arg ∈ args →
        Functions.Scope.ExprScoped callerLive arg :=
    hScoped.2.2
  have hParamLength :
      artifact.slots.params.length = fn.params.length := by
    simpa using congrArg List.length artifact.slotsMatch.2.1
  have hFrame :
      name ∉ callerCtx.frameFunctions := by
    intro hMem
    have hNeedsFrame :=
      (compilation.call_needsFrame_iff hCallerShared artifact).1 hMem
    simpa [hNoFrame] using hNeedsFrame
  have hCallArgsShape : callArgs = loweredArgs := by
    simpa [hFrame] using hCallArgs.symm
  subst callArgs
  obtain
      ⟨targetAfterArgs, _callerBase, hArgsRun, hArgsResult,
        _hCallerRel, hCallStack, _hCallerBaseStack⟩ :=
    AllocationObserverCall.PreparedArguments.stack_neutral
      hSafeArgs hArgsScoped hLowerArgs hArgsCode hInvariant
  let targetEntry :=
    AllocationObserverCall.CalleeEntry.structuredState
      targetAfterArgs argValues.reverse target.source.evm.stack
      artifact.lowerProc.retc
  have hEntry :
      ActivationCalleeEntryRel program.memoryContract prepared.plan []
        artifact.slots.params 0 .stack sourceBodyStart targetEntry := by
    rw [hBodyStart]
    have hArgsResult' :
        ActivationExprResultRel program.memoryContract callerPlan
          callerLive 0 callerFrameBase argValues.length .stack
          sourceAfterArgs target targetAfterArgs argValues := by
      simpa [hSafeArgs.values_length] using hArgsResult
    exact
      AllocationObserverCall.CalleeEntry.stack_of_arguments
        hArgsResult' hParamLookup
  have hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length := by
    change argValues.reverse.length = artifact.entryLayout.length
    simp [
      AllocationObserverCall.SelectedCallee.Artifact.entryLayout,
      hNoFrame, hArgsResult.valuesLength, hArgsLength,
      hParamLength]
  have hEntryReturnFrame : targetEntry.source.returns ≠ [] := by
    simp [targetEntry,
      AllocationObserverCall.CalleeEntry.structuredState,
      Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.withEVM, Structured.RunState.pushReturn]
  obtain ⟨calleeFinal, bodyFuel, hCalleeEval, hHaltRel⟩ :=
    hCallee hEntry hEntryReturnFrame hEntryStackLength
  have hCallArgsLength :
      argValues.reverse.length = artifact.lowerProc.argc := by
    rw [prepared.procArgc]
    simp [hNoFrame, hArgsResult.valuesLength, hArgsLength, hParamLength]
  have hCallEval :
      Structured.ObserverSemantics.Stmt.Eval expressions.toStructured
        (bodyFuel + 1) (.call name) targetAfterArgs
        (Structured.EffectSemantics.Outcome.halt kind calleeFinal) :=
    AllocationObserverCall.StructuredCall.halt
      artifact.targetLookup
      (by simpa using hCallStack)
      hCallArgsLength hCalleeEval
  have hCallerHaltRel :
      HaltStateRel program.memoryContract callerPlan
        sourceFinal calleeFinal :=
    ⟨hHaltRel.cursor, hHaltRel.shared⟩
  obtain ⟨targetFuel, hTargetEvalRaw⟩ :=
    eval_halt_phases hArgsRun hCallEval
  have hTargetEval :
      Structured.ObserverSemantics.Block.Eval expressions.toStructured
        targetFuel
        { stmts :=
            Expressions.StmtList.toStructured compiledStmts }
        target
        (Structured.EffectSemantics.Outcome.halt kind calleeFinal) := by
    rw [hCompiledShape,
      Expressions.StmtList.toStructured_append,
      Expressions.StmtList.toStructured_append,
      Expressions.StmtList.toStructured_append]
    simpa [Locals.codeStmt,
      Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTargetEvalRaw
  exact
    ⟨calleeFinal, sourceFuel, targetFuel, hSourceOrdinary, hTargetEval,
      by
        intro hMode
        change Locals.Source.Mode.halt kind = .regular at hMode
        contradiction,
      .halt kind hCallerHaltRel⟩

/--
Compose one selected source call after source semantics has exposed its
argument, callee-entry, return, and caller-writeback data.

The callee callback is for this one selected activation only. The forthcoming
source-fuel theorem constructs it recursively; it is not retained by any
public adjacent-pass theorem.
-/
theorem regular_of_selected
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {allocatorDepth sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {callerMode : ActivationMode}
    {source sourceAfterArgs sourceBodyStart sourceReturned sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {args : List (Functions.Expr 1)}
    {argValues returnValues : List Word}
    {bodyStore returnStore : Locals.Source.Store}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {bodyMode : AllocationObserverCall.StructuredCall.ReturnMode}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx))
    (hSafeArgs :
      AllocationObserverSafety.ArgList.MemorySafeEval
        program.memoryContract transcript args source sourceAfterArgs
        argValues)
    (hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst)
          bodyStore =
        some argValues)
    (hBodyStart :
      sourceBodyStart =
        (Functions.ObserverSemantics.stateModel transcript).withSource
          sourceAfterArgs
          { shared := sourceAfterArgs.source.shared
            vars := bodyStore })
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.source.vars =
        some returnStore)
    (hFinal :
      sourceFinal =
        (Functions.ObserverSemantics.stateModel transcript).withSource
          sourceReturned
          { shared := sourceReturned.source.shared
            vars := returnStore })
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive
        (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth callerCtx callerState
        callerLocals callerPlan callerLive callerFrameBase callerMode
        source target)
    (hBudget : Frame.Budget config allocatorDepth)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hCallee :
      ∀ {targetEntry : Structured.ObserverSemantics.State transcript}
        {calleeDepth calleeFrameBase : Nat},
        ActivationCalleeEntryRel
            program.memoryContract prepared.plan []
            artifact.slots.params calleeFrameBase prepared.mode
            sourceBodyStart targetEntry →
        targetEntry.source.returns ≠ [] →
        targetEntry.source.evm.stack.length =
            artifact.entryCtx.layout.length →
        Frame.AllocatorReady config calleeDepth targetEntry →
        Frame.ActivationOwned config calleeDepth calleeFrameBase
            prepared.mode →
        AllocationObserverCall.RegularCallee.protectedBound
            calleeDepth prepared.mode =
          allocatorDepth + 1 →
        ∃ calleeFinal bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            artifact.lowerProc.toStructured.body targetEntry
            (bodyMode.outcome calleeFinal) ∧
          calleeFinal.source.evm.stack = returnValues.reverse ∧
          sourceReturned.cursor = calleeFinal.cursor ∧
          Compiler.MemoryRelation.MachineRel program.memoryContract
            sourceReturned.source.shared.toMachineState
            calleeFinal.source.evm.toMachineState ∧
          sourceReturned.source.shared.toState =
            calleeFinal.source.evm.toSharedState.toState ∧
          Frame.BoundedEffect config calleeDepth (allocatorDepth + 1)
            targetEntry calleeFinal) :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        callerCtx callerFinalState callerFinalLocals callerPlan callerLive
        callerFrameBase callerMode callerMode program sourceCtx
        (.call targets name args) source expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceFinal targetFinal sourceCtx := by
  obtain
      ⟨slotInfo, loweredArgs, callArgs, stores, release,
        argsCode, releaseCode, hSlotLookup, hArgsLength,
        hTargetsLength, hTargetsNodup, hLowerArgs, hCallArgs,
        hStores, hRelease, hArgsCode, hReleaseCode,
        hCompiledShape, hCallerState, hCallerLocals⟩ :=
    AllocationObserverCall.CallCompiler.components hLower hCompile
  subst callerFinalState
  subst callerFinalLocals
  obtain ⟨hRecipeEq, _hSlotsEq, _hFrameNameEq⟩ :=
    compilation.selected_agrees artifact
  have hArtifactSlotLookup :
      AllocationSupport.lookupFun? name callerCtx.functions =
        some artifact.slots := by
    rw [hCallerShared.functions, ← hRecipeEq]
    simpa [artifact.sourceName] using artifact.slotsLookup
  have hSlotInfo : slotInfo = artifact.slots := by
    rw [hArtifactSlotLookup] at hSlotLookup
    exact (Option.some.inj hSlotLookup).symm
  subst slotInfo
  have hArtifactConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config := by
    obtain ⟨hRecipe, _hSlots, _hFrameName⟩ :=
      compilation.selected_agrees artifact
    simpa [hRecipe] using hConfig
  have hSourceOrdinary :=
    AllocationObserverSafety.SafeSemantics.stmt_run_eq hSource
  have hArgsScoped :
      ∀ arg, arg ∈ args →
        Functions.Scope.ExprScoped callerLive arg :=
    hScoped.2.2
  have hTargetsLive :
      ∀ targetName, targetName ∈ targets →
        targetName ∈ callerLive :=
    hScoped.2.1
  have hReturnLength :
      returnValues.length = artifact.lowerProc.retc := by
    rw [prepared.procRetc]
    calc
      returnValues.length = targets.length :=
        Functions.Source.Store.assignMany_length hAssign
      _ = artifact.slots.returns.length := hTargetsLength
      _ = (artifact.slots.returns.map Prod.fst).length := by simp
      _ = fn.returns.length :=
        congrArg List.length artifact.slotsMatch.2.2
  have hParamLength :
      artifact.slots.params.length = fn.params.length := by
    simpa using congrArg List.length artifact.slotsMatch.2.1
  have hCallerStackLength :
      target.source.evm.stack.length = callerLocals.layout.length :=
    hInvariant.activation.stackLength
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hFrame :
        name ∈ callerCtx.frameFunctions :=
      (compilation.call_needsFrame_iff hCallerShared artifact).2 hNeedsFrame
    have hCallerFrameConfig :
        callerCtx.frameConfig? = some config := by
      rw [hCallerShared.frameConfig]
      simpa [Compilation.frameConfig?] using hConfig
    have hCallArgsShape :
        callArgs =
          AllocationLowering.frameExpr config :: loweredArgs := by
      simpa [hFrame, hCallerFrameConfig] using hCallArgs.symm
    subst callArgs
    obtain ⟨ordinaryArgsCode, hOrdinaryArgsCode, hArgsCodeShape⟩ :=
      AllocationLowering.frameExpr_cons_compileCode_components hArgsCode
    have hPositive :
        0 < config.frameWords :=
      compilation.selected_config_frameWords_pos artifact hConfig hNeedsFrame
    obtain
        ⟨targetAfterAcquire, targetAfterArgs, callerBase,
          hAcquireRun, hOrdinaryArgsRun, hArgsResult, hCallerRel,
          hCallStack, hCallerBaseStack, hCallerBaseMachine,
          hAcquireStack,
          hFrameActive, hFrameAllocated, hGrowth, hArgsEffect⟩ :=
      AllocationObserverCall.PreparedArguments.scratch
        hConfig hPositive hBudget hSafeArgs hArgsScoped hLowerArgs
        hOrdinaryArgsCode hInvariant
    have hArgsRun :
        Structured.ObserverSemantics.Code.run argsCode target =
          .ok targetAfterArgs := by
      rw [hArgsCodeShape,
        Structured.ObserverSemantics.Code.run_append]
      rw [hAcquireRun]
      exact hOrdinaryArgsRun
    let callVector :=
      argValues.reverse ++
        [EvmYul.UInt256.ofNat
          (Frame.baseAt config allocatorDepth)]
    let targetEntry :=
      AllocationObserverCall.CalleeEntry.structuredState
        targetAfterArgs callVector target.source.evm.stack
        artifact.lowerProc.retc
    have hEntry :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params
          (Frame.baseAt config allocatorDepth)
          (.scratch 0 config.frameWords)
          sourceBodyStart targetEntry := by
      rw [hBodyStart]
      have hArgsResult' :
          ActivationExprResultRel program.memoryContract callerPlan
            callerLive 1 callerFrameBase argValues.length callerMode
            sourceAfterArgs targetAfterAcquire targetAfterArgs argValues := by
        simpa [hSafeArgs.values_length] using hArgsResult
      apply AllocationObserverCall.CalleeEntry.scratch_of_arguments
        hConfig hBudget hArgsResult' hAcquireStack
          hFrameActive hFrameAllocated hGrowth hParamLookup
    have hPreparedMode :
        prepared.mode = .scratch 0 config.frameWords := by
      rw [prepared.mode_eq_scratch_of_needsFrame hNeedsFrame]
      obtain
          ⟨_reservation, _hReservation, _hAllocator, _hFirst, _hLimit,
            hWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hArtifactConfig
      rw [hWords]
    have hEntry' :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params
          (Frame.baseAt config allocatorDepth) prepared.mode
          sourceBodyStart targetEntry := by
      simpa [hPreparedMode] using hEntry
    have hEntryStackLength :
        targetEntry.source.evm.stack.length =
          artifact.entryCtx.layout.length := by
      change callVector.length = artifact.entryLayout.length
      simp [callVector,
        AllocationObserverCall.SelectedCallee.Artifact.entryLayout,
        hNeedsFrame, hArgsResult.valuesLength, hArgsLength,
        hParamLength]
    have hEntryReturnFrame : targetEntry.source.returns ≠ [] := by
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryReady :
        Frame.AllocatorReady config (allocatorDepth + 1) targetEntry := by
      apply hArgsEffect.ready.of_machine_eq
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryOwned :
        Frame.ActivationOwned config (allocatorDepth + 1)
          (Frame.baseAt config allocatorDepth) prepared.mode := by
      rw [hPreparedMode]
      exact .scratch rfl rfl
    have hProtectedBound :
        AllocationObserverCall.RegularCallee.protectedBound
            (allocatorDepth + 1) prepared.mode =
          allocatorDepth + 1 := by
      simp [hPreparedMode,
        AllocationObserverCall.RegularCallee.protectedBound]
    obtain
        ⟨calleeFinal, bodyFuel, hCalleeEval, hReturnedStack,
          hCursor, hMachine, hWorld, hCalleeEffect⟩ :=
      hCallee hEntry' hEntryReturnFrame hEntryStackLength hEntryReady hEntryOwned
        hProtectedBound
    have hCallerReady :
        Frame.AllocatorReady config (allocatorDepth + 1) callerBase := by
      apply hArgsEffect.ready.of_machine_eq
      exact hCallerBaseMachine
    have hEntryMachine :
        targetEntry.source.evm.toMachineState =
          callerBase.source.evm.toMachineState := by
      calc
        targetEntry.source.evm.toMachineState =
            targetAfterArgs.source.evm.toMachineState := by
          simp [targetEntry,
            AllocationObserverCall.CalleeEntry.structuredState,
            Structured.ObserverSemantics.stateModel,
            Structured.EffectSemantics.StateModel.withEVM,
            Structured.RunState.withEVM, Structured.RunState.pushReturn]
        _ = callerBase.source.evm.toMachineState :=
          hCallerBaseMachine.symm
    have hEntryEffect :
        Frame.BoundedEffect config (allocatorDepth + 1)
          (allocatorDepth + 1) callerBase targetEntry :=
      Frame.BoundedEffect.of_machine_eq hCallerReady hEntryMachine
    have hCallEffect :
        Frame.BoundedEffect config (allocatorDepth + 1)
          (allocatorDepth + 1) callerBase calleeFinal :=
      hEntryEffect.trans hCalleeEffect
    obtain
        ⟨callFinal, targetAssigned, hCallEval, hStoresRun,
          hAssignedRel, hAssignedStackLength, hAssignedEffect⟩ :=
      AllocationObserverCall.RegularCall.resume_and_writeback
        hConfig hCallerRel hInvariant.frame (by omega) hBudget
        hCallerBaseStack artifact.targetLookup
        (by simpa [callVector] using hCallStack)
        (by
          change callVector.length = artifact.lowerProc.argc
          rw [prepared.procArgc]
          simp [callVector, hNeedsFrame, hArgsResult.valuesLength,
            hArgsLength, hParamLength])
        hCalleeEval hReturnedStack hReturnLength hCursor hMachine hWorld
        hCallEffect hInvariant.activation.compiler
        hInvariant.activation.planWF hTargetsLive hTargetsNodup
        hAssign hStores
    have hAssignedDefined :
        LiveDefined callerLive
          ((Functions.ObserverSemantics.stateModel transcript).withSource
            sourceReturned
            { shared := sourceReturned.source.shared
              vars := returnStore }).source := by
      have hAfterArgsDefined :
          LiveDefined callerLive sourceAfterArgs.source :=
        hInvariant.activation.defined.congr_vars hSafeArgs.vars_eq
      simpa [Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.withSource,
        Locals.Source.State.withVars] using
        hAfterArgsDefined.assignMany_preserves hAssign
    have hAssignedInvariant :
        AllocationObserverContext.ActivationInvariant
          program.memoryContract callerCtx callerState callerLocals
          callerPlan callerLive callerFrameBase callerMode sourceFinal
          targetAssigned := by
      refine
        { compiler := hInvariant.activation.compiler
          planWF := hInvariant.activation.planWF
          defined := ?_
          state := ?_
          stackLength := ?_ }
      · simpa [hFinal] using hAssignedDefined
      · simpa [hFinal] using hAssignedRel
      · exact hAssignedStackLength.trans hCallerStackLength
    have hWholeAssignedEffect :
        Frame.BoundedEffect config (allocatorDepth + 1)
          (AllocationObserverCall.CallTargets.protectedBound
            allocatorDepth callerMode)
          target targetAssigned := by
      have hArgsToBase :
          Frame.BoundedEffect config (allocatorDepth + 1)
            (allocatorDepth + 1) target callerBase := by
        exact
          hArgsEffect.trans
            (Frame.BoundedEffect.of_machine_eq hArgsEffect.ready
              hCallerBaseMachine)
      have hBound :
          AllocationObserverCall.CallTargets.protectedBound
              allocatorDepth callerMode ≤
            allocatorDepth + 1 := by
        cases callerMode <;>
          simp [AllocationObserverCall.CallTargets.protectedBound]
      exact
        (Frame.BoundedEffect.weaken hBound hArgsToBase).trans
          hAssignedEffect
    have hReleaseShape :
        release =
          [.expr
            (Locals.Expr.code (results := 0)
              (AllocationSupport.scratchFrameReleaseCode config))] := by
      simpa [hFrame, hCallerFrameConfig] using hRelease.symm
    subst release
    have hReleaseCodeShape :
        releaseCode =
          Locals.codeStmt
            (AllocationSupport.scratchFrameReleaseCode config) := by
      have hSingle :=
        Locals.Block.compileOpen_single_components hReleaseCode
      simpa [Locals.Stmt.compile, Locals.Expr.compileCode] using hSingle.symm
    obtain
        ⟨targetFinal, hReleaseRun, hFinalInvariant, hFinalEffect⟩ :=
      AllocationObserverCall.RegularCall.complete_with_release
        hConfig hBudget hAssignedInvariant hInvariant.frame
        hWholeAssignedEffect
    have hReleaseEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured 2
          { stmts :=
              Expressions.StmtList.toStructured releaseCode }
          targetAssigned
          (Structured.EffectSemantics.Outcome.regular targetFinal) := by
      rw [hReleaseCodeShape]
      exact
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hReleaseRun)
          Structured.EffectSemantics.Block.Eval.nil
    obtain ⟨targetFuel, hTargetEvalRaw⟩ :=
      eval_phases hArgsRun hCallEval hStoresRun
        (by
          simpa [hReleaseCodeShape,
            Expressions.StmtList.toStructured,
            Expressions.Stmt.toStructured] using hReleaseEval)
    have hTargetEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured
          targetFuel
          { stmts :=
              Expressions.StmtList.toStructured compiledStmts }
          target
          (Structured.EffectSemantics.Outcome.regular targetFinal) := by
      rw [hCompiledShape,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append]
      simpa [Locals.codeStmt,
        Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured,
        hReleaseCodeShape] using hTargetEvalRaw
    exact
      ⟨targetFinal, sourceFuel, targetFuel, hSourceOrdinary, hTargetEval,
        hFinalInvariant, SameFrame.refl callerMode, hFinalEffect⟩
  · have hNoFrame : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hFrame :
        name ∉ callerCtx.frameFunctions := by
      intro hMem
      exact hNeedsFrame
        ((compilation.call_needsFrame_iff hCallerShared artifact).1 hMem)
    have hCallArgsShape : callArgs = loweredArgs := by
      simpa [hFrame] using hCallArgs.symm
    subst callArgs
    obtain
        ⟨targetAfterArgs, callerBase, hArgsRun, hArgsResult,
          hCallerRel, hCallStack, hCallerBaseStack,
          hCallerBaseMachine, hArgsEffect⟩ :=
      AllocationObserverCall.PreparedArguments.stack
        hConfig hSafeArgs hArgsScoped hLowerArgs hArgsCode hInvariant
    let targetEntry :=
      AllocationObserverCall.CalleeEntry.structuredState
        targetAfterArgs argValues.reverse target.source.evm.stack
        artifact.lowerProc.retc
    have hEntry :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params 0 .stack sourceBodyStart targetEntry := by
      rw [hBodyStart]
      have hArgsResult' :
          ActivationExprResultRel program.memoryContract callerPlan
            callerLive 0 callerFrameBase argValues.length callerMode
            sourceAfterArgs target targetAfterArgs argValues := by
        simpa [hSafeArgs.values_length] using hArgsResult
      exact
        AllocationObserverCall.CalleeEntry.stack_of_arguments
          hArgsResult' hParamLookup
    have hPreparedMode : prepared.mode = .stack :=
      prepared.mode_eq_stack_of_noFrame hNoFrame
    have hEntry' :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params 0 prepared.mode sourceBodyStart
          targetEntry := by
      simpa [hPreparedMode] using hEntry
    have hEntryStackLength :
        targetEntry.source.evm.stack.length =
          artifact.entryCtx.layout.length := by
      change argValues.reverse.length = artifact.entryLayout.length
      simp [
        AllocationObserverCall.SelectedCallee.Artifact.entryLayout,
        hNoFrame, hArgsResult.valuesLength, hArgsLength,
        hParamLength]
    have hEntryReturnFrame : targetEntry.source.returns ≠ [] := by
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryReady :
        Frame.AllocatorReady config allocatorDepth targetEntry := by
      apply hArgsEffect.ready.of_machine_eq
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryOwned :
        Frame.ActivationOwned config allocatorDepth 0 prepared.mode := by
      rw [hPreparedMode]
      exact .stack
    have hProtectedBound :
        AllocationObserverCall.RegularCallee.protectedBound
            allocatorDepth prepared.mode =
          allocatorDepth + 1 := by
      simp [hPreparedMode,
        AllocationObserverCall.RegularCallee.protectedBound]
    obtain
        ⟨calleeFinal, bodyFuel, hCalleeEval, hReturnedStack,
          hCursor, hMachine, hWorld, hCalleeEffect⟩ :=
      hCallee hEntry' hEntryReturnFrame hEntryStackLength hEntryReady hEntryOwned
        hProtectedBound
    have hCallerReady :
        Frame.AllocatorReady config allocatorDepth callerBase := by
      apply hArgsEffect.ready.of_machine_eq
      exact hCallerBaseMachine
    have hEntryMachine :
        targetEntry.source.evm.toMachineState =
          callerBase.source.evm.toMachineState := by
      calc
        targetEntry.source.evm.toMachineState =
            targetAfterArgs.source.evm.toMachineState := by
          simp [targetEntry,
            AllocationObserverCall.CalleeEntry.structuredState,
            Structured.ObserverSemantics.stateModel,
            Structured.EffectSemantics.StateModel.withEVM,
            Structured.RunState.withEVM, Structured.RunState.pushReturn]
        _ = callerBase.source.evm.toMachineState :=
          hCallerBaseMachine.symm
    have hEntryEffect :
        Frame.BoundedEffect config allocatorDepth (allocatorDepth + 1)
          callerBase targetEntry :=
      Frame.BoundedEffect.of_machine_eq hCallerReady hEntryMachine
    have hCallEffect :
        Frame.BoundedEffect config allocatorDepth (allocatorDepth + 1)
          callerBase calleeFinal :=
      hEntryEffect.trans hCalleeEffect
    obtain
        ⟨callFinal, targetAssigned, hCallEval, hStoresRun,
          hAssignedRel, hAssignedStackLength, hAssignedEffect⟩ :=
      AllocationObserverCall.RegularCall.resume_and_writeback
        hConfig hCallerRel hInvariant.frame (by omega) hBudget
        hCallerBaseStack artifact.targetLookup
        (by simpa using hCallStack)
        (by
          change argValues.reverse.length = artifact.lowerProc.argc
          rw [prepared.procArgc]
          simp [hNoFrame, hArgsResult.valuesLength,
            hArgsLength, hParamLength])
        hCalleeEval hReturnedStack hReturnLength hCursor hMachine hWorld
        hCallEffect hInvariant.activation.compiler
        hInvariant.activation.planWF hTargetsLive hTargetsNodup
        hAssign hStores
    have hAssignedDefined :
        LiveDefined callerLive
          ((Functions.ObserverSemantics.stateModel transcript).withSource
            sourceReturned
            { shared := sourceReturned.source.shared
              vars := returnStore }).source := by
      have hAfterArgsDefined :
          LiveDefined callerLive sourceAfterArgs.source :=
        hInvariant.activation.defined.congr_vars hSafeArgs.vars_eq
      simpa [Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.withSource,
        Locals.Source.State.withVars] using
        hAfterArgsDefined.assignMany_preserves hAssign
    have hAssignedInvariant :
        AllocationObserverContext.ActivationInvariant
          program.memoryContract callerCtx callerState callerLocals
          callerPlan callerLive callerFrameBase callerMode sourceFinal
          targetAssigned := by
      refine
        { compiler := hInvariant.activation.compiler
          planWF := hInvariant.activation.planWF
          defined := ?_
          state := ?_
          stackLength := ?_ }
      · simpa [hFinal] using hAssignedDefined
      · simpa [hFinal] using hAssignedRel
      · exact hAssignedStackLength.trans hCallerStackLength
    have hArgsToBase :
        Frame.BoundedEffect config allocatorDepth (allocatorDepth + 1)
          target callerBase :=
      hArgsEffect.trans
        (Frame.BoundedEffect.of_machine_eq hArgsEffect.ready
          hCallerBaseMachine)
    have hBound :
        AllocationObserverCall.CallTargets.protectedBound
            allocatorDepth callerMode ≤
          allocatorDepth + 1 := by
      cases callerMode <;>
        simp [AllocationObserverCall.CallTargets.protectedBound]
    have hWholeAssignedEffect :
        Frame.BoundedEffect config allocatorDepth
          (AllocationObserverCall.CallTargets.protectedBound
            allocatorDepth callerMode)
          target targetAssigned :=
      (Frame.BoundedEffect.weaken hBound hArgsToBase).trans
        hAssignedEffect
    obtain ⟨hFinalInvariant, hFinalEffect⟩ :=
      AllocationObserverCall.RegularCall.complete_without_release
        hAssignedInvariant hInvariant.frame hWholeAssignedEffect
    have hReleaseShape : release = [] := by
      simpa [hFrame] using hRelease.symm
    subst release
    have hReleaseCodeShape : releaseCode = [] := by
      simpa [Locals.Block.compileOpen] using
        hReleaseCode
    have hReleaseEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured 1
          { stmts := Expressions.StmtList.toStructured releaseCode }
          targetAssigned
          (Structured.EffectSemantics.Outcome.regular targetAssigned) := by
      rw [hReleaseCodeShape]
      exact Structured.EffectSemantics.Block.Eval.nil
    obtain ⟨targetFuel, hTargetEvalRaw⟩ :=
      eval_phases hArgsRun hCallEval hStoresRun
        (by simpa [hReleaseCodeShape] using hReleaseEval)
    have hTargetEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured
          targetFuel
          { stmts :=
              Expressions.StmtList.toStructured compiledStmts }
          target
          (Structured.EffectSemantics.Outcome.regular targetAssigned) := by
      rw [hCompiledShape,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append]
      simpa [Locals.codeStmt,
        Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured,
        hReleaseCodeShape] using hTargetEvalRaw
    exact
      ⟨targetAssigned, sourceFuel, targetFuel, hSourceOrdinary,
        hTargetEval, hFinalInvariant, SameFrame.refl callerMode,
        hFinalEffect⟩

/--
Compose one compiler-selected source call whose callee halts.

The generated caller writeback and optional scratch-frame release are
unreachable. The result therefore retains the exact terminal shared-state
relation and protects the caller-owned allocator prefix while allowing the
allocator to remain ready at the deepest terminal callee.
-/
theorem halt_of_selected
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {allocatorDepth sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {callerMode : ActivationMode}
    {source sourceAfterArgs sourceBodyStart sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {args : List (Functions.Expr 1)}
    {argValues : List Word}
    {bodyStore : Locals.Source.Store}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {kind : Assembly.HaltKind}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            sourceCtx))
    (hSafeArgs :
      AllocationObserverSafety.ArgList.MemorySafeEval
        program.memoryContract transcript args source sourceAfterArgs
        argValues)
    (hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst)
          bodyStore =
        some argValues)
    (hBodyStart :
      sourceBodyStart =
        (Functions.ObserverSemantics.stateModel transcript).withSource
          sourceAfterArgs
          { shared := sourceAfterArgs.source.shared
            vars := bodyStore })
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive
        (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth callerCtx callerState
        callerLocals callerPlan callerLive callerFrameBase callerMode
        source target)
    (hBudget : Frame.Budget config allocatorDepth)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hCallee :
      ∀ {targetEntry : Structured.ObserverSemantics.State transcript}
        {calleeDepth calleeFrameBase : Nat},
        ActivationCalleeEntryRel
            program.memoryContract prepared.plan []
            artifact.slots.params calleeFrameBase prepared.mode
            sourceBodyStart targetEntry →
        targetEntry.source.returns ≠ [] →
        targetEntry.source.evm.stack.length =
            artifact.entryCtx.layout.length →
        Frame.AllocatorReady config calleeDepth targetEntry →
        Frame.ActivationOwned config calleeDepth calleeFrameBase
            prepared.mode →
        AllocationObserverCall.RegularCallee.protectedBound
            calleeDepth prepared.mode =
          allocatorDepth + 1 →
        ∃ calleeFinal bodyFuel finalDepth,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            artifact.lowerProc.toStructured.body targetEntry
            (Structured.EffectSemantics.Outcome.halt kind calleeFinal) ∧
          HaltStateRel program.memoryContract prepared.plan
            sourceFinal calleeFinal ∧
          Frame.BoundedEffect config finalDepth (allocatorDepth + 1)
            targetEntry calleeFinal) :
    ∃ targetFinal,
      AllocationObserverOutcome.NonregularStmtRuntimeForward
        program.memoryContract config allocatorDepth transcript
        callerPlan callerLive callerFrameBase callerMode callerMode
        program sourceCtx (.call targets name args) source
        expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)
        sourceCtx := by
  obtain
      ⟨slotInfo, loweredArgs, callArgs, stores, release,
        argsCode, releaseCode, hSlotLookup, hArgsLength,
        _hTargetsLength, _hTargetsNodup, hLowerArgs, hCallArgs,
        _hStores, _hRelease, hArgsCode, _hReleaseCode,
        hCompiledShape, hCallerState, hCallerLocals⟩ :=
    AllocationObserverCall.CallCompiler.components hLower hCompile
  subst callerFinalState
  subst callerFinalLocals
  obtain ⟨hRecipeEq, _hSlotsEq, _hFrameNameEq⟩ :=
    compilation.selected_agrees artifact
  have hArtifactSlotLookup :
      AllocationSupport.lookupFun? name callerCtx.functions =
        some artifact.slots := by
    rw [hCallerShared.functions, ← hRecipeEq]
    simpa [artifact.sourceName] using artifact.slotsLookup
  have hSlotInfo : slotInfo = artifact.slots := by
    rw [hArtifactSlotLookup] at hSlotLookup
    exact (Option.some.inj hSlotLookup).symm
  subst slotInfo
  have hArtifactConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config := by
    obtain ⟨hRecipe, _hSlots, _hFrameName⟩ :=
      compilation.selected_agrees artifact
    simpa [hRecipe] using hConfig
  have hSourceOrdinary :=
    AllocationObserverSafety.SafeSemantics.stmt_run_eq hSource
  have hArgsScoped :
      ∀ arg, arg ∈ args →
        Functions.Scope.ExprScoped callerLive arg :=
    hScoped.2.2
  have hParamLength :
      artifact.slots.params.length = fn.params.length := by
    simpa using congrArg List.length artifact.slotsMatch.2.1
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hFrame :
        name ∈ callerCtx.frameFunctions :=
      (compilation.call_needsFrame_iff hCallerShared artifact).2 hNeedsFrame
    have hCallerFrameConfig :
        callerCtx.frameConfig? = some config := by
      rw [hCallerShared.frameConfig]
      simpa [Compilation.frameConfig?] using hConfig
    have hCallArgsShape :
        callArgs =
          AllocationLowering.frameExpr config :: loweredArgs := by
      simpa [hFrame, hCallerFrameConfig] using hCallArgs.symm
    subst callArgs
    obtain ⟨ordinaryArgsCode, hOrdinaryArgsCode, hArgsCodeShape⟩ :=
      AllocationLowering.frameExpr_cons_compileCode_components hArgsCode
    have hPositive :
        0 < config.frameWords :=
      compilation.selected_config_frameWords_pos artifact hConfig hNeedsFrame
    obtain
        ⟨targetAfterAcquire, targetAfterArgs, _callerBase,
          hAcquireRun, hOrdinaryArgsRun, hArgsResult, _hCallerRel,
          hCallStack, _hCallerBaseStack, _hCallerBaseMachine,
          hAcquireStack, hFrameActive, hFrameAllocated, hGrowth,
          hArgsEffect⟩ :=
      AllocationObserverCall.PreparedArguments.scratch
        hConfig hPositive hBudget hSafeArgs hArgsScoped hLowerArgs
        hOrdinaryArgsCode hInvariant
    have hArgsRun :
        Structured.ObserverSemantics.Code.run argsCode target =
          .ok targetAfterArgs := by
      rw [hArgsCodeShape,
        Structured.ObserverSemantics.Code.run_append]
      rw [hAcquireRun]
      exact hOrdinaryArgsRun
    let callVector :=
      argValues.reverse ++
        [EvmYul.UInt256.ofNat
          (Frame.baseAt config allocatorDepth)]
    let targetEntry :=
      AllocationObserverCall.CalleeEntry.structuredState
        targetAfterArgs callVector target.source.evm.stack
        artifact.lowerProc.retc
    have hEntry :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params
          (Frame.baseAt config allocatorDepth)
          (.scratch 0 config.frameWords)
          sourceBodyStart targetEntry := by
      rw [hBodyStart]
      have hArgsResult' :
          ActivationExprResultRel program.memoryContract callerPlan
            callerLive 1 callerFrameBase argValues.length callerMode
            sourceAfterArgs targetAfterAcquire targetAfterArgs argValues := by
        simpa [hSafeArgs.values_length] using hArgsResult
      apply AllocationObserverCall.CalleeEntry.scratch_of_arguments
        hConfig hBudget hArgsResult' hAcquireStack
          hFrameActive hFrameAllocated hGrowth hParamLookup
    have hPreparedMode :
        prepared.mode = .scratch 0 config.frameWords := by
      rw [prepared.mode_eq_scratch_of_needsFrame hNeedsFrame]
      obtain
          ⟨_reservation, _hReservation, _hAllocator, _hFirst, _hLimit,
            hWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hArtifactConfig
      rw [hWords]
    have hEntry' :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params
          (Frame.baseAt config allocatorDepth) prepared.mode
          sourceBodyStart targetEntry := by
      simpa [hPreparedMode] using hEntry
    have hEntryStackLength :
        targetEntry.source.evm.stack.length =
          artifact.entryCtx.layout.length := by
      change callVector.length = artifact.entryLayout.length
      simp [callVector,
        AllocationObserverCall.SelectedCallee.Artifact.entryLayout,
        hNeedsFrame, hArgsResult.valuesLength, hArgsLength,
        hParamLength]
    have hEntryReturnFrame : targetEntry.source.returns ≠ [] := by
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryReady :
        Frame.AllocatorReady config (allocatorDepth + 1) targetEntry := by
      apply hArgsEffect.ready.of_machine_eq
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryOwned :
        Frame.ActivationOwned config (allocatorDepth + 1)
          (Frame.baseAt config allocatorDepth) prepared.mode := by
      rw [hPreparedMode]
      exact .scratch rfl rfl
    have hProtectedBound :
        AllocationObserverCall.RegularCallee.protectedBound
            (allocatorDepth + 1) prepared.mode =
          allocatorDepth + 1 := by
      simp [hPreparedMode,
        AllocationObserverCall.RegularCallee.protectedBound]
    obtain
        ⟨calleeFinal, bodyFuel, finalDepth, hCalleeEval,
          hHaltRel, hCalleeEffect⟩ :=
      hCallee hEntry' hEntryReturnFrame hEntryStackLength hEntryReady hEntryOwned
        hProtectedBound
    have hCallArgsLength :
        callVector.length = artifact.lowerProc.argc := by
      rw [prepared.procArgc]
      simp [callVector, hNeedsFrame, hArgsResult.valuesLength, hArgsLength,
        hParamLength]
    have hCallEval :
        Structured.ObserverSemantics.Stmt.Eval expressions.toStructured
          (bodyFuel + 1) (.call name) targetAfterArgs
          (Structured.EffectSemantics.Outcome.halt kind calleeFinal) :=
      AllocationObserverCall.StructuredCall.halt
        artifact.targetLookup
        (by simpa [callVector] using hCallStack)
        hCallArgsLength hCalleeEval
    have hEntryMachine :
        targetEntry.source.evm.toMachineState =
          targetAfterArgs.source.evm.toMachineState := by
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryEffect :
        Frame.BoundedEffect config (allocatorDepth + 1)
          (allocatorDepth + 1) targetAfterArgs targetEntry :=
      Frame.BoundedEffect.of_machine_eq hArgsEffect.ready hEntryMachine
    have hThroughCall :
        Frame.BoundedEffect config finalDepth (allocatorDepth + 1)
          target calleeFinal :=
      hArgsEffect.trans (hEntryEffect.trans hCalleeEffect)
    have hBound :
        Frame.activationProtectedBound allocatorDepth callerMode ≤
          allocatorDepth + 1 := by
      cases callerMode <;>
        simp [Frame.activationProtectedBound]
    have hWholeEffect :
        Frame.BoundedEffect config finalDepth
          (Frame.activationProtectedBound allocatorDepth callerMode)
          target calleeFinal :=
      Frame.BoundedEffect.weaken hBound hThroughCall
    have hCallerHaltRel :
        HaltStateRel program.memoryContract callerPlan
          sourceFinal calleeFinal :=
      ⟨hHaltRel.cursor, hHaltRel.shared⟩
    obtain ⟨targetFuel, hTargetEvalRaw⟩ :=
      eval_halt_phases hArgsRun hCallEval
    have hTargetEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured
          targetFuel
          { stmts :=
              Expressions.StmtList.toStructured compiledStmts }
          target
          (Structured.EffectSemantics.Outcome.halt kind calleeFinal) := by
      rw [hCompiledShape,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append]
      simpa [Locals.codeStmt,
        Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] using hTargetEvalRaw
    exact
      ⟨calleeFinal, sourceFuel, targetFuel, hSourceOrdinary, hTargetEval,
        by
          intro hMode
          change Locals.Source.Mode.halt kind = .regular at hMode
          contradiction,
        .halt kind hCallerHaltRel, SameFrame.refl callerMode,
        Frame.OutcomeEffect.halt_of_bounded hWholeEffect⟩
  · have hNoFrame : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hFrame :
        name ∉ callerCtx.frameFunctions := by
      intro hMem
      exact hNeedsFrame
        ((compilation.call_needsFrame_iff hCallerShared artifact).1 hMem)
    have hCallArgsShape : callArgs = loweredArgs := by
      simpa [hFrame] using hCallArgs.symm
    subst callArgs
    obtain
        ⟨targetAfterArgs, _callerBase, hArgsRun, hArgsResult,
          _hCallerRel, hCallStack, _hCallerBaseStack,
          _hCallerBaseMachine, hArgsEffect⟩ :=
      AllocationObserverCall.PreparedArguments.stack
        hConfig hSafeArgs hArgsScoped hLowerArgs hArgsCode hInvariant
    let targetEntry :=
      AllocationObserverCall.CalleeEntry.structuredState
        targetAfterArgs argValues.reverse target.source.evm.stack
        artifact.lowerProc.retc
    have hEntry :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params 0 .stack sourceBodyStart targetEntry := by
      rw [hBodyStart]
      have hArgsResult' :
          ActivationExprResultRel program.memoryContract callerPlan
            callerLive 0 callerFrameBase argValues.length callerMode
            sourceAfterArgs target targetAfterArgs argValues := by
        simpa [hSafeArgs.values_length] using hArgsResult
      exact
        AllocationObserverCall.CalleeEntry.stack_of_arguments
          hArgsResult' hParamLookup
    have hPreparedMode : prepared.mode = .stack :=
      prepared.mode_eq_stack_of_noFrame hNoFrame
    have hEntry' :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params 0 prepared.mode sourceBodyStart
          targetEntry := by
      simpa [hPreparedMode] using hEntry
    have hEntryStackLength :
        targetEntry.source.evm.stack.length =
          artifact.entryCtx.layout.length := by
      change argValues.reverse.length = artifact.entryLayout.length
      simp [
        AllocationObserverCall.SelectedCallee.Artifact.entryLayout,
        hNoFrame, hArgsResult.valuesLength, hArgsLength,
        hParamLength]
    have hEntryReturnFrame : targetEntry.source.returns ≠ [] := by
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryReady :
        Frame.AllocatorReady config allocatorDepth targetEntry := by
      apply hArgsEffect.ready.of_machine_eq
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryOwned :
        Frame.ActivationOwned config allocatorDepth 0 prepared.mode := by
      rw [hPreparedMode]
      exact .stack
    have hProtectedBound :
        AllocationObserverCall.RegularCallee.protectedBound
            allocatorDepth prepared.mode =
          allocatorDepth + 1 := by
      simp [hPreparedMode,
        AllocationObserverCall.RegularCallee.protectedBound]
    obtain
        ⟨calleeFinal, bodyFuel, finalDepth, hCalleeEval,
          hHaltRel, hCalleeEffect⟩ :=
      hCallee hEntry' hEntryReturnFrame hEntryStackLength hEntryReady hEntryOwned
        hProtectedBound
    have hCallArgsLength :
        argValues.reverse.length = artifact.lowerProc.argc := by
      rw [prepared.procArgc]
      simp [hNoFrame, hArgsResult.valuesLength, hArgsLength, hParamLength]
    have hCallEval :
        Structured.ObserverSemantics.Stmt.Eval expressions.toStructured
          (bodyFuel + 1) (.call name) targetAfterArgs
          (Structured.EffectSemantics.Outcome.halt kind calleeFinal) :=
      AllocationObserverCall.StructuredCall.halt
        artifact.targetLookup
        (by simpa using hCallStack)
        hCallArgsLength hCalleeEval
    have hEntryMachine :
        targetEntry.source.evm.toMachineState =
          targetAfterArgs.source.evm.toMachineState := by
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryEffect :
        Frame.BoundedEffect config allocatorDepth (allocatorDepth + 1)
          targetAfterArgs targetEntry :=
      Frame.BoundedEffect.of_machine_eq hArgsEffect.ready hEntryMachine
    have hThroughCall :
        Frame.BoundedEffect config finalDepth (allocatorDepth + 1)
          target calleeFinal :=
      hArgsEffect.trans (hEntryEffect.trans hCalleeEffect)
    have hBound :
        Frame.activationProtectedBound allocatorDepth callerMode ≤
          allocatorDepth + 1 := by
      cases callerMode <;>
        simp [Frame.activationProtectedBound]
    have hWholeEffect :
        Frame.BoundedEffect config finalDepth
          (Frame.activationProtectedBound allocatorDepth callerMode)
          target calleeFinal :=
      Frame.BoundedEffect.weaken hBound hThroughCall
    have hCallerHaltRel :
        HaltStateRel program.memoryContract callerPlan
          sourceFinal calleeFinal :=
      ⟨hHaltRel.cursor, hHaltRel.shared⟩
    obtain ⟨targetFuel, hTargetEvalRaw⟩ :=
      eval_halt_phases hArgsRun hCallEval
    have hTargetEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured
          targetFuel
          { stmts :=
              Expressions.StmtList.toStructured compiledStmts }
          target
          (Structured.EffectSemantics.Outcome.halt kind calleeFinal) := by
      rw [hCompiledShape,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append]
      simpa [Locals.codeStmt,
        Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] using hTargetEvalRaw
    exact
      ⟨calleeFinal, sourceFuel, targetFuel, hSourceOrdinary, hTargetEval,
        by
          intro hMode
          change Locals.Source.Mode.halt kind = .regular at hMode
          contradiction,
        .halt kind hCallerHaltRel, SameFrame.refl callerMode,
        Frame.OutcomeEffect.halt_of_bounded hWholeEffect⟩

/--
Lift a successful guarded source call through compiler-selected all-stack
callee artifacts.
-/
theorem regular_stack_of_safe_source
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {allocatorDepth sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {source sourceFinal : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {name : Functions.Name}
    {args : List (Functions.Expr 1)}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hFrameFunctions :
      AllocationLowering.frameFunctions
          compilation.recipe compilation.stackSlots =
        [])
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 2) (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx))
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth callerCtx
        callerState callerLocals callerPlan callerLive callerFrameBase
        .stack source target)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hBody :
      ∀ {fn : Functions.FunDef}
        {artifact :
          AllocationObserverCall.SelectedCallee.Artifact
            allocation program expressions name fn}
        (prepared :
          AllocationObserverCall.SelectedCallee.Prepared artifact)
        (hNoFrame : artifact.needsFrame = false)
        {sourceBodyStart :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx' : Functions.Source.Ctx}
        {targetBodyStart : Structured.ObserverSemantics.State transcript},
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            sourceFuel fn.body sourceBodyStart =
          .ok (bodyOutcome, bodyCtx') →
        AllocationObserverContext.ActivationResourceInvariant
            .stackOnly program.memoryContract allocatorDepth
            artifact.lowerCtx artifact.bodyStart prepared.returnCtx
            prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            0 .stack sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            artifact.lowerCtx prepared.bodyFinal prepared.bodyCtx
            prepared.plan fn.returns
            (Functions.Scope.Block.outEnv
              ((artifact.slots.returns.map Prod.fst).reverse ++
                (artifact.slots.params.map Prod.fst).reverse)
              fn.body)
            0 .stack program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            fn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart bodyOutcome targetOutcome bodyCtx') :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.RegularStmtResourceInvariantForward
        program.memoryContract .stackOnly allocatorDepth transcript
        callerCtx callerFinalState callerFinalLocals callerPlan callerLive
        callerFrameBase .stack .stack program sourceCtx
        (.call targets name args) source expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceFinal targetFinal sourceCtx := by
  obtain
      ⟨sourceAfterArgs, argValues, fn, sourceAfterCall,
        returnValues, returnStore, paramStore, bodyOutcome, bodyCtx',
        _hTargetsNodup, hArgs, hFind, hParams, hBodyRun, hBodyMode,
        hReturns, hBodyState, hAssign, hFinal⟩ :=
    Functions.Source.Effectful.Stmt.call_regular_body_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (AllocationObserverSafety.SafeSemantics.primitiveSemantics
        program.memoryContract transcript)
      program hSource
  obtain ⟨artifact⟩ := compilation.selectedCallee hFind
  obtain ⟨prepared⟩ := artifact.prepare
  have hArtifactFrames :
      AllocationLowering.frameFunctions
          artifact.recipe artifact.stackSlots =
        [] := by
    obtain ⟨hRecipe, hSlots, _hFrameName⟩ :=
      compilation.selected_agrees artifact
    simpa [hRecipe, hSlots] using hFrameFunctions
  have hNoFrame : artifact.needsFrame = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hNeedsFrame
    have hMem := artifact.mem_frameFunctions_iff.mpr hNeedsFrame
    rw [hArtifactFrames] at hMem
    simp at hMem
  let bodyStore :=
    Functions.Source.Store.initReturns fn.returns paramStore
  let sourceBodyStart :=
    (Functions.ObserverSemantics.stateModel transcript).withSource
      sourceAfterArgs
      { shared := sourceAfterArgs.source.shared
        vars := bodyStore }
  have hBodyRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body sourceBodyStart =
        .ok (bodyOutcome, bodyCtx') := by
    simpa [sourceBodyStart, bodyStore] using hBodyRun
  have hBodyVars :
      sourceBodyStart.source.vars = bodyStore := by
    simp [sourceBodyStart, bodyStore,
      Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource]
  have hInitialized :
      Functions.Source.Store.lookupMany fn.params
            sourceBodyStart.source.vars =
          some argValues ∧
        (∀ returnName, returnName ∈ fn.returns →
          sourceBodyStart.source.vars returnName =
            some AllocationSupport.zeroWord) ∧
        LiveDefined (fn.returns.reverse ++ fn.params.reverse)
          sourceBodyStart.source :=
    AllocationObserverCall.FunctionPrelude.initialized_source_facts
      (params := fn.params)
      (returns := fn.returns)
      (args := argValues)
      (paramStore := paramStore)
      (source := sourceBodyStart)
      prepared.signatureNodup hParams
      (by simpa [bodyStore] using hBodyVars)
  obtain ⟨hParamSource, hZeroSource, hDefinedSource⟩ := hInitialized
  have hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst) bodyStore =
        some argValues := by
    rw [artifact.slotsMatch.2.1]
    simpa [hBodyVars] using hParamSource
  have hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord := by
    rw [artifact.slotsMatch.2.2]
    exact hZeroSource
  have hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source := by
    simpa [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2] using
      hDefinedSource
  have hSafeArgs :=
    AllocationObserverSafety.ArgList.MemorySafeEval.of_safe_eval hArgs
  have hReturnsLive :
      ∀ returnName, returnName ∈ fn.returns →
        returnName ∈
          Functions.Scope.Block.outEnv
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            fn.body := by
    intro returnName hReturn
    apply Functions.Scope.Block.mem_outEnv
    apply List.mem_append_left
    rw [List.mem_reverse, artifact.slotsMatch.2.2]
    exact hReturn
  rcases hBodyMode with hRegular | hLeave
  · have hBodyOutcome :
        bodyOutcome =
          Functions.Source.Effectful.Outcome.regular sourceAfterCall := by
      rcases bodyOutcome with ⟨bodyState, bodyMode⟩
      simp only [Functions.Source.Effectful.Outcome.regular] at hRegular ⊢
      cases hRegular
      simp only [Functions.Source.Effectful.Outcome.regular,
        Locals.Source.Effectful.Outcome.regular]
      cases hBodyState
      rfl
    subst bodyOutcome
    have hCallee :
        ∀ {targetEntry : Structured.ObserverSemantics.State transcript},
          ActivationCalleeEntryRel
              program.memoryContract prepared.plan []
              artifact.slots.params 0 .stack sourceBodyStart targetEntry →
          targetEntry.source.returns ≠ [] →
          targetEntry.source.evm.stack.length =
              artifact.entryCtx.layout.length →
          ∃ calleeFinal bodyFuel,
            Structured.ObserverSemantics.Block.Eval
              expressions.toStructured bodyFuel
              artifact.lowerProc.toStructured.body targetEntry
              (AllocationObserverCall.StructuredCall.ReturnMode.regular.outcome
                calleeFinal) ∧
            calleeFinal.source.evm.stack = returnValues.reverse ∧
            sourceAfterCall.cursor = calleeFinal.cursor ∧
            Compiler.MemoryRelation.MachineRel program.memoryContract
              sourceAfterCall.source.shared.toMachineState
              calleeFinal.source.evm.toMachineState ∧
            sourceAfterCall.source.shared.toState =
              calleeFinal.source.evm.toSharedState.toState ∧
            calleeFinal.source.evm.activeWords.toNat *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
      intro targetEntry hEntry hReturnFrame hEntryStack
      apply Callee.prepared_regular_stack prepared hNoFrame hEntry hEntryStack
        hZero hDefined hReturnFrame
      · intro targetBodyStart hBodyInvariant hBodyReturnFrame
        obtain ⟨targetOutcome, hBodyForward⟩ :=
          hBody prepared hNoFrame hBodyRun'
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hBodyInvariant rfl)
            hBodyReturnFrame
        cases hBodyForward with
        | regular hForward _hControl =>
            exact ⟨_, _, hForward.toInvariant⟩
        | nonregular _hMode _hForward =>
            contradiction
      · exact hReturnsLive
      · simpa [hBodyState] using hReturns
    obtain ⟨targetFinal, hForward⟩ :=
      regular_stack_of_selected compilation prepared hNoFrame hCallerShared
        hSource hSafeArgs hParamLookup rfl hAssign
        (by simpa [hBodyState] using hFinal)
        hScoped hInvariant.activation hLower hCompile hCallee
    exact ⟨targetFinal, hForward.toStackResource rfl⟩
  · have hBodyOutcome :
        bodyOutcome =
          Functions.Source.Effectful.Outcome.leave sourceAfterCall := by
      rcases bodyOutcome with ⟨bodyState, bodyMode⟩
      simp only [Functions.Source.Effectful.Outcome.leave] at hLeave ⊢
      cases hLeave
      simp only [Functions.Source.Effectful.Outcome.leave,
        Locals.Source.Effectful.Outcome.leave]
      cases hBodyState
      rfl
    subst bodyOutcome
    have hCallee :
        ∀ {targetEntry : Structured.ObserverSemantics.State transcript},
          ActivationCalleeEntryRel
              program.memoryContract prepared.plan []
              artifact.slots.params 0 .stack sourceBodyStart targetEntry →
          targetEntry.source.returns ≠ [] →
          targetEntry.source.evm.stack.length =
              artifact.entryCtx.layout.length →
          ∃ calleeFinal bodyFuel,
            Structured.ObserverSemantics.Block.Eval
              expressions.toStructured bodyFuel
              artifact.lowerProc.toStructured.body targetEntry
              (AllocationObserverCall.StructuredCall.ReturnMode.leave.outcome
                calleeFinal) ∧
            calleeFinal.source.evm.stack = returnValues.reverse ∧
            sourceAfterCall.cursor = calleeFinal.cursor ∧
            Compiler.MemoryRelation.MachineRel program.memoryContract
              sourceAfterCall.source.shared.toMachineState
              calleeFinal.source.evm.toMachineState ∧
            sourceAfterCall.source.shared.toState =
              calleeFinal.source.evm.toSharedState.toState ∧
            calleeFinal.source.evm.activeWords.toNat *
                MemoryContract.wordBytes <
              EvmYul.UInt256.size := by
      intro targetEntry hEntry hReturnFrame hEntryStack
      apply Callee.prepared_leave_stack prepared hNoFrame hEntry hEntryStack
        hZero hDefined hReturnFrame
      · intro targetBodyStart hBodyInvariant hBodyReturnFrame
        obtain ⟨targetOutcome, hBodyForward⟩ :=
          hBody prepared hNoFrame hBodyRun'
            (AllocationObserverContext.ActivationResourceInvariant.stackOnly
              hBodyInvariant rfl)
            hBodyReturnFrame
        cases hBodyForward with
        | nonregular _hMode hForward =>
            rcases hForward with
              ⟨_sourceBodyFuel, targetBodyFuel, _hSourceBody,
                hTargetBody, hOutcomeRel, hSame, _hEffect⟩
            cases hOutcomeRel with
            | leave hLeaveRel =>
                exact
                  ⟨_, _, targetBodyFuel, hTargetBody, hSame, hLeaveRel⟩
      · simpa [hBodyState] using hReturns
    obtain ⟨targetFinal, hForward⟩ :=
      regular_stack_of_selected compilation prepared hNoFrame hCallerShared
        hSource hSafeArgs hParamLookup rfl hAssign
        (by simpa [hBodyState] using hFinal)
        hScoped hInvariant.activation hLower hCompile hCallee
    exact ⟨targetFinal, hForward.toStackResource rfl⟩

/--
Lift a successful guarded source call through the real selected-callee
compiler artifacts.

The body callback is fuel-smaller proof recursion only. It consumes the exact
guarded body run exposed by the canonical Functions semantics and is not
retained by the public adjacent-pass theorem.
-/
theorem regular_of_safe_source
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {config : Frame.Config}
    {allocatorDepth sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {callerMode : ActivationMode}
    {source sourceFinal : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {name : Functions.Name}
    {args : List (Functions.Expr 1)}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 2) (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx))
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth callerCtx callerState
        callerLocals callerPlan callerLive callerFrameBase callerMode
        source target)
    (hBudget : Frame.Budget config allocatorDepth)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hBody :
      ∀ {fn : Functions.FunDef}
        {artifact :
          AllocationObserverCall.SelectedCallee.Artifact
            allocation program expressions name fn}
        (prepared :
          AllocationObserverCall.SelectedCallee.Prepared artifact)
        {sourceBodyStart :
          Functions.ObserverSemantics.State transcript}
        {bodyOutcome :
          Functions.ObserverSemantics.Outcome
            (Functions.ObserverSemantics.State transcript)}
        {bodyCtx' : Functions.Source.Ctx}
        {targetBodyStart : Structured.ObserverSemantics.State transcript}
        {calleeDepth calleeFrameBase : Nat},
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            sourceFuel fn.body sourceBodyStart =
          .ok (bodyOutcome, bodyCtx') →
        calleeDepth ≤ allocatorDepth + 1 →
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            calleeFrameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config calleeDepth transcript
            artifact.lowerCtx prepared.bodyFinal prepared.bodyCtx
            prepared.plan fn.returns
            (Functions.Scope.Block.outEnv
              ((artifact.slots.returns.map Prod.fst).reverse ++
                (artifact.slots.params.map Prod.fst).reverse)
              fn.body)
            calleeFrameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            fn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart bodyOutcome targetOutcome bodyCtx') :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        callerCtx callerFinalState callerFinalLocals callerPlan callerLive
        callerFrameBase callerMode callerMode program sourceCtx
        (.call targets name args) source expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceFinal targetFinal sourceCtx := by
  obtain
      ⟨sourceAfterArgs, argValues, fn, sourceAfterCall,
        returnValues, returnStore, paramStore, bodyOutcome, bodyCtx',
        hTargetsNodup, hArgs, hFind, hParams, hBodyRun, hBodyMode,
        hReturns, hBodyState, hAssign, hFinal⟩ :=
    Functions.Source.Effectful.Stmt.call_regular_body_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (AllocationObserverSafety.SafeSemantics.primitiveSemantics
        program.memoryContract transcript)
      program hSource
  obtain ⟨artifact⟩ := compilation.selectedCallee hFind
  obtain ⟨prepared⟩ := artifact.prepare
  have hArtifactConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config := by
    rw [(compilation.selected_agrees artifact).1]
    exact hConfig
  let bodyStore :=
    Functions.Source.Store.initReturns fn.returns paramStore
  let sourceBodyStart :=
    (Functions.ObserverSemantics.stateModel transcript).withSource
      sourceAfterArgs
      { shared := sourceAfterArgs.source.shared
        vars := bodyStore }
  have hBodyRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body sourceBodyStart =
        .ok (bodyOutcome, bodyCtx') := by
    simpa [sourceBodyStart, bodyStore] using hBodyRun
  have hBodyVars :
      sourceBodyStart.source.vars = bodyStore := by
    simp [sourceBodyStart, bodyStore,
      Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource]
  have hInitialized :
      Functions.Source.Store.lookupMany fn.params
            sourceBodyStart.source.vars =
          some argValues ∧
        (∀ returnName, returnName ∈ fn.returns →
          sourceBodyStart.source.vars returnName =
            some AllocationSupport.zeroWord) ∧
        LiveDefined (fn.returns.reverse ++ fn.params.reverse)
          sourceBodyStart.source :=
    AllocationObserverCall.FunctionPrelude.initialized_source_facts
      (params := fn.params)
      (returns := fn.returns)
      (args := argValues)
      (paramStore := paramStore)
      (source := sourceBodyStart)
      prepared.signatureNodup hParams
      (by simpa [bodyStore] using hBodyVars)
  obtain ⟨hParamSource, hZeroSource, hDefinedSource⟩ := hInitialized
  have hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst) bodyStore =
        some argValues := by
    rw [artifact.slotsMatch.2.1]
    simpa [hBodyVars] using hParamSource
  have hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord := by
    rw [artifact.slotsMatch.2.2]
    exact hZeroSource
  have hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source := by
    simpa [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2] using
      hDefinedSource
  have hSafeArgs :=
    AllocationObserverSafety.ArgList.MemorySafeEval.of_safe_eval hArgs
  have hReturnsLive :
      ∀ returnName, returnName ∈ fn.returns →
        returnName ∈
          Functions.Scope.Block.outEnv
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            fn.body := by
    intro returnName hReturn
    apply Functions.Scope.Block.mem_outEnv
    apply List.mem_append_left
    rw [List.mem_reverse, artifact.slotsMatch.2.2]
    exact hReturn
  rcases hBodyMode with hRegular | hLeave
  · have hBodyOutcome :
        bodyOutcome =
          Functions.Source.Effectful.Outcome.regular sourceAfterCall := by
      rcases bodyOutcome with ⟨bodyState, bodyMode⟩
      simp only [Functions.Source.Effectful.Outcome.regular] at hRegular ⊢
      cases hRegular
      simp only [Functions.Source.Effectful.Outcome.regular,
        Locals.Source.Effectful.Outcome.regular]
      cases hBodyState
      rfl
    subst bodyOutcome
    have hCallee :
        ∀ {targetEntry : Structured.ObserverSemantics.State transcript}
          {calleeDepth calleeFrameBase : Nat},
          ActivationCalleeEntryRel
              program.memoryContract prepared.plan []
              artifact.slots.params calleeFrameBase prepared.mode
              sourceBodyStart targetEntry →
          targetEntry.source.returns ≠ [] →
          targetEntry.source.evm.stack.length =
              artifact.entryCtx.layout.length →
          Frame.AllocatorReady config calleeDepth targetEntry →
          Frame.ActivationOwned config calleeDepth calleeFrameBase
              prepared.mode →
          AllocationObserverCall.RegularCallee.protectedBound
              calleeDepth prepared.mode =
            allocatorDepth + 1 →
          ∃ calleeFinal bodyFuel,
            Structured.ObserverSemantics.Block.Eval
              expressions.toStructured bodyFuel
              artifact.lowerProc.toStructured.body targetEntry
              (AllocationObserverCall.StructuredCall.ReturnMode.regular.outcome
                calleeFinal) ∧
            calleeFinal.source.evm.stack = returnValues.reverse ∧
            sourceAfterCall.cursor = calleeFinal.cursor ∧
            Compiler.MemoryRelation.MachineRel program.memoryContract
              sourceAfterCall.source.shared.toMachineState
              calleeFinal.source.evm.toMachineState ∧
            sourceAfterCall.source.shared.toState =
              calleeFinal.source.evm.toSharedState.toState ∧
            Frame.BoundedEffect config calleeDepth (allocatorDepth + 1)
              targetEntry calleeFinal := by
      intro targetEntry calleeDepth calleeFrameBase hEntry
        hReturnFrame hEntryStack hReady hOwned hProtected
      have hCalleeDepth : calleeDepth ≤ allocatorDepth + 1 := by
        rw [← hProtected]
        exact
          AllocationObserverCall.RegularCallee.depth_le_protectedBound
            calleeDepth prepared.mode
      apply Callee.prepared_regular prepared hArtifactConfig hEntry hEntryStack
        hZero hDefined hReady hOwned hReturnFrame
      · intro targetBodyStart hBodyInvariant hBodyReturnFrame
        obtain ⟨targetOutcome, hBodyForward⟩ :=
          hBody prepared hBodyRun' hCalleeDepth hBodyInvariant
            hBodyReturnFrame
        cases hBodyForward with
        | regular hForward =>
            exact ⟨_, _, hForward⟩
        | nonregular _hForward =>
            contradiction
      · exact hReturnsLive
      · simpa [hBodyState] using hReturns
      · exact hProtected
    exact
      regular_of_selected compilation prepared hConfig hCallerShared
        hSource hSafeArgs hParamLookup rfl hAssign
        (by simpa [hBodyState] using hFinal)
        hScoped hInvariant hBudget hLower hCompile hCallee
  · have hBodyOutcome :
        bodyOutcome =
          Functions.Source.Effectful.Outcome.leave sourceAfterCall := by
      rcases bodyOutcome with ⟨bodyState, bodyMode⟩
      simp only [Functions.Source.Effectful.Outcome.leave] at hLeave ⊢
      cases hLeave
      simp only [Functions.Source.Effectful.Outcome.leave,
        Locals.Source.Effectful.Outcome.leave]
      cases hBodyState
      rfl
    subst bodyOutcome
    have hCallee :
        ∀ {targetEntry : Structured.ObserverSemantics.State transcript}
          {calleeDepth calleeFrameBase : Nat},
          ActivationCalleeEntryRel
              program.memoryContract prepared.plan []
              artifact.slots.params calleeFrameBase prepared.mode
              sourceBodyStart targetEntry →
          targetEntry.source.returns ≠ [] →
          targetEntry.source.evm.stack.length =
              artifact.entryCtx.layout.length →
          Frame.AllocatorReady config calleeDepth targetEntry →
          Frame.ActivationOwned config calleeDepth calleeFrameBase
              prepared.mode →
          AllocationObserverCall.RegularCallee.protectedBound
              calleeDepth prepared.mode =
            allocatorDepth + 1 →
          ∃ calleeFinal bodyFuel,
            Structured.ObserverSemantics.Block.Eval
              expressions.toStructured bodyFuel
              artifact.lowerProc.toStructured.body targetEntry
              (AllocationObserverCall.StructuredCall.ReturnMode.leave.outcome
                calleeFinal) ∧
            calleeFinal.source.evm.stack = returnValues.reverse ∧
            sourceAfterCall.cursor = calleeFinal.cursor ∧
            Compiler.MemoryRelation.MachineRel program.memoryContract
              sourceAfterCall.source.shared.toMachineState
              calleeFinal.source.evm.toMachineState ∧
            sourceAfterCall.source.shared.toState =
              calleeFinal.source.evm.toSharedState.toState ∧
            Frame.BoundedEffect config calleeDepth (allocatorDepth + 1)
              targetEntry calleeFinal := by
      intro targetEntry calleeDepth calleeFrameBase hEntry
        hReturnFrame hEntryStack hReady hOwned hProtected
      have hCalleeDepth : calleeDepth ≤ allocatorDepth + 1 := by
        rw [← hProtected]
        exact
          AllocationObserverCall.RegularCallee.depth_le_protectedBound
            calleeDepth prepared.mode
      apply Callee.prepared_leave prepared hArtifactConfig hEntry hEntryStack
        hZero hDefined hReady hOwned hReturnFrame
      · intro targetBodyStart hBodyInvariant _hBodyReturnFrame
        obtain ⟨targetOutcome, hBodyForward⟩ :=
          hBody prepared hBodyRun' hCalleeDepth hBodyInvariant
            _hBodyReturnFrame
        cases hBodyForward with
        | nonregular _hMode hForward =>
            rcases hForward with
              ⟨_sourceBodyFuel, targetBodyFuel, _hSourceBody,
                hTargetBody, hOutcomeRel, hSame, hEffect⟩
            cases hOutcomeRel with
            | leave hLeaveRel =>
                obtain ⟨returned, hReturned, hStack⟩ :=
                  hLeaveRel.values
                have hReturnedEq : returned = returnValues := by
                  exact Option.some.inj (hReturned.symm.trans hReturns)
                subst returned
                have hActivationEffect :=
                  Frame.OutcomeEffect.activation_of_not_halt hEffect (by
                    intro kind hMode
                    cases hMode)
                exact
                  ⟨_, _, targetBodyFuel, hTargetBody, hSame,
                    hActivationEffect,
                    hStack, hLeaveRel.cursor, hLeaveRel.shared.machine,
                    hLeaveRel.shared.world⟩
      · exact hProtected
    exact
      regular_of_selected compilation prepared hConfig hCallerShared
        hSource hSafeArgs hParamLookup rfl hAssign
        (by simpa [hBodyState] using hFinal)
        hScoped hInvariant hBudget hLower hCompile hCallee

/--
Lift a guarded halting call through compiler-selected all-stack callee
artifacts.
-/
theorem halt_stack_of_safe_source
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {allocatorDepth sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {source sourceFinal : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {name : Functions.Name}
    {args : List (Functions.Expr 1)}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {kind : Assembly.HaltKind}
    (hFrameFunctions :
      AllocationLowering.frameFunctions
          compilation.recipe compilation.stackSlots =
        [])
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 2) (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            sourceCtx))
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        .stackOnly program.memoryContract allocatorDepth callerCtx
        callerState callerLocals callerPlan callerLive callerFrameBase
        .stack source target)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hBody :
      ∀ {fn : Functions.FunDef}
        {artifact :
          AllocationObserverCall.SelectedCallee.Artifact
            allocation program expressions name fn}
        (prepared :
          AllocationObserverCall.SelectedCallee.Prepared artifact)
        (hNoFrame : artifact.needsFrame = false)
        {sourceBodyStart :
          Functions.ObserverSemantics.State transcript}
        {bodyCtx' : Functions.Source.Ctx}
        {targetBodyStart : Structured.ObserverSemantics.State transcript},
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            sourceFuel fn.body sourceBodyStart =
          .ok
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
              bodyCtx') →
        AllocationObserverContext.ActivationResourceInvariant
            .stackOnly program.memoryContract allocatorDepth
            artifact.lowerCtx artifact.bodyStart prepared.returnCtx
            prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            0 .stack sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockResourceResult
            program.memoryContract .stackOnly allocatorDepth transcript
            artifact.lowerCtx prepared.bodyFinal prepared.bodyCtx
            prepared.plan fn.returns
            (Functions.Scope.Block.outEnv
              ((artifact.slots.returns.map Prod.fst).reverse ++
                (artifact.slots.params.map Prod.fst).reverse)
              fn.body)
            0 .stack program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            fn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
            targetOutcome bodyCtx') :
    ∃ targetFinal,
      AllocationObserverOutcome.NonregularStmtResourceForward
        program.memoryContract .stackOnly allocatorDepth transcript
        callerPlan callerLive callerFrameBase .stack .stack
        program sourceCtx (.call targets name args) source
        expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)
        sourceCtx := by
  obtain
      ⟨sourceAfterArgs, argValues, fn, paramStore, bodyCtx',
        _hTargetsNodup, hArgs, hFind, hParams, hBodyRun⟩ :=
    Functions.Source.Effectful.Stmt.call_halted_body_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (AllocationObserverSafety.SafeSemantics.primitiveSemantics
        program.memoryContract transcript)
      program hSource
  obtain ⟨artifact⟩ := compilation.selectedCallee hFind
  obtain ⟨prepared⟩ := artifact.prepare
  have hArtifactFrames :
      AllocationLowering.frameFunctions
          artifact.recipe artifact.stackSlots =
        [] := by
    obtain ⟨hRecipe, hSlots, _hFrameName⟩ :=
      compilation.selected_agrees artifact
    simpa [hRecipe, hSlots] using hFrameFunctions
  have hNoFrame : artifact.needsFrame = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hNeedsFrame
    have hMem := artifact.mem_frameFunctions_iff.mpr hNeedsFrame
    rw [hArtifactFrames] at hMem
    simp at hMem
  let bodyStore :=
    Functions.Source.Store.initReturns fn.returns paramStore
  let sourceBodyStart :=
    (Functions.ObserverSemantics.stateModel transcript).withSource
      sourceAfterArgs
      { shared := sourceAfterArgs.source.shared
        vars := bodyStore }
  have hBodyRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body sourceBodyStart =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            bodyCtx') := by
    simpa [sourceBodyStart, bodyStore] using hBodyRun
  have hBodyVars :
      sourceBodyStart.source.vars = bodyStore := by
    simp [sourceBodyStart, bodyStore,
      Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource]
  have hInitialized :
      Functions.Source.Store.lookupMany fn.params
            sourceBodyStart.source.vars =
          some argValues ∧
        (∀ returnName, returnName ∈ fn.returns →
          sourceBodyStart.source.vars returnName =
            some AllocationSupport.zeroWord) ∧
        LiveDefined (fn.returns.reverse ++ fn.params.reverse)
          sourceBodyStart.source :=
    AllocationObserverCall.FunctionPrelude.initialized_source_facts
      (params := fn.params)
      (returns := fn.returns)
      (args := argValues)
      (paramStore := paramStore)
      (source := sourceBodyStart)
      prepared.signatureNodup hParams
      (by simpa [bodyStore] using hBodyVars)
  obtain ⟨hParamSource, hZeroSource, hDefinedSource⟩ := hInitialized
  have hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst) bodyStore =
        some argValues := by
    rw [artifact.slotsMatch.2.1]
    simpa [hBodyVars] using hParamSource
  have hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord := by
    rw [artifact.slotsMatch.2.2]
    exact hZeroSource
  have hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source := by
    simpa [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2] using
      hDefinedSource
  have hSafeArgs :=
    AllocationObserverSafety.ArgList.MemorySafeEval.of_safe_eval hArgs
  have hCallee :
      ∀ {targetEntry : Structured.ObserverSemantics.State transcript},
        ActivationCalleeEntryRel
            program.memoryContract prepared.plan []
            artifact.slots.params 0 .stack sourceBodyStart targetEntry →
        targetEntry.source.returns ≠ [] →
        targetEntry.source.evm.stack.length =
            artifact.entryCtx.layout.length →
        ∃ calleeFinal bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            artifact.lowerProc.toStructured.body targetEntry
            (Structured.EffectSemantics.Outcome.halt kind calleeFinal) ∧
          HaltStateRel program.memoryContract prepared.plan
            sourceFinal calleeFinal := by
    intro targetEntry hEntry hReturnFrame hEntryStack
    apply Callee.prepared_halt_stack prepared hNoFrame hEntry hEntryStack
      hZero hDefined hReturnFrame
    intro targetBodyStart hBodyInvariant hBodyReturnFrame
    obtain ⟨targetOutcome, hBodyForward⟩ :=
      hBody prepared hNoFrame hBodyRun'
        (AllocationObserverContext.ActivationResourceInvariant.stackOnly
          hBodyInvariant rfl)
        hBodyReturnFrame
    cases hBodyForward with
    | nonregular _hMode hForward =>
        rcases hForward with
          ⟨_sourceBodyFuel, targetBodyFuel, _hSourceBody,
            hTargetBody, hOutcomeRel, hSame, _hEffect⟩
        cases hOutcomeRel with
        | halt _ hHaltRel =>
            exact
              ⟨_, _, targetBodyFuel, hTargetBody, hSame, hHaltRel⟩
  obtain ⟨targetFinal, hForward⟩ :=
    halt_stack_of_selected compilation prepared hNoFrame hCallerShared
      (sourceFuel := sourceFuel + 2) hSource hSafeArgs hParamLookup rfl
      hScoped hInvariant.activation hLower hCompile hCallee
  exact ⟨targetFinal, hForward.toStackResource rfl rfl⟩

/--
Lift a guarded halting source call through the real selected-callee artifacts.

The body callback is the strictly fuel-smaller recursive block theorem. The
selected procedure, parameter/return initialization, entry representation, and
terminal caller path are all reconstructed from the existing compiler and
source semantics.
-/
theorem halt_of_safe_source
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {config : Frame.Config}
    {allocatorDepth sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {callerMode : ActivationMode}
    {source sourceFinal : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {name : Functions.Name}
    {args : List (Functions.Expr 1)}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {kind : Assembly.HaltKind}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx (sourceFuel + 2) (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            sourceCtx))
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth callerCtx callerState
        callerLocals callerPlan callerLive callerFrameBase callerMode
        source target)
    (hBudget : Frame.Budget config allocatorDepth)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hBody :
      ∀ {fn : Functions.FunDef}
        {artifact :
          AllocationObserverCall.SelectedCallee.Artifact
            allocation program expressions name fn}
        (prepared :
          AllocationObserverCall.SelectedCallee.Prepared artifact)
        {sourceBodyStart :
          Functions.ObserverSemantics.State transcript}
        {bodyCtx' : Functions.Source.Ctx}
        {targetBodyStart : Structured.ObserverSemantics.State transcript}
        {calleeDepth calleeFrameBase : Nat},
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            sourceFuel fn.body sourceBodyStart =
          .ok
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
              bodyCtx') →
        calleeDepth ≤ allocatorDepth + 1 →
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            calleeFrameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        targetBodyStart.source.returns ≠ [] →
        ∃ targetOutcome,
          AllocationObserverOutcome.BlockRuntimeResult
            program.memoryContract config calleeDepth transcript
            artifact.lowerCtx prepared.bodyFinal prepared.bodyCtx
            prepared.plan fn.returns
            (Functions.Scope.Block.outEnv
              ((artifact.slots.returns.map Prod.fst).reverse ++
                (artifact.slots.params.map Prod.fst).reverse)
              fn.body)
            calleeFrameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            fn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
            targetOutcome bodyCtx') :
    ∃ targetFinal,
      AllocationObserverOutcome.NonregularStmtRuntimeForward
        program.memoryContract config allocatorDepth transcript
        callerPlan callerLive callerFrameBase callerMode callerMode
        program sourceCtx (.call targets name args) source
        expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)
        sourceCtx := by
  obtain
      ⟨sourceAfterArgs, argValues, fn, paramStore, bodyCtx',
        _hTargetsNodup, hArgs, hFind, hParams, hBodyRun⟩ :=
    Functions.Source.Effectful.Stmt.call_halted_body_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (AllocationObserverSafety.SafeSemantics.primitiveSemantics
        program.memoryContract transcript)
      program hSource
  obtain ⟨artifact⟩ := compilation.selectedCallee hFind
  obtain ⟨prepared⟩ := artifact.prepare
  have hArtifactConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config := by
    rw [(compilation.selected_agrees artifact).1]
    exact hConfig
  let bodyStore :=
    Functions.Source.Store.initReturns fn.returns paramStore
  let sourceBodyStart :=
    (Functions.ObserverSemantics.stateModel transcript).withSource
      sourceAfterArgs
      { shared := sourceAfterArgs.source.shared
        vars := bodyStore }
  have hBodyRun' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body sourceBodyStart =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            bodyCtx') := by
    simpa [sourceBodyStart, bodyStore] using hBodyRun
  have hBodyVars :
      sourceBodyStart.source.vars = bodyStore := by
    simp [sourceBodyStart, bodyStore,
      Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource]
  have hInitialized :
      Functions.Source.Store.lookupMany fn.params
            sourceBodyStart.source.vars =
          some argValues ∧
        (∀ returnName, returnName ∈ fn.returns →
          sourceBodyStart.source.vars returnName =
            some AllocationSupport.zeroWord) ∧
        LiveDefined (fn.returns.reverse ++ fn.params.reverse)
          sourceBodyStart.source :=
    AllocationObserverCall.FunctionPrelude.initialized_source_facts
      (params := fn.params)
      (returns := fn.returns)
      (args := argValues)
      (paramStore := paramStore)
      (source := sourceBodyStart)
      prepared.signatureNodup hParams
      (by simpa [bodyStore] using hBodyVars)
  obtain ⟨hParamSource, hZeroSource, hDefinedSource⟩ := hInitialized
  have hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst) bodyStore =
        some argValues := by
    rw [artifact.slotsMatch.2.1]
    simpa [hBodyVars] using hParamSource
  have hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord := by
    rw [artifact.slotsMatch.2.2]
    exact hZeroSource
  have hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source := by
    simpa [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2] using
      hDefinedSource
  have hSafeArgs :=
    AllocationObserverSafety.ArgList.MemorySafeEval.of_safe_eval hArgs
  have hCallee :
      ∀ {targetEntry : Structured.ObserverSemantics.State transcript}
        {calleeDepth calleeFrameBase : Nat},
        ActivationCalleeEntryRel
            program.memoryContract prepared.plan []
            artifact.slots.params calleeFrameBase prepared.mode
            sourceBodyStart targetEntry →
        targetEntry.source.returns ≠ [] →
        targetEntry.source.evm.stack.length =
            artifact.entryCtx.layout.length →
        Frame.AllocatorReady config calleeDepth targetEntry →
        Frame.ActivationOwned config calleeDepth calleeFrameBase
            prepared.mode →
        AllocationObserverCall.RegularCallee.protectedBound
            calleeDepth prepared.mode =
          allocatorDepth + 1 →
        ∃ calleeFinal bodyFuel finalDepth,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            artifact.lowerProc.toStructured.body targetEntry
            (Structured.EffectSemantics.Outcome.halt kind calleeFinal) ∧
          HaltStateRel program.memoryContract prepared.plan
            sourceFinal calleeFinal ∧
          Frame.BoundedEffect config finalDepth (allocatorDepth + 1)
            targetEntry calleeFinal := by
    intro targetEntry calleeDepth calleeFrameBase hEntry
      hReturnFrame hEntryStack hReady hOwned hProtected
    have hCalleeDepth : calleeDepth ≤ allocatorDepth + 1 := by
      rw [← hProtected]
      exact
        AllocationObserverCall.RegularCallee.depth_le_protectedBound
          calleeDepth prepared.mode
    apply Callee.prepared_halt prepared hArtifactConfig hEntry hEntryStack
      hZero hDefined hReady hOwned hReturnFrame
    · intro targetBodyStart hBodyInvariant hBodyReturnFrame
      obtain ⟨targetOutcome, hBodyForward⟩ :=
        hBody prepared hBodyRun' hCalleeDepth hBodyInvariant
          hBodyReturnFrame
      cases hBodyForward with
      | nonregular _hMode hForward =>
          rcases hForward with
            ⟨_sourceBodyFuel, targetBodyFuel, _hSourceBody,
              hTargetBody, hOutcomeRel, hSame, hEffect⟩
          cases hOutcomeRel with
          | halt _ hHaltRel =>
              exact
                ⟨_, _, targetBodyFuel, hTargetBody, hSame,
                  hEffect, hHaltRel⟩
    · exact hProtected
  exact
    halt_of_selected compilation prepared hConfig hCallerShared
      (sourceFuel := sourceFuel + 2) hSource hSafeArgs hParamLookup rfl
      hScoped hInvariant hBudget hLower hCompile hCallee

end Call

end AllocationObserverForward
end Functions
end EvmCompiler
