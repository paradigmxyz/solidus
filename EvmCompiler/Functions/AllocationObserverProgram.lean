import EvmCompiler.Functions.AllocationObserverRecursive

namespace EvmCompiler
namespace Functions
namespace AllocationObserverProgram

open AllocationObserverRelation
open AllocationObserverForward

abbrev Trace := Assembly.ResourceTrace

private theorem block_eq_of_stmts_eq
    {left right : Functions.Block}
    (hStmts : left.stmts = right.stmts) :
    left = right := by
  cases left
  cases right
  simp_all

/--
Compiler-owned artifact for the distinguished Functions main body.

Unlike selected functions, main has no parameter/return prelude or procedure
lookup. Its real lowering instead preserves an initial source-code prelude,
inserts allocator/frame setup, lowers the remaining open body, and lets the
Locals compiler append top-level cleanup.
-/
structure MainArtifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation :
      AllocationObserverForward.Compilation allocation program expressions)
    where
  main : Locals.Block
  final : AllocationLowering.State
  components :
    AllocationLowering.MainComponents
      compilation.recipe compilation.stackSlots compilation.frameName
      compilation.frameConfig?
      { env := []
        nextSlot := compilation.recipe.stateAfterFunctions.nextSlot }
      program.body main final
  finalPlan :
    final.allocation = compilation.recipe.main
  compile :
    Locals.Block.compile Locals.Ctx.initial main =
      some expressions.body

theorem MainArtifact.ofCompilation
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation :
      AllocationObserverForward.Compilation allocation program expressions) :
    Nonempty (MainArtifact compilation) := by
  obtain
      ⟨recipe, stackSlots, frameName, _procs, _stateAfterFunctions,
        main, final, hValidate, hFresh, _hFunctions, _hState,
        hComponents, hFinal, _hProcs, hCompile⟩ :=
    AllocationLowering.lowerExpressionsFromAllocation?_main_components
      compilation.lower
  have hValidated :
      (recipe, stackSlots) =
        (compilation.recipe, compilation.stackSlots) :=
    Option.some.inj (hValidate.symm.trans compilation.validate)
  have hFrameName :
      frameName = compilation.frameName :=
    Option.some.inj (hFresh.symm.trans compilation.fresh)
  have hRecipe : recipe = compilation.recipe :=
    congrArg Prod.fst hValidated
  have hSlots : stackSlots = compilation.stackSlots :=
    congrArg Prod.snd hValidated
  subst recipe
  subst stackSlots
  subst frameName
  rcases hComponents with ⟨components⟩
  exact
    ⟨{ main := main
       final := final
       components := by
         simpa [AllocationObserverForward.Compilation.frameConfig?] using
           components
       finalPlan := hFinal
       compile := hCompile }⟩

def MainArtifact.plan
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (_artifact : MainArtifact compilation) :
    Locals.Allocation.Plan :=
  MixedAllocation.allocationOfState
    program.memoryContract compilation.recipe.frameWords
    (MixedAllocation.AllocationRecipe.stackEntriesForScope
      compilation.recipe compilation.stackSlots .main
      compilation.recipe.main)
    compilation.recipe.main

theorem MainArtifact.planFind
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) :
    allocation.find? .main = some artifact.plan := by
  simpa [MainArtifact.plan] using
    AllocationLowering.validatePlan?_main_plan compilation.validate

theorem MainArtifact.planWF
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) :
    artifact.plan.WellFormed :=
  Locals.Allocation.ProgramPlan.wellFormed_of_find?_eq_some
    (AllocationLowering.validatePlan?_sound compilation.validate).1
    artifact.planFind

def MainArtifact.lowerCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (_artifact : MainArtifact compilation) :
    AllocationLowering.Ctx :=
  compilation.lowerCtx .main
    (AllocationLowering.mainScratchBindings
      compilation.recipe compilation.stackSlots)

@[simp] theorem MainArtifact.lowerCtx_eq_mainCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) :
    artifact.lowerCtx =
      AllocationLowering.mainCtx compilation.recipe compilation.stackSlots
        compilation.frameName compilation.frameConfig? := by
  rfl

def MainArtifact.start
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (_artifact : MainArtifact compilation) :
    AllocationLowering.State :=
  AllocationLowering.mainStartWithFrame
    compilation.recipe compilation.stackSlots compilation.frameName
    { env := []
      nextSlot := compilation.recipe.stateAfterFunctions.nextSlot }

theorem MainArtifact.lowerRest
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) :
    AllocationLowering.lowerBlockOpen artifact.lowerCtx []
        artifact.start { stmts := artifact.components.rest } =
      some (artifact.components.lowered, artifact.final) := by
  simpa [MainArtifact.lowerCtx, MainArtifact.start] using
    artifact.components.lower

/--
The real Locals compilation of main, split at the three pass-owned boundaries:
preserved source prelude, allocator initialization, optional frame setup, and
the ordinary allocation-lowered body. The final cleanup remains a separate
compiler-owned suffix.
-/
structure MainPrepared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) where
  sourceCode : List Expressions.Stmt
  sourceCtx : Locals.Ctx
  allocatorCode : List Expressions.Stmt
  allocatorCtx : Locals.Ctx
  frameCode : List Expressions.Stmt
  bodyCtx : Locals.Ctx
  bodyCode : List Expressions.Stmt
  finalCtx : Locals.Ctx
  cleanup : Structured.Code
  compileSource :
    Locals.Block.compileOpen Locals.Ctx.initial
        { stmts := artifact.components.sourcePrelude } =
      some (sourceCode, sourceCtx)
  compileAllocator :
    Locals.Block.compileOpen sourceCtx
        { stmts := artifact.components.allocatorPrelude } =
      some (allocatorCode, allocatorCtx)
  compileFrame :
    Locals.Block.compileOpen allocatorCtx
        { stmts := artifact.components.framePrelude } =
      some (frameCode, bodyCtx)
  compileBody :
    Locals.Block.compileOpen bodyCtx
        { stmts := artifact.components.lowered.stmts } =
      some (bodyCode, finalCtx)
  cleanupCode :
    finalCtx.cleanupTo? Locals.Ctx.initial.layout.length = some cleanup
  output :
    expressions.body =
      { stmts :=
          sourceCode ++ allocatorCode ++ frameCode ++ bodyCode ++
            Locals.codeStmt cleanup }

theorem MainPrepared.ofArtifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) :
    Nonempty (MainPrepared artifact) := by
  obtain ⟨openCode, finalCtx, hOpen, hFinish⟩ :=
    Locals.Block.compile_components artifact.compile
  rw [artifact.components.output] at hOpen
  have hOpenSource :
      Locals.Block.compileOpen Locals.Ctx.initial
          { stmts :=
              artifact.components.sourcePrelude ++
                (artifact.components.allocatorPrelude ++
                  artifact.components.framePrelude ++
                  artifact.components.lowered.stmts) } =
        some (openCode, finalCtx) := by
    simpa [List.append_assoc] using hOpen
  obtain
      ⟨sourceCode, sourceCtx, afterSourceCode,
        hSource, hAfterSource, hOpenCode⟩ :=
    Locals.Block.compileOpen_append_components hOpenSource
  have hAfterSource' :
      Locals.Block.compileOpen sourceCtx
          { stmts :=
              artifact.components.allocatorPrelude ++
                (artifact.components.framePrelude ++
                  artifact.components.lowered.stmts) } =
        some (afterSourceCode, finalCtx) := by
    simpa [List.append_assoc] using hAfterSource
  obtain
      ⟨allocatorCode, allocatorCtx, afterAllocatorCode,
        hAllocator, hAfterAllocator, hAfterSourceCode⟩ :=
    Locals.Block.compileOpen_append_components
      (left := artifact.components.allocatorPrelude)
      (right :=
        artifact.components.framePrelude ++
          artifact.components.lowered.stmts)
      hAfterSource'
  obtain
      ⟨frameCode, bodyCtx, bodyCode,
        hFrame, hBody, hAfterAllocatorCode⟩ :=
    Locals.Block.compileOpen_append_components
      (left := artifact.components.framePrelude)
      (right := artifact.components.lowered.stmts)
      hAfterAllocator
  obtain ⟨cleanup, hCleanup, hBodyOutput⟩ :=
    Locals.finishScoped_components hFinish
  have hOutput :
      expressions.body =
        { stmts :=
            sourceCode ++ allocatorCode ++ frameCode ++ bodyCode ++
              Locals.codeStmt cleanup } := by
    calc
      expressions.body =
          { stmts := openCode ++ Locals.codeStmt cleanup } :=
        hBodyOutput
      _ =
          { stmts :=
              sourceCode ++ allocatorCode ++ frameCode ++ bodyCode ++
                Locals.codeStmt cleanup } := by
        simp [hOpenCode, hAfterSourceCode, hAfterAllocatorCode,
          List.append_assoc]
  have hBody' :
      Locals.Block.compileOpen bodyCtx artifact.components.lowered =
        some (bodyCode, finalCtx) := by
    cases hLowered : artifact.components.lowered with
    | mk stmts =>
        change Locals.Block.compileOpen bodyCtx { stmts := stmts } =
          some (bodyCode, finalCtx)
        simpa [hLowered] using hBody
  exact
    ⟨{ sourceCode := sourceCode
       sourceCtx := sourceCtx
       allocatorCode := allocatorCode
       allocatorCtx := allocatorCtx
       frameCode := frameCode
       bodyCtx := bodyCtx
       bodyCode := bodyCode
       finalCtx := finalCtx
       cleanup := cleanup
       compileSource := hSource
       compileAllocator := hAllocator
       compileFrame := hFrame
       compileBody := hBody'
       cleanupCode := hCleanup
       output := hOutput }⟩

theorem MainArtifact.frameName_not_mem_final_env
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) :
    compilation.frameName ∉ artifact.final.allocation.env.map Prod.fst := by
  rw [artifact.finalPlan]
  have hFresh :=
    AllocationLowering.freshFrameName_not_mem_allSourceNames
      compilation.fresh
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  intro hFrame
  apply hFresh
  simp only [AllocationLowering.allSourceNames, List.mem_append,
    List.mem_flatMap]
  apply Or.inr
  refine
    ⟨compilation.recipe,
      by simp [hRecipe],
      { scope := .main, state := compilation.recipe.main },
      ?_, hFrame⟩
  simp [AllocationLowering.scopedStates]

/--
The owner-neutral main root together with the pass outputs needed by the
whole-program composition theorem.
-/
structure MainRoot
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    (prepared : MainPrepared artifact) where
  root : AllocationObserverForward.BodyCursor.RootArtifact compilation
  sourceBlock :
    root.sourceBlock = { stmts := artifact.components.rest }
  startState : root.startState = artifact.start
  startLocals : root.startLocals = prepared.bodyCtx
  finalState : root.finalState = artifact.final
  finalLocals : root.finalLocals = prepared.finalCtx
  lowered : root.lowered = artifact.components.lowered
  compiled : root.compiled = prepared.bodyCode
  lowerCtx : root.lowerCtx = artifact.lowerCtx
  plan : root.plan = artifact.plan

/--
Construct the distinguished main body as an owner-neutral recursive root.

All planning, lowering, compilation, freshness, and source-scope evidence is
derived from the existing compiler artifacts. The only semantic premise is
the ordinary whole-program scoping judgment.
-/
theorem MainPrepared.rootArtifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    (prepared : MainPrepared artifact)
    (hProgramScoped : program.Scoped) :
    Nonempty (MainRoot prepared) := by
  obtain ⟨sourcePrefix, hSourceBody, hPrelude⟩ :=
    AllocationLowering.splitPrelude_components artifact.components.split
  have hSourceBlock :
      program.body =
        { stmts := sourcePrefix ++ artifact.components.rest } := by
    exact block_eq_of_stmts_eq hSourceBody
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  obtain
      ⟨mainPlan, hMainPlan, hMainAllocation, _hFrameWords,
        hMainScopes⟩ :=
    AllocationSupport.planRecipeCore?_main hRecipe
  let initialPlanning : AllocationSupport.PlanningState :=
    {
      allocation :=
        { env := []
          nextSlot := compilation.recipe.stateAfterFunctions.nextSlot }
      nextScope := 0
      scopes := []
    }
  have hMainPlan' :
      AllocationSupport.planBlockOpen .main initialPlanning
          { stmts := artifact.components.rest } =
        mainPlan := by
    have hWhole :
        AllocationSupport.planBlockOpen .main initialPlanning
            { stmts := sourcePrefix ++ artifact.components.rest } =
          mainPlan := by
      rw [← hSourceBlock]
      simpa [initialPlanning] using hMainPlan
    rw [hPrelude.planBlockOpen_append] at hWhole
    exact hWhole
  have hRestScoped :
      Functions.Scope.Block.Scoped [] { stmts := artifact.components.rest } := by
    apply hPrelude.scopedTail
    change
      Functions.Scope.StmtList.Scoped []
        (sourcePrefix ++ artifact.components.rest)
    have hBodyScoped := hProgramScoped.2
    rw [hSourceBlock] at hBodyScoped
    exact hBodyScoped
  let emptySlots : AllocationSupport.FunSlots :=
    { name := ""
      params := []
      returns := [] }
  refine
    ⟨{
      root := {
        functionRoot? := none
        rootScope := .main
        slots := emptySlots
        returns := []
        sourceBlock := { stmts := artifact.components.rest }
        startState := artifact.start
        startLocals := prepared.bodyCtx
        planning := initialPlanning
        planningAllocation := by
          rfl
        rootScopeOwner := rfl
        plan := artifact.plan
        planWF := artifact.planWF
        finalState := artifact.final
        finalLocals := prepared.finalCtx
        planEq := by
          simp [MainArtifact.plan, artifact.finalPlan]
        finalFrameFresh := artifact.frameName_not_mem_final_env
        lexicalFrameFresh := by
          intro entry hEntry
          have hFresh :=
            AllocationLowering.freshFrameName_not_mem_allSourceNames
              compilation.fresh
          have hRecipe :
              AllocationSupport.planRecipeCore? program =
                some compilation.recipe :=
            (AllocationLowering.validatePlan?_eq_some_exact
              compilation.validate).2.2.1
          intro hFrame
          apply hFresh
          simp only [AllocationLowering.allSourceNames, List.mem_append,
            List.mem_flatMap]
          apply Or.inr
          refine
            ⟨compilation.recipe, by simp [hRecipe], entry, ?_, hFrame⟩
          simp [AllocationLowering.scopedStates, hEntry]
        scopeStackEntries := by
          intro scope state added hRoot hEnv
          simp [MixedAllocation.AllocationRecipe.stackEntriesForScope,
            hRoot, hEnv, AllocationSupport.functionEnv, emptySlots,
            MixedAllocation.stackEntries, List.filter_append,
            List.take_append]
        plannedFinal := by
          rw [hMainPlan', hMainAllocation, artifact.finalPlan]
        plannedScopes := by
          intro entry hEntry
          apply hMainScopes
          rw [hMainPlan'] at hEntry
          exact hEntry
        lowered := artifact.components.lowered
        compiled := prepared.bodyCode
        lowerCtx := artifact.lowerCtx
        lowerCtxShared :=
          compilation.lowerCtx_shared .main
            (AllocationLowering.mainScratchBindings
              compilation.recipe compilation.stackSlots)
        lower := artifact.lowerRest
        compile := prepared.compileBody
        sourceScoped := by
          simpa [emptySlots] using hRestScoped
        activeEnv := by
          refine ⟨[], ?_, ?_⟩
          · rfl
          · simp [emptySlots]
      }
      sourceBlock := rfl
      startState := rfl
      startLocals := rfl
      finalState := rfl
      finalLocals := rfl
      lowered := rfl
      compiled := rfl
      lowerCtx := rfl
      plan := rfl
    }⟩

end AllocationObserverProgram
end Functions
end EvmCompiler
