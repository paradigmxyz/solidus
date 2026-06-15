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

namespace SourcePrelude

/--
Forward preservation for the compiler-owned no-variable source prelude.

The proof consumes the ordinary allocation expression lowerer and Locals
compiler through `compileNoVarExprCode?_of_lowerExpr`. It does not execute the
prelude compiler as a separate semantics.
-/
theorem forward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {sourcePrefix : List Functions.Stmt}
    {loweredPrefix : List Locals.Stmt}
    (hPrelude :
      AllocationLowering.PreludeLowered sourcePrefix loweredPrefix)
    {compiledPrefix : List Expressions.Stmt}
    {finalLocals : Locals.Ctx}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {frameBase : Nat}
    {transcript : Trace}
    {sourceCtx finalSourceCtx : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredPrefix } =
        some (compiledPrefix, finalLocals))
    (hSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel { stmts := sourcePrefix } source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            finalSourceCtx))
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        program.memoryContract lowerCtx lowerState localsCtx plan []
        frameBase .stack source target) :
    ∃ targetFinal targetFuel,
      finalLocals = localsCtx ∧
        finalSourceCtx = sourceCtx ∧
        Structured.ObserverSemantics.Block.Eval
          expressions.toStructured targetFuel
          { stmts :=
              Expressions.StmtList.toStructured compiledPrefix }
          target
          (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
        AllocationObserverContext.ActivationInvariant
          program.memoryContract lowerCtx lowerState localsCtx plan []
          frameBase .stack sourceFinal targetFinal := by
  induction hPrelude generalizing compiledPrefix finalLocals sourceFuel
      source sourceFinal target finalSourceCtx with
  | nil =>
      have hCompiled :
          ([], localsCtx) = (compiledPrefix, finalLocals) := by
        simpa [Locals.Block.compileOpen] using hCompile
      have hCompiledPrefix := congrArg Prod.fst hCompiled
      have hFinalLocals := congrArg Prod.snd hCompiled
      simp only [Prod.fst] at hCompiledPrefix
      simp only [Prod.snd] at hFinalLocals
      subst compiledPrefix
      subst finalLocals
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Block.runOpen,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ fuel =>
          have hSourcePair :
              (Functions.Source.Effectful.Outcome.regular source,
                  sourceCtx) =
                (Functions.Source.Effectful.Outcome.regular sourceFinal,
                  finalSourceCtx) := by
            simpa [Functions.Source.Effectful.Block.runOpen] using hSource
          cases hSourcePair
          exact
            ⟨target, 1, rfl, rfl,
              Structured.EffectSemantics.Block.Eval.nil, hInvariant⟩
  | @cons stmt rest code lowered head tail ih =>
      cases stmt with
      | expr expr =>
          have hNoVar :
              AllocationSupport.compileNoVarExprCode? expr = some code := by
            cases hActual :
                AllocationSupport.compileNoVarExprCode? expr with
            | none =>
                simp [AllocationSupport.compilePreludeStmt?, hActual] at head
            | some actual =>
                have hCode : actual = code := by
                  simpa [AllocationSupport.compilePreludeStmt?, hActual] using
                    head
                subst actual
                rfl
          cases hTailCompile :
              Locals.Block.compileOpen localsCtx
                { stmts := lowered } with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.Expr.compileCode, Locals.codeStmt,
                hTailCompile] at hCompile
          | some tailResult =>
              rcases tailResult with ⟨compiledTail, tailLocals⟩
              have hCompiled :
                  (Expressions.Stmt.code code :: compiledTail,
                      tailLocals) =
                    (compiledPrefix, finalLocals) := by
                simpa [Locals.Block.compileOpen, Locals.Stmt.compile,
                  Locals.Expr.compileCode, Locals.codeStmt,
                  hTailCompile] using hCompile
              have hCompiledPrefix := congrArg Prod.fst hCompiled
              have hFinalLocals := congrArg Prod.snd hCompiled
              simp only [Prod.fst] at hCompiledPrefix
              simp only [Prod.snd] at hFinalLocals
              subst compiledPrefix
              subst finalLocals
              cases sourceFuel with
              | zero =>
                  simp [Functions.Source.Effectful.Block.runOpen,
                    Functions.Source.invalid, Structured.invalid] at hSource
              | succ fuel =>
                  cases hEval :
                      Functions.Source.Effectful.Expr.eval
                        (Functions.ObserverSemantics.stateModel transcript)
                        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                          program.memoryContract transcript)
                        expr source with
                  | error err =>
                      simp [Functions.Source.Effectful.Block.runOpen,
                        Functions.Source.Effectful.Stmt.run, hEval] at hSource
                  | ok evalResult =>
                      rcases evalResult with ⟨sourceHead, values⟩
                      have hTailSource :
                          Functions.Source.Effectful.Block.runOpen
                              (Functions.ObserverSemantics.stateModel
                                transcript)
                              (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                                program.memoryContract transcript)
                              program sourceCtx fuel
                              { stmts := rest } sourceHead =
                            .ok
                              (Functions.Source.Effectful.Outcome.regular
                                sourceFinal,
                                finalSourceCtx) := by
                        simpa [Functions.Source.Effectful.Block.runOpen,
                          Functions.Source.Effectful.Stmt.run, hEval] using
                          hSource
                      have hSafe :
                          AllocationObserverSafety.Expr.MemorySafeEval
                            program.memoryContract transcript expr source
                              sourceHead values :=
                        AllocationObserverSafety.Expr.MemorySafeEval.of_safe_eval
                          hEval
                      have hScoped :
                          Functions.Scope.ExprScoped [] expr :=
                        hSafe.scoped_of_compileNoVar hNoVar
                      obtain ⟨loweredExpr, hLowerExpr, hCompileExpr⟩ :=
                        AllocationLowering.compileNoVarExprCode?_of_lowerExpr
                          hNoVar lowerCtx lowerState localsCtx 0
                      obtain ⟨targetHead, hTargetHead, hHeadResult⟩ :=
                        AllocationObserverExpression.forwardExpr
                          (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
                            program.memoryContract)
                          hSafe hInvariant.compiler hScoped hLowerExpr
                          hCompileExpr hInvariant.state
                      have hHeadInvariant :
                          AllocationObserverContext.ActivationInvariant
                            program.memoryContract lowerCtx lowerState
                            localsCtx plan [] frameBase .stack
                            sourceHead targetHead :=
                        AllocationObserverExpression.Expr.invariant_zero
                          hInvariant hSafe hHeadResult
                      obtain
                          ⟨targetFinal, targetFuel, hTailLocals,
                            hTailCtx, hTargetTail, hFinalInvariant⟩ :=
                        ih hTailCompile hTailSource hHeadInvariant
                      subst tailLocals
                      subst finalSourceCtx
                      exact
                        ⟨targetFinal, targetFuel + 1, rfl, rfl,
                          Structured.EffectSemantics.Block.Eval.cons_regular
                            (Structured.EffectSemantics.Stmt.Eval.code
                              hTargetHead)
                            hTargetTail,
                          hFinalInvariant⟩
      | let_ name value | assign name value | block block
      | if_ cond block | switch scrutinee cases defaultBody
      | for_ init cond post loopBody | brk | cont | leave
      | call targets functionName args | terminal kind
      | terminalArgs kind args =>
          simp [AllocationSupport.compilePreludeStmt?] at head

end SourcePrelude

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

/--
The ordinary allocation lowerer determines whether the complete program is
stack-only or uses the concrete scratch-frame configuration embedded in the
compiler artifact.
-/
theorem MainArtifact.runtimeSelection
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) :
    artifact.components.RuntimeSelection :=
  artifact.components.runtimeSelection

def compilationResourceMode
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation :
      AllocationObserverForward.Compilation allocation program expressions) :
    AllocationObserverRelation.Frame.ResourceMode :=
  if AllocationLowering.mainNeedsAllocator
      compilation.recipe compilation.stackSlots then
    match compilation.frameConfig? with
    | none => .stackOnly
    | some config => .scratch config
  else
    .stackOnly

def MainArtifact.resourceMode
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (_artifact : MainArtifact compilation) :
    AllocationObserverRelation.Frame.ResourceMode :=
  compilationResourceMode compilation

/--
The semantic resource index is computed from the ordinary compiler artifact,
and its complete classification follows from successful main lowering.
-/
theorem MainArtifact.resourceMode_spec
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation) :
    (artifact.resourceMode = .stackOnly ∧
        AllocationLowering.mainNeedsAllocator
            compilation.recipe compilation.stackSlots =
          false ∧
        AllocationLowering.mainNeedsFrame
            compilation.recipe compilation.stackSlots =
          false ∧
        AllocationLowering.frameFunctions
            compilation.recipe compilation.stackSlots =
          [] ∧
        artifact.components.allocatorPrelude = [] ∧
        artifact.components.framePrelude = []) ∨
      ∃ config,
        artifact.resourceMode = .scratch config ∧
          compilation.frameConfig? = some config ∧
          AllocationLowering.mainNeedsAllocator
              compilation.recipe compilation.stackSlots =
            true := by
  cases artifact.runtimeSelection with
  | stackOnly hAllocator hFrame hFunctions hAllocatorPrelude
      hFramePrelude =>
      exact
        Or.inl
          ⟨by
              simp [MainArtifact.resourceMode,
                compilationResourceMode,
                hAllocator],
            hAllocator, hFrame, hFunctions, hAllocatorPrelude,
            hFramePrelude⟩
  | scratch config hConfig hAllocator =>
      exact
        Or.inr
          ⟨config,
            by
              simp [MainArtifact.resourceMode,
                compilationResourceMode,
                hAllocator, hConfig],
            hConfig, hAllocator⟩

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
  rootScope : root.rootScope = .main
  live :
    (root.slots.returns.map Prod.fst).reverse ++
        (root.slots.params.map Prod.fst).reverse =
      []
  returns : root.returns = []
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
      rootScope := rfl
      live := by simp [emptySlots]
      returns := rfl
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

namespace MainRoot

/--
The shared source/control constructor at the start of the allocation-lowered
main body.

Only the resource-indexed budget and activation invariant are supplied by the
adjacent setup theorem. Source scope and target control facts are derived here
from ordinary initial contexts and the real Locals compilation of the setup
prefix.
-/
private def boundaryFor
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    (mainRoot : MainRoot prepared)
    {resource : Frame.ResourceMode}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hBudget : resource.Budget allocatorDepth)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        resource program.memoryContract allocatorDepth mainRoot.root.lowerCtx
        mainRoot.root.startState mainRoot.root.startLocals mainRoot.root.plan
        ((mainRoot.root.slots.returns.map Prod.fst).reverse ++
          (mainRoot.root.slots.params.map Prod.fst).reverse)
        frameBase mode source target) :
    AllocationObserverDispatcher.BodyCursor.ResourceBoundary
      mainRoot.root.cursor
      (resource := resource) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := Functions.Source.Ctx.initial)
      (source := source) (target := target) := by
  have hSourceControl :=
    Locals.Block.compileOpen_sameControl prepared.compileSource
  have hAllocatorControl :=
    Locals.Block.compileOpen_sameControl prepared.compileAllocator
  have hFrameControl :=
    Locals.Block.compileOpen_sameControl prepared.compileFrame
  have hSetupControl :
      Locals.Ctx.SameControl Locals.Ctx.initial prepared.bodyCtx :=
    (hSourceControl.trans hAllocatorControl).trans hFrameControl
  refine
    { sourceScope := ?_
      control := ?_
      destinations := ?_
      returnFrame := ?_
      leaveTarget := ?_
      budget := hBudget
      invariant := hInvariant }
  · intro name
    rw [mainRoot.live]
    simp [Functions.Source.Ctx.initial]
  · constructor <;>
      simp [Functions.Source.Ctx.initial, mainRoot.returns, mainRoot.live]
  · refine
      { brk := .unavailable ?_ ?_
        cont := .unavailable ?_ ?_ }
    · rfl
    · change mainRoot.root.startLocals.breakDepth? = none
      rw [mainRoot.startLocals, ← hSetupControl.breakDepth]
      rfl
    · rfl
    · change mainRoot.root.startLocals.continueDepth? = none
      rw [mainRoot.startLocals, ← hSetupControl.continueDepth]
      rfl
  · intro functionScope hLeave
    simp [Functions.Source.Ctx.initial] at hLeave
  · intro functionScope hLeave
    simp [Functions.Source.Ctx.initial] at hLeave

/--
The canonical compiler-selected resource boundary for recursive main-body
preservation.
-/
def resourceBoundary
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    (mainRoot : MainRoot prepared)
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hBudget : artifact.resourceMode.Budget allocatorDepth)
    (hInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        artifact.resourceMode program.memoryContract allocatorDepth
        mainRoot.root.lowerCtx mainRoot.root.startState
        mainRoot.root.startLocals mainRoot.root.plan
        ((mainRoot.root.slots.returns.map Prod.fst).reverse ++
          (mainRoot.root.slots.params.map Prod.fst).reverse)
        frameBase mode source target) :
    AllocationObserverDispatcher.BodyCursor.ResourceBoundary
      mainRoot.root.cursor
      (resource := artifact.resourceMode)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (mode := mode) (sourceCtx := Functions.Source.Ctx.initial)
      (source := source) (target := target) :=
  mainRoot.boundaryFor hBudget hInvariant

/--
The existing scratch-backed boundary is the corresponding specialization of
the shared resource constructor.
-/
def boundary
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    (mainRoot : MainRoot prepared)
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hBudget : Frame.Budget config allocatorDepth)
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth mainRoot.root.lowerCtx
        mainRoot.root.startState mainRoot.root.startLocals mainRoot.root.plan
        ((mainRoot.root.slots.returns.map Prod.fst).reverse ++
          (mainRoot.root.slots.params.map Prod.fst).reverse)
        frameBase mode source target) :
    AllocationObserverDispatcher.BodyCursor.Boundary
      mainRoot.root.cursor
      (config := config) (allocatorDepth := allocatorDepth)
      (frameBase := frameBase) (mode := mode)
      (sourceCtx := Functions.Source.Ctx.initial)
      (source := source) (target := target) :=
  (mainRoot.boundaryFor (resource := .scratch config) hBudget
      (AllocationObserverContext.ActivationResourceInvariant.scratch
        hInvariant)).toScratch

/--
Instantiate the shared source-fuel theorem at the distinguished main root.
-/
theorem recursiveForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    (mainRoot : MainRoot prepared)
    {config : Frame.Config}
    {allocatorDepth frameBase maxDepth : Nat}
    {transcript : Trace}
    (fuelBound : Nat)
    (hProgramScoped : program.Scoped)
    (hFuelSafe : Frame.FuelSafe config maxDepth)
    (hDepthBound : allocatorDepth + fuelBound ≤ maxDepth)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config) :
    AllocationObserverDispatcher.BodyCursor.RecursiveBlockForward
      (root := mainRoot.root) (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (fuelBound := fuelBound) (transcript := transcript) :=
  AllocationObserverRecursive.BodyCursor.recursiveProgramForward
    (allocation := allocation) (program := program)
    (expressions := expressions) (transcript := transcript)
    maxDepth fuelBound hProgramScoped hFuelSafe hDepthBound hConfig

/--
Instantiate the compiler-selected resource recursion theorem at main.

Stack-only artifacts use the shared stack induction directly. Scratch-backed
artifacts reuse the existing allocator-aware induction and lift its result into
the same resource-indexed block interface.
-/
theorem resourceRecursiveForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    (mainRoot : MainRoot prepared)
    {allocatorDepth frameBase maxDepth : Nat}
    {transcript : Trace}
    (fuelBound : Nat)
    (hProgramScoped : program.Scoped)
    (hFuelSafe : artifact.resourceMode.FuelSafe maxDepth)
    (hDepthBound : allocatorDepth + fuelBound ≤ maxDepth) :
    AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward
      (root := mainRoot.root) (resource := artifact.resourceMode)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (fuelBound := fuelBound) (transcript := transcript) := by
  rcases artifact.resourceMode_spec with hStack | hScratch
  · rcases hStack with
      ⟨hMode, _hAllocator, _hFrame, hFrameFunctions,
        _hAllocatorPrelude, _hFramePrelude⟩
    rw [hMode]
    exact
      AllocationObserverRecursive.BodyCursor.stackRecursiveBlockForward
        fuelBound hProgramScoped hFrameFunctions
  · rcases hScratch with
      ⟨config, hMode, hFrameConfig, _hAllocator⟩
    rw [hMode] at hFuelSafe
    have hConfig :
        AllocationSupport.scratchFrameConfig?
            program.memoryContract compilation.recipe.frameWords =
          some config := by
      simpa [AllocationObserverForward.Compilation.frameConfig?] using
        hFrameConfig
    have hScratchRecursive :
        AllocationObserverDispatcher.BodyCursor.RecursiveBlockForward
          (root := mainRoot.root) (config := config)
          (allocatorDepth := allocatorDepth) (frameBase := frameBase)
          (fuelBound := fuelBound) (transcript := transcript) :=
      mainRoot.recursiveForward fuelBound hProgramScoped hFuelSafe
        hDepthBound hConfig
    rw [hMode]
    intro scope live sourceBlock lowerState localsCtx mode sourceCtx finalCtx
      source target sourceFuel sourceOutcome cursor hFuel hBoundary hSource
    exact
      (hScratchRecursive cursor hFuel hBoundary.toScratch hSource).toResource

end MainRoot

/--
Construct the checked recursive main-body theorem without accepting any
compiler-generated evidence at the theorem boundary.
-/
theorem mainRecursiveForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation :
      AllocationObserverForward.Compilation allocation program expressions)
    {config : Frame.Config}
    {allocatorDepth frameBase maxDepth : Nat}
    {transcript : Trace}
    (fuelBound : Nat)
    (hProgramScoped : program.Scoped)
    (hFuelSafe : Frame.FuelSafe config maxDepth)
    (hDepthBound : allocatorDepth + fuelBound ≤ maxDepth)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config) :
    ∃ artifact : MainArtifact compilation,
      ∃ prepared : MainPrepared artifact,
        ∃ mainRoot : MainRoot prepared,
          AllocationObserverDispatcher.BodyCursor.RecursiveBlockForward
            (root := mainRoot.root) (config := config)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            (fuelBound := fuelBound) (transcript := transcript) := by
  obtain ⟨artifact⟩ := MainArtifact.ofCompilation compilation
  obtain ⟨prepared⟩ := MainPrepared.ofArtifact artifact
  obtain ⟨mainRoot⟩ := prepared.rootArtifact hProgramScoped
  exact
    ⟨artifact, prepared, mainRoot,
      mainRoot.recursiveForward fuelBound hProgramScoped hFuelSafe
        hDepthBound hConfig⟩

/--
Construct the checked compiler-selected recursive main-body theorem without
accepting generated artifacts or a resource-mode witness at the public
boundary.
-/
theorem mainResourceRecursiveForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation :
      AllocationObserverForward.Compilation allocation program expressions)
    {allocatorDepth frameBase maxDepth : Nat}
    {transcript : Trace}
    (fuelBound : Nat)
    (hProgramScoped : program.Scoped)
    (hFuelSafe :
      (compilationResourceMode compilation).FuelSafe maxDepth)
    (hDepthBound : allocatorDepth + fuelBound ≤ maxDepth) :
    ∃ artifact : MainArtifact compilation,
      ∃ prepared : MainPrepared artifact,
        ∃ mainRoot : MainRoot prepared,
          AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward
            (root := mainRoot.root) (resource := artifact.resourceMode)
            (allocatorDepth := allocatorDepth) (frameBase := frameBase)
            (fuelBound := fuelBound) (transcript := transcript) := by
  obtain ⟨artifact⟩ := MainArtifact.ofCompilation compilation
  obtain ⟨prepared⟩ := MainPrepared.ofArtifact artifact
  obtain ⟨mainRoot⟩ := prepared.rootArtifact hProgramScoped
  exact
    ⟨artifact, prepared, mainRoot,
      mainRoot.resourceRecursiveForward fuelBound hProgramScoped
        (by simpa [MainArtifact.resourceMode] using hFuelSafe)
        hDepthBound⟩

end AllocationObserverProgram
end Functions
end EvmCompiler
