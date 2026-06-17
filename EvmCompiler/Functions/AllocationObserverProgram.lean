import EvmCompiler.Functions.AllocationObserverRecursive

namespace EvmCompiler
namespace Functions
namespace AllocationObserverProgram

open AllocationObserverRelation
open AllocationObserverForward

abbrev Trace := Assembly.ResourceTrace

structure InitialRel
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (source : Functions.ObserverSemantics.State transcript)
    (target : Structured.ObserverSemantics.State transcript) : Prop where
  cursor : source.cursor = target.cursor
  shared :
    AllocationObserverRelation.SharedRel
      contract source.source.shared target.source.evm.toSharedState
  stack : target.source.evm.stack = []
  activeNoWrap :
    target.source.evm.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size

structure FinalStateRel
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (source : Functions.ObserverSemantics.State transcript)
    (target : Structured.ObserverSemantics.State transcript) : Prop where
  cursor : source.cursor = target.cursor
  shared :
    AllocationObserverRelation.SharedRel
      contract source.source.shared target.source.evm.toSharedState

inductive OutcomeRel
    {transcript : Trace}
    (contract : MemoryContract.Contract) :
    Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript) →
      Structured.ObserverSemantics.Outcome
        (transcript := transcript) → Prop where
  | regular
      {source : Functions.ObserverSemantics.State transcript}
      {target : Structured.ObserverSemantics.State transcript}
      (state : FinalStateRel contract source target)
      (stack : target.source.evm.stack = []) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.regular source)
        (Structured.EffectSemantics.Outcome.regular target)
  | brk
      {source : Functions.ObserverSemantics.State transcript}
      {target : Structured.ObserverSemantics.State transcript}
      (state : FinalStateRel contract source target) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.brk source)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont
      {source : Functions.ObserverSemantics.State transcript}
      {target : Structured.ObserverSemantics.State transcript}
      (state : FinalStateRel contract source target) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.cont source)
        (Structured.EffectSemantics.Outcome.cont target)
  | leave
      {source : Functions.ObserverSemantics.State transcript}
      {target : Structured.ObserverSemantics.State transcript}
      (state : FinalStateRel contract source target) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.leave source)
        (Structured.EffectSemantics.Outcome.leave target)
  | halt
      (kind : Assembly.HaltKind)
      {source : Functions.ObserverSemantics.State transcript}
      {target : Structured.ObserverSemantics.State transcript}
      (state : FinalStateRel contract source target) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.halt kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

namespace FinalStateRel

theorem of_activationOutcome
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      AllocationObserverRelation.ActivationOutcomeRel
        contract plan live stackOffset frameBase mode
        sourceOutcome targetOutcome) :
    FinalStateRel contract sourceOutcome.state targetOutcome.state := by
  cases hRel with
  | regular hState | brk hState | cont hState =>
      exact
        { cursor := hState.base.cursor
          shared :=
            { machine := hState.base.core.machine
              world := hState.base.core.world } }
  | leave hState =>
      exact
        { cursor := hState.cursor
          shared := hState.shared }
  | halt kind hState =>
      exact
        { cursor := hState.cursor
          shared := hState.shared }

theorem after_cleanup_empty
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hRel : FinalStateRel contract source target)
    (hCursor : targetFinal.cursor = target.cursor)
    (hShared :
      targetFinal.source.evm.toSharedState =
        target.source.evm.toSharedState) :
    FinalStateRel contract
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        [] source)
      targetFinal := by
  refine
    { cursor := ?_
      shared := ?_ }
  · simpa [Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.restrictTo,
      Simulation.ResourceReplay.State.withSource] using
        hRel.cursor.trans hCursor.symm
  · refine
      { machine := ?_
        world := ?_ }
    · simpa [Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.restrictTo,
        Simulation.ResourceReplay.State.withSource, hShared] using
          hRel.shared.machine
    · simpa [Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.restrictTo,
        Simulation.ResourceReplay.State.withSource, hShared] using
          hRel.shared.world

end FinalStateRel

namespace OutcomeRel

theorem of_nonregular_activation
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hRel :
      AllocationObserverRelation.ActivationOutcomeRel
        contract plan live stackOffset frameBase mode
        sourceOutcome targetOutcome)
    (hMode : sourceOutcome.mode ≠ .regular) :
    OutcomeRel contract sourceOutcome targetOutcome := by
  cases hRel with
  | regular _ =>
      exact False.elim (hMode rfl)
  | brk hState =>
      exact .brk (FinalStateRel.of_activationOutcome (.brk hState))
  | cont hState =>
      exact .cont (FinalStateRel.of_activationOutcome (.cont hState))
  | leave hState =>
      exact
        .leave
          { cursor := hState.cursor
            shared := hState.shared }
  | halt kind hState =>
      exact
        .halt kind
          { cursor := hState.cursor
            shared := hState.shared }

end OutcomeRel

def closeOutcome
    {transcript : Trace}
    (outcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)) :
    Functions.ObserverSemantics.Outcome
      (Functions.ObserverSemantics.State transcript) :=
  if outcome.mode = .regular then
    Functions.Source.Effectful.Outcome.regular
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        [] outcome.state)
  else
    outcome

private theorem sourceOutcome_eq_regular_of_mode
    {transcript : Trace}
    {outcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hMode : outcome.mode = .regular) :
    outcome =
      Functions.Source.Effectful.Outcome.regular outcome.state := by
  cases outcome with
  | mk state mode =>
      cases hMode
      rfl

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

/--
Split a successful real source run at the compiler-owned no-variable prelude.

Every accepted prelude statement is an expression statement, so successful
execution of the whole block forces the prefix to finish regularly and exposes
the exact remaining open-block run.
-/
theorem splitOpen
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {sourcePrefix : List Functions.Stmt}
    {loweredPrefix : List Locals.Stmt}
    (hPrelude :
      AllocationLowering.PreludeLowered sourcePrefix loweredPrefix)
    {rest : List Functions.Stmt}
    {transcript : Trace}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {sourceFuel : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel
          { stmts := sourcePrefix ++ rest } source =
        .ok (sourceOutcome, finalCtx)) :
    ∃ mid midCtx prefixFuel tailFuel,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx prefixFuel
          { stmts := sourcePrefix } source =
        .ok
          (Functions.Source.Effectful.Outcome.regular mid, midCtx) ∧
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program midCtx tailFuel { stmts := rest } mid =
        .ok (sourceOutcome, finalCtx) ∧
      tailFuel ≤ sourceFuel := by
  induction hPrelude generalizing sourceFuel source sourceOutcome finalCtx
      sourceCtx with
  | nil =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Block.runOpen,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ fuel =>
          exact
            ⟨source, sourceCtx, fuel + 1, fuel + 1,
              by simp [Functions.Source.Effectful.Block.runOpen],
              by simpa using hSource, Nat.le_refl _⟩
  | @cons stmt prefixRest code lowered head tail ih =>
      cases stmt with
      | expr expr =>
          cases sourceFuel with
          | zero =>
              simp [Functions.Source.Effectful.Block.runOpen,
                Functions.Source.invalid, Structured.invalid] at hSource
          | succ fuel =>
              rcases
                  Functions.Source.Effectful.Block.runOpen_cons_cases
                    (Functions.ObserverSemantics.stateModel transcript)
                    (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                      program.memoryContract transcript)
                    program hSource with
                hRegular | hNonregular
              · rcases hRegular with
                  ⟨headFinal, headCtx, hHead, hTailSource⟩
                obtain
                    ⟨mid, midCtx, prefixFuel, tailFuel,
                      hPrefix, hTail, hTailFuel⟩ :=
                  ih hTailSource
                obtain ⟨combinedFuel, hCombined⟩ :=
                  Functions.Source.Effectful.Block.runOpen_cons_regular_exists
                    (Functions.ObserverSemantics.stateModel transcript)
                    (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                      program.memoryContract transcript)
                    program hHead hPrefix
                exact
                  ⟨mid, midCtx, combinedFuel, tailFuel,
                    hCombined, hTail, hTailFuel.trans (by omega)⟩
              · rcases hNonregular with
                  ⟨headOutcome, headCtx, hHead, hMode,
                    _hOutcome, _hCtx⟩
                cases hEval :
                    Functions.Source.Effectful.Expr.eval
                      (Functions.ObserverSemantics.stateModel transcript)
                      (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                        program.memoryContract transcript)
                      expr source with
                | error err =>
                    simp [Functions.Source.Effectful.Stmt.run, hEval]
                      at hHead
                | ok evalResult =>
                    rcases evalResult with ⟨headFinal, values⟩
                    have hPair :
                        (Functions.Source.Effectful.Outcome.regular headFinal,
                            sourceCtx) =
                          (headOutcome, headCtx) := by
                      simpa [Functions.Source.Effectful.Stmt.run, hEval] using
                        hHead
                    have hRegularMode :
                        headOutcome.mode = .regular := by
                      simpa using
                        (congrArg
                          (fun result => result.1.mode) hPair).symm
                    exact False.elim (hMode hRegularMode)
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

/--
Public compiler-selected resource mode, computed directly from the source
program and requested allocation plan.
-/
def selectedResourceMode
    (allocation : Locals.Allocation.ProgramPlan)
    (program : Functions.Program) :
    AllocationObserverRelation.Frame.ResourceMode :=
  match AllocationLowering.validatePlan? allocation program with
  | none => .stackOnly
  | some (recipe, stackSlots) =>
      if AllocationLowering.mainNeedsAllocator recipe stackSlots then
        match AllocationSupport.scratchFrameConfig?
            program.memoryContract recipe.frameWords with
        | none => .stackOnly
        | some config => .scratch config
      else
        .stackOnly

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

theorem selectedResourceMode_eq_compilation
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation :
      AllocationObserverForward.Compilation allocation program expressions) :
    selectedResourceMode allocation program =
      compilationResourceMode compilation := by
  simp [selectedResourceMode, compilationResourceMode,
    compilation.validate,
    AllocationObserverForward.Compilation.frameConfig?]

theorem selectedResourceMode_fuelSafe_of_recipe_capacity
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {recipe : AllocationSupport.AllocationRecipe}
    {reservation : MemoryContract.ScratchReservation}
    {fuel : Nat}
    (hRecipe :
      AllocationSupport.planRecipeCore? program = some recipe)
    (hReservation :
      program.memoryContract.scratch? = some reservation)
    (hCapacity :
      (fuel + 1) * recipe.frameWords ≤ reservation.usableWords) :
    (selectedResourceMode allocation program).FuelSafe fuel := by
  cases hValidate :
      AllocationLowering.validatePlan? allocation program with
  | none =>
      simp [selectedResourceMode, hValidate,
        AllocationObserverRelation.Frame.ResourceMode.FuelSafe,
        AllocationObserverRelation.Frame.ResourceMode.Budget]
  | some validated =>
      rcases validated with ⟨validatedRecipe, stackSlots⟩
      have hValidatedCore :
          AllocationSupport.planRecipeCore? program =
            some validatedRecipe :=
        (AllocationLowering.validatePlan?_eq_some_exact
          hValidate).2.2.1
      have hRecipeEq : validatedRecipe = recipe :=
        Option.some.inj (hValidatedCore.symm.trans hRecipe)
      subst validatedRecipe
      by_cases hNeeds :
          AllocationLowering.mainNeedsAllocator recipe stackSlots = true
      · cases hConfig :
          AllocationSupport.scratchFrameConfig?
            program.memoryContract recipe.frameWords with
        | none =>
            simp [selectedResourceMode, hValidate, hNeeds, hConfig,
              AllocationObserverRelation.Frame.ResourceMode.FuelSafe,
              AllocationObserverRelation.Frame.ResourceMode.Budget]
        | some config =>
            simpa [selectedResourceMode, hValidate, hNeeds, hConfig,
              AllocationObserverRelation.Frame.ResourceMode.FuelSafe,
              AllocationObserverRelation.Frame.ResourceMode.Budget] using
              (AllocationObserverRelation.Frame.fuelSafe_of_scratchFrameConfig?_of_capacity
                hConfig hReservation hCapacity)
      · have hNoNeeds :
            AllocationLowering.mainNeedsAllocator recipe stackSlots =
              false :=
          Bool.eq_false_of_not_eq_true hNeeds
        simp [selectedResourceMode, hValidate, hNoNeeds,
          AllocationObserverRelation.Frame.ResourceMode.FuelSafe,
          AllocationObserverRelation.Frame.ResourceMode.Budget]

theorem selectedResourceMode_fuelSafe_of_no_scratch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {fuel : Nat}
    (hNoScratch : program.memoryContract.scratch? = none) :
    (selectedResourceMode allocation program).FuelSafe fuel := by
  cases hValidate :
      AllocationLowering.validatePlan? allocation program with
  | none =>
      simp [selectedResourceMode, hValidate,
        AllocationObserverRelation.Frame.ResourceMode.FuelSafe,
        AllocationObserverRelation.Frame.ResourceMode.Budget]
  | some validated =>
      rcases validated with ⟨recipe, stackSlots⟩
      by_cases hNeeds :
          AllocationLowering.mainNeedsAllocator recipe stackSlots = true
      · simp [selectedResourceMode, hValidate, hNeeds,
          AllocationSupport.scratchFrameConfig?, hNoScratch,
          AllocationObserverRelation.Frame.ResourceMode.FuelSafe,
          AllocationObserverRelation.Frame.ResourceMode.Budget]
      · have hNoNeeds :
            AllocationLowering.mainNeedsAllocator recipe stackSlots =
              false :=
          Bool.eq_false_of_not_eq_true hNeeds
        simp [selectedResourceMode, hValidate, hNoNeeds,
          AllocationObserverRelation.Frame.ResourceMode.FuelSafe,
          AllocationObserverRelation.Frame.ResourceMode.Budget]

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

/--
Allocation-lowering state before compiler-owned allocator/frame setup.

The source prelude has no local bindings, so its adjacent preservation theorem
uses this empty layout. Main-frame setup then establishes `MainArtifact.start`.
-/
def MainArtifact.beforeSetup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (_artifact : MainArtifact compilation) :
    AllocationLowering.State :=
  { allocation :=
      { env := []
        nextSlot := compilation.recipe.stateAfterFunctions.nextSlot }
    layout := [] }

/--
Every source-facing initial relation instantiates the empty compiler activation
for any checked main allocation artifact.
-/
theorem InitialRel.invariant
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    (artifact : MainArtifact compilation)
    {transcript : Trace}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hInitial :
      InitialRel program.memoryContract source target) :
    AllocationObserverContext.ActivationInvariant
      program.memoryContract artifact.lowerCtx artifact.beforeSetup
      Locals.Ctx.initial artifact.plan [] 0 .stack source target := by
  refine
    { compiler := ?_
      planWF := artifact.planWF
      defined := ?_
      state := ?_
      stackLength := ?_ }
  · apply
      AllocationObserverContext.ActivationExprContext.stack_of_layout
        artifact.planWF
    · rfl
    · simp [AllocationObserverRelation.currentStackOrder,
        MainArtifact.beforeSetup]
    · simp [MainArtifact.beforeSetup]
    · intro name slot hLive _hLocation
      simp at hLive
    · intro name hLive
      simp at hLive
    · intro name hLive
      simp at hLive
  · intro name hLive
    simp at hLive
  · exact
      .stack
        (by
          intro name slot hLive _hLocation
          simp at hLive)
        hInitial.activeNoWrap
        { cursor := hInitial.cursor
          core :=
            { machine := hInitial.shared.machine
              world := hInitial.shared.world
              store := by
                intro name location hLive _hLocation
                simp at hLive } }
  · rw [hInitial.stack]
    rfl

/--
Number of scratch frames owned when execution reaches the lowered main body.
-/
def mainSetupDepth
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation :
      AllocationObserverForward.Compilation allocation program expressions) :
    Nat :=
  if AllocationLowering.mainNeedsFrame
      compilation.recipe compilation.stackSlots then
    1
  else
    0

/--
Public compiler-selected number of scratch frames owned at main-body entry.
-/
def selectedMainSetupDepth
    (allocation : Locals.Allocation.ProgramPlan)
    (program : Functions.Program) : Nat :=
  match AllocationLowering.validatePlan? allocation program with
  | none => 0
  | some (recipe, stackSlots) =>
      if AllocationLowering.mainNeedsFrame recipe stackSlots then 1 else 0

theorem selectedMainSetupDepth_eq_compilation
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation :
      AllocationObserverForward.Compilation allocation program expressions) :
    selectedMainSetupDepth allocation program =
      mainSetupDepth compilation := by
  simp [selectedMainSetupDepth, mainSetupDepth, compilation.validate]

theorem selectedMainSetupDepth_le_one
    (allocation : Locals.Allocation.ProgramPlan)
    (program : Functions.Program) :
    selectedMainSetupDepth allocation program ≤ 1 := by
  cases hValidate :
      AllocationLowering.validatePlan? allocation program with
  | none =>
      simp [selectedMainSetupDepth, hValidate]
  | some validated =>
      rcases validated with ⟨recipe, stackSlots⟩
      by_cases hNeeds :
          AllocationLowering.mainNeedsFrame recipe stackSlots = true
      · simp [selectedMainSetupDepth, hValidate, hNeeds]
      · have hNoNeeds :
            AllocationLowering.mainNeedsFrame recipe stackSlots = false :=
          Bool.eq_false_of_not_eq_true hNeeds
        simp [selectedMainSetupDepth, hValidate, hNoNeeds]

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

namespace MainSetup

/--
Execute the allocator and optional main-frame setup emitted by the ordinary
allocation and Locals passes.

The result is the exact compiler-selected resource invariant consumed by the
recursive main-body theorem. No observer-specific compiler, generated-code
premise, replay certificate, or call oracle appears in the interface.
-/
theorem forward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    (prepared : MainPrepared artifact)
    {transcript : Trace}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hSourceCtx : prepared.sourceCtx = Locals.Ctx.initial)
    (hInvariant :
      AllocationObserverContext.ActivationInvariant
        program.memoryContract artifact.lowerCtx artifact.beforeSetup
        Locals.Ctx.initial artifact.plan [] 0 .stack source target) :
    ∃ frameBase mode targetFinal targetFuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured targetFuel
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.allocatorCode ++ prepared.frameCode) }
        target
        (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      AllocationObserverContext.ActivationResourceInvariant
        artifact.resourceMode program.memoryContract
        (mainSetupDepth compilation) artifact.lowerCtx artifact.start
        prepared.bodyCtx artifact.plan [] frameBase mode source
        targetFinal := by
  rcases artifact.resourceMode_spec with hStack | hScratch
  · rcases hStack with
      ⟨hMode, hNoAllocator, hNoFrame, _hFunctions,
        _hAllocatorPrelude, _hFramePrelude⟩
    have hAllocatorExpected :=
      artifact.components.compileAllocator_of_no_allocator
        hNoAllocator prepared.sourceCtx
    have hAllocatorPair :
        (prepared.allocatorCode, prepared.allocatorCtx) =
          ([], prepared.sourceCtx) :=
      Option.some.inj
        (prepared.compileAllocator.symm.trans hAllocatorExpected)
    have hAllocatorCode := congrArg Prod.fst hAllocatorPair
    have hAllocatorCtx := congrArg Prod.snd hAllocatorPair
    simp only [Prod.fst] at hAllocatorCode
    simp only [Prod.snd] at hAllocatorCtx
    have hFrameExpected :=
      artifact.components.compileFrame_of_no_frame
        hNoFrame prepared.allocatorCtx
    have hFramePair :
        (prepared.frameCode, prepared.bodyCtx) =
          ([], prepared.allocatorCtx) :=
      Option.some.inj
        (prepared.compileFrame.symm.trans hFrameExpected)
    have hFrameCode := congrArg Prod.fst hFramePair
    have hBodyCtx := congrArg Prod.snd hFramePair
    simp only [Prod.fst] at hFrameCode
    simp only [Prod.snd] at hBodyCtx
    have hStart :
        artifact.start = artifact.beforeSetup := by
      simp [MainArtifact.start, MainArtifact.beforeSetup,
        AllocationLowering.mainStartWithFrame, hNoFrame]
    have hBodyCtxInitial :
        prepared.bodyCtx = Locals.Ctx.initial := by
      rw [hBodyCtx, hAllocatorCtx, hSourceCtx]
    have hActivation :
        AllocationObserverContext.ActivationInvariant
          program.memoryContract artifact.lowerCtx artifact.start
          prepared.bodyCtx artifact.plan [] 0 .stack source target := by
      rw [hStart, hBodyCtxInitial]
      exact hInvariant
    refine
      ⟨0, .stack, target, 1, ?_,
        ?_⟩
    · simpa [hAllocatorCode, hFrameCode,
        Expressions.StmtList.toStructured] using
          (Structured.EffectSemantics.Block.Eval.nil
            (program := expressions.toStructured) (state := target))
    · rw [hMode]
      simpa [mainSetupDepth, hNoFrame] using
        (AllocationObserverContext.ActivationResourceInvariant.stackOnly
          (allocatorDepth := 0) hActivation rfl)
  · rcases hScratch with
      ⟨config, hMode, hFrameConfig, hNeedsAllocator⟩
    have hConfig :
        AllocationSupport.scratchFrameConfig?
            program.memoryContract compilation.recipe.frameWords =
          some config := by
      simpa [AllocationObserverForward.Compilation.frameConfig?] using
        hFrameConfig
    have hAllocatorExpected :=
      artifact.components.compileAllocator_of_scratch
        hFrameConfig hNeedsAllocator prepared.sourceCtx
    have hAllocatorPair :
        (prepared.allocatorCode, prepared.allocatorCtx) =
          ([Expressions.Stmt.code
              (AllocationSupport.scratchAllocatorInitCode config)],
            prepared.sourceCtx) :=
      Option.some.inj
        (prepared.compileAllocator.symm.trans hAllocatorExpected)
    have hAllocatorCode := congrArg Prod.fst hAllocatorPair
    have hAllocatorCtx := congrArg Prod.snd hAllocatorPair
    simp only [Prod.fst] at hAllocatorCode
    simp only [Prod.snd] at hAllocatorCtx
    obtain
        ⟨targetAfterInit, hInitRun, hInitRel, hInitReady, hInitStack⟩ :=
      AllocationObserverPreservation.Frame.allocatorInit_forward
        hInvariant.state.base hConfig hInvariant.state.activeNoWrap
    by_cases hNeedsFrame :
        AllocationLowering.mainNeedsFrame
            compilation.recipe compilation.stackSlots =
          true
    · have hFrameExpected :=
        artifact.components.compileFrame_of_scratch
          hFrameConfig hNeedsFrame prepared.allocatorCtx
      have hFramePair :
          (prepared.frameCode, prepared.bodyCtx) =
            ([Expressions.Stmt.code
                (AllocationSupport.scratchFrameAcquireCode config ++
                  Locals.bindLocals 0
                    (compilation.frameName ::
                      prepared.allocatorCtx.layout)),
              Expressions.Stmt.code
                (AllocationSupport.bindScratchBindingsCode 0
                  (AllocationLowering.mainScratchBindings
                    compilation.recipe compilation.stackSlots))],
              prepared.allocatorCtx.withLayout
                (compilation.frameName ::
                  prepared.allocatorCtx.layout)) :=
        Option.some.inj
          (prepared.compileFrame.symm.trans hFrameExpected)
      have hFrameCode := congrArg Prod.fst hFramePair
      have hBodyCtx := congrArg Prod.snd hFramePair
      simp only [Prod.fst] at hFrameCode
      simp only [Prod.snd] at hBodyCtx
      have hPositiveRecipe :
          0 < compilation.recipe.frameWords := by
        apply
          AllocationLowering.frameWords_pos_of_validate_of_rootNeedsFrame
            compilation.validate
        simpa [AllocationLowering.rootNeedsFrame,
          AllocationLowering.mainNeedsFrame,
          AllocationLowering.mainScratchBindings] using hNeedsFrame
      obtain
          ⟨_reservation, _hReservation, _hAllocator, _hFirst,
            _hLimit, hWords, _hWF, _hHost, _hReservationPositive,
            _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hConfig
      have hPositive : 0 < config.frameWords := by
        rw [hWords]
        exact hPositiveRecipe
      have hBudget :
          AllocationObserverRelation.Frame.Budget config 0 :=
        AllocationObserverRelation.Frame.budget_zero_of_scratchFrameConfig?
          hConfig
      obtain
          ⟨targetAfterFrame, hFrameRun, hFrameRel, hFrameReady,
            hFrameStack⟩ :=
        AllocationObserverPreservation.Frame.scratchFrameAcquire_empty_forward
          hConfig hPositive hBudget hInitReady hInitRel
      have hBindLocalsRun :
          Structured.ObserverSemantics.Code.run
              (Locals.bindLocals 0
                (compilation.frameName ::
                  prepared.allocatorCtx.layout))
              targetAfterFrame =
            .ok targetAfterFrame := by
        rfl
      have hFrameHeadRun :
          Structured.ObserverSemantics.Code.run
              (AllocationSupport.scratchFrameAcquireCode config ++
                Locals.bindLocals 0
                  (compilation.frameName ::
                    prepared.allocatorCtx.layout))
              targetAfterInit =
            .ok targetAfterFrame := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hFrameRun]
        simpa only [Except.bind] using hBindLocalsRun
      have hBindingsRun :
          Structured.ObserverSemantics.Code.run
              (AllocationSupport.bindScratchBindingsCode 0
                (AllocationLowering.mainScratchBindings
                  compilation.recipe compilation.stackSlots))
              targetAfterFrame =
            .ok targetAfterFrame :=
        AllocationObserverCall.EntryMarkers.run_bindScratchBindingsCode
          0
          (AllocationLowering.mainScratchBindings
            compilation.recipe compilation.stackSlots)
          targetAfterFrame
      have hTargetEval :
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured 4
            { stmts :=
                [Structured.Stmt.code
                    (AllocationSupport.scratchAllocatorInitCode config),
                  Structured.Stmt.code
                    (AllocationSupport.scratchFrameAcquireCode config ++
                      Locals.bindLocals 0
                        (compilation.frameName ::
                          prepared.allocatorCtx.layout)),
                  Structured.Stmt.code
                    (AllocationSupport.bindScratchBindingsCode 0
                      (AllocationLowering.mainScratchBindings
                        compilation.recipe compilation.stackSlots))] }
            target
            (Structured.EffectSemantics.Outcome.regular
              targetAfterFrame) :=
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hInitRun)
          (Structured.EffectSemantics.Block.Eval.cons_regular
            (Structured.EffectSemantics.Stmt.Eval.code hFrameHeadRun)
            (Structured.EffectSemantics.Block.Eval.cons_regular
              (Structured.EffectSemantics.Stmt.Eval.code hBindingsRun)
              Structured.EffectSemantics.Block.Eval.nil))
      have hAllocatorCtxInitial :
          prepared.allocatorCtx = Locals.Ctx.initial := by
        rw [hAllocatorCtx, hSourceCtx]
      have hBodyLayout :
          prepared.bodyCtx.layout = [compilation.frameName] := by
        rw [hBodyCtx, hAllocatorCtxInitial]
        rfl
      have hStartLayout :
          artifact.start.layout = [compilation.frameName] := by
        simp [MainArtifact.start,
          AllocationLowering.mainStartWithFrame, hNeedsFrame]
      have hCompiler :
          AllocationObserverContext.ActivationExprContext
            artifact.lowerCtx artifact.start prepared.bodyCtx
            artifact.plan [] (.scratch 0 config.frameWords) := by
        apply
          AllocationObserverContext.ActivationExprContext.scratch_of_layout
            artifact.planWF
        · rw [hBodyLayout, hStartLayout]
        · simp [hStartLayout, MainArtifact.lowerCtx,
            AllocationObserverForward.Compilation.lowerCtx,
            AllocationObserverRelation.currentStackOrder]
        · simp [AllocationObserverRelation.currentStackOrder]
        · simp [MainArtifact.lowerCtx,
            AllocationObserverForward.Compilation.lowerCtx,
            AllocationObserverRelation.currentStackOrder]
        · intro name hLive
          simp at hLive
        · intro name slot hLive
          simp at hLive
        · intro name slot hLive
          simp at hLive
      have hTargetInitialStack :
          target.source.evm.stack = [] := by
        apply List.length_eq_zero_iff.mp
        simpa [Locals.Ctx.initial] using hInvariant.stackLength
      have hTargetFrameLength :
          targetAfterFrame.source.evm.stack.length = 1 := by
        rw [hFrameStack, hInitStack, hTargetInitialStack]
        rfl
      have hActivation :
          AllocationObserverContext.ActivationInvariant
            program.memoryContract artifact.lowerCtx artifact.start
            prepared.bodyCtx artifact.plan []
            (AllocationObserverRelation.Frame.baseAt config 0)
            (.scratch 0 config.frameWords) source targetAfterFrame :=
        { compiler := hCompiler
          planWF := artifact.planWF
          defined := hInvariant.defined
          state := hFrameRel
          stackLength := by
            rw [hTargetFrameLength, hBodyLayout]
            rfl }
      have hResource :
          AllocationObserverContext.ActivationResourceInvariant
            (.scratch config) program.memoryContract 1
            artifact.lowerCtx artifact.start prepared.bodyCtx
            artifact.plan []
            (AllocationObserverRelation.Frame.baseAt config 0)
            (.scratch 0 config.frameWords) source targetAfterFrame :=
        { activation := hActivation
          ready := by simpa using hFrameReady
          owned := .scratch rfl rfl }
      refine
        ⟨AllocationObserverRelation.Frame.baseAt config 0,
          .scratch 0 config.frameWords, targetAfterFrame, 4, ?_, ?_⟩
      · simpa [hAllocatorCode, hFrameCode,
          Expressions.StmtList.toStructured] using hTargetEval
      · rw [hMode]
        simpa [mainSetupDepth, hNeedsFrame] using hResource
    · have hNoFrame :
          AllocationLowering.mainNeedsFrame
              compilation.recipe compilation.stackSlots =
            false :=
        Bool.eq_false_of_not_eq_true hNeedsFrame
      have hFrameExpected :=
        artifact.components.compileFrame_of_no_frame
          hNoFrame prepared.allocatorCtx
      have hFramePair :
          (prepared.frameCode, prepared.bodyCtx) =
            ([], prepared.allocatorCtx) :=
        Option.some.inj
          (prepared.compileFrame.symm.trans hFrameExpected)
      have hFrameCode := congrArg Prod.fst hFramePair
      have hBodyCtx := congrArg Prod.snd hFramePair
      simp only [Prod.fst] at hFrameCode
      simp only [Prod.snd] at hBodyCtx
      have hBodyCtxInitial :
          prepared.bodyCtx = Locals.Ctx.initial := by
        rw [hBodyCtx, hAllocatorCtx, hSourceCtx]
      have hStart :
          artifact.start = artifact.beforeSetup := by
        simp [MainArtifact.start, MainArtifact.beforeSetup,
          AllocationLowering.mainStartWithFrame, hNoFrame]
      have hCompiler :
          AllocationObserverContext.ActivationExprContext
            artifact.lowerCtx artifact.start prepared.bodyCtx
            artifact.plan [] .stack := by
        rw [hStart, hBodyCtxInitial]
        exact hInvariant.compiler
      have hActivation :
          AllocationObserverContext.ActivationInvariant
            program.memoryContract artifact.lowerCtx artifact.start
            prepared.bodyCtx artifact.plan [] 0 .stack source
            targetAfterInit :=
        { compiler := hCompiler
          planWF := artifact.planWF
          defined := hInvariant.defined
          state :=
            .stack
              (by
                intro name slot hLive _hLocation
                simp at hLive)
              hInitReady.activeNoWrap hInitRel
          stackLength := by
            rw [hInitStack, hInvariant.stackLength, hBodyCtxInitial] }
      have hTargetEval :
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured 2
            { stmts :=
                [Structured.Stmt.code
                  (AllocationSupport.scratchAllocatorInitCode config)] }
            target
            (Structured.EffectSemantics.Outcome.regular
              targetAfterInit) :=
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hInitRun)
          Structured.EffectSemantics.Block.Eval.nil
      have hResource :
          AllocationObserverContext.ActivationResourceInvariant
            (.scratch config) program.memoryContract 0
            artifact.lowerCtx artifact.start prepared.bodyCtx
            artifact.plan [] 0 .stack source targetAfterInit :=
        { activation := hActivation
          ready := hInitReady
          owned := .stack }
      refine ⟨0, .stack, targetAfterInit, 2, ?_, ?_⟩
      · simpa [hAllocatorCode, hFrameCode,
          Expressions.StmtList.toStructured] using hTargetEval
      · rw [hMode]
        simpa [mainSetupDepth, hNoFrame] using hResource

end MainSetup

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
Whole-main forward preservation for one successful open source execution.

All compiler artifacts are explicit only because this is the pass-internal
composition theorem. `mainForward` below constructs them from the ordinary
compiler equation before exposing the public source-facing interface.
-/
theorem MainPrepared.forwardOpen
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    (prepared : MainPrepared artifact)
    (mainRoot : MainRoot prepared)
    {maxDepth fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {finalCtx : Functions.Source.Ctx}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hProgramScoped : program.Scoped)
    (hFuelSafe :
      (compilationResourceMode compilation).FuelSafe maxDepth)
    (hDepthBound :
      mainSetupDepth compilation + fuelBound ≤ maxDepth)
    (hSourceFuel : sourceFuel < fuelBound)
    (hInitial :
      InitialRel program.memoryContract source target)
    (hSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program Functions.Source.Ctx.initial sourceFuel program.body
          source =
        .ok (sourceOutcome, finalCtx)) :
    ∃ targetOutcome targetFuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured targetFuel expressions.body.toStructured
        target
        targetOutcome ∧
      OutcomeRel program.memoryContract
        (closeOutcome sourceOutcome) targetOutcome := by
  obtain ⟨sourcePrefix, hSourceBody, hPrelude⟩ :=
    AllocationLowering.splitPrelude_components artifact.components.split
  have hProgramBody :
      program.body =
        { stmts := sourcePrefix ++ artifact.components.rest } :=
    block_eq_of_stmts_eq hSourceBody
  have hSourceSplit := hSource
  rw [hProgramBody] at hSourceSplit
  obtain
      ⟨sourceAfterPrefix, sourceAfterPrefixCtx,
        sourcePrefixFuel, sourceTailFuel,
        hSourcePrefix, hSourceTail, hTailFuelLe⟩ :=
    SourcePrelude.splitOpen
      (allocation := allocation) (expressions := expressions)
      (compilation := compilation) hPrelude hSourceSplit
  have hInitialInvariant := hInitial.invariant artifact
  obtain
      ⟨targetAfterPrefix, targetPrefixFuel,
        hSourceCtx, hSourceAfterPrefixCtx,
        hTargetPrefix, hPrefixInvariant⟩ :=
    SourcePrelude.forward
      (allocation := allocation) (compilation := compilation)
      hPrelude prepared.compileSource hSourcePrefix hInitialInvariant
  have hSourceTail' :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program Functions.Source.Ctx.initial sourceTailFuel
          { stmts := artifact.components.rest } sourceAfterPrefix =
        .ok (sourceOutcome, finalCtx) := by
    simpa [hSourceAfterPrefixCtx] using hSourceTail
  obtain
      ⟨frameBase, mode, targetAfterSetup, targetSetupFuel,
        hTargetSetup, hSetupInvariant⟩ :=
    MainSetup.forward prepared hSourceCtx hPrefixInvariant
  have hArtifactFuelSafe :
      artifact.resourceMode.FuelSafe maxDepth := by
    simpa [MainArtifact.resourceMode] using hFuelSafe
  have hBudget :
      artifact.resourceMode.Budget (mainSetupDepth compilation) :=
    hArtifactFuelSafe.depth_safe (by omega)
  have hRootInvariant :
      AllocationObserverContext.ActivationResourceInvariant
        artifact.resourceMode program.memoryContract
        (mainSetupDepth compilation)
        mainRoot.root.lowerCtx mainRoot.root.startState
        mainRoot.root.startLocals mainRoot.root.plan
        ((mainRoot.root.slots.returns.map Prod.fst).reverse ++
          (mainRoot.root.slots.params.map Prod.fst).reverse)
        frameBase mode sourceAfterPrefix targetAfterSetup := by
    simpa [mainRoot.lowerCtx, mainRoot.startState, mainRoot.startLocals,
      mainRoot.plan, mainRoot.live] using hSetupInvariant
  let boundary :=
    mainRoot.resourceBoundary hBudget hRootInvariant
  have hRecursive :
      AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward
        (root := mainRoot.root) (resource := artifact.resourceMode)
        (allocatorDepth := mainSetupDepth compilation)
        (frameBase := frameBase) (fuelBound := fuelBound)
        (transcript := transcript) :=
    mainRoot.resourceRecursiveForward fuelBound hProgramScoped
      hArtifactFuelSafe hDepthBound
  have hTailFuel : sourceTailFuel < fuelBound :=
    hTailFuelLe.trans_lt hSourceFuel
  have hRootSource :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program Functions.Source.Ctx.initial sourceTailFuel
          mainRoot.root.sourceBlock sourceAfterPrefix =
        .ok (sourceOutcome, finalCtx) := by
    rw [mainRoot.sourceBlock]
    exact hSourceTail'
  by_cases hRegular : sourceOutcome.mode = .regular
  · have hSourceOutcome :
        sourceOutcome =
          Functions.Source.Effectful.Outcome.regular
            sourceOutcome.state :=
      sourceOutcome_eq_regular_of_mode hRegular
    have hRootSourceRegular :
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            program Functions.Source.Ctx.initial sourceTailFuel
            mainRoot.root.sourceBlock sourceAfterPrefix =
          .ok
            (Functions.Source.Effectful.Outcome.regular
              sourceOutcome.state,
              finalCtx) := by
      rw [hSourceOutcome] at hRootSource
      exact hRootSource
    obtain
        ⟨targetAfterBody, finalMode, hBodyForward,
          _hControl, _hFinalScope⟩ :=
      AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward.regular
        mainRoot.root.cursor hRecursive hTailFuel boundary
        hRootSourceRegular
    rcases hBodyForward with
      ⟨_bodySourceFuel, targetBodyFuel, _hBodySource,
        hTargetBody, hFinalInvariant, _hSameFrame, _hBodyEffect⟩
    have hFinalStackLength :
        targetAfterBody.source.evm.stack.length =
          prepared.finalCtx.layout.length := by
      have hStackLength := hFinalInvariant.activation.stackLength
      change
        targetAfterBody.source.evm.stack.length =
          mainRoot.root.finalLocals.layout.length at hStackLength
      rw [mainRoot.finalLocals] at hStackLength
      exact hStackLength
    obtain
        ⟨targetFinal, hCleanupRun, hFinalStackLength,
          _hCleanupMachine, hCleanupCursor, hCleanupShared⟩ :=
      AllocationObserverCleanup.Plain.run_exact
        hFinalStackLength prepared.cleanupCode
    have hTargetCleanup :
        Structured.ObserverSemantics.Block.Eval
          expressions.toStructured 2
          { stmts := [Structured.Stmt.code prepared.cleanup] }
          targetAfterBody
          (Structured.EffectSemantics.Outcome.regular targetFinal) :=
      Structured.EffectSemantics.Block.Eval.cons_regular
        (Structured.EffectSemantics.Stmt.Eval.code hCleanupRun)
        Structured.EffectSemantics.Block.Eval.nil
    have hTargetBody' :
        Structured.ObserverSemantics.Block.Eval
          expressions.toStructured targetBodyFuel
          { stmts :=
              Expressions.StmtList.toStructured prepared.bodyCode }
          targetAfterSetup
          (Structured.EffectSemantics.Outcome.regular
            targetAfterBody) := by
      change
        Structured.ObserverSemantics.Block.Eval
          expressions.toStructured targetBodyFuel
          { stmts :=
              Expressions.StmtList.toStructured mainRoot.root.compiled }
          targetAfterSetup
          (Structured.EffectSemantics.Outcome.regular
            targetAfterBody) at hTargetBody
      rw [mainRoot.compiled] at hTargetBody
      exact hTargetBody
    obtain ⟨targetBodyCleanupFuel, hTargetBodyCleanup⟩ :=
      Structured.EffectSemantics.Block.Eval.append_regular_exists
        hTargetBody' hTargetCleanup
    obtain ⟨targetSetupBodyFuel, hTargetSetupBody⟩ :=
      Structured.EffectSemantics.Block.Eval.append_regular_exists
        hTargetSetup hTargetBodyCleanup
    obtain ⟨targetFuel, hTargetAll⟩ :=
      Structured.EffectSemantics.Block.Eval.append_regular_exists
        hTargetPrefix hTargetSetupBody
    have hBeforeCleanup :
        FinalStateRel program.memoryContract sourceOutcome.state
          targetAfterBody :=
      FinalStateRel.of_activationOutcome
        (AllocationObserverRelation.ActivationOutcomeRel.regular
          hFinalInvariant.activation.state)
    have hAfterCleanup :
        FinalStateRel program.memoryContract
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            [] sourceOutcome.state)
          targetFinal :=
      hBeforeCleanup.after_cleanup_empty hCleanupCursor hCleanupShared
    have hFinalStack : targetFinal.source.evm.stack = [] :=
      List.length_eq_zero_iff.mp hFinalStackLength
    refine
      ⟨Structured.EffectSemantics.Outcome.regular targetFinal,
        targetFuel, ?_, ?_⟩
    · rw [prepared.output]
      simpa only [Expressions.Block.toStructured,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured, Locals.codeStmt,
        List.append_assoc] using hTargetAll
    · rw [hSourceOutcome]
      simpa [closeOutcome] using
        (OutcomeRel.regular hAfterCleanup hFinalStack)
  · obtain ⟨targetOutcome, finalMode, hBodyForward⟩ :=
      AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward.nonregular
        mainRoot.root.cursor hRecursive hTailFuel boundary hRootSource
        hRegular
    rcases hBodyForward with
      ⟨_bodySourceFuel, targetBodyFuel, _hBodySource,
        hTargetBody, hOutcomeRel, _hSameFrame, _hBodyEffect⟩
    have hTargetBody' :
        Structured.ObserverSemantics.Block.Eval
          expressions.toStructured targetBodyFuel
          { stmts :=
              Expressions.StmtList.toStructured prepared.bodyCode }
          targetAfterSetup targetOutcome := by
      change
        Structured.ObserverSemantics.Block.Eval
          expressions.toStructured targetBodyFuel
          { stmts :=
              Expressions.StmtList.toStructured mainRoot.root.compiled }
          targetAfterSetup targetOutcome at hTargetBody
      rw [mainRoot.compiled] at hTargetBody
      exact hTargetBody
    have hTargetNonregular : targetOutcome.mode ≠ .regular :=
      hOutcomeRel.target_nonregular hRegular
    have hTargetBodyCleanup :
        Structured.ObserverSemantics.Block.Eval
          expressions.toStructured targetBodyFuel
          { stmts :=
              Expressions.StmtList.toStructured prepared.bodyCode ++
                [Structured.Stmt.code prepared.cleanup] }
          targetAfterSetup targetOutcome :=
      Structured.EffectSemantics.Block.Eval.append_nonregular
        hTargetBody' hTargetNonregular
    obtain ⟨targetSetupBodyFuel, hTargetSetupBody⟩ :=
      Structured.EffectSemantics.Block.Eval.append_regular_exists
        hTargetSetup hTargetBodyCleanup
    obtain ⟨targetFuel, hTargetAll⟩ :=
      Structured.EffectSemantics.Block.Eval.append_regular_exists
        hTargetPrefix hTargetSetupBody
    refine ⟨targetOutcome, targetFuel, ?_, ?_⟩
    · rw [prepared.output]
      simpa only [Expressions.Block.toStructured,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured, Locals.codeStmt,
        List.append_assoc] using hTargetAll
    · simpa [closeOutcome, hRegular] using
        OutcomeRel.of_nonregular_activation hOutcomeRel hRegular

/--
Compiler-selected whole-main preservation for the checked no-external-effects
Functions semantics.

The theorem constructs every allocation, lowering, compilation, resource-mode,
and recursive-root artifact internally. Its public premises are source scoping,
source-facing resource bounds, an initial semantic relation, and one successful
run of the canonical guarded Functions interpreter.
-/
theorem mainForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (hLower :
      AllocationLowering.lowerExpressionsFromAllocation? allocation program =
        some expressions)
    {maxDepth fuelBound sourceFuel : Nat}
    {transcript : Trace}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hProgramScoped : program.Scoped)
    (hFuelSafe :
      (selectedResourceMode allocation program).FuelSafe maxDepth)
    (hDepthBound :
      selectedMainSetupDepth allocation program + fuelBound ≤ maxDepth)
    (hSourceFuel : sourceFuel < fuelBound)
    (hInitial :
      InitialRel program.memoryContract source target)
    (hSource :
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          sourceFuel program source =
        .ok sourceOutcome) :
    ∃ targetOutcome targetFuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured targetFuel expressions.body.toStructured
        target targetOutcome ∧
      OutcomeRel program.memoryContract sourceOutcome targetOutcome := by
  obtain ⟨compilation⟩ :=
    AllocationObserverForward.Compilation.of_lowering hLower
  have hCompilationFuelSafe :
      (compilationResourceMode compilation).FuelSafe maxDepth := by
    rw [← selectedResourceMode_eq_compilation compilation]
    exact hFuelSafe
  have hCompilationDepthBound :
      mainSetupDepth compilation + fuelBound ≤ maxDepth := by
    rw [← selectedMainSetupDepth_eq_compilation compilation]
    exact hDepthBound
  obtain ⟨artifact⟩ := MainArtifact.ofCompilation compilation
  obtain ⟨prepared⟩ := MainPrepared.ofArtifact artifact
  obtain ⟨mainRoot⟩ := prepared.rootArtifact hProgramScoped
  rcases
      Functions.Source.Effectful.Block.runScoped_cases
        (Functions.ObserverSemantics.stateModel transcript)
        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
          program.memoryContract transcript)
        program hSource with
    hRegular | hNonregular
  · rcases hRegular with
      ⟨final, finalCtx, hOpen, hSourceOutcome⟩
    obtain ⟨targetOutcome, targetFuel, hTarget, hOutcome⟩ :=
      prepared.forwardOpen mainRoot hProgramScoped hCompilationFuelSafe
        hCompilationDepthBound hSourceFuel hInitial hOpen
    refine ⟨targetOutcome, targetFuel, hTarget, ?_⟩
    rw [hSourceOutcome]
    simpa [closeOutcome] using hOutcome
  · rcases hNonregular with
      ⟨openOutcome, finalCtx, hOpen, hMode, hSourceOutcome⟩
    obtain ⟨targetOutcome, targetFuel, hTarget, hOutcome⟩ :=
      prepared.forwardOpen mainRoot hProgramScoped hCompilationFuelSafe
        hCompilationDepthBound hSourceFuel hInitial hOpen
    refine ⟨targetOutcome, targetFuel, hTarget, ?_⟩
    rw [hSourceOutcome]
    simpa [closeOutcome, hMode] using hOutcome

/--
Any successful target evaluation agrees with the unique target outcome
constructed from a successful guarded source run.

This is a determinism-strengthened forward theorem, not backward adequacy:
constructing the guarded source run from target execution remains a separate
obligation.
-/
theorem mainTargetAgreement
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (hLower :
      AllocationLowering.lowerExpressionsFromAllocation? allocation program =
        some expressions)
    {maxDepth fuelBound sourceFuel targetFuel : Nat}
    {transcript : Trace}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hProgramScoped : program.Scoped)
    (hFuelSafe :
      (selectedResourceMode allocation program).FuelSafe maxDepth)
    (hDepthBound :
      selectedMainSetupDepth allocation program + fuelBound ≤ maxDepth)
    (hSourceFuel : sourceFuel < fuelBound)
    (hInitial :
      InitialRel program.memoryContract source target)
    (hSource :
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          sourceFuel program source =
        .ok sourceOutcome)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured targetFuel expressions.body.toStructured
        target targetOutcome) :
    OutcomeRel program.memoryContract sourceOutcome targetOutcome := by
  obtain
      ⟨expectedOutcome, expectedFuel, hExpected, hOutcomeRel⟩ :=
    mainForward hLower hProgramScoped hFuelSafe hDepthBound hSourceFuel
      hInitial hSource
  have hOutcome :
      expectedOutcome = targetOutcome :=
    Structured.EffectSemantics.Block.Eval.outcome_unique
      hExpected hTarget
  simpa [hOutcome] using hOutcomeRel

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
