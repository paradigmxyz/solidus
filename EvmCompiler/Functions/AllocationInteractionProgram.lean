import EvmCompiler.Functions.AllocationInteractionProgramArtifact
import EvmCompiler.Functions.AllocationInteractionFramePreservation
import EvmCompiler.Functions.AllocationInteractionStackRuntime

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionProgram

open AllocationInteractionCursor
open AllocationInteractionCall
open AllocationInteractionFrame
open AllocationInteractionFrameExecution
open AllocationInteractionFramePreservation
open AllocationInteractionRelation
open AllocationInteractionProgramArtifact

/-- Source-facing initial relation for the adjacent allocation pass. -/
structure InitialRel
    (contract : MemoryContract.Contract)
    (source : Functions.InteractionSemantics.State)
    (target : Expressions.InteractionSemantics.RunState) : Prop where
  shared : SharedRel contract source.shared target.evm.toSharedState
  stack : target.evm.stack = []
  returns : target.returns = []
  activeNoWrap :
    target.evm.activeWords.toNat * MemoryContract.wordBytes <
      EvmYul.UInt256.size

namespace InitialRel

/-- Every related initial state realizes the compiler's empty stack
activation before allocator/frame setup. -/
theorem invariant
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    (artifact : MainArtifact compilation)
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hInitial : InitialRel program.memoryContract source target) :
    AllocationContext.ActivationInvariant program.memoryContract
      artifact.lowerCtx artifact.beforeSetup Locals.Ctx.initial artifact.plan
      [] 0 .stack source target := by
  refine
    { compiler := ?_
      planWF := artifact.planWF
      defined := ?_
      state := ?_
      stackLength := ?_ }
  · apply AllocationContext.ActivationExprContext.stack_of_layout
      artifact.planWF
    · rfl
    · simp [AllocationInteractionRelation.currentStackOrder,
        MainArtifact.beforeSetup]
    · simp [MainArtifact.beforeSetup, MainArtifact.lowerCtx,
        Compilation.lowerCtx]
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
        { machine := hInitial.shared.machine
          world := hInitial.shared.world
          store := by
            intro name location hLive _hLocation
            simp at hLive }
  · rw [hInitial.stack]
    rfl

end InitialRel

/-- Result of executing the allocator and optional main-frame setup selected by
the ordinary allocation and Locals passes.  This is internal pass state: the
public adjacent theorem constructs it from the compiler artifact. -/
structure ScratchSetupResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    (prepared : MainPrepared artifact)
    (config : Config)
    (source : Functions.InteractionSemantics.State)
    (target : Expressions.InteractionSemantics.RunState)
    (frameBase : Nat)
    (mode : ActivationMode)
    (targetFinal : Expressions.InteractionSemantics.RunState)
    (targetFuel : Nat) : Prop where
  targetFuel_eq :
    targetFuel = (prepared.allocatorCode ++ prepared.frameCode).length + 1
  execution :
    Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        { stmts := prepared.allocatorCode ++ prepared.frameCode } target =
      .done (.ok (Structured.Outcome.regular targetFinal))
  invariant :
    AllocationContext.ActivationInvariant program.memoryContract
      artifact.lowerCtx artifact.start prepared.bodyCtx artifact.plan []
      frameBase mode source targetFinal
  ready : AllocatorReady config (mainSetupDepth compilation) targetFinal
  owned :
    ActivationOwned config (mainSetupDepth compilation) frameBase mode
  returns : targetFinal.returns = target.returns

/-- Empty allocator/frame setup selected for a wholly stack-backed program. -/
structure StackSetupResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    (prepared : MainPrepared artifact)
    (source : Functions.InteractionSemantics.State)
    (target : Expressions.InteractionSemantics.RunState)
    (targetFuel : Nat) : Prop where
  targetFuel_eq :
    targetFuel = (prepared.allocatorCode ++ prepared.frameCode).length + 1
  execution :
    Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        { stmts := prepared.allocatorCode ++ prepared.frameCode } target =
      .done (.ok (Structured.Outcome.regular target))
  invariant :
    AllocationContext.ActivationInvariant program.memoryContract
      artifact.lowerCtx artifact.start prepared.bodyCtx artifact.plan []
      0 .stack source target
  returns : target.returns = target.returns

namespace MainPrepared

/-- Execute the exact empty setup selected when no function or main activation
uses compiler scratch storage. -/
theorem stackSetup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    (prepared : MainPrepared artifact)
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hSourceCtx : prepared.sourceCtx = Locals.Ctx.initial)
    (hNoAllocator :
      AllocationLowering.mainNeedsAllocator
          compilation.recipe compilation.stackSlots = false)
    (hNoFrame :
      AllocationLowering.mainNeedsFrame
          compilation.recipe compilation.stackSlots = false)
    (hInitial : InitialRel program.memoryContract source target) :
    StackSetupResult prepared source target 1 := by
  have hInvariant := InitialRel.invariant artifact hInitial
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
    artifact.components.compileFrame_of_no_frame hNoFrame
      prepared.allocatorCtx
  have hFramePair :
      (prepared.frameCode, prepared.bodyCtx) =
        ([], prepared.allocatorCtx) :=
    Option.some.inj (prepared.compileFrame.symm.trans hFrameExpected)
  have hFrameCode := congrArg Prod.fst hFramePair
  have hBodyCtx := congrArg Prod.snd hFramePair
  simp only [Prod.fst] at hFrameCode
  simp only [Prod.snd] at hBodyCtx
  have hBodyCtxInitial : prepared.bodyCtx = Locals.Ctx.initial := by
    rw [hBodyCtx, hAllocatorCtx, hSourceCtx]
  have hStart : artifact.start = artifact.beforeSetup := by
    simp [MainArtifact.start, MainArtifact.beforeSetup,
      AllocationLowering.mainStartWithFrame, hNoFrame]
  have hActivation :
      AllocationContext.ActivationInvariant program.memoryContract
        artifact.lowerCtx artifact.start prepared.bodyCtx artifact.plan []
        0 .stack source target := by
    rw [hStart, hBodyCtxInitial]
    exact hInvariant
  refine
    { targetFuel_eq := by simp [hAllocatorCode, hFrameCode]
      execution := ?_
      invariant := hActivation
      returns := rfl }
  simpa [hAllocatorCode, hFrameCode] using
    (Expressions.InteractionSemantics.Block.openRun_nil expressions 0 target)

/-- Execute the exact scratch allocator and optional main-frame setup emitted
by the ordinary compiler.  The no-main-frame branch still initializes the
allocator because nested compiler-selected callees may require scratch. -/
theorem scratchSetup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    (prepared : MainPrepared artifact)
    {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hSourceCtx : prepared.sourceCtx = Locals.Ctx.initial)
    (hFrameConfig : compilation.frameConfig? = some config)
    (hNeedsAllocator :
      AllocationLowering.mainNeedsAllocator
          compilation.recipe compilation.stackSlots = true)
    (hInitial : InitialRel program.memoryContract source target) :
    ∃ frameBase mode targetFinal targetFuel,
      ScratchSetupResult prepared config source target
        frameBase mode targetFinal targetFuel := by
  have hInvariant := InitialRel.invariant artifact hInitial
  have hConfig :
      AllocationSupport.scratchFrameConfig? program.memoryContract
          compilation.recipe.frameWords = some config := by
    simpa [Compilation.frameConfig?] using hFrameConfig
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
  obtain ⟨hBaseRel, hActiveNoWrap⟩ :
      StateRel program.memoryContract artifact.plan [] 0 0 source target ∧
        target.evm.activeWords.toNat * MemoryContract.wordBytes <
          EvmYul.UInt256.size := by
    cases hInvariant.state with
    | stack _ hNoWrap hState => exact ⟨hState, hNoWrap⟩
  obtain
      ⟨targetAfterInit, hInitRun, hInitRel, hInitReady, hInitStack,
        hInitReturns⟩ :=
    allocatorInit_correct hBaseRel hConfig hActiveNoWrap
  by_cases hNeedsFrame :
      AllocationLowering.mainNeedsFrame
          compilation.recipe compilation.stackSlots = true
  · have hFrameExpected :=
      artifact.components.compileFrame_of_scratch
        hFrameConfig hNeedsFrame prepared.allocatorCtx
    have hFramePair :
        (prepared.frameCode, prepared.bodyCtx) =
          ([Expressions.Stmt.code
              (AllocationSupport.scratchFrameAcquireCode config ++
                Locals.bindLocals 0
                  (compilation.frameName :: prepared.allocatorCtx.layout)),
            Expressions.Stmt.code
              (AllocationSupport.bindScratchBindingsCode 0
                (AllocationLowering.mainScratchBindings
                  compilation.recipe compilation.stackSlots))],
            prepared.allocatorCtx.withLayout
              (compilation.frameName :: prepared.allocatorCtx.layout)) :=
      Option.some.inj
        (prepared.compileFrame.symm.trans hFrameExpected)
    have hFrameCode := congrArg Prod.fst hFramePair
    have hBodyCtx := congrArg Prod.snd hFramePair
    simp only [Prod.fst] at hFrameCode
    simp only [Prod.snd] at hBodyCtx
    have hPositiveRecipe : 0 < compilation.recipe.frameWords := by
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
    have hBudget : Budget config 0 :=
      budget_zero_of_scratchFrameConfig? hConfig
    obtain ⟨hAcquire, hFrameRel⟩ :=
      scratchFrameAcquire_empty_correct hConfig hPositive hBudget
        hInitReady hInitRel
    let targetAfterFrame := scratchFrameAcquireTarget config 0 targetAfterInit
    have hFrameRun :
        Structured.InteractionSemantics.Code.openRun
            (AllocationSupport.scratchFrameAcquireCode config)
            targetAfterInit =
          .done (.ok targetAfterFrame) := by
      simpa [targetAfterFrame] using hAcquire.execution
    have hBindLocalsRun :
        Structured.InteractionSemantics.Code.openRun
            (Locals.bindLocals 0
              (compilation.frameName :: prepared.allocatorCtx.layout))
            targetAfterFrame =
          .done (.ok targetAfterFrame) := by
      simpa using
        Locals.InteractionPreservation.Code.openRun_bindLocals 0
          (compilation.frameName :: prepared.allocatorCtx.layout)
          targetAfterFrame
    have hFrameHeadRun :
        Structured.InteractionSemantics.Code.openRun
            (AllocationSupport.scratchFrameAcquireCode config ++
              Locals.bindLocals 0
                (compilation.frameName :: prepared.allocatorCtx.layout))
            targetAfterInit =
          .done (.ok targetAfterFrame) := by
      rw [Structured.InteractionSemantics.Code.openRun_append, hFrameRun]
      exact hBindLocalsRun
    have hBindingsRun :
        Structured.InteractionSemantics.Code.openRun
            (AllocationSupport.bindScratchBindingsCode 0
              (AllocationLowering.mainScratchBindings
                compilation.recipe compilation.stackSlots))
            targetAfterFrame =
          .done (.ok targetAfterFrame) :=
      EntryMarkers.openRun_bindScratchBindingsCode 0
        (AllocationLowering.mainScratchBindings
          compilation.recipe compilation.stackSlots) targetAfterFrame
    have hInitStmt :=
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        expressions 4 (AllocationSupport.scratchAllocatorInitCode config)
        target targetAfterInit (by omega) hInitRun
    have hFrameStmt :=
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        expressions 3
        (AllocationSupport.scratchFrameAcquireCode config ++
          Locals.bindLocals 0
            (compilation.frameName :: prepared.allocatorCtx.layout))
        targetAfterInit targetAfterFrame (by omega) hFrameHeadRun
    have hBindingsStmt :=
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        expressions 2
        (AllocationSupport.bindScratchBindingsCode 0
          (AllocationLowering.mainScratchBindings
            compilation.recipe compilation.stackSlots))
        targetAfterFrame targetAfterFrame (by omega) hBindingsRun
    have hTailRun :
        Expressions.InteractionSemantics.Block.openRun expressions 3
            { stmts :=
                [Expressions.Stmt.code
                  (AllocationSupport.scratchFrameAcquireCode config ++
                    Locals.bindLocals 0
                      (compilation.frameName ::
                        prepared.allocatorCtx.layout))] ++
                [Expressions.Stmt.code
                  (AllocationSupport.bindScratchBindingsCode 0
                    (AllocationLowering.mainScratchBindings
                      compilation.recipe compilation.stackSlots))] }
            targetAfterInit =
          .done (.ok (Structured.Outcome.regular targetAfterFrame)) := by
      rw [Expressions.InteractionSemantics.Block.openRun_append expressions
        [Expressions.Stmt.code
          (AllocationSupport.scratchFrameAcquireCode config ++
            Locals.bindLocals 0
              (compilation.frameName :: prepared.allocatorCtx.layout))]
        [Expressions.Stmt.code
          (AllocationSupport.bindScratchBindingsCode 0
            (AllocationLowering.mainScratchBindings
              compilation.recipe compilation.stackSlots))]
        3 targetAfterInit, hFrameStmt]
      simpa using hBindingsStmt
    have hTargetRun :
        Expressions.InteractionSemantics.Block.openRun expressions 4
            { stmts :=
                [Expressions.Stmt.code
                    (AllocationSupport.scratchAllocatorInitCode config),
                  Expressions.Stmt.code
                    (AllocationSupport.scratchFrameAcquireCode config ++
                      Locals.bindLocals 0
                        (compilation.frameName ::
                          prepared.allocatorCtx.layout)),
                  Expressions.Stmt.code
                    (AllocationSupport.bindScratchBindingsCode 0
                      (AllocationLowering.mainScratchBindings
                        compilation.recipe compilation.stackSlots))] }
            target =
          .done (.ok (Structured.Outcome.regular targetAfterFrame)) := by
      change
        Expressions.InteractionSemantics.Block.openRun expressions 4
            { stmts :=
                [Expressions.Stmt.code
                  (AllocationSupport.scratchAllocatorInitCode config)] ++
                [Expressions.Stmt.code
                    (AllocationSupport.scratchFrameAcquireCode config ++
                      Locals.bindLocals 0
                        (compilation.frameName ::
                          prepared.allocatorCtx.layout)),
                  Expressions.Stmt.code
                    (AllocationSupport.bindScratchBindingsCode 0
                      (AllocationLowering.mainScratchBindings
                        compilation.recipe compilation.stackSlots))] }
            target =
          .done (.ok (Structured.Outcome.regular targetAfterFrame))
      rw [Expressions.InteractionSemantics.Block.openRun_append expressions
        [Expressions.Stmt.code
          (AllocationSupport.scratchAllocatorInitCode config)]
        [Expressions.Stmt.code
            (AllocationSupport.scratchFrameAcquireCode config ++
              Locals.bindLocals 0
                (compilation.frameName :: prepared.allocatorCtx.layout)),
          Expressions.Stmt.code
            (AllocationSupport.bindScratchBindingsCode 0
              (AllocationLowering.mainScratchBindings
                compilation.recipe compilation.stackSlots))]
        4 target, hInitStmt]
      simpa using hTailRun
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
        AllocationContext.ActivationExprContext artifact.lowerCtx
          artifact.start prepared.bodyCtx artifact.plan []
          (.scratch 0 config.frameWords) := by
      apply AllocationContext.ActivationExprContext.scratch_of_layout
        artifact.planWF
      · rw [hBodyLayout, hStartLayout]
      · simp [hStartLayout, MainArtifact.lowerCtx, Compilation.lowerCtx,
          currentStackOrder]
      · simp [currentStackOrder]
      · simp [MainArtifact.lowerCtx, Compilation.lowerCtx,
          currentStackOrder]
      · intro name hLive
        simp at hLive
      · intro name slot hLive
        simp at hLive
      · intro name slot hLive
        simp at hLive
    have hTargetFrameLength : targetAfterFrame.evm.stack.length = 1 := by
      rw [show targetAfterFrame.evm.stack =
          EvmYul.UInt256.ofNat (baseAt config 0) ::
            targetAfterInit.evm.stack by
        simpa [targetAfterFrame] using hAcquire.stack]
      rw [hInitStack, hInitial.stack]
      rfl
    have hActivation :
        AllocationContext.ActivationInvariant program.memoryContract
          artifact.lowerCtx artifact.start prepared.bodyCtx artifact.plan []
          (baseAt config 0) (.scratch 0 config.frameWords) source
          targetAfterFrame :=
      { compiler := hCompiler
        planWF := artifact.planWF
        defined := hInvariant.defined
        state := by simpa [targetAfterFrame] using hFrameRel
        stackLength := by simp [hTargetFrameLength, hBodyLayout] }
    refine
      ⟨baseAt config 0, .scratch 0 config.frameWords, targetAfterFrame, 4,
      { targetFuel_eq := ?_
        execution := ?_
        invariant := hActivation
        ready := ?_
        owned := ?_
        returns := ?_ }⟩
    · simp [hAllocatorCode, hFrameCode]
    · simpa [hAllocatorCode, hFrameCode] using hTargetRun
    · simpa [mainSetupDepth, hNeedsFrame, targetAfterFrame] using
        hAcquire.effect.ready
    · simpa [mainSetupDepth, hNeedsFrame] using
        (ActivationOwned.scratch (config := config) (previousDepth := 0)
          (frameDepth := 0) (frameWords := config.frameWords) rfl rfl)
    · rw [show targetAfterFrame.returns = targetAfterInit.returns by
        simp [targetAfterFrame], hInitReturns]
  · have hNoFrame :
        AllocationLowering.mainNeedsFrame
            compilation.recipe compilation.stackSlots = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hFrameExpected :=
      artifact.components.compileFrame_of_no_frame hNoFrame
        prepared.allocatorCtx
    have hFramePair :
        (prepared.frameCode, prepared.bodyCtx) =
          ([], prepared.allocatorCtx) :=
      Option.some.inj
        (prepared.compileFrame.symm.trans hFrameExpected)
    have hFrameCode := congrArg Prod.fst hFramePair
    have hBodyCtx := congrArg Prod.snd hFramePair
    simp only [Prod.fst] at hFrameCode
    simp only [Prod.snd] at hBodyCtx
    have hBodyCtxInitial : prepared.bodyCtx = Locals.Ctx.initial := by
      rw [hBodyCtx, hAllocatorCtx, hSourceCtx]
    have hStart : artifact.start = artifact.beforeSetup := by
      simp [MainArtifact.start, MainArtifact.beforeSetup,
        AllocationLowering.mainStartWithFrame, hNoFrame]
    have hCompiler :
        AllocationContext.ActivationExprContext artifact.lowerCtx
          artifact.start prepared.bodyCtx artifact.plan [] .stack := by
      rw [hStart, hBodyCtxInitial]
      exact hInvariant.compiler
    have hActivation :
        AllocationContext.ActivationInvariant program.memoryContract
          artifact.lowerCtx artifact.start prepared.bodyCtx artifact.plan []
          0 .stack source targetAfterInit :=
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
    have hTargetRun :=
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        expressions 2 (AllocationSupport.scratchAllocatorInitCode config)
        target targetAfterInit (by omega) hInitRun
    refine
      ⟨0, .stack, targetAfterInit, 2,
      { targetFuel_eq := ?_
        execution := ?_
        invariant := hActivation
        ready := ?_
        owned := ?_
        returns := hInitReturns }⟩
    · simp [hAllocatorCode, hFrameCode]
    · simpa [hAllocatorCode, hFrameCode] using hTargetRun
    · simpa [mainSetupDepth, hNoFrame] using hInitReady
    · simpa [mainSetupDepth, hNoFrame] using
        (ActivationOwned.stack (config := config)
          (allocatorDepth := 0) (frameBase := 0))

end MainPrepared

namespace StackSetupResult

/-- Package empty stack-only setup as the exact recursive-body boundary. -/
theorem boundary
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    {targetFuel : Nat}
    (mainRoot : MainRoot prepared)
    (hSetup : StackSetupResult prepared source target targetFuel) :
    AllocationInteractionStackRuntime.Boundary mainRoot.root.cursor
      program.memoryContract 0 .stack Functions.Source.Ctx.initial source
      target := by
  refine
    { semantic :=
        { invariant := ?_
          sourceScope := ?_
          control := ?_
          capacity := trivial }
      controlAgreement := ?_
      stackMode := rfl }
  · simpa [AllocationInteractionCursor.RootArtifact.cursor,
      mainRoot.lowerCtx, mainRoot.startState, mainRoot.startLocals,
      mainRoot.plan, mainRoot.live] using hSetup.invariant
  · simpa [AllocationInteractionCursor.RootArtifact.cursor,
      mainRoot.live, Functions.Source.Ctx.initial]
  · refine
      { breakScope := ?_
        continueScope := ?_
        returnsLive := ?_
        leaveScope := ?_ }
    · simp [Functions.Source.Ctx.initial]
    · simp [Functions.Source.Ctx.initial]
    · simpa [AllocationInteractionCursor.RootArtifact.cursor,
        mainRoot.returns, mainRoot.live]
    · simp [Functions.Source.Ctx.initial]
  · exact
      AllocationInteractionControlAgreement.Agreement.noControl
        (by rfl) (by rfl) (by rfl)

end StackSetupResult

namespace ScratchSetupResult

/-- Package checked main setup as the exact recursive-body boundary.  The
fuel-indexed frame budget is the sole dynamic scratch-capacity premise and is
stated over the compiler-selected reservation. -/
theorem boundary
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target targetFinal : Expressions.InteractionSemantics.RunState}
    {frameBase targetFuel sourceFuel : Nat}
    {mode : ActivationMode}
    (mainRoot : MainRoot prepared)
    (hSetup :
      ScratchSetupResult prepared config source target
        frameBase mode targetFinal targetFuel)
    (hFrameConfig : compilation.frameConfig? = some config)
    (hFuelBudget :
      Budget config (mainSetupDepth compilation + sourceFuel)) :
    AllocationInteractionRecursiveResource.Boundary
      mainRoot.root.cursor program.memoryContract
      compilation.recipe.frameWords config (mainSetupDepth compilation)
      frameBase mode Functions.Source.Ctx.initial source targetFinal := by
  have hConfig :
      AllocationSupport.scratchFrameConfig? program.memoryContract
          compilation.recipe.frameWords = some config := by
    simpa [Compilation.frameConfig?] using hFrameConfig
  obtain
      ⟨_reservation, _hReservation, _hAllocator, _hFirst,
        _hLimit, hWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  refine
    { semantic := ?_
      controlAgreement := ?_
      configEq := hConfig
      ready := hSetup.ready
      owned := hSetup.owned
      budget := Budget.mono (Nat.le_add_right _ sourceFuel) hFuelBudget }
  · refine
      { invariant := ?_
        sourceScope := ?_
        control := ?_
        capacity := ?_ }
    · simpa [AllocationInteractionCursor.RootArtifact.cursor,
        mainRoot.lowerCtx, mainRoot.startState, mainRoot.startLocals,
        mainRoot.plan, mainRoot.live] using hSetup.invariant
    · simpa [AllocationInteractionCursor.RootArtifact.cursor,
        mainRoot.live, Functions.Source.Ctx.initial]
    · refine
        { breakScope := ?_
          continueScope := ?_
          returnsLive := ?_
          leaveScope := ?_ }
      · simp [Functions.Source.Ctx.initial]
      · simp [Functions.Source.Ctx.initial]
      · simpa [AllocationInteractionCursor.RootArtifact.cursor,
          mainRoot.returns, mainRoot.live]
      · simp [Functions.Source.Ctx.initial]
    · cases mode with
      | stack => trivial
      | scratch frameDepth frameWords =>
          simp only [AllocationInteractionForward.FrameCapacity]
          rw [hSetup.owned.scratch_words, hWords]
  · exact
      AllocationInteractionControlAgreement.Agreement.noControl
        (by rfl) (by rfl) (by rfl)

/-- Preserve the compiler-selected main body after checked scratch setup.  All
recursive source calls are discharged by the pass-owned source-fuel fixed
point; no callee oracle or generated body premise reaches this interface. -/
theorem body
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target targetFinal : Expressions.InteractionSemantics.RunState}
    {frameBase targetFuel sourceFuel : Nat}
    {mode : ActivationMode}
    (mainRoot : MainRoot prepared)
    (hSetup :
      ScratchSetupResult prepared config source target
        frameBase mode targetFinal targetFuel)
    (hProgramScoped : program.Scoped)
    (hSafety :
      AllocationInteractionSafety.SourceSafety program.memoryContract)
    (hFrameConfig : compilation.frameConfig? = some config)
    (hFuelBudget :
      Budget config (mainSetupDepth compilation + sourceFuel))
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          Functions.Source.Ctx.initial sourceFuel
          mainRoot.root.sourceBlock source)) :
    Simulation.Interaction.Rel
      (AllocationInteractionResourceComposition.RuntimeResultRel
        program.memoryContract mainRoot.root.lowerCtx
        mainRoot.root.cursor.finalState mainRoot.root.cursor.finalLocals
        mainRoot.root.cursor.plan mainRoot.root.returns
        (Functions.Scope.Block.outEnv
          ((mainRoot.root.slots.returns.map Prod.fst).reverse ++
            (mainRoot.root.slots.params.map Prod.fst).reverse)
          mainRoot.root.sourceBlock)
        frameBase mode Functions.Source.Ctx.initial
        { Functions.Source.Ctx.initial with
          scope := Functions.Scope.Block.outEnv
            ((mainRoot.root.slots.returns.map Prod.fst).reverse ++
              (mainRoot.root.slots.params.map Prod.fst).reverse)
            mainRoot.root.sourceBlock }
        config (mainSetupDepth compilation) targetFinal)
      (Functions.InteractionSemantics.Block.openRun program
        Functions.Source.Ctx.initial sourceFuel
        mainRoot.root.sourceBlock source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        (AllocationInteractionRecursive.targetBudget mainRoot.root.cursor
          sourceFuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            mainRoot.root.cursor.compiled))
        { stmts := mainRoot.root.cursor.compiled } targetFinal) := by
  have hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (compilation := compilation) program.memoryContract
        compilation.recipe.frameWords (sourceFuel + 1) :=
    AllocationInteractionRecursiveRuntime.complete
      (compilation := compilation) hProgramScoped hSafety (sourceFuel + 1)
  have hBoundary :=
    hSetup.boundary mainRoot hFrameConfig hFuelBudget
  exact
    AllocationInteractionRecursiveResource.RecursiveOpenRuntime.at_targetFuel
      hRecursive mainRoot.root.cursor (by omega) (Nat.le_refl _)
      hBoundary hFuelBudget hSuccess

end ScratchSetupResult

end AllocationInteractionProgram
end Functions
end EvmCompiler
