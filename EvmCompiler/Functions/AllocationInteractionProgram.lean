import EvmCompiler.Functions.AllocationInteractionProgramArtifact
import EvmCompiler.Functions.AllocationInteractionFramePreservation
import EvmCompiler.Functions.AllocationInteractionExecutionRuntime
import EvmCompiler.Functions.AllocationInteractionStackRuntime
import EvmCompiler.Functions.AllocationInteractionPrelude

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

/-- Source/compiler-input-facing scratch capacity for the selected allocation.
It quantifies only over the deterministic validation and memory-contract
configuration computed from the source program; stack-only compilations make
the premise vacuous. -/
def ResourceSafe
    (allocation : Locals.Allocation.ProgramPlan)
    (program : Functions.Program) (sourceFuel : Nat) : Prop :=
  ∀ recipe stackSlots config,
    AllocationLowering.validatePlan? allocation program =
        some (recipe, stackSlots) →
    AllocationSupport.scratchFrameConfig?
        program.memoryContract recipe.frameWords = some config →
    Budget config
      ((if AllocationLowering.mainNeedsFrame recipe stackSlots then 1 else 0) +
        sourceFuel)

/-- Source/allocation-facing safety of the Structured code selected by the
ordinary allocation lowerer. This is semantic execution safety, not generated
compiler evidence. -/
def StructuredFrameSafe
    (allocation : Locals.Allocation.ProgramPlan)
    (program : Functions.Program) : Prop :=
  forall expressions,
    AllocationLowering.lowerExpressionsFromAllocation?
        allocation program = some expressions ->
      expressions.toStructured.FrameSafe

theorem ResourceSafe.compilation
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {config : Config} {sourceFuel : Nat}
    (hSafe : ResourceSafe allocation program sourceFuel)
    (hConfig : compilation.frameConfig? = some config) :
    Budget config (mainSetupDepth compilation + sourceFuel) := by
  apply hSafe compilation.recipe compilation.stackSlots config
    compilation.validate
  simpa [Compilation.frameConfig?] using hConfig

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

theorem targetCodeImage
    {contract : MemoryContract.Contract}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    {image : ByteArray}
    (hRel : InitialRel contract source target)
    (hSource : source.shared.executionEnv.codeBytes = image) :
    target.evm.executionEnv.codeBytes = image := by
  have hEnv := hRel.shared.executionEnv_eq
  have hCodeBytes :
      source.shared.executionEnv.codeBytes =
        target.evm.executionEnv.codeBytes := by
    exact congrArg (fun env => env.codeBytes) hEnv
  exact hCodeBytes.symm.trans hSource

end InitialRel

/-- Observable state relation after the distinguished program activation has
ended and compiler-owned locals are no longer live. -/
structure FinalStateRel
    (contract : MemoryContract.Contract)
    (source : Functions.InteractionSemantics.State)
    (target : Expressions.InteractionSemantics.RunState) : Prop where
  shared : SharedRel contract source.shared target.evm.toSharedState

/-- Whole-program outcome relation.  Allocation representation is erased at
the public boundary, while control mode and the cleaned regular stack remain
observable. -/
inductive OutcomeRel
    (contract : MemoryContract.Contract) :
    Functions.InteractionSemantics.Outcome →
      Expressions.InteractionSemantics.Outcome → Prop where
  | regular {source target}
      (state : FinalStateRel contract source target)
      (stack : target.evm.stack = []) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.regular source)
        (Structured.EffectSemantics.Outcome.regular target)
  | brk {source target}
      (state : FinalStateRel contract source target) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.brk source)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont {source target}
      (state : FinalStateRel contract source target) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.cont source)
        (Structured.EffectSemantics.Outcome.cont target)
  | leave {source target}
      (state : FinalStateRel contract source target) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.leave source)
        (Structured.EffectSemantics.Outcome.leave target)
  | halt (kind : Assembly.HaltKind) {source target}
      (state : FinalStateRel contract source target) :
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.halt kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

abbrev OpenOutcomeRel (contract : MemoryContract.Contract) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (OutcomeRel contract)

/-- Terminal whole-program Functions outcomes at the allocation boundary. -/
def SourceHalted :
    Except EVMException Functions.InteractionSemantics.Outcome -> Prop
  | .ok { mode := .halt _ , .. } => True
  | _ => False

/-- Terminal whole-program Expressions outcomes produced by allocation. -/
def TargetHalted :
    Except EVMException Expressions.InteractionSemantics.Outcome -> Prop
  | .ok { mode := .halt _ , .. } => True
  | _ => False

namespace SourceHalted

theorem successful
    {run : Simulation.Interaction
      EVMException Functions.InteractionSemantics.Outcome}
    (hHalted : Simulation.Interaction.AllDone SourceHalted run) :
    Simulation.Interaction.Successful run := by
  apply Simulation.Interaction.AllDone.mono hHalted
  intro outcome hOutcome
  cases outcome with
  | error error => cases hOutcome
  | ok source => trivial

end SourceHalted

namespace OpenOutcomeRel

theorem targetHalted_of_sourceHalted
    {contract : MemoryContract.Contract}
    {source : Except EVMException Functions.InteractionSemantics.Outcome}
    {target : Except EVMException Expressions.InteractionSemantics.Outcome}
    (hRel : OpenOutcomeRel contract source target)
    (hSource : SourceHalted source) :
    TargetHalted target := by
  cases hRel with
  | error hError => cases hSource
  | ok hOutcome =>
      cases hOutcome with
      | regular state stack => cases hSource
      | brk state => cases hSource
      | cont state => cases hSource
      | leave state => cases hSource
      | halt kind state => trivial

theorem allDone_targetHalted
    {contract : MemoryContract.Contract}
    {sourceRun : Simulation.Interaction
      EVMException Functions.InteractionSemantics.Outcome}
    {targetRun : Simulation.Interaction
      EVMException Expressions.InteractionSemantics.Outcome}
    (hRel : Simulation.Interaction.Rel (OpenOutcomeRel contract)
      sourceRun targetRun)
    (hSource : Simulation.Interaction.AllDone SourceHalted sourceRun) :
    Simulation.Interaction.AllDone TargetHalted targetRun := by
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_left hRel hSource
  apply Simulation.Interaction.Rel.allDone_right hStrong
  intro sourceDone targetDone hDone
  exact targetHalted_of_sourceHalted hDone.1 hDone.2

end OpenOutcomeRel

namespace FinalStateRel

theorem of_activationOutcome
    {contract : MemoryContract.Contract} {plan : Locals.Allocation.Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : Functions.InteractionSemantics.Outcome}
    {target : Expressions.InteractionSemantics.Outcome}
    (hRel :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        source target) :
    FinalStateRel contract source.state target.state := by
  cases hRel with
  | regular state | brk _ _ _ state | cont _ _ _ state =>
      exact ⟨state.shared⟩
  | leave state => exact ⟨state.shared⟩
  | halt kind state => exact ⟨state.shared⟩

end FinalStateRel

namespace OutcomeRel

theorem of_nonregular_activation
    {contract : MemoryContract.Contract} {plan : Locals.Allocation.Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {source : Functions.InteractionSemantics.Outcome}
    {target : Expressions.InteractionSemantics.Outcome}
    (hRel :
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        source target)
    (hNonregular : source.mode ≠ .regular) :
    OutcomeRel contract source target := by
  cases hRel with
  | regular state => exact False.elim (hNonregular rfl)
  | brk defined stackLength modeMatches state =>
      exact .brk ⟨state.shared⟩
  | cont defined stackLength modeMatches state =>
      exact .cont ⟨state.shared⟩
  | leave state => exact .leave ⟨state.shared⟩
  | halt kind state => exact .halt kind ⟨state.shared⟩

end OutcomeRel

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

/-- Execute the exact top-level cleanup selected by the Locals compiler after
a regular main-body result.  The theorem intentionally erases stack/scratch
representation instead of pretending that a scratch frame remains live after
its frame pointer is popped. -/
theorem regularCleanup
    {contract : MemoryContract.Contract}
    {program : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Locals.Allocation.Plan}
    {live : List Locals.Name} {frameBase targetFuel : Nat}
    {mode : ActivationMode}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    {cleanup : Structured.Code}
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hCleanup : localsCtx.cleanupTo? 0 = some cleanup)
    (hFuel : 2 ≤ targetFuel) :
    ∃ targetFinal,
      Expressions.InteractionSemantics.Block.openRun program targetFuel
          { stmts := Locals.codeStmt cleanup } target =
        .done (.ok (Structured.Outcome.regular targetFinal)) ∧
      OutcomeRel contract
        (Functions.Source.Effectful.Outcome.regular
          (source.restrictTo []))
        (Structured.Outcome.regular targetFinal) := by
  obtain ⟨_hDepth, hCleanupCode⟩ :=
    AllocationInteractionCleanup.Plain.cleanupTo?_shape hCleanup
  have hPopBound :
      localsCtx.layout.length ≤ target.evm.stack.length := by
    rw [hInvariant.stackLength]
  obtain ⟨targetFinal, hRun, hFinalStack, hShared, _hReturns⟩ :=
    Locals.InteractionPreservation.Code.openRun_replicate_pop
      localsCtx.layout.length hPopBound
  have hTargetRun :=
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
      program targetFuel cleanup target targetFinal hFuel
        (by simpa [hCleanupCode] using hRun)
  refine ⟨targetFinal, by simpa [Locals.codeStmt] using hTargetRun, ?_⟩
  apply OutcomeRel.regular
  · refine ⟨?_⟩
    rw [hShared]
    simpa [Locals.Source.State.restrictTo] using hInvariant.state.shared
  · rw [hFinalStack, ← hInvariant.stackLength]
    exact List.drop_length

/-- Append compiler-owned top-level cleanup to any related main-body run.
Regular results execute cleanup and erase locals; abrupt and terminal results
skip the unreachable suffix with their exact mode preserved. -/
theorem closeBody
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {sourceFuel targetFuel : Nat}
    {sourceBlock : Functions.Block}
    {bodyCode : List Expressions.Stmt}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Locals.Allocation.Plan}
    {returns regularLive : List Locals.Name} {frameBase : Nat}
    {entryMode : ActivationMode}
    {regularCtx : Functions.Source.Ctx}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    {cleanup : Structured.Code}
    (hCleanup : localsCtx.cleanupTo? 0 = some cleanup)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.Rel
        (AllocationInteractionComposition.OpenControlResultRel contract
          lowerCtx lowerState localsCtx plan returns regularLive frameBase
          entryMode Functions.Source.Ctx.initial regularCtx)
        (Functions.InteractionSemantics.Block.openRun sourceProgram
          Functions.Source.Ctx.initial sourceFuel sourceBlock source)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.Rel (OpenOutcomeRel contract)
      (Functions.InteractionSemantics.Block.openRunScoped sourceProgram
        Functions.Source.Ctx.initial sourceBlock sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := bodyCode ++ Locals.codeStmt cleanup } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  unfold Functions.InteractionSemantics.Block.openRunScoped
    Functions.Source.Canonical.Block.runScoped
    Functions.Source.Effectful.Control.Block.runScoped
  apply Simulation.Interaction.Rel.bind_custom hBody
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError => exact .done (.error hError)
  | ok hResult =>
      cases hResult with
      | @regular sourceAfter targetAfter modeAfter hInvariant hSameFrame
          hControl =>
          obtain ⟨targetFinal, hTargetCleanup, hOutcome⟩ :=
            regularCleanup hInvariant hCleanup hCleanupFuel
              (program := targetProgram)
          change
            Simulation.Interaction.Rel (OpenOutcomeRel contract)
              (Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  (sourceAfter.restrictTo [])))
              (Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetFuel - bodyCode.length)
                { stmts := Locals.codeStmt cleanup } targetAfter)
          rw [hTargetCleanup]
          exact .done (.ok hOutcome)
      | nonregular hNonregular hSameFrame hControl hState =>
          have hOutcome :=
            OutcomeRel.of_nonregular_activation hState hNonregular
          cases hState with
          | regular state => exact False.elim (hNonregular rfl)
          | brk defined stackLength modeMatches state =>
              exact .done (.ok hOutcome)
          | cont defined stackLength modeMatches state =>
              exact .done (.ok hOutcome)
          | leave state => exact .done (.ok hOutcome)
          | halt kind state => exact .done (.ok hOutcome)

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
  codeOnly :
    ∀ stmt, stmt ∈ prepared.allocatorCode ++ prepared.frameCode →
      ∃ code, stmt = .code code
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
  codeOnly :
    ∀ stmt, stmt ∈ prepared.allocatorCode ++ prepared.frameCode →
      ∃ code, stmt = .code code
  invariant :
    AllocationContext.ActivationInvariant program.memoryContract
      artifact.lowerCtx artifact.start prepared.bodyCtx artifact.plan []
      0 .stack source target
  returns : target.returns = target.returns

/-- Re-run a checked flat setup prefix at the larger fuel retained by whole
program composition. -/
private theorem setupExecutionAt
    {program : Expressions.Program}
    {code : List Expressions.Stmt}
    {source final : Expressions.InteractionSemantics.RunState}
    {storedFuel targetFuel : Nat}
    (hStoredFuel : storedFuel = code.length + 1)
    (hCodeOnly :
      ∀ stmt, stmt ∈ code → ∃ rawCode, stmt = .code rawCode)
    (hExecution :
      Expressions.InteractionSemantics.Block.openRun program storedFuel
          { stmts := code } source =
        .done (.ok (Structured.Outcome.regular final)))
    (hTargetFuel : code.length < targetFuel) :
    Expressions.InteractionSemantics.Block.openRun program targetFuel
        { stmts := code } source =
      .done (.ok (Structured.Outcome.regular final)) := by
  have hStoredBound : code.length < storedFuel := by
    omega
  calc
    Expressions.InteractionSemantics.Block.openRun program targetFuel
        { stmts := code } source =
        Expressions.InteractionSemantics.Block.openRun program storedFuel
          { stmts := code } source :=
      Expressions.InteractionSemantics.Block.openRun_codeOnly_fuel_eq
        program code hCodeOnly targetFuel storedFuel source hTargetFuel
          hStoredBound
    _ = .done (.ok (Structured.Outcome.regular final)) := hExecution

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
      codeOnly := by simp [hAllocatorCode, hFrameCode]
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
        codeOnly := ?_
        invariant := hActivation
        ready := ?_
        owned := ?_
        returns := ?_ }⟩
    · simp [hAllocatorCode, hFrameCode]
    · simpa [hAllocatorCode, hFrameCode] using hTargetRun
    · simp [hAllocatorCode, hFrameCode]
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
        codeOnly := ?_
        invariant := hActivation
        ready := ?_
        owned := ?_
        returns := hInitReturns }⟩
    · simp [hAllocatorCode, hFrameCode]
    · simpa [hAllocatorCode, hFrameCode] using hTargetRun
    · simp [hAllocatorCode, hFrameCode]
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

/-- Preserve the compiler-selected main body after empty stack-only setup.
The no-allocator fact comes from ordinary lowering and internally discharges
the all-stack callee condition. -/
theorem body
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    {targetFuel sourceFuel bodyTargetFuel : Nat}
    (mainRoot : MainRoot prepared)
    (hSetup : StackSetupResult prepared source target targetFuel)
    (hNoAllocator :
      AllocationLowering.mainNeedsAllocator
          compilation.recipe compilation.stackSlots = false)
    (hProgramScoped : program.Scoped)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe
        program.memoryContract program Functions.Source.Ctx.initial sourceFuel
          mainRoot.root.sourceBlock source)
    (hTargetCapacity :
      AllocationInteractionRecursive.targetBudget mainRoot.root.cursor
          sourceFuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            mainRoot.root.cursor.compiled) ≤
        bodyTargetFuel) :
    Simulation.Interaction.Rel
      (AllocationInteractionComposition.OpenControlResultRel
        program.memoryContract mainRoot.root.lowerCtx
        mainRoot.root.cursor.finalState mainRoot.root.cursor.finalLocals
        mainRoot.root.cursor.plan mainRoot.root.returns
        (Functions.Scope.Block.outEnv
          ((mainRoot.root.slots.returns.map Prod.fst).reverse ++
            (mainRoot.root.slots.params.map Prod.fst).reverse)
          mainRoot.root.sourceBlock)
        0 .stack Functions.Source.Ctx.initial
        { Functions.Source.Ctx.initial with
          scope := Functions.Scope.Block.outEnv
            ((mainRoot.root.slots.returns.map Prod.fst).reverse ++
              (mainRoot.root.slots.params.map Prod.fst).reverse)
            mainRoot.root.sourceBlock })
      (Functions.InteractionSemantics.Block.openRun program
        Functions.Source.Ctx.initial sourceFuel
        mainRoot.root.sourceBlock source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        bodyTargetFuel
        { stmts := mainRoot.root.cursor.compiled } target) := by
  have hAllStack :
      AllocationInteractionStackRuntime.AllFunctionsStack compilation :=
    (artifact.components.stackOnly_of_no_allocator hNoAllocator).2.1
  have hRecursive :
      AllocationInteractionStackRuntime.ExecutionSafeRecursiveOpenRuntime
        (compilation := compilation) program.memoryContract (sourceFuel + 1) :=
    AllocationInteractionStackRuntime.complete
      (compilation := compilation) hAllStack hProgramScoped (sourceFuel + 1)
  exact
    AllocationInteractionStackRuntime.ExecutionSafeRecursiveOpenRuntime.at_targetFuel
      hRecursive mainRoot.root.cursor (by omega) hTargetCapacity
      (hSetup.boundary mainRoot) hExecutionSafe

/-- Compose empty stack setup, the recursively preserved main body, and exact
top-level cleanup at one retained target fuel. -/
theorem closedBody
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    {setupFuel sourceFuel bodyTargetFuel : Nat}
    (mainRoot : MainRoot prepared)
    (hSetup : StackSetupResult prepared source target setupFuel)
    (hNoAllocator :
      AllocationLowering.mainNeedsAllocator
          compilation.recipe compilation.stackSlots = false)
    (hProgramScoped : program.Scoped)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe
        program.memoryContract program Functions.Source.Ctx.initial sourceFuel
          mainRoot.root.sourceBlock source)
    (hTargetCapacity :
      AllocationInteractionRecursive.targetBudget mainRoot.root.cursor
          sourceFuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            mainRoot.root.cursor.compiled) ≤
        bodyTargetFuel)
    (hCleanupFuel :
      2 ≤ bodyTargetFuel - mainRoot.root.cursor.compiled.length) :
    Simulation.Interaction.Rel (OpenOutcomeRel program.memoryContract)
      (Functions.InteractionSemantics.Block.openRunScoped program
        Functions.Source.Ctx.initial mainRoot.root.sourceBlock sourceFuel
        source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        ((prepared.allocatorCode ++ prepared.frameCode).length +
          bodyTargetFuel)
        { stmts :=
            (prepared.allocatorCode ++ prepared.frameCode) ++
              mainRoot.root.cursor.compiled ++
                Locals.codeStmt prepared.cleanup }
        target) := by
  have hBody :=
    hSetup.body mainRoot hNoAllocator hProgramScoped hExecutionSafe
      hTargetCapacity
  have hClosed :=
    closeBody
      (hCleanup := by
        simpa [AllocationInteractionCursor.RootArtifact.cursor,
          mainRoot.finalLocals] using prepared.cleanupCode)
      hCleanupFuel hBody
  have hSetupRun :=
    setupExecutionAt hSetup.targetFuel_eq hSetup.codeOnly hSetup.execution
      (show
        (prepared.allocatorCode ++ prepared.frameCode).length <
          (prepared.allocatorCode ++ prepared.frameCode).length +
            bodyTargetFuel by
        have : 0 < bodyTargetFuel := by omega
        omega)
  rw [List.append_assoc]
  rw [Expressions.InteractionSemantics.Block.openRun_append expressions
    (prepared.allocatorCode ++ prepared.frameCode)
    (mainRoot.root.cursor.compiled ++ Locals.codeStmt prepared.cleanup)
    ((prepared.allocatorCode ++ prepared.frameCode).length + bodyTargetFuel)
    target, hSetupRun]
  simp only [Simulation.Interaction.bind_done_ok]
  have hFuel :
      (prepared.allocatorCode ++ prepared.frameCode).length +
            bodyTargetFuel -
          (prepared.allocatorCode ++ prepared.frameCode).length =
        bodyTargetFuel := by omega
  simpa [hFuel, List.append_assoc] using hClosed

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
    {frameBase targetFuel sourceFuel bodyTargetFuel : Nat}
    {mode : ActivationMode}
    (mainRoot : MainRoot prepared)
    (hSetup :
      ScratchSetupResult prepared config source target
        frameBase mode targetFinal targetFuel)
    (hProgramScoped : program.Scoped)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe
        program.memoryContract program Functions.Source.Ctx.initial sourceFuel
          mainRoot.root.sourceBlock source)
    (hFrameConfig : compilation.frameConfig? = some config)
    (hFuelBudget :
      Budget config (mainSetupDepth compilation + sourceFuel))
    (hTargetCapacity :
      AllocationInteractionRecursive.targetBudget mainRoot.root.cursor
          sourceFuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            mainRoot.root.cursor.compiled) ≤
        bodyTargetFuel) :
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
        bodyTargetFuel
        { stmts := mainRoot.root.cursor.compiled } targetFinal) := by
  have hRecursive :
      AllocationInteractionRecursiveResource.ExecutionSafeRecursiveOpenRuntime
        (compilation := compilation) program.memoryContract
        compilation.recipe.frameWords (sourceFuel + 1) :=
    AllocationInteractionExecutionRuntime.complete
      (compilation := compilation) hProgramScoped (sourceFuel + 1)
  have hBoundary :=
    hSetup.boundary mainRoot hFrameConfig hFuelBudget
  exact
    AllocationInteractionRecursiveResource.ExecutionSafeRecursiveOpenRuntime.at_targetFuel
      hRecursive mainRoot.root.cursor (by omega) hTargetCapacity
      hBoundary hFuelBudget hExecutionSafe

/-- Compose scratch allocator/frame setup, the recursively preserved main body,
and exact top-level cleanup while keeping allocator evidence internal. -/
theorem closedBody
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {artifact : MainArtifact compilation}
    {prepared : MainPrepared artifact}
    {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target targetFinal : Expressions.InteractionSemantics.RunState}
    {frameBase setupFuel sourceFuel bodyTargetFuel : Nat}
    {mode : ActivationMode}
    (mainRoot : MainRoot prepared)
    (hSetup :
      ScratchSetupResult prepared config source target frameBase mode
        targetFinal setupFuel)
    (hProgramScoped : program.Scoped)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Block.ExecutionSafe
        program.memoryContract program Functions.Source.Ctx.initial sourceFuel
          mainRoot.root.sourceBlock source)
    (hFrameConfig : compilation.frameConfig? = some config)
    (hFuelBudget :
      Budget config (mainSetupDepth compilation + sourceFuel))
    (hTargetCapacity :
      AllocationInteractionRecursive.targetBudget mainRoot.root.cursor
          sourceFuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            mainRoot.root.cursor.compiled) ≤
        bodyTargetFuel)
    (hCleanupFuel :
      2 ≤ bodyTargetFuel - mainRoot.root.cursor.compiled.length) :
    Simulation.Interaction.Rel (OpenOutcomeRel program.memoryContract)
      (Functions.InteractionSemantics.Block.openRunScoped program
        Functions.Source.Ctx.initial mainRoot.root.sourceBlock sourceFuel
        source)
      (Expressions.InteractionSemantics.Block.openRun expressions
        ((prepared.allocatorCode ++ prepared.frameCode).length +
          bodyTargetFuel)
        { stmts :=
            (prepared.allocatorCode ++ prepared.frameCode) ++
              mainRoot.root.cursor.compiled ++
                Locals.codeStmt prepared.cleanup }
        target) := by
  have hBodyRaw :=
    hSetup.body mainRoot hProgramScoped hExecutionSafe hFrameConfig hFuelBudget
      hTargetCapacity
  have hBody :=
    Simulation.Interaction.Rel.mono hBodyRaw
      (fun _left _right hDone => hDone.1)
  have hClosed :=
    closeBody
      (hCleanup := by
        simpa [AllocationInteractionCursor.RootArtifact.cursor,
          mainRoot.finalLocals] using prepared.cleanupCode)
      hCleanupFuel hBody
  have hSetupRun :=
    setupExecutionAt hSetup.targetFuel_eq hSetup.codeOnly hSetup.execution
      (show
        (prepared.allocatorCode ++ prepared.frameCode).length <
          (prepared.allocatorCode ++ prepared.frameCode).length +
            bodyTargetFuel by
        have : 0 < bodyTargetFuel := by omega
        omega)
  rw [List.append_assoc]
  rw [Expressions.InteractionSemantics.Block.openRun_append expressions
    (prepared.allocatorCode ++ prepared.frameCode)
    (mainRoot.root.cursor.compiled ++ Locals.codeStmt prepared.cleanup)
    ((prepared.allocatorCode ++ prepared.frameCode).length + bodyTargetFuel)
    target, hSetupRun]
  simp only [Simulation.Interaction.bind_done_ok]
  have hFuel :
      (prepared.allocatorCode ++ prepared.frameCode).length +
            bodyTargetFuel -
          (prepared.allocatorCode ++ prepared.frameCode).length =
        bodyTargetFuel := by omega
  simpa [hFuel, List.append_assoc] using hClosed

end ScratchSetupResult

/-- Compiler-selected whole-main open-interaction preservation. Every
allocation, lowering, setup, recursive-root, and cleanup artifact is
constructed internally. -/
theorem mainForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (hLower :
      AllocationLowering.lowerExpressionsFromAllocation? allocation program =
        some expressions)
    {sourceFuel : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hProgramScoped : program.Scoped)
    (hExecutionSafe :
      AllocationInteractionSafeSemantics.Program.ExecutionSafe
        program.memoryContract sourceFuel program source)
    (hResourceSafe : ResourceSafe allocation program sourceFuel)
    (hInitial : InitialRel program.memoryContract source target) :
    ∃ targetFuel,
      Simulation.Interaction.Rel (OpenOutcomeRel program.memoryContract)
        (Functions.InteractionSemantics.Program.openRunState
          sourceFuel program source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          targetFuel expressions.body target) := by
  obtain ⟨compilation⟩ := Compilation.of_lowering hLower
  obtain ⟨artifact⟩ := MainArtifact.ofCompilation compilation
  obtain ⟨prepared⟩ := MainPrepared.ofArtifact artifact
  obtain ⟨mainRoot⟩ := prepared.rootArtifact hProgramScoped
  obtain ⟨sourcePrefix, hSourceBody, hPrelude⟩ :=
    AllocationLowering.splitPrelude_components artifact.components.split
  have hProgramBody :
      program.body =
        { stmts := sourcePrefix ++ artifact.components.rest } :=
    block_eq_of_stmts_eq hSourceBody
  obtain ⟨hSourceCtx, hSourceLength, hSourceCodeOnly⟩ :=
    AllocationInteractionPrelude.compile_shape hPrelude prepared.compileSource
  have hWholeScoped := hProgramScoped.2
  rw [hProgramBody] at hWholeScoped
  have hPrefixScoped : Functions.Scope.StmtList.Scoped [] sourcePrefix :=
    AllocationInteractionPrelude.scopedPrefix hPrelude hWholeScoped
  let tailSourceFuel := sourceFuel - sourcePrefix.length
  let bodyTargetFuel :=
    AllocationInteractionRecursive.targetBudget mainRoot.root.cursor
        tailSourceFuel
        (AllocationInteractionTargetFuel.stmtListNestedSize
          mainRoot.root.cursor.compiled) + 2
  let setupCode := prepared.allocatorCode ++ prepared.frameCode
  let targetFuel := sourcePrefix.length + setupCode.length + bodyTargetFuel
  have hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Program.openRunState
          sourceFuel program source) := by
    rw [←
      AllocationInteractionSafeSemantics.Program.openRunState_eq_ordinary_of_executionSafe
        program.memoryContract sourceFuel program source hExecutionSafe]
    exact hExecutionSafe
  have hOpenSuccess :=
    Functions.InteractionSemantics.Program.successful_openRunState_open hSuccess
  have hOpenSafe := hExecutionSafe.body
  rw [hProgramBody,
    Functions.InteractionSemantics.Block.openRun_append] at hOpenSuccess
  unfold AllocationInteractionSafeSemantics.Block.ExecutionSafe at hOpenSafe
  rw [hProgramBody,
    AllocationInteractionSafeSemantics.Block.openRun_append] at hOpenSafe
  have hPrefixSuccess :=
    Simulation.Interaction.Successful.bind_left hOpenSuccess
  have hPrefixSafe := Simulation.Interaction.Successful.bind_left hOpenSafe
  have hContinuationSuccess :=
    Simulation.Interaction.Successful.bind_inv hOpenSuccess
  have hContinuationSafe :=
    Simulation.Interaction.Successful.bind_inv hOpenSafe
  rw [AllocationInteractionSafeSemantics.Block.openRun_eq_ordinary_of_successful
    program.memoryContract program Functions.Source.Ctx.initial sourceFuel
      { stmts := sourcePrefix } source hPrefixSafe] at hContinuationSafe
  have hPrefix :=
    AllocationInteractionPrelude.forward (targetProgram := expressions)
      hPrelude prepared.compileSource
      hPrefixScoped (InitialRel.invariant artifact hInitial)
      (targetFuel := targetFuel) (by
        dsimp [targetFuel, setupCode, bodyTargetFuel]
        omega) hPrefixSafe
  have hPrefixStrong :=
    Simulation.Interaction.Rel.strengthen_right
      (Simulation.Interaction.Rel.strengthen_left
        (Simulation.Interaction.Rel.strengthen_left hPrefix
          hContinuationSuccess)
        hContinuationSafe)
      (Expressions.InteractionReturns.Block.openRun_returns expressions
        targetFuel { stmts := prepared.sourceCode } target)
  refine ⟨targetFuel, ?_⟩
  change
    Simulation.Interaction.Rel (OpenOutcomeRel program.memoryContract)
      (Functions.InteractionSemantics.Block.openRunScoped program
        Functions.Source.Ctx.initial program.body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        expressions.body target)
  rw [hProgramBody,
    Functions.InteractionSemantics.Block.openRunScoped_append]
  rw [prepared.output]
  rw [show prepared.sourceCode ++ prepared.allocatorCode ++
          prepared.frameCode ++ prepared.bodyCode ++
          Locals.codeStmt prepared.cleanup =
        prepared.sourceCode ++
          (setupCode ++ mainRoot.root.cursor.compiled ++
            Locals.codeStmt prepared.cleanup) by
      simp [setupCode, AllocationInteractionCursor.RootArtifact.cursor,
        mainRoot.compiled, List.append_assoc]]
  rw [Expressions.InteractionSemantics.Block.openRun_append expressions
    prepared.sourceCode
    (setupCode ++ mainRoot.root.cursor.compiled ++
      Locals.codeStmt prepared.cleanup)
    targetFuel target]
  apply Simulation.Interaction.Rel.bind_custom hPrefixStrong
  intro sourceDone targetDone hDone
  rcases hDone with
    ⟨⟨⟨hRelated, hTailSuccess⟩, hTailSafe⟩, hTargetReturns⟩
  cases hRelated with
  | error hError => exact False.elim hTailSuccess
  | @ok sourceResult targetOutcome hResult =>
      cases hResult with
      | @regular sourceAfter targetAfter mode hInvariant hSameFrame hControl =>
          cases hSameFrame
          cases hState : hInvariant.state with
          | stack hLiveStackOnly hActiveNoWrap hStateRel =>
              have hAfterInitial :
                  InitialRel program.memoryContract sourceAfter targetAfter :=
                { shared := ⟨hStateRel.machine, hStateRel.world⟩
                  stack :=
                    List.eq_nil_of_length_eq_zero (by
                      rw [hInvariant.stackLength]
                      rfl)
                  returns := by
                    have hReturns : targetAfter.returns = target.returns := by
                      simpa [Structured.InteractionReturns.OutcomeReturnsEq]
                        using hTargetReturns
                    exact hReturns.trans hInitial.returns
                  activeNoWrap := hActiveNoWrap }
              have hTailSuccess' :
                  Simulation.Interaction.Successful
                    (Functions.InteractionSemantics.Block.openRun program
                      Functions.Source.Ctx.initial tailSourceFuel
                      mainRoot.root.sourceBlock sourceAfter) := by
                simpa [tailSourceFuel, mainRoot.sourceBlock] using hTailSuccess
              have hTailSafe' :
                  AllocationInteractionSafeSemantics.Block.ExecutionSafe
                    program.memoryContract program Functions.Source.Ctx.initial
                      tailSourceFuel mainRoot.root.sourceBlock sourceAfter := by
                simpa [tailSourceFuel, mainRoot.sourceBlock] using hTailSafe
              have hCapacity :
                  AllocationInteractionRecursive.targetBudget
                      mainRoot.root.cursor tailSourceFuel
                      (AllocationInteractionTargetFuel.stmtListNestedSize
                        mainRoot.root.cursor.compiled) ≤
                    bodyTargetFuel := by
                dsimp [bodyTargetFuel]
                omega
              have hCleanupFuel :
                  2 ≤ bodyTargetFuel - mainRoot.root.cursor.compiled.length := by
                dsimp [bodyTargetFuel,
                  AllocationInteractionRecursive.targetBudget]
                omega
              cases artifact.components.runtimeSelection with
              | stackOnly hNoAllocator hNoFrame hFrameFunctions
                  hAllocatorPrelude hFramePrelude =>
                  have hSetup :=
                    AllocationInteractionProgram.MainPrepared.stackSetup
                      prepared hSourceCtx hNoAllocator hNoFrame hAfterInitial
                  have hClosed :=
                    StackSetupResult.closedBody mainRoot hSetup hNoAllocator
                      hProgramScoped hTailSafe' hCapacity hCleanupFuel
                  have hTargetTailFuel :
                      targetFuel - prepared.sourceCode.length =
                        setupCode.length + bodyTargetFuel := by
                    dsimp [targetFuel]
                    rw [hSourceLength]
                    omega
                  simpa [setupCode, hTargetTailFuel, tailSourceFuel,
                    mainRoot.sourceBlock,
                    Functions.InteractionSemantics.Block.openRunScoped,
                    Functions.Source.Canonical.Block.runScoped,
                    Functions.Source.Effectful.Control.Block.runScoped]
                    using hClosed
              | scratch config hFrameConfig hNeedsAllocator =>
                  obtain ⟨frameBase, mode, targetAfterSetup, setupFuel,
                      hSetup⟩ :=
                    AllocationInteractionProgram.MainPrepared.scratchSetup
                      prepared hSourceCtx hFrameConfig hNeedsAllocator
                        hAfterInitial
                  have hBudget :
                      Budget config
                        (mainSetupDepth compilation + tailSourceFuel) :=
                    Budget.mono (by
                      dsimp [tailSourceFuel]
                      omega)
                      (hResourceSafe.compilation hFrameConfig)
                  have hClosed :=
                    ScratchSetupResult.closedBody mainRoot hSetup
                      hProgramScoped hTailSafe' hFrameConfig hBudget hCapacity
                      hCleanupFuel
                  have hTargetTailFuel :
                      targetFuel - prepared.sourceCode.length =
                        setupCode.length + bodyTargetFuel := by
                    dsimp [targetFuel]
                    rw [hSourceLength]
                    omega
                  simpa [setupCode, hTargetTailFuel, tailSourceFuel,
                    mainRoot.sourceBlock,
                    Functions.InteractionSemantics.Block.openRunScoped,
                    Functions.Source.Canonical.Block.runScoped,
                    Functions.Source.Effectful.Control.Block.runScoped]
                    using hClosed
      | @nonregular sourceOutcome targetOutcome finalCtx mode hNonregular
          hSameFrame hControl hState =>
          have hOutcome :=
            OutcomeRel.of_nonregular_activation hState hNonregular
          cases hState with
          | regular state => exact False.elim (hNonregular rfl)
          | brk defined stackLength modeMatches state =>
              exact .done (.ok hOutcome)
          | cont defined stackLength modeMatches state =>
              exact .done (.ok hOutcome)
          | leave state => exact .done (.ok hOutcome)
          | halt kind state => exact .done (.ok hOutcome)

end AllocationInteractionProgram
end Functions
end EvmCompiler
