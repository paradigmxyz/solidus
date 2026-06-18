import EvmCompiler.Functions.AllocationInteractionCallResultResource
import EvmCompiler.Functions.AllocationInteractionCallReturnResource
import EvmCompiler.Functions.AllocationInteractionPreparedCallResources

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCallStatementResource

open AllocationInteractionCall
open AllocationInteractionCallResultResource
open AllocationInteractionComposition
open AllocationInteractionFrame
open AllocationInteractionFrameExecution
open AllocationInteractionFramePreservation
open AllocationInteractionRelation
open AllocationInteractionResourceComposition

namespace CallResultRel

/-- Return assignment changes only caller values; all compiler-owned static
context and stack-shape facts are inherited from the call boundary. -/
theorem callerInvariant_after_writeback
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {sourceInitial sourceAfterArgs sourceReturned : SourceState}
    {targetInitial targetFinal : TargetState}
    {targets : List Locals.Name} {returnValues : List Word}
    {returnStore : Locals.Source.Store}
    (hInitial :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode sourceInitial targetInitial)
    (hArgsVars : sourceAfterArgs.vars = sourceInitial.vars)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.vars =
        some returnStore)
    (hFinalRel :
      ActivationStateRel contract plan live 0 frameBase mode
        { shared := sourceReturned.shared, vars := returnStore } targetFinal)
    (hFinalStack : targetFinal.evm.stack.length = localsCtx.layout.length) :
    AllocationContext.ActivationInvariant contract lowerCtx lowerState
      localsCtx plan live frameBase mode
      { shared := sourceReturned.shared, vars := returnStore } targetFinal := by
  refine
    { compiler := hInitial.compiler
      planWF := hInitial.planWF
      defined := ?_
      state := hFinalRel
      stackLength := hFinalStack }
  have hAfterArgsDefined : LiveDefined live sourceAfterArgs :=
    hInitial.defined.congr_vars hArgsVars
  have hAssigned := hAfterArgsDefined.assignMany_preserves hAssign
  simpa [Locals.Source.State.withVars] using hAssigned

/-- Restore a suspended caller and run its exact compiler-emitted return stores
after one regular compiler-selected callee result. -/
theorem returned_writeback
    {contract : MemoryContract.Contract}
    {globalFrameWords callerDepth calleeDepth : Nat}
    {config : Config}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Plan} {callerLive : List Locals.Name}
    {callerFrameBase : Nat} {callerMode calleeMode : ActivationMode}
    {sourceAfterArgs sourceReturned : SourceState}
    {targetInitial targetCaller callerBase targetEntry callFinal : TargetState}
    {callerStack returnValues : List Word}
    {targets : List Locals.Name} {returnStore : Locals.Source.Store}
    {stores : Structured.Code}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hCallerRel :
      ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
        callerMode sourceAfterArgs callerBase)
    (hCallerOwned :
      ActivationOwned config callerDepth callerFrameBase callerMode)
    (hCallerDepth : callerDepth ≤ calleeDepth)
    (hBudget : Budget config callerDepth)
    (hCallerStack : callerBase.evm.stack = callerStack)
    (hInitialToBase :
      BoundedEffect config calleeDepth (callerDepth + 1)
        targetInitial callerBase)
    (hBaseToEntry :
      BoundedEffect config calleeDepth (callerDepth + 1)
        callerBase targetEntry)
    (hCalleeBound :
      activationProtectedBound calleeDepth calleeMode = callerDepth + 1)
    (hCall :
      AllocationInteractionCallResultResource.CallResultRel
        contract config calleeDepth calleeMode targetCaller targetEntry
        callerStack (.returned sourceReturned returnValues)
        (Structured.EffectSemantics.Outcome.regular callFinal))
    (hCallerContext :
      AllocationContext.ActivationExprContext callerLowerCtx callerLowerState
        callerLocalsCtx callerPlan callerLive callerMode)
    (hCallerWF : callerPlan.WellFormed)
    (hTargetsLive : ∀ target, target ∈ targets → target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.vars =
        some returnStore)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse targets.length =
        some stores) :
    ∃ targetAfterWrite,
      Structured.InteractionSemantics.Code.openRun stores callFinal =
          .done (.ok targetAfterWrite) ∧
        ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
          callerMode
          { shared := sourceReturned.shared, vars := returnStore }
          targetAfterWrite ∧
        targetAfterWrite.evm.stack.length = callerBase.evm.stack.length ∧
        BoundedEffect config calleeDepth
          (CallTargets.protectedBound callerDepth callerMode)
          targetInitial targetAfterWrite := by
  cases hCall with
  | returned hShared hStack _hReturns hCalleeEffect =>
      have hCalleeBounded :
          BoundedEffect config calleeDepth
            (activationProtectedBound calleeDepth calleeMode)
            targetEntry callFinal := by
        cases calleeMode <;> exact hCalleeEffect.to_boundedEffect
      rw [hCalleeBound] at hCalleeBounded
      have hCallBounded :
          BoundedEffect config calleeDepth (callerDepth + 1)
            callerBase callFinal :=
        hBaseToEntry.trans hCalleeBounded
      obtain
          ⟨targetAfterWrite, hStoresRun, hFinalRel, hFinalStack,
            hWriteEffect⟩ :=
        AllocationInteractionCallReturnResource.resume_and_writeback
          hConfig hCallerRel hCallerOwned hCallerDepth hBudget
          hShared.machine hShared.world
          (by simpa [hCallerStack] using hStack)
          hCallBounded hCallerContext hCallerWF hTargetsLive hTargetsNodup
          hAssign hStores
      have hProtected :
          CallTargets.protectedBound callerDepth callerMode ≤ callerDepth + 1 := by
        cases callerMode <;> simp [CallTargets.protectedBound]
      exact
        ⟨targetAfterWrite, hStoresRun, hFinalRel, hFinalStack,
          (BoundedEffect.weaken hProtected hInitialToBase).trans
            hWriteEffect⟩

/-- A stack-backed callee completes with return writeback and no frame-release
suffix. -/
theorem returned_without_release
    {contract : MemoryContract.Contract}
    {globalFrameWords callerDepth calleeDepth : Nat}
    {config : Config}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Plan} {callerLive returns : List Locals.Name}
    {callerFrameBase : Nat} {callerMode calleeMode : ActivationMode}
    {controlCtx : Functions.Source.Ctx}
    {sourceInitial sourceAfterArgs sourceReturned : SourceState}
    {targetInitial targetCaller callerBase targetEntry callFinal : TargetState}
    {callerStack returnValues : List Word}
    {targets : List Locals.Name} {returnStore : Locals.Source.Store}
    {stores : Structured.Code}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hInitial :
      AllocationContext.ActivationInvariant contract callerLowerCtx
        callerLowerState callerLocalsCtx callerPlan callerLive callerFrameBase
        callerMode sourceInitial targetInitial)
    (hArgsVars : sourceAfterArgs.vars = sourceInitial.vars)
    (hCallerRel :
      ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
        callerMode sourceAfterArgs callerBase)
    (hCallerOwned :
      ActivationOwned config callerDepth callerFrameBase callerMode)
    (hDepthEq : calleeDepth = callerDepth)
    (hBudget : Budget config callerDepth)
    (hCallerStack : callerBase.evm.stack = callerStack)
    (hCallerStackLength :
      callerBase.evm.stack.length = callerLocalsCtx.layout.length)
    (hInitialToBase :
      BoundedEffect config calleeDepth (callerDepth + 1)
        targetInitial callerBase)
    (hBaseToEntry :
      BoundedEffect config calleeDepth (callerDepth + 1)
        callerBase targetEntry)
    (hCalleeBound :
      activationProtectedBound calleeDepth calleeMode = callerDepth + 1)
    (hCall :
      AllocationInteractionCallResultResource.CallResultRel
        contract config calleeDepth calleeMode targetCaller targetEntry
        callerStack (.returned sourceReturned returnValues)
        (Structured.EffectSemantics.Outcome.regular callFinal))
    (hTargetsLive : ∀ target, target ∈ targets → target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.vars =
        some returnStore)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse targets.length =
        some stores) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun stores callFinal =
          .done (.ok targetFinal) ∧
        RuntimeResultRel contract callerLowerCtx callerLowerState
          callerLocalsCtx callerPlan returns callerLive callerFrameBase
          callerMode controlCtx controlCtx config callerDepth targetInitial
          (.ok
            (Functions.Source.Effectful.Outcome.regular
              { shared := sourceReturned.shared, vars := returnStore },
              controlCtx))
          (.ok (Structured.EffectSemantics.Outcome.regular targetFinal)) := by
  obtain ⟨targetFinal, hStoresRun, hFinalRel, hFinalStack, hEffect⟩ :=
    returned_writeback hConfig hCallerRel hCallerOwned
      (by omega) hBudget hCallerStack hInitialToBase hBaseToEntry
      hCalleeBound hCall hInitial.compiler hInitial.planWF hTargetsLive
      hTargetsNodup hAssign hStores
  have hInvariant :=
    callerInvariant_after_writeback hInitial hArgsVars hAssign hFinalRel
      (hFinalStack.trans hCallerStackLength)
  subst calleeDepth
  have hFinalEffect :
      ActivationEffect config callerDepth callerMode targetInitial targetFinal :=
    AllocationInteractionCallReturnResource.complete_without_release
      (frameBase := callerFrameBase) hEffect
  exact
    ⟨targetFinal, hStoresRun,
      ⟨Simulation.Interaction.ExceptRel.ok
          (ControlResultRel.regular hInvariant (SameFrame.refl callerMode)
            (Functions.Source.Ctx.SameControl.refl controlCtx)),
        Simulation.Interaction.ExceptRel.ok
          (OutcomeEffect.of_activation hFinalEffect)⟩⟩

/-- A scratch-backed callee writes returns, releases its one nested frame, and
restores the caller's exact activation resource. -/
theorem returned_with_release
    {contract : MemoryContract.Contract}
    {globalFrameWords callerDepth calleeDepth : Nat}
    {config : Config}
    {callerLowerCtx : AllocationLowering.Ctx}
    {callerLowerState : AllocationLowering.State}
    {callerLocalsCtx : Locals.Ctx}
    {callerPlan : Plan} {callerLive returns : List Locals.Name}
    {callerFrameBase : Nat} {callerMode calleeMode : ActivationMode}
    {controlCtx : Functions.Source.Ctx}
    {sourceInitial sourceAfterArgs sourceReturned : SourceState}
    {targetInitial targetCaller callerBase targetEntry callFinal : TargetState}
    {callerStack returnValues : List Word}
    {targets : List Locals.Name} {returnStore : Locals.Source.Store}
    {stores : Structured.Code}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hInitial :
      AllocationContext.ActivationInvariant contract callerLowerCtx
        callerLowerState callerLocalsCtx callerPlan callerLive callerFrameBase
        callerMode sourceInitial targetInitial)
    (hArgsVars : sourceAfterArgs.vars = sourceInitial.vars)
    (hCallerRel :
      ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
        callerMode sourceAfterArgs callerBase)
    (hCallerOwned :
      ActivationOwned config callerDepth callerFrameBase callerMode)
    (hDepthEq : calleeDepth = callerDepth + 1)
    (hBudget : Budget config callerDepth)
    (hCallerStack : callerBase.evm.stack = callerStack)
    (hCallerStackLength :
      callerBase.evm.stack.length = callerLocalsCtx.layout.length)
    (hInitialToBase :
      BoundedEffect config calleeDepth (callerDepth + 1)
        targetInitial callerBase)
    (hBaseToEntry :
      BoundedEffect config calleeDepth (callerDepth + 1)
        callerBase targetEntry)
    (hCalleeBound :
      activationProtectedBound calleeDepth calleeMode = callerDepth + 1)
    (hCall :
      AllocationInteractionCallResultResource.CallResultRel
        contract config calleeDepth calleeMode targetCaller targetEntry
        callerStack (.returned sourceReturned returnValues)
        (Structured.EffectSemantics.Outcome.regular callFinal))
    (hTargetsLive : ∀ target, target ∈ targets → target ∈ callerLive)
    (hTargetsNodup : targets.Nodup)
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.vars =
        some returnStore)
    (hStores :
      AllocationLowering.lowerCallTargetsCode?
          callerLowerCtx callerLowerState targets.reverse targets.length =
        some stores) :
    ∃ targetAfterWrite targetFinal,
      Structured.InteractionSemantics.Code.openRun stores callFinal =
          .done (.ok targetAfterWrite) ∧
        Structured.InteractionSemantics.Code.openRun
            (AllocationSupport.scratchFrameReleaseCode config)
            targetAfterWrite =
          .done (.ok targetFinal) ∧
        RuntimeResultRel contract callerLowerCtx callerLowerState
          callerLocalsCtx callerPlan returns callerLive callerFrameBase
          callerMode controlCtx controlCtx config callerDepth targetInitial
          (.ok
            (Functions.Source.Effectful.Outcome.regular
              { shared := sourceReturned.shared, vars := returnStore },
              controlCtx))
          (.ok (Structured.EffectSemantics.Outcome.regular targetFinal)) := by
  obtain ⟨targetAfterWrite, hStoresRun, hAfterWriteRel, hAfterWriteStack,
      hEffect⟩ :=
    returned_writeback hConfig hCallerRel hCallerOwned
      (by omega) hBudget hCallerStack hInitialToBase hBaseToEntry
      hCalleeBound hCall hInitial.compiler hInitial.planWF hTargetsLive
      hTargetsNodup hAssign hStores
  subst calleeDepth
  obtain ⟨hReleaseRun, hFinalRel, hFinalEffect⟩ :=
    AllocationInteractionCallReturnResource.complete_with_release
      hConfig hBudget hCallerOwned hAfterWriteRel hEffect
  let targetFinal :=
    scratchFrameReleaseTarget config callerDepth targetAfterWrite
  have hReleaseStack :
      targetFinal.evm.stack.length = callerLocalsCtx.layout.length := by
    change targetAfterWrite.evm.stack.length = callerLocalsCtx.layout.length
    exact hAfterWriteStack.trans hCallerStackLength
  have hInvariant :=
    callerInvariant_after_writeback hInitial hArgsVars hAssign hFinalRel
      hReleaseStack
  exact
    ⟨targetAfterWrite, targetFinal, hStoresRun, hReleaseRun,
      ⟨Simulation.Interaction.ExceptRel.ok
          (ControlResultRel.regular hInvariant (SameFrame.refl callerMode)
            (Functions.Source.Ctx.SameControl.refl controlCtx)),
        Simulation.Interaction.ExceptRel.ok
          (OutcomeEffect.of_activation hFinalEffect)⟩⟩

end CallResultRel

namespace SelectedCallee

/-- Realize one stack-backed selected callee from a completed canonical
argument phase, including the suspended caller and exact recursive call. -/
theorem stack_after_arguments
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : AllocationInteractionCursor.Compilation
      allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth callerFrameBase bodyFuel fuelBound
      targetExtra : Nat}
    {callerPlan : Plan} {callerLive : List Locals.Name}
    {callerMode : ActivationMode}
    {sourceAfterArgs : SourceState}
    {targetInitial targetAfterArgs : TargetState}
    {argValues : List Word} {paramStore : Locals.Source.Store}
    {reservation : MemoryContract.ScratchReservation}
    (hNeedsFrame : artifact.needsFrame = false)
    (hArgs :
      AllocationInteractionCallArgumentResources.ResultRel
        contract config allocatorDepth callerPlan callerLive 0 callerFrameBase
        argValues.length callerMode targetInitial
        (sourceAfterArgs, argValues) targetAfterArgs)
    (hInsert :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (hReservation : contract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract
          compilation.recipe.frameWords =
        some config)
    (hCallerOwned :
      ActivationOwned config allocatorDepth callerFrameBase callerMode)
    (hBudget : Budget config allocatorDepth)
    (hFuelBudget : Budget config (allocatorDepth + bodyFuel))
    (hTargetExtra : 3 ≤ targetExtra)
    (hBodyFuel : bodyFuel < fuelBound)
    (hBodySuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) bodyFuel fn.body
          (AllocationInteractionCall.CalleeEntry.sourceState
            sourceAfterArgs fn.returns paramStore)))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (root := prepared.rootArtifact hProgramScoped)
        contract compilation.recipe.frameWords fuelBound) :
    ∃ callerBase targetEntry targetFuel,
      ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
          callerMode sourceAfterArgs callerBase ∧
        AllocatorReady config allocatorDepth callerBase ∧
        callerBase.evm.stack = targetInitial.evm.stack ∧
        BoundedEffect config allocatorDepth (allocatorDepth + 1)
          targetInitial callerBase ∧
        BoundedEffect config allocatorDepth (allocatorDepth + 1)
          callerBase targetEntry ∧
        targetFuel =
          prepared.markerCode.length + prepared.paramCode.length +
            prepared.returnCode.length +
              (targetExtra + prepared.bodyCode.length +
                AllocationInteractionRecursive.callStride expressions *
                  (bodyFuel + 1)) ∧
        Simulation.Interaction.Rel
          (AllocationInteractionCallResultResource.OpenCallResultRel
            contract config allocatorDepth artifact.mode targetAfterArgs
            targetEntry targetInitial.evm.stack)
          (Functions.InteractionSemantics.FunDef.openRunBody
            program fn argValues (bodyFuel + 1) sourceAfterArgs)
          (Expressions.InteractionSemantics.Stmt.openRun
            expressions (targetFuel + 1) (.call name) targetAfterArgs) := by
  let targetEntry :=
    AllocationInteractionCall.CalleeEntry.structuredState targetAfterArgs
      argValues.reverse targetInitial.evm.stack fn.returns.length
  obtain ⟨hEntry, hZero, _hDefined, hEntryStackLength⟩ :=
    prepared.stack_entry_of_arguments hNeedsFrame hArgs.1 hInsert
  have hArgLength : argValues.length = fn.params.length :=
    Functions.Source.Store.insertMany_length hInsert
  have hSplit :
      Structured.StackFrame.splitArgs? artifact.lowerProc.argc
          targetAfterArgs.evm.stack =
        some (argValues.reverse, targetInitial.evm.stack) := by
    apply AllocationInteractionCall.CalleeEntry.splitArgs_of_arguments hArgs.1
    rw [prepared.procArgc, hArgLength]
    simp [hNeedsFrame]
  have hEntryReady : AllocatorReady config allocatorDepth targetEntry := by
    apply hArgs.2.ready.of_machine_eq
    simp [targetEntry,
      AllocationInteractionCall.CalleeEntry.structuredState,
      Structured.RunState.withEVM, Structured.RunState.pushReturn]
  have hEntryOwned :
      ActivationOwned config allocatorDepth 0 artifact.mode := by
    simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
      hNeedsFrame] using
        (ActivationOwned.stack (config := config)
          (allocatorDepth := allocatorDepth) (frameBase := 0))
  obtain ⟨targetFuel, _hPositive, hTargetFuel, hCall⟩ :=
    AllocationInteractionCallResultResource.SelectedCallee.complete_call
      prepared hProgramScoped hInsert hSplit
      (by simpa [targetEntry,
        AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrame] using hEntry)
      hZero hEntryStackLength hReservation hConfig hEntryReady hEntryOwned
      hBudget hFuelBudget hTargetExtra hBodyFuel hBodySuccess hRecursive
  let callerBase :=
    AllocationInteractionCall.PreparedArguments.callerState
      targetAfterArgs targetInitial
  obtain ⟨hCallerRel, hCallerReady, hCallerStack⟩ :=
    AllocationInteractionCall.PreparedArguments.caller_state_of_result hArgs
  have hAfterArgsToBase :
      BoundedEffect config allocatorDepth (allocatorDepth + 1)
        targetAfterArgs callerBase :=
    BoundedEffect.of_machine_eq hArgs.2.ready (by
      simp [callerBase,
        AllocationInteractionCall.PreparedArguments.callerState,
        Structured.RunState.withEVM])
  have hInitialToBase :
      BoundedEffect config allocatorDepth (allocatorDepth + 1)
        targetInitial callerBase :=
    (BoundedEffect.of_allocatorEffect hArgs.2).trans hAfterArgsToBase
  have hBaseToEntry :
      BoundedEffect config allocatorDepth (allocatorDepth + 1)
        callerBase targetEntry :=
    BoundedEffect.of_machine_eq hCallerReady (by
      simp [callerBase, targetEntry,
        AllocationInteractionCall.PreparedArguments.callerState,
        AllocationInteractionCall.CalleeEntry.structuredState,
        Structured.RunState.withEVM, Structured.RunState.pushReturn])
  exact
    ⟨callerBase, targetEntry, targetFuel, hCallerRel, hCallerReady,
      hCallerStack, hInitialToBase, hBaseToEntry, hTargetFuel, hCall⟩

/-- Realize one scratch-backed selected callee, including acquire, synthetic
frame argument, suspended caller, and exact recursive call. -/
theorem scratch_after_arguments
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program} {expressions : Expressions.Program}
    {compilation : AllocationInteractionCursor.Compilation
      allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared : AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth callerFrameBase bodyFuel fuelBound
      targetExtra : Nat}
    {callerPlan : Plan} {callerLive : List Locals.Name}
    {callerMode : ActivationMode}
    {sourceAfterArgs : SourceState}
    {targetInitial targetAfterAcquire targetAfterArgs : TargetState}
    {argValues : List Word} {paramStore : Locals.Source.Store}
    {reservation : MemoryContract.ScratchReservation}
    {sourceMachine : EvmYul.MachineState}
    (hNeedsFrame : artifact.needsFrame = true)
    (hAcquire :
      ScratchFrameAcquireCorrect contract config allocatorDepth sourceMachine
        targetInitial targetAfterAcquire)
    (hArgs :
      AllocationInteractionCallArgumentResources.ResultRel
        contract config (allocatorDepth + 1) callerPlan callerLive 1
        callerFrameBase argValues.length callerMode targetAfterAcquire
        (sourceAfterArgs, argValues) targetAfterArgs)
    (hInsert :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (hReservation : contract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract
          compilation.recipe.frameWords =
        some config)
    (hBudget : Budget config allocatorDepth)
    (hFuelBudget : Budget config ((allocatorDepth + 1) + bodyFuel))
    (hTargetExtra : 3 ≤ targetExtra)
    (hBodyFuel : bodyFuel < fuelBound)
    (hBodySuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn) bodyFuel fn.body
          (AllocationInteractionCall.CalleeEntry.sourceState
            sourceAfterArgs fn.returns paramStore)))
    (hRecursive :
      AllocationInteractionRecursiveResource.RecursiveOpenRuntime
        (root := prepared.rootArtifact hProgramScoped)
        contract compilation.recipe.frameWords fuelBound) :
    ∃ callerBase targetEntry targetFuel,
      ActivationStateRel contract callerPlan callerLive 0 callerFrameBase
          callerMode sourceAfterArgs callerBase ∧
        AllocatorReady config (allocatorDepth + 1) callerBase ∧
        callerBase.evm.stack = targetInitial.evm.stack ∧
        BoundedEffect config (allocatorDepth + 1) (allocatorDepth + 1)
          targetInitial callerBase ∧
        BoundedEffect config (allocatorDepth + 1) (allocatorDepth + 1)
          callerBase targetEntry ∧
        targetFuel =
          prepared.markerCode.length + prepared.paramCode.length +
            prepared.returnCode.length +
              (targetExtra + prepared.bodyCode.length +
                AllocationInteractionRecursive.callStride expressions *
                  (bodyFuel + 1)) ∧
        Simulation.Interaction.Rel
          (AllocationInteractionCallResultResource.OpenCallResultRel
            contract config (allocatorDepth + 1) artifact.mode targetAfterArgs
            targetEntry targetInitial.evm.stack)
          (Functions.InteractionSemantics.FunDef.openRunBody
            program fn argValues (bodyFuel + 1) sourceAfterArgs)
          (Expressions.InteractionSemantics.Stmt.openRun
            expressions (targetFuel + 1) (.call name) targetAfterArgs) := by
  let callVector :=
    argValues.reverse ++
      [EvmYul.UInt256.ofNat (baseAt config allocatorDepth)]
  let targetEntry :=
    AllocationInteractionCall.CalleeEntry.structuredState targetAfterArgs
      callVector targetInitial.evm.stack fn.returns.length
  obtain ⟨hEntry, hZero, _hDefined, hEntryStackLength, hEntryEffect⟩ :=
    prepared.scratch_entry_of_arguments hNeedsFrame hConfig hBudget hAcquire
      hArgs hInsert
  obtain
      ⟨_reservation, _hReservation, _hAllocator, _hFirst, _hLimit,
        hFrameWords, _hWF, _hHost, _hPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  have hArgLength : argValues.length = fn.params.length :=
    Functions.Source.Store.insertMany_length hInsert
  have hCallVectorLength : callVector.length = artifact.lowerProc.argc := by
    rw [prepared.procArgc]
    simp [callVector, hNeedsFrame, hArgLength]
  have hCallStack : targetAfterArgs.evm.stack =
      callVector ++ targetInitial.evm.stack := by
    rw [hArgs.1.stack, hAcquire.stack]
    simp [callVector, List.append_assoc]
  have hSplit :
      Structured.StackFrame.splitArgs? artifact.lowerProc.argc
          targetAfterArgs.evm.stack =
        some (callVector, targetInitial.evm.stack) := by
    rw [hCallStack, ← hCallVectorLength]
    simpa using
      Structured.StackFrame.splitArgs?_append callVector
        targetInitial.evm.stack
  have hEntryReady :
      AllocatorReady config (allocatorDepth + 1) targetEntry := by
    simpa [targetEntry, callVector] using hEntryEffect.ready
  have hEntryOwned :
      ActivationOwned config (allocatorDepth + 1) (baseAt config allocatorDepth)
        artifact.mode := by
    simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
      hNeedsFrame, hFrameWords] using
        (ActivationOwned.scratch (config := config)
          (previousDepth := allocatorDepth)
          (frameBase := baseAt config allocatorDepth)
          (frameDepth := 0) (frameWords := config.frameWords) rfl rfl)
  have hCalleeBudget : Budget config (allocatorDepth + 1) :=
    Budget.mono (by omega) hFuelBudget
  obtain ⟨targetFuel, _hPositive, hTargetFuel, hCall⟩ :=
    AllocationInteractionCallResultResource.SelectedCallee.complete_call
      prepared hProgramScoped hInsert hSplit
      (by simpa [targetEntry, callVector,
        AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrame, hFrameWords] using hEntry)
      hZero hEntryStackLength hReservation hConfig hEntryReady hEntryOwned
      hCalleeBudget hFuelBudget hTargetExtra hBodyFuel hBodySuccess hRecursive
  let callerBase :=
    AllocationInteractionCall.PreparedArguments.callerState
      targetAfterArgs targetInitial
  obtain ⟨hCallerRel, hCallerReady, hCallerStack, hInitialToBase⟩ :=
    AllocationInteractionCall.PreparedArguments.caller_state_of_scratch_result
      hAcquire hArgs
  have hBaseToEntry :
      BoundedEffect config (allocatorDepth + 1) (allocatorDepth + 1)
        callerBase targetEntry :=
    BoundedEffect.of_machine_eq hCallerReady (by
      simp [callerBase, targetEntry, callVector,
        AllocationInteractionCall.PreparedArguments.callerState,
        AllocationInteractionCall.CalleeEntry.structuredState,
        Structured.RunState.withEVM, Structured.RunState.pushReturn])
  exact
    ⟨callerBase, targetEntry, targetFuel, hCallerRel, hCallerReady,
      hCallerStack, hInitialToBase, hBaseToEntry, hTargetFuel, hCall⟩

end SelectedCallee

end AllocationInteractionCallStatementResource
end Functions
end EvmCompiler
