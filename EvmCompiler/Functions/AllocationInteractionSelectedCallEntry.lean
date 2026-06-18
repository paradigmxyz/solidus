import EvmCompiler.Functions.AllocationInteractionScratchCallEntry
import EvmCompiler.Functions.AllocationInteractionCallArgumentResources

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall

open AllocationInteractionRelation
open AllocationInteractionCursor
open AllocationInteractionFrame
open AllocationInteractionFrameExecution
open AllocationInteractionFramePreservation

namespace SelectedCallee

/-- Compiler-selected all-stack entry from canonical source arguments. -/
theorem Prepared.stack_entry_of_arguments
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {callerPlan : Plan} {callerLive : List Locals.Name}
    {callerFrameBase : Nat} {callerMode : ActivationMode}
    {sourceAfterArgs : SourceState}
    {targetInitial targetAfterArgs : TargetState}
    {args : List Word} {paramStore : Locals.Source.Store}
    (hNeedsFrame : artifact.needsFrame = false)
    (hArgs :
      ActivationExprResultRel contract callerPlan callerLive 0
        callerFrameBase args.length callerMode sourceAfterArgs targetInitial
        targetAfterArgs args)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore) :
    let sourceEntry :=
      CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore
    let targetEntry :=
      CalleeEntry.structuredState targetAfterArgs args.reverse
        targetInitial.evm.stack fn.returns.length
    ActivationCalleeEntryRel contract prepared.plan [] artifact.slots.params
        0 .stack sourceEntry targetEntry ∧
      (∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
          sourceEntry.vars localName = some AllocationSupport.zeroWord) ∧
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceEntry ∧
      targetEntry.evm.stack.length = artifact.entryCtx.layout.length := by
  dsimp only
  have hSignature : (fn.returns ++ fn.params).Nodup := by
    simpa [List.map_append, artifact.slotsMatch.2.1,
      artifact.slotsMatch.2.2] using prepared.signatureNodup
  have hFacts :=
    CalleeEntry.initialized_source_facts
      (source := CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore)
      hSignature hInsert (by
        rfl)
  have hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst)
          (CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore).vars =
        some args := by
    simpa [artifact.slotsMatch.2.1] using hFacts.1
  have hEntry :=
    CalleeEntry.stack_of_arguments
      (calleePlan := prepared.plan) (calleeFrameBase := 0)
      (pending := artifact.slots.params)
      (initialStore :=
        Functions.Source.Store.initReturns fn.returns paramStore)
      (callerStack := targetInitial.evm.stack)
      (retc := fn.returns.length) hArgs hParamLookup
  have hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
          (CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore).vars
              localName =
            some AllocationSupport.zeroWord := by
    intro localName hLocal
    exact hFacts.2.1 localName (by
      simpa [artifact.slotsMatch.2.2] using hLocal)
  have hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        (CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore) := by
    simpa [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2] using hFacts.2.2
  have hArgsLength : args.length = fn.params.length :=
    Functions.Source.Store.insertMany_length hInsert
  refine ⟨?_, hZero, hDefined, ?_⟩
  · simpa [CalleeEntry.sourceState] using hEntry
  · simp [CalleeEntry.structuredState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn, Artifact.entryCtx,
      Artifact.entryLayout, hNeedsFrame, hArgsLength,
      Locals.Ctx.procEntryWithLayoutAndRetc,
      Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
      Locals.Ctx.initial]

/-- Compiler-selected scratch-backed entry after acquire and arguments. -/
theorem Prepared.scratch_entry_of_arguments
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {globalFrameWords depth : Nat} {config : Config}
    {callerPlan : Plan} {callerLive : List Locals.Name}
    {callerFrameBase : Nat} {callerMode : ActivationMode}
    {sourceAfterArgs : SourceState}
    {targetInitial targetAfterAcquire targetAfterArgs : TargetState}
    {args : List Word} {paramStore : Locals.Source.Store}
    {acquireSourceMachine : EvmYul.MachineState}
    (hNeedsFrame : artifact.needsFrame = true)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hBudget : Budget config depth)
    (hAcquire :
      ScratchFrameAcquireCorrect contract config depth acquireSourceMachine
        targetInitial targetAfterAcquire)
    (hArgs :
      AllocationInteractionCallArgumentResources.ResultRel
        contract config (depth + 1) callerPlan callerLive 1
        callerFrameBase args.length callerMode targetAfterAcquire
        (sourceAfterArgs, args) targetAfterArgs)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty =
        some paramStore) :
    let sourceEntry :=
      CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore
    let targetEntry :=
      CalleeEntry.structuredState targetAfterArgs
        (args.reverse ++ [EvmYul.UInt256.ofNat (baseAt config depth)])
        targetInitial.evm.stack fn.returns.length
    ActivationCalleeEntryRel contract prepared.plan [] artifact.slots.params
        (baseAt config depth) (.scratch 0 config.frameWords)
        sourceEntry targetEntry ∧
      (∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
          sourceEntry.vars localName = some AllocationSupport.zeroWord) ∧
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceEntry ∧
      targetEntry.evm.stack.length = artifact.entryCtx.layout.length ∧
      BoundedEffect config (depth + 1) (depth + 1)
        targetInitial targetEntry := by
  dsimp only
  rcases hArgs with ⟨hArgs, hArgsEffect⟩
  have hSignature : (fn.returns ++ fn.params).Nodup := by
    simpa [List.map_append, artifact.slotsMatch.2.1,
      artifact.slotsMatch.2.2] using prepared.signatureNodup
  have hFacts :=
    CalleeEntry.initialized_source_facts
      (source := CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore)
      hSignature hInsert (by rfl)
  have hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst)
          (CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore).vars =
        some args := by
    simpa [artifact.slotsMatch.2.1] using hFacts.1
  have hEntry :=
    CalleeEntry.scratch_of_arguments
      (calleePlan := prepared.plan)
      (pending := artifact.slots.params)
      (initialStore := Functions.Source.Store.initReturns fn.returns paramStore)
      (callerStack := targetInitial.evm.stack)
      (retc := fn.returns.length)
      hConfig hBudget hArgs hAcquire.stack hAcquire.frameActive
      hAcquire.frameAllocated hArgsEffect.growth hParamLookup
  have hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
          (CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore).vars
              localName =
            some AllocationSupport.zeroWord := by
    intro localName hLocal
    exact hFacts.2.1 localName (by
      simpa [artifact.slotsMatch.2.2] using hLocal)
  have hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        (CalleeEntry.sourceState sourceAfterArgs fn.returns paramStore) := by
    simpa [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2] using hFacts.2.2
  have hArgsLength : args.length = fn.params.length :=
    Functions.Source.Store.insertMany_length hInsert
  have hEffect :
      BoundedEffect config (depth + 1) (depth + 1) targetInitial
        (CalleeEntry.structuredState targetAfterArgs
          (args.reverse ++ [EvmYul.UInt256.ofNat (baseAt config depth)])
          targetInitial.evm.stack fn.returns.length) := by
    have hArgsBounded :
        BoundedEffect config (depth + 1) (depth + 1)
          targetAfterAcquire targetAfterArgs :=
      BoundedEffect.weaken (by omega)
        (BoundedEffect.of_allocatorEffect hArgsEffect)
    have hBaseEffect := hAcquire.effect.trans hArgsBounded
    refine
      { ready := ?_
        growth := ?_
        prefixStable := ?_ }
    · refine
        { allocatorAt := ?_
          cellActive := ?_
          cellAllocated := ?_
          activeNoWrap := ?_ }
      · simpa [AllocatorAt, CalleeEntry.structuredState,
          Structured.RunState.withEVM, Structured.RunState.pushReturn] using
          hBaseEffect.ready.allocatorAt
      · simpa [CalleeEntry.structuredState, Structured.RunState.withEVM,
          Structured.RunState.pushReturn] using hBaseEffect.ready.cellActive
      · simpa [CalleeEntry.structuredState, Structured.RunState.withEVM,
          Structured.RunState.pushReturn] using
          hBaseEffect.ready.cellAllocated
      · simpa [CalleeEntry.structuredState, Structured.RunState.withEVM,
          Structured.RunState.pushReturn] using
          hBaseEffect.ready.activeNoWrap
    · exact
        { active := by
            simpa [CalleeEntry.structuredState,
              Structured.RunState.withEVM,
              Structured.RunState.pushReturn] using hBaseEffect.growth.active
          memory := by
            simpa [CalleeEntry.structuredState,
              Structured.RunState.withEVM,
              Structured.RunState.pushReturn] using hBaseEffect.growth.memory }
    · intro protectedDepth hProtected hProtectedBudget
      have hPrefix :=
        hBaseEffect.prefixStable hProtected hProtectedBudget
      refine
        { growth :=
            { active := by
                simpa [CalleeEntry.structuredState,
                  Structured.RunState.withEVM,
                  Structured.RunState.pushReturn] using hPrefix.growth.active
              memory := by
                simpa [CalleeEntry.structuredState,
                  Structured.RunState.withEVM,
                  Structured.RunState.pushReturn] using hPrefix.growth.memory }
          lookup := ?_ }
      intro address hStart hEnd hReadMemory hReadActive
      simpa [CalleeEntry.structuredState, Structured.RunState.withEVM,
        Structured.RunState.pushReturn] using
        hPrefix.lookup hStart hEnd hReadMemory hReadActive
  refine ⟨?_, hZero, hDefined, ?_, hEffect⟩
  · simpa [CalleeEntry.sourceState] using hEntry
  · simp [CalleeEntry.structuredState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn, Artifact.entryCtx,
      Artifact.entryLayout, hNeedsFrame, hArgsLength,
      Locals.Ctx.procEntryWithLayoutAndRetc,
      Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
      Locals.Ctx.initial]

end SelectedCallee

end AllocationInteractionCall
end Functions
end EvmCompiler
