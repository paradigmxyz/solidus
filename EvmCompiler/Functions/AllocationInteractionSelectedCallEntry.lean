import EvmCompiler.Functions.AllocationInteractionCall

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall

open AllocationInteractionRelation
open AllocationInteractionCursor

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

end SelectedCallee

end AllocationInteractionCall
end Functions
end EvmCompiler
