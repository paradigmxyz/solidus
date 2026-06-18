import EvmCompiler.Functions.AllocationInteractionCallArguments

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall
namespace PreparedArguments

open AllocationInteractionRelation

/-- Suspended caller state after argument effects, with only the temporary
argument stack prefix removed. -/
def callerState (targetAfterArgs targetInitial : TargetState) : TargetState :=
  targetAfterArgs.withEVM
    { targetAfterArgs.evm with stack := targetInitial.evm.stack }

/-- Canonical arguments leave a related suspended caller once their temporary
target stack prefix is removed. -/
theorem caller_state_of_semantic_result
    {contract : MemoryContract.Contract}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {sourceAfterArgs : SourceState}
    {targetInitial targetAfterArgs : TargetState}
    {args : List Word}
    (hArgs :
      ActivationExprResultRel contract plan live 0 frameBase args.length
        mode sourceAfterArgs targetInitial targetAfterArgs args) :
    ActivationStateRel contract plan live 0 frameBase mode sourceAfterArgs
        (callerState targetAfterArgs targetInitial) ∧
      (callerState targetAfterArgs targetInitial).evm.stack =
        targetInitial.evm.stack := by
  have hState :
      ActivationStateRel contract plan live
        (0 + args.reverse.length) frameBase mode sourceAfterArgs
        targetAfterArgs := by
    simpa [hArgs.valuesLength] using hArgs.state
  have hRebased :=
    hState.rebase_prefix
      (sourceFinal := sourceAfterArgs)
      (targetFinal := callerState targetAfterArgs targetInitial)
      (oldPrefix := args.reverse) (newPrefix := [])
      (baseStack := targetInitial.evm.stack)
      (by
        simpa [callerState, Structured.RunState.withEVM] using hState.shared)
      hArgs.stack
      (by simp [callerState, Structured.RunState.withEVM])
      (by
        intro name slot hLive hLocation
        rfl)
      rfl
      (by simp [callerState, Structured.RunState.withEVM])
      (by simp [callerState, Structured.RunState.withEVM])
      (by
        simpa [callerState, Structured.RunState.withEVM] using
          hState.activeNoWrap)
  exact ⟨by simpa using hRebased, rfl⟩

/-- Reconstruct an all-stack caller after a callee returns values above the
exact suspended caller stack. -/
theorem resume_after_stack_call
    {contract : MemoryContract.Contract}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {sourceBefore sourceAfter : SourceState}
    {targetBefore targetAfter : TargetState}
    {returned : List Word}
    (hRel :
      ActivationStateRel contract plan live 0 frameBase .stack
        sourceBefore targetBefore)
    (hVars : sourceAfter.vars = sourceBefore.vars)
    (hShared :
      SharedRel contract sourceAfter.shared targetAfter.evm.toSharedState)
    (hStack :
      targetAfter.evm.stack = returned ++ targetBefore.evm.stack)
    (hActiveNoWrap :
      targetAfter.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size) :
    ActivationStateRel contract plan live returned.length frameBase .stack
      sourceAfter targetAfter := by
  cases hRel with
  | stack hOnly _hBeforeNoWrap hState =>
      refine .stack hOnly hActiveNoWrap ?_
      refine
        { machine := hShared.machine
          world := hShared.world
          store := ?_ }
      intro name location hLive hLocation
      have hOld := hState.store name location hLive hLocation
      cases location with
      | stack planDepth =>
          rcases hOld with ⟨depth, hDepth, hValue⟩
          refine ⟨depth, hDepth, ?_⟩
          rw [hStack]
          rw [List.getElem?_append_right
            (Nat.le_add_right returned.length depth)]
          simpa [hVars] using hValue
      | scratch slot =>
          exact False.elim (hOnly name slot hLive hLocation)

end PreparedArguments
end AllocationInteractionCall
end Functions
end EvmCompiler
