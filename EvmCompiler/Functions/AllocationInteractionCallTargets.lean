import EvmCompiler.Functions.AllocationContext
import EvmCompiler.Functions.AllocationInteractionFrame
import EvmCompiler.Functions.AllocationInteractionScratchStore
import EvmCompiler.Functions.AllocationLowering

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall
namespace CallTargets

open AllocationInteractionRelation
open AllocationInteractionFrame

/-- Prefix depth protected while writing returned values into one caller. -/
def protectedBound (callerDepth : Nat) (mode : ActivationMode) : Nat :=
  match mode with
  | .stack => callerDepth + 1
  | .scratch _ _ => callerDepth

private def PreservesBoundedEffect
    (contract : MemoryContract.Contract)
    (frameBase : Nat) (mode : ActivationMode)
    (before after : TargetState) : Prop :=
  ∀ {globalFrameWords : Nat} {config : Config}
    {callerDepth readyDepth : Nat},
    AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config →
    ActivationOwned config callerDepth frameBase mode →
    callerDepth ≤ readyDepth →
    AllocatorReady config readyDepth before →
    BoundedEffect config readyDepth (protectedBound callerDepth mode)
      before after

private theorem PreservesBoundedEffect.refl
    {contract : MemoryContract.Contract} {frameBase : Nat}
    {mode : ActivationMode} {target : TargetState} :
    PreservesBoundedEffect contract frameBase mode target target := by
  intro _ _ _ _ _ _ _ hReady
  exact BoundedEffect.refl hReady

private theorem PreservesBoundedEffect.trans
    {contract : MemoryContract.Contract} {frameBase : Nat}
    {mode : ActivationMode} {before middle after : TargetState}
    (hFirst : PreservesBoundedEffect contract frameBase mode before middle)
    (hSecond : PreservesBoundedEffect contract frameBase mode middle after) :
    PreservesBoundedEffect contract frameBase mode before after := by
  intro globalFrameWords config callerDepth readyDepth
    hConfig hOwned hDepth hReady
  have hFirstEffect := hFirst hConfig hOwned hDepth hReady
  exact hFirstEffect.trans
    (hSecond hConfig hOwned hDepth hFirstEffect.ready)

private theorem PreservesBoundedEffect.of_machine_eq
    {contract : MemoryContract.Contract} {frameBase : Nat}
    {mode : ActivationMode} {before after : TargetState}
    (hMachine :
      after.evm.toMachineState = before.evm.toMachineState) :
    PreservesBoundedEffect contract frameBase mode before after := by
  intro _ _ _ _ _ _ _ hReady
  exact BoundedEffect.of_machine_eq hReady hMachine

private theorem PreservesBoundedEffect.of_scratch_store
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name}
    {stackOffset frameBase frameDepth frameWords slot : Nat}
    {source : SourceState} {before after : TargetState}
    {name : Locals.Name} {value : Word}
    (hRel :
      ScratchStateRel contract plan live stackOffset frameBase
        frameDepth frameWords source before)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hMachine :
      after.evm.toMachineState =
        before.evm.toMachineState.mstore
          (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) value) :
    PreservesBoundedEffect contract frameBase
      (.scratch frameDepth frameWords) before after := by
  intro globalFrameWords config callerDepth readyDepth
    hConfig hOwned _hDepth hReady
  exact hOwned.boundedEffect_of_scratchStore hConfig hRel hLive hLocation
    hReady hMachine

private theorem set_append_offset
    {α : Type} (above suffix : List α) (depth : Nat) (value : α) :
    (above ++ suffix).set (above.length + depth) value =
      above ++ suffix.set depth value := by
  induction above with
  | nil => simp
  | cons head tail ih => simp [Nat.succ_add, ih]

private theorem lookupDepth?_none_of_not_mem
    {name : Locals.Name} {layout : Locals.Layout}
    (hNotMem : name ∉ layout) :
    Locals.Layout.lookupDepth? name layout = none := by
  cases hLookup : Locals.Layout.lookupDepth? name layout with
  | none => rfl
  | some depth =>
      exact False.elim
        (hNotMem (Locals.Layout.mem_of_lookupDepth?_eq_some hLookup))

private theorem stack_step
    {contract : MemoryContract.Contract}
    {plan : Plan} {live : List Locals.Name}
    {frameBase planDepth depth : Nat} {mode : ActivationMode}
    {layout : Locals.Layout} {name : Locals.Name} {value old : Word}
    {remaining rest : List Word} {source : SourceState}
    {target : TargetState} {code : Structured.Code}
    (hCode :
      AllocationLowering.stackAssignTopCode?
          layout remaining.length name = some code)
    (hRel :
      ActivationStateRel contract plan live (remaining.length + 1)
        frameBase mode source target)
    (hStack : target.evm.stack = value :: (remaining ++ rest))
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
        some (depth + 1))
    (hCompileDepth :
      Locals.Layout.lookupDepth? name layout = some (depth + 1))
    (hDepthValid : mode.StackDepthValid depth)
    (hOld : source.vars name = some old) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok targetFinal) ∧
        ActivationStateRel contract plan live remaining.length frameBase mode
          (source.insert name value) targetFinal ∧
        targetFinal.evm.stack = remaining ++ rest.set depth value ∧
        targetFinal.evm.toMachineState = target.evm.toMachineState := by
  cases hSwap : Locals.StackOp.swap? (remaining.length + (depth + 1)) with
  | none =>
      simp [AllocationLowering.stackAssignTopCode?, hCompileDepth, hSwap]
        at hCode
  | some op =>
      simp [AllocationLowering.stackAssignTopCode?, hCompileDepth, hSwap]
        at hCode
      subst code
      have hStored := hRel.state.store name (.stack planDepth) hLive hLocation
      rcases hStored with ⟨actualDepth, hActualDepth, hStored⟩
      have hActualDepthEq : actualDepth = depth := by
        exact Nat.succ.inj
          (Option.some.inj (hActualDepth.symm.trans hDepth))
      subst actualDepth
      rw [hStack, hOld] at hStored
      have hRestGet :
          (remaining ++ rest)[remaining.length + depth]? = some old := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hStored
      obtain ⟨targetFinal, hRun, hFinalStack, hShared, _hReturns⟩ :=
        Locals.InteractionPreservation.Code.openRun_swap_pop
          (by simpa [Nat.add_assoc] using hSwap) hRestGet hStack
      have hFinalRel :=
        hRel.assign_stack_live_at hStack hFinalStack hShared hLive
          hLocation hDepth hDepthValid hOld
      refine ⟨targetFinal, hRun, hFinalRel, ?_, ?_⟩
      · rw [hFinalStack, set_append_offset]
      · exact congrArg EvmYul.SharedState.toMachineState hShared

private theorem scratch_step
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {plan : Plan} {live : List Locals.Name}
    {frameBase frameDepth frameWords slot : Nat}
    {name : Locals.Name} {value : Word}
    {remaining rest : List Word} {source : SourceState}
    {target : TargetState} {code : Structured.Code}
    (hCode :
      AllocationLowering.scratchAssignTopCode?
          lowerCtx lowerState remaining.length slot = some code)
    (hRel :
      ScratchStateRel contract plan live (remaining.length + 1) frameBase
        frameDepth frameWords source target)
    (hStack : target.evm.stack = value :: (remaining ++ rest))
    (hWF : plan.WellFormed)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hFrameDepth :
      Locals.Layout.lookupDepth? lowerCtx.frameName lowerState.layout =
        some (frameDepth + 1)) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok targetFinal) ∧
        ActivationStateRel contract plan live remaining.length frameBase
          (.scratch frameDepth frameWords) (source.insert name value)
          targetFinal ∧
        targetFinal.evm.stack = remaining ++ rest ∧
        targetFinal.evm.toMachineState =
          target.evm.toMachineState.mstore
            (EvmYul.UInt256.ofNat (scratchAddress frameBase slot)) value := by
  have hStoreCode :
      AllocationSupport.storeTopSlotCode?
          (remaining.length + frameDepth + 1) slot = some code := by
    simpa [AllocationLowering.scratchAssignTopCode?,
      AllocationLowering.frameDepth?, hFrameDepth, Nat.add_assoc] using hCode
  cases hDup :
      Locals.StackOp.dup? (remaining.length + frameDepth + 2) with
  | none =>
      have hDup' :
          Locals.StackOp.dup? (remaining.length + (frameDepth + 2)) = none := by
        simpa [Nat.add_assoc] using hDup
      simp [AllocationSupport.storeTopSlotCode?,
        AllocationSupport.slotAddressCode?, AllocationSupport.dupCode?,
        hDup', Nat.add_assoc] at hStoreCode
  | some op =>
      have hDup' :
          Locals.StackOp.dup? (remaining.length + (frameDepth + 2)) =
            some op := by
        simpa [Nat.add_assoc] using hDup
      have hCodeEq :
          code =
            [.op op, .push (AllocationSupport.slotOffset slot),
              .op .add, .op .mstore] := by
        apply Option.some.inj
        calc
          some code =
              AllocationSupport.storeTopSlotCode?
                (remaining.length + frameDepth + 1) slot := hStoreCode.symm
          _ = some
              [.op op, .push (AllocationSupport.slotOffset slot),
                .op .add, .op .mstore] := by
            simp [AllocationSupport.storeTopSlotCode?,
              AllocationSupport.slotAddressCode?, AllocationSupport.dupCode?,
              hDup', Nat.add_assoc]
      subst code
      have hSlotBound := hRel.scratchBound name slot hLive hLocation
      obtain ⟨reservation, hReservation, _hFrameRegion⟩ := hRel.frameReserved
      have hRegion :=
        hRel.scratchAddress_reserved_of_bound hSlotBound hReservation
      obtain ⟨targetFinal, hRun, hFinalRel, hFinalStack, hFinalMachine⟩ :=
        AllocationInteractionScratchStore.assignTop hRel hStack hWF
          (fun other hOther => Or.inr hOther) rfl hLocation hSlotBound
          hReservation hRegion (by simpa [Nat.add_assoc] using hDup)
      exact
        ⟨targetFinal, hRun, .scratch hFinalRel, hFinalStack, hFinalMachine⟩

private theorem forward_core
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name} {frameBase : Nat}
    {mode : ActivationMode} {names : List Locals.Name} {values : List Word}
    {finalStore : Locals.Source.Store} {code : Structured.Code}
    {source : SourceState} {target : TargetState} {rest : List Word}
    (hContext :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hLive : ∀ name, name ∈ names → name ∈ live)
    (hAssign :
      Functions.Source.Store.assignMany names values source.vars =
        some finalStore)
    (hCode :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState names values.length = some code)
    (hRel :
      ActivationStateRel contract plan live values.length frameBase mode
        source target)
    (hStack : target.evm.stack = values ++ rest) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok targetFinal) ∧
        ActivationStateRel contract plan live 0 frameBase mode
          (source.withVars finalStore) targetFinal ∧
        targetFinal.evm.stack.length = rest.length ∧
        PreservesBoundedEffect contract frameBase mode target targetFinal := by
  induction names generalizing values code source target rest with
  | nil =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
          subst finalStore
          have hCode' : code = [] := by
            simpa [AllocationLowering.lowerCallTargetsCode?] using hCode.symm
          subst code
          exact
            ⟨target, rfl,
              by simpa [Locals.Source.State.withVars] using hRel,
              by simpa using congrArg List.length hStack,
              PreservesBoundedEffect.refl⟩
      | cons value values =>
          simp [Functions.Source.Store.assignMany] at hAssign
  | cons name names ih =>
      cases values with
      | nil => simp [Functions.Source.Store.assignMany] at hAssign
      | cons value values =>
          have hNameLive : name ∈ live := hLive name (by simp)
          have hTailLive : ∀ other, other ∈ names → other ∈ live := by
            intro other hOther
            exact hLive other (by simp [hOther])
          change
            (if source.vars.contains name then
                Functions.Source.Store.assignMany names values
                  (Locals.Source.Store.insert source.vars name value)
              else none) = some finalStore at hAssign
          by_cases hContains : source.vars.contains name = true
          · simp [hContains] at hAssign
            cases hOld : source.vars name with
            | none => simp [Locals.Source.Store.contains, hOld] at hContains
            | some old =>
                let sourceNext := source.insert name value
                have hTailAssign :
                    Functions.Source.Store.assignMany names values
                        sourceNext.vars = some finalStore := by
                  simpa [sourceNext, Locals.Source.State.insert] using hAssign
                have hHeadStack :
                    target.evm.stack = value :: (values ++ rest) := by
                  simpa using hStack
                have hHeadRel :
                    ActivationStateRel contract plan live
                      (values.length + 1) frameBase mode source target := by
                  simpa using hRel
                obtain ⟨slot, hSlot⟩ :=
                  match hContext with
                  | .stack ctx => ctx.slot name hNameLive
                  | .scratch ctx => ctx.slot name hNameLive
                by_cases hStackSlot :
                    AllocationLowering.isStackSlot lowerCtx slot = true
                · cases hHeadCode :
                    AllocationLowering.stackAssignTopCode?
                      lowerState.layout values.length name with
                  | none =>
                      simp [AllocationLowering.lowerCallTargetsCode?,
                        hSlot, hStackSlot, hHeadCode] at hCode
                  | some headCode =>
                      cases hTailCode :
                          AllocationLowering.lowerCallTargetsCode?
                            lowerCtx lowerState names values.length with
                      | none =>
                          simp [AllocationLowering.lowerCallTargetsCode?,
                            hSlot, hStackSlot, hHeadCode, hTailCode] at hCode
                      | some tailCode =>
                          have hWholeCode : code = headCode ++ tailCode := by
                            apply Option.some.inj
                            calc
                              some code =
                                  AllocationLowering.lowerCallTargetsCode?
                                    lowerCtx lowerState (name :: names)
                                      (values.length + 1) := hCode.symm
                              _ = some (headCode ++ tailCode) := by
                                simp [AllocationLowering.lowerCallTargetsCode?,
                                  hSlot, hStackSlot, hHeadCode, hTailCode]
                          subst code
                          cases hContext with
                          | stack stackContext =>
                              obtain ⟨planDepth, depth, hLocation,
                                  hCurrentDepth, hLowerDepth⟩ :=
                                stackContext.stack name slot hNameLive hSlot
                                  hStackSlot
                              obtain ⟨targetHead, hHeadRun, hHeadFinalRel,
                                  hHeadFinalStack, hHeadMachine⟩ :=
                                stack_step hHeadCode hHeadRel hHeadStack
                                  hNameLive hLocation hCurrentDepth hLowerDepth
                                  trivial hOld
                              obtain ⟨targetFinal, hTailRun, hFinalRel,
                                  hFinalStack, hTailEffect⟩ :=
                                ih hTailLive hTailAssign hTailCode
                                  hHeadFinalRel hHeadFinalStack
                              refine ⟨targetFinal, ?_, ?_, ?_, ?_⟩
                              · rw [Structured.InteractionSemantics.Code.openRun_append,
                                  hHeadRun]
                                exact hTailRun
                              · simpa [sourceNext,
                                  Locals.Source.State.withVars] using hFinalRel
                              · simpa [List.length_set] using hFinalStack
                              · exact
                                  PreservesBoundedEffect.trans
                                    (PreservesBoundedEffect.of_machine_eq
                                      hHeadMachine)
                                    hTailEffect
                          | @scratch frameDepth frameWords scratchContext =>
                              obtain ⟨planDepth, depth, hLocation,
                                  hCurrentDepth, hLowerDepth⟩ :=
                                scratchContext.stack name slot hNameLive hSlot
                                  hStackSlot
                              have hDepthValid :
                                  ActivationMode.StackDepthValid
                                    (.scratch frameDepth frameWords) depth :=
                                scratchContext.stack_depth_lt_frame hCurrentDepth
                              obtain ⟨targetHead, hHeadRun, hHeadFinalRel,
                                  hHeadFinalStack, hHeadMachine⟩ :=
                                stack_step hHeadCode hHeadRel hHeadStack
                                  hNameLive hLocation hCurrentDepth hLowerDepth
                                  hDepthValid hOld
                              obtain ⟨targetFinal, hTailRun, hFinalRel,
                                  hFinalStack, hTailEffect⟩ :=
                                ih hTailLive hTailAssign hTailCode
                                  hHeadFinalRel hHeadFinalStack
                              refine ⟨targetFinal, ?_, ?_, ?_, ?_⟩
                              · rw [Structured.InteractionSemantics.Code.openRun_append,
                                  hHeadRun]
                                exact hTailRun
                              · simpa [sourceNext,
                                  Locals.Source.State.withVars] using hFinalRel
                              · simpa [List.length_set] using hFinalStack
                              · exact
                                  PreservesBoundedEffect.trans
                                    (PreservesBoundedEffect.of_machine_eq
                                      hHeadMachine)
                                    hTailEffect
                · have hScratchSlot :
                    AllocationLowering.isStackSlot lowerCtx slot = false :=
                    Bool.eq_false_of_not_eq_true hStackSlot
                  cases hContext with
                  | stack stackContext =>
                      have hFrameNone :
                          Locals.Layout.lookupDepth?
                              lowerCtx.frameName lowerState.layout = none :=
                        lookupDepth?_none_of_not_mem stackContext.frameAbsent
                      simp [AllocationLowering.lowerCallTargetsCode?, hSlot,
                        hScratchSlot, AllocationLowering.scratchAssignTopCode?,
                        AllocationLowering.frameDepth?, hFrameNone] at hCode
                  | @scratch frameDepth frameWords scratchContext =>
                      cases hRel with
                      | scratch scratchRel =>
                          obtain ⟨hLocation, hFrameDepth⟩ :=
                            scratchContext.scratch name slot hNameLive hSlot
                              hScratchSlot
                          cases hHeadCode :
                              AllocationLowering.scratchAssignTopCode?
                                lowerCtx lowerState values.length slot with
                          | none =>
                              simp [AllocationLowering.lowerCallTargetsCode?,
                                hSlot, hScratchSlot, hHeadCode] at hCode
                          | some headCode =>
                              cases hTailCode :
                                  AllocationLowering.lowerCallTargetsCode?
                                    lowerCtx lowerState names values.length with
                              | none =>
                                  simp [AllocationLowering.lowerCallTargetsCode?,
                                    hSlot, hScratchSlot, hHeadCode, hTailCode]
                                    at hCode
                              | some tailCode =>
                                  have hWholeCode :
                                      code = headCode ++ tailCode := by
                                    apply Option.some.inj
                                    calc
                                      some code =
                                          AllocationLowering.lowerCallTargetsCode?
                                            lowerCtx lowerState (name :: names)
                                              (values.length + 1) := hCode.symm
                                      _ = some (headCode ++ tailCode) := by
                                        simp [
                                          AllocationLowering.lowerCallTargetsCode?,
                                          hSlot, hScratchSlot, hHeadCode,
                                          hTailCode]
                                  subst code
                                  obtain ⟨targetHead, hHeadRun,
                                      hHeadFinalRel, hHeadFinalStack,
                                      hHeadMachine⟩ :=
                                    scratch_step hHeadCode scratchRel hHeadStack
                                      hWF hNameLive hLocation hFrameDepth
                                  obtain ⟨targetFinal, hTailRun, hFinalRel,
                                      hFinalStack, hTailEffect⟩ :=
                                    ih hTailLive hTailAssign hTailCode
                                      hHeadFinalRel hHeadFinalStack
                                  refine ⟨targetFinal, ?_, ?_, hFinalStack, ?_⟩
                                  · rw [
                                      Structured.InteractionSemantics.Code.openRun_append,
                                      hHeadRun]
                                    exact hTailRun
                                  · simpa [sourceNext,
                                      Locals.Source.State.withVars] using hFinalRel
                                  · exact
                                      PreservesBoundedEffect.trans
                                        (PreservesBoundedEffect.of_scratch_store
                                          scratchRel hNameLive hLocation
                                          hHeadMachine)
                                        hTailEffect
          · simp [hContains] at hAssign

/-- Execute the ordinary compiler's returned-value assignment code. -/
theorem forward
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name} {frameBase : Nat}
    {mode : ActivationMode} {names : List Locals.Name} {values : List Word}
    {finalStore : Locals.Source.Store} {code : Structured.Code}
    {source : SourceState} {target : TargetState} {rest : List Word}
    (hContext :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hLive : ∀ name, name ∈ names → name ∈ live)
    (hAssign :
      Functions.Source.Store.assignMany names values source.vars =
        some finalStore)
    (hCode :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState names values.length = some code)
    (hRel :
      ActivationStateRel contract plan live values.length frameBase mode
        source target)
    (hStack : target.evm.stack = values ++ rest) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok targetFinal) ∧
        ActivationStateRel contract plan live 0 frameBase mode
          (source.withVars finalStore) targetFinal ∧
        targetFinal.evm.stack.length = rest.length := by
  obtain ⟨targetFinal, hRun, hFinalRel, hFinalStack, _hEffect⟩ :=
    forward_core hContext hWF hLive hAssign hCode hRel hStack
  exact ⟨targetFinal, hRun, hFinalRel, hFinalStack⟩

/--
Returned-value assignment while the allocator may still be ready at a deeper
callee depth. The caller prefix protected by its representation is explicit.
-/
theorem forward_bounded
    {contract : MemoryContract.Contract} {globalFrameWords : Nat}
    {config : Config} {callerDepth readyDepth : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State} {localsCtx : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name} {frameBase : Nat}
    {mode : ActivationMode} {names : List Locals.Name} {values : List Word}
    {finalStore : Locals.Source.Store} {code : Structured.Code}
    {source : SourceState} {target : TargetState} {rest : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hContext :
      AllocationContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hLive : ∀ name, name ∈ names → name ∈ live)
    (hAssign :
      Functions.Source.Store.assignMany names values source.vars =
        some finalStore)
    (hCode :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState names values.length = some code)
    (hRel :
      ActivationStateRel contract plan live values.length frameBase mode
        source target)
    (hStack : target.evm.stack = values ++ rest)
    (hOwned : ActivationOwned config callerDepth frameBase mode)
    (hDepth : callerDepth ≤ readyDepth)
    (hReady : AllocatorReady config readyDepth target) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun code target =
          .done (.ok targetFinal) ∧
        ActivationStateRel contract plan live 0 frameBase mode
          (source.withVars finalStore) targetFinal ∧
        targetFinal.evm.stack.length = rest.length ∧
        BoundedEffect config readyDepth (protectedBound callerDepth mode)
          target targetFinal := by
  obtain ⟨targetFinal, hRun, hFinalRel, hFinalStack, hEffect⟩ :=
    forward_core hContext hWF hLive hAssign hCode hRel hStack
  exact
    ⟨targetFinal, hRun, hFinalRel, hFinalStack,
      hEffect hConfig hOwned hDepth hReady⟩

end CallTargets
end AllocationInteractionCall
end Functions
end EvmCompiler
