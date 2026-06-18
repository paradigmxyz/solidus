import EvmCompiler.Functions.AllocationInteractionCall
import EvmCompiler.Functions.AllocationInteractionFrame

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCallPreludeResource

open AllocationInteractionCall
open AllocationInteractionFrame
open AllocationInteractionRelation

/-- One compiler-emitted scratch-parameter realization preserves resources. -/
theorem scratch_parameter_step
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {plan : Locals.Allocation.Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords slot : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {name : Locals.Name}
    {ctx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {above suffix : Locals.Layout}
    {targetProgram : Expressions.Program}
    {reservation : MemoryContract.ScratchReservation}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hRel :
      ActivationCalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase
        (.scratch frameDepth frameWords) source target)
    (hWF : plan.WellFormed)
    (hLocation : plan.location? name = some (.scratch slot))
    (hStackOrder :
      currentStackOrder plan (name :: realized) =
        currentStackOrder plan realized)
    (hSlot : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hLayout : localsCtx.layout = above ++ name :: suffix)
    (hAboveLength : above.length = pending.length)
    (hAboveFresh : name ∉ above)
    (hSuffixFresh : name ∉ suffix)
    (hNameDepthBound : above.length + 1 ≤ 16)
    (hFrameDepth :
      Locals.Layout.lookupDepth? ctx.frameName (above ++ name :: suffix) =
        some ((pending.length + 1) + frameDepth + 1))
    (hFrameDepthBound :
      1 + ((pending.length + 1) + frameDepth + 1) ≤ 16)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    ∃ compiled final,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerScratchParam ctx name slot
                (above ++ name :: suffix)).1 } =
        some (compiled, localsCtx.withLayout (above ++ suffix)) ∧
      compiled.length = 3 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + 4) { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular final))) ∧
      ActivationCalleeEntryRel contract plan (name :: realized) pending
        frameBase (.scratch frameDepth frameWords) source final ∧
      final.evm.stack.length + 1 = target.evm.stack.length ∧
      ActivationEffect config allocatorDepth
        (.scratch frameDepth frameWords) target final := by
  obtain
      ⟨compiled, final, hCompile, hLength, hRun, hFinalRel, hStackLength,
        hMachine⟩ :=
    ParameterPrelude.scratch_step_of_lowerScratchParam
      (targetProgram := targetProgram) hRel hWF hLocation hStackOrder hSlot
      hReservation hLayout hAboveLength hAboveFresh hSuffixFresh
      hNameDepthBound hFrameDepth hFrameDepthBound
  have hScratch :
      ScratchStateRel contract plan realized (pending.length + 1) frameBase
        frameDepth frameWords source target := by
    cases hRel.state with
    | scratch hState => simpa using hState
  have hBounded :=
    hOwned.boundedEffect_of_scratchStoreSlot hConfig hScratch hSlot hReady
      hMachine
  have hEffect :
      ActivationEffect config allocatorDepth
        (.scratch frameDepth frameWords) target final :=
    ActivationEffect.of_boundedEffect (by simpa using hBounded)
  exact
    ⟨compiled, final, hCompile, hLength, hRun, hFinalRel, hStackLength,
      hEffect⟩

/-- Complete scratch-backed parameter realization with one activation effect. -/
theorem parameters_scratch
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Expressions.Program}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hContext :
      ParameterPrelude.Context lowerCtx plan frameWords realized pending
        frameDepth localsCtx)
    (hRel :
      ActivationCalleeEntryRel contract plan realized pending frameBase
        (.scratch frameDepth frameWords) source target)
    (hFrameDepth :
      frameDepth = (currentStackOrder plan realized).length)
    (hStackLength : target.evm.stack.length = localsCtx.layout.length)
    (hWF : plan.WellFormed)
    (hReservation : contract.scratch? = some reservation)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    ∃ compiled finalCtx finalTarget finalFrameDepth fuel,
      0 < fuel ∧
      fuel = compiled.length + 1 ∧
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerParams lowerCtx pending
          localsCtx.layout).2 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + fuel) { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ScratchStateRel contract plan
        ((pending.map Prod.fst).reverse ++ realized) 0 frameBase
        finalFrameDepth frameWords source finalTarget ∧
      finalFrameDepth =
        (currentStackOrder plan
          ((pending.map Prod.fst).reverse ++ realized)).length ∧
      finalTarget.evm.stack.length = finalCtx.layout.length ∧
      ActivationEffect config allocatorDepth
        (.scratch frameDepth frameWords) target finalTarget := by
  cases hContext with
  | nil =>
      refine ⟨[], localsCtx, target, frameDepth, 1, by omega, rfl,
        ?_, ?_, ?_, ?_, ?_, hStackLength, ?_⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · intro targetExtra
        simpa using
          Expressions.InteractionSemantics.Block.openRun_nil
            targetProgram targetExtra target
      · cases hRel.finish with
        | scratch state => simpa using state
      · simpa using hFrameDepth
      · exact ActivationEffect.refl hReady
  | @stack _ tailPending _ planDepth _ name slot classification fresh
      location stackOrder tail =>
      have hNextRel :
          ActivationCalleeEntryRel contract plan (name :: realized)
            tailPending frameBase
            (.scratch (frameDepth + 1) frameWords) source target := by
        simpa [ActivationMode.afterStackDeclaration] using
          hRel.activate_stack fresh location stackOrder
      have hSame :=
        SameFrame.afterStackDeclaration
          (.scratch frameDepth frameWords)
      have hNextOwned := hOwned.sameFrame hSame
      obtain
          ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel,
            hFuel, hFuelLength, hCompile, hFinalLayout, hEvalAt, hFinalRel,
            hFinalDepth, hFinalStackLength, hTailEffect⟩ :=
        parameters_scratch (targetProgram := targetProgram) hConfig tail
          hNextRel
          (by
            rw [stackOrder, hFrameDepth]
            simp)
          hStackLength hWF hReservation hReady hNextOwned
      refine
        ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel, hFuel,
          hFuelLength, ?_, ?_, hEvalAt, ?_, ?_, hFinalStackLength, ?_⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hTailEffect.sameFrame hSame.symm
  | @scratch _ tailPending _ _ name slot classification fresh location
      stackOrder slotBound layout aboveFresh suffixFresh nameDepthBound
      frameDepthLookup frameDepthBound tail =>
      let above : Locals.Layout := (tailPending.map Prod.fst).reverse
      let suffix : Locals.Layout :=
        currentStackOrder plan (name :: realized) ++ [lowerCtx.frameName]
      have hLayout : localsCtx.layout = above ++ name :: suffix := by
        simpa [above, suffix, stackOrder] using layout
      have hSuffixFresh : name ∉ suffix := by
        simpa [suffix, stackOrder] using suffixFresh
      have hFrameDepthLookup :
          Locals.Layout.lookupDepth? lowerCtx.frameName
              (above ++ name :: suffix) =
            some ((tailPending.length + 1) + frameDepth + 1) := by
        simpa [above, suffix, stackOrder] using frameDepthLookup
      obtain
          ⟨headCompiled, midTarget, hHeadCompile, hHeadLength,
            hHeadEval, hNextRel, hStepLength, hHeadEffect⟩ :=
        scratch_parameter_step hConfig hRel hWF location stackOrder slotBound
          hReservation hLayout (by simp [above])
          (by simpa [above] using aboveFresh) hSuffixFresh
          (by simpa [above] using nameDepthBound) hFrameDepthLookup
          frameDepthBound hReady hOwned
      have hMidStackLength :
          midTarget.evm.stack.length =
            (localsCtx.withLayout (above ++ suffix)).layout.length := by
        simp only [Locals.Ctx.withLayout]
        have hInitialLength :
            target.evm.stack.length = (above ++ name :: suffix).length := by
          rw [hStackLength, hLayout]
        simp only [List.length_append, List.length_cons] at hInitialLength
        simp only [List.length_append]
        omega
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth, tailFuel,
            hTailFuel, hTailFuelLength, hTailCompile, hFinalLayout,
            hTailEvalAt, hFinalRel, hFinalDepth, hFinalStackLength,
            hTailEffect⟩ :=
        parameters_scratch (targetProgram := targetProgram) hConfig tail
          hNextRel (by simpa [stackOrder] using hFrameDepth)
          (by
            simpa [above, suffix, List.append_assoc] using hMidStackLength)
          hWF hReservation hHeadEffect.ready hOwned
      have hHeadCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  (AllocationLowering.lowerScratchParam lowerCtx name slot
                    localsCtx.layout).1 } =
            some
              (headCompiled, localsCtx.withLayout (above ++ suffix)) := by
        simpa [hLayout] using hHeadCompile
      have hTailCompile' :
          Locals.Block.compileOpen
              (localsCtx.withLayout (above ++ suffix))
              { stmts :=
                  (AllocationLowering.lowerParams lowerCtx tailPending
                    (above ++ suffix)).1 } =
            some (tailCompiled, finalCtx) := by
        simpa [Locals.Ctx.withLayout, above, suffix,
          List.append_assoc] using hTailCompile
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile' hTailCompile'
      have hErase :
          AllocationLowering.eraseName name (above ++ name :: suffix) =
            above ++ suffix :=
        AllocationLowering.eraseName_append_name aboveFresh hSuffixFresh
      let fuel := headCompiled.length + tailFuel
      have hCombinedEval :
          ∀ targetExtra,
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + fuel)
                { stmts := headCompiled ++ tailCompiled } target =
              .done (.ok (Structured.Outcome.regular finalTarget)) := by
        intro targetExtra
        have hHeadAtFuel :
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + fuel) { stmts := headCompiled } target =
              .done (.ok (Structured.Outcome.regular midTarget)) := by
          have hRun := hHeadEval (targetExtra + tailFuel - 1)
          have hFuelEq :
              targetExtra + tailFuel - 1 + 4 = targetExtra + fuel := by
            simp [fuel, hHeadLength]
            omega
          simpa [hFuelEq] using hRun
        rw [Expressions.InteractionSemantics.Block.openRun_append,
          hHeadAtFuel]
        have hRemaining :
            targetExtra + fuel - headCompiled.length =
              targetExtra + tailFuel := by
          simp only [fuel]
          omega
        simpa [hRemaining] using hTailEvalAt targetExtra
      refine
        ⟨headCompiled ++ tailCompiled, finalCtx, finalTarget,
          finalFrameDepth, fuel, ?_, ?_, ?_, ?_, hCombinedEval, ?_, ?_,
          hFinalStackLength, hHeadEffect.trans hTailEffect⟩
      · simp [fuel]
        omega
      · simp only [fuel, List.length_append, hHeadLength, hTailFuelLength]
        omega
      · simpa [AllocationLowering.lowerParams, classification, hLayout,
          AllocationLowering.lowerScratchParam, hErase] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerParams, classification, hLayout,
          AllocationLowering.lowerScratchParam, hErase] using hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
termination_by pending.length

end AllocationInteractionCallPreludeResource
end Functions
end EvmCompiler
