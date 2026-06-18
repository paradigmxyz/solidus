import EvmCompiler.Functions.AllocationInteractionCall
import EvmCompiler.Functions.AllocationInteractionFrame

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCallPreludeResource

open AllocationInteractionCall
open AllocationInteractionCall.SelectedCallee
open AllocationInteractionCursor
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

/-- Complete all-stack parameter realization with one activation effect. -/
theorem parameters_stack
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
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
    (hContext :
      ParameterPrelude.Context lowerCtx plan frameWords realized pending
        frameDepth localsCtx)
    (hAllStack :
      ∀ binding, binding ∈ pending →
        AllocationLowering.isStackSlot lowerCtx binding.2 = true)
    (hRel :
      ActivationCalleeEntryRel contract plan realized pending frameBase
        .stack source target)
    (hStackLength : target.evm.stack.length = localsCtx.layout.length)
    (hReady : AllocatorReady config allocatorDepth target) :
    ∃ compiled finalCtx finalTarget fuel,
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
      ActivationStateRel contract plan
        ((pending.map Prod.fst).reverse ++ realized) 0 frameBase
        .stack source finalTarget ∧
      finalTarget.evm.stack.length = finalCtx.layout.length ∧
      ActivationEffect config allocatorDepth .stack target finalTarget := by
  cases hContext with
  | nil =>
      refine ⟨[], localsCtx, target, 1, by omega, rfl, ?_, ?_, ?_, ?_,
        hStackLength, ActivationEffect.refl hReady⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · intro targetExtra
        simpa using
          Expressions.InteractionSemantics.Block.openRun_nil
            targetProgram targetExtra target
      · simpa using hRel.finish
  | @stack _ tailPending _ _ _ name slot classification fresh location
      stackOrder tail =>
      have hNextRel :
          ActivationCalleeEntryRel contract plan (name :: realized)
            tailPending frameBase .stack source target := by
        simpa [ActivationMode.afterStackDeclaration] using
          hRel.activate_stack fresh location stackOrder
      obtain
          ⟨compiled, finalCtx, finalTarget, fuel, hFuel, hFuelLength,
            hCompile, hFinalLayout, hEvalAt, hFinalRel,
            hFinalStackLength, hEffect⟩ :=
        parameters_stack (targetProgram := targetProgram) tail
          (fun binding hBinding =>
            hAllStack binding (by simp [hBinding]))
          hNextRel hStackLength hReady
      refine
        ⟨compiled, finalCtx, finalTarget, fuel, hFuel, hFuelLength,
          ?_, ?_, hEvalAt, ?_, hFinalStackLength, hEffect⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
  | @scratch _ tailPending _ _ name slot classification _fresh _location
      _stackOrder _slotBound _layout _aboveFresh _suffixFresh
      _nameDepthBound _frameDepthLookup _frameDepthBound _tail =>
      have hCurrent := hAllStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

/-- Complete all-stack return initialization with one activation effect. -/
theorem returns_stack
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth : Nat}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Expressions.Program}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    (hContext :
      ReturnPrelude.Context lowerCtx plan frameWords live pending
        frameDepth localsCtx)
    (hAllStack :
      ∀ binding, binding ∈ pending →
        AllocationLowering.isStackSlot lowerCtx binding.2 = true)
    (hRel :
      ActivationStateRel contract plan live 0 frameBase .stack source target)
    (hZero :
      ∀ name, name ∈ pending.map Prod.fst →
        source.vars name = some AllocationSupport.zeroWord)
    (hStackLength : target.evm.stack.length = localsCtx.layout.length)
    (hReady : AllocatorReady config allocatorDepth target) :
    ∃ compiled finalCtx finalTarget fuel,
      0 < fuel ∧
      fuel = compiled.length + 1 ∧
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerReturns lowerCtx pending
          localsCtx.layout).2 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + fuel) { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ActivationStateRel contract plan
        ((pending.map Prod.fst).reverse ++ live) 0 frameBase .stack
        source finalTarget ∧
      finalTarget.evm.stack.length = finalCtx.layout.length ∧
      ActivationEffect config allocatorDepth .stack target finalTarget := by
  cases hContext with
  | nil =>
      refine ⟨[], localsCtx, target, 1, by omega, rfl, ?_, ?_, ?_, ?_,
        hStackLength, ActivationEffect.refl hReady⟩
      · simp [AllocationLowering.lowerReturns, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerReturns]
      · intro targetExtra
        simpa using
          Expressions.InteractionSemantics.Block.openRun_nil
            targetProgram targetExtra target
      · simpa using hRel
  | @stack _ tailPending _ _ _ name slot classification fresh location
      stackOrder tail =>
      let pushed := StateRel.pushTargetBy 33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.InteractionSemantics.Code.openRun
              [.push AllocationSupport.zeroWord] target =
            .done (.ok pushed) := by
        simpa [pushed, StateRel.pushTargetBy] using
          Locals.InteractionPreservation.Code.openRun_push
            AllocationSupport.zeroWord target
      have hPushedRel :
          ActivationStateRel contract plan live 1 frameBase .stack
            source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.evm.stack = AllocationSupport.zeroWord :: target.evm.stack :=
        rfl
      have hNameZero :
          source.vars name = some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          ActivationStateRel contract plan (name :: live) 0 frameBase .stack
            source pushed := by
        have hDeclared :=
          hPushedRel.declare_stack_live hPushedStack
            (fun other hOther => by
              simp at hOther
              exact hOther)
            location stackOrder
        rw [Locals.Source.State.insert_eq_of_apply_eq hNameZero] at hDeclared
        simpa [ActivationMode.afterStackDeclaration] using hDeclared
      have hNextStackLength :
          pushed.evm.stack.length =
            (localsCtx.withLayout
              (name :: localsCtx.layout)).layout.length := by
        rw [hPushedStack]
        simp [Locals.Ctx.withLayout, hStackLength]
      have hHeadEffect :
          ActivationEffect config allocatorDepth .stack target pushed := by
        exact AllocatorEffect.of_machine_eq hReady (by rfl)
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, tailFuel, hTailFuel,
            hTailFuelLength, hTailCompile, hFinalLayout, hTailEvalAt,
            hFinalRel, hFinalStackLength, hTailEffect⟩ :=
        returns_stack (targetProgram := targetProgram) tail
          (fun binding hBinding =>
            hAllStack binding (by simp [hBinding]))
          hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          hNextStackLength hHeadEffect.ready
      let headCode : Structured.Code :=
        [.push AllocationSupport.zeroWord] ++
          Locals.bindLocals 0 (name :: localsCtx.layout)
      let headStmt : Expressions.Stmt := .code headCode
      have hHeadCompile :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      have hHeadCodeRun :
          Structured.InteractionSemantics.Code.openRun headCode target =
            .done (.ok pushed) := by
        rw [show headCode =
            [.push AllocationSupport.zeroWord] ++
              Locals.bindLocals 0 (name :: localsCtx.layout) by rfl,
          Structured.InteractionSemantics.Code.openRun_append, hPushRun]
        rfl
      have hHeadStmtRun (targetExtra : Nat) :
          Expressions.EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Ordinary.runStateModel
              Structured.InteractionSemantics.handler targetProgram
              (targetExtra + tailFuel) headStmt target =
            .done (.ok (Structured.Outcome.regular pushed)) := by
        simp only [headStmt, Expressions.EffectSemantics.Control.Stmt.run]
        change
          Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun headCode target)
              _ =
            .done (.ok (Structured.Outcome.regular pushed))
        rw [hHeadCodeRun]
        rfl
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      have hCombinedEval :
          ∀ targetExtra,
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + (tailFuel + 1))
                { stmts := headStmt :: tailCompiled } target =
              .done (.ok (Structured.Outcome.regular finalTarget)) := by
        intro targetExtra
        have hFuel :
            targetExtra + (tailFuel + 1) =
              (targetExtra + tailFuel) + 1 := by omega
        rw [hFuel, Expressions.InteractionSemantics.Block.openRun_cons,
          hHeadStmtRun targetExtra]
        exact hTailEvalAt targetExtra
      refine
        ⟨headStmt :: tailCompiled, finalCtx, finalTarget, tailFuel + 1,
          by omega, ?_, ?_, ?_, hCombinedEval, ?_, hFinalStackLength,
          hHeadEffect.trans hTailEffect⟩
      · simp [hTailFuelLength]
      · simpa [headStmt, headCode, AllocationLowering.lowerReturns,
          classification] using hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
  | @scratch _ tailPending _ _ name slot classification _fresh _location
      _stackOrder _slotBound _frameDepthLookup _frameDepthBound _tail =>
      have hCurrent := hAllStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

/-- Complete mixed return initialization with one scratch activation effect. -/
theorem returns_scratch
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Expressions.Program}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hContext :
      ReturnPrelude.Context lowerCtx plan frameWords live pending
        frameDepth localsCtx)
    (hRel :
      ScratchStateRel contract plan live 0 frameBase frameDepth frameWords
        source target)
    (hZero :
      ∀ name, name ∈ pending.map Prod.fst →
        source.vars name = some AllocationSupport.zeroWord)
    (hFrameDepth :
      frameDepth = (currentStackOrder plan live).length)
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
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerReturns lowerCtx pending
          localsCtx.layout).2 ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + fuel) { stmts := compiled } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ScratchStateRel contract plan
        ((pending.map Prod.fst).reverse ++ live) 0 frameBase
        finalFrameDepth frameWords source finalTarget ∧
      finalFrameDepth =
        (currentStackOrder plan
          ((pending.map Prod.fst).reverse ++ live)).length ∧
      finalTarget.evm.stack.length = finalCtx.layout.length ∧
      ActivationEffect config allocatorDepth
        (.scratch frameDepth frameWords) target finalTarget := by
  cases hContext with
  | nil =>
      refine ⟨[], localsCtx, target, frameDepth, 1, by omega, rfl,
        ?_, ?_, ?_, ?_, ?_, hStackLength, ActivationEffect.refl hReady⟩
      · simp [AllocationLowering.lowerReturns, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerReturns]
      · intro targetExtra
        simpa using
          Expressions.InteractionSemantics.Block.openRun_nil
            targetProgram targetExtra target
      · simpa using hRel
      · simpa using hFrameDepth
  | @stack _ tailPending _ _ _ name slot classification fresh location
      stackOrder tail =>
      let pushed := StateRel.pushTargetBy 33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.InteractionSemantics.Code.openRun
              [.push AllocationSupport.zeroWord] target =
            .done (.ok pushed) := by
        simpa [pushed, StateRel.pushTargetBy] using
          Locals.InteractionPreservation.Code.openRun_push
            AllocationSupport.zeroWord target
      have hPushedRel :
          ScratchStateRel contract plan live 1 frameBase frameDepth
            frameWords source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.evm.stack = AllocationSupport.zeroWord :: target.evm.stack :=
        rfl
      have hNameZero :
          source.vars name = some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          ScratchStateRel contract plan (name :: live) 0 frameBase
            (frameDepth + 1) frameWords source pushed := by
        have hDeclared :=
          hPushedRel.declare_stack_live hPushedStack
            (fun other hOther => by
              simp at hOther
              exact hOther)
            location stackOrder
        rw [Locals.Source.State.insert_eq_of_apply_eq hNameZero] at hDeclared
        simpa using hDeclared
      have hNextStackLength :
          pushed.evm.stack.length =
            (localsCtx.withLayout
              (name :: localsCtx.layout)).layout.length := by
        rw [hPushedStack]
        simp [Locals.Ctx.withLayout, hStackLength]
      have hHeadEffect :
          ActivationEffect config allocatorDepth
            (.scratch frameDepth frameWords) target pushed :=
        ActivationEffect.of_allocatorEffect
          (AllocatorEffect.of_machine_eq hReady (by rfl))
      have hSame :=
        SameFrame.afterStackDeclaration
          (.scratch frameDepth frameWords)
      have hNextOwned := hOwned.sameFrame hSame
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth, tailFuel,
            hTailFuel, hTailFuelLength, hTailCompile, hFinalLayout,
            hTailEvalAt, hFinalRel, hFinalDepth, hFinalStackLength,
            hTailEffect⟩ :=
        returns_scratch (targetProgram := targetProgram) hConfig tail
          hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          (by
            rw [stackOrder, hFrameDepth]
            simp)
          hNextStackLength hWF hReservation hHeadEffect.ready hNextOwned
      let headCode : Structured.Code :=
        [.push AllocationSupport.zeroWord] ++
          Locals.bindLocals 0 (name :: localsCtx.layout)
      let headStmt : Expressions.Stmt := .code headCode
      have hHeadCompile :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      have hHeadCodeRun :
          Structured.InteractionSemantics.Code.openRun headCode target =
            .done (.ok pushed) := by
        rw [show headCode =
            [.push AllocationSupport.zeroWord] ++
              Locals.bindLocals 0 (name :: localsCtx.layout) by rfl,
          Structured.InteractionSemantics.Code.openRun_append, hPushRun]
        rfl
      have hHeadStmtRun (targetExtra : Nat) :
          Expressions.EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Ordinary.runStateModel
              Structured.InteractionSemantics.handler targetProgram
              (targetExtra + tailFuel) headStmt target =
            .done (.ok (Structured.Outcome.regular pushed)) := by
        simp only [headStmt, Expressions.EffectSemantics.Control.Stmt.run]
        change
          Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun headCode target)
              _ =
            .done (.ok (Structured.Outcome.regular pushed))
        rw [hHeadCodeRun]
        rfl
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      have hCombinedEval :
          ∀ targetExtra,
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + (tailFuel + 1))
                { stmts := headStmt :: tailCompiled } target =
              .done (.ok (Structured.Outcome.regular finalTarget)) := by
        intro targetExtra
        have hFuel :
            targetExtra + (tailFuel + 1) =
              (targetExtra + tailFuel) + 1 := by omega
        rw [hFuel, Expressions.InteractionSemantics.Block.openRun_cons,
          hHeadStmtRun targetExtra]
        exact hTailEvalAt targetExtra
      refine
        ⟨headStmt :: tailCompiled, finalCtx, finalTarget, finalFrameDepth,
          tailFuel + 1, by omega, ?_, ?_, ?_, hCombinedEval, ?_, ?_,
          hFinalStackLength,
          hHeadEffect.trans (hTailEffect.sameFrame hSame.symm)⟩
      · simp [hTailFuelLength]
      · simpa [headStmt, headCode, AllocationLowering.lowerReturns,
          classification] using hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
  | @scratch _ tailPending _ _ name slot classification fresh location
      stackOrder slotBound frameDepthLookup frameDepthBound tail =>
      obtain ⟨frameOp, hFrameOp⟩ :=
        Locals.StackOp.exists_dup?_of_pos_of_le
          (depth := 1 + (frameDepth + 1)) (by omega) frameDepthBound
      let pushed := StateRel.pushTargetBy 33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.InteractionSemantics.Code.openRun
              [.push AllocationSupport.zeroWord] target =
            .done (.ok pushed) := by
        simpa [pushed, StateRel.pushTargetBy] using
          Locals.InteractionPreservation.Code.openRun_push
            AllocationSupport.zeroWord target
      have hPushedRel :
          ScratchStateRel contract plan live 1 frameBase frameDepth
            frameWords source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.evm.stack = AllocationSupport.zeroWord :: target.evm.stack :=
        rfl
      have hRegion :
          reservation.containsRegion (scratchAddress frameBase slot) 1 :=
        hRel.scratchAddress_reserved_of_bound slotBound hReservation
      obtain
          ⟨midTarget, hStoreRun, hStoredRel, hStoredStack,
            hStoredMachine⟩ :=
        AllocationInteractionScratchStore.assignTop
          (stackOffset := 0) hPushedRel hPushedStack hWF
          (fun other hOther => by
            simp at hOther
            exact hOther)
          stackOrder location slotBound hReservation hRegion
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hFrameOp)
      have hNameZero :
          source.vars name = some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          ScratchStateRel contract plan (name :: live) 0 frameBase
            frameDepth frameWords source midTarget := by
        have hInsert :
            source.insert name AllocationSupport.zeroWord = source :=
          Locals.Source.State.insert_eq_of_apply_eq hNameZero
        simpa [hInsert] using hStoredRel
      have hNextStackLength :
          midTarget.evm.stack.length = localsCtx.layout.length := by
        rw [hStoredStack]
        exact hStackLength
      have hMachine :
          midTarget.evm.toMachineState =
            target.evm.toMachineState.mstore
              (EvmYul.UInt256.ofNat (scratchAddress frameBase slot))
              AllocationSupport.zeroWord := by
        simpa [pushed, StateRel.pushTargetBy] using hStoredMachine
      have hHeadBounded :=
        hOwned.boundedEffect_of_scratchStoreSlot hConfig hRel slotBound
          hReady hMachine
      have hHeadEffect :
          ActivationEffect config allocatorDepth
            (.scratch frameDepth frameWords) target midTarget :=
        ActivationEffect.of_boundedEffect hHeadBounded
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth, tailFuel,
            hTailFuel, hTailFuelLength, hTailCompile, hFinalLayout,
            hTailEvalAt, hFinalRel, hFinalDepth, hFinalStackLength,
            hTailEffect⟩ :=
        returns_scratch (targetProgram := targetProgram) hConfig tail
          hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          (by simpa [stackOrder] using hFrameDepth)
          hNextStackLength hWF hReservation hHeadEffect.ready hOwned
      let headCode : Structured.Code :=
        [.push AllocationSupport.zeroWord] ++
          [.op frameOp,
           .push (AllocationSupport.slotOffset slot),
           .op .add,
           .op .mstore]
      let headStmt : Expressions.Stmt := .code headCode
      have hHeadCompile :=
        AllocationLowering.lowerScratchReturn_compileOpen
          (ctx := lowerCtx) (name := name) (slot := slot)
          (frameDepth := frameDepth + 1) (localsCtx := localsCtx)
          (frameOp := frameOp) frameDepthLookup hFrameOp
      have hHeadCodeRun :
          Structured.InteractionSemantics.Code.openRun headCode target =
            .done (.ok midTarget) := by
        rw [show headCode =
            [.push AllocationSupport.zeroWord] ++
              [.op frameOp,
               .push (AllocationSupport.slotOffset slot),
               .op .add,
               .op .mstore] by rfl,
          Structured.InteractionSemantics.Code.openRun_append, hPushRun]
        exact hStoreRun
      have hHeadStmtRun (targetExtra : Nat) :
          Expressions.EffectSemantics.Control.Stmt.run
              Structured.EffectSemantics.Ordinary.runStateModel
              Structured.InteractionSemantics.handler targetProgram
              (targetExtra + tailFuel) headStmt target =
            .done (.ok (Structured.Outcome.regular midTarget)) := by
        simp only [headStmt, Expressions.EffectSemantics.Control.Stmt.run]
        change
          Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun headCode target)
              _ =
            .done (.ok (Structured.Outcome.regular midTarget))
        rw [hHeadCodeRun]
        rfl
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      have hCombinedEval :
          ∀ targetExtra,
            Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + (tailFuel + 1))
                { stmts := headStmt :: tailCompiled } target =
              .done (.ok (Structured.Outcome.regular finalTarget)) := by
        intro targetExtra
        have hFuel :
            targetExtra + (tailFuel + 1) =
              (targetExtra + tailFuel) + 1 := by omega
        rw [hFuel, Expressions.InteractionSemantics.Block.openRun_cons,
          hHeadStmtRun targetExtra]
        exact hTailEvalAt targetExtra
      refine
        ⟨headStmt :: tailCompiled, finalCtx, finalTarget, finalFrameDepth,
          tailFuel + 1, by omega, ?_, ?_, ?_, hCombinedEval, ?_, ?_,
          hFinalStackLength, hHeadEffect.trans hTailEffect⟩
      · simp [hTailFuelLength]
      · simpa [headStmt, headCode, AllocationLowering.lowerReturns,
          classification] using hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
termination_by pending.length

/-- Compiler-selected scratch parameter setup preserves one activation. -/
theorem Prepared.parameters_resource_scratch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase : Nat} {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase
        (.scratch 0 compilation.recipe.frameWords) source target)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReservation : contract.scratch? = some reservation)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch 0 compilation.recipe.frameWords)) :
    ∃ finalTarget finalFrameDepth fuel,
      0 < fuel ∧
      fuel = prepared.paramCode.length + 1 ∧
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryCtx.layout).2 ∧
      Expressions.InteractionSemantics.Block.openRun expressions fuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + fuel) { stmts := prepared.paramCode } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ScratchStateRel contract prepared.plan
        (artifact.slots.params.map Prod.fst).reverse 0 frameBase
        finalFrameDepth compilation.recipe.frameWords source finalTarget ∧
      finalFrameDepth =
        (currentStackOrder prepared.plan
          (artifact.slots.params.map Prod.fst).reverse).length ∧
      finalTarget.evm.stack.length = prepared.paramCtx.layout.length ∧
      ActivationEffect config allocatorDepth
        (.scratch 0 compilation.recipe.frameWords) target finalTarget := by
  obtain
      ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel, hFuel,
        hFuelLength, hCompile, hFinalLayout, hEvalAt, hFinalRel,
        hFinalDepth, hFinalStackLength, hEffect⟩ :=
    parameters_scratch (targetProgram := expressions) hConfig
      prepared.parameterContext hRel (by simp [currentStackOrder])
      hStackLength prepared.planWF hReservation hReady hOwned
  have hPair :
      (compiled, finalCtx) = (prepared.paramCode, prepared.paramCtx) :=
    Option.some.inj (hCompile.symm.trans prepared.compileParams)
  cases hPair
  exact
    ⟨finalTarget, finalFrameDepth, fuel, hFuel, hFuelLength, hFinalLayout,
      by simpa using hEvalAt 0, hEvalAt, by simpa using hFinalRel,
      by simpa using hFinalDepth, hFinalStackLength, hEffect⟩

/-- Compiler-selected all-stack parameter setup preserves one activation. -/
theorem Prepared.parameters_resource_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase .stack source target)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReady : AllocatorReady config allocatorDepth target) :
    ∃ finalTarget fuel,
      0 < fuel ∧
      fuel = prepared.paramCode.length + 1 ∧
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryCtx.layout).2 ∧
      Expressions.InteractionSemantics.Block.openRun expressions fuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + fuel) { stmts := prepared.paramCode } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ActivationStateRel contract prepared.plan
        (artifact.slots.params.map Prod.fst).reverse 0 frameBase .stack
        source finalTarget ∧
      finalTarget.evm.stack.length = prepared.paramCtx.layout.length ∧
      ActivationEffect config allocatorDepth .stack target finalTarget := by
  obtain
      ⟨compiled, finalCtx, finalTarget, fuel, hFuel, hFuelLength, hCompile,
        hFinalLayout, hEvalAt, hFinalRel, hFinalStackLength, hEffect⟩ :=
    parameters_stack (targetProgram := expressions)
      prepared.parameterContext
      (artifact.paramsAllStack_of_needsFrame_false hNeedsFrame)
      hRel hStackLength hReady
  have hPair :
      (compiled, finalCtx) = (prepared.paramCode, prepared.paramCtx) :=
    Option.some.inj (hCompile.symm.trans prepared.compileParams)
  cases hPair
  exact
    ⟨finalTarget, fuel, hFuel, hFuelLength, hFinalLayout,
      by simpa using hEvalAt 0, hEvalAt, by simpa using hFinalRel,
      hFinalStackLength, hEffect⟩

/-- Compiler-selected scratch return setup preserves one activation. -/
theorem Prepared.returns_resource_scratch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase : Nat} {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hRel :
      ScratchStateRel contract prepared.plan
        (artifact.slots.params.map Prod.fst).reverse 0 frameBase
        (currentStackOrder prepared.plan
          (artifact.slots.params.map Prod.fst).reverse).length
        compilation.recipe.frameWords source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = prepared.paramCtx.layout.length)
    (hReservation : contract.scratch? = some reservation)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch
          (currentStackOrder prepared.plan
            (artifact.slots.params.map Prod.fst).reverse).length
          compilation.recipe.frameWords)) :
    ∃ finalTarget finalFrameDepth fuel,
      0 < fuel ∧
      fuel = prepared.returnCode.length + 1 ∧
      prepared.returnCtx.layout =
        (AllocationLowering.lowerReturns artifact.lowerCtx
          artifact.slots.returns prepared.paramCtx.layout).2 ∧
      Expressions.InteractionSemantics.Block.openRun expressions fuel
          { stmts := prepared.returnCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + fuel) { stmts := prepared.returnCode } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ScratchStateRel contract prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        0 frameBase finalFrameDepth compilation.recipe.frameWords
        source finalTarget ∧
      finalFrameDepth =
        (currentStackOrder prepared.plan
          ((artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse)).length ∧
      finalTarget.evm.stack.length = prepared.returnCtx.layout.length ∧
      ActivationEffect config allocatorDepth
        (.scratch
          (currentStackOrder prepared.plan
            (artifact.slots.params.map Prod.fst).reverse).length
          compilation.recipe.frameWords)
        target finalTarget := by
  obtain
      ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel, hFuel,
        hFuelLength, hCompile, hFinalLayout, hEvalAt, hFinalRel,
        hFinalDepth, hFinalStackLength, hEffect⟩ :=
    returns_scratch (targetProgram := expressions) hConfig
      prepared.returnContext hRel hZero rfl hStackLength prepared.planWF
      hReservation hReady hOwned
  have hPair :
      (compiled, finalCtx) = (prepared.returnCode, prepared.returnCtx) :=
    Option.some.inj (hCompile.symm.trans prepared.compileReturns)
  cases hPair
  exact
    ⟨finalTarget, finalFrameDepth, fuel, hFuel, hFuelLength, hFinalLayout,
      by simpa using hEvalAt 0, hEvalAt, hFinalRel, hFinalDepth,
      hFinalStackLength, hEffect⟩

/-- Compiler-selected all-stack return setup preserves one activation. -/
theorem Prepared.returns_resource_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hRel :
      ActivationStateRel contract prepared.plan
        (artifact.slots.params.map Prod.fst).reverse 0 frameBase .stack
        source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = prepared.paramCtx.layout.length)
    (hReady : AllocatorReady config allocatorDepth target) :
    ∃ finalTarget fuel,
      0 < fuel ∧
      fuel = prepared.returnCode.length + 1 ∧
      prepared.returnCtx.layout =
        (AllocationLowering.lowerReturns artifact.lowerCtx
          artifact.slots.returns prepared.paramCtx.layout).2 ∧
      Expressions.InteractionSemantics.Block.openRun expressions fuel
          { stmts := prepared.returnCode } target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ targetExtra,
        Expressions.InteractionSemantics.Block.openRun expressions
            (targetExtra + fuel) { stmts := prepared.returnCode } target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      ActivationStateRel contract prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        0 frameBase .stack source finalTarget ∧
      finalTarget.evm.stack.length = prepared.returnCtx.layout.length ∧
      ActivationEffect config allocatorDepth .stack target finalTarget := by
  obtain
      ⟨compiled, finalCtx, finalTarget, fuel, hFuel, hFuelLength, hCompile,
        hFinalLayout, hEvalAt, hFinalRel, hFinalStackLength, hEffect⟩ :=
    returns_stack (targetProgram := expressions) prepared.returnContext
      (artifact.returnsAllStack_of_needsFrame_false hNeedsFrame)
      hRel hZero hStackLength hReady
  have hPair :
      (compiled, finalCtx) = (prepared.returnCode, prepared.returnCtx) :=
    Option.some.inj (hCompile.symm.trans prepared.compileReturns)
  cases hPair
  exact
    ⟨finalTarget, fuel, hFuel, hFuelLength, hFinalLayout,
      by simpa using hEvalAt 0, hEvalAt, hFinalRel, hFinalStackLength,
      hEffect⟩

/-- Scratch-backed compiler-selected setup reaches the body resource boundary. -/
theorem Prepared.body_entry_resource_scratch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase : Nat} {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hNeedsFrame : artifact.needsFrame = true)
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase
        (.scratch 0 compilation.recipe.frameWords) source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReservation : contract.scratch? = some reservation)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch 0 compilation.recipe.frameWords)) :
    ∃ afterParams finalTarget paramFuel returnFuel preludeFuel,
      0 < paramFuel ∧
      0 < returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions 4
          { stmts := prepared.markerCode } target =
        .done (.ok (Structured.Outcome.regular target)) ∧
      Expressions.InteractionSemantics.Block.openRun expressions paramFuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular afterParams)) ∧
      Expressions.InteractionSemantics.Block.openRun expressions returnFuel
          { stmts := prepared.returnCode } afterParams =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      0 < preludeFuel ∧
      preludeFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions preludeFuel
          { stmts :=
              prepared.markerCode ++
                (prepared.paramCode ++ prepared.returnCode) }
          target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ suffixFuel, 0 < suffixFuel →
        Expressions.InteractionSemantics.Block.openRun expressions
            (prepared.markerCode.length + prepared.paramCode.length +
              prepared.returnCode.length + suffixFuel)
            { stmts :=
                prepared.markerCode ++
                  (prepared.paramCode ++ prepared.returnCode) }
            target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      AllocationContext.ActivationInvariant contract artifact.lowerCtx
        artifact.bodyStart prepared.returnCtx prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        frameBase prepared.bodyMode source finalTarget ∧
      ActivationEffect config allocatorDepth
        (.scratch 0 compilation.recipe.frameWords) target finalTarget := by
  obtain
      ⟨afterParams, paramFrameDepth, paramFuel, hParamFuel,
        hParamFuelLength, _hParamLayout, hParamRun, hParamRunAt, hParamRel,
        hParamDepth, hParamStackLength, hParamEffect⟩ :=
    _root_.EvmCompiler.Functions.AllocationInteractionCallPreludeResource.Prepared.parameters_resource_scratch
      prepared hConfig hRel hStackLength hReservation hReady hOwned
  have hParamSame :
      SameFrame (.scratch 0 compilation.recipe.frameWords)
        (.scratch paramFrameDepth compilation.recipe.frameWords) :=
    .scratch 0 paramFrameDepth compilation.recipe.frameWords
  have hReturnOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch
          (currentStackOrder prepared.plan
            (artifact.slots.params.map Prod.fst).reverse).length
          compilation.recipe.frameWords) := by
    simpa [hParamDepth] using hOwned.sameFrame hParamSame
  obtain
      ⟨finalTarget, finalFrameDepth, returnFuel, hReturnFuel,
        hReturnFuelLength, _hReturnLayout, hReturnRun, hReturnRunAt,
        hReturnRel, hReturnDepth, hReturnStackLength, hReturnEffect⟩ :=
    _root_.EvmCompiler.Functions.AllocationInteractionCallPreludeResource.Prepared.returns_resource_scratch
      prepared hConfig
      (by simpa [hParamDepth] using hParamRel) hZero hParamStackLength
      hReservation hParamEffect.ready hReturnOwned
  obtain ⟨preludeFuel, hPreludeFuel, hPreludeLength, hPreludeRun⟩ :=
    prepared.prelude_forward hParamFuel hReturnFuel hParamFuelLength
      hParamRunAt hReturnRun
  have hState :
      ActivationStateRel contract prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        0 frameBase prepared.bodyMode source finalTarget := by
    have hScratchState :
        ActivationStateRel contract prepared.plan
          ((artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse)
          0 frameBase
          (.scratch finalFrameDepth compilation.recipe.frameWords)
          source finalTarget :=
      .scratch hReturnRel
    simpa [Prepared.bodyMode, Artifact.mode, hNeedsFrame,
      ActivationMode.atStackDepth, hReturnDepth] using hScratchState
  have hInvariant :
      AllocationContext.ActivationInvariant contract artifact.lowerCtx
        artifact.bodyStart prepared.returnCtx prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        frameBase prepared.bodyMode source finalTarget :=
    { compiler := prepared.bodyCompiler
      planWF := prepared.planWF
      defined := prepared.bodyLiveDefined hRel hZero
      state := hState
      stackLength := hReturnStackLength }
  have hEffect :
      ActivationEffect config allocatorDepth
        (.scratch 0 compilation.recipe.frameWords) target finalTarget :=
    hParamEffect.trans
      (hReturnEffect.sameFrame
        (.scratch
          (currentStackOrder prepared.plan
            (artifact.slots.params.map Prod.fst).reverse).length
          0 compilation.recipe.frameWords))
  exact
    ⟨afterParams, finalTarget, paramFuel, returnFuel, preludeFuel,
      hParamFuel, hReturnFuel, prepared.markers_forward target,
      hParamRun, hReturnRun, hPreludeFuel, hPreludeLength, hPreludeRun,
      (fun suffixFuel hSuffixFuel =>
        prepared.prelude_forward_at hParamFuelLength hReturnFuelLength
          hParamRunAt hReturnRunAt suffixFuel hSuffixFuel),
      hInvariant, hEffect⟩

/-- All-stack compiler-selected setup reaches the body resource boundary. -/
theorem Prepared.body_entry_resource_stack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    {contract : MemoryContract.Contract}
    {config : Config} {allocatorDepth frameBase : Nat}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    (hNeedsFrame : artifact.needsFrame = false)
    (hRel :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase .stack source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReady : AllocatorReady config allocatorDepth target) :
    ∃ afterParams finalTarget paramFuel returnFuel preludeFuel,
      0 < paramFuel ∧
      0 < returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions 4
          { stmts := prepared.markerCode } target =
        .done (.ok (Structured.Outcome.regular target)) ∧
      Expressions.InteractionSemantics.Block.openRun expressions paramFuel
          { stmts := prepared.paramCode } target =
        .done (.ok (Structured.Outcome.regular afterParams)) ∧
      Expressions.InteractionSemantics.Block.openRun expressions returnFuel
          { stmts := prepared.returnCode } afterParams =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      0 < preludeFuel ∧
      preludeFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          returnFuel ∧
      Expressions.InteractionSemantics.Block.openRun expressions preludeFuel
          { stmts :=
              prepared.markerCode ++
                (prepared.paramCode ++ prepared.returnCode) }
          target =
        .done (.ok (Structured.Outcome.regular finalTarget)) ∧
      (∀ suffixFuel, 0 < suffixFuel →
        Expressions.InteractionSemantics.Block.openRun expressions
            (prepared.markerCode.length + prepared.paramCode.length +
              prepared.returnCode.length + suffixFuel)
            { stmts :=
                prepared.markerCode ++
                  (prepared.paramCode ++ prepared.returnCode) }
            target =
          .done (.ok (Structured.Outcome.regular finalTarget))) ∧
      AllocationContext.ActivationInvariant contract artifact.lowerCtx
        artifact.bodyStart prepared.returnCtx prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        frameBase prepared.bodyMode source finalTarget ∧
      ActivationEffect config allocatorDepth .stack target finalTarget := by
  obtain
      ⟨afterParams, paramFuel, hParamFuel, hParamFuelLength,
        _hParamLayout, hParamRun, hParamRunAt, hParamRel,
        hParamStackLength, hParamEffect⟩ :=
    _root_.EvmCompiler.Functions.AllocationInteractionCallPreludeResource.Prepared.parameters_resource_stack
      prepared hNeedsFrame hRel hStackLength hReady
  obtain
      ⟨finalTarget, returnFuel, hReturnFuel, hReturnFuelLength,
        _hReturnLayout, hReturnRun, hReturnRunAt, hReturnRel,
        hReturnStackLength, hReturnEffect⟩ :=
    _root_.EvmCompiler.Functions.AllocationInteractionCallPreludeResource.Prepared.returns_resource_stack
      prepared hNeedsFrame hParamRel hZero hParamStackLength
      hParamEffect.ready
  obtain ⟨preludeFuel, hPreludeFuel, hPreludeLength, hPreludeRun⟩ :=
    prepared.prelude_forward hParamFuel hReturnFuel hParamFuelLength
      hParamRunAt hReturnRun
  have hState :
      ActivationStateRel contract prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        0 frameBase prepared.bodyMode source finalTarget := by
    simpa [Prepared.bodyMode, Artifact.mode, hNeedsFrame,
      ActivationMode.atStackDepth] using hReturnRel
  have hInvariant :
      AllocationContext.ActivationInvariant contract artifact.lowerCtx
        artifact.bodyStart prepared.returnCtx prepared.plan
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        frameBase prepared.bodyMode source finalTarget :=
    { compiler := prepared.bodyCompiler
      planWF := prepared.planWF
      defined := prepared.bodyLiveDefined hRel hZero
      state := hState
      stackLength := hReturnStackLength }
  exact
    ⟨afterParams, finalTarget, paramFuel, returnFuel, preludeFuel,
      hParamFuel, hReturnFuel, prepared.markers_forward target,
      hParamRun, hReturnRun, hPreludeFuel, hPreludeLength, hPreludeRun,
      (fun suffixFuel hSuffixFuel =>
        prepared.prelude_forward_at hParamFuelLength hReturnFuelLength
          hParamRunAt hReturnRunAt suffixFuel hSuffixFuel),
      hInvariant, hParamEffect.trans hReturnEffect⟩

end AllocationInteractionCallPreludeResource
end Functions
end EvmCompiler
