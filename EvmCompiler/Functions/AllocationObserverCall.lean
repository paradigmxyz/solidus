import EvmCompiler.Functions.AllocationObserverExpression

namespace EvmCompiler
namespace Functions
namespace AllocationObserverCall

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

open AllocationObserverRelation

namespace EntryMarkers

theorem compileOpen
    {localsCtx : Locals.Ctx}
    {entryLayout : Locals.Layout}
    {baseDepth : Nat}
    {scratchBindings : List (Locals.Name × Nat)}
    {needsFrame : Bool} :
    Locals.Block.compileOpen localsCtx
        { stmts :=
            [AllocationLowering.bindEntryLayout entryLayout] ++
              if needsFrame then
                [AllocationLowering.bindScratchBindings
                  baseDepth scratchBindings]
              else
                [] } =
      some
        ([Expressions.Stmt.code
            [Structured.BasicInstr.bindLocals 0 entryLayout]] ++
          if needsFrame then
            [Expressions.Stmt.code
              (AllocationSupport.bindScratchBindingsCode
                baseDepth scratchBindings)]
          else
            [],
         localsCtx) := by
  cases needsFrame <;>
    simp [AllocationLowering.bindEntryLayout,
      AllocationLowering.bindScratchBindings,
      Locals.Block.compileOpen, Locals.Stmt.compile,
      Locals.Expr.compileCode, Locals.codeStmt]

theorem run_bindScratchBindingsCode
    {transcript : Trace}
    (baseDepth : Nat)
    (bindings : List (Locals.Name × Nat))
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.Code.run
        (AllocationSupport.bindScratchBindingsCode baseDepth bindings)
        target =
      .ok target := by
  induction bindings with
  | nil =>
      rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, slot⟩
      simp only [AllocationSupport.bindScratchBindingsCode, List.map_cons]
      rw [Structured.ObserverSemantics.Code.run_cons_eq_run_single_bind]
      change
        (Except.ok target).bind
          (Structured.ObserverSemantics.Code.run
            (AllocationSupport.bindScratchBindingsCode baseDepth rest)) =
          .ok target
      simpa only [Except.bind] using ih

theorem run
    {transcript : Trace}
    (entryLayout : Locals.Layout)
    (baseDepth : Nat)
    (scratchBindings : List (Locals.Name × Nat))
    (needsFrame : Bool)
    (target : Structured.ObserverSemantics.State transcript) :
    Structured.ObserverSemantics.Code.run
        ([Structured.BasicInstr.bindLocals 0 entryLayout] ++
          if needsFrame then
            AllocationSupport.bindScratchBindingsCode
              baseDepth scratchBindings
          else
            [])
        target =
      .ok target := by
  cases needsFrame with
  | false =>
      rfl
  | true =>
      rw [AllocationObserverPreservation.ObserverCode.run_append]
      change
        (Except.ok target).bind
            (Structured.ObserverSemantics.Code.run
              (AllocationSupport.bindScratchBindingsCode
                baseDepth scratchBindings)) =
          .ok target
      simpa only [Except.bind] using
        run_bindScratchBindingsCode baseDepth scratchBindings target

theorem eval
    {transcript : Trace}
    (program : Structured.Program)
    (entryLayout : Locals.Layout)
    (baseDepth : Nat)
    (scratchBindings : List (Locals.Name × Nat))
    (needsFrame : Bool)
    (target : Structured.ObserverSemantics.State transcript) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval program fuel
        { stmts :=
            [Structured.Stmt.code
              [Structured.BasicInstr.bindLocals 0 entryLayout]] ++
              if needsFrame then
                [Structured.Stmt.code
                  (AllocationSupport.bindScratchBindingsCode
                    baseDepth scratchBindings)]
              else
                [] }
        target
        (Structured.EffectSemantics.Outcome.regular target) := by
  cases needsFrame with
  | false =>
      exact
        ⟨2,
          Structured.EffectSemantics.Block.Eval.cons_regular
            (Structured.EffectSemantics.Stmt.Eval.code (by rfl))
            Structured.EffectSemantics.Block.Eval.nil⟩
  | true =>
      refine
        ⟨3,
          Structured.EffectSemantics.Block.Eval.cons_regular
            (Structured.EffectSemantics.Stmt.Eval.code (by rfl))
            ?_⟩
      exact
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code
            (run_bindScratchBindingsCode
              baseDepth scratchBindings target))
          Structured.EffectSemantics.Block.Eval.nil

end EntryMarkers

namespace ParameterPrelude

/--
Execute the concrete scratch-parameter sequence while converting one raw entry
argument into an ordinary live spilled local.

The code is exactly the value `DUP`, frame-address/store tail, compiler
promotion swaps, and final `POP` emitted by `lowerScratchParam`.
-/
theorem scratch_step_code
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name}
    {nameOp frameOp : Structured.BasicOp}
    {promoteCode : Structured.Code}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      AllocationObserverRelation.CalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase frameDepth frameWords
        source target)
    (hWF : plan.WellFormed)
    (hFresh : name ∉ realized)
    (hLocation : plan.location? name = some (.scratch slot))
    (hStackOrder :
      AllocationObserverRelation.currentStackOrder plan (name :: realized) =
        AllocationObserverRelation.currentStackOrder plan realized)
    (hSlot : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hNameOp :
      Locals.StackOp.dup? (pending.length + 1) = some nameOp)
    (hFrameOp :
      Locals.StackOp.dup?
          ((pending.length + 1) + frameDepth + 2) =
        some frameOp)
    (hPromote :
      Locals.Ctx.swapRestoreUpTo? pending.length = some promoteCode) :
    ∃ written promoted final,
      Structured.ObserverSemantics.Code.run
          ([Structured.BasicInstr.op nameOp] ++
            [ Structured.BasicInstr.op frameOp,
              Structured.BasicInstr.push
                (AllocationSupport.slotOffset slot),
              Structured.BasicInstr.op .add,
              Structured.BasicInstr.op .mstore ])
          target =
        .ok written ∧
      Structured.ObserverSemantics.Code.run promoteCode written =
        .ok promoted ∧
      Structured.ObserverSemantics.Code.run
          [Structured.BasicInstr.op .pop] promoted =
        .ok final ∧
      Structured.ObserverSemantics.Code.run
          ([Structured.BasicInstr.op nameOp] ++
            [ Structured.BasicInstr.op frameOp,
              Structured.BasicInstr.push
                (AllocationSupport.slotOffset slot),
              Structured.BasicInstr.op .add,
              Structured.BasicInstr.op .mstore ] ++
            promoteCode ++
            [Structured.BasicInstr.op .pop])
          target =
        .ok final ∧
      AllocationObserverRelation.CalleeEntryRel contract plan
        (name :: realized) pending frameBase frameDepth frameWords
        source final := by
  obtain ⟨value, values, suffix, hValue, hLookup, hTargetStack⟩ :=
    hRel.cons_parts
  have hValuesLength :
      values.length = pending.length := by
    simpa using Functions.Source.Store.lookupMany_length hLookup
  have hValueAt :
      target.source.evm.stack[pending.length]? = some value := by
    rw [hTargetStack]
    simp [hValuesLength]
  let afterValue :=
    AllocationObserverRelation.StateRel.pushTarget value target
  have hValueRun :
      Structured.ObserverSemantics.Code.run
          [Structured.BasicInstr.op nameOp] target =
        .ok afterValue := by
    exact
      AllocationObserverPreservation.ObserverCode.run_dup
        hNameOp hValueAt
  have hAfterValueRel :
      AllocationObserverRelation.ScratchStateRel contract plan realized
        ((pending.length + 1) + 1) frameBase frameDepth frameWords
        source afterValue := by
    simpa using hRel.state.push_target value
  have hAfterValueStack :
      afterValue.source.evm.stack =
        value :: target.source.evm.stack := by
    rfl
  have hRegion :
      reservation.containsRegion
        (AllocationObserverRelation.scratchAddress frameBase slot) 1 :=
    hRel.state.scratchAddress_reserved_of_bound hSlot hReservation
  obtain ⟨written, hStoreRun, hWrittenRel, hWrittenStack⟩ :=
    AllocationObserverPreservation.Expr.scratchAssignTop_forward_live
      (stackOffset := pending.length + 1)
      hAfterValueRel hAfterValueStack hWF
      (fun other hOther => by
        simp at hOther
        exact hOther)
      hStackOrder (by simp) hLocation hSlot hReservation hRegion hFrameOp
  have hWrittenRel' :
      AllocationObserverRelation.ScratchStateRel contract plan
        (name :: realized) (pending.length + 1) frameBase
        frameDepth frameWords source written := by
    have hInsert :
        source.source.insert name value = source.source :=
      Locals.Source.State.insert_eq_of_apply_eq hValue
    simpa [hInsert] using hWrittenRel
  have hWrittenStack' :
      written.source.evm.stack =
        values.reverse ++ value :: suffix := by
    rw [hWrittenStack, hTargetStack]
  obtain
      ⟨promoted, hPromoteRun, hPromoteCursor,
        hPromoteStack, hPromoteShared, _hPromoteReturns⟩ :=
    AllocationObserverPreservation.ObserverCode.run_swapRestoreUpTo?
      hPromote (by simp [hValuesLength]) hWrittenStack'
  let final :=
    AllocationObserverRelation.StateRel.replaceStackBy
      1 (values.reverse ++ suffix) promoted
  have hPopRun :
      Structured.ObserverSemantics.Code.run
          [Structured.BasicInstr.op .pop] promoted =
        .ok final := by
    simpa [final] using
      AllocationObserverPreservation.ObserverCode.run_pop hPromoteStack
  have hFinalCursor : final.cursor = written.cursor := by
    rw [show final.cursor = promoted.cursor by
      simp [final, AllocationObserverRelation.StateRel.replaceStackBy,
        Simulation.ResourceReplay.State.withSource]]
    exact hPromoteCursor
  have hFinalShared :
      final.source.evm.toSharedState =
        written.source.evm.toSharedState := by
    rw [show
        final.source.evm.toSharedState =
          promoted.source.evm.toSharedState by
      simp [final, AllocationObserverRelation.StateRel.replaceStackBy,
        Simulation.ResourceReplay.State.withSource,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]]
    exact hPromoteShared
  have hFinalStack :
      final.source.evm.stack = values.reverse ++ suffix := by
    rfl
  have hFinalRel :
      AllocationObserverRelation.CalleeEntryRel contract plan
        (name :: realized) pending frameBase frameDepth frameWords
        source final := by
    apply hRel.activate_scratch_after hLookup hTargetStack hWrittenRel'
    · exact hWrittenStack
    · exact hFinalCursor
    · exact hFinalShared
    · exact hFinalStack
  have hWholeStoreRun :
      Structured.ObserverSemantics.Code.run
          ([Structured.BasicInstr.op nameOp] ++
            [ Structured.BasicInstr.op frameOp,
              Structured.BasicInstr.push
                (AllocationSupport.slotOffset slot),
              Structured.BasicInstr.op .add,
              Structured.BasicInstr.op .mstore ])
          target =
        .ok written := by
    rw [AllocationObserverPreservation.ObserverCode.run_append, hValueRun]
    exact hStoreRun
  refine
    ⟨written, promoted, final, hWholeStoreRun, hPromoteRun,
      hPopRun, ?_, hFinalRel⟩
  let storeCode : Structured.Code :=
    [ Structured.BasicInstr.op frameOp,
      Structured.BasicInstr.push (AllocationSupport.slotOffset slot),
      Structured.BasicInstr.op .add,
      Structured.BasicInstr.op .mstore ]
  change
    Structured.ObserverSemantics.Code.run
        ((([Structured.BasicInstr.op nameOp] ++ storeCode) ++
            promoteCode) ++
          [Structured.BasicInstr.op .pop])
        target =
      .ok final
  rw [AllocationObserverPreservation.ObserverCode.run_append]
  change
    (Structured.ObserverSemantics.Code.run
        (([Structured.BasicInstr.op nameOp] ++ storeCode) ++ promoteCode)
        target).bind
      (Structured.ObserverSemantics.Code.run
        [Structured.BasicInstr.op .pop]) =
      .ok final
  rw [AllocationObserverPreservation.ObserverCode.run_append]
  change
    ((Structured.ObserverSemantics.Code.run
        ([Structured.BasicInstr.op nameOp] ++ storeCode) target).bind
      (Structured.ObserverSemantics.Code.run promoteCode)).bind
      (Structured.ObserverSemantics.Code.run
        [Structured.BasicInstr.op .pop]) =
      .ok final
  rw [AllocationObserverPreservation.ObserverCode.run_append, hValueRun]
  simp only [Except.bind]
  change
    ((Structured.ObserverSemantics.Code.run storeCode afterValue).bind
        (Structured.ObserverSemantics.Code.run promoteCode)).bind
      (Structured.ObserverSemantics.Code.run
        [Structured.BasicInstr.op .pop]) =
      .ok final
  rw [show
      Structured.ObserverSemantics.Code.run storeCode afterValue =
        .ok written by simpa [storeCode] using hStoreRun]
  simp only [Except.bind]
  rw [hPromoteRun]
  exact hPopRun

/--
Compile and evaluate one real scratch-parameter prelude step.

The opcode witnesses are constructed from source-facing stack-depth bounds,
and the resulting Structured block is the actual output of
`lowerScratchParam` followed by `Locals.Block.compileOpen`.
-/
theorem scratch_step_of_lowerScratchParam
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameBase frameDepth frameWords slot : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {name : Locals.Name}
    {ctx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {above suffix : Locals.Layout}
    {targetProgram : Structured.Program}
    {reservation : MemoryContract.ScratchReservation}
    (hRel :
      AllocationObserverRelation.CalleeEntryRel contract plan realized
        ((name, slot) :: pending) frameBase frameDepth frameWords
        source target)
    (hWF : plan.WellFormed)
    (hFresh : name ∉ realized)
    (hLocation : plan.location? name = some (.scratch slot))
    (hStackOrder :
      AllocationObserverRelation.currentStackOrder plan (name :: realized) =
        AllocationObserverRelation.currentStackOrder plan realized)
    (hSlot : slot < frameWords)
    (hReservation : contract.scratch? = some reservation)
    (hLayout :
      localsCtx.layout = above ++ name :: suffix)
    (hAboveLength : above.length = pending.length)
    (hAboveFresh : name ∉ above)
    (hSuffixFresh : name ∉ suffix)
    (hNameDepthBound : above.length + 1 ≤ 16)
    (hFrameDepth :
      Locals.Layout.lookupDepth? ctx.frameName
          (above ++ name :: suffix) =
        some ((pending.length + 1) + frameDepth + 1))
    (hFrameDepthBound :
      1 + ((pending.length + 1) + frameDepth + 1) ≤ 16) :
    ∃ compiled final,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerScratchParam ctx name slot
                (above ++ name :: suffix)).1 } =
        some
          (compiled, localsCtx.withLayout (above ++ suffix)) ∧
      Structured.ObserverSemantics.Block.Eval targetProgram 4
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular final) ∧
      AllocationObserverRelation.CalleeEntryRel contract plan
        (name :: realized) pending frameBase frameDepth frameWords
        source final := by
  obtain ⟨nameOp, hNameOp⟩ :=
    Locals.StackOp.exists_dup?_of_pos_of_le
      (depth := above.length + 1) (by omega) hNameDepthBound
  obtain ⟨frameOp, hFrameOp⟩ :=
    Locals.StackOp.exists_dup?_of_pos_of_le
      (depth := 1 + ((pending.length + 1) + frameDepth + 1))
      (by omega) hFrameDepthBound
  obtain ⟨promoteCode, hPromote⟩ :=
    Locals.Ctx.exists_swapRestoreUpTo?_of_le
      (depth := above.length) (by omega)
  have hCompile :=
    AllocationLowering.lowerScratchParam_compileOpen
      (ctx := ctx) (name := name) (slot := slot)
      (frameDepth := (pending.length + 1) + frameDepth + 1)
      (above := above) (suffix := suffix) (localsCtx := localsCtx)
      (nameOp := nameOp) (frameOp := frameOp)
      (promoteCode := promoteCode)
      hLayout hAboveFresh hSuffixFresh (by omega) hFrameDepth
      hNameOp hFrameOp hPromote
  have hNameOp' :
      Locals.StackOp.dup? (pending.length + 1) = some nameOp := by
    simpa [hAboveLength] using hNameOp
  have hFrameOp' :
      Locals.StackOp.dup?
          ((pending.length + 1) + frameDepth + 2) =
        some frameOp := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFrameOp
  have hPromote' :
      Locals.Ctx.swapRestoreUpTo? pending.length =
        some promoteCode := by
    simpa [hAboveLength] using hPromote
  obtain
      ⟨written, promoted, final, hStoreRun, hPromoteRun,
        hPopRun, _hWholeRun, hFinalRel⟩ :=
    scratch_step_code hRel hWF hFresh hLocation hStackOrder hSlot
      hReservation hNameOp' hFrameOp' hPromote'
  let compiled : Expressions.Block :=
    { stmts :=
        [ Expressions.Stmt.code
            ([Structured.BasicInstr.op nameOp] ++
              [ Structured.BasicInstr.op frameOp,
                Structured.BasicInstr.push
                  (AllocationSupport.slotOffset slot),
                Structured.BasicInstr.op .add,
                Structured.BasicInstr.op .mstore ]),
          Expressions.Stmt.code promoteCode,
          Expressions.Stmt.code [Structured.BasicInstr.op .pop] ] }
  refine
    ⟨compiled.stmts, final, by simpa [compiled] using hCompile, ?_,
      hFinalRel⟩
  change
    Structured.ObserverSemantics.Block.Eval targetProgram 4
      { stmts :=
          [ Structured.Stmt.code
              ([Structured.BasicInstr.op nameOp] ++
                [ Structured.BasicInstr.op frameOp,
                  Structured.BasicInstr.push
                    (AllocationSupport.slotOffset slot),
                  Structured.BasicInstr.op .add,
                  Structured.BasicInstr.op .mstore ]),
            Structured.Stmt.code promoteCode,
            Structured.Stmt.code [Structured.BasicInstr.op .pop] ] }
      target
      (Structured.EffectSemantics.Outcome.regular final)
  exact
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hStoreRun)
      (Structured.EffectSemantics.Block.Eval.cons_regular
        (Structured.EffectSemantics.Stmt.Eval.code hPromoteRun)
        (Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hPopRun)
          Structured.EffectSemantics.Block.Eval.nil))

/--
Execute and compile the complete real parameter prelude described by the
allocation-owned entry context.

This theorem is recursive over `lowerParams` itself. Its context remains an
internal compiler invariant; the whole-function boundary must construct that
context from the mixed-allocation plan and successful lowering.
-/
theorem forward_of_context
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Structured.Program}
    {realized : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hContext :
      AllocationObserverContext.ParameterPreludeContext
        lowerCtx plan frameWords realized pending frameDepth localsCtx)
    (hRel :
      AllocationObserverRelation.CalleeEntryRel contract plan realized
        pending frameBase frameDepth frameWords source target)
    (hWF : plan.WellFormed)
    (hReservation : contract.scratch? = some reservation) :
    ∃ compiled finalCtx finalTarget finalFrameDepth fuel,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerParams lowerCtx pending
          localsCtx.layout).2 ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ScratchStateRel contract plan
        ((pending.map Prod.fst).reverse ++ realized) 0 frameBase
        finalFrameDepth frameWords source finalTarget := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, frameDepth, 1, ?_, ?_, ?_, ?_⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel.finish
  | @stack _ _ _ _ name slot planDepth classification fresh location
      stackOrder tail =>
      have hNextRel :=
        hRel.activate_stack fresh location stackOrder
      obtain
          ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel,
            hCompile, hFinalLayout, hEval, hFinalRel⟩ :=
        forward_of_context tail hNextRel hWF hReservation
      refine
        ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel,
          ?_, ?_, hEval, ?_⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
  | @scratch _ pending _ localsCtx name slot classification fresh location
      stackOrder slotBound layout aboveFresh suffixFresh nameDepthBound
      frameDepthLookup frameDepthBound tail =>
      let above : Locals.Layout :=
        (pending.map Prod.fst).reverse
      let suffix : Locals.Layout :=
        AllocationObserverRelation.currentStackOrder plan
            (name :: realized) ++
          [lowerCtx.frameName]
      have hLayout :
          localsCtx.layout = above ++ name :: suffix := by
        simpa [above, suffix, stackOrder] using layout
      have hSuffixFresh : name ∉ suffix := by
        simpa [suffix, stackOrder] using suffixFresh
      have hFrameDepthLookup :
          Locals.Layout.lookupDepth? lowerCtx.frameName
              (above ++ name :: suffix) =
            some ((pending.length + 1) + frameDepth + 1) := by
        simpa [above, suffix, stackOrder] using frameDepthLookup
      obtain
          ⟨headCompiled, midTarget, hHeadCompile, hHeadEval, hNextRel⟩ :=
        scratch_step_of_lowerScratchParam
          (contract := contract) (transcript := transcript)
          (plan := plan) (realized := realized) (pending := pending)
          (frameBase := frameBase) (frameDepth := frameDepth)
          (frameWords := frameWords) (slot := slot)
          (source := source) (target := target)
          (name := name) (ctx := lowerCtx) (localsCtx := localsCtx)
          (above := above) (suffix := suffix)
          (targetProgram := targetProgram) (reservation := reservation)
          hRel hWF fresh location stackOrder slotBound hReservation
          hLayout (by simp [above]) (by simpa [above] using aboveFresh)
          hSuffixFresh (by simpa [above] using nameDepthBound)
          hFrameDepthLookup frameDepthBound
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel⟩ :=
        forward_of_context tail hNextRel hWF hReservation
      have hHeadCompile' :
          Locals.Block.compileOpen localsCtx
              { stmts :=
                  (AllocationLowering.lowerScratchParam lowerCtx name slot
                    localsCtx.layout).1 } =
            some
              (headCompiled,
                localsCtx.withLayout (above ++ suffix)) := by
        simpa [hLayout] using hHeadCompile
      have hTailCompile' :
          Locals.Block.compileOpen
              (localsCtx.withLayout (above ++ suffix))
              { stmts :=
                  (AllocationLowering.lowerParams lowerCtx pending
                    (above ++ suffix)).1 } =
            some (tailCompiled, finalCtx) := by
        simpa [above, suffix, List.append_assoc] using hTailCompile
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile' hTailCompile'
      obtain ⟨fuel, hCombinedEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hHeadEval hTailEval
      have hErase :
          AllocationLowering.eraseName name
              (above ++ name :: suffix) =
            above ++ suffix :=
        AllocationLowering.eraseName_append_name aboveFresh hSuffixFresh
      refine
        ⟨headCompiled ++ tailCompiled, finalCtx, finalTarget,
          finalFrameDepth, fuel, ?_, ?_, ?_, ?_⟩
      · simpa [AllocationLowering.lowerParams, classification, hLayout,
          AllocationLowering.lowerScratchParam, hErase] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerParams, classification, hLayout,
          AllocationLowering.lowerScratchParam, hErase] using
          hFinalLayout
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  (headCompiled ++ tailCompiled) }
            target
            (Structured.EffectSemantics.Outcome.regular finalTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
termination_by pending.length

end ParameterPrelude

namespace ArgList

/--
Forward preservation for the actual list representation used by Functions
calls. Each source argument is lowered by `lowerExprList`, compiled as the
corresponding `exprSeqOfList`, and discharged by the shared expression theorem.
-/
theorem forward
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        AllocationObserverExpression.ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationExprResultRel
          contract plan live stackOffset frameBase args.length mode
          sourceFinal target targetFinal values := by
  induction hSafe generalizing lowered code stackOffset target with
  | nil =>
      have hLowered : lowered = [] := by
        simpa [AllocationLowering.lowerExprList] using hLower.symm
      subst lowered
      have hCode : code = [] := by
        simpa [AllocationLowering.exprSeqOfList,
          Locals.ExprSeq.compileCode] using hCompile.symm
      subst code
      exact
        ⟨target, rfl,
          AllocationObserverRelation.ActivationExprResultRel.nil hRel⟩
  | @cons arg rest source afterArg final value values hArg hRest ih =>
      cases hLowerArg :
          AllocationLowering.lowerExpr lowerCtx lowerState arg with
      | none =>
          simp [AllocationLowering.lowerExprList, hLowerArg] at hLower
      | some loweredArg =>
          cases hLowerRest :
              AllocationLowering.lowerExprList lowerCtx lowerState rest with
          | none =>
              simp [AllocationLowering.lowerExprList, hLowerArg,
                hLowerRest] at hLower
          | some loweredRest =>
              have hLowered :
                  lowered = loweredArg :: loweredRest := by
                simpa [AllocationLowering.lowerExprList, hLowerArg,
                  hLowerRest] using hLower.symm
              subst lowered
              rw [AllocationLowering.exprSeqOfList_compileCode_cons] at hCompile
              cases hArgCode :
                  Locals.Expr.compileCode localsCtx stackOffset loweredArg with
              | none =>
                  simp [hArgCode] at hCompile
              | some argCode =>
                  cases hRestCode :
                      Locals.ExprSeq.compileCode localsCtx (stackOffset + 1)
                        (AllocationLowering.exprSeqOfList loweredRest) with
                  | none =>
                      simp [hArgCode, hRestCode] at hCompile
                  | some restCode =>
                      have hCode : code = argCode ++ restCode := by
                        simpa [hArgCode, hRestCode] using hCompile.symm
                      subst code
                      have hArgScoped :
                          Functions.Scope.ExprScoped live arg :=
                        hScoped arg (by simp)
                      have hRestScoped :
                          ∀ candidate, candidate ∈ rest →
                            Functions.Scope.ExprScoped live candidate := by
                        intro candidate hMember
                        exact hScoped candidate (by simp [hMember])
                      obtain ⟨targetAfterArg, hArgRun, hArgRel⟩ :=
                        AllocationObserverExpression.forwardExpr hPrimitive
                          hArg hCtx hArgScoped hLowerArg hArgCode hRel
                      obtain ⟨targetFinal, hRestRun, hRestRel⟩ :=
                        ih hRestScoped hLowerRest hRestCode hArgRel.state
                      refine ⟨targetFinal, ?_, ?_⟩
                      · rw [
                          AllocationObserverPreservation.ObserverCode.run_append,
                          hArgRun]
                        exact hRestRun
                      · simpa [Nat.add_comm] using
                          AllocationObserverRelation.ActivationExprResultRel.append
                            hArgRel hRestRel

/--
Deterministic target execution reflects the same canonical safe source
argument evaluation and result relation computed by `forward`.
-/
theorem backward_of_safeEval
    {contract : MemoryContract.Contract}
    (hPrimitive :
      ∀ op : Structured.BasicOp,
        AllocationObserverExpression.ActivationPrimitiveForward contract op)
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {args : List (Functions.Expr 1)}
    {lowered : List (Locals.Expr 1)}
    {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.ArgList.MemorySafeEval
        contract transcript args source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg)
    (hLower :
      AllocationLowering.lowerExprList lowerCtx lowerState args =
        some lowered)
    (hCompile :
      Locals.ExprSeq.compileCode localsCtx stackOffset
          (AllocationLowering.exprSeqOfList lowered) =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hRun :
      Structured.ObserverSemantics.Code.run code target =
        .ok targetFinal) :
    Functions.Source.Effectful.ArgList.eval
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        args source =
      .ok (sourceFinal, values) ∧
    AllocationObserverRelation.ActivationExprResultRel
      contract plan live stackOffset frameBase args.length mode
      sourceFinal target targetFinal values := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    forward hPrimitive hSafe hCtx hScoped hLower hCompile hRel
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hSafe.eval_eq, hExpectedRel⟩

end ArgList

end AllocationObserverCall
end Functions
end EvmCompiler
