import EvmCompiler.Functions.AllocationObserverExpression

namespace EvmCompiler
namespace Functions
namespace AllocationObserverCall

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

open AllocationObserverRelation

namespace CalleeEntry

/--
The exact target state constructed by Structured call semantics after argument
splitting and before procedure-body execution.
-/
def structuredState {transcript : Trace}
    (target : Structured.ObserverSemantics.State transcript)
    (args callerStack : EvmYul.Stack Word) (retc : Nat) :
    Structured.ObserverSemantics.State transcript :=
  (Structured.ObserverSemantics.stateModel transcript).pushReturn
    ((Structured.ObserverSemantics.stateModel transcript).withEVM target
      { target.source.evm with stack := args })
    callerStack retc

/--
Argument evaluation followed by the actual Structured call-frame construction
establishes the transient entry relation for an all-stack callee.
-/
theorem stack_of_arguments
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {callerPlan calleePlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase calleeFrameBase : Nat}
    {callerMode : AllocationObserverRelation.ActivationMode}
    {pending : List (Locals.Name × Nat)}
    {sourceAfterArgs : Functions.ObserverSemantics.State transcript}
    {targetInitial targetAfterArgs :
      Structured.ObserverSemantics.State transcript}
    {args : List Word}
    {initialStore : Locals.Source.Store}
    {callerStack : EvmYul.Stack Word}
    {retc : Nat}
    (hArgs :
      AllocationObserverRelation.ActivationExprResultRel
        contract callerPlan callerLive 0 callerFrameBase args.length
        callerMode sourceAfterArgs targetInitial targetAfterArgs args)
    (hLookup :
      Functions.Source.Store.lookupMany
          (pending.map Prod.fst) initialStore =
        some args) :
    AllocationObserverRelation.ActivationCalleeEntryRel
      contract calleePlan [] pending calleeFrameBase .stack
      ((Functions.ObserverSemantics.stateModel transcript).withSource
        sourceAfterArgs
        { shared := sourceAfterArgs.source.shared
          vars := initialStore })
      (structuredState targetAfterArgs args.reverse callerStack retc) := by
  have hBase := hArgs.state.base
  apply AllocationObserverRelation.ActivationCalleeEntryRel.stack_empty
      (values := args) (suffix := [])
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.pushReturn] using hBase.cursor
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Simulation.ResourceReplay.State.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hBase.core.machine
  · simpa [structuredState, Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource,
      Simulation.ResourceReplay.State.withSource,
      Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hBase.core.world
  · simpa [structuredState, Structured.ObserverSemantics.stateModel,
      Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hArgs.state.activeNoWrap
  · simpa [Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.stateModel,
      Locals.Source.Effectful.StateModel.withSource] using hLookup
  · simp [structuredState, Structured.ObserverSemantics.stateModel,
      Structured.EffectSemantics.StateModel.withEVM,
      Structured.RunState.withEVM, Structured.RunState.pushReturn]

end CalleeEntry

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
  exact AllocationLowering.entryMarkers_compileOpen

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
        source final ∧
      final.source.evm.stack.length + 1 =
        target.source.evm.stack.length := by
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
      hPopRun, ?_, hFinalRel, ?_⟩
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
  · exact hPopRun
  · rw [hFinalStack, hTargetStack]
    simp only [List.length_append, List.length_reverse,
      List.length_cons, hValuesLength]
    omega

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
        source final ∧
      final.source.evm.stack.length + 1 =
        target.source.evm.stack.length := by
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
        hPopRun, _hWholeRun, hFinalRel, hStackLength⟩ :=
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
      hFinalRel, hStackLength⟩
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
    (hFrameDepth :
      frameDepth =
        (AllocationObserverRelation.currentStackOrder plan realized).length)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length)
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
        finalFrameDepth frameWords source finalTarget ∧
      finalFrameDepth =
        (AllocationObserverRelation.currentStackOrder plan
          ((pending.map Prod.fst).reverse ++ realized)).length ∧
      finalTarget.source.evm.stack.length = finalCtx.layout.length := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, frameDepth, 1,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel.finish
      · simpa using hFrameDepth
      · exact hStackLength
  | @stack _ _ _ _ name slot planDepth classification fresh location
      stackOrder tail =>
      have hNextRel :=
        hRel.activate_stack fresh location stackOrder
      obtain
          ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel,
            hCompile, hFinalLayout, hEval, hFinalRel, hFinalDepth,
            hFinalStackLength⟩ :=
        forward_of_context tail hNextRel
          (by
            rw [stackOrder, hFrameDepth]
            simp)
          hStackLength hWF hReservation
      refine
        ⟨compiled, finalCtx, finalTarget, finalFrameDepth, fuel,
          ?_, ?_, hEval, ?_, ?_, ?_⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hFinalStackLength
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
          ⟨headCompiled, midTarget, hHeadCompile, hHeadEval, hNextRel,
            hStepLength⟩ :=
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
      have hMidStackLength :
          midTarget.source.evm.stack.length =
            (localsCtx.withLayout (above ++ suffix)).layout.length := by
        simp only [Locals.Ctx.withLayout]
        have hInitialLength :
            target.source.evm.stack.length =
              (above ++ name :: suffix).length := by
          rw [hStackLength, hLayout]
        simp only [List.length_append, List.length_cons] at hInitialLength
        simp only [List.length_append]
        omega
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel,
            hFinalDepth, hFinalStackLength⟩ :=
        forward_of_context tail hNextRel
          (by simpa [stackOrder] using hFrameDepth)
          (by
            simpa [above, suffix, List.append_assoc] using hMidStackLength)
          hWF hReservation
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
          finalFrameDepth, fuel, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hFinalStackLength
termination_by pending.length

/--
Compile and evaluate the complete parameter prelude for an all-stack
activation.

The compiler emits no executable parameter code in this branch. The proof
still follows the real `lowerParams` recursion and derives each live-local
activation from the raw entry stack.
-/
theorem forward_stack_of_context
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
    (hContext :
      AllocationObserverContext.ParameterPreludeContext
        lowerCtx plan frameWords realized pending frameDepth localsCtx)
    (hAllStack :
      ∀ binding ∈ pending,
        AllocationLowering.isStackSlot lowerCtx binding.2 = true)
    (hRel :
      AllocationObserverRelation.ActivationCalleeEntryRel contract plan
        realized pending frameBase .stack source target)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length) :
    ∃ compiled finalCtx finalTarget fuel,
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
      AllocationObserverRelation.ActivationStateRel contract plan
        ((pending.map Prod.fst).reverse ++ realized) 0 frameBase
        .stack source finalTarget ∧
      finalTarget.source.evm.stack.length = finalCtx.layout.length := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, 1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [AllocationLowering.lowerParams, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerParams]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel.finish
      · exact hStackLength
  | @stack _ _ _ _ name slot planDepth classification fresh location
      stackOrder tail =>
      have hNextRel := by
        simpa [AllocationObserverRelation.ActivationMode.afterStackDeclaration]
          using hRel.activate_stack fresh location stackOrder
      obtain
          ⟨compiled, finalCtx, finalTarget, fuel,
            hCompile, hFinalLayout, hEval, hFinalRel,
            hFinalStackLength⟩ :=
        forward_stack_of_context tail
          (fun binding hBinding =>
            hAllStack binding (by simp [hBinding]))
          hNextRel hStackLength
      refine
        ⟨compiled, finalCtx, finalTarget, fuel,
          ?_, ?_, hEval, ?_, ?_⟩
      · simpa [AllocationLowering.lowerParams, classification] using hCompile
      · simpa [AllocationLowering.lowerParams, classification] using
          hFinalLayout
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · exact hFinalStackLength
  | @scratch _ pending _ _ name slot classification _fresh _location
      _stackOrder _slotBound _layout _aboveFresh _suffixFresh
      _nameDepthBound _frameDepthLookup _frameDepthBound _tail =>
      have hCurrent :=
        hAllStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

end ParameterPrelude

namespace ReturnPrelude

/--
Compile and execute the complete real return-initialization prelude.

The source function store already contains zero for every named return, so the
compiler-only declarations and frame stores preserve the source state while
establishing the ordinary allocation relation for all returns.
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
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    {reservation : MemoryContract.ScratchReservation}
    (hContext :
      AllocationObserverContext.ReturnPreludeContext
        lowerCtx plan frameWords live pending frameDepth localsCtx)
    (hRel :
      AllocationObserverRelation.ScratchStateRel contract plan live 0
        frameBase frameDepth frameWords source target)
    (hZero :
      ∀ name, name ∈ pending.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hFrameDepth :
      frameDepth =
        (AllocationObserverRelation.currentStackOrder plan live).length)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length)
    (hWF : plan.WellFormed)
    (hReservation : contract.scratch? = some reservation) :
    ∃ compiled finalCtx finalTarget finalFrameDepth fuel,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerReturns lowerCtx pending
          localsCtx.layout).2 ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ScratchStateRel contract plan
        ((pending.map Prod.fst).reverse ++ live) 0 frameBase
        finalFrameDepth frameWords source finalTarget ∧
      finalFrameDepth =
        (AllocationObserverRelation.currentStackOrder plan
          ((pending.map Prod.fst).reverse ++ live)).length ∧
      finalTarget.source.evm.stack.length = finalCtx.layout.length := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, frameDepth, 1,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [AllocationLowering.lowerReturns, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerReturns]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel
      · simpa using hFrameDepth
      · exact hStackLength
  | @stack _ pending _ planDepth _ name slot classification fresh location
      stackOrder tail =>
      let pushed :=
        AllocationObserverRelation.StateRel.pushTargetBy
          33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.ObserverSemantics.Code.run
              [Structured.BasicInstr.push AllocationSupport.zeroWord]
              target =
            .ok pushed :=
        AllocationObserverPreservation.ObserverCode.run_push
          AllocationSupport.zeroWord target
      have hPushedRel :
          AllocationObserverRelation.ScratchStateRel contract plan live 1
            frameBase frameDepth frameWords source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.source.evm.stack =
            AllocationSupport.zeroWord :: target.source.evm.stack := by
        rfl
      have hNameZero :
          source.source.vars name =
            some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          AllocationObserverRelation.ScratchStateRel contract plan
            (name :: live) 0 frameBase (frameDepth + 1) frameWords
            source pushed :=
        hPushedRel.declare_stack_live_existing hPushedStack
          (fun other hOther => by
            simp at hOther
            exact hOther)
            (by simp) location stackOrder hNameZero
      have hNextStackLength :
          pushed.source.evm.stack.length =
            (localsCtx.withLayout
              (name :: localsCtx.layout)).layout.length := by
        rw [hPushedStack]
        simp [Locals.Ctx.withLayout, hStackLength]
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel,
            hFinalDepth, hFinalStackLength⟩ :=
        forward_of_context tail hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          (by
            rw [stackOrder, hFrameDepth]
            simp)
          hNextStackLength hWF hReservation
      have hHeadCompile :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      have hHeadRun :
          Structured.ObserverSemantics.Code.run
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                Locals.bindLocals 0 (name :: localsCtx.layout))
              target =
            .ok pushed := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hPushRun]
        rfl
      have hHeadEval :
          Structured.ObserverSemantics.Block.Eval targetProgram 2
              { stmts :=
                  [Structured.Stmt.code
                    ([Structured.BasicInstr.push
                        AllocationSupport.zeroWord] ++
                      Locals.bindLocals 0
                        (name :: localsCtx.layout))] }
              target
              (Structured.EffectSemantics.Outcome.regular pushed) :=
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hHeadRun)
          Structured.EffectSemantics.Block.Eval.nil
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      obtain ⟨fuel, hCombinedEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hHeadEval hTailEval
      refine
        ⟨[Expressions.Stmt.code
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                Locals.bindLocals 0 (name :: localsCtx.layout))] ++
            tailCompiled,
          finalCtx, finalTarget, finalFrameDepth, fuel,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [AllocationLowering.lowerReturns, classification] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  ([Expressions.Stmt.code
                      ([Structured.BasicInstr.push
                          AllocationSupport.zeroWord] ++
                        Locals.bindLocals 0
                          (name :: localsCtx.layout))] ++
                    tailCompiled) }
            target
            (Structured.EffectSemantics.Outcome.regular finalTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hFinalStackLength
  | @scratch _ pending _ _ name slot classification fresh location
      stackOrder slotBound frameDepthLookup frameDepthBound tail =>
      obtain ⟨frameOp, hFrameOp⟩ :=
        Locals.StackOp.exists_dup?_of_pos_of_le
          (depth := 1 + (frameDepth + 1)) (by omega) frameDepthBound
      let pushed :=
        AllocationObserverRelation.StateRel.pushTargetBy
          33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.ObserverSemantics.Code.run
              [Structured.BasicInstr.push AllocationSupport.zeroWord]
              target =
            .ok pushed :=
        AllocationObserverPreservation.ObserverCode.run_push
          AllocationSupport.zeroWord target
      have hPushedRel :
          AllocationObserverRelation.ScratchStateRel contract plan live 1
            frameBase frameDepth frameWords source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.source.evm.stack =
            AllocationSupport.zeroWord :: target.source.evm.stack := by
        rfl
      have hRegion :
          reservation.containsRegion
            (AllocationObserverRelation.scratchAddress frameBase slot) 1 :=
        hRel.scratchAddress_reserved_of_bound slotBound hReservation
      obtain ⟨midTarget, hStoreRun, hStoredRel, hStoredStack⟩ :=
        AllocationObserverPreservation.Expr.scratchAssignTop_forward_live
          (stackOffset := 0) hPushedRel hPushedStack hWF
          (fun other hOther => by
            simp at hOther
            exact hOther)
          stackOrder (by simp) location slotBound hReservation hRegion
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hFrameOp)
      have hNameZero :
          source.source.vars name =
            some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          AllocationObserverRelation.ScratchStateRel contract plan
            (name :: live) 0 frameBase frameDepth frameWords
            source midTarget := by
        have hInsert :
            source.source.insert name AllocationSupport.zeroWord =
              source.source :=
          Locals.Source.State.insert_eq_of_apply_eq hNameZero
        simpa [hInsert] using hStoredRel
      have hNextStackLength :
          midTarget.source.evm.stack.length = localsCtx.layout.length := by
        rw [hStoredStack]
        exact hStackLength
      obtain
          ⟨tailCompiled, finalCtx, finalTarget, finalFrameDepth,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel,
            hFinalDepth, hFinalStackLength⟩ :=
        forward_of_context tail hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          (by simpa [stackOrder] using hFrameDepth)
          hNextStackLength hWF hReservation
      have hHeadCompile :=
        AllocationLowering.lowerScratchReturn_compileOpen
          (ctx := lowerCtx) (name := name) (slot := slot)
          (frameDepth := frameDepth + 1) (localsCtx := localsCtx)
          (frameOp := frameOp) frameDepthLookup hFrameOp
      have hHeadRun :
          Structured.ObserverSemantics.Code.run
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                [ Structured.BasicInstr.op frameOp,
                  Structured.BasicInstr.push
                    (AllocationSupport.slotOffset slot),
                  Structured.BasicInstr.op .add,
                  Structured.BasicInstr.op .mstore ])
              target =
            .ok midTarget := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hPushRun]
        exact hStoreRun
      have hHeadEval :
          Structured.ObserverSemantics.Block.Eval targetProgram 2
              { stmts :=
                  [Structured.Stmt.code
                    ([Structured.BasicInstr.push
                        AllocationSupport.zeroWord] ++
                      [ Structured.BasicInstr.op frameOp,
                        Structured.BasicInstr.push
                          (AllocationSupport.slotOffset slot),
                        Structured.BasicInstr.op .add,
                        Structured.BasicInstr.op .mstore ])] }
              target
              (Structured.EffectSemantics.Outcome.regular midTarget) :=
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hHeadRun)
          Structured.EffectSemantics.Block.Eval.nil
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      obtain ⟨fuel, hCombinedEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hHeadEval hTailEval
      refine
        ⟨[Expressions.Stmt.code
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                [ Structured.BasicInstr.op frameOp,
                  Structured.BasicInstr.push
                    (AllocationSupport.slotOffset slot),
                  Structured.BasicInstr.op .add,
                  Structured.BasicInstr.op .mstore ])] ++
            tailCompiled,
          finalCtx, finalTarget, finalFrameDepth, fuel,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [AllocationLowering.lowerReturns, classification] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  ([Expressions.Stmt.code
                      ([Structured.BasicInstr.push
                          AllocationSupport.zeroWord] ++
                        [ Structured.BasicInstr.op frameOp,
                          Structured.BasicInstr.push
                            (AllocationSupport.slotOffset slot),
                          Structured.BasicInstr.op .add,
                          Structured.BasicInstr.op .mstore ])] ++
                    tailCompiled) }
            target
            (Structured.EffectSemantics.Outcome.regular finalTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · simpa [List.reverse_cons, List.append_assoc] using hFinalDepth
      · exact hFinalStackLength
termination_by pending.length

/--
Compile and execute the complete return-initialization prelude for an
all-stack activation.
-/
theorem forward_stack_of_context
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {frameBase frameWords : Nat}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {lowerCtx : AllocationLowering.Ctx}
    {localsCtx : Locals.Ctx}
    {targetProgram : Structured.Program}
    {live : List Locals.Name}
    {pending : List (Locals.Name × Nat)}
    {frameDepth : Nat}
    (hContext :
      AllocationObserverContext.ReturnPreludeContext
        lowerCtx plan frameWords live pending frameDepth localsCtx)
    (hAllStack :
      ∀ binding ∈ pending,
        AllocationLowering.isStackSlot lowerCtx binding.2 = true)
    (hRel :
      AllocationObserverRelation.ActivationStateRel contract plan live 0
        frameBase .stack source target)
    (hZero :
      ∀ name, name ∈ pending.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length) :
    ∃ compiled finalCtx finalTarget fuel,
      Locals.Block.compileOpen localsCtx
          { stmts :=
              (AllocationLowering.lowerReturns lowerCtx pending
                localsCtx.layout).1 } =
        some (compiled, finalCtx) ∧
      finalCtx.layout =
        (AllocationLowering.lowerReturns lowerCtx pending
          localsCtx.layout).2 ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ActivationStateRel contract plan
        ((pending.map Prod.fst).reverse ++ live) 0 frameBase
        .stack source finalTarget ∧
      finalTarget.source.evm.stack.length = finalCtx.layout.length := by
  cases hContext with
  | nil =>
      refine
        ⟨[], localsCtx, target, 1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [AllocationLowering.lowerReturns, Locals.Block.compileOpen]
      · simp [AllocationLowering.lowerReturns]
      · exact Structured.EffectSemantics.Block.Eval.nil
      · simpa using hRel
      · exact hStackLength
  | @stack _ pending _ planDepth _ name slot classification fresh location
      stackOrder tail =>
      let pushed :=
        AllocationObserverRelation.StateRel.pushTargetBy
          33 AllocationSupport.zeroWord target
      have hPushRun :
          Structured.ObserverSemantics.Code.run
              [Structured.BasicInstr.push AllocationSupport.zeroWord]
              target =
            .ok pushed :=
        AllocationObserverPreservation.ObserverCode.run_push
          AllocationSupport.zeroWord target
      have hPushedRel :
          AllocationObserverRelation.ActivationStateRel contract plan live 1
            frameBase .stack source pushed := by
        simpa [pushed] using
          hRel.push_target_by 33 AllocationSupport.zeroWord
      have hPushedStack :
          pushed.source.evm.stack =
            AllocationSupport.zeroWord :: target.source.evm.stack := by
        rfl
      have hNameZero :
          source.source.vars name =
            some AllocationSupport.zeroWord :=
        hZero name (by simp)
      have hNextRel :
          AllocationObserverRelation.ActivationStateRel contract plan
            (name :: live) 0 frameBase .stack source pushed := by
        simpa [AllocationObserverRelation.ActivationMode.afterStackDeclaration]
          using hPushedRel.declare_stack_live_existing hPushedStack
            (fun other hOther => by
              simp at hOther
              exact hOther)
            (by simp) location stackOrder hNameZero
      have hNextStackLength :
          pushed.source.evm.stack.length =
            (localsCtx.withLayout
              (name :: localsCtx.layout)).layout.length := by
        rw [hPushedStack]
        simp [Locals.Ctx.withLayout, hStackLength]
      obtain
          ⟨tailCompiled, finalCtx, finalTarget,
            tailFuel, hTailCompile, hFinalLayout, hTailEval, hFinalRel,
            hFinalStackLength⟩ :=
        forward_stack_of_context tail
          (fun binding hBinding =>
            hAllStack binding (by simp [hBinding]))
          hNextRel
          (fun other hOther => hZero other (by simp [hOther]))
          hNextStackLength
      have hHeadCompile :=
        AllocationLowering.lowerStackReturn_compileOpen
          (name := name) (localsCtx := localsCtx)
      have hHeadRun :
          Structured.ObserverSemantics.Code.run
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                Locals.bindLocals 0 (name :: localsCtx.layout))
              target =
            .ok pushed := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hPushRun]
        rfl
      have hHeadEval :
          Structured.ObserverSemantics.Block.Eval targetProgram 2
              { stmts :=
                  [Structured.Stmt.code
                    ([Structured.BasicInstr.push
                        AllocationSupport.zeroWord] ++
                      Locals.bindLocals 0
                        (name :: localsCtx.layout))] }
              target
              (Structured.EffectSemantics.Outcome.regular pushed) :=
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hHeadRun)
          Structured.EffectSemantics.Block.Eval.nil
      have hCombinedCompile :=
        Locals.Block.compileOpen_append hHeadCompile hTailCompile
      obtain ⟨fuel, hCombinedEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hHeadEval hTailEval
      refine
        ⟨[Expressions.Stmt.code
              ([Structured.BasicInstr.push AllocationSupport.zeroWord] ++
                Locals.bindLocals 0 (name :: localsCtx.layout))] ++
            tailCompiled,
          finalCtx, finalTarget, fuel, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [AllocationLowering.lowerReturns, classification] using
          hCombinedCompile
      · simpa [AllocationLowering.lowerReturns, classification] using
          hFinalLayout
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  ([Expressions.Stmt.code
                      ([Structured.BasicInstr.push
                          AllocationSupport.zeroWord] ++
                        Locals.bindLocals 0
                          (name :: localsCtx.layout))] ++
                    tailCompiled) }
            target
            (Structured.EffectSemantics.Outcome.regular finalTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hCombinedEval
      · simpa [List.reverse_cons, List.append_assoc] using hFinalRel
      · exact hFinalStackLength
  | @scratch _ pending _ _ name slot classification _fresh _location
      _stackOrder _slotBound _frameDepthLookup _frameDepthBound _tail =>
      have hCurrent :=
        hAllStack (name, slot) (by simp)
      rw [classification] at hCurrent
      contradiction
termination_by pending.length

end ReturnPrelude

namespace FunctionPrelude

/--
Scratch authorization is required exactly for frame-backed activations.
-/
def ScratchAuthorized
    (contract : MemoryContract.Contract) :
    AllocationObserverRelation.ActivationMode → Prop
  | .stack => True
  | .scratch _frameDepth _frameWords =>
      ∃ reservation,
        contract.scratch? = some reservation

/--
The canonical Functions function-entry store supplies every source-facing
premise required by the allocation prelude: parameters retain the argument
values, returns are initialized to zero, and the complete body scope is
defined.
-/
theorem initialized_source_facts
    {transcript : Trace}
    {params returns : List Functions.Name}
    {args : List Word}
    {paramStore : Locals.Source.Store}
    {source : Functions.ObserverSemantics.State transcript}
    (hSignature : (returns ++ params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany params args
          Locals.Source.Store.empty =
        some paramStore)
    (hVars :
      source.source.vars =
        Functions.Source.Store.initReturns returns paramStore) :
    Functions.Source.Store.lookupMany params source.source.vars =
        some args ∧
      (∀ name, name ∈ returns →
        source.source.vars name = some AllocationSupport.zeroWord) ∧
      AllocationObserverRelation.LiveDefined
        (returns.reverse ++ params.reverse) source.source := by
  obtain ⟨hParams, hReturns⟩ :=
    Functions.Source.Store.initializedStore_lookupMany
      hSignature hInsert
  have hReturnNodup := (List.nodup_append.mp hSignature).1
  have hParams' :
      Functions.Source.Store.lookupMany params source.source.vars =
        some args := by
    simpa [hVars] using hParams
  have hReturns' :
      Functions.Source.Store.lookupMany returns source.source.vars =
        some (returns.map fun _name => AllocationSupport.zeroWord) := by
    simpa [hVars] using hReturns
  refine ⟨hParams', ?_, ?_⟩
  · intro name hName
    rw [hVars]
    exact
      Functions.Source.Store.initReturns_apply_of_mem
        hReturnNodup hName
  · exact
      (AllocationObserverRelation.LiveDefined.of_lookupMany
          (Functions.Source.Store.lookupMany_reverse hReturns')).append
        (AllocationObserverRelation.LiveDefined.of_lookupMany
          (Functions.Source.Store.lookupMany_reverse hParams'))

/--
Compile and execute the complete parameter/return prelude selected by a
checked function compiler artifact.

No generated code is accepted from the caller: both compilation phases are
recovered from `FunctionPreludeContext`, which is constructed by the real
validator, Functions lowerer, and Locals compiler.
-/
theorem forward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan} {frameWords frameBase : Nat}
    {slots : AllocationSupport.FunSlots}
    {entryCtx paramCtx returnCtx : Locals.Ctx}
    {mode : AllocationObserverRelation.ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    (hContext :
      AllocationObserverContext.FunctionPreludeContext
        lowerCtx plan frameWords slots entryCtx paramCtx returnCtx mode)
    (hEntry :
      AllocationObserverRelation.ActivationCalleeEntryRel contract plan
        [] slots.params frameBase mode source target)
    (hEntryStackLength :
      target.source.evm.stack.length = entryCtx.layout.length)
    (hZero :
      ∀ name, name ∈ slots.returns.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hWF : plan.WellFormed)
    (hScratch : ScratchAuthorized contract mode) :
    ∃ compiled finalTarget fuel,
      Locals.Block.compileOpen entryCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx slots.params
                entryCtx.layout).1 ++
              (AllocationLowering.lowerReturns lowerCtx slots.returns
                paramCtx.layout).1 } =
        some (compiled, returnCtx) ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverRelation.ActivationStateRel contract plan
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        0 frameBase
        (mode.atStackDepth
          (AllocationObserverRelation.currentStackOrder plan
            ((slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse)).length)
        source finalTarget ∧
      finalTarget.source.evm.stack.length = returnCtx.layout.length ∧
      AllocationObserverRelation.SameFrame mode
        (mode.atStackDepth
          (AllocationObserverRelation.currentStackOrder plan
            ((slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse)).length) := by
  cases hContext with
  | stack parameterSlots returnSlots signatureNodup frameFresh
      parameters returns
      parameterCompile returnCompile entryLayout parameterLayout bodyLayout =>
      obtain ⟨paramExpected, hParamExpected⟩ := parameterCompile
      obtain
          ⟨paramCompiled, paramFinalCtx, paramTarget, paramFuel,
            hParamCompile, _hParamLayout, hParamEval, hParamRel,
            hParamStackLength⟩ :=
        ParameterPrelude.forward_stack_of_context
          parameters parameterSlots hEntry hEntryStackLength
      rw [hParamExpected] at hParamCompile
      cases hParamCompile
      have hParamRel' :
          AllocationObserverRelation.ActivationStateRel contract plan
            (slots.params.map Prod.fst).reverse 0 frameBase .stack
            source paramTarget := by
        simpa using hParamRel
      obtain ⟨returnExpected, hReturnExpected⟩ := returnCompile
      obtain
          ⟨returnCompiled, returnFinalCtx, returnTarget, returnFuel,
            hReturnCompile, _hReturnLayout, hReturnEval, hReturnRel,
            hReturnStackLength⟩ :=
        ReturnPrelude.forward_stack_of_context
          returns returnSlots hParamRel' hZero hParamStackLength
      rw [hReturnExpected] at hReturnCompile
      cases hReturnCompile
      have hCompile :=
        Locals.Block.compileOpen_append hParamExpected hReturnExpected
      obtain ⟨fuel, hEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hParamEval hReturnEval
      refine
        ⟨paramExpected ++ returnExpected, returnTarget, fuel,
          hCompile, ?_, ?_, hReturnStackLength,
          AllocationObserverRelation.SameFrame.stack⟩
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  (paramExpected ++ returnExpected) }
            target
            (Structured.EffectSemantics.Outcome.regular returnTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hEval
      · exact hReturnRel
  | scratch signatureNodup frameFresh parameters returns
      parameterCompile returnCompile
      entryLayout parameterLayout bodyLayout =>
      obtain ⟨reservation, hReservation⟩ := hScratch
      have hScratchEntry :=
        AllocationObserverRelation.ActivationCalleeEntryRel.to_scratch hEntry
      obtain ⟨paramExpected, hParamExpected⟩ := parameterCompile
      obtain
          ⟨paramCompiled, paramFinalCtx, paramTarget, paramFrameDepth,
            paramFuel, hParamCompile, _hParamLayout, hParamEval,
            hParamRel, hParamDepth, hParamStackLength⟩ :=
        ParameterPrelude.forward_of_context
          parameters hScratchEntry
            (by
              simp [AllocationObserverRelation.currentStackOrder])
            hEntryStackLength hWF hReservation
      rw [hParamExpected] at hParamCompile
      cases hParamCompile
      have hParamDepth' :
          paramFrameDepth =
            (AllocationObserverRelation.currentStackOrder plan
              (slots.params.map Prod.fst).reverse).length := by
        simpa using hParamDepth
      have hParamRel' :
          AllocationObserverRelation.ScratchStateRel contract plan
            (slots.params.map Prod.fst).reverse 0 frameBase
            paramFrameDepth frameWords source paramTarget := by
        simpa using hParamRel
      have hParamRelExact :
          AllocationObserverRelation.ScratchStateRel contract plan
            (slots.params.map Prod.fst).reverse 0 frameBase
            (AllocationObserverRelation.currentStackOrder plan
              (slots.params.map Prod.fst).reverse).length
            frameWords source paramTarget := by
        simpa [hParamDepth'] using hParamRel'
      obtain ⟨returnExpected, hReturnExpected⟩ := returnCompile
      obtain
          ⟨returnCompiled, returnFinalCtx, returnTarget, returnFrameDepth,
            returnFuel, hReturnCompile, _hReturnLayout, hReturnEval,
            hReturnRel, hReturnDepth, hReturnStackLength⟩ :=
        ReturnPrelude.forward_of_context
          returns hParamRelExact hZero rfl hParamStackLength
          hWF hReservation
      rw [hReturnExpected] at hReturnCompile
      cases hReturnCompile
      have hCompile :=
        Locals.Block.compileOpen_append hParamExpected hReturnExpected
      obtain ⟨fuel, hEval⟩ :=
        Structured.EffectSemantics.Block.Eval.append_regular_exists
          hParamEval hReturnEval
      refine
        ⟨paramExpected ++ returnExpected, returnTarget, fuel,
          hCompile, ?_, ?_, hReturnStackLength, ?_⟩
      · change
          Structured.ObserverSemantics.Block.Eval targetProgram fuel
            { stmts :=
                Expressions.StmtList.toStructured
                  (paramExpected ++ returnExpected) }
            target
            (Structured.EffectSemantics.Outcome.regular returnTarget)
        rw [Expressions.StmtList.toStructured_append]
        exact hEval
      · exact
          AllocationObserverRelation.ActivationStateRel.scratch
            (by simpa [hReturnDepth] using hReturnRel)
      · exact
          AllocationObserverRelation.SameFrame.scratch
            0
            (AllocationObserverRelation.currentStackOrder plan
              ((slots.returns.map Prod.fst).reverse ++
                (slots.params.map Prod.fst).reverse)).length
            frameWords

/--
Compile and execute the complete function prelude, then package its exact
post-state with the compiler-derived body context as the standard recursive
statement invariant.
-/
theorem forward_invariant
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {plan : Locals.Allocation.Plan} {frameWords frameBase : Nat}
    {slots : AllocationSupport.FunSlots}
    {entryCtx paramCtx returnCtx : Locals.Ctx}
    {mode : AllocationObserverRelation.ActivationMode}
    {bodyState : AllocationLowering.State}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    (hContext :
      AllocationObserverContext.FunctionPreludeContext
        lowerCtx plan frameWords slots entryCtx paramCtx returnCtx mode)
    (hEntry :
      AllocationObserverRelation.ActivationCalleeEntryRel contract plan
        [] slots.params frameBase mode source target)
    (hEntryStackLength :
      target.source.evm.stack.length = entryCtx.layout.length)
    (hZero :
      ∀ name, name ∈ slots.returns.map Prod.fst →
        source.source.vars name = some AllocationSupport.zeroWord)
    (hWF : plan.WellFormed)
    (hScratch : ScratchAuthorized contract mode)
    (hBodyEnv :
      bodyState.allocation.env =
        AllocationSupport.functionEnv slots)
    (hBodyLayout : bodyState.layout = returnCtx.layout)
    (hDefined :
      AllocationObserverRelation.LiveDefined
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        source.source) :
    ∃ compiled finalTarget fuel,
      Locals.Block.compileOpen entryCtx
          { stmts :=
              (AllocationLowering.lowerParams lowerCtx slots.params
                entryCtx.layout).1 ++
              (AllocationLowering.lowerReturns lowerCtx slots.returns
                paramCtx.layout).1 } =
        some (compiled, returnCtx) ∧
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
          (Expressions.Block.toStructured { stmts := compiled })
          target
          (Structured.EffectSemantics.Outcome.regular finalTarget) ∧
      AllocationObserverContext.ActivationInvariant
        contract lowerCtx bodyState returnCtx plan
        ((slots.returns.map Prod.fst).reverse ++
          (slots.params.map Prod.fst).reverse)
        frameBase
        (mode.atStackDepth
          (AllocationObserverRelation.currentStackOrder plan
            ((slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse)).length)
        source finalTarget ∧
      AllocationObserverRelation.SameFrame mode
        (mode.atStackDepth
          (AllocationObserverRelation.currentStackOrder plan
            ((slots.returns.map Prod.fst).reverse ++
              (slots.params.map Prod.fst).reverse)).length) := by
  obtain
      ⟨compiled, finalTarget, fuel, hCompile, hEval, hRel,
        hStackLength, hSameFrame⟩ :=
    forward hContext hEntry hEntryStackLength hZero hWF hScratch
  refine
    ⟨compiled, finalTarget, fuel, hCompile, hEval, ?_, hSameFrame⟩
  exact
    { compiler :=
        AllocationObserverContext.FunctionPreludeContext.bodyCompiler
          hContext hBodyEnv hBodyLayout hWF
      planWF := hWF
      defined := hDefined
      state := hRel
      stackLength := hStackLength }

end FunctionPrelude

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

namespace CallTargets

private theorem set_append_offset
    {α : Type} (above suffix : List α) (depth : Nat) (value : α) :
    (above ++ suffix).set (above.length + depth) value =
      above ++ suffix.set depth value := by
  induction above with
  | nil =>
      simp
  | cons head tail ih =>
      simp [Nat.succ_add, ih]

private theorem lookupDepth?_none_of_not_mem
    {name : Locals.Name} {layout : Locals.Layout}
    (hNotMem : name ∉ layout) :
    Locals.Layout.lookupDepth? name layout = none := by
  cases hLookup : Locals.Layout.lookupDepth? name layout with
  | none =>
      rfl
  | some depth =>
      exact False.elim
        (hNotMem (Locals.Layout.mem_of_lookupDepth?_eq_some hLookup))

private theorem stack_step
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase planDepth depth : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {layout : Locals.Layout}
    {name : Locals.Name} {value old : Word}
    {remaining rest : List Word}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {code : Structured.Code}
    (hCode :
      AllocationLowering.stackAssignTopCode?
          layout remaining.length name =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live (remaining.length + 1) frameBase mode
        source target)
    (hStack :
      target.source.evm.stack = value :: (remaining ++ rest))
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hDepth :
      Locals.Layout.lookupDepth? name
          (AllocationObserverRelation.currentStackOrder plan live) =
        some (depth + 1))
    (hCompileDepth :
      Locals.Layout.lookupDepth? name layout = some (depth + 1))
    (hDepthValid : mode.StackDepthValid depth)
    (hOld : source.source.vars name = some old) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live remaining.length frameBase mode
          (source.withSource (source.source.insert name value))
          targetFinal ∧
        targetFinal.source.evm.stack =
          remaining ++ rest.set depth value := by
  cases hSwap :
      Locals.StackOp.swap? (remaining.length + (depth + 1)) with
  | none =>
      simp [AllocationLowering.stackAssignTopCode?, hCompileDepth, hSwap]
        at hCode
  | some op =>
      simp [AllocationLowering.stackAssignTopCode?, hCompileDepth, hSwap]
        at hCode
      subst code
      have hOldTarget :=
        hRel.base.core.store.stack_at hLive hLocation hDepth
      rw [hStack, hOld] at hOldTarget
      have hRestGet :
          (remaining ++ rest)[remaining.length + depth]? = some old := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hOldTarget
      let targetFinal :=
        AllocationObserverRelation.StateRel.replaceStackBy 2
          ((remaining ++ rest).set (remaining.length + depth) value)
          target
      have hRun :
          Structured.ObserverSemantics.Code.run
              [.op op, .op .pop] target =
            .ok targetFinal := by
        simpa [targetFinal, Nat.add_assoc] using
          AllocationObserverPreservation.ObserverCode.run_swap_pop
            (by simpa [Nat.add_assoc] using hSwap)
            hRestGet hStack
      have hFinalRel :
          AllocationObserverRelation.ActivationStateRel
            contract plan live remaining.length frameBase mode
            (source.withSource (source.source.insert name value))
            targetFinal := by
        exact
          hRel.assign_stack_live_at hStack hLive hLocation hDepth
            hDepthValid hOld
      refine ⟨targetFinal, hRun, hFinalRel, ?_⟩
      simp [targetFinal,
        AllocationObserverRelation.StateRel.replaceStackBy,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, set_append_offset]

private theorem scratch_step
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase frameDepth frameWords slot : Nat}
    {name : Locals.Name} {value : Word}
    {remaining rest : List Word}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {code : Structured.Code}
    (hCode :
      AllocationLowering.scratchAssignTopCode?
          lowerCtx lowerState remaining.length slot =
        some code)
    (hRel :
      AllocationObserverRelation.ScratchStateRel
        contract plan live (remaining.length + 1) frameBase
        frameDepth frameWords source target)
    (hStack :
      target.source.evm.stack = value :: (remaining ++ rest))
    (hWF : plan.WellFormed)
    (hLive : name ∈ live)
    (hLocation : plan.location? name = some (.scratch slot))
    (hFrameDepth :
      Locals.Layout.lookupDepth? lowerCtx.frameName lowerState.layout =
        some (frameDepth + 1)) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live remaining.length frameBase
          (.scratch frameDepth frameWords)
          (source.withSource (source.source.insert name value))
          targetFinal ∧
        targetFinal.source.evm.stack = remaining ++ rest := by
  have hStoreCode :
      AllocationSupport.storeTopSlotCode?
          (remaining.length + frameDepth + 1) slot =
        some code := by
    simpa [AllocationLowering.scratchAssignTopCode?,
      AllocationLowering.frameDepth?, hFrameDepth, Nat.add_assoc] using hCode
  have hSlotBound :=
    hRel.scratchBound name slot hLive hLocation
  obtain ⟨reservation, hReservation, _hFrameRegion⟩ :=
    hRel.frameReserved
  have hRegion :=
    hRel.scratchAddress_reserved_of_bound hSlotBound hReservation
  obtain ⟨targetFinal, hRun, hFinalRel, hFinalStack⟩ :=
    AllocationObserverPreservation.Expr.scratchAssignTop_forward_of_storeTopSlotCode?_live
        hRel hStack hWF
        (fun other hOther => Or.inr hOther)
        rfl hLive hLocation hSlotBound hReservation hRegion hStoreCode
  exact ⟨targetFinal, hRun, .scratch hFinalRel, hFinalStack⟩

/--
Execute the actual code emitted for assigning returned call values to source
targets.

The compiler and source semantics both process the already-reversed target and
value lists from left to right. Each step consumes exactly one temporary stack
value, updates either a stack local or its allocated scratch slot, and leaves
the remaining return prefix intact for the recursive step.
-/
theorem forward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat}
    {mode : AllocationObserverRelation.ActivationMode}
    {names : List Locals.Name} {values : List Word}
    {finalStore : Locals.Source.Store}
    {code : Structured.Code}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {rest : List Word}
    (hContext :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hWF : plan.WellFormed)
    (hLive :
      ∀ name, name ∈ names → name ∈ live)
    (hAssign :
      Functions.Source.Store.assignMany names values source.source.vars =
        some finalStore)
    (hCode :
      AllocationLowering.lowerCallTargetsCode?
          lowerCtx lowerState names values.length =
        some code)
    (hRel :
      AllocationObserverRelation.ActivationStateRel
        contract plan live values.length frameBase mode source target)
    (hStack :
      target.source.evm.stack = values ++ rest) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run code target =
          .ok targetFinal ∧
        AllocationObserverRelation.ActivationStateRel
          contract plan live 0 frameBase mode
          (source.withSource (source.source.withVars finalStore))
          targetFinal ∧
        targetFinal.source.evm.stack.length = rest.length := by
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
              by
                simpa [Locals.Source.State.withVars] using hRel,
              by simpa using congrArg List.length hStack⟩
      | cons value values =>
          simp [Functions.Source.Store.assignMany] at hAssign
  | cons name names ih =>
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
      | cons value values =>
          have hNameLive : name ∈ live :=
            hLive name (by simp)
          have hTailLive :
              ∀ other, other ∈ names → other ∈ live := by
            intro other hOther
            exact hLive other (by simp [hOther])
          change
            (if source.source.vars.contains name then
                Functions.Source.Store.assignMany names values
                  (Locals.Source.Store.insert
                    source.source.vars name value)
              else none) =
              some finalStore at hAssign
          by_cases hContains :
              source.source.vars.contains name = true
          · simp [hContains] at hAssign
            cases hOld : source.source.vars name with
            | none =>
                simp [Locals.Source.Store.contains, hOld] at hContains
            | some old =>
                let sourceNext :=
                  source.withSource (source.source.insert name value)
                have hTailAssign :
                    Functions.Source.Store.assignMany names values
                        sourceNext.source.vars =
                      some finalStore := by
                  simpa [sourceNext, Locals.Source.State.insert] using hAssign
                have hHeadStack :
                    target.source.evm.stack =
                      value :: (values ++ rest) := by
                  simpa using hStack
                have hHeadRel :
                    AllocationObserverRelation.ActivationStateRel
                      contract plan live (values.length + 1) frameBase mode
                      source target := by
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
                          have hWholeCode :
                              code = headCode ++ tailCode := by
                            apply Option.some.inj
                            calc
                              some code =
                                  AllocationLowering.lowerCallTargetsCode?
                                    lowerCtx lowerState (name :: names)
                                      (values.length + 1) :=
                                hCode.symm
                              _ = some (headCode ++ tailCode) := by
                                simp [
                                  AllocationLowering.lowerCallTargetsCode?,
                                  hSlot, hStackSlot, hHeadCode, hTailCode]
                          subst code
                          cases hContext with
                          | stack stackContext =>
                              obtain
                                  ⟨planDepth, depth, hLocation, hCurrentDepth,
                                    hLowerDepth⟩ :=
                                stackContext.stack name slot hNameLive
                                  hSlot hStackSlot
                              obtain
                                  ⟨targetHead, hHeadRun, hHeadFinalRel,
                                    hHeadFinalStack⟩ :=
                                stack_step hHeadCode hHeadRel hHeadStack
                                  hNameLive hLocation hCurrentDepth hLowerDepth
                                  trivial hOld
                              obtain
                                  ⟨targetFinal, hTailRun, hFinalRel,
                                    hFinalStack⟩ :=
                                ih hTailLive hTailAssign hTailCode
                                  hHeadFinalRel hHeadFinalStack
                              refine
                                ⟨targetFinal, ?_, ?_, ?_⟩
                              · rw [
                                  AllocationObserverPreservation.ObserverCode.run_append,
                                  hHeadRun]
                                exact hTailRun
                              · simpa [sourceNext,
                                  Locals.Source.State.withVars] using hFinalRel
                              · simpa using hFinalStack
                          | @scratch frameDepth frameWords scratchContext =>
                              obtain
                                  ⟨planDepth, depth, hLocation, hCurrentDepth,
                                    hLowerDepth⟩ :=
                                scratchContext.stack name slot hNameLive
                                  hSlot hStackSlot
                              have hDepthValid :
                                  AllocationObserverRelation.ActivationMode.StackDepthValid
                                    (.scratch frameDepth frameWords) depth :=
                                scratchContext.stack_depth_lt_frame
                                  hCurrentDepth
                              obtain
                                  ⟨targetHead, hHeadRun, hHeadFinalRel,
                                    hHeadFinalStack⟩ :=
                                stack_step hHeadCode hHeadRel hHeadStack
                                  hNameLive hLocation hCurrentDepth hLowerDepth
                                  hDepthValid hOld
                              obtain
                                  ⟨targetFinal, hTailRun, hFinalRel,
                                    hFinalStack⟩ :=
                                ih hTailLive hTailAssign hTailCode
                                  hHeadFinalRel hHeadFinalStack
                              refine
                                ⟨targetFinal, ?_, ?_, ?_⟩
                              · rw [
                                  AllocationObserverPreservation.ObserverCode.run_append,
                                  hHeadRun]
                                exact hTailRun
                              · simpa [sourceNext,
                                  Locals.Source.State.withVars] using hFinalRel
                              · simpa using hFinalStack
                · have hScratchSlot :
                    AllocationLowering.isStackSlot lowerCtx slot = false :=
                    Bool.eq_false_of_not_eq_true hStackSlot
                  cases hContext with
                  | stack stackContext =>
                      have hFrameNone :
                          Locals.Layout.lookupDepth?
                              lowerCtx.frameName lowerState.layout =
                            none :=
                        lookupDepth?_none_of_not_mem
                          stackContext.frameAbsent
                      simp [AllocationLowering.lowerCallTargetsCode?,
                        hSlot, hScratchSlot,
                        AllocationLowering.scratchAssignTopCode?,
                        AllocationLowering.frameDepth?, hFrameNone] at hCode
                  | @scratch frameDepth frameWords scratchContext =>
                      cases hRel with
                      | scratch scratchRel =>
                          obtain ⟨hLocation, hFrameDepth⟩ :=
                            scratchContext.scratch name slot hNameLive
                              hSlot hScratchSlot
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
                                  simp [
                                    AllocationLowering.lowerCallTargetsCode?,
                                    hSlot, hScratchSlot, hHeadCode, hTailCode]
                                    at hCode
                              | some tailCode =>
                                  have hWholeCode :
                                      code = headCode ++ tailCode := by
                                    apply Option.some.inj
                                    calc
                                      some code =
                                          AllocationLowering.lowerCallTargetsCode?
                                              lowerCtx lowerState
                                                (name :: names)
                                                (values.length + 1) :=
                                        hCode.symm
                                      _ = some (headCode ++ tailCode) := by
                                        simp [
                                          AllocationLowering.lowerCallTargetsCode?,
                                          hSlot, hScratchSlot, hHeadCode,
                                          hTailCode]
                                  subst code
                                  obtain
                                      ⟨targetHead, hHeadRun, hHeadFinalRel,
                                        hHeadFinalStack⟩ :=
                                    scratch_step hHeadCode scratchRel hHeadStack
                                      hWF hNameLive hLocation hFrameDepth
                                  obtain
                                      ⟨targetFinal, hTailRun, hFinalRel,
                                        hFinalStack⟩ :=
                                    ih hTailLive hTailAssign hTailCode
                                      hHeadFinalRel hHeadFinalStack
                                  refine
                                    ⟨targetFinal, ?_, ?_, hFinalStack⟩
                                  · rw [
                                      AllocationObserverPreservation.ObserverCode.run_append,
                                      hHeadRun]
                                    exact hTailRun
                                  · simpa [sourceNext,
                                      Locals.Source.State.withVars] using
                                      hFinalRel
          · simp [hContains] at hAssign

end CallTargets

end AllocationObserverCall
end Functions
end EvmCompiler
