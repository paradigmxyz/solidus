import EvmCompiler.Functions.AllocationObserverContext
import EvmCompiler.Functions.AllocationObserverPreservation
import EvmCompiler.Functions.AllocationObserverSafety

namespace EvmCompiler
namespace Functions
namespace AllocationObserverCleanup

open AllocationObserverRelation

abbrev Trace := Assembly.ResourceTrace

/--
Representation change performed by plain stack cleanup.

The surviving stack depth is allocation-owned. Scratch activations retain the
same frame and move its hidden pointer upward by the number of discarded stack
locals.
-/
inductive ModeTransition (finalStackDepth targetDepth : Nat) :
    ActivationMode → ActivationMode → Prop where
  | stack
      (target : targetDepth = finalStackDepth) :
      ModeTransition finalStackDepth targetDepth .stack .stack
  | scratch
      (beforeDepth afterDepth frameWords : Nat)
      (after : afterDepth = finalStackDepth)
      (target : targetDepth = afterDepth + 1) :
      ModeTransition finalStackDepth targetDepth
        (.scratch beforeDepth frameWords)
        (.scratch afterDepth frameWords)

/--
Source/allocation-facing control transition for `break` and `continue`
cleanup. It contains no target execution premise or generated code.
-/
structure Transition
    (plan : Locals.Allocation.Plan)
    (beforeLive afterLive : List Locals.Name)
    (targetDepth : Nat)
    (beforeMode afterMode : ActivationMode) where
  dropped : List Locals.Name
  subset :
    ∀ name, name ∈ afterLive → name ∈ beforeLive
  stackOrder :
    currentStackOrder plan beforeLive =
      dropped ++ currentStackOrder plan afterLive
  mode :
    ModeTransition
      (currentStackOrder plan afterLive).length targetDepth
      beforeMode afterMode

namespace Plain

theorem finishScoped_shape
    {outer final : Locals.Ctx}
    {stmts : List Expressions.Stmt}
    {block : Expressions.Block}
    (hFinish :
      Locals.finishScoped outer final stmts = some block) :
    ∃ cleanup,
      final.cleanupTo? outer.layout.length = some cleanup ∧
      block.stmts =
        stmts ++ [Expressions.Stmt.code cleanup] := by
  unfold Locals.finishScoped at hFinish
  cases hCleanup :
      final.cleanupTo? outer.layout.length with
  | none =>
      simp [hCleanup] at hFinish
  | some cleanup =>
      simp [hCleanup, Locals.codeStmt] at hFinish
      cases hFinish
      exact ⟨cleanup, rfl, rfl⟩

theorem cleanupTo?_shape
    {ctx : Locals.Ctx} {targetDepth : Nat}
    {code : Structured.Code}
    (hCleanup : ctx.cleanupTo? targetDepth = some code) :
    targetDepth ≤ ctx.layout.length ∧
      code =
        List.replicate (ctx.layout.length - targetDepth)
          (Structured.BasicInstr.op .pop) := by
  unfold Locals.Ctx.cleanupTo? at hCleanup
  by_cases hDepth : targetDepth ≤ ctx.layout.length
  · simp only [hDepth, if_pos, Option.some.injEq] at hCleanup
    exact ⟨hDepth, hCleanup.symm⟩
  · simp [hDepth] at hCleanup

/--
Construct the exact cleanup transition from the real open-block lowerer's state
extension and the two adjacent compiler contexts.
-/
theorem transition_of_stateExtends
    {lowerCtx : AllocationLowering.Ctx}
    {bodyState outerState : AllocationLowering.State}
    {bodyLocals outerLocals : Locals.Ctx}
    {bodyPlan outerPlan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth : Nat}
    {beforeMode afterMode : ActivationMode}
    (hBody :
      AllocationObserverContext.ActivationExprContext
        lowerCtx bodyState bodyLocals bodyPlan beforeLive beforeMode)
    (hOuter :
      AllocationObserverContext.ActivationExprContext
        lowerCtx outerState outerLocals outerPlan afterLive afterMode)
    (hSubset :
      ∀ name, name ∈ afterLive → name ∈ beforeLive)
    (hSameFrame : SameFrame beforeMode afterMode)
    (hTargetDepth : targetDepth = outerLocals.layout.length)
    (hExtends :
      AllocationLowering.StateExtends
        afterLive outerState bodyState) :
    ∃ hTransition :
        Transition bodyPlan beforeLive afterLive targetDepth
          beforeMode afterMode,
      bodyState.layout =
          hTransition.dropped ++ outerState.layout ∧
        ∀ name,
          name ∈ afterLive →
          AllocationSupport.lookupSlot?
              name bodyState.allocation.env =
            AllocationSupport.lookupSlot?
              name outerState.allocation.env := by
  rcases hExtends with
    ⟨dropped, hLayout, hFresh, hSlots⟩
  have hDroppedFilter :
      dropped.filter (fun name => decide (name ∈ afterLive)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro name hDropped
    simpa using hFresh name hDropped
  cases hSameFrame with
  | stack =>
      cases hBody with
      | stack body =>
          cases hOuter with
          | stack outer =>
              have hOuterFilter :
                  outerState.layout.filter
                      (fun name => decide (name ∈ afterLive)) =
                    outerState.layout := by
                apply List.filter_eq_self.mpr
                intro name hName
                have hLive :
                    name ∈ afterLive := by
                  apply mem_live_of_mem_currentStackOrder
                  rw [outer.stackOrder]
                  exact hName
                simpa using hLive
              have hAfterOrder :
                  currentStackOrder bodyPlan afterLive =
                    outerState.layout := by
                calc
                  currentStackOrder bodyPlan afterLive =
                      (currentStackOrder bodyPlan beforeLive).filter
                        (fun name => decide (name ∈ afterLive)) :=
                    (currentStackOrder_restrict hSubset).symm
                  _ =
                      bodyState.layout.filter
                        (fun name => decide (name ∈ afterLive)) := by
                    rw [body.stackOrder]
                  _ =
                      (dropped ++ outerState.layout).filter
                        (fun name => decide (name ∈ afterLive)) := by
                    rw [hLayout]
                  _ = outerState.layout := by
                    rw [List.filter_append, hDroppedFilter, hOuterFilter]
                    rfl
              have hStackOrder :
                  currentStackOrder bodyPlan beforeLive =
                    dropped ++ currentStackOrder bodyPlan afterLive := by
                calc
                  currentStackOrder bodyPlan beforeLive =
                      bodyState.layout := body.stackOrder
                  _ = dropped ++ outerState.layout := hLayout
                  _ =
                      dropped ++ currentStackOrder bodyPlan afterLive := by
                    rw [hAfterOrder]
              have hTarget :
                  targetDepth =
                    (currentStackOrder bodyPlan afterLive).length := by
                calc
                  targetDepth = outerLocals.layout.length := hTargetDepth
                  _ = outerState.layout.length :=
                    congrArg List.length outer.layout
                  _ =
                      (currentStackOrder bodyPlan afterLive).length :=
                    congrArg List.length hAfterOrder.symm
              let transition :
                  Transition bodyPlan beforeLive afterLive targetDepth
                    .stack .stack :=
                { dropped := dropped
                  subset := hSubset
                  stackOrder := hStackOrder
                  mode := .stack hTarget }
              exact ⟨transition, hLayout, hSlots⟩
  | scratch beforeDepth afterDepth frameWords =>
      cases hBody with
      | scratch body =>
          cases hOuter with
          | scratch outer =>
              have hDepth :
                  beforeDepth = dropped.length + afterDepth := by
                have hBodyLength := body.frameBottom
                have hOuterLength := outer.frameBottom
                rw [hLayout] at hBodyLength
                simp only [List.length_append] at hBodyLength
                omega
              have hBeforeOrder :
                  currentStackOrder bodyPlan beforeLive =
                    dropped ++ outerState.layout.take afterDepth := by
                rw [body.stackPrefix, hLayout]
                calc
                  List.take beforeDepth
                        (dropped ++ outerState.layout) =
                      List.take (dropped.length + afterDepth)
                        (dropped ++ outerState.layout) :=
                    congrArg
                      (fun depth =>
                        List.take depth (dropped ++ outerState.layout))
                      hDepth
                  _ = dropped ++ outerState.layout.take afterDepth :=
                    List.take_length_add_append afterDepth
              have hOuterFilter :
                  (outerState.layout.take afterDepth).filter
                      (fun name => decide (name ∈ afterLive)) =
                    outerState.layout.take afterDepth := by
                apply List.filter_eq_self.mpr
                intro name hName
                have hLive :
                    name ∈ afterLive := by
                  apply mem_live_of_mem_currentStackOrder
                  rw [outer.stackPrefix]
                  exact hName
                simpa using hLive
              have hAfterOrder :
                  currentStackOrder bodyPlan afterLive =
                    currentStackOrder outerPlan afterLive := by
                calc
                  currentStackOrder bodyPlan afterLive =
                      (currentStackOrder bodyPlan beforeLive).filter
                        (fun name => decide (name ∈ afterLive)) :=
                    (currentStackOrder_restrict hSubset).symm
                  _ =
                      (dropped ++
                        outerState.layout.take afterDepth).filter
                        (fun name => decide (name ∈ afterLive)) := by
                    rw [hBeforeOrder]
                  _ = outerState.layout.take afterDepth := by
                    rw [List.filter_append, hDroppedFilter, hOuterFilter]
                    rfl
                  _ = currentStackOrder outerPlan afterLive :=
                    outer.stackPrefix.symm
              have hStackOrder :
                  currentStackOrder bodyPlan beforeLive =
                    dropped ++ currentStackOrder bodyPlan afterLive := by
                calc
                  currentStackOrder bodyPlan beforeLive =
                      dropped ++ outerState.layout.take afterDepth :=
                    hBeforeOrder
                  _ =
                      dropped ++ currentStackOrder outerPlan afterLive := by
                    rw [outer.stackPrefix]
                  _ =
                      dropped ++ currentStackOrder bodyPlan afterLive := by
                    rw [hAfterOrder]
              have hAfterDepth :
                  afterDepth =
                    (currentStackOrder bodyPlan afterLive).length := by
                calc
                  afterDepth =
                      (currentStackOrder outerPlan afterLive).length :=
                    outer.currentStackOrder_length.symm
                  _ =
                      (currentStackOrder bodyPlan afterLive).length :=
                    congrArg List.length hAfterOrder.symm
              have hTarget :
                  targetDepth = afterDepth + 1 := by
                calc
                  targetDepth = outerLocals.layout.length :=
                    hTargetDepth
                  _ = outerState.layout.length :=
                    congrArg List.length outer.layout
                  _ = afterDepth + 1 := outer.frameBottom
              let transition :
                  Transition bodyPlan beforeLive afterLive targetDepth
                    (.scratch beforeDepth frameWords)
                    (.scratch afterDepth frameWords) :=
                { dropped := dropped
                  subset := hSubset
                  stackOrder := hStackOrder
                  mode :=
                    .scratch beforeDepth afterDepth frameWords
                      hAfterDepth hTarget }
              exact ⟨transition, hLayout, hSlots⟩

/--
Restore an inner plan's compiler context after plain lexical cleanup.

The two explicit premises are ordinary lowering facts: stack declarations in
the inner scope extend the outer layout by a prefix, and surviving source names
retain their allocation slots. No target execution or observer evidence is
used.
-/
theorem restore_context
    {lowerCtx : AllocationLowering.Ctx}
    {bodyState outerState : AllocationLowering.State}
    {bodyLocals outerLocals : Locals.Ctx}
    {bodyPlan outerPlan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth : Nat}
    {beforeMode afterMode : ActivationMode}
    (hBody :
      AllocationObserverContext.ActivationExprContext
        lowerCtx bodyState bodyLocals bodyPlan beforeLive beforeMode)
    (hOuter :
      AllocationObserverContext.ActivationExprContext
        lowerCtx outerState outerLocals outerPlan afterLive afterMode)
    (hTransition :
      Transition bodyPlan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hLayout :
      bodyState.layout =
        hTransition.dropped ++ outerState.layout)
    (hSlots :
      ∀ name,
        name ∈ afterLive →
        AllocationSupport.lookupSlot?
            name bodyState.allocation.env =
          AllocationSupport.lookupSlot?
            name outerState.allocation.env) :
    AllocationObserverContext.ActivationExprContext
        lowerCtx outerState outerLocals bodyPlan afterLive afterMode ∧
      PlanAgreesOn bodyPlan outerPlan afterLive := by
  have hSubset := hTransition.subset
  cases hTransition.mode with
  | stack hTarget =>
      cases hBody with
      | stack body =>
          cases hOuter with
          | stack outer =>
              have hOrder :
                  currentStackOrder bodyPlan afterLive =
                    currentStackOrder outerPlan afterLive := by
                apply List.append_cancel_left
                calc
                  hTransition.dropped ++
                        currentStackOrder bodyPlan afterLive =
                      currentStackOrder bodyPlan beforeLive :=
                    hTransition.stackOrder.symm
                  _ = bodyState.layout := body.stackOrder
                  _ = hTransition.dropped ++ outerState.layout := hLayout
                  _ =
                      hTransition.dropped ++
                        currentStackOrder outerPlan afterLive := by
                    rw [outer.stackOrder]
              have hRestored :
                  AllocationObserverContext.ActivationExprContext
                    lowerCtx outerState outerLocals bodyPlan afterLive
                      .stack := by
                refine .stack
                  { layout := outer.layout
                    stackOrder := hOrder.trans outer.stackOrder
                    frameAbsent := outer.frameAbsent
                    liveStackOnly := ?_
                    location := ?_
                    slot := outer.slot
                    stack := ?_ }
                · intro name slot hLive hLocation
                  exact
                    body.liveStackOnly name slot
                      (hSubset name hLive) hLocation
                · intro name hLive
                  exact body.location name (hSubset name hLive)
                · intro name slot hLive hOuterSlot hStack
                  obtain
                      ⟨outerPlanDepth, depth, _hOuterLocation,
                        hOuterCurrent, hOuterLayout⟩ :=
                    outer.stack name slot hLive hOuterSlot hStack
                  obtain ⟨bodyLocation, hBodyLocation⟩ :=
                    body.location name (hSubset name hLive)
                  cases bodyLocation with
                  | scratch scratchSlot =>
                      exact False.elim
                        (body.liveStackOnly name scratchSlot
                          (hSubset name hLive) hBodyLocation)
                  | stack bodyPlanDepth =>
                      exact
                        ⟨bodyPlanDepth, depth, hBodyLocation,
                          by simpa [hOrder] using hOuterCurrent,
                          hOuterLayout⟩
              exact
                ⟨hRestored,
                  AllocationObserverContext.ActivationExprContext.planAgreesOn
                    hRestored (.stack outer)⟩
  | scratch beforeDepth afterDepth frameWords hAfter hTarget =>
      cases hBody with
      | scratch body =>
          cases hOuter with
          | scratch outer =>
              have hDepth :
                  beforeDepth =
                    hTransition.dropped.length + afterDepth := by
                have hBodyLength := body.frameBottom
                have hOuterLength := outer.frameBottom
                rw [hLayout] at hBodyLength
                simp only [List.length_append] at hBodyLength
                omega
              have hBeforeOrder :
                  currentStackOrder bodyPlan beforeLive =
                    hTransition.dropped ++ outerState.layout.take afterDepth := by
                rw [body.stackPrefix, hLayout]
                calc
                  List.take beforeDepth
                        (hTransition.dropped ++ outerState.layout) =
                      List.take
                        (hTransition.dropped.length + afterDepth)
                        (hTransition.dropped ++ outerState.layout) :=
                    congrArg
                      (fun depth =>
                        List.take depth
                          (hTransition.dropped ++ outerState.layout))
                      hDepth
                  _ =
                      hTransition.dropped ++
                        outerState.layout.take afterDepth :=
                    List.take_length_add_append afterDepth
              have hOrder :
                  currentStackOrder bodyPlan afterLive =
                    currentStackOrder outerPlan afterLive := by
                apply List.append_cancel_left
                calc
                  hTransition.dropped ++
                        currentStackOrder bodyPlan afterLive =
                      currentStackOrder bodyPlan beforeLive :=
                    hTransition.stackOrder.symm
                  _ =
                      hTransition.dropped ++
                        outerState.layout.take afterDepth :=
                    hBeforeOrder
                  _ =
                      hTransition.dropped ++
                        currentStackOrder outerPlan afterLive := by
                    rw [outer.stackPrefix]
              have hRestored :
                  AllocationObserverContext.ActivationExprContext
                    lowerCtx outerState outerLocals bodyPlan afterLive
                      (.scratch afterDepth frameWords) := by
                refine .scratch
                  { layout := outer.layout
                    stackPrefix := hOrder.trans outer.stackPrefix
                    frame := outer.frame
                    frameBottom := outer.frameBottom
                    location := ?_
                    slot := outer.slot
                    stack := ?_
                    scratch := ?_ }
                · intro name hLive
                  exact body.location name (hSubset name hLive)
                · intro name slot hLive hOuterSlot hStack
                  have hBodySlot :
                      AllocationSupport.lookupSlot?
                          name bodyState.allocation.env =
                        some slot := by
                    rw [hSlots name hLive]
                    exact hOuterSlot
                  obtain
                      ⟨bodyPlanDepth, _bodyRuntimeDepth,
                        hBodyLocation, _hBodyCurrent, _hBodyLayout⟩ :=
                    body.stack name slot (hSubset name hLive)
                      hBodySlot hStack
                  obtain
                      ⟨_outerPlanDepth, depth,
                        _hOuterLocation, hOuterCurrent, hOuterLayout⟩ :=
                    outer.stack name slot hLive hOuterSlot hStack
                  exact
                    ⟨bodyPlanDepth, depth, hBodyLocation,
                      by simpa [hOrder] using hOuterCurrent,
                      hOuterLayout⟩
                · intro name slot hLive hOuterSlot hScratch
                  have hBodySlot :
                      AllocationSupport.lookupSlot?
                          name bodyState.allocation.env =
                        some slot := by
                    rw [hSlots name hLive]
                    exact hOuterSlot
                  obtain ⟨hBodyLocation, _hBodyFrame⟩ :=
                    body.scratch name slot (hSubset name hLive)
                      hBodySlot hScratch
                  exact ⟨hBodyLocation, outer.frame⟩
              exact
                ⟨hRestored,
                  AllocationObserverContext.ActivationExprContext.planAgreesOn
                    hRestored (.scratch outer)⟩

/--
Forward preservation for the exact `POP` sequence emitted by
`Locals.Ctx.cleanupTo?`.
-/
theorem forward
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {cleanup : Structured.Code}
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan beforeLive beforeMode)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hWF : plan.WellFormed)
    (hDefined : LiveDefined beforeLive source.source)
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target)
    (hCleanup :
      localsCtx.cleanupTo? targetDepth = some cleanup) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run cleanup target =
          .ok targetFinal ∧
        ActivationStateRel contract plan afterLive 0 frameBase
          afterMode
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source)
          targetFinal := by
  obtain ⟨hTargetDepth, hCleanupCode⟩ :=
    cleanupTo?_shape hCleanup
  have hLayoutBound :=
    hCtx.layout_length_le_target_stack hWF hDefined hRel
  have hPopBound :
      localsCtx.layout.length - targetDepth ≤
        target.source.evm.stack.length :=
    (Nat.sub_le _ _).trans hLayoutBound
  obtain
      ⟨targetFinal, hRun, hCursor, hFinalStack,
        hShared, _hReturns⟩ :=
    AllocationObserverPreservation.ObserverCode.run_replicate_pop
      (localsCtx.layout.length - targetDepth) hPopBound
  refine ⟨targetFinal, ?_, ?_⟩
  · simpa [hCleanupCode] using hRun
  · cases hTransition.mode with
    | stack hFinalDepth =>
        cases hCtx with
        | stack hStackCtx =>
            cases hRel with
            | stack hOnly hActive hState =>
                have hLayoutLength :
                    localsCtx.layout.length =
                      (currentStackOrder plan beforeLive).length := by
                  rw [hStackCtx.layout, ← hStackCtx.stackOrder]
                have hOrderLength :=
                  congrArg List.length hTransition.stackOrder
                have hCount :
                    localsCtx.layout.length - targetDepth =
                      hTransition.dropped.length := by
                  simp only [List.length_append] at hOrderLength
                  omega
                have hBase :=
                  hState.restrict_drop_stack_prefix hWF
                    hTransition.subset hTransition.stackOrder
                    hCursor hShared
                    (by simpa [hCount] using hFinalStack)
                exact
                  .stack
                    (fun name slot hLive hLocation =>
                      hOnly name slot
                        (hTransition.subset name hLive) hLocation)
                    (by simpa [hShared] using hActive)
                    hBase
    | scratch beforeDepth afterDepth frameWords hAfterDepth hFinalDepth =>
        cases hCtx with
        | scratch hScratchCtx =>
            cases hRel with
            | scratch hScratch =>
                have hBeforeDepth :
                    beforeDepth =
                      hTransition.dropped.length + afterDepth := by
                  have hBeforeOrder :=
                    hScratchCtx.currentStackOrder_length
                  have hOrderLength :=
                    congrArg List.length hTransition.stackOrder
                  simp only [List.length_append] at hOrderLength
                  omega
                have hCount :
                    localsCtx.layout.length - targetDepth =
                      hTransition.dropped.length := by
                  have hLayout :
                      localsCtx.layout.length = beforeDepth + 1 := by
                    rw [hScratchCtx.layout, hScratchCtx.frameBottom]
                  omega
                have hBase :=
                  hScratch.base.restrict_drop_stack_prefix hWF
                    hTransition.subset hTransition.stackOrder
                    hCursor hShared
                    (by simpa [hCount] using hFinalStack)
                have hFramePointer :
                    targetFinal.source.evm.stack[afterDepth]? =
                      some (EvmYul.UInt256.ofNat frameBase) := by
                  rw [hFinalStack, List.getElem?_drop]
                  simpa [hCount, hBeforeDepth,
                    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                    hScratch.framePointer
                exact
                  .scratch
                    { base := hBase
                      framePointer := by simpa using hFramePointer
                      frameActive := by
                        simpa [hShared] using hScratch.frameActive
                      frameAllocated := by
                        simpa [hShared] using hScratch.frameAllocated
                      frameNoWrap := hScratch.frameNoWrap
                      frameHostAddressable := hScratch.frameHostAddressable
                      activeNoWrap := by
                        simpa [hShared] using hScratch.activeNoWrap
                      frameReserved := hScratch.frameReserved
                      scratchBound := fun name slot hLive hLocation =>
                        hScratch.scratchBound name slot
                          (hTransition.subset name hLive) hLocation }

/--
Plain cleanup started from an exact compiler-layout stack finishes at exactly
the requested target depth.

This is the stack-balance fact needed to rebuild the complete activation
invariant after lexical-scope cleanup.
-/
theorem forward_exact
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {cleanup : Structured.Code}
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan beforeLive beforeMode)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hWF : plan.WellFormed)
    (hDefined : LiveDefined beforeLive source.source)
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target)
    (hStackLength :
      target.source.evm.stack.length = localsCtx.layout.length)
    (hCleanup :
      localsCtx.cleanupTo? targetDepth = some cleanup) :
    ∃ targetFinal,
      Structured.ObserverSemantics.Code.run cleanup target =
          .ok targetFinal ∧
        ActivationStateRel contract plan afterLive 0 frameBase
          afterMode
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source)
          targetFinal ∧
        targetFinal.source.evm.stack.length = targetDepth := by
  obtain ⟨targetFinal, hRun, hFinalRel⟩ :=
    forward hCtx hTransition hWF hDefined hRel hCleanup
  obtain ⟨hDepth, hCleanupCode⟩ :=
    cleanupTo?_shape hCleanup
  have hBound :
      localsCtx.layout.length - targetDepth ≤
        target.source.evm.stack.length := by
    omega
  obtain
      ⟨expected, hExpectedRun, _hCursor, hExpectedStack,
        _hShared, _hReturns⟩ :=
    AllocationObserverPreservation.ObserverCode.run_replicate_pop
      (localsCtx.layout.length - targetDepth) hBound
  have hExpectedRun' :
      Structured.ObserverSemantics.Code.run cleanup target =
        .ok expected := by
    simpa [hCleanupCode] using hExpectedRun
  rw [hRun] at hExpectedRun'
  cases hExpectedRun'
  refine ⟨targetFinal, hRun, hFinalRel, ?_⟩
  rw [hExpectedStack, List.length_drop, hStackLength]
  omega

/--
Backward adequacy for plain cleanup follows from deterministic execution of the
same compiler-emitted `POP` sequence.
-/
theorem backward
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {cleanup : Structured.Code}
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan beforeLive beforeMode)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hWF : plan.WellFormed)
    (hDefined : LiveDefined beforeLive source.source)
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target)
    (hCleanup :
      localsCtx.cleanupTo? targetDepth = some cleanup)
    (hRun :
      Structured.ObserverSemantics.Code.run cleanup target =
        .ok targetFinal) :
    ActivationStateRel contract plan afterLive 0 frameBase
      afterMode
      ((Functions.ObserverSemantics.stateModel transcript).restrictTo
        afterLive source)
      targetFinal := by
  obtain ⟨expected, hExpectedRun, hExpectedRel⟩ :=
    forward hCtx hTransition hWF hDefined hRel hCleanup
  rw [hExpectedRun] at hRun
  cases hRun
  exact hExpectedRel

end Plain

namespace Preserving

theorem cleanupToPreserving?_shape
    {ctx : Locals.Ctx} {preserve targetDepth : Nat}
    {code : Structured.Code}
    (hCleanup :
      ctx.cleanupToPreserving? preserve targetDepth = some code) :
    targetDepth ≤ ctx.layout.length ∧
      Locals.Ctx.cleanupManyPreserving?
          (ctx.layout.length - targetDepth) preserve =
        some code := by
  unfold Locals.Ctx.cleanupToPreserving? at hCleanup
  by_cases hDepth : targetDepth ≤ ctx.layout.length
  · simp only [hDepth, if_pos] at hCleanup
    exact ⟨hDepth, hCleanup⟩
  · simp [hDepth] at hCleanup

/--
Executing preserving cleanup to activation depth zero removes the complete
compiler layout beneath the returned values.
-/
theorem forward_zero {transcript : Trace}
    {ctx : Locals.Ctx} {preserve : Nat}
    {cleanup : Structured.Code}
    {values baseStack : List Assembly.Word}
    {target : Structured.ObserverSemantics.State transcript}
    (hCleanup :
      ctx.cleanupToPreserving? preserve 0 = some cleanup)
    (hValuesLength : values.length = preserve)
    (hBaseLength : baseStack.length = ctx.layout.length)
    (hStack :
      target.source.evm.stack = values ++ baseStack) :
    ∃ final,
      Structured.ObserverSemantics.Code.run cleanup target = .ok final ∧
      final.cursor = target.cursor ∧
      final.source.evm.stack = values ∧
      final.source.evm.toSharedState =
        target.source.evm.toSharedState ∧
      final.source.returns = target.source.returns := by
  obtain ⟨_hDepth, hMany⟩ :=
    cleanupToPreserving?_shape hCleanup
  obtain ⟨final, hRun, hCursor, hFinalStack, hShared, hReturns⟩ :=
    AllocationObserverPreservation.ObserverCode.run_cleanupManyPreserving?
      (discarded := baseStack) (suffix := [])
      hMany hValuesLength
        (by simpa [hBaseLength])
        (by simpa using hStack)
  exact
    ⟨final, hRun, hCursor, by simpa using hFinalStack,
      hShared, hReturns⟩

/--
Backward adequacy for exact preserving cleanup follows from deterministic
execution of the compiler-emitted code.
-/
theorem backward_zero {transcript : Trace}
    {ctx : Locals.Ctx} {preserve : Nat}
    {cleanup : Structured.Code}
    {values baseStack : List Assembly.Word}
    {target final : Structured.ObserverSemantics.State transcript}
    (hCleanup :
      ctx.cleanupToPreserving? preserve 0 = some cleanup)
    (hValuesLength : values.length = preserve)
    (hBaseLength : baseStack.length = ctx.layout.length)
    (hStack :
      target.source.evm.stack = values ++ baseStack)
    (hRun :
      Structured.ObserverSemantics.Code.run cleanup target = .ok final) :
    final.cursor = target.cursor ∧
      final.source.evm.stack = values ∧
      final.source.evm.toSharedState =
        target.source.evm.toSharedState ∧
      final.source.returns = target.source.returns := by
  obtain
      ⟨expected, hExpectedRun, hCursor, hExpectedStack,
        hShared, hReturns⟩ :=
    forward_zero hCleanup hValuesLength hBaseLength hStack
  rw [hExpectedRun] at hRun
  cases hRun
  exact ⟨hCursor, hExpectedStack, hShared, hReturns⟩

end Preserving

namespace ReturnValues

private theorem memorySafeEval_cast
    {contract : MemoryContract.Contract} {transcript : Trace}
    {left right : Nat} (h : left = right)
    {exprs : Locals.ExprSeq left}
    {source final : Functions.ObserverSemantics.State transcript}
    {values : List Assembly.Word}
    (hEval :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        contract transcript exprs source final values) :
    AllocationObserverSafety.ExprSeq.MemorySafeEval
      contract transcript
      (cast (congrArg Locals.ExprSeq h) exprs)
      source final values := by
  cases h
  exact hEval

theorem memorySafeEval
    {contract : MemoryContract.Contract} {transcript : Trace}
    {returns : List Functions.Name} {values : List Assembly.Word}
    {source : Functions.ObserverSemantics.State transcript}
    (hLookup :
      Functions.Source.Store.lookupMany returns source.source.vars =
        some values) :
    AllocationObserverSafety.ExprSeq.MemorySafeEval
      contract transcript (Functions.Lower.returnExprs returns)
      source source values := by
  induction returns generalizing values with
  | nil =>
      simp [Functions.Source.Store.lookupMany] at hLookup
      subst values
      exact .nil
  | cons name returns ih =>
      unfold Functions.Source.Store.lookupMany at hLookup
      cases hValue : source.source.vars name with
      | none =>
          simp [hValue] at hLookup
      | some value =>
          cases hTail :
              Functions.Source.Store.lookupMany returns source.source.vars with
          | none =>
              simp [hValue, hTail] at hLookup
          | some tailValues =>
              simp [hValue, hTail] at hLookup
              subst values
              unfold Functions.Lower.returnExprs
              let exprs : Locals.ExprSeq (1 + returns.length) :=
                Locals.ExprSeq.cons (.var name)
                  (Functions.Lower.returnExprs returns)
              have hLen : 1 + returns.length = returns.length + 1 := by
                omega
              change
                AllocationObserverSafety.ExprSeq.MemorySafeEval
                  contract transcript
                  (cast (congrArg Locals.ExprSeq hLen) exprs)
                  source source (value :: tailValues)
              apply memorySafeEval_cast hLen
              exact
                AllocationObserverSafety.ExprSeq.MemorySafeEval.cons
                  (AllocationObserverSafety.Expr.MemorySafeEval.var hValue)
                  (ih hTail)

private theorem exprSeqScoped_cast
    {left right : Nat} (h : left = right)
    {live : List Functions.Name} {exprs : Locals.ExprSeq left}
    (hScoped : Functions.Scope.ExprSeqScoped live exprs) :
    Functions.Scope.ExprSeqScoped live
      (cast (congrArg Locals.ExprSeq h) exprs) := by
  cases h
  exact hScoped

theorem returnExprsScoped
    {returns live : List Functions.Name}
    (hSubset : ∀ name, name ∈ returns → name ∈ live) :
    Functions.Scope.ExprSeqScoped live
      (Functions.Lower.returnExprs returns) := by
  induction returns with
  | nil =>
      trivial
  | cons name returns ih =>
      unfold Functions.Lower.returnExprs
      let exprs : Locals.ExprSeq (1 + returns.length) :=
        Locals.ExprSeq.cons (.var name)
          (Functions.Lower.returnExprs returns)
      have hLen : 1 + returns.length = returns.length + 1 := by
        omega
      change
        Functions.Scope.ExprSeqScoped live
          (cast (congrArg Locals.ExprSeq hLen) exprs)
      apply exprSeqScoped_cast hLen
      exact
        ⟨hSubset name (by simp),
          ih (fun other hOther => hSubset other (by simp [hOther]))⟩

theorem lowerExprSeq
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {returns : List Functions.Name}
    {lowered : Locals.ExprSeq returns.length}
    (hLower :
      AllocationLowering.lowerReturnExprs lowerCtx lowerState returns =
        some lowered) :
    AllocationLowering.lowerExprSeq lowerCtx lowerState
        (Functions.Lower.returnExprs returns) =
      some lowered := by
  exact hLower

end ReturnValues

namespace LeaveLeaf

theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hDepth : localsCtx.leaveDepth? = some 0)
    (hRetc : localsCtx.leaveRetc = returns.length)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .leave =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ loweredReturns returnCode cleanup,
      AllocationLowering.lowerReturnExprs
          lowerCtx lowerState returns =
        some loweredReturns ∧
      AllocationLowering.lowerExprSeq lowerCtx lowerState
          (Functions.Lower.returnExprs returns) =
        some loweredReturns ∧
      Locals.ExprSeq.compileCode localsCtx 0
          loweredReturns =
        some returnCode ∧
      localsCtx.cleanupToPreserving? returns.length 0 =
        some cleanup ∧
      loweredStmts =
        [.exprs loweredReturns, .leave] ∧
      lowerFinal = lowerState ∧
      compiledStmts =
        [ Expressions.Stmt.code returnCode,
          Expressions.Stmt.code cleanup,
          Expressions.Stmt.leave ] ∧
      localsFinal = localsCtx := by
  cases hReturns :
      AllocationLowering.lowerReturnExprs
        lowerCtx lowerState returns with
  | none =>
      simp [AllocationLowering.lowerStmt, hReturns] at hLower
  | some loweredReturns =>
      simp [AllocationLowering.lowerStmt, hReturns] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      have hLowerSeq :=
        ReturnValues.lowerExprSeq hReturns
      cases hReturnCode :
          Locals.ExprSeq.compileCode localsCtx 0
            loweredReturns with
      | none =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile,
            hReturnCode] at hCompile
      | some returnCode =>
          cases hCleanup :
              localsCtx.cleanupToPreserving? localsCtx.leaveRetc 0 with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hReturnCode, hDepth, hCleanup] at hCompile
          | some cleanup =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.codeStmt, hReturnCode, hDepth, hCleanup]
                at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              refine
                ⟨loweredReturns, returnCode, cleanup,
                  rfl, hLowerSeq, hReturnCode, ?_,
                  rfl, rfl, rfl, rfl⟩
              simpa [hRetc] using hCleanup

end LeaveLeaf

namespace BreakLeaf

theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {targetDepth : Nat}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hDepth : localsCtx.breakDepth? = some targetDepth)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .brk =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ cleanup,
      localsCtx.cleanupTo? targetDepth = some cleanup ∧
        loweredStmts = [.brk] ∧
        lowerFinal = lowerState ∧
        compiledStmts =
          [Expressions.Stmt.code cleanup, Expressions.Stmt.brk] ∧
        localsFinal = localsCtx := by
  simp [AllocationLowering.lowerStmt] at hLower
  rcases hLower with ⟨rfl, rfl⟩
  cases hCleanup : localsCtx.cleanupTo? targetDepth with
  | none =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        hDepth, hCleanup] at hCompile
  | some cleanup =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        Locals.codeStmt, hDepth, hCleanup] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact ⟨cleanup, rfl, rfl, rfl, rfl, rfl⟩

theorem forward_of_compilers
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : localsCtx.breakDepth? = some targetDepth)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan beforeLive beforeMode)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hWF : plan.WellFormed)
    (hDefined : LiveDefined beforeLive source.source)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .brk =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx 0 .brk source =
        .ok
          (Functions.Source.Effectful.Outcome.brk
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source),
            sourceCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target
        (Structured.EffectSemantics.Outcome.brk targetFinal) ∧
      ActivationOutcomeRel contract plan afterLive 0 frameBase afterMode
        (Functions.Source.Effectful.Outcome.brk
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source))
        (Structured.EffectSemantics.Outcome.brk targetFinal) := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    compiler_shape hTargetDepth hLower hCompile
  obtain ⟨targetFinal, hCleanupRun, hFinalRel⟩ :=
    Plain.forward hCtx hTransition hWF hDefined hRel hCleanup
  have hBreakStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 0 .brk targetFinal
          (Structured.EffectSemantics.Outcome.brk targetFinal) :=
    Structured.EffectSemantics.Stmt.Eval.brk
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := [Structured.Stmt.code cleanup, Structured.Stmt.brk] }
        target
        (Structured.EffectSemantics.Outcome.brk targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code
        (fuel := 1) hCleanupRun)
      (Structured.EffectSemantics.Block.Eval.cons_brk hBreakStmt)
  have hSource :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.brk
      (contract := contract) (transcript := transcript)
      (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
      (source := source) hSourceScope).run_eq
  refine ⟨targetFinal, hSource, ?_, ActivationOutcomeRel.brk hFinalRel⟩
  simpa [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] using hTarget

theorem backward_of_compilers
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {targetFuel : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : localsCtx.breakDepth? = some targetDepth)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan beforeLive beforeMode)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hWF : plan.WellFormed)
    (hDefined : LiveDefined beforeLive source.source)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .brk =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target
        (Structured.EffectSemantics.Outcome.brk targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx 0 .brk source =
      .ok
        (Functions.Source.Effectful.Outcome.brk
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source),
          sourceCtx) ∧
    ActivationOutcomeRel contract plan afterLive 0 frameBase afterMode
      (Functions.Source.Effectful.Outcome.brk
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source))
      (Structured.EffectSemantics.Outcome.brk targetFinal) := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    compiler_shape hTargetDepth hLower hCompile
  simp only [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] at hTarget
  cases hTarget with
  | cons_regular hCleanupStmt hTail =>
      cases hCleanupStmt with
      | code hCleanupRun =>
          cases hTail with
          | cons_regular hBreak _hRest =>
              cases hBreak
          | cons_brk _hBreak =>
              cases _hBreak
              have hFinalRel :=
                Plain.backward hCtx hTransition hWF hDefined hRel
                  hCleanup hCleanupRun
              have hSource :=
                (AllocationObserverSafety.Stmt.LeafMemorySafeRun.brk
                  (contract := contract) (transcript := transcript)
                  (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
                  (source := source) hSourceScope).run_eq
              exact ⟨hSource, ActivationOutcomeRel.brk hFinalRel⟩
  | cons_brk hCleanupStmt =>
      cases hCleanupStmt

end BreakLeaf

namespace ContinueLeaf

theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {targetDepth : Nat}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hDepth : localsCtx.continueDepth? = some targetDepth)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .cont =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ cleanup,
      localsCtx.cleanupTo? targetDepth = some cleanup ∧
        loweredStmts = [.cont] ∧
        lowerFinal = lowerState ∧
        compiledStmts =
          [Expressions.Stmt.code cleanup, Expressions.Stmt.cont] ∧
        localsFinal = localsCtx := by
  simp [AllocationLowering.lowerStmt] at hLower
  rcases hLower with ⟨rfl, rfl⟩
  cases hCleanup : localsCtx.cleanupTo? targetDepth with
  | none =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        hDepth, hCleanup] at hCompile
  | some cleanup =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        Locals.codeStmt, hDepth, hCleanup] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact ⟨cleanup, rfl, rfl, rfl, rfl, rfl⟩

theorem forward_of_compilers
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : localsCtx.continueDepth? = some targetDepth)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan beforeLive beforeMode)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hWF : plan.WellFormed)
    (hDefined : LiveDefined beforeLive source.source)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .cont =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx 0 .cont source =
        .ok
          (Functions.Source.Effectful.Outcome.cont
            ((Functions.ObserverSemantics.stateModel transcript).restrictTo
              afterLive source),
            sourceCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target
        (Structured.EffectSemantics.Outcome.cont targetFinal) ∧
      ActivationOutcomeRel contract plan afterLive 0 frameBase afterMode
        (Functions.Source.Effectful.Outcome.cont
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source))
        (Structured.EffectSemantics.Outcome.cont targetFinal) := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    compiler_shape hTargetDepth hLower hCompile
  obtain ⟨targetFinal, hCleanupRun, hFinalRel⟩ :=
    Plain.forward hCtx hTransition hWF hDefined hRel hCleanup
  have hContinueStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 0 .cont targetFinal
          (Structured.EffectSemantics.Outcome.cont targetFinal) :=
    Structured.EffectSemantics.Stmt.Eval.cont
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := [Structured.Stmt.code cleanup, Structured.Stmt.cont] }
        target
        (Structured.EffectSemantics.Outcome.cont targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code
        (fuel := 1) hCleanupRun)
      (Structured.EffectSemantics.Block.Eval.cons_cont hContinueStmt)
  have hSource :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.cont
      (contract := contract) (transcript := transcript)
      (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
      (source := source) hSourceScope).run_eq
  refine ⟨targetFinal, hSource, ?_, ActivationOutcomeRel.cont hFinalRel⟩
  simpa [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] using hTarget

theorem backward_of_compilers
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {targetFuel : Nat}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : localsCtx.continueDepth? = some targetDepth)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan beforeLive beforeMode)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hWF : plan.WellFormed)
    (hDefined : LiveDefined beforeLive source.source)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .cont =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target
        (Structured.EffectSemantics.Outcome.cont targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx 0 .cont source =
      .ok
        (Functions.Source.Effectful.Outcome.cont
          ((Functions.ObserverSemantics.stateModel transcript).restrictTo
            afterLive source),
          sourceCtx) ∧
    ActivationOutcomeRel contract plan afterLive 0 frameBase afterMode
      (Functions.Source.Effectful.Outcome.cont
        ((Functions.ObserverSemantics.stateModel transcript).restrictTo
          afterLive source))
      (Structured.EffectSemantics.Outcome.cont targetFinal) := by
  obtain ⟨cleanup, hCleanup, rfl, rfl, rfl, rfl⟩ :=
    compiler_shape hTargetDepth hLower hCompile
  simp only [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] at hTarget
  cases hTarget with
  | cons_regular hCleanupStmt hTail =>
      cases hCleanupStmt with
      | code hCleanupRun =>
          cases hTail with
          | cons_regular hContinue _hRest =>
              cases hContinue
          | cons_cont hContinue =>
              cases hContinue
              have hFinalRel :=
                Plain.backward hCtx hTransition hWF hDefined hRel
                  hCleanup hCleanupRun
              have hSource :=
                (AllocationObserverSafety.Stmt.LeafMemorySafeRun.cont
                  (contract := contract) (transcript := transcript)
                  (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
                  (source := source) hSourceScope).run_eq
              exact ⟨hSource, ActivationOutcomeRel.cont hFinalRel⟩
  | cons_cont hCleanupStmt =>
      cases hCleanupStmt

end ContinueLeaf

end AllocationObserverCleanup
end Functions
end EvmCompiler
