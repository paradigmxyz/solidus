import EvmCompiler.Functions.AllocationContext
import EvmCompiler.Locals.InteractionCleanupPreservation
import EvmCompiler.Locals.InteractionPreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCleanup

open AllocationInteractionRelation

/-- Runtime-representation change induced by compiler-owned stack cleanup. -/
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

namespace ModeTransition

/-- Plain cleanup preserves the activation representation and frame width. -/
theorem sameFrame
    {finalStackDepth targetDepth : Nat}
    {before after : ActivationMode}
    (hTransition :
      ModeTransition finalStackDepth targetDepth before after) :
    SameFrame before after := by
  cases hTransition with
  | stack => exact .stack
  | scratch beforeDepth afterDepth frameWords =>
      exact .scratch beforeDepth afterDepth frameWords

end ModeTransition

/-- Source/allocation-facing transition for `break` and `continue` cleanup. -/
structure Transition
    (plan : Plan) (beforeLive afterLive : List Locals.Name)
    (targetDepth : Nat) (beforeMode afterMode : ActivationMode) where
  dropped : List Locals.Name
  subset : ∀ name, name ∈ afterLive → name ∈ beforeLive
  stackOrder :
    currentStackOrder plan beforeLive =
      dropped ++ currentStackOrder plan afterLive
  mode :
    ModeTransition (currentStackOrder plan afterLive).length targetDepth
      beforeMode afterMode

namespace Transition

theorem sameFrame
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {targetDepth : Nat} {beforeMode afterMode : ActivationMode}
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode) :
    SameFrame beforeMode afterMode :=
  hTransition.mode.sameFrame

theorem targetDepth_eq_stackLength
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {targetDepth : Nat} {beforeMode afterMode : ActivationMode}
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode) :
    targetDepth = afterMode.stackLength plan afterLive := by
  cases hTransition.mode with
  | stack hTarget => simpa [ActivationMode.stackLength] using hTarget
  | scratch beforeDepth afterDepth frameWords hAfter hTarget =>
      simpa [ActivationMode.stackLength] using hTarget

theorem after_matches
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {targetDepth : Nat} {beforeMode afterMode : ActivationMode}
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode) :
    afterMode.Matches plan afterLive := by
  cases hTransition.mode with
  | stack hTarget => trivial
  | scratch beforeDepth afterDepth frameWords hAfter hTarget =>
      exact hAfter

end Transition

namespace Plain

/-- Expose the exact body-plus-cleanup block emitted by `finishScoped`. -/
theorem finishScoped_shape
    {outer final : Locals.Ctx}
    {stmts : List Expressions.Stmt}
    {block : Expressions.Block}
    (hFinish : Locals.finishScoped outer final stmts = some block) :
    ∃ cleanup,
      final.cleanupTo? outer.layout.length = some cleanup ∧
      block.stmts = stmts ++ [Expressions.Stmt.code cleanup] := by
  unfold Locals.finishScoped at hFinish
  cases hCleanup : final.cleanupTo? outer.layout.length with
  | none => simp [hCleanup] at hFinish
  | some cleanup =>
      simp [hCleanup, Locals.codeStmt] at hFinish
      cases hFinish
      exact ⟨cleanup, rfl, rfl⟩

theorem cleanupTo?_shape
    {ctx : Locals.Ctx} {targetDepth : Nat} {code : Structured.Code}
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
Derive lexical cleanup directly from the real open-block lowering extension and
the adjacent compiler contexts.
-/
theorem transition_of_stateExtends
    {lowerCtx : AllocationLowering.Ctx}
    {bodyState outerState : AllocationLowering.State}
    {bodyLocals outerLocals : Locals.Ctx}
    {bodyPlan outerPlan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth : Nat}
    {beforeMode afterMode : ActivationMode}
    (hBody :
      AllocationContext.ActivationExprContext lowerCtx bodyState bodyLocals
        bodyPlan beforeLive beforeMode)
    (hOuter :
      AllocationContext.ActivationExprContext lowerCtx outerState outerLocals
        outerPlan afterLive afterMode)
    (hSubset : ∀ name, name ∈ afterLive → name ∈ beforeLive)
    (hSameFrame : SameFrame beforeMode afterMode)
    (hTargetDepth : targetDepth = outerLocals.layout.length)
    (hExtends :
      AllocationLowering.StateExtends afterLive outerState bodyState) :
    ∃ transition :
      Transition bodyPlan beforeLive afterLive targetDepth
        beforeMode afterMode,
      bodyState.layout = transition.dropped ++ outerState.layout := by
  rcases hExtends with ⟨dropped, hLayout, hFresh, hSlots⟩
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
                have hLive : name ∈ afterLive := by
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
              exact ⟨transition, hLayout⟩
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
                  List.take beforeDepth (dropped ++ outerState.layout) =
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
                have hLive : name ∈ afterLive := by
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
              have hTarget : targetDepth = afterDepth + 1 := by
                calc
                  targetDepth = outerLocals.layout.length := hTargetDepth
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
              exact ⟨transition, hLayout⟩

/--
The exact `POP` sequence emitted by `cleanupTo?` restricts the source lexical
scope and preserves either allocator-selected runtime representation.
-/
theorem forward_exact
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {beforeLive afterLive : List Locals.Name}
    {targetDepth frameBase : Nat}
    {beforeMode afterMode : ActivationMode}
    {source : SourceState} {target : TargetState}
    {cleanup : Structured.Code}
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan beforeLive frameBase beforeMode source target)
    (hTransition :
      Transition plan beforeLive afterLive targetDepth
        beforeMode afterMode)
    (hCleanup : localsCtx.cleanupTo? targetDepth = some cleanup) :
    ∃ targetFinal,
      Structured.InteractionSemantics.Code.openRun cleanup target =
          .done (.ok targetFinal) ∧
        ActivationStateRel contract plan afterLive 0 frameBase afterMode
          (source.restrictTo afterLive) targetFinal ∧
        targetFinal.evm.stack.length = targetDepth := by
  obtain ⟨hTargetDepth, hCleanupCode⟩ := cleanupTo?_shape hCleanup
  have hPopBound :
      localsCtx.layout.length - targetDepth ≤ target.evm.stack.length := by
    rw [hInvariant.stackLength]
    exact Nat.sub_le _ _
  obtain ⟨targetFinal, hRun, hFinalStack, hShared, _hReturns⟩ :=
    Locals.InteractionPreservation.Code.openRun_replicate_pop
      (localsCtx.layout.length - targetDepth) hPopBound
  refine ⟨targetFinal, ?_, ?_, ?_⟩
  · simpa [hCleanupCode] using hRun
  · cases hTransition.mode with
    | stack hFinalDepth =>
        cases hInvariant.compiler with
        | stack hStackCtx =>
            cases hInvariant.state with
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
                  hState.restrict_drop_stack_prefix hInvariant.planWF
                    hTransition.subset hTransition.stackOrder hShared
                    (by simpa [hCount] using hFinalStack)
                exact
                  .stack
                    (fun name slot hLive hLocation =>
                      hOnly name slot
                        (hTransition.subset name hLive) hLocation)
                    (by simpa [hShared] using hActive)
                    hBase
    | scratch beforeDepth afterDepth frameWords hAfterDepth hFinalDepth =>
        cases hInvariant.compiler with
        | scratch hScratchCtx =>
            cases hInvariant.state with
            | scratch hScratch =>
                have hBeforeDepth :
                    beforeDepth =
                      hTransition.dropped.length + afterDepth := by
                  have hBeforeOrder := hScratchCtx.currentStackOrder_length
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
                  hScratch.base.restrict_drop_stack_prefix hInvariant.planWF
                    hTransition.subset hTransition.stackOrder hShared
                    (by simpa [hCount] using hFinalStack)
                have hFramePointer :
                    targetFinal.evm.stack[afterDepth]? =
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
  · rw [hFinalStack, List.length_drop, hInvariant.stackLength]
    omega

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

/-- Cleanup to activation depth zero retains exactly the returned values. -/
theorem forward_zero
    {ctx : Locals.Ctx} {preserve : Nat}
    {cleanup : Structured.Code}
    {values baseStack : List Assembly.Word}
    {target : Structured.RunState}
    (hCleanup : ctx.cleanupToPreserving? preserve 0 = some cleanup)
    (hValuesLength : values.length = preserve)
    (hBaseLength : baseStack.length = ctx.layout.length)
    (hStack : target.evm.stack = values ++ baseStack) :
    ∃ final,
      Structured.InteractionSemantics.Code.openRun cleanup target =
          .done (.ok final) ∧
        final.evm.stack = values ∧
        final.evm.toSharedState = target.evm.toSharedState ∧
        final.returns = target.returns := by
  obtain ⟨_hDepth, hMany⟩ := cleanupToPreserving?_shape hCleanup
  obtain ⟨final, hRun, hFinalStack, hShared, hReturns⟩ :=
    Locals.InteractionCleanupPreservation.openRun_cleanupManyPreserving?
      (discarded := baseStack) (suffix := []) hMany hValuesLength
      (by simpa [hBaseLength]) (by simpa using hStack)
  exact ⟨final, hRun, by simpa using hFinalStack, hShared, hReturns⟩

end Preserving

namespace ReturnValues

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
  | nil => trivial
  | cons name returns ih =>
      unfold Functions.Lower.returnExprs
      let exprs : Locals.ExprSeq (1 + returns.length) :=
        Locals.ExprSeq.cons (.var name)
          (Functions.Lower.returnExprs returns)
      have hLen : 1 + returns.length = returns.length + 1 := by omega
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
      some lowered :=
  hLower

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
      AllocationLowering.lowerReturnExprs lowerCtx lowerState returns =
          some loweredReturns ∧
        AllocationLowering.lowerExprSeq lowerCtx lowerState
            (Functions.Lower.returnExprs returns) =
          some loweredReturns ∧
        Locals.ExprSeq.compileCode localsCtx 0 loweredReturns =
          some returnCode ∧
        localsCtx.cleanupToPreserving? returns.length 0 = some cleanup ∧
        loweredStmts = [.exprs loweredReturns, .leave] ∧
        lowerFinal = lowerState ∧
        compiledStmts = [.code returnCode, .code cleanup, .leave] ∧
        localsFinal = localsCtx := by
  cases hReturns :
      AllocationLowering.lowerReturnExprs lowerCtx lowerState returns with
  | none => simp [AllocationLowering.lowerStmt, hReturns] at hLower
  | some loweredReturns =>
      simp [AllocationLowering.lowerStmt, hReturns] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      have hLowerSeq := ReturnValues.lowerExprSeq hReturns
      cases hReturnCode :
          Locals.ExprSeq.compileCode localsCtx 0 loweredReturns with
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
                Locals.codeStmt, hReturnCode, hDepth, hCleanup] at hCompile
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
    {localsCtx localsFinal : Locals.Ctx} {targetDepth : Nat}
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
        loweredStmts = [.brk] ∧ lowerFinal = lowerState ∧
        compiledStmts = [.code cleanup, .brk] ∧
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

end BreakLeaf

namespace ContinueLeaf

theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx} {targetDepth : Nat}
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
        loweredStmts = [.cont] ∧ lowerFinal = lowerState ∧
        compiledStmts = [.code cleanup, .cont] ∧
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

end ContinueLeaf

end AllocationInteractionCleanup
end Functions
end EvmCompiler
