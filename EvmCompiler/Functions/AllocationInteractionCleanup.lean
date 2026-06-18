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

namespace Plain

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
