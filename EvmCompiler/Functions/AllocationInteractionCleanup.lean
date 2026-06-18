import EvmCompiler.Functions.AllocationContext
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
