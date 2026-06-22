import EvmCompiler.Functions.AllocationInteractionCleanup
import EvmCompiler.Functions.AllocationInteractionExpressionRecursive
import EvmCompiler.Functions.AllocationInteractionComposition

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionLeave

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionCleanup

namespace ReturnValues

private theorem openEval_cast
    {left right : Nat} (h : left = right)
    {exprs : Locals.ExprSeq left} {source : SourceState} :
    Functions.InteractionSemantics.ExprSeq.openEval
        (cast (congrArg Locals.ExprSeq h) exprs) source =
      Functions.InteractionSemantics.ExprSeq.openEval exprs source := by
  cases h
  rfl

theorem openEval
    {returns : List Functions.Name} {values : List Assembly.Word}
    {source : SourceState}
    (hLookup :
      Functions.Source.Store.lookupMany returns source.vars = some values) :
    Functions.InteractionSemantics.ExprSeq.openEval
        (Functions.Lower.returnExprs returns) source =
      .done (.ok (source, values)) := by
  induction returns generalizing values with
  | nil =>
      simp [Functions.Source.Store.lookupMany] at hLookup
      subst values
      rfl
  | cons name returns ih =>
      unfold Functions.Source.Store.lookupMany at hLookup
      cases hValue : source.vars name with
      | none => simp [hValue] at hLookup
      | some value =>
          cases hTail :
              Functions.Source.Store.lookupMany returns source.vars with
          | none => simp [hValue, hTail] at hLookup
          | some tailValues =>
              simp [hValue, hTail] at hLookup
              subst values
              unfold Functions.Lower.returnExprs
              let exprs : Locals.ExprSeq (1 + returns.length) :=
                Locals.ExprSeq.cons (.var name)
                  (Functions.Lower.returnExprs returns)
              have hLen : 1 + returns.length = returns.length + 1 := by omega
              change
                Functions.InteractionSemantics.ExprSeq.openEval
                    (cast (congrArg Locals.ExprSeq hLen) exprs) source =
                  .done (.ok (source, value :: tailValues))
              rw [openEval_cast hLen]
              have hTailOpen := ih hTail
              unfold Functions.InteractionSemantics.ExprSeq.openEval
                Locals.InteractionSemantics.ExprSeq.openEval at hTailOpen
              unfold Functions.InteractionSemantics.ExprSeq.openEval
                Locals.InteractionSemantics.ExprSeq.openEval
              simp only [exprs,
                Locals.Source.Effectful.Expr.Control.ExprSeq.eval,
                Locals.Source.Effectful.Expr.Control.eval]
              change
                (do
                  let headResult ←
                    (match source.vars name with
                    | some headValue => pure (source, [headValue])
                    | none =>
                        throw
                          EvmYul.EVM.ExecutionException.InvalidInstruction)
                  let tailResult ←
                    Locals.Source.Effectful.Expr.Control.ExprSeq.eval
                      Locals.InteractionSemantics.stateModel
                      Locals.InteractionSemantics.primitiveSemantics
                      (Functions.Lower.returnExprs returns) headResult.1
                  pure
                    (tailResult.1,
                      headResult.2 ++ tailResult.2)) =
                  .done (.ok (source, value :: tailValues))
              rw [hValue]
              change
                (do
                  let tailResult ←
                    Locals.Source.Effectful.Expr.Control.ExprSeq.eval
                      Locals.InteractionSemantics.stateModel
                      Locals.InteractionSemantics.primitiveSemantics
                      (Functions.Lower.returnExprs returns) source
                  pure (tailResult.1, [value] ++ tailResult.2)) =
                  .done (.ok (source, value :: tailValues))
              rw [hTailOpen]
              rfl

private theorem exprSeqSafe_cast
    {contract : MemoryContract.Contract}
    {left right : Nat} (h : left = right)
    {exprs : Locals.ExprSeq left} {source : SourceState}
    (hSafe :
      AllocationInteractionSafety.ExprSeqSafe contract exprs source) :
    AllocationInteractionSafety.ExprSeqSafe contract
      (cast (congrArg Locals.ExprSeq h) exprs) source := by
  cases h
  exact hSafe

theorem safe
    (contract : MemoryContract.Contract)
    {returns live : List Functions.Name} {source : SourceState}
    (hDefined : LiveDefined live source)
    (hSubset : ∀ name, name ∈ returns → name ∈ live) :
    AllocationInteractionSafety.ExprSeqSafe contract
      (Functions.Lower.returnExprs returns) source := by
  induction returns with
  | nil => trivial
  | cons name returns ih =>
      obtain ⟨value, hValue⟩ :=
        hDefined name (hSubset name (by simp))
      unfold Functions.Lower.returnExprs
      let exprs : Locals.ExprSeq (1 + returns.length) :=
        Locals.ExprSeq.cons (.var name)
          (Functions.Lower.returnExprs returns)
      have hLen : 1 + returns.length = returns.length + 1 := by omega
      change
        AllocationInteractionSafety.ExprSeqSafe contract
          (cast (congrArg Locals.ExprSeq hLen) exprs) source
      apply exprSeqSafe_cast hLen
      refine ⟨⟨value, hValue⟩, ?_⟩
      unfold Locals.InteractionSemantics.Expr.openEval
      simp only [Locals.Source.Effectful.Expr.Control.eval]
      change
        Simulation.Interaction.AllDone _
          (match source.vars name with
          | some value => pure (source, [value])
          | none =>
              throw EvmYul.EVM.ExecutionException.InvalidInstruction)
      rw [hValue]
      exact Simulation.Interaction.AllDone.done
        (ih (fun other hOther => hSubset other (by simp [hOther])))

end ReturnValues

/-- `leave` preservation through return-value emission and frame cleanup. -/
theorem leave_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns functionScope live : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hReturnsLive : ∀ name, name ∈ returns → name ∈ live)
    (hReturnsScope : ∀ name, name ∈ returns → name ∈ functionScope)
    (hTargetDepth : localsCtx.leaveDepth? = some 0)
    (hRetc : localsCtx.leaveRetc = returns.length)
    (hReturnFrame : target.returns ≠ [])
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState .leave =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerFinal localsFinal plan
        returns live frameBase mode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel .leave source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 4) { stmts := compiledStmts } target) := by
  obtain ⟨values, hLookup⟩ :=
    lookupMany_of_liveDefined hInvariant.defined hReturnsLive
  have hSafe :=
    ReturnValues.safe contract hInvariant.defined hReturnsLive
  have hScoped :=
    AllocationInteractionCleanup.ReturnValues.returnExprsScoped hReturnsLive
  obtain
      ⟨loweredReturns, returnCode, cleanup,
        hLowerReturns, hLowerSeq, hReturnCode, hCleanup,
        rfl, rfl, rfl, rfl⟩ :=
    LeaveLeaf.compiler_shape hTargetDepth hRetc hLower hCompile
  have hReturnRel :=
    AllocationInteractionExpressionRecursive.forwardExprSeq
      hSafe hInvariant.compiler hScoped hLowerSeq hReturnCode
      hInvariant.state
  have hReturnEval := ReturnValues.openEval hLookup
  rw [hReturnEval] at hReturnRel
  obtain ⟨targetDone, hReturnRun, hReturnDone⟩ :=
    Simulation.Interaction.Rel.done_left hReturnRel
  cases hReturnDone with
  | @ok sourceResult targetAfterReturns hReturnResult =>
      obtain
          ⟨targetFinal, hCleanupRun, hFinalStack,
            hCleanupShared, hCleanupReturns⟩ :=
        Preserving.forward_zero
          (values := values.reverse) (baseStack := target.evm.stack)
          hCleanup
          (by simpa [List.length_reverse] using hReturnResult.valuesLength)
          (by simpa using hInvariant.stackLength)
          hReturnResult.stack
      have hAfterReturns :
          targetAfterReturns.returns = target.returns := by
        have hAll :=
          Structured.InteractionSemantics.Code.openRun_returns
            returnCode target
        rw [hReturnRun] at hAll
        cases hAll with
        | done hDone => exact hDone
      have hFinalFrame : targetFinal.returns ≠ [] := by
        rw [hCleanupReturns, hAfterReturns]
        exact hReturnFrame
      have hLeaveRel :
          LeaveStateRel contract returns
            (source.restrictTo functionScope) targetFinal := by
        refine
          { shared := ?_
            activeNoWrap := ?_
            values := ⟨values, ?_, hFinalStack⟩ }
        · rw [hCleanupShared]
          exact hReturnResult.state.shared
        · rw [hCleanupShared]
          exact hReturnResult.state.activeNoWrap
        · exact
            Functions.Source.Store.lookupMany_restrictTo_of_mem
              hReturnsScope hLookup
      have hSource :
          Functions.InteractionSemantics.Stmt.openRun
              sourceProgram sourceCtx sourceFuel .leave source =
            .done
              (.ok
                (Functions.Source.Effectful.Outcome.leave
                  (source.restrictTo functionScope),
                  sourceCtx)) := by
        unfold Functions.InteractionSemantics.Stmt.openRun
          Functions.Source.Canonical.Stmt.run
        simp only [Functions.Source.Effectful.Control.Stmt.run]
        rw [hSourceScope]
        simp [Functions.InteractionSemantics.stateModel,
          Locals.InteractionSemantics.stateModel,
          Locals.Source.Effectful.Ordinary.stateModel,
          Locals.Source.Effectful.StateModel.restrictTo,
          Simulation.Interaction.pure]
        rfl
      have hTarget :
          Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetExtra + 4)
              { stmts :=
                  [.code returnCode, .code cleanup, .leave] }
              target =
            .done
              (.ok (Structured.EffectSemantics.Outcome.leave targetFinal)) := by
        unfold Expressions.InteractionSemantics.Block.openRun
        simp only [Expressions.EffectSemantics.Control.Block.run,
          Expressions.EffectSemantics.Control.Stmt.run]
        unfold Structured.InteractionSemantics.Code.openRun at hReturnRun
        rw [hReturnRun]
        change
          Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetExtra + 3)
              { stmts := [.code cleanup, .leave] }
              targetAfterReturns =
            .done
              (.ok (Structured.EffectSemantics.Outcome.leave targetFinal))
        exact
          Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_leave
            targetProgram targetExtra cleanup targetAfterReturns targetFinal
              hCleanupRun hFinalFrame
      rw [hSource, hTarget]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      refine ControlResultRel.nonregular (mode := mode) (by simp)
        (SameFrame.refl mode)
        (Functions.Source.Ctx.SameControl.refl sourceCtx) ?_
      exact ActivationOutcomeRel.leave hLeaveRel

end AllocationInteractionLeave
end Functions
end EvmCompiler
