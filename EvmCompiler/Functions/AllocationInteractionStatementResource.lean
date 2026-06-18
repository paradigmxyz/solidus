import EvmCompiler.Functions.AllocationInteractionPrimitiveResource
import EvmCompiler.Functions.AllocationInteractionResource
import EvmCompiler.Functions.AllocationInteractionStatement
import EvmCompiler.Functions.AllocationInteractionAssignment

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionStatementResource

open AllocationInteractionRelation
open AllocationInteractionFrame
open AllocationInteractionResource

/--
An expression statement preserves allocator resources through the ordinary
allocation lowerer and Locals compiler.
-/
theorem expr_of_lower_compile
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {sourceFuel targetExtra frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth mode target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases hLowerExpr :
      AllocationLowering.lowerExpr lowerCtx lowerState expr with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
  | some lowered =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      cases hCode : Locals.Expr.compileCode localsCtx 0 lowered with
      | none =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode]
            at hCompile
      | some code =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode]
            at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          have hExpr :=
            AllocationInteractionExpressionResource.forwardExpr
              (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
                contract)
              hConfig hSafe hInvariant.compiler hScoped hLowerExpr hCode
              hInvariant.state hReady
          simp only [Locals.codeStmt]
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run]
          apply Simulation.Interaction.Rel.bind_custom hExpr
          intro sourceDone targetDone hDone
          cases hDone with
          | error hError => exact .done (.error hError)
          | ok hResult =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact ActivationEffect.of_allocatorEffect hResult.2

/-- Resource preservation for a declaration in a stack-only activation. -/
theorem stack_let_of_lower_compile
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {sourceFuel targetExtra frameBase : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hAfter :
      AllocationContext.StackExprContext lowerCtx afterState afterLocals
        plan (name :: live))
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx beforeState
        beforeLocals plan live frameBase .stack source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth .stack target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases hInvariant.compiler with
  | stack hBefore =>
      obtain
          ⟨loweredValue, valueCode, hLowerValue, hCompileValue,
            _hStackOrder, rfl, rfl, rfl, rfl⟩ :=
        AllocationInteractionStatement.stack_let_compiler_shape
          hBefore hAfter hLower hCompile
      have hExpr :=
        AllocationInteractionExpressionResource.forwardExpr
          (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
            contract)
          hConfig hSafe (.stack hBefore) hScoped hLowerValue hCompileValue
          hInvariant.state hReady
      have hCore :
          Simulation.Interaction.Rel
            (OpenResultRel config allocatorDepth .stack target)
            (Simulation.Interaction.bind
              (Functions.InteractionSemantics.Expr.openEval valueExpr source)
              (fun result =>
                Simulation.Interaction.bind
                  (match result.2 with
                  | [value] =>
                      Simulation.Interaction.pure (result.1, value)
                  | _ =>
                      Simulation.Interaction.error .InvalidInstruction)
                  (fun valueResult =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        (valueResult.1.insert name valueResult.2),
                        { sourceCtx with
                          scope := name :: sourceCtx.scope }))))
            (Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun valueCode target)
              (fun targetAfterValue =>
                Simulation.Interaction.pure
                  (Structured.Outcome.regular targetAfterValue))) := by
        apply Simulation.Interaction.Rel.bind_custom hExpr
        intro sourceDone targetDone hDone
        cases hDone with
        | error hError => exact .done (.error hError)
        | @ok sourceResult targetAfterValue hResult =>
            rcases sourceResult with ⟨sourceAfterValue, values⟩
            cases values with
            | nil =>
                have hLength := hResult.1.valuesLength
                simp at hLength
            | cons value tail =>
                cases tail with
                | cons other rest =>
                    have hLength := hResult.1.valuesLength
                    simp at hLength
                | nil =>
                    apply Simulation.Interaction.Rel.done
                    apply Simulation.Interaction.ExceptRel.ok
                    exact hResult.2
      have hCoreNested :
          Simulation.Interaction.Rel
            (OpenResultRel config allocatorDepth .stack target)
            (Simulation.Interaction.bind
              (Simulation.Interaction.bind
                (Functions.InteractionSemantics.Expr.openEval
                  valueExpr source)
                (fun result =>
                  match result.2 with
                  | [value] =>
                      Simulation.Interaction.pure (result.1, value)
                  | _ =>
                      Simulation.Interaction.error .InvalidInstruction))
              (fun valueResult =>
                Simulation.Interaction.pure
                  (Functions.Source.Effectful.Outcome.regular
                    (valueResult.1.insert name valueResult.2),
                    { sourceCtx with
                      scope := name :: sourceCtx.scope })))
            (Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun valueCode target)
              (fun targetAfterValue =>
                Simulation.Interaction.pure
                  (Structured.Outcome.regular targetAfterValue))) := by
        rw [Simulation.Interaction.bind_assoc]
        exact hCore
      rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run
        Expressions.InteractionSemantics.Stmt.openRun
      simp only [Functions.Source.Effectful.Control.Stmt.run,
        Expressions.EffectSemantics.Control.Stmt.run]
      unfold Locals.Source.Effectful.Expr.Control.evalOne
      change
        Simulation.Interaction.Rel _ _
          (Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun
              (valueCode ++
                Locals.bindLocals 0 (name :: beforeLocals.layout)) target)
            (fun final => Simulation.Interaction.pure
              (Structured.Outcome.regular final)))
      rw [Structured.InteractionSemantics.Code.openRun_append,
        show Locals.bindLocals 0 (name :: beforeLocals.layout) =
          [.bindLocals 0 (name :: beforeLocals.layout)] by rfl]
      have hBindRun :
          Structured.InteractionSemantics.Code.openRun
              [.bindLocals 0 (name :: beforeLocals.layout)] =
            fun state => Simulation.Interaction.pure state := by
        funext state
        exact Locals.InteractionPreservation.Code.openRun_bindLocals
          0 (name :: beforeLocals.layout) state
      rw [hBindRun]
      simpa [Simulation.Interaction.bind,
        Functions.InteractionSemantics.Expr.openEval,
        Locals.InteractionSemantics.Expr.openEval,
        Functions.InteractionSemantics.primitiveSemantics,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.insert] using hCoreNested

/-- Resource preservation for a declaration in a scratch-backed activation. -/
theorem scratch_let_of_lower_compile
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {sourceFuel targetExtra beforeFrameDepth afterFrameDepth frameBase
      frameWords : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hAfter :
      AllocationContext.ExprContext lowerCtx afterState afterLocals plan
        afterLive afterFrameDepth)
    (hScoped : Functions.Scope.ExprScoped beforeLive valueExpr)
    (hAfterLive : afterLive = name :: beforeLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hScratchBound :
      ∀ slot, plan.location? name = some (.scratch slot) →
        slot < frameWords)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx beforeState
        beforeLocals plan beforeLive frameBase
          (.scratch beforeFrameDepth frameWords) source target)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch beforeFrameDepth frameWords)) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth
        (.scratch beforeFrameDepth frameWords) target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases hInvariant.compiler with
  | @scratch _ _ hBefore =>
      have hNameAfter : name ∈ afterLive := by
        simp [hAfterLive]
      have hShape :=
        AllocationInteractionDeclaration.compiler_shape
          hBefore hAfter hNameAfter hNameFrame hLower hCompile
      cases hShape with
      | stack slot planDepth loweredValue valueCode
          hLowerValue hCompileValue hLocation hStackOrder hFrameDepth
          hLowered hAfterState hCompiled hAfterLocals =>
          subst loweredStmts
          subst afterState
          subst compiledStmts
          subst afterLocals
          subst afterLive
          subst afterFrameDepth
          have hExpr :=
            AllocationInteractionExpressionResource.forwardExpr
              (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
                contract)
              hConfig hSafe (.scratch hBefore) hScoped hLowerValue
              hCompileValue hInvariant.state hReady
          have hCore :
              Simulation.Interaction.Rel
                (OpenResultRel config allocatorDepth
                  (.scratch beforeFrameDepth frameWords) target)
                (Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Expr.openEval
                    valueExpr source)
                  (fun result =>
                    Simulation.Interaction.bind
                      (match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error .InvalidInstruction)
                      (fun valueResult =>
                        Simulation.Interaction.pure
                          (Functions.Source.Effectful.Outcome.regular
                            (valueResult.1.insert name valueResult.2),
                            { sourceCtx with
                              scope := name :: sourceCtx.scope }))))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.pure
                      (Structured.Outcome.regular targetAfterValue))) := by
            apply Simulation.Interaction.Rel.bind_custom hExpr
            intro sourceDone targetDone hDone
            cases hDone with
            | error hError => exact .done (.error hError)
            | @ok sourceResult targetAfterValue hResult =>
                rcases sourceResult with ⟨sourceAfterValue, values⟩
                cases values with
                | nil =>
                    have hLength := hResult.1.valuesLength
                    simp at hLength
                | cons value tail =>
                    cases tail with
                    | cons other rest =>
                        have hLength := hResult.1.valuesLength
                        simp at hLength
                    | nil =>
                        apply Simulation.Interaction.Rel.done
                        apply Simulation.Interaction.ExceptRel.ok
                        exact ActivationEffect.of_allocatorEffect hResult.2
          have hCoreNested :
              Simulation.Interaction.Rel
                (OpenResultRel config allocatorDepth
                  (.scratch beforeFrameDepth frameWords) target)
                (Simulation.Interaction.bind
                  (Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Expr.openEval
                      valueExpr source)
                    (fun result =>
                      match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error .InvalidInstruction))
                  (fun valueResult =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        (valueResult.1.insert name valueResult.2),
                        { sourceCtx with
                          scope := name :: sourceCtx.scope })))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.pure
                      (Structured.Outcome.regular targetAfterValue))) := by
            rw [Simulation.Interaction.bind_assoc]
            exact hCore
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run]
          unfold Locals.Source.Effectful.Expr.Control.evalOne
          change
            Simulation.Interaction.Rel _ _
              (Simulation.Interaction.bind
                (Structured.InteractionSemantics.Code.openRun
                  (valueCode ++
                    Locals.bindLocals 0 (name :: beforeLocals.layout))
                  target)
                (fun final => Simulation.Interaction.pure
                  (Structured.Outcome.regular final)))
          rw [Structured.InteractionSemantics.Code.openRun_append,
            show Locals.bindLocals 0 (name :: beforeLocals.layout) =
              [.bindLocals 0 (name :: beforeLocals.layout)] by rfl]
          have hBindRun :
              Structured.InteractionSemantics.Code.openRun
                  [.bindLocals 0 (name :: beforeLocals.layout)] =
                fun state => Simulation.Interaction.pure state := by
            funext state
            exact Locals.InteractionPreservation.Code.openRun_bindLocals
              0 (name :: beforeLocals.layout) state
          rw [hBindRun]
          simpa [Simulation.Interaction.bind,
            Functions.InteractionSemantics.Expr.openEval,
            Locals.InteractionSemantics.Expr.openEval,
            Functions.InteractionSemantics.primitiveSemantics,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.insert] using hCoreNested
      | scratch slot loweredValue valueCode op
          hLowerValue hCompileValue hLocation hDup hStackOrder hFrameDepth
          hLowered hAfterState hCompiled hAfterLocals =>
          subst loweredStmts
          subst afterState
          subst compiledStmts
          subst afterLocals
          subst afterLive
          subst afterFrameDepth
          have hExpr :=
            AllocationInteractionExpressionResource.forwardExpr
              (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
                contract)
              hConfig hSafe (.scratch hBefore) hScoped hLowerValue
              hCompileValue hInvariant.state hReady
          have hCore :
              Simulation.Interaction.Rel
                (OpenResultRel config allocatorDepth
                  (.scratch beforeFrameDepth frameWords) target)
                (Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Expr.openEval
                    valueExpr source)
                  (fun result =>
                    Simulation.Interaction.bind
                      (match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error .InvalidInstruction)
                      (fun valueResult =>
                        Simulation.Interaction.pure
                          (Functions.Source.Effectful.Outcome.regular
                            (valueResult.1.insert name valueResult.2),
                            { sourceCtx with
                              scope := name :: sourceCtx.scope }))))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.bind
                      (Structured.InteractionSemantics.Code.openRun
                        [ .op op,
                          .push (AllocationSupport.slotOffset slot),
                          .op .add,
                          .op .mstore ] targetAfterValue)
                      (fun targetFinal =>
                        Simulation.Interaction.pure
                          (Structured.Outcome.regular targetFinal)))) := by
            apply Simulation.Interaction.Rel.bind_custom hExpr
            intro sourceDone targetDone hDone
            cases hDone with
            | error hError => exact .done (.error hError)
            | @ok sourceResult targetAfterValue hResult =>
                rcases sourceResult with ⟨sourceAfterValue, values⟩
                cases values with
                | nil =>
                    have hLength := hResult.1.valuesLength
                    simp at hLength
                | cons value tail =>
                    cases tail with
                    | cons other rest =>
                        have hLength := hResult.1.valuesLength
                        simp at hLength
                    | nil =>
                        have hValueStack :
                            targetAfterValue.evm.stack =
                              value :: target.evm.stack := by
                          simpa using hResult.1.stack
                        cases hResult.1.state with
                        | scratch hValueScratch =>
                            have hBound := hScratchBound slot hLocation
                            obtain
                                ⟨reservation, hReservation, _hFrameRegion⟩ :=
                              hValueScratch.frameReserved
                            have hRegion :=
                              hValueScratch.scratchAddress_reserved_of_bound
                                hBound hReservation
                            obtain
                                ⟨targetFinal, hStoreRun, _hFinalRel,
                                  _hFinalStack, hFinalMachine⟩ :=
                              AllocationInteractionScratchStore.assignTop
                                hValueScratch hValueStack hInvariant.planWF
                                (by
                                  intro other hOther
                                  simpa using hOther)
                                hStackOrder hLocation hBound hReservation
                                hRegion
                                (by simpa [Nat.add_assoc] using hDup)
                            have hStoreBounded :=
                              hOwned.boundedEffect_of_scratchStoreSlot
                                hConfig hValueScratch hBound hResult.2.ready
                                hFinalMachine
                            have hStoreEffect :
                                ActivationEffect config allocatorDepth
                                  (.scratch beforeFrameDepth frameWords)
                                  targetAfterValue targetFinal :=
                              ActivationEffect.of_boundedEffect hStoreBounded
                            simp only [Simulation.Interaction.bind, hStoreRun]
                            apply Simulation.Interaction.Rel.done
                            apply Simulation.Interaction.ExceptRel.ok
                            exact ActivationEffect.trans
                              (ActivationEffect.of_allocatorEffect hResult.2)
                              hStoreEffect
          have hCoreNested :
              Simulation.Interaction.Rel
                (OpenResultRel config allocatorDepth
                  (.scratch beforeFrameDepth frameWords) target)
                (Simulation.Interaction.bind
                  (Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Expr.openEval
                      valueExpr source)
                    (fun result =>
                      match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error .InvalidInstruction))
                  (fun valueResult =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        (valueResult.1.insert name valueResult.2),
                        { sourceCtx with
                          scope := name :: sourceCtx.scope })))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.bind
                      (Structured.InteractionSemantics.Code.openRun
                        [ .op op,
                          .push (AllocationSupport.slotOffset slot),
                          .op .add,
                          .op .mstore ] targetAfterValue)
                      (fun targetFinal =>
                        Simulation.Interaction.pure
                          (Structured.Outcome.regular targetFinal)))) := by
            rw [Simulation.Interaction.bind_assoc]
            exact hCore
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run]
          unfold Locals.Source.Effectful.Expr.Control.evalOne
          change
            Simulation.Interaction.Rel _ _
              (Simulation.Interaction.bind
                (Structured.InteractionSemantics.Code.openRun
                  (valueCode ++
                    [ .op op,
                      .push (AllocationSupport.slotOffset slot),
                      .op .add,
                      .op .mstore ]) target)
                (fun final => Simulation.Interaction.pure
                  (Structured.Outcome.regular final)))
          rw [Structured.InteractionSemantics.Code.openRun_append,
            Simulation.Interaction.bind_assoc]
          simpa [Simulation.Interaction.bind,
            Functions.InteractionSemantics.Expr.openEval,
            Locals.InteractionSemantics.Expr.openEval,
            Functions.InteractionSemantics.primitiveSemantics,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.insert] using hCoreNested

/-- Assignment resource preservation while an owned scratch frame is live. -/
theorem scratch_assign_of_lower_compile
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {sourceFuel targetExtra frameDepth frameBase frameWords : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase (.scratch frameDepth frameWords)
        source target)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase
        (.scratch frameDepth frameWords)) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth
        (.scratch frameDepth frameWords) target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases hInvariant.compiler with
  | @scratch _ _ hCtx =>
      obtain ⟨hShape, hLowerFinal, hLocalsFinal⟩ :=
        AllocationInteractionAssignment.compiler_shape
          hCtx hLive hLower hCompile
      subst lowerFinal
      subst localsFinal
      obtain ⟨old, hOld⟩ := hInvariant.defined name hLive
      have hContains : source.vars.contains name = true := by
        simp [Locals.Source.Store.contains, hOld]
      have hVars :=
        Locals.InteractionStatePreservation.expr_openEval_vars
          valueExpr source
      cases hShape with
      | stack slot planDepth depth loweredValue valueCode op
          hLowerValue hCompileValue hLocation hCurrentDepth hDepthFrame
          hSwap hLowered hCompiled =>
          subst loweredStmts
          subst compiledStmts
          have hExpr :=
            AllocationInteractionExpressionResource.forwardExpr
              (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
                contract)
              hConfig hSafe (.scratch hCtx) hScoped hLowerValue hCompileValue
              hInvariant.state hReady
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          have hCore :
              Simulation.Interaction.Rel
                (OpenResultRel config allocatorDepth
                  (.scratch frameDepth frameWords) target)
                (Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Expr.openEval
                    valueExpr source)
                  (fun result =>
                    Simulation.Interaction.bind
                      (match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error .InvalidInstruction)
                      (fun valueResult =>
                        Simulation.Interaction.pure
                          (Functions.Source.Effectful.Outcome.regular
                            (valueResult.1.insert name valueResult.2),
                            sourceCtx))))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.bind
                      (Structured.InteractionSemantics.Code.openRun
                        (.op op :: .op .pop ::
                          Locals.bindLocals 0 localsCtx.layout)
                        targetAfterValue)
                      (fun targetFinal =>
                        Simulation.Interaction.pure
                          (Structured.Outcome.regular targetFinal)))) := by
            apply Simulation.Interaction.Rel.bind_custom hExprStrong
            intro sourceDone targetDone hDone
            rcases hDone with ⟨hRelated, hVarsDone⟩
            cases hRelated with
            | error hError => exact .done (.error hError)
            | @ok sourceResult targetAfterValue hResult =>
                rcases sourceResult with ⟨sourceAfterValue, values⟩
                cases values with
                | nil =>
                    have hLength := hResult.1.valuesLength
                    simp at hLength
                | cons value tail =>
                    cases tail with
                    | cons other rest =>
                        have hLength := hResult.1.valuesLength
                        simp at hLength
                    | nil =>
                        have hValueStack :
                            targetAfterValue.evm.stack =
                              value :: target.evm.stack := by
                          simpa using hResult.1.stack
                        have hOldAfter :
                            sourceAfterValue.vars name = some old := by
                          rw [hVarsDone, hOld]
                        have hOldTarget :=
                          hResult.1.state.state.store name (.stack planDepth)
                            hLive hLocation
                        rcases hOldTarget with
                          ⟨actualDepth, hActualDepth, hOldTarget⟩
                        have hActualDepthEq : actualDepth = depth := by
                          exact Nat.succ.inj
                            (Option.some.inj
                              (hActualDepth.symm.trans hCurrentDepth))
                        subst actualDepth
                        rw [hValueStack, hOldAfter] at hOldTarget
                        have hRestGet :
                            target.evm.stack[depth]? = some old := by
                          simpa [show 1 + depth = depth + 1 by omega] using
                            hOldTarget
                        obtain
                            ⟨targetFinal, hAssignRun, _hFinalStack,
                              hShared, _hReturns⟩ :=
                          Locals.InteractionPreservation.Code.openRun_swap_pop
                            hSwap hRestGet hValueStack
                        have hBindRun :
                            Structured.InteractionSemantics.Code.openRun
                                (Locals.bindLocals 0 localsCtx.layout)
                                targetFinal =
                              Simulation.Interaction.pure targetFinal := by
                          simpa [Locals.bindLocals] using
                            Locals.InteractionPreservation.Code.openRun_bindLocals
                              0 localsCtx.layout targetFinal
                        have hTailRun :
                            Structured.InteractionSemantics.Code.openRun
                                (.op op :: .op .pop ::
                                  Locals.bindLocals 0 localsCtx.layout)
                                targetAfterValue =
                              .done (.ok targetFinal) := by
                          change
                            Structured.InteractionSemantics.Code.openRun
                                ([.op op, .op .pop] ++
                                  Locals.bindLocals 0 localsCtx.layout)
                                targetAfterValue =
                              .done (.ok targetFinal)
                          rw [Structured.InteractionSemantics.Code.openRun_append,
                            hAssignRun]
                          exact hBindRun
                        have hTailMachine :
                            targetFinal.evm.toMachineState =
                              targetAfterValue.evm.toMachineState :=
                          congrArg EvmYul.SharedState.toMachineState hShared
                        have hTailEffect :=
                          AllocatorEffect.of_machine_eq hResult.2.ready
                            hTailMachine
                        simp only [Simulation.Interaction.bind, hTailRun]
                        apply Simulation.Interaction.Rel.done
                        apply Simulation.Interaction.ExceptRel.ok
                        exact ActivationEffect.of_allocatorEffect
                          (hResult.2.trans hTailEffect)
          have hCoreNested :
              Simulation.Interaction.Rel
                (OpenResultRel config allocatorDepth
                  (.scratch frameDepth frameWords) target)
                (Simulation.Interaction.bind
                  (Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Expr.openEval
                      valueExpr source)
                    (fun result =>
                      match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error .InvalidInstruction))
                  (fun valueResult =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        (valueResult.1.insert name valueResult.2), sourceCtx)))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.bind
                      (Structured.InteractionSemantics.Code.openRun
                        (.op op :: .op .pop ::
                          Locals.bindLocals 0 localsCtx.layout)
                        targetAfterValue)
                      (fun targetFinal =>
                        Simulation.Interaction.pure
                          (Structured.Outcome.regular targetFinal)))) := by
            rw [Simulation.Interaction.bind_assoc]
            exact hCore
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.vars, id_eq,
            hContains, ↓reduceIte]
          unfold Locals.Source.Effectful.Expr.Control.evalOne
          change
            Simulation.Interaction.Rel _ _
              (Simulation.Interaction.bind
                (Structured.InteractionSemantics.Code.openRun
                  (valueCode ++
                    (.op op :: .op .pop ::
                      Locals.bindLocals 0 localsCtx.layout)) target)
                (fun final => Simulation.Interaction.pure
                  (Structured.Outcome.regular final)))
          rw [Structured.InteractionSemantics.Code.openRun_append,
            Simulation.Interaction.bind_assoc]
          simpa [Simulation.Interaction.bind,
            Functions.InteractionSemantics.Expr.openEval,
            Locals.InteractionSemantics.Expr.openEval,
            Functions.InteractionSemantics.primitiveSemantics,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.withVars,
            Locals.Source.State.withVars,
            Locals.Source.Effectful.StateModel.insert] using hCoreNested
      | scratch slot loweredValue valueCode op hLowerValue hCompileValue
          hLocation hDup hLowered hCompiled =>
          subst loweredStmts
          subst compiledStmts
          have hExpr :=
            AllocationInteractionExpressionResource.forwardExpr
              (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
                contract)
              hConfig hSafe (.scratch hCtx) hScoped hLowerValue hCompileValue
              hInvariant.state hReady
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          have hCore :
              Simulation.Interaction.Rel
                (OpenResultRel config allocatorDepth
                  (.scratch frameDepth frameWords) target)
                (Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Expr.openEval
                    valueExpr source)
                  (fun result =>
                    Simulation.Interaction.bind
                      (match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error .InvalidInstruction)
                      (fun valueResult =>
                        Simulation.Interaction.pure
                          (Functions.Source.Effectful.Outcome.regular
                            (valueResult.1.insert name valueResult.2),
                            sourceCtx))))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.bind
                      (Structured.InteractionSemantics.Code.openRun
                        [ .op op,
                          .push (AllocationSupport.slotOffset slot),
                          .op .add,
                          .op .mstore ] targetAfterValue)
                      (fun targetFinal =>
                        Simulation.Interaction.pure
                          (Structured.Outcome.regular targetFinal)))) := by
            apply Simulation.Interaction.Rel.bind_custom hExprStrong
            intro sourceDone targetDone hDone
            rcases hDone with ⟨hRelated, _hVarsDone⟩
            cases hRelated with
            | error hError => exact .done (.error hError)
            | @ok sourceResult targetAfterValue hResult =>
                rcases sourceResult with ⟨sourceAfterValue, values⟩
                cases values with
                | nil =>
                    have hLength := hResult.1.valuesLength
                    simp at hLength
                | cons value tail =>
                    cases tail with
                    | cons other rest =>
                        have hLength := hResult.1.valuesLength
                        simp at hLength
                    | nil =>
                        have hValueStack :
                            targetAfterValue.evm.stack =
                              value :: target.evm.stack := by
                          simpa using hResult.1.stack
                        cases hResult.1.state with
                        | scratch hScratch =>
                            have hBound :=
                              hScratch.scratchBound name slot hLive hLocation
                            obtain
                                ⟨reservation, hReservation, _hFrameRegion⟩ :=
                              hScratch.frameReserved
                            have hRegion :=
                              hScratch.scratchAddress_reserved_of_bound
                                hBound hReservation
                            obtain
                                ⟨targetFinal, hStoreRun, _hFinalRel,
                                  _hFinalStack, hFinalMachine⟩ :=
                              AllocationInteractionScratchStore.assignTop
                                hScratch hValueStack hInvariant.planWF
                                (fun other hOther => Or.inr hOther) rfl
                                hLocation hBound hReservation hRegion
                                (by simpa [Nat.add_assoc] using hDup)
                            have hStoreBounded :=
                              hOwned.boundedEffect_of_scratchStore
                                hConfig hScratch hLive hLocation
                                hResult.2.ready hFinalMachine
                            have hStoreEffect :
                                ActivationEffect config allocatorDepth
                                  (.scratch frameDepth frameWords)
                                  targetAfterValue targetFinal :=
                              ActivationEffect.of_boundedEffect hStoreBounded
                            simp only [Simulation.Interaction.bind, hStoreRun]
                            apply Simulation.Interaction.Rel.done
                            apply Simulation.Interaction.ExceptRel.ok
                            exact ActivationEffect.trans
                              (ActivationEffect.of_allocatorEffect hResult.2)
                              hStoreEffect
          have hCoreNested :
              Simulation.Interaction.Rel
                (OpenResultRel config allocatorDepth
                  (.scratch frameDepth frameWords) target)
                (Simulation.Interaction.bind
                  (Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Expr.openEval
                      valueExpr source)
                    (fun result =>
                      match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error .InvalidInstruction))
                  (fun valueResult =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        (valueResult.1.insert name valueResult.2), sourceCtx)))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.bind
                      (Structured.InteractionSemantics.Code.openRun
                        [ .op op,
                          .push (AllocationSupport.slotOffset slot),
                          .op .add,
                          .op .mstore ] targetAfterValue)
                      (fun targetFinal =>
                        Simulation.Interaction.pure
                          (Structured.Outcome.regular targetFinal)))) := by
            rw [Simulation.Interaction.bind_assoc]
            exact hCore
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.vars, id_eq,
            hContains, ↓reduceIte]
          unfold Locals.Source.Effectful.Expr.Control.evalOne
          change
            Simulation.Interaction.Rel _ _
              (Simulation.Interaction.bind
                (Structured.InteractionSemantics.Code.openRun
                  (valueCode ++
                    [ .op op,
                      .push (AllocationSupport.slotOffset slot),
                      .op .add,
                      .op .mstore ]) target)
                (fun final => Simulation.Interaction.pure
                  (Structured.Outcome.regular final)))
          rw [Structured.InteractionSemantics.Code.openRun_append,
            Simulation.Interaction.bind_assoc]
          simpa [Simulation.Interaction.bind,
            Functions.InteractionSemantics.Expr.openEval,
            Locals.InteractionSemantics.Expr.openEval,
            Functions.InteractionSemantics.primitiveSemantics,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.withVars,
            Locals.Source.State.withVars,
            Locals.Source.Effectful.StateModel.insert] using hCoreNested

/-- Assignment resource preservation for a genuinely stack-only activation. -/
theorem stack_assign_of_lower_compile
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {sourceFuel targetExtra frameBase : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase .stack source target)
    (hReady : AllocatorReady config allocatorDepth target) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth .stack target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases hInvariant.compiler with
  | stack hCtx =>
      obtain
          ⟨slot, planDepth, depth, loweredValue, valueCode, op,
            hLowerValue, hCompileValue, hLocation, hCurrentDepth, hSwap,
            rfl, rfl, hLowerFinal, hLocalsFinal⟩ :=
        AllocationInteractionAssignment.stack_compiler_shape
          hCtx hLive hLower hCompile
      subst lowerFinal
      subst localsFinal
      obtain ⟨old, hOld⟩ := hInvariant.defined name hLive
      have hContains : source.vars.contains name = true := by
        simp [Locals.Source.Store.contains, hOld]
      have hVars :=
        Locals.InteractionStatePreservation.expr_openEval_vars
          valueExpr source
      have hExpr :=
        AllocationInteractionExpressionResource.forwardExpr
          (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
            contract)
          hConfig hSafe (.stack hCtx) hScoped hLowerValue hCompileValue
          hInvariant.state hReady
      have hExprStrong :=
        Simulation.Interaction.Rel.strengthen_left hExpr hVars
      have hCore :
          Simulation.Interaction.Rel
            (OpenResultRel config allocatorDepth .stack target)
            (Simulation.Interaction.bind
              (Functions.InteractionSemantics.Expr.openEval valueExpr source)
              (fun result =>
                Simulation.Interaction.bind
                  (match result.2 with
                  | [value] =>
                      Simulation.Interaction.pure (result.1, value)
                  | _ =>
                      Simulation.Interaction.error .InvalidInstruction)
                  (fun valueResult =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        (valueResult.1.insert name valueResult.2),
                        sourceCtx))))
            (Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun valueCode target)
              (fun targetAfterValue =>
                Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    (.op op :: .op .pop ::
                      Locals.bindLocals 0 localsCtx.layout)
                    targetAfterValue)
                  (fun targetFinal =>
                    Simulation.Interaction.pure
                      (Structured.Outcome.regular targetFinal)))) := by
        apply Simulation.Interaction.Rel.bind_custom hExprStrong
        intro sourceDone targetDone hDone
        rcases hDone with ⟨hRelated, hVarsDone⟩
        cases hRelated with
        | error hError => exact .done (.error hError)
        | @ok sourceResult targetAfterValue hResult =>
            rcases sourceResult with ⟨sourceAfterValue, values⟩
            cases values with
            | nil =>
                have hLength := hResult.1.valuesLength
                simp at hLength
            | cons value tail =>
                cases tail with
                | cons other rest =>
                    have hLength := hResult.1.valuesLength
                    simp at hLength
                | nil =>
                    have hValueStack :
                        targetAfterValue.evm.stack =
                          value :: target.evm.stack := by
                      simpa using hResult.1.stack
                    have hOldAfter :
                        sourceAfterValue.vars name = some old := by
                      rw [hVarsDone, hOld]
                    have hOldTarget :=
                      hResult.1.state.state.store name (.stack planDepth)
                        hLive hLocation
                    rcases hOldTarget with
                      ⟨actualDepth, hActualDepth, hOldTarget⟩
                    have hActualDepthEq : actualDepth = depth := by
                      exact Nat.succ.inj
                        (Option.some.inj
                          (hActualDepth.symm.trans hCurrentDepth))
                    subst actualDepth
                    rw [hValueStack, hOldAfter] at hOldTarget
                    have hRestGet :
                        target.evm.stack[depth]? = some old := by
                      simpa [show 1 + depth = depth + 1 by omega] using
                        hOldTarget
                    obtain
                        ⟨targetFinal, hAssignRun, _hFinalStack,
                          hShared, _hReturns⟩ :=
                      Locals.InteractionPreservation.Code.openRun_swap_pop
                        hSwap hRestGet hValueStack
                    have hBindRun :
                        Structured.InteractionSemantics.Code.openRun
                            (Locals.bindLocals 0 localsCtx.layout)
                            targetFinal =
                          Simulation.Interaction.pure targetFinal := by
                      simpa [Locals.bindLocals] using
                        Locals.InteractionPreservation.Code.openRun_bindLocals
                          0 localsCtx.layout targetFinal
                    have hTailRun :
                        Structured.InteractionSemantics.Code.openRun
                            (.op op :: .op .pop ::
                              Locals.bindLocals 0 localsCtx.layout)
                            targetAfterValue =
                          .done (.ok targetFinal) := by
                      change
                        Structured.InteractionSemantics.Code.openRun
                            ([.op op, .op .pop] ++
                              Locals.bindLocals 0 localsCtx.layout)
                            targetAfterValue =
                          .done (.ok targetFinal)
                      rw [Structured.InteractionSemantics.Code.openRun_append,
                        hAssignRun]
                      exact hBindRun
                    have hTailMachine :
                        targetFinal.evm.toMachineState =
                          targetAfterValue.evm.toMachineState :=
                      congrArg EvmYul.SharedState.toMachineState hShared
                    have hTailEffect :=
                      AllocatorEffect.of_machine_eq hResult.2.ready
                        hTailMachine
                    simp only [Simulation.Interaction.bind, hTailRun]
                    apply Simulation.Interaction.Rel.done
                    apply Simulation.Interaction.ExceptRel.ok
                    exact hResult.2.trans hTailEffect
      have hCoreNested :
          Simulation.Interaction.Rel
            (OpenResultRel config allocatorDepth .stack target)
            (Simulation.Interaction.bind
              (Simulation.Interaction.bind
                (Functions.InteractionSemantics.Expr.openEval
                  valueExpr source)
                (fun result =>
                  match result.2 with
                  | [value] =>
                      Simulation.Interaction.pure (result.1, value)
                  | _ =>
                      Simulation.Interaction.error .InvalidInstruction))
              (fun valueResult =>
                Simulation.Interaction.pure
                  (Functions.Source.Effectful.Outcome.regular
                    (valueResult.1.insert name valueResult.2), sourceCtx)))
            (Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun valueCode target)
              (fun targetAfterValue =>
                Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    (.op op :: .op .pop ::
                      Locals.bindLocals 0 localsCtx.layout)
                    targetAfterValue)
                  (fun targetFinal =>
                    Simulation.Interaction.pure
                      (Structured.Outcome.regular targetFinal)))) := by
        rw [Simulation.Interaction.bind_assoc]
        exact hCore
      rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run
        Expressions.InteractionSemantics.Stmt.openRun
      simp only [Functions.Source.Effectful.Control.Stmt.run,
        Expressions.EffectSemantics.Control.Stmt.run,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.vars, id_eq,
        hContains, ↓reduceIte]
      unfold Locals.Source.Effectful.Expr.Control.evalOne
      change
        Simulation.Interaction.Rel _ _
          (Simulation.Interaction.bind
            (Structured.InteractionSemantics.Code.openRun
              (valueCode ++
                (.op op :: .op .pop ::
                  Locals.bindLocals 0 localsCtx.layout)) target)
            (fun final => Simulation.Interaction.pure
              (Structured.Outcome.regular final)))
      rw [Structured.InteractionSemantics.Code.openRun_append,
        Simulation.Interaction.bind_assoc]
      simpa [Simulation.Interaction.bind,
        Functions.InteractionSemantics.Expr.openEval,
        Locals.InteractionSemantics.Expr.openEval,
        Functions.InteractionSemantics.primitiveSemantics,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.withVars,
        Locals.Source.State.withVars,
        Locals.Source.Effectful.StateModel.insert] using hCoreNested

/-- Mode-polymorphic assignment resource preservation. -/
theorem assign_of_lower_compile
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth : Nat} {config : Config}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {sourceFuel targetExtra frameBase : Nat} {mode : ActivationMode}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned : ActivationOwned config allocatorDepth frameBase mode) :
    Simulation.Interaction.Rel
      (OpenResultRel config allocatorDepth mode target)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases mode with
  | stack =>
      exact stack_assign_of_lower_compile hConfig hSafe hScoped hLive
        hLower hCompile hInvariant hReady
  | scratch frameDepth frameWords =>
      exact scratch_assign_of_lower_compile hConfig hSafe hScoped hLive
        hLower hCompile hInvariant hReady hOwned

end AllocationInteractionStatementResource
end Functions
end EvmCompiler
