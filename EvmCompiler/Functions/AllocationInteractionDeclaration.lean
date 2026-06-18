import EvmCompiler.Functions.AllocationInteractionScratchStore
import EvmCompiler.Functions.AllocationInteractionStatement

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionDeclaration

open AllocationInteractionRelation

/-- Exact compiler shape for one declaration in a scratch-capable activation. -/
inductive CompilerShape
    (lowerCtx : AllocationLowering.Ctx)
    (beforeState afterState : AllocationLowering.State)
    (beforeLocals afterLocals : Locals.Ctx)
    (plan : Plan) (beforeLive afterLive : List Locals.Name)
    (beforeFrameDepth afterFrameDepth : Nat)
    (name : Locals.Name) (value : Functions.Expr 1)
    (loweredStmts : List Locals.Stmt)
    (compiledStmts : List Expressions.Stmt) : Prop where
  | stack
      (slot planDepth : Nat)
      (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code)
      (hLowerValue :
        AllocationLowering.lowerExpr lowerCtx beforeState value =
          some loweredValue)
      (hCompileValue :
        Locals.Expr.compileCode beforeLocals 0 loweredValue =
          some valueCode)
      (hLocation : plan.location? name = some (.stack planDepth))
      (hStackOrder :
        currentStackOrder plan afterLive =
          name :: currentStackOrder plan beforeLive)
      (hFrameDepth : afterFrameDepth = beforeFrameDepth + 1)
      (hLowered : loweredStmts = [.let_ name loweredValue])
      (hAfterState :
        afterState =
          { allocation :=
              (AllocationSupport.allocateName
                name beforeState.allocation).2
            layout := name :: beforeState.layout })
      (hCompiled :
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              Locals.bindLocals 0 (name :: beforeLocals.layout))])
      (hAfterLocals :
        afterLocals =
          beforeLocals.withLayout (name :: beforeLocals.layout)) :
      CompilerShape lowerCtx beforeState afterState beforeLocals afterLocals
        plan beforeLive afterLive beforeFrameDepth afterFrameDepth name value
        loweredStmts compiledStmts
  | scratch
      (slot : Nat) (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code) (op : Structured.BasicOp)
      (hLowerValue :
        AllocationLowering.lowerExpr lowerCtx beforeState value =
          some loweredValue)
      (hCompileValue :
        Locals.Expr.compileCode beforeLocals 0 loweredValue =
          some valueCode)
      (hLocation : plan.location? name = some (.scratch slot))
      (hDup :
        Locals.StackOp.dup? (beforeFrameDepth + 2) = some op)
      (hStackOrder :
        currentStackOrder plan afterLive =
          currentStackOrder plan beforeLive)
      (hFrameDepth : afterFrameDepth = beforeFrameDepth)
      (hLowered :
        loweredStmts =
          [.expr
            (AllocationLowering.scratchStoreExpr
              lowerCtx.frameName slot loweredValue)])
      (hAfterState :
        afterState =
          { beforeState with
            allocation :=
              (AllocationSupport.allocateName
                name beforeState.allocation).2 })
      (hCompiled :
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              [ .op op,
                .push (AllocationSupport.slotOffset slot),
                .op .add,
                .op .mstore ])])
      (hAfterLocals : afterLocals = beforeLocals) :
      CompilerShape lowerCtx beforeState afterState beforeLocals afterLocals
        plan beforeLive afterLive beforeFrameDepth afterFrameDepth name value
        loweredStmts compiledStmts

/-- Derive the declaration shape from the ordinary allocation and Locals passes. -/
theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {beforeFrameDepth afterFrameDepth : Nat}
    {name : Locals.Name} {value : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hBefore :
      AllocationContext.ExprContext lowerCtx beforeState beforeLocals plan
        beforeLive beforeFrameDepth)
    (hAfter :
      AllocationContext.ExprContext lowerCtx afterState afterLocals plan
        afterLive afterFrameDepth)
    (hNameAfter : name ∈ afterLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name value) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals)) :
    CompilerShape lowerCtx beforeState afterState beforeLocals afterLocals
      plan beforeLive afterLive beforeFrameDepth afterFrameDepth name value
      loweredStmts compiledStmts := by
  have hTransition :=
    AllocationContext.classify_let_transition
      hBefore hAfter hNameAfter hNameFrame hLower
  cases hTransition with
  | stack slot planDepth hSlot hStack hLocation hStackOrder hFrameDepth =>
      subst slot
      cases hLowerValue :
          AllocationLowering.lowerExpr lowerCtx beforeState value with
      | none =>
          simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
      | some loweredValue =>
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          cases hValueCode :
              Locals.Expr.compileCode beforeLocals 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hValueCode] at hCompile
          | some valueCode =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.codeStmt, hValueCode] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              exact
                .stack beforeState.allocation.nextSlot planDepth
                  loweredValue valueCode hLowerValue hValueCode hLocation
                  hStackOrder hFrameDepth rfl rfl rfl rfl
  | scratch slot hSlot hStack hLocation hStackOrder hFrameDepth =>
      subst slot
      cases hLowerValue :
          AllocationLowering.lowerExpr lowerCtx beforeState value with
      | none =>
          simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
      | some loweredValue =>
          have hFrameMember : lowerCtx.frameName ∈ beforeState.layout :=
            Locals.Layout.mem_of_lookupDepth?_eq_some hBefore.frame
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack, hFrameMember] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          cases hValueCode :
              Locals.Expr.compileCode beforeLocals 0 loweredValue with
          | none =>
              have hFrameLocals :
                  Locals.Layout.lookupDepth?
                      lowerCtx.frameName beforeLocals.layout =
                    some (beforeFrameDepth + 1) := by
                rw [hBefore.layout]
                exact hBefore.frame
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                AllocationLowering.scratchStoreExpr,
                AllocationLowering.scratchAddressExpr,
                AllocationLowering.exprSeqTwo,
                Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                hValueCode, hFrameLocals] at hCompile
          | some valueCode =>
              have hFrameLocals :
                  Locals.Layout.lookupDepth?
                      lowerCtx.frameName beforeLocals.layout =
                    some (beforeFrameDepth + 1) := by
                rw [hBefore.layout]
                exact hBefore.frame
              cases hDup :
                  Locals.StackOp.dup? (beforeFrameDepth + 2) with
              | none =>
                  have hDup' :
                      Locals.StackOp.dup?
                          (1 + (beforeFrameDepth + 1)) = none := by
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hDup
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    AllocationLowering.scratchStoreExpr,
                    AllocationLowering.scratchAddressExpr,
                    AllocationLowering.exprSeqTwo,
                    Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                    hValueCode, hFrameLocals, hDup', Nat.add_assoc]
                    at hCompile
              | some op =>
                  have hDup' :
                      Locals.StackOp.dup?
                          (1 + (beforeFrameDepth + 1)) = some op := by
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hDup
                  have hStoreCode :=
                    AllocationLowering.scratchStoreExpr_compileCode
                      (frameName := lowerCtx.frameName)
                      (slot := beforeState.allocation.nextSlot)
                      (offset := 0) hValueCode hFrameLocals hDup'
                  simp only [Locals.Block.compileOpen,
                    Locals.Stmt.compile] at hCompile
                  rw [hStoreCode] at hCompile
                  simp [Locals.codeStmt] at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  exact
                    .scratch beforeState.allocation.nextSlot
                      loweredValue valueCode op hLowerValue hValueCode
                      hLocation hDup hStackOrder hFrameDepth rfl rfl rfl rfl

/--
Preservation of one declaration in a scratch-capable activation. The proof
follows the allocator-selected stack or scratch placement without changing the
shared interaction order.
-/
theorem of_lower_compile
    {contract : MemoryContract.Contract}
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
          (.scratch beforeFrameDepth frameWords) source target) :
    Simulation.Interaction.Rel
      (AllocationInteractionStatement.OpenStmtResultRel contract lowerCtx
        afterState afterLocals plan returns afterLive frameBase
          (.scratch afterFrameDepth frameWords) sourceCtx
        { sourceCtx with scope := name :: sourceCtx.scope })
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases hInvariant.compiler with
  | @scratch _ _ hBefore =>
      have hNameAfter : name ∈ afterLive := by
        simp [hAfterLive]
      have hShape :=
        compiler_shape hBefore hAfter hNameAfter hNameFrame hLower hCompile
      have hVars :=
        Locals.InteractionStatePreservation.expr_openEval_vars valueExpr source
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
            AllocationInteractionExpressionRecursive.forwardExpr
              hSafe (.scratch hBefore) hScoped hLowerValue hCompileValue
              hInvariant.state
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          have hCore :
              Simulation.Interaction.Rel
                (AllocationInteractionStatement.OpenStmtResultRel contract
                  lowerCtx
                  { allocation :=
                      (AllocationSupport.allocateName
                        name beforeState.allocation).2
                    layout := name :: beforeState.layout }
                  (beforeLocals.withLayout
                    (name :: beforeLocals.layout))
                  plan returns (name :: beforeLive) frameBase
                    (.scratch (beforeFrameDepth + 1) frameWords) sourceCtx
                  { sourceCtx with scope := name :: sourceCtx.scope })
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
            apply Simulation.Interaction.Rel.bind_custom hExprStrong
            intro sourceDone targetDone hDone
            rcases hDone with ⟨hRelated, hVarsDone⟩
            cases hRelated with
            | error hError => exact .done (.error hError)
            | @ok sourceResult targetAfterValue hResult =>
                rcases sourceResult with ⟨sourceAfterValue, values⟩
                cases values with
                | nil =>
                    have hLength := hResult.valuesLength
                    simp at hLength
                | cons value tail =>
                    cases tail with
                    | cons other rest =>
                        have hLength := hResult.valuesLength
                        simp at hLength
                    | nil =>
                        have hValueStack :
                            targetAfterValue.evm.stack =
                              value :: target.evm.stack := by
                          simpa using hResult.stack
                        have hFinalState :
                            ActivationStateRel contract plan
                              (name :: beforeLive) 0 frameBase
                              (.scratch (beforeFrameDepth + 1) frameWords)
                              (sourceAfterValue.insert name value)
                              targetAfterValue :=
                          hResult.state.declare_stack_live hValueStack
                            (by
                              intro other hOther
                              simpa using hOther)
                            hLocation hStackOrder
                        apply Simulation.Interaction.Rel.done
                        apply Simulation.Interaction.ExceptRel.ok
                        refine ⟨rfl,
                          AllocationInteractionStatement.BoundaryOutcomeRel.regular
                            ?_⟩
                        exact
                          { compiler := .scratch hAfter
                            planWF := hInvariant.planWF
                            defined :=
                              (hInvariant.defined.congr_vars
                                hVarsDone).insert_cons
                            state := hFinalState
                            stackLength := by
                              simp [hValueStack, Locals.Ctx.withLayout,
                                hInvariant.stackLength] }
          have hCoreNested :
              Simulation.Interaction.Rel
                (AllocationInteractionStatement.OpenStmtResultRel contract
                  lowerCtx
                  { allocation :=
                      (AllocationSupport.allocateName
                        name beforeState.allocation).2
                    layout := name :: beforeState.layout }
                  (beforeLocals.withLayout
                    (name :: beforeLocals.layout))
                  plan returns (name :: beforeLive) frameBase
                    (.scratch (beforeFrameDepth + 1) frameWords) sourceCtx
                  { sourceCtx with scope := name :: sourceCtx.scope })
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
            AllocationInteractionExpressionRecursive.forwardExpr
              hSafe (.scratch hBefore) hScoped hLowerValue hCompileValue
              hInvariant.state
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          have hCore :
              Simulation.Interaction.Rel
                (AllocationInteractionStatement.OpenStmtResultRel contract
                  lowerCtx
                  { beforeState with
                    allocation :=
                      (AllocationSupport.allocateName
                        name beforeState.allocation).2 }
                  beforeLocals plan returns (name :: beforeLive) frameBase
                    (.scratch beforeFrameDepth frameWords) sourceCtx
                  { sourceCtx with scope := name :: sourceCtx.scope })
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
            apply Simulation.Interaction.Rel.bind_custom hExprStrong
            intro sourceDone targetDone hDone
            rcases hDone with ⟨hRelated, hVarsDone⟩
            cases hRelated with
            | error hError => exact .done (.error hError)
            | @ok sourceResult targetAfterValue hResult =>
                rcases sourceResult with ⟨sourceAfterValue, values⟩
                cases values with
                | nil =>
                    have hLength := hResult.valuesLength
                    simp at hLength
                | cons value tail =>
                    cases tail with
                    | cons other rest =>
                        have hLength := hResult.valuesLength
                        simp at hLength
                    | nil =>
                        have hValueStack :
                            targetAfterValue.evm.stack =
                              value :: target.evm.stack := by
                          simpa using hResult.stack
                        cases hResult.state with
                        | scratch hValueScratch =>
                            have hBound := hScratchBound slot hLocation
                            obtain
                                ⟨reservation, hReservation, _hFrameRegion⟩ :=
                              hValueScratch.frameReserved
                            have hRegion :=
                              hValueScratch.scratchAddress_reserved_of_bound
                                hBound hReservation
                            obtain
                                ⟨targetFinal, hStoreRun, hFinalRel,
                                  hFinalStack, _hFinalMachine⟩ :=
                              AllocationInteractionScratchStore.assignTop
                                hValueScratch hValueStack hInvariant.planWF
                                (by
                                  intro other hOther
                                  simpa using hOther)
                                hStackOrder hLocation hBound hReservation
                                hRegion
                                (by simpa [Nat.add_assoc] using hDup)
                            simp only [Simulation.Interaction.bind, hStoreRun]
                            apply Simulation.Interaction.Rel.done
                            apply Simulation.Interaction.ExceptRel.ok
                            refine ⟨rfl,
                              AllocationInteractionStatement.BoundaryOutcomeRel.regular
                                ?_⟩
                            exact
                              { compiler := .scratch hAfter
                                planWF := hInvariant.planWF
                                defined :=
                                  (hInvariant.defined.congr_vars
                                    hVarsDone).insert_cons
                                state := .scratch hFinalRel
                                stackLength := by
                                  rw [hFinalStack]
                                  exact hInvariant.stackLength }
          have hCoreNested :
              Simulation.Interaction.Rel
                (AllocationInteractionStatement.OpenStmtResultRel contract
                  lowerCtx
                  { beforeState with
                    allocation :=
                      (AllocationSupport.allocateName
                        name beforeState.allocation).2 }
                  beforeLocals plan returns (name :: beforeLive) frameBase
                    (.scratch beforeFrameDepth frameWords) sourceCtx
                  { sourceCtx with scope := name :: sourceCtx.scope })
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

end AllocationInteractionDeclaration
end Functions
end EvmCompiler
