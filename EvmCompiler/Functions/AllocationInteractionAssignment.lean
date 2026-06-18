import EvmCompiler.Functions.AllocationInteractionDeclaration

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionAssignment

open AllocationInteractionRelation

/-- Exact assignment compiler shape in a scratch-capable activation. -/
inductive CompilerShape
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan) (live : List Locals.Name)
    (frameDepth : Nat) (name : Locals.Name) (value : Functions.Expr 1)
    (loweredStmts : List Locals.Stmt)
    (compiledStmts : List Expressions.Stmt) : Prop where
  | stack
      (slot planDepth depth : Nat)
      (loweredValue : Locals.Expr 1) (valueCode : Structured.Code)
      (op : Structured.BasicOp)
      (hLowerValue :
        AllocationLowering.lowerExpr lowerCtx lowerState value =
          some loweredValue)
      (hCompileValue :
        Locals.Expr.compileCode localsCtx 0 loweredValue = some valueCode)
      (hLocation : plan.location? name = some (.stack planDepth))
      (hCurrentDepth :
        Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
          some (depth + 1))
      (hDepthFrame : depth < frameDepth)
      (hSwap : Locals.StackOp.swap? (depth + 1) = some op)
      (hLowered : loweredStmts = [.assign name loweredValue])
      (hCompiled :
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              (.op op :: .op .pop ::
                Locals.bindLocals 0 localsCtx.layout))]) :
      CompilerShape lowerCtx lowerState localsCtx plan live frameDepth name
        value loweredStmts compiledStmts
  | scratch
      (slot : Nat) (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code) (op : Structured.BasicOp)
      (hLowerValue :
        AllocationLowering.lowerExpr lowerCtx lowerState value =
          some loweredValue)
      (hCompileValue :
        Locals.Expr.compileCode localsCtx 0 loweredValue = some valueCode)
      (hLocation : plan.location? name = some (.scratch slot))
      (hDup : Locals.StackOp.dup? (frameDepth + 2) = some op)
      (hLowered :
        loweredStmts =
          [.expr
            (AllocationLowering.scratchStoreExpr
              lowerCtx.frameName slot loweredValue)])
      (hCompiled :
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              [ .op op,
                .push (AllocationSupport.slotOffset slot),
                .op .add,
                .op .mstore ])]) :
      CompilerShape lowerCtx lowerState localsCtx plan live frameDepth name
        value loweredStmts compiledStmts

/-- Derive the scratch-capable assignment shape from both ordinary passes. -/
theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name} {frameDepth : Nat}
    {name : Locals.Name} {value : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hCtx :
      AllocationContext.ExprContext lowerCtx lowerState localsCtx plan live
        frameDepth)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name value) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    CompilerShape lowerCtx lowerState localsCtx plan live frameDepth name value
        loweredStmts compiledStmts ∧
      lowerFinal = lowerState ∧ localsFinal = localsCtx := by
  obtain ⟨slot, hSlot⟩ := hCtx.slot name hLive
  cases hLowerValue :
      AllocationLowering.lowerExpr lowerCtx lowerState value with
  | none =>
      simp [AllocationLowering.lowerStmt, hSlot, hLowerValue] at hLower
  | some loweredValue =>
      cases hStack : AllocationLowering.isStackSlot lowerCtx slot with
      | true =>
          simp [AllocationLowering.lowerStmt, hSlot, hLowerValue, hStack]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          obtain
              ⟨planDepth, depth, hLocation, hCurrentDepth, hLayoutDepth⟩ :=
            hCtx.stack name slot hLive hSlot hStack
          have hLocalsDepth :
              Locals.Layout.lookupDepth? name localsCtx.layout =
                some (depth + 1) := by
            rw [hCtx.layout]
            exact hLayoutDepth
          cases hValueCode :
              Locals.Expr.compileCode localsCtx 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hLocalsDepth, hValueCode] at hCompile
          | some valueCode =>
              cases hSwap : Locals.StackOp.swap? (depth + 1) with
              | none =>
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    hLocalsDepth, hValueCode, hSwap] at hCompile
              | some op =>
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    Locals.codeStmt, hLocalsDepth, hValueCode, hSwap]
                    at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  exact
                    ⟨.stack slot planDepth depth loweredValue valueCode op
                        hLowerValue hValueCode hLocation hCurrentDepth
                        (hCtx.stack_depth_lt_frame hCurrentDepth)
                        hSwap rfl rfl,
                      rfl, rfl⟩
      | false =>
          obtain ⟨hLocation, hFrameDepth⟩ :=
            hCtx.scratch name slot hLive hSlot hStack
          have hFrameMember : lowerCtx.frameName ∈ lowerState.layout :=
            Locals.Layout.mem_of_lookupDepth?_eq_some hFrameDepth
          simp [AllocationLowering.lowerStmt, hSlot, hLowerValue,
            hStack, hFrameMember] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          have hFrameLocals :
              Locals.Layout.lookupDepth?
                  lowerCtx.frameName localsCtx.layout =
                some (frameDepth + 1) := by
            rw [hCtx.layout]
            exact hFrameDepth
          cases hValueCode :
              Locals.Expr.compileCode localsCtx 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                AllocationLowering.scratchStoreExpr,
                AllocationLowering.scratchAddressExpr,
                AllocationLowering.exprSeqTwo,
                Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                hValueCode, hFrameLocals] at hCompile
          | some valueCode =>
              cases hDup : Locals.StackOp.dup? (frameDepth + 2) with
              | none =>
                  have hDup' :
                      Locals.StackOp.dup? (1 + (frameDepth + 1)) = none := by
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
                      Locals.StackOp.dup? (1 + (frameDepth + 1)) = some op := by
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hDup
                  have hStoreCode :=
                    AllocationLowering.scratchStoreExpr_compileCode
                      (frameName := lowerCtx.frameName) (slot := slot)
                      (offset := 0) hValueCode hFrameLocals hDup'
                  simp only [Locals.Block.compileOpen,
                    Locals.Stmt.compile] at hCompile
                  rw [hStoreCode] at hCompile
                  simp [Locals.codeStmt] at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  exact
                    ⟨.scratch slot loweredValue valueCode op hLowerValue
                        hValueCode hLocation hDup rfl rfl,
                      rfl, rfl⟩

/-- Exact assignment shape for a genuinely stack-only activation. -/
theorem stack_compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {name : Locals.Name} {value : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hCtx :
      AllocationContext.StackExprContext lowerCtx lowerState localsCtx plan
        live)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name value) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ (slot planDepth depth : Nat) (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code) (op : Structured.BasicOp),
      AllocationLowering.lowerExpr lowerCtx lowerState value =
          some loweredValue ∧
        Locals.Expr.compileCode localsCtx 0 loweredValue = some valueCode ∧
        plan.location? name = some (.stack planDepth) ∧
        Locals.Layout.lookupDepth? name (currentStackOrder plan live) =
          some (depth + 1) ∧
        Locals.StackOp.swap? (depth + 1) = some op ∧
        loweredStmts = [.assign name loweredValue] ∧
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              (.op op :: .op .pop ::
                Locals.bindLocals 0 localsCtx.layout))] ∧
        lowerFinal = lowerState ∧ localsFinal = localsCtx := by
  obtain ⟨slot, hSlot⟩ := hCtx.slot name hLive
  cases hLowerValue :
      AllocationLowering.lowerExpr lowerCtx lowerState value with
  | none =>
      simp [AllocationLowering.lowerStmt, hSlot, hLowerValue] at hLower
  | some loweredValue =>
      cases hStack : AllocationLowering.isStackSlot lowerCtx slot with
      | false =>
          simp [AllocationLowering.lowerStmt, hSlot, hLowerValue,
            hStack, hCtx.frameAbsent] at hLower
      | true =>
          simp [AllocationLowering.lowerStmt, hSlot, hLowerValue, hStack]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          obtain
              ⟨planDepth, depth, hLocation, hCurrentDepth, hLayoutDepth⟩ :=
            hCtx.stack name slot hLive hSlot hStack
          have hLocalsDepth :
              Locals.Layout.lookupDepth? name localsCtx.layout =
                some (depth + 1) := by
            rw [hCtx.layout]
            exact hLayoutDepth
          cases hValueCode :
              Locals.Expr.compileCode localsCtx 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hLocalsDepth, hValueCode] at hCompile
          | some valueCode =>
              cases hSwap : Locals.StackOp.swap? (depth + 1) with
              | none =>
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    hLocalsDepth, hValueCode, hSwap] at hCompile
              | some op =>
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    Locals.codeStmt, hLocalsDepth, hValueCode, hSwap]
                    at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  exact
                    ⟨slot, planDepth, depth, loweredValue, valueCode, op,
                      rfl, hValueCode, hLocation, hCurrentDepth, hSwap,
                      rfl, rfl, rfl, rfl⟩

/-- Assignment preservation while a compiler-owned scratch frame is live. -/
theorem scratch_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameDepth frameBase frameWords : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
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
        source target) :
    Simulation.Interaction.Rel
      (AllocationInteractionStatement.OpenStmtResultRel contract lowerCtx
        lowerFinal localsFinal plan live frameBase
          (.scratch frameDepth frameWords) sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx 0 (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram 2 { stmts := compiledStmts } target) := by
  cases hInvariant.compiler with
  | @scratch _ _ hCtx =>
      obtain ⟨hShape, hLowerFinal, hLocalsFinal⟩ :=
        compiler_shape hCtx hLive hLower hCompile
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
            AllocationInteractionExpressionRecursive.forwardExpr
              hSafe (.scratch hCtx) hScoped hLowerValue hCompileValue
              hInvariant.state
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          have hCore :
              Simulation.Interaction.Rel
                (AllocationInteractionStatement.OpenStmtResultRel contract
                  lowerCtx lowerState localsCtx plan live frameBase
                    (.scratch frameDepth frameWords) sourceCtx)
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
                        have hOldAfter :
                            sourceAfterValue.vars name = some old := by
                          rw [hVarsDone, hOld]
                        have hOldTarget :=
                          hResult.state.state.store name (.stack planDepth)
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
                            ⟨targetFinal, hAssignRun, hFinalStack,
                              hShared, _hReturns⟩ :=
                          Locals.InteractionPreservation.Code.openRun_swap_pop
                            hSwap hRestGet hValueStack
                        have hFinalRel :
                            ScratchStateRel contract plan live 0 frameBase
                              frameDepth frameWords
                              (sourceAfterValue.insert name value)
                              targetFinal := by
                          cases hResult.state with
                          | scratch hScratch =>
                              exact hScratch.assign_stack_live hValueStack
                                hFinalStack hShared hLive hLocation
                                hCurrentDepth hDepthFrame hOldAfter
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
                        simp only [Simulation.Interaction.bind, hTailRun]
                        apply Simulation.Interaction.Rel.done
                        apply Simulation.Interaction.ExceptRel.ok
                        refine ⟨rfl,
                          AllocationInteractionStatement.BoundaryOutcomeRel.regular
                            ?_⟩
                        exact
                          { compiler := .scratch hCtx
                            planWF := hInvariant.planWF
                            defined :=
                              (hInvariant.defined.congr_vars
                                hVarsDone).insert_preserves
                            state := .scratch hFinalRel
                            stackLength := by
                              rw [hFinalStack]
                              simpa using hInvariant.stackLength }
          have hCoreNested :
              Simulation.Interaction.Rel
                (AllocationInteractionStatement.OpenStmtResultRel contract
                  lowerCtx lowerState localsCtx plan live frameBase
                    (.scratch frameDepth frameWords) sourceCtx)
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
            AllocationInteractionExpressionRecursive.forwardExpr
              hSafe (.scratch hCtx) hScoped hLowerValue hCompileValue
              hInvariant.state
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          have hCore :
              Simulation.Interaction.Rel
                (AllocationInteractionStatement.OpenStmtResultRel contract
                  lowerCtx lowerState localsCtx plan live frameBase
                    (.scratch frameDepth frameWords) sourceCtx)
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
                        have hOldAfter :
                            sourceAfterValue.vars name = some old := by
                          rw [hVarsDone, hOld]
                        cases hResult.state with
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
                                ⟨targetFinal, hStoreRun, hFinalRel,
                                  hFinalStack⟩ :=
                              AllocationInteractionScratchStore.assignTop
                                hScratch hValueStack hInvariant.planWF
                                (fun other hOther => Or.inr hOther) rfl
                                hLocation hBound hReservation hRegion
                                (by simpa [Nat.add_assoc] using hDup)
                            simp only [Simulation.Interaction.bind, hStoreRun]
                            apply Simulation.Interaction.Rel.done
                            apply Simulation.Interaction.ExceptRel.ok
                            refine ⟨rfl,
                              AllocationInteractionStatement.BoundaryOutcomeRel.regular
                                ?_⟩
                            exact
                              { compiler := .scratch hCtx
                                planWF := hInvariant.planWF
                                defined :=
                                  (hInvariant.defined.congr_vars
                                    hVarsDone).insert_preserves
                                state := .scratch hFinalRel
                                stackLength := by
                                  rw [hFinalStack]
                                  exact hInvariant.stackLength }
          have hCoreNested :
              Simulation.Interaction.Rel
                (AllocationInteractionStatement.OpenStmtResultRel contract
                  lowerCtx lowerState localsCtx plan live frameBase
                    (.scratch frameDepth frameWords) sourceCtx)
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

/-- Assignment preservation for a genuinely stack-only activation. -/
theorem stack_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name} {frameBase : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
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
        localsCtx plan live frameBase .stack source target) :
    Simulation.Interaction.Rel
      (AllocationInteractionStatement.OpenStmtResultRel contract lowerCtx
        lowerFinal localsFinal plan live frameBase .stack sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx 0 (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram 2 { stmts := compiledStmts } target) := by
  cases hInvariant.compiler with
  | stack hCtx =>
      obtain
          ⟨slot, planDepth, depth, loweredValue, valueCode, op,
            hLowerValue, hCompileValue, hLocation, hCurrentDepth, hSwap,
            rfl, rfl, hLowerFinal, hLocalsFinal⟩ :=
        stack_compiler_shape hCtx hLive hLower hCompile
      subst lowerFinal
      subst localsFinal
      obtain ⟨old, hOld⟩ := hInvariant.defined name hLive
      have hContains : source.vars.contains name = true := by
        simp [Locals.Source.Store.contains, hOld]
      have hExpr :=
        AllocationInteractionExpressionRecursive.forwardExpr
          hSafe (.stack hCtx) hScoped hLowerValue hCompileValue
          hInvariant.state
      have hVars :=
        Locals.InteractionStatePreservation.expr_openEval_vars
          valueExpr source
      have hExprStrong :=
        Simulation.Interaction.Rel.strengthen_left hExpr hVars
      have hCore :
          Simulation.Interaction.Rel
            (AllocationInteractionStatement.OpenStmtResultRel contract
              lowerCtx lowerState localsCtx plan live frameBase .stack
              sourceCtx)
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
                    have hOldAfter :
                        sourceAfterValue.vars name = some old := by
                      rw [hVarsDone, hOld]
                    have hOldTarget :=
                      hResult.state.state.store name (.stack planDepth)
                        hLive hLocation
                    rcases hOldTarget with
                      ⟨actualDepth, hActualDepth, hOldTarget⟩
                    have hActualDepthEq : actualDepth = depth := by
                      exact Nat.succ.inj
                        (Option.some.inj
                          (hActualDepth.symm.trans hCurrentDepth))
                    subst actualDepth
                    rw [hValueStack, hOldAfter] at hOldTarget
                    have hRestGet : target.evm.stack[depth]? = some old := by
                      simpa [show 1 + depth = depth + 1 by omega] using
                        hOldTarget
                    obtain
                        ⟨targetFinal, hAssignRun, hFinalStack,
                          hShared, _hReturns⟩ :=
                      Locals.InteractionPreservation.Code.openRun_swap_pop
                        hSwap hRestGet hValueStack
                    have hFinalState :
                        StateRel contract plan live 0 frameBase
                          (sourceAfterValue.insert name value)
                          targetFinal := by
                      exact hResult.state.state.assign_stack_live
                        hValueStack hFinalStack hShared hLive hLocation
                        hCurrentDepth hOldAfter
                    have hFinalActivation :
                        ActivationStateRel contract plan live 0 frameBase
                          .stack (sourceAfterValue.insert name value)
                          targetFinal := by
                      cases hResult.state with
                      | stack hOnly hActive hState =>
                          exact .stack hOnly
                            (by simpa [hShared] using hActive) hFinalState
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
                    simp only [Simulation.Interaction.bind, hTailRun]
                    apply Simulation.Interaction.Rel.done
                    apply Simulation.Interaction.ExceptRel.ok
                    refine ⟨rfl,
                      AllocationInteractionStatement.BoundaryOutcomeRel.regular
                        ?_⟩
                    exact
                      { compiler := .stack hCtx
                        planWF := hInvariant.planWF
                        defined :=
                          (hInvariant.defined.congr_vars
                            hVarsDone).insert_preserves
                        state := hFinalActivation
                        stackLength := by
                          rw [hFinalStack]
                          simpa using hInvariant.stackLength }
      have hCoreNested :
          Simulation.Interaction.Rel
            (AllocationInteractionStatement.OpenStmtResultRel contract
              lowerCtx lowerState localsCtx plan live frameBase .stack
              sourceCtx)
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

/-- Mode-polymorphic assignment preservation for recursive statement proofs. -/
theorem of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
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
        localsCtx plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (AllocationInteractionStatement.OpenStmtResultRel contract lowerCtx
        lowerFinal localsFinal plan live frameBase mode sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx 0 (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram 2 { stmts := compiledStmts } target) := by
  cases mode with
  | stack =>
      exact stack_of_lower_compile hSafe hScoped hLive hLower hCompile
        hInvariant
  | scratch frameDepth frameWords =>
      exact scratch_of_lower_compile hSafe hScoped hLive hLower hCompile
        hInvariant

end AllocationInteractionAssignment
end Functions
end EvmCompiler
