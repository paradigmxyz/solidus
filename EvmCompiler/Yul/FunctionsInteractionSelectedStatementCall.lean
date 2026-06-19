import EvmCompiler.Yul.FunctionsInteractionPreparedStatement
import EvmCompiler.Yul.CompilerCallDecomposition

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionSelectedStatementCall

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation

/-- Preserve a compiler-selected internal call under an abstract, relation-owned
multi-target writeback policy. Target readiness is stated at call-prelude entry
and transported through the generated argument computation. -/
theorem selectedTargets
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel targetBodyFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {targets finalLayout : List Functions.Name}
    {initial final : Fresh.State}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout
          targets.length (.Call (.inr functionName) args) = true)
    (hTargetsNodup : targets.Nodup)
    (hTargetsReady : ∀ name, name ∈ targets →
      target.vars.contains name = true)
    (hWriteback :
      ∀ {caller : Functions.InteractionSemantics.State}
        {sourceAfter : Yul.InteractionSemantics.State}
        {callAfter : Functions.InteractionSemantics.State}
        {values : List Assembly.Word} {finalVars : Locals.Source.Store},
        ScopedStateRel layout sourceAfter
            { shared := callAfter.shared, vars := caller.vars } →
        Functions.Source.Store.insertMany targets values caller.vars =
          some finalVars →
        ScopedStateRel finalLayout
          (sourceAfter.multifill targets values)
          { shared := callAfter.shared, vars := finalVars })
    (hArgsLowering : Expr.UncheckedCallArgsLowering
      initial args preArgs lowerArgs final)
    (hBound : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (sourceFuel + 1)
      (preArgs.length + targetBodyFuel + 3)
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodyForward : FunctionsInteractionSelectedCall.BodyForwardAt
      profile sourceProgram targetProgram sourceFuel targetBodyFuel)
    (hTargetBodyFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1) ≤ targetBodyFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel finalLayout)
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (sourceFuel + 1)
          args.reverse (some sourceProgram.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.call (sourceFuel + 1)
              argsResult.2.reverse (some functionName)
              (some sourceProgram.contract) argsResult.1)
            (fun callResult =>
              pure (callResult.1.multifill targets callResult.2))))
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx
        (preArgs.length + targetBodyFuel + 3)
        { stmts := preArgs ++
            [.call targets functionName lowerArgs] } target) := by
  obtain ⟨params, returns, body, hLookup⟩ :=
    SolcValidation.exprOk_functionCall_lookup_exists hExprOk
  obtain ⟨before, after, fn, hPrefix, hFind, hFnName,
      hFnParams, hFnReturns, hLowerBody, hReserved⟩ :=
    hDecomposition.findFunction_parts hLookup
  obtain ⟨hResultCount, hArgCount, hSignature⟩ :=
    SolcValidation.programOkWith_functionCall_partsN
      hProgramOk hExprOk hLookup
  have hArgsOk :
      SolcValidation.ExprsOk? profile sourceProgram.contract layout args =
        true :=
    SolcValidation.exprsOk_of_exprOk_functionCall hExprOk hLookup
  have hBodyOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          (fn.returns ++ fn.params) false false true body = true := by
    rw [hFnReturns, hFnParams]
    exact SolcValidation.programOkWith_function_bodyOk hProgramOk hLookup
  have hPrepared :=
    FunctionsInteractionPreparedCall.ofUncheckedCallArgsLowering
      (ctx := ctx) hArgsLowering hArgsOk hBound
      (by omega) hRel hDomain hLayout
      (by omega)
  rw [Functions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind_custom hPrepared
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.revert hState))
  | @regular sourceAfter reversedValues targetAfter ctxAfter
      hStable hScoped _hDomainAfter hExtendsAfter =>
      have hCallStable :
          FunctionsInteractionExpression.StableArgs lowerArgs targetAfter
            reversedValues.reverse := by
        simpa using hStable.reverse
      have hValueLength :
          reversedValues.reverse.length = fn.params.length := by
        calc
          reversedValues.reverse.length = reversedValues.length := by simp
          _ = (lowerArgs.reverse).length := hStable.length
          _ = lowerArgs.length := by simp
          _ = args.length := hArgsLowering.length_lowerArgs_eq
          _ = params.length := hArgCount
          _ = (identNames params).length := by
            simp [identNames_eq_self]
          _ = fn.params.length := by rw [hFnParams]
      obtain ⟨paramStore, hParamStore⟩ :=
        Functions.Source.Store.insertMany_exists_of_length
          (names := fn.params) (values := reversedValues.reverse)
          (store := Locals.Source.Store.empty) hValueLength
      have hFnSignature : (fn.returns ++ fn.params).Nodup := by
        simpa [hFnReturns, hFnParams, identNames_eq_self] using hSignature
      have hFnResultCount : fn.returns.length = targets.length := by
        rw [hFnReturns]
        simpa [identNames_eq_self] using hResultCount.symm
      have hEntry := ScopedStateRel.initcall hScoped.state
        hFnSignature hParamStore
      have hBodyRel := hBodyForward hLowerBody hBodyOk hReserved
        (by
          unfold FunctionsInteractionStaticCost.bodyBudget
          exact
            (FunctionsInteractionFuel.executionBudgetFor_le_global_at
              (FunctionsInteractionStaticCost.program sourceProgram)
              (FunctionsInteractionStaticCost.function_body_le_program_of_lookup
                hLookup) (by omega)).trans hTargetBodyFuel)
        (by
          simpa [hFnParams, hFnReturns, identNames_eq_self,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.source,
            Locals.Source.Effectful.StateModel.withSource]
            using hEntry)
      have hRunBody := FunctionsInteractionCall.runBodyForward
        (program := targetProgram.toFunctions)
        (targetBodyFuel := targetBodyFuel)
        hParamStore hScoped hFnResultCount hBodyRel
        (by
          simp [hFnReturns, identNames_eq_self,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.source,
            Locals.Source.Effectful.StateModel.withSource])
      have hCallRun :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionCall.RunBodyDoneRel layout sourceAfter
              targetAfter targets.length)
            (Yul.InteractionSemantics.call (sourceFuel + 1)
              reversedValues.reverse (some functionName)
              (some sourceProgram.contract) sourceAfter)
            (Functions.InteractionSemantics.FunDef.openRunBody
              targetProgram.toFunctions fn reversedValues.reverse
              (targetBodyFuel + 1) targetAfter) := by
        rw [Yul.InteractionSemantics.Call.explicit_succ
          sourceFuel reversedValues.reverse functionName
          sourceProgram.contract params returns body sourceAfter hLookup]
        simpa [hFnParams, hFnReturns, identNames_eq_self] using hRunBody
      have hContains : ∀ name, name ∈ targets →
          targetAfter.vars.contains name = true := by
        intro name hName
        have hReady := hTargetsReady name hName
        cases hLookup : target.vars name with
        | none =>
            simp [Locals.Source.Store.contains, hLookup] at hReady
        | some value =>
            have hAfter := hExtendsAfter name value hLookup
            simp [Locals.Source.Store.contains, hAfter]
      have hFinished := FunctionsInteractionCall.finishManyForward
        (results := targets.length) (ctx := ctxAfter)
        rfl hContains
        (fun hScopedAfter hInsert => hWriteback hScopedAfter hInsert)
        hCallRun
      have hArgsEval := hCallStable.openEval
        (TargetExtends.refl targetAfter.vars)
      unfold Functions.InteractionSemantics.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval at hArgsEval
      have hStmt :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionStatement.PathScopedDoneRel finalLayout)
            (Simulation.Interaction.bind
              (Yul.InteractionSemantics.call (sourceFuel + 1)
                reversedValues.reverse (some functionName)
                (some sourceProgram.contract) sourceAfter)
              (fun callResult =>
                pure (callResult.1.multifill targets callResult.2)))
            (Functions.InteractionSemantics.Stmt.openRun
              targetProgram.toFunctions ctxAfter (targetBodyFuel + 2)
              (.call targets functionName lowerArgs) targetAfter) := by
        rw [show targetBodyFuel + 2 = (targetBodyFuel + 1) + 1 by omega,
          Functions.InteractionSemantics.Stmt.openRun_call]
        simp only [hTargetsNodup, if_true]
        rw [hArgsEval]
        simp only [Simulation.Interaction.bind_done_ok, hFind,
          Option.elim_some]
        simpa [Functions.InteractionSemantics.FunDef.openRunBody,
          Functions.Source.Canonical.FunDef.runBody] using hFinished
      have hSingleton := FunctionsInteractionStatement.PathScopedDoneRel.singleton
        (targetFuel := targetBodyFuel + 1) hStmt
      have hResidual :
          preArgs.length + targetBodyFuel + 3 - preArgs.length =
            targetBodyFuel + 3 := by
        omega
      simp only
      rw [hResidual]
      simpa using hSingleton

/-- Visible-target specialization used by assignment calls. -/
theorem visibleTargets
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel targetBodyFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {targets : List Functions.Name}
    {initial final : Fresh.State}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout
          targets.length (.Call (.inr functionName) args) = true)
    (hTargetsNodup : targets.Nodup)
    (hTargetsVisible : ∀ name, name ∈ targets → name ∈ layout)
    (hArgsLowering : Expr.UncheckedCallArgsLowering
      initial args preArgs lowerArgs final)
    (hBound : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (sourceFuel + 1)
      (preArgs.length + targetBodyFuel + 3)
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodyForward : FunctionsInteractionSelectedCall.BodyForwardAt
      profile sourceProgram targetProgram sourceFuel targetBodyFuel)
    (hTargetBodyFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1) ≤ targetBodyFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel layout)
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (sourceFuel + 1)
          args.reverse (some sourceProgram.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.call (sourceFuel + 1)
              argsResult.2.reverse (some functionName)
              (some sourceProgram.contract) argsResult.1)
            (fun callResult =>
              pure (callResult.1.multifill targets callResult.2))))
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx
        (preArgs.length + targetBodyFuel + 3)
        { stmts := preArgs ++
            [.call targets functionName lowerArgs] } target) :=
  selectedTargets hDecomposition hProgramOk hExprOk hTargetsNodup
    (fun name hName => hRel.targetContains (hTargetsVisible name hName))
    (fun hScoped hInsert =>
      hScoped.multifill_insertMany_visible
        hTargetsNodup hTargetsVisible hInsert)
    hArgsLowering hBound hBodyForward hTargetBodyFuel hRel hDomain hLayout

/-- Fresh-target specialization used after the compiler's declaration
initialization prefix. -/
theorem freshTargets
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel targetBodyFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {targets : List Functions.Name}
    {initial final : Fresh.State}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout
          targets.length (.Call (.inr functionName) args) = true)
    (hTargetsNodup : targets.Nodup)
    (hTargetsFresh : ∀ name, name ∈ targets → name ∉ layout)
    (hTargetsReady : ∀ name, name ∈ targets →
      target.vars.contains name = true)
    (hArgsLowering : Expr.UncheckedCallArgsLowering
      initial args preArgs lowerArgs final)
    (hBound : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (sourceFuel + 1)
      (preArgs.length + targetBodyFuel + 3)
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodyForward : FunctionsInteractionSelectedCall.BodyForwardAt
      profile sourceProgram targetProgram sourceFuel targetBodyFuel)
    (hTargetBodyFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1) ≤ targetBodyFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel (targets ++ layout))
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs (sourceFuel + 1)
          args.reverse (some sourceProgram.contract) source)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.call (sourceFuel + 1)
              argsResult.2.reverse (some functionName)
              (some sourceProgram.contract) argsResult.1)
            (fun callResult =>
              pure (callResult.1.multifill targets callResult.2))))
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx
        (preArgs.length + targetBodyFuel + 3)
        { stmts := preArgs ++
            [.call targets functionName lowerArgs] } target) :=
  selectedTargets hDecomposition hProgramOk hExprOk hTargetsNodup
    hTargetsReady
    (fun hScoped hInsert =>
      hScoped.multifill_insertMany
        hTargetsNodup hTargetsFresh hInsert)
    hArgsLowering hBound hBodyForward hTargetBodyFuel hRel hDomain hLayout

/-- Ordinary compiler-selected assignment call, with all generated argument
preludes and multi-result writeback discharged internally. -/
theorem compiledAssignCall
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {names : List EvmYul.Identifier}
    {functionName : Name} {args : List AstExpr}
    {initial final : Fresh.State} {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hStmtOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
        functionNames layout canBreak canContinue canLeave
        (.Assign names (.Call (.inr functionName) args)) = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel initial
          (.Assign names (.Call (.inr functionName) args)) =
        some (lower, final))
    (hHeads : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (sourceFuel + 1) targetFuel
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodies : ∀ bodyTargetFuel,
      FunctionsInteractionSelectedCall.BodyForwardAt
        profile sourceProgram targetProgram sourceFuel bodyTargetFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1) + lower.length + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec (sourceFuel + 3)
        (.Assign names (.Call (.inr functionName) args))
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerEq⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_call_parts hLower
  have hOkParts :
      SolcValidation.assignableList? layout (identNames names) = true ∧
        SolcValidation.ExprOk? profile sourceProgram.contract layout
          names.length (.Call (.inr functionName) args) = true := by
    simpa [SolcValidation.StmtOk?] using hStmtOk
  have hAssignParts :
      (identNames names).Nodup ∧
        (∀ name, name ∈ identNames names → name ∈ layout) := by
    have hAssignable := hOkParts.1
    simp [SolcValidation.assignableList?, SolcValidation.nonemptyNames?,
      SolcValidation.namesNodup?, SolcValidation.namesIn?] at hAssignable
    exact ⟨hAssignable.2.1, hAssignable.2.2⟩
  have hFuelEq :
      preArgs.length + (targetFuel - preArgs.length - 3) + 3 =
        targetFuel := by
    rw [hLowerEq] at hTargetFuel
    simp only [List.length_append, List.length_cons, List.length_nil]
      at hTargetFuel
    omega
  have hHeads' : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (sourceFuel + 1)
      (preArgs.length + (targetFuel - preArgs.length - 3) + 3)
      (some sourceProgram.contract) targetProgram.toFunctions layout := by
    rw [hFuelEq]
    exact hHeads
  have hSelected := visibleTargets
    (sourceFuel := sourceFuel)
    (targetBodyFuel := targetFuel - preArgs.length - 3)
    (targets := identNames names) (ctx := ctx)
    hDecomposition hProgramOk
    (by simpa [identNames_eq_self] using hOkParts.2)
    hAssignParts.1 hAssignParts.2 hArgsLowering hHeads'
    (hBodies _)
    (by
      rw [hLowerEq] at hTargetFuel
      simp only [List.length_append, List.length_cons, List.length_nil]
        at hTargetFuel
      omega)
    hRel hDomain hLayout
  have hCheck := hRel.assignmentCheck_many
    hAssignParts.1 hAssignParts.2
  have hCheck' : EvmYul.Yul.checkAssignment source names = .ok () := by
    simpa [identNames_eq_self] using hCheck
  rw [show sourceFuel + 3 = (sourceFuel + 2) + 1 by omega,
    Yul.InteractionSemantics.Exec.assign_succ
      (sourceFuel + 2) names (.Call (.inr functionName) args)
      (some sourceProgram.contract) source hCheck',
    Yul.InteractionSemantics.EvalValues.internal_succ,
    Simulation.Interaction.bind_assoc]
  rw [hLowerEq]
  simpa [hFuelEq, identNames_eq_self] using hSelected

/-- Ordinary compiler-selected declaration call, including the silent
`initNames` prefix required before Functions call writeback. -/
theorem compiledLetCall
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {names : List EvmYul.Identifier}
    {functionName : Name} {args : List AstExpr}
    {initial final : Fresh.State} {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hStmtOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
        functionNames layout canBreak canContinue canLeave
        (.Let names (some (.Call (.inr functionName) args))) = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel initial
          (.Let names (some (.Call (.inr functionName) args))) =
        some (lower, final))
    (hHeads : ∀ recursiveTargetFuel,
      FunctionsInteractionPreparedArgs.RecursiveBoundHeads
        profile sourceProgram (sourceFuel + 1)
        recursiveTargetFuel (some sourceProgram.contract)
        targetProgram.toFunctions layout)
    (hBodies : ∀ bodyTargetFuel,
      FunctionsInteractionSelectedCall.BodyForwardAt
        profile sourceProgram targetProgram sourceFuel bodyTargetFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hTargetsUsed : ∀ name, name ∈ identNames names →
      name ∈ initial.used)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1) + lower.length + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel
        (identNames names ++ layout))
      (Yul.InteractionSemantics.exec (sourceFuel + 3)
        (.Let names (some (.Call (.inr functionName) args)))
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerEq⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_call_parts hLower
  have hLowerGrouped :
      lower = Stmt.initNames (identNames names) ++
        (preArgs ++
          [Functions.Stmt.call (identNames names) functionName lowerArgs]) := by
    simpa only [List.append_assoc] using hLowerEq
  have hOkParts :
      SolcValidation.bindableList? (functionNames ++ layout)
          (identNames names) = true ∧
        SolcValidation.ExprOk? profile sourceProgram.contract layout
          names.length (.Call (.inr functionName) args) = true := by
    simpa [SolcValidation.StmtOk?] using hStmtOk
  have hBindParts :
      (identNames names).Nodup ∧
        (∀ name, name ∈ identNames names → name ∉ layout) := by
    have hBindable := hOkParts.1
    simp [SolcValidation.bindableList?, SolcValidation.nonemptyNames?,
      SolcValidation.bindingNames?, SolcValidation.namesNodup?,
      SolcValidation.namesFresh?] at hBindable
    refine ⟨hBindable.2.2.1, ?_⟩
    intro name hName hLayoutName
    exact (hBindable.2.2.2 name hName).2 hLayoutName
  have hOverallFuel :
      (identNames names).length + 1 ≤ targetFuel := by
    rw [hLowerEq] at hTargetFuel
    simp [Stmt.initNames] at hTargetFuel
    omega
  let extra := targetFuel - (identNames names).length - 1
  have hInitFuel :
      (identNames names).length + extra + 1 = targetFuel := by
    dsimp [extra]
    omega
  obtain ⟨initVars, hInitInsert, hInitRun⟩ :=
    FunctionsInteractionStatement.InitNames.openRun_extra
      (identNames names) targetProgram.toFunctions target ctx extra
  have hInitRun' :
      Functions.InteractionSemantics.Block.openRun
          targetProgram.toFunctions ctx targetFuel
          { stmts := Stmt.initNames (identNames names) } target =
        pure
          (Functions.Source.Effectful.Outcome.regular
            { shared := target.shared, vars := initVars },
            { ctx with
              scope := (identNames names).reverse ++ ctx.scope }) := by
    simpa [hInitFuel] using hInitRun
  let targetInit : Functions.InteractionSemantics.State :=
    { shared := target.shared, vars := initVars }
  let ctxInit : Functions.Source.Ctx :=
    { ctx with scope := (identNames names).reverse ++ ctx.scope }
  have hRelInit : ScopedStateRel layout source targetInit := by
    exact hRel.insertMany_private hBindParts.2 hInitInsert
  have hDomainInit : TargetDomainWithin initial.used targetInit.vars := by
    exact hDomain.insertMany_used hTargetsUsed hInitInsert
  have hReady : ∀ name, name ∈ identNames names →
      targetInit.vars.contains name = true := by
    intro name hName
    exact Functions.Source.Store.insertMany_contains_of_mem
      hBindParts.1 hInitInsert hName
  have hSuffixFuel :
      targetFuel - (Stmt.initNames (identNames names)).length =
        targetFuel - (identNames names).length := by
    simp [Stmt.initNames]
  have hCallFuel :
      preArgs.length +
            (targetFuel - (identNames names).length - preArgs.length - 3) +
          3 =
        targetFuel - (identNames names).length := by
    rw [hLowerEq] at hTargetFuel
    simp [Stmt.initNames] at hTargetFuel
    omega
  have hHeads' : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (sourceFuel + 1)
      (preArgs.length +
        (targetFuel - (identNames names).length - preArgs.length - 3) + 3)
      (some sourceProgram.contract) targetProgram.toFunctions layout := by
    rw [hCallFuel]
    exact hHeads (targetFuel - (identNames names).length)
  have hSelected := freshTargets
    (sourceFuel := sourceFuel)
    (targetBodyFuel :=
      targetFuel - (identNames names).length - preArgs.length - 3)
    (targets := identNames names) (ctx := ctxInit)
    hDecomposition hProgramOk
    (by simpa [identNames_eq_self] using hOkParts.2)
    hBindParts.1 hBindParts.2 hReady hArgsLowering
    hHeads' (hBodies _)
    (by
      rw [hLowerEq] at hTargetFuel
      simp [Stmt.initNames] at hTargetFuel
      omega)
    hRelInit hDomainInit hLayout
  have hCheck := hRel.declarationCheck_many hBindParts.1 hBindParts.2
  have hCheck' : EvmYul.Yul.checkDeclaration source names = .ok () := by
    simpa [identNames_eq_self] using hCheck
  rw [show sourceFuel + 3 = (sourceFuel + 2) + 1 by omega,
    Yul.InteractionSemantics.Exec.let_some_succ
      (sourceFuel + 2) names (.Call (.inr functionName) args)
      (some sourceProgram.contract) source hCheck',
    Yul.InteractionSemantics.EvalValues.internal_succ,
    Simulation.Interaction.bind_assoc]
  rw [hLowerGrouped, Functions.InteractionSemantics.Block.openRun_append,
    hInitRun']
  simp only [Simulation.Interaction.pure,
    Simulation.Interaction.bind_done_ok]
  change
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionStatement.PathScopedDoneRel
        (identNames names ++ layout))
      _
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctxInit
        (targetFuel - (Stmt.initNames (identNames names)).length)
        { stmts := preArgs ++
            [.call (identNames names) functionName lowerArgs] } targetInit)
  rw [hSuffixFuel]
  rw [hCallFuel] at hSelected
  simpa [identNames_eq_self] using hSelected

end FunctionsInteractionSelectedStatementCall
end Yul
end EvmCompiler
