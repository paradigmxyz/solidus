import EvmCompiler.Yul.FunctionsInteractionPreparedStatement
import EvmCompiler.Yul.CompilerCallDecomposition

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionSelectedStatementCall

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation

/-- Preserve a compiler-selected internal call under an abstract, relation-owned
multi-target writeback policy. Target readiness is stated at call-prelude entry
and transported through the generated argument computation. -/
theorem selectedTargets
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {argsFuel sourceFuel targetBodyFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {targets finalLayout : List Functions.Name}
    {initial final : Fresh.State}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
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
    (hTargetsUsed : ∀ name, name ∈ targets → name ∈ final.used)
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
      profile sourceProgram argsFuel
      (preArgs.length + targetBodyFuel + 3)
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodyForward : FunctionsInteractionSelectedCall.BodyForwardAt
      profile sourceProgram targetProgram sourceFuel targetBodyFuel)
    (hArgsTargetFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram argsFuel ≤ targetBodyFuel)
    (hTargetBodyFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1) ≤ targetBodyFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hTargetScope : TargetScopeWithin initial.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hFinalControl : ControlContextRel sourceScopes finalLayout
      canBreak canContinue canLeave ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used finalLayout sourceScopes
        canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs argsFuel
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
  have hBodyNames : ∀ candidate,
      candidate ∈ Stmt.List.names body → candidate ∈ before.used := by
    intro candidate hCandidate
    apply hPrefix candidate
    change candidate ∈ Contract.names sourceProgram.contract
    exact (Contract.function_names_mem_names_of_lookup hLookup).2
      candidate (by simp [FunctionDefinition.names, hCandidate])
  have hPrepared :=
    FunctionsInteractionPreparedCall.ofUncheckedCallArgsLowering
      (fuel := argsFuel) (ctx := ctx) hArgsLowering hArgsOk hBound
      (by omega) hRel hDomain hTargetScope hLayout
      (by omega)
  rw [Functions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind_custom hPrepared
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done
        (ControlDoneRel.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (ControlDoneRel.terminal (.revert hState))
  | @regular sourceAfter reversedValues targetAfter ctxAfter
      hStable hScoped hDomainAfter hExtendsAfter hScopeCtx hSameCtx
      hTargetScopeAfter =>
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
      have hBodyRel := hBodyForward hLowerBody hBodyOk hReserved hBodyNames
        (by
          unfold FunctionsInteractionStaticCost.bodyBudget
          exact
            (FunctionsInteractionFuel.executionBudgetFor_le_global_at
              (FunctionsInteractionStaticCost.program sourceProgram)
              (FunctionsInteractionStaticCost.function_body_budget_cost_le_program_of_lookup
                hLookup)
              (by omega)).trans hTargetBodyFuel)
        (by
          simpa [hFnParams, hFnReturns, identNames_eq_self,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.source,
            Locals.Source.Effectful.StateModel.withSource]
            using hEntry)
        (by
          simpa [hFnParams, hFnReturns, identNames_eq_self,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.source,
            Locals.Source.Effectful.StateModel.withSource] using
            (FunctionsInteractionSelectedCall.entryTargetDomain
              hParamStore hReserved))
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
      have hControlAfter : ControlContextRel sourceScopes finalLayout
          canBreak canContinue canLeave ctxAfter := by
        apply ControlContextRel.transport hFinalControl
        · exact fun _candidate hMem => hMem
        · exact hSameCtx
        · intro candidate hMem
          exact hScopeCtx candidate
            (hFinalControl.scope candidate hMem)
      have hFinished := FunctionsInteractionCall.finishManyForward
        (results := targets.length) (ctx := ctxAfter)
        rfl hContains hDomainAfter hTargetsUsed
        (fun hScopedAfter hInsert => hWriteback hScopedAfter hInsert)
        hControlAfter hTargetScopeAfter hCallRun
      have hArgsEval := hCallStable.openEval
        (TargetExtends.refl targetAfter.vars)
      unfold Functions.InteractionSemantics.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval at hArgsEval
      have hStmt :
          Simulation.Interaction.ForwardRel Truncated
            (ControlDoneRel final.used finalLayout sourceScopes
              canBreak canContinue canLeave)
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
      have hSingleton := FunctionsInteractionStatement.ControlDoneRel.singleton
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
    {argsFuel sourceFuel targetBodyFuel : Nat}
    {functionName : Name} {args : List AstExpr}
    {targets : List Functions.Name}
    {initial final : Fresh.State}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
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
      profile sourceProgram argsFuel
      (preArgs.length + targetBodyFuel + 3)
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodyForward : FunctionsInteractionSelectedCall.BodyForwardAt
      profile sourceProgram targetProgram sourceFuel targetBodyFuel)
    (hTargetBodyFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1) ≤ targetBodyFuel)
    (hArgsTargetFuel :
      FunctionsInteractionStaticCost.programBudget
        sourceProgram argsFuel ≤ targetBodyFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hTargetScope : TargetScopeWithin initial.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used layout sourceScopes
        canBreak canContinue canLeave)
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs argsFuel
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
    (fun name hName =>
      hArgsLowering.stateExtends
        name (hLayout name (hTargetsVisible name hName)))
    (fun hScoped hInsert =>
      hScoped.multifill_insertMany_visible
        hTargetsNodup hTargetsVisible hInsert)
    hArgsLowering hBound hBodyForward hArgsTargetFuel hTargetBodyFuel
    hRel hDomain hTargetScope
    hLayout
    hControl

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
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
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
    (hTargetsUsed : ∀ name, name ∈ targets → name ∈ final.used)
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
    (hTargetScope : TargetScopeWithin initial.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hControl : ControlContextRel sourceScopes (targets ++ layout)
      canBreak canContinue canLeave ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used (targets ++ layout) sourceScopes
        canBreak canContinue canLeave)
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
    hTargetsReady hTargetsUsed
    (fun hScoped hInsert =>
      hScoped.multifill_insertMany
        hTargetsNodup hTargetsFresh hInsert)
    hArgsLowering hBound hBodyForward hTargetBodyFuel hTargetBodyFuel
    hRel hDomain hTargetScope
    hLayout
    hControl

/-- Ordinary compiler-selected discarded internal call. Argument evaluation
has one more source-fuel step than callee execution in canonical Yul semantics,
so the two recursive budgets remain explicit at this boundary. -/
theorem compiledExprCall
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {functionName : Name} {args : List AstExpr}
    {initial final : Fresh.State} {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hStmtOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
        functionNames layout canBreak canContinue canLeave
        (.ExprStmtCall (.Call (.inr functionName) args)) = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel initial
          (.ExprStmtCall (.Call (.inr functionName) args)) =
        some (lower, final))
    (hHeads : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (sourceFuel + 2) targetFuel
      (some sourceProgram.contract) targetProgram.toFunctions layout)
    (hBodies : ∀ bodyTargetFuel,
      FunctionsInteractionSelectedCall.BodyForwardAt
        profile sourceProgram targetProgram sourceFuel bodyTargetFuel)
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin initial.used target.vars)
    (hTargetScope : TargetScopeWithin initial.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 2) + lower.length + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (sourceFuel + 3)
        (.ExprStmtCall (.Call (.inr functionName) args))
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨preArgs, lowerArgs, hArgsLowering, hLowerEq⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_call_parts hLower
  have hExprOk :
      SolcValidation.ExprOk? profile sourceProgram.contract layout 0
          (.Call (.inr functionName) args) = true := by
    simpa [SolcValidation.StmtOk?] using hStmtOk
  have hFuelEq :
      preArgs.length + (targetFuel - preArgs.length - 3) + 3 =
        targetFuel := by
    rw [hLowerEq] at hTargetFuel
    simp only [List.length_append, List.length_cons, List.length_nil]
      at hTargetFuel
    omega
  have hHeads' : FunctionsInteractionPreparedArgs.RecursiveBoundHeads
      profile sourceProgram (sourceFuel + 2)
      (preArgs.length + (targetFuel - preArgs.length - 3) + 3)
      (some sourceProgram.contract) targetProgram.toFunctions layout := by
    rw [hFuelEq]
    exact hHeads
  have hBodyBudget :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1) ≤
        targetFuel - preArgs.length - 3 := by
    have hMono :
        FunctionsInteractionStaticCost.programBudget
            sourceProgram (sourceFuel + 1) ≤
          FunctionsInteractionStaticCost.programBudget
            sourceProgram (sourceFuel + 2) := by
      exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
    rw [hLowerEq] at hTargetFuel
    simp only [List.length_append, List.length_cons, List.length_nil]
      at hTargetFuel
    omega
  have hArgsBudget :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 2) ≤
        targetFuel - preArgs.length - 3 := by
    rw [hLowerEq] at hTargetFuel
    simp only [List.length_append, List.length_cons, List.length_nil]
      at hTargetFuel
    omega
  have hSelected := visibleTargets
    (argsFuel := sourceFuel + 2)
    (sourceFuel := sourceFuel)
    (targetBodyFuel := targetFuel - preArgs.length - 3)
    (targets := []) (ctx := ctx)
    hDecomposition hProgramOk hExprOk (by simp) (by simp)
    hArgsLowering hHeads' (hBodies _) hBodyBudget hArgsBudget
    hRel hDomain hTargetScope hLayout hControl
  rw [Yul.InteractionSemantics.Exec.expr_internal_succ
    (sourceFuel + 1) functionName args (some sourceProgram.contract) source,
    hLowerEq]
  simpa [hFuelEq] using hSelected

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
    {sourceScopes : SourceScopes}
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
    (hTargetScope : TargetScopeWithin initial.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1) + lower.length + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used layout sourceScopes
        canBreak canContinue canLeave)
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
    (argsFuel := sourceFuel + 1)
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
    (by
      rw [hLowerEq] at hTargetFuel
      simp only [List.length_append, List.length_cons, List.length_nil]
        at hTargetFuel
      omega)
    hRel hDomain hTargetScope hLayout hControl
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
    {sourceScopes : SourceScopes}
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
    (hTargetScope : TargetScopeWithin initial.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetsUsed : ∀ name, name ∈ identNames names →
      name ∈ initial.used)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1) + lower.length + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel final.used (identNames names ++ layout) sourceScopes
        canBreak canContinue canLeave)
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
  have hControlInit : ControlContextRel sourceScopes
      (identNames names ++ layout) canBreak canContinue canLeave ctxInit := by
    apply ControlContextRel.transport hControl
    · intro candidate hMem
      exact List.mem_append_right _ hMem
    · simpa [ctxInit] using
        (Functions.Source.Ctx.SameControl.scopeUpdate ctx
          ((identNames names).reverse ++ ctx.scope))
    · intro candidate hMem
      rcases List.mem_append.mp hMem with hNames | hLayoutName
      · exact List.mem_append_left _ (List.mem_reverse.mpr hNames)
      · exact List.mem_append_right _
          (hControl.scope candidate hLayoutName)
  have hTargetScopeInit : TargetScopeWithin initial.used ctxInit := by
    intro candidate hMem
    change candidate ∈ (identNames names).reverse ++ ctx.scope at hMem
    rcases List.mem_append.mp hMem with hNames | hOuter
    · exact hTargetsUsed candidate (List.mem_reverse.mp hNames)
    · exact hTargetScope candidate hOuter
  have hSelected := freshTargets
    (sourceFuel := sourceFuel)
    (targetBodyFuel :=
      targetFuel - (identNames names).length - preArgs.length - 3)
    (targets := identNames names) (ctx := ctxInit)
    hDecomposition hProgramOk
    (by simpa [identNames_eq_self] using hOkParts.2)
    hBindParts.1 hBindParts.2 hReady
    (fun name hName =>
      hArgsLowering.stateExtends name (hTargetsUsed name hName))
    hArgsLowering
    hHeads' (hBodies _)
    (by
      rw [hLowerEq] at hTargetFuel
      simp [Stmt.initNames] at hTargetFuel
      omega)
    hRelInit hDomainInit hTargetScopeInit hLayout hControlInit
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
      (ControlDoneRel final.used (identNames names ++ layout) sourceScopes
        canBreak canContinue canLeave)
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
