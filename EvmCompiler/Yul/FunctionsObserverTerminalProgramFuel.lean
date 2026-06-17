import EvmCompiler.Yul.FunctionsObserverTerminalLoopFuel

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverTerminalFuel

/-!
Recursive-family packaging and the bounded whole-program terminal theorem for
the adjacent Yul-to-Functions pass.
-/

structure RecursiveTerminalProgramBoundedFamily
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop where
  expression :
    RecursiveTerminalExpressionForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile bound
  body :
    RecursiveTerminalBodyForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile bound
  stmt :
    RecursiveTerminalStmtForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile bound
  list :
    RecursiveTerminalListForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile bound
  loop :
    RecursiveTerminalLoopForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile bound

namespace RecursiveTerminalProgramBoundedFamily

theorem ofCompiler
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true) :
    ∀ bound,
      RecursiveTerminalProgramBoundedFamily
        contract transcript codeRel sourceProgram targetProgram profile
        bound := by
  intro bound
  induction bound with
  | zero =>
      refine
        { expression := ?_
          body := ?_
          stmt := ?_
          list := ?_
          loop := ?_ }
      · simp [RecursiveTerminalExpressionForwardProgramBounded]
      · simp [RecursiveTerminalBodyForwardProgramBounded]
      · simp [RecursiveTerminalStmtForwardProgramBounded]
      · simp [RecursiveTerminalListForwardProgramBounded]
      · simp [RecursiveTerminalLoopForwardProgramBounded]
  | succ bound ih =>
      have regular :=
        FunctionsObserverForwardFuel.RecursiveForwardProgramBoundedFamily.ofCompiler
          (contract := contract) (transcript := transcript)
          (codeRel := codeRel) (profile := profile)
          hDecomposition hProgramOk bound
      have ordinaryTerminal :=
        FunctionsObserverTerminalForward.RecursiveTerminalFamily.ofCompiler
          (contract := contract) (transcript := transcript)
          (codeRel := codeRel) (profile := profile)
          hDecomposition hProgramOk (bound + 1)
      have hRegularExpr :
          FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
            contract transcript codeRel sourceProgram targetProgram profile
            bound :=
        FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded.expression
          regular.value
      have hLoop :
          RecursiveTerminalLoopForwardProgramBounded
            contract transcript codeRel sourceProgram targetProgram profile
            (bound + 1) :=
        RecursiveTerminalLoopForwardProgramBounded.ofComponents
          ordinaryTerminal.loop regular.value regular.list
          ih.expression ih.list
      exact
        { expression :=
            RecursiveTerminalExpressionForwardProgramBounded.ofComponents
              hDecomposition hProgramOk hRegularExpr
              ih.expression ih.body
          body :=
            RecursiveTerminalBodyForwardProgramBounded.ofList ih.list
          stmt :=
            RecursiveTerminalStmtForwardProgramBounded.ofComponents
              hDecomposition hProgramOk hRegularExpr
              ih.expression ih.body ih.list hLoop
          list :=
            RecursiveTerminalListForwardProgramBounded.ofStmt
              regular.stmt ih.stmt ih.list
          loop := hLoop }

theorem dispatcherForward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {sourceFuel : Nat}
    {sourceEntry :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel [] sourceEntry target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        (Fresh.initial
          (Contract.names sourceProgram.contract)).used
        target.source.vars)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.Block [sourceProgram.contract.dispatcher])
          (some sourceProgram.contract) sourceEntry =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    ∃ targetFuel outcome,
      Functions.Source.Effectful.Program.runState
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          targetFuel targetProgram.toFunctions target =
        .ok outcome ∧
      FunctionsObserverOutcome.TerminalFailureRel codeRel failure outcome ∧
      targetFuel ≤
        FunctionsObserverFuel.executionBudgetFor
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.program sourceProgram)
          sourceFuel := by
  have hCompiler := hDecomposition
  obtain
      ⟨bodyStmts, afterBody, functions, afterFunctions,
        hLowerBody, _hLowerFunctions, hTargetProgram⟩ :=
    hDecomposition
  rcases
      Yul.Source.Effectful.exec_block_error_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hRun with hOuter | hBodyFailure
  · rcases hOuter with ⟨rfl, hFailure⟩
    rw [← hFailure] at hObservable
    simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  · rcases hBodyFailure with
      ⟨listSourceFuel, hSourceFuel, hListRun⟩
    have hLowerList :
        Stmt.List.toFunctionsUncheckedFuel?
            (Stmt.fuel sourceProgram.contract.dispatcher + 1)
            (Fresh.initial (Contract.names sourceProgram.contract))
            [sourceProgram.contract.dispatcher] =
          some (bodyStmts, afterBody) :=
      Stmt.List.toFunctionsUncheckedFuel?_singleton_of_stmt
        (by
          cases sourceProgram.contract.dispatcher <;>
            simp [Stmt.fuel])
        hLowerBody
    have hDispatcherOk :
        SolcValidation.StmtOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            [] false false false sourceProgram.contract.dispatcher =
          true := by
      have hParts := hProgramOk
      simp [SolcValidation.ProgramOkWith?,
        SolcValidation.ContractOkWith?,
        SolcValidation.ContractOkWithEntries?] at hParts
      exact hParts.2.1
    have hListOk :
        SolcValidation.StmtsOk? profile sourceProgram.contract
            ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
            [] false false false
            [sourceProgram.contract.dispatcher] =
          true := by
      simpa [SolcValidation.StmtsOk?,
        SolcValidation.StmtOutVars] using hDispatcherOk
    let initial :=
      Fresh.initial (Contract.names sourceProgram.contract)
    have hNames :
        StateRelation.Vars.NamesWithin initial.used
          (Stmt.List.names [sourceProgram.contract.dispatcher]) := by
      intro name hMem
      change name ∈ Contract.names sourceProgram.contract
      have hDispatcherName :
          name ∈ Stmt.names sourceProgram.contract.dispatcher := by
        simpa [Stmt.List.names] using hMem
      simpa [Contract.names] using
        List.mem_append_left
          (FunctionList.names
            (Contract.functionEntries sourceProgram.contract))
          hDispatcherName
    let sourceControl : FunctionsObserverOutcome.SourceControlScopes :=
      { breakScope? := none
        continueScope? := none
        leaveScope? := none }
    have hControl :
        FunctionsObserverOutcome.ControlContextRel sourceControl []
          false false false Functions.Source.Ctx.initial := by
      refine
        { scope := ?_
          breakScope := ?_
          continueScope := ?_
          leaveScope := ?_ }
      · simp [FunctionsObserverOutcome.LayoutWithinScope]
      · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
          Functions.Source.Ctx.initial]
      · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
          Functions.Source.Ctx.initial]
      · simp [sourceControl, FunctionsObserverOutcome.ScopeOptionWithin,
          Functions.Source.Ctx.initial]
    have hFamily :=
      ofCompiler
        (contract := contract) (transcript := transcript)
        (codeRel := codeRel) (profile := profile)
        hCompiler hProgramOk (listSourceFuel + 1)
    obtain ⟨bounded⟩ :=
      hFamily.list
        (sourceFuel := listSourceFuel)
        (compilerFuel := Stmt.fuel sourceProgram.contract.dispatcher + 1)
        (sourceControl := sourceControl)
        (before := initial) (after := afterBody)
        (layout := []) (stmts := [sourceProgram.contract.dispatcher])
        (lower := bodyStmts)
        (source := sourceEntry) (failure := failure)
        (target := target) (ctx := Functions.Source.Ctx.initial)
        (canBreak := false) (canContinue := false) (canLeave := false)
        (by omega)
        (FunctionsObserverStaticCost.dispatcherList_le_program sourceProgram)
        hListOk hNames hLowerList hRel hDomain
        (by
          intro name hMem
          simp [Functions.Source.Ctx.initial] at hMem)
        (by
          intro name hMem
          simp at hMem)
        hControl hListRun hObservable
    let result := bounded.1
    have hTargetOpen :=
      FunctionsObserverTerminal.StatementResult.run_requiredFuel result
    have hTargetScoped :=
      Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        targetProgram.toFunctions hTargetOpen (by simp)
    have hBodyEq :
        targetProgram.toFunctions.body = { stmts := bodyStmts } :=
      congrArg (fun program => program.body) hTargetProgram
    have hProgramRun :
        Functions.Source.Effectful.Program.runState
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            result.requiredFuel targetProgram.toFunctions target =
          .ok
            (Functions.Source.Effectful.Outcome.halt
              result.kind result.finalTarget) := by
      unfold Functions.Source.Effectful.Program.runState
      rw [hBodyEq]
      exact hTargetScoped
    have hLocal :=
      FunctionsObserverFuel.executionBudgetFor_local_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        listSourceFuel
        (FunctionsObserverStaticCost.dispatcherList_le_program sourceProgram)
    have hDynamic :=
      FunctionsObserverFuel.executionBudgetFor_mono
        (FunctionsObserverStaticCost.program sourceProgram)
        (FunctionsObserverStaticCost.program sourceProgram)
        (show listSourceFuel ≤ sourceFuel by omega)
    refine
      ⟨result.requiredFuel,
        Functions.Source.Effectful.Outcome.halt
          result.kind result.finalTarget,
        hProgramRun, result.relation, ?_⟩
    exact bounded.2.trans (hLocal.trans hDynamic)

end RecursiveTerminalProgramBoundedFamily
end FunctionsObserverTerminalFuel
end Yul
end EvmCompiler
