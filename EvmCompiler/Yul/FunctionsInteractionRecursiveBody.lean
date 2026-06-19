import EvmCompiler.Yul.FunctionsInteractionRecursiveStatement

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRecursiveBody

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation
open FunctionsInteractionRecursiveStatement

/-- Package one exact recursively preserved source body list as the selected
Functions function body. Target-fuel accounting remains an explicit private
premise here and is discharged by the source-owned compiler expansion bound. -/
theorem ofListAt
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {listFuel targetFuel : Nat}
    {compilerFuel : Nat}
    {body : List AstStmt} {before after : Fresh.State}
    {fn : Functions.FunDef}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hList : ListForwardAt profile sourceProgram targetProgram
      listFuel targetFuel)
    (hLower : Stmt.List.toBlockUncheckedFuel?
      compilerFuel
      before body = some (fn.body, after))
    (hBodyOk : SolcValidation.StmtsOk? profile sourceProgram.contract
      ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
      (fn.returns ++ fn.params) false false true body = true)
    (hReserved : ∀ name, name ∈ fn.returns ++ fn.params →
      name ∈ before.used)
    (hBodyNames : ∀ name, name ∈ Stmt.List.names body →
      name ∈ before.used)
    (hRel : ScopedStateRel (fn.returns ++ fn.params) source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram listFuel +
          FunctionsInteractionTargetCost.list fn.body.stmts + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionCall.FunctionBodyDoneRel
        (fn.returns ++ fn.params))
      (Yul.InteractionSemantics.exec (listFuel + 1) (.Block body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions
        (Functions.Source.Effectful.FunDef.bodyCtx fn)
        targetFuel fn.body target) := by
  obtain ⟨compilerFuel, lower, _hCompilerFuel, hLowerList, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLower
  obtain ⟨sourceScope, hScopeStore, hScopeUsed, hScopeLayout, hControl⟩ :=
    ControlContextRel.functionBody (fn := fn) rfl hRel hReserved
  have hTargetScope : TargetScopeWithin before.used
      (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    intro name hName
    exact hReserved name (by
      simpa [Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial,
        Functions.Source.Ctx.withLeaveScope] using hName)
  have hBodyRel := hList hBodyOk hBodyNames hLowerList hRel hDomain
    hTargetScope hReserved hControl (by simpa [hFnBody] using hTargetFuel)
  apply FunctionsInteractionCall.functionBodyOfList
    (layout := fn.returns ++ fn.params)
    (bodyLayout := SolcValidation.StmtsOutVars
      (fn.returns ++ fn.params) body)
    (sourceScope := sourceScope) rfl hRel
  · simpa [hScopeStore]
  · exact hScopeLayout
  · exact FunctionsInteractionRecursiveStatement.layoutWithinStmtsOutVars
      (fn.returns ++ fn.params) body
  · simpa [hFnBody, hScopeUsed] using hBodyRel

/-- Construct every selected callee body below `bound` from strictly earlier
statement preservation. The only generated-code fact used internally is
discharged by the compiler-owned source expansion theorem. -/
theorem ofEarlierStatements
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {bound bodyFuel targetFuel : Nat}
    (hEarlier : ∀ childBound, childBound < bound →
      RecursiveStmtForward profile sourceProgram targetProgram childBound)
    (hBodyFuel : bodyFuel < bound) :
    FunctionsInteractionSelectedCall.BodyForwardAt
      profile sourceProgram targetProgram bodyFuel targetFuel := by
  intro body before after fn source target compilerFuel hLower hBodyOk hReserved
    hBodyNames hBudget hRel hDomain
  cases bodyFuel with
  | zero =>
      rw [Yul.InteractionSemantics.Exec.zero]
      exact Simulation.Interaction.ForwardRel.truncated
        (right := Functions.InteractionSemantics.Block.openRun
          targetProgram.toFunctions
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          targetFuel fn.body target)
        (by trivial)
  | succ listFuel =>
      have hStatements :
          RecursiveStmtForward profile sourceProgram targetProgram
            (listFuel + 1) :=
        hEarlier (listFuel + 1) hBodyFuel
      have hLists :
          RecursiveListForward profile sourceProgram targetProgram
            (listFuel + 2) :=
        RecursiveListForward.ofStmt hStatements
      have hListAt :
          ListForwardAt profile sourceProgram targetProgram
            listFuel targetFuel :=
        hLists (sourceFuel := listFuel) (targetFuel := targetFuel) (by omega)
      have hCompiledCost :=
        FunctionsInteractionCompilerCost.toBlockUncheckedFuel?_cost hLower
      have hCompiledListCost :
          FunctionsInteractionTargetCost.list fn.body.stmts ≤
            FunctionsInteractionCompilerCost.stmtList body := by
        simpa [FunctionsInteractionTargetCost.block] using hCompiledCost
      have hBudgetStep :=
        FunctionsInteractionStaticCost.programBudget_add_compilerCost_lt_bodyBudget_step
          sourceProgram body listFuel
      exact ofListAt hListAt hLower hBodyOk hReserved hBodyNames hRel hDomain
        (by omega)

/-- Closed strong source-fuel fixed point for all ordinary Yul statements and
compiler-selected internal function bodies. -/
theorem recursiveStmt
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    (hDecomposition :
      FunctionsCompilerArtifact.PassDecomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (bound : Nat) :
    RecursiveStmtForward profile sourceProgram targetProgram bound := by
  induction bound using Nat.strong_induction_on with
  | h bound hEarlier =>
      apply recursiveStmtOfEarlier hDecomposition hProgramOk hEarlier
      intro bodyFuel bodyTargetFuel hBodyFuel
      exact ofEarlierStatements hEarlier hBodyFuel

/-- Statement lists inherit the closed statement/body fixed point. -/
theorem recursiveList
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    (hDecomposition :
      FunctionsCompilerArtifact.PassDecomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (bound : Nat) :
    RecursiveListForward profile sourceProgram targetProgram bound := by
  intro sourceFuel targetFuel hSourceFuel
  have hStatements :
      RecursiveStmtForward profile sourceProgram targetProgram bound :=
    recursiveStmt hDecomposition hProgramOk bound
  have hLists :
      RecursiveListForward profile sourceProgram targetProgram (bound + 1) :=
    RecursiveListForward.ofStmt hStatements
  unfold ListForwardAt
  intro compilerFuel functionNames layout sourceScopes canBreak canContinue
    canLeave before after stmts lower source target ctx hOk hNames hLower hRel
    hDomain hTargetScope hLayout hControl hTargetFuel
  exact hLists (sourceFuel := sourceFuel) (targetFuel := targetFuel)
    (lt_trans hSourceFuel (by omega)) hOk hNames hLower hRel hDomain
    hTargetScope hLayout hControl hTargetFuel

end FunctionsInteractionRecursiveBody
end Yul
end EvmCompiler
