import EvmCompiler.Yul.FunctionsInteractionRecursiveBody

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionProgram

open FunctionsInteractionRelation
open FunctionsInteractionPrimitive
open FunctionsInteractionControlRelation
open FunctionsInteractionRecursiveStatement

/-- Whole-program outcomes hide the compiler's path-independent final
reservation set while retaining the ordinary open-world outcome relation. -/
def DoneRel :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Except EVMException Functions.InteractionSemantics.Outcome → Prop :=
  fun source target =>
    ∃ used,
      ControlOutcomeDoneRel used []
        { breakScope? := none
          continueScope? := none
          leaveScope? := none }
        false false false source target

/-- Whole-program Yul-to-Functions forward preservation at the compiler's
ordinary dispatcher entry. The target fuel is derived entirely from source
syntax and source fuel; generated target cost is discharged inside the proof.
-/
theorem dispatcherForward
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hDecomposition :
      FunctionsCompilerArtifact.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hRel : ScopedStateRel [] source target)
    (hDomain : TargetDomainWithin
      (Fresh.initial (Contract.names sourceProgram.contract)).used
      target.vars) :
    Simulation.Interaction.ForwardRel Truncated
      DoneRel
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Program.openRunState
        (FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1))
        targetProgram.toFunctions target) := by
  have hCompiler := hDecomposition
  obtain ⟨bodyStmts, afterBody, functions, afterFunctions,
      hLowerBody, _hLowerFunctions, hTargetProgram⟩ := hDecomposition
  have hLowerList :
      Stmt.List.toFunctionsUncheckedFuel?
          (Stmt.fuel sourceProgram.contract.dispatcher + 1)
          (Fresh.initial (Contract.names sourceProgram.contract))
          [sourceProgram.contract.dispatcher] =
        some (bodyStmts, afterBody) :=
    Stmt.List.toFunctionsUncheckedFuel?_singleton_of_stmt
      (by
        cases sourceProgram.contract.dispatcher <;> simp [Stmt.fuel])
      hLowerBody
  have hDispatcherOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          [] false false false sourceProgram.contract.dispatcher = true := by
    have hParts := hProgramOk
    simp [SolcValidation.ProgramOkWith?,
      SolcValidation.ContractOkWith?,
      SolcValidation.ContractOkWithEntries?] at hParts
    exact hParts.2.1
  have hListOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          [] false false false
          [sourceProgram.contract.dispatcher] = true := by
    simpa [SolcValidation.StmtsOk?, SolcValidation.StmtOutVars] using
      hDispatcherOk
  let initial := Fresh.initial (Contract.names sourceProgram.contract)
  have hNames : ∀ name,
      name ∈ Stmt.List.names [sourceProgram.contract.dispatcher] →
        name ∈ initial.used := by
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
  let sourceScopes : SourceScopes :=
    { breakScope? := none
      continueScope? := none
      leaveScope? := none }
  have hControl :
      ControlContextRel sourceScopes [] false false false
        Functions.Source.Ctx.initial := by
    refine
      { scope := ?_
        breakScope := ?_
        continueScope := ?_
        leaveScope := ?_ }
    · simp [LayoutWithinScope]
    · simp [sourceScopes, ScopeOptionRel, Functions.Source.Ctx.initial]
    · simp [sourceScopes, ScopeOptionRel, Functions.Source.Ctx.initial]
    · simp [sourceScopes, ScopeOptionRel, Functions.Source.Ctx.initial]
  have hTargetScope : TargetScopeWithin initial.used
      Functions.Source.Ctx.initial := by
    intro name hName
    simp [Functions.Source.Ctx.initial] at hName
  have hCompilerCost :=
    FunctionsInteractionCompilerCost.toFunctionsUncheckedFuel?_cost hLowerList
  have hDispatcherCost :
      FunctionsInteractionCompilerCost.stmtList
          [sourceProgram.contract.dispatcher] ≤
        FunctionsInteractionStaticCost.program sourceProgram := by
    simpa [FunctionsInteractionCompilerCost.stmtList] using
      FunctionsInteractionStaticCost.expansion_dispatcher_le_program
        sourceProgram
  have hBudgetStep :=
    FunctionsInteractionStaticCost.programBudget_add_cost_lt_step
      sourceProgram hDispatcherCost
      (fuel := sourceFuel)
  have hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram sourceFuel +
          FunctionsInteractionTargetCost.list bodyStmts + 1 <
        FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1) := by
    omega
  have hLists :
      RecursiveListForward profile sourceProgram targetProgram
        (sourceFuel + 1) :=
    FunctionsInteractionRecursiveBody.recursiveList
      hCompiler hProgramOk (sourceFuel + 1)
  have hListAt :
      ListForwardAt profile sourceProgram targetProgram sourceFuel
        (FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1)) :=
    hLists
    (sourceFuel := sourceFuel)
    (targetFuel := FunctionsInteractionStaticCost.programBudget
      sourceProgram (sourceFuel + 1))
    (by omega)
  have hOpen := hListAt hListOk hNames hLowerList hRel hDomain hTargetScope
    (by simp) hControl hTargetFuel
  have hScoped :=
    FunctionsInteractionStatement.ControlDoneRel.blockScoped
      hRel hControl (by simp) hOpen
  unfold Functions.InteractionSemantics.Program.openRunState
    Functions.Source.Canonical.Program.runState
    Functions.Source.Effectful.Control.Program.runState
  rw [hTargetProgram]
  apply Simulation.Interaction.ForwardRel.mono (by
    simpa [Functions.InteractionSemantics.Block.openRunScoped,
      hTargetProgram] using hScoped)
  intro sourceDone targetDone hDone
  exact ⟨afterBody.used, by simpa [sourceScopes] using hDone⟩

end FunctionsInteractionProgram
end Yul
end EvmCompiler
