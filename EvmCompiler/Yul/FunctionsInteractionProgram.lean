import EvmCompiler.Yul.FunctionsInteractionRecursiveBody

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionProgram

open FunctionsInteractionRelation
open FunctionsInteractionPrimitive
open FunctionsInteractionControlRelation
open FunctionsInteractionRecursiveStatement

/-- Whole-program Yul leaves that terminate through an EVM halt rather than a
finite-semantics truncation or a runtime error. -/
def SourceTerminal :
    Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State -> Prop
  | .error failure =>
      match failure.exception with
      | .YulHalt _ _ | .Revert _ => True
      | _ => False
  | .ok _ => False

namespace SourceTerminal

theorem excludes_truncated
    {failure : Yul.InteractionSemantics.Failure}
    (hTerminal : SourceTerminal (.error failure)) :
    Not (Truncated failure) := by
  rcases failure with ⟨exception, state⟩
  cases exception <;>
    simp [SourceTerminal, Truncated] at hTerminal ⊢

end SourceTerminal

/-- The Functions representation of a terminal Yul whole-program leaf. -/
def TargetHalted :
    Except EVMException Functions.InteractionSemantics.Outcome -> Prop
  | .ok { mode := .halt _ , .. } => True
  | _ => False

namespace TargetHalted

theorem successful
    {run : Simulation.Interaction
      EVMException Functions.InteractionSemantics.Outcome}
    (hHalted : Simulation.Interaction.AllDone TargetHalted run) :
    Simulation.Interaction.Successful run := by
  apply Simulation.Interaction.AllDone.mono hHalted
  intro outcome hOutcome
  cases outcome with
  | error error => cases hOutcome
  | ok target => trivial

end TargetHalted

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

namespace DoneRel

theorem target_ok_of_source_ok
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Except EVMException Functions.InteractionSemantics.Outcome}
    (hRel : DoneRel sourceDone targetDone)
    (hSource : match sourceDone with | .error _ => False | .ok _ => True) :
    match targetDone with | .error _ => False | .ok _ => True := by
  rcases hRel with ⟨used, hRel⟩
  cases hRel <;> simp_all

theorem targetHalted_of_sourceTerminal
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Except EVMException Functions.InteractionSemantics.Outcome}
    (hRel : DoneRel sourceDone targetDone)
    (hTerminal : SourceTerminal sourceDone) :
    TargetHalted targetDone := by
  rcases hRel with ⟨used, hRel⟩
  cases hRel with
  | @error sourceFailure targetError hError =>
      rcases sourceFailure with ⟨exception, state⟩
      cases exception <;>
        simp [SourceTerminal, ErrorRel] at hTerminal hError
  | regular hScoped hDomain =>
      cases hTerminal
  | brk hScope hMode hAbrupt =>
      cases hTerminal
  | cont hScope hMode hAbrupt =>
      cases hTerminal
  | leave hScope hMode hAbrupt =>
      cases hTerminal
  | terminal hTerminalRel =>
      cases hTerminalRel <;> trivial

end DoneRel

/-- On universally terminal source branches, the whole-program forward theorem
is a full open-world relation and every Functions branch is halted. -/
theorem terminalRel
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {targetRun : Simulation.Interaction
      EVMException Functions.InteractionSemantics.Outcome}
    (hForward : Simulation.Interaction.ForwardRel Truncated DoneRel
      sourceRun targetRun)
    (hTerminal : Simulation.Interaction.AllDone SourceTerminal sourceRun) :
    Simulation.Interaction.Rel DoneRel sourceRun targetRun /\
      Simulation.Interaction.AllDone TargetHalted targetRun := by
  have hRel := Simulation.Interaction.ForwardRel.rel_of_allDone
    hForward hTerminal
    (fun failure hSource => SourceTerminal.excludes_truncated hSource)
  refine ⟨hRel, ?_⟩
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_left hRel hTerminal
  exact Simulation.Interaction.Rel.allDone_right hStrong
    (fun _ _ hDone =>
      DoneRel.targetHalted_of_sourceTerminal hDone.1 hDone.2)

/-- A universally successful Yul interaction tree remains universally
successful after the adjacent Yul-to-Functions forward simulation. -/
theorem targetSuccessful
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {targetRun : Simulation.Interaction
      EVMException Functions.InteractionSemantics.Outcome}
    (hForward : Simulation.Interaction.ForwardRel Truncated DoneRel
      sourceRun targetRun)
    (hSuccessful : Simulation.Interaction.Successful sourceRun) :
    Simulation.Interaction.Successful targetRun := by
  apply Simulation.Interaction.ForwardRel.successful_right
    hForward hSuccessful
  intro sourceDone targetDone hDone hSource
  cases sourceDone with
  | error sourceError => exact False.elim hSource
  | ok sourceValue =>
      cases targetDone with
      | error targetError =>
          exact DoneRel.target_ok_of_source_ok hDone trivial
      | ok targetValue => trivial

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
      FunctionsCompilerArtifact.PassDecomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
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
  obtain ⟨bodyStmts, afterBody, functions, afterFunctions,
      hLowerBody, _hLowerFunctions, hTargetProgram⟩ :=
    hDecomposition.compiler
  have hLowerList :
      Stmt.List.toFunctionsUncheckedFuel?
          (Stmt.fuel sourceProgram.contract.dispatcher + 1)
          (Fresh.initial hDecomposition.initialNames)
          [sourceProgram.contract.dispatcher] =
        some (bodyStmts, afterBody) :=
    Stmt.List.toFunctionsUncheckedFuel?_singleton_of_stmt
      (by
        cases sourceProgram.contract.dispatcher <;> simp [Stmt.fuel])
      hLowerBody
  have hDispatcherOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          (hDecomposition.functionEntries.map Prod.fst)
          [] false false false sourceProgram.contract.dispatcher = true := by
    exact SolcValidation.contractOkWithEntries_dispatcherOk hProgramOk
  have hListOk :
      SolcValidation.StmtsOk? profile sourceProgram.contract
          (hDecomposition.functionEntries.map Prod.fst)
          [] false false false
          [sourceProgram.contract.dispatcher] = true := by
    simpa [SolcValidation.StmtsOk?, SolcValidation.StmtOutVars] using
      hDispatcherOk
  let initial := Fresh.initial hDecomposition.initialNames
  have hNames : ∀ name,
      name ∈ Stmt.List.names [sourceProgram.contract.dispatcher] →
        name ∈ initial.used := by
    intro name hMem
    have hDispatcherName :
        name ∈ Stmt.names sourceProgram.contract.dispatcher := by
      simpa [Stmt.List.names] using hMem
    apply hDecomposition.sourceNamesReserved name
    exact List.mem_append_left _ hDispatcherName
  have hDomainActual : TargetDomainWithin initial.used target.vars := by
    intro name value hLookup
    apply hDecomposition.sourceNamesReserved name
    exact hDomain name value hLookup
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
      hDecomposition hProgramOk (sourceFuel + 1)
  have hListAt :
      ListForwardAt profile sourceProgram targetProgram sourceFuel
        (FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1)) :=
    hLists
    (sourceFuel := sourceFuel)
    (targetFuel := FunctionsInteractionStaticCost.programBudget
      sourceProgram (sourceFuel + 1))
    (by omega)
  have hOpen := hListAt hListOk hNames hLowerList hRel hDomainActual hTargetScope
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

/-- Executable source-order Yul lowering satisfies the same adjacent
open-interaction theorem. Representation and distinct-name facts are source
validation obligations; all compiler equations are derived from `toObjects?`.
-/
theorem dispatcherForward_of_ordered_toObjects?
    {profile : SolcValidation.DialectProfile}
    {ordered : OrderedProgram} {targetProgram : Objects.Program}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : ordered.toObjects? = some targetProgram)
    (hRepresents : ordered.RepresentsSource)
    (hNames : ordered.FunctionNamesNodup)
    (hProgramOk :
      SolcValidation.ProgramOkWithEntries? profile ordered.program
        ordered.functionEntries = true)
    (hRel : ScopedStateRel [] source target)
    (hDomain : TargetDomainWithin
      (Fresh.initial (Contract.names ordered.program.contract)).used
      target.vars) :
    Simulation.Interaction.ForwardRel Truncated
      DoneRel
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [ordered.program.contract.dispatcher])
        (some ordered.program.contract) source)
      (Functions.InteractionSemantics.Program.openRunState
        (FunctionsInteractionStaticCost.programBudget
          ordered.program (sourceFuel + 1))
        targetProgram.toFunctions target) := by
  exact dispatcherForward
    (FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?
      hLower hRepresents hNames)
    hProgramOk hRel hDomain

end FunctionsInteractionProgram
end Yul
end EvmCompiler
