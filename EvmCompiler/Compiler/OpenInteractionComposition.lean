import EvmCompiler.Yul.FunctionsInteractionProgram
import EvmCompiler.Functions.AllocationInteractionProgram

namespace EvmCompiler
namespace Compiler
namespace OpenInteractionComposition

open Yul.FunctionsInteractionPrimitive

/-- Outcome relation obtained by horizontally composing the adjacent
Yul-to-Functions and allocation-driven Functions-to-Expressions relations. -/
def YulExpressionsDoneRel (contract : MemoryContract.Contract) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State ->
      Except Expressions.EVMException
        Expressions.InteractionSemantics.Outcome -> Prop :=
  fun source target =>
    exists middle,
      Yul.FunctionsInteractionProgram.DoneRel source middle /\
        Functions.AllocationInteractionProgram.OpenOutcomeRel
          contract middle target

/-- Compose the checked Yul-to-Functions whole-program theorem with the
allocation pass's checked whole-main theorem. No compiler recursion or
generated-code reasoning occurs in this module. -/
theorem yulToAllocatedExpressions
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {allocation : Locals.Allocation.ProgramPlan}
    {expressions : Expressions.Program}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.Decomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hLower :
      Functions.AllocationLowering.lowerExpressionsFromAllocation?
        allocation objects.toFunctions = some expressions)
    (hScoped : objects.toFunctions.Scoped)
    (hSafety : Functions.AllocationInteractionSafety.SourceSafety
      objects.toFunctions.memoryContract)
    (hResourceSafe : Functions.AllocationInteractionProgram.ResourceSafe
      allocation objects.toFunctions
      (Yul.FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1)))
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars)
    (hAllocationInitial :
      Functions.AllocationInteractionProgram.InitialRel
        objects.toFunctions.memoryContract functionsState expressionsState)
    (hSuccessful : Simulation.Interaction.Successful
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    exists targetFuel,
      Simulation.Interaction.ForwardRel Truncated
        (YulExpressionsDoneRel objects.toFunctions.memoryContract)
        (Yul.InteractionSemantics.exec (sourceFuel + 1)
          (.Block [sourceProgram.contract.dispatcher])
          (some sourceProgram.contract) source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          targetFuel expressions.body expressionsState) := by
  have hYul := Yul.FunctionsInteractionProgram.dispatcherForward
    (sourceFuel := sourceFuel)
    hDecomposition hProgramOk hYulInitial hYulDomain
  have hFunctionsSuccessful :=
    Yul.FunctionsInteractionProgram.targetSuccessful hYul hSuccessful
  obtain ⟨targetFuel, hAllocation⟩ :=
    Functions.AllocationInteractionProgram.mainForward
      hLower hScoped hSafety hResourceSafe hAllocationInitial
      hFunctionsSuccessful
  exact ⟨targetFuel, by
    simpa [YulExpressionsDoneRel] using
      Simulation.Interaction.ForwardRel.trans_rel hYul hAllocation⟩

/-- Lift any horizontally composed Yul-to-Expressions result across the
canonical Expressions-to-Structured whole-program semantic equality. -/
theorem expressionsToStructured
    {contract : MemoryContract.Contract}
    {expressions : Expressions.Program} {targetFuel : Nat}
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hForward : Simulation.Interaction.ForwardRel Truncated
      (YulExpressionsDoneRel contract) sourceRun
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target)) :
    Simulation.Interaction.ForwardRel Truncated
      (YulExpressionsDoneRel contract) sourceRun
      (Structured.InteractionSemantics.Program.openRunState
        targetFuel expressions.toStructured target) := by
  change Simulation.Interaction.ForwardRel Truncated
    (YulExpressionsDoneRel contract) sourceRun
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hForward
  rw [Expressions.InteractionPreservation.Program.openRunState_toStructured]
    at hForward
  exact hForward

end OpenInteractionComposition
end Compiler
end EvmCompiler
