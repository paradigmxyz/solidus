import EvmCompiler.Yul.FunctionsInteractionProgram
import EvmCompiler.Functions.AllocationInteractionProgram
import EvmCompiler.Functions.StackRecursivePreservation
import EvmCompiler.Structured.InteractionTerminalPreservation
import EvmCompiler.TypedCfg.InteractionPreservation
import EvmCompiler.Assembly.InteractionBytecode
import EvmCompiler.Assembly.InteractionConcreteResources
import EvmCompiler.Solidity.VerifiedStackObjectArtifact

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

/-- Outcome relation for the compiler-owned stack allocator. The adjacent
Functions relation is exact on ordinary state and carries no scratch-memory
contract because this path emits no compiler memory accesses. -/
def YulStackExpressionsDoneRel :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Except Expressions.EVMException
        Expressions.InteractionSemantics.Outcome → Prop :=
  fun source target =>
    ∃ middle,
      Yul.FunctionsInteractionProgram.DoneRel source middle ∧
        Functions.StackStatementPreservation.ControlScopedOutcomeRel
          {} [] Locals.Ctx.initial [] [] Functions.Source.Ctx.initial
          middle target

/-- Compose the established Yul-to-Functions theorem with the checked
stack-only Functions allocator. All allocation analysis and recursive calls
are discharged by the adjacent allocation theorem. -/
theorem yulToStackExpressionsTerminal
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {locals : Locals.Program} {expressions : Expressions.Program}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
    (hWF : objects.toFunctions.WF)
    (hScoped : objects.toFunctions.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported
        objects.toFunctions)
    (hLower :
      Functions.StackLowering.lowerProgram? objects.toFunctions = some locals)
    (hCompile :
      Locals.Program.toExpressions? locals = some expressions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    ∃ targetFuel,
      Simulation.Interaction.Rel YulStackExpressionsDoneRel
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (Expressions.InteractionSemantics.Block.openRun expressions
            targetFuel expressions.body expressionsState) ∧
        Simulation.Interaction.AllDone
          Functions.StackRecursivePreservation.ProgramTargetHalted
          (Expressions.InteractionSemantics.Block.openRun expressions
            targetFuel expressions.body expressionsState) := by
  let functionsFuel :=
    Yul.FunctionsInteractionStaticCost.programBudget
      sourceProgram (sourceFuel + 1)
  have hYul := Yul.FunctionsInteractionProgram.dispatcherForward
    (sourceFuel := sourceFuel)
    hDecomposition hProgramOk hYulInitial hYulDomain
  obtain ⟨hYulRel, hYulTargetHalted⟩ :=
    Yul.FunctionsInteractionProgram.terminalRel hYul hTerminal
  have hFunctionsHalted : Simulation.Interaction.AllDone
      Functions.StackRecursivePreservation.ProgramSourceHalted
      (Functions.InteractionSemantics.Program.openRunState
        functionsFuel objects.toFunctions functionsState) := by
    apply Simulation.Interaction.AllDone.mono hYulTargetHalted
    intro outcome hOutcome
    simpa [functionsFuel,
      Yul.FunctionsInteractionProgram.TargetHalted,
      Functions.StackRecursivePreservation.ProgramSourceHalted] using hOutcome
  obtain ⟨targetFuel, hStackRel, hStackHalted⟩ :=
    Functions.StackRecursivePreservation.compiledProgramBodyTerminal
      objects.toFunctions locals expressions functionsFuel hWF hScoped
      hSupported hLower hCompile hStackInitial hFunctionsHalted
  refine ⟨targetFuel, ?_, hStackHalted⟩
  simpa [YulStackExpressionsDoneRel] using
    Simulation.Interaction.Rel.trans hYulRel hStackRel

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
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
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

/-- Terminal whole-program Yul preservation through compiler-selected
allocation. Terminal Yul failures become halted Functions/Expressions outcomes,
so the result is a full structural relation rather than a truncating forward
relation. -/
theorem yulToAllocatedExpressionsTerminal
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {allocation : Locals.Allocation.ProgramPlan}
    {expressions : Expressions.Program}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
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
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    exists targetFuel,
      Simulation.Interaction.Rel
          (YulExpressionsDoneRel objects.toFunctions.memoryContract)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (Expressions.InteractionSemantics.Block.openRun expressions
            targetFuel expressions.body expressionsState) /\
        Simulation.Interaction.AllDone
          Functions.AllocationInteractionProgram.TargetHalted
          (Expressions.InteractionSemantics.Block.openRun expressions
            targetFuel expressions.body expressionsState) := by
  have hYul := Yul.FunctionsInteractionProgram.dispatcherForward
    (sourceFuel := sourceFuel)
    hDecomposition hProgramOk hYulInitial hYulDomain
  obtain ⟨hYulRel, hYulTargetHalted⟩ :=
    Yul.FunctionsInteractionProgram.terminalRel hYul hTerminal
  have hFunctionsHalted : Simulation.Interaction.AllDone
      Functions.AllocationInteractionProgram.SourceHalted
      (Functions.InteractionSemantics.Program.openRunState
        (Yul.FunctionsInteractionStaticCost.programBudget
          sourceProgram (sourceFuel + 1))
        objects.toFunctions functionsState) := by
    apply Simulation.Interaction.AllDone.mono hYulTargetHalted
    intro outcome hOutcome
    simpa [Yul.FunctionsInteractionProgram.TargetHalted,
      Functions.AllocationInteractionProgram.SourceHalted] using hOutcome
  obtain ⟨targetFuel, hAllocation⟩ :=
    Functions.AllocationInteractionProgram.mainForward
      hLower hScoped hSafety hResourceSafe hAllocationInitial
      (Functions.AllocationInteractionProgram.SourceHalted.successful
        hFunctionsHalted)
  have hExpressionsHalted :=
    Functions.AllocationInteractionProgram.OpenOutcomeRel.allDone_targetHalted
      hAllocation hFunctionsHalted
  refine ⟨targetFuel, ?_, hExpressionsHalted⟩
  simpa [YulExpressionsDoneRel] using
    Simulation.Interaction.Rel.trans hYulRel hAllocation

/-- The canonical Expressions-to-Structured adapter preserves both the full
open relation and terminality. -/
theorem allocatedExpressionsToStructuredTerminal
    {contract : MemoryContract.Contract}
    {expressions : Expressions.Program} {targetFuel : Nat}
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hRel : Simulation.Interaction.Rel
      (YulExpressionsDoneRel contract) sourceRun
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target))
    (hHalted : Simulation.Interaction.AllDone
      Functions.AllocationInteractionProgram.TargetHalted
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target)) :
    Simulation.Interaction.Rel
        (YulExpressionsDoneRel contract) sourceRun
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured target) /\
      Simulation.Interaction.AllDone
        Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured target) := by
  change Simulation.Interaction.Rel
    (YulExpressionsDoneRel contract) sourceRun
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hRel
  change Simulation.Interaction.AllDone
    Functions.AllocationInteractionProgram.TargetHalted
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hHalted
  rw [Expressions.InteractionPreservation.Program.openRunState_toStructured]
    at hRel hHalted
  refine ⟨hRel, ?_⟩
  apply Simulation.Interaction.AllDone.mono hHalted
  intro outcome hOutcome
  simpa [Functions.AllocationInteractionProgram.TargetHalted,
    Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted]
    using hOutcome

/-- Transparent Expressions-to-Structured composition for the checked stack
allocator path. -/
theorem stackExpressionsToStructuredTerminal
    {expressions : Expressions.Program} {targetFuel : Nat}
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hRel : Simulation.Interaction.Rel
      YulStackExpressionsDoneRel sourceRun
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target))
    (hHalted : Simulation.Interaction.AllDone
      Functions.StackRecursivePreservation.ProgramTargetHalted
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target)) :
    Simulation.Interaction.Rel
        YulStackExpressionsDoneRel sourceRun
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured target) ∧
      Simulation.Interaction.AllDone
        Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured target) := by
  change Simulation.Interaction.Rel
    YulStackExpressionsDoneRel sourceRun
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hRel
  change Simulation.Interaction.AllDone
    Functions.StackRecursivePreservation.ProgramTargetHalted
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hHalted
  rw [Expressions.InteractionPreservation.Program.openRunState_toStructured]
    at hRel hHalted
  refine ⟨hRel, ?_⟩
  apply Simulation.Interaction.AllDone.mono hHalted
  intro outcome hOutcome
  simpa [Functions.StackRecursivePreservation.ProgramTargetHalted,
    Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted]
    using hOutcome

/-- Terminal Yul-to-Structured preservation through the stack allocator. -/
theorem yulToStackStructuredTerminal
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {locals : Locals.Program} {expressions : Expressions.Program}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
    (hWF : objects.toFunctions.WF)
    (hScoped : objects.toFunctions.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported
        objects.toFunctions)
    (hLower :
      Functions.StackLowering.lowerProgram? objects.toFunctions = some locals)
    (hCompile :
      Locals.Program.toExpressions? locals = some expressions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    ∃ targetFuel,
      Simulation.Interaction.Rel YulStackExpressionsDoneRel
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (Structured.InteractionSemantics.Program.openRunState
            targetFuel expressions.toStructured expressionsState) ∧
        Simulation.Interaction.AllDone
          Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted
          (Structured.InteractionSemantics.Program.openRunState
            targetFuel expressions.toStructured expressionsState) := by
  obtain ⟨targetFuel, hRel, hHalted⟩ :=
    yulToStackExpressionsTerminal hDecomposition hProgramOk hWF hScoped
      hSupported hLower hCompile hYulInitial hYulDomain hStackInitial hTerminal
  exact ⟨targetFuel,
    stackExpressionsToStructuredTerminal hRel hHalted⟩

/-- Full terminal Yul-to-Structured open-world preservation, composed only
from the two adjacent upper boundaries and the transparent adapter equality. -/
theorem yulToStructuredTerminal
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {allocation : Locals.Allocation.ProgramPlan}
    {expressions : Expressions.Program}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
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
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    exists targetFuel,
      Simulation.Interaction.Rel
          (YulExpressionsDoneRel objects.toFunctions.memoryContract)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (Structured.InteractionSemantics.Program.openRunState
            targetFuel expressions.toStructured expressionsState) /\
        Simulation.Interaction.AllDone
          Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted
          (Structured.InteractionSemantics.Program.openRunState
            targetFuel expressions.toStructured expressionsState) := by
  obtain ⟨targetFuel, hRel, hHalted⟩ :=
    yulToAllocatedExpressionsTerminal
      hDecomposition hProgramOk hLower hScoped hSafety hResourceSafe
      hYulInitial hYulDomain hAllocationInitial hTerminal
  exact ⟨targetFuel,
    allocatedExpressionsToStructuredTerminal hRel hHalted⟩

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

/-- Outcome relation obtained by horizontally composing the adjacent
Structured-to-TypedCfg and TypedCfg-to-Assembly relations. Bytecode execution
has the same terminal result as ordinary Assembly execution. -/
def StructuredBytecodeDoneRel
    (source : Structured.Program)
    (entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      source entryShapes cfg)
    (assembly : Assembly.Program)
    (returns : List Structured.ReturnDest) :
    Except Structured.EVMException Structured.Outcome ->
      Assembly.Source.ExecutionOutcome -> Prop :=
  fun sourceDone targetDone =>
    exists cfgDone,
      Structured.InteractionControlPreservation.OpenOutcome.OutcomeDoneRel
          generated.main
          { procs := source.procs }
          Structured.ProcLabel.programEnd returns []
          sourceDone cfgDone /\
        TypedCfg.InteractionPreservation.OpenBlock.RunSimulates
          assembly cfgDone targetDone

theorem StructuredBytecodeDoneRel.targetTerminal
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      source entryShapes cfg}
    {assembly : Assembly.Program}
    {returns : List Structured.ReturnDest}
    {sourceDone : Except Structured.EVMException Structured.Outcome}
    {targetDone : Assembly.Source.ExecutionOutcome}
    (hSourceHalted :
      Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted
        sourceDone)
    (hRel : StructuredBytecodeDoneRel source entryShapes cfg generated
      assembly returns sourceDone targetDone) :
    Assembly.InteractionSemantics.Terminal targetDone := by
  rcases hRel with ⟨cfgDone, hStructured, hAssembly⟩
  have hSafe :=
    Structured.InteractionTerminalPreservation.OpenOutcome.assemblySafeHalted_of_related
      hStructured hSourceHalted
  exact
    TypedCfg.InteractionPreservation.OpenBlock.terminal_of_assemblySafeHalted
      hSafe hAssembly

/-- Compose the checked terminal Structured lowering through certified
TypedCfg lowering and Assembly encoding. This module only composes adjacent
pass-owned theorems; generated compiler context remains an output. -/
theorem structuredToEncodedBytecode
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {bytecode : Assembly.TargetProgram}
    {sourceFuel : Nat}
    {sourceState : Structured.RunState}
    {cfgState assemblyState : Structured.EVMState}
    (hGenerate :
      Structured.TypedCfgCompiler.generateWithProcEntryShapes?
          source entryShapes = some cfg)
    (hCompile : cfg.compileCertified? = some artifact)
    (hSourceWF : source.WF)
    (hFrameSafe : source.FrameSafe)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hAssemblyCompile : Assembly.compile? artifact.target = some bytecode)
    (hByteLength :
      Assembly.Program.byteLength artifact.target < EvmYul.UInt256.size)
    (hSourceHalted : Simulation.Interaction.AllDone
      Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted
      (Structured.InteractionSemantics.Block.openRun
        source sourceFuel source.body sourceState))
    (hStructuredInitial :
      Structured.TypedCfgPreservation.StateRel sourceState [] cfgState)
    (hAssemblyPc : assemblyState.pc = EvmYul.UInt256.ofNat 0)
    (hAssemblyInitial :
      Assembly.SameRuntimeData cfgState assemblyState.incrPC) :
    Assembly.Accepted artifact.target /\
      exists generated :
          Structured.TypedCfgPreservation.Program.GeneratedContext
            source entryShapes cfg,
        Simulation.Interaction.Rel
          (StructuredBytecodeDoneRel source entryShapes cfg generated
            artifact.target
            sourceState.returns)
          (Structured.InteractionSemantics.Block.openRun
            source sourceFuel source.body sourceState)
          (Assembly.InteractionSemantics.Target.openRunNResult
            bytecode
            (2 *
              (Structured.InteractionStaticCost.blockBudget
                  source sourceFuel source.body *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  cfg))
            assemblyState) := by
  let cfgFuel :=
    Structured.InteractionStaticCost.blockBudget
      source sourceFuel source.body
  let assemblyFuel :=
    cfgFuel *
      TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg
  obtain ⟨generated, hStructuredFor⟩ :=
    Structured.InteractionTerminalPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_terminal
      hGenerate
      (TypedCfg.Program.compileCertified?_wellTyped hCompile)
      hSourceWF hFrameSafe sourceFuel sourceState hSourceHalted
  have hEntry : cfg.entry = Structured.TypedCfgCompiler.entryLabel := by
    simpa using congrArg TypedCfg.Program.entry generated.cfgEq
  have hStructured := hStructuredFor cfgState hStructuredInitial
  have hCfgSafe :=
    Structured.InteractionTerminalPreservation.OpenOutcome.allDone_assemblySafeHalted
      hStructured hSourceHalted
  have hCfgSafeAtEntry : Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.AssemblySafeHalted
      (TypedCfg.InteractionSemantics.Program.openRunN
        cfg cfgFuel cfg.entry cfgState) := by
    rw [hEntry]
    simpa [cfgFuel] using hCfgSafe
  have hCfgAssembly :=
    TypedCfg.InteractionPreservation.Program.compileCertified?_entry_openRunN_assembly_rel
      cfgFuel hCompile hIndependent hAssemblyPc hAssemblyInitial
        hCfgSafeAtEntry
  have hAssemblyTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.target assemblyFuel assemblyState) := by
    have hStrong :=
      Simulation.Interaction.Rel.strengthen_left hCfgAssembly hCfgSafeAtEntry
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro cfgDone assemblyDone hDone
    rcases hDone with ⟨hSimulates, hSafe⟩
    exact
      TypedCfg.InteractionPreservation.OpenBlock.terminal_of_assemblySafeHalted
        hSafe hSimulates
  obtain ⟨hAccepted, hAssemblyBytecode⟩ :=
    Assembly.InteractionPreservation.compile_openRunNResult_target_rel_terminal
      hAssemblyCompile hByteLength hAssemblyTerminal
  refine ⟨hAccepted, generated, ?_⟩
  have hCfgBytecode :=
    Simulation.Interaction.Rel.trans_eq_right
      hCfgAssembly hAssemblyBytecode
  rw [hEntry] at hCfgBytecode
  simpa [StructuredBytecodeDoneRel, cfgFuel, assemblyFuel] using
    Simulation.Interaction.Rel.trans hStructured hCfgBytecode

/-- Adjacent Structured-to-Assembly source-semantics endpoint used by later
Assembly-owned physical encodings. No assembler or byte representation is
selected at this boundary. -/
theorem structuredToAssemblySource
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {sourceFuel : Nat}
    {sourceState : Structured.RunState}
    {cfgState assemblyState : Structured.EVMState}
    (hGenerate :
      Structured.TypedCfgCompiler.generateWithProcEntryShapes?
          source entryShapes = some cfg)
    (hCompile : cfg.compileCertified? = some artifact)
    (hSourceWF : source.WF)
    (hFrameSafe : source.FrameSafe)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hSourceHalted : Simulation.Interaction.AllDone
      Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted
      (Structured.InteractionSemantics.Block.openRun
        source sourceFuel source.body sourceState))
    (hStructuredInitial :
      Structured.TypedCfgPreservation.StateRel sourceState [] cfgState)
    (hAssemblyPc : assemblyState.pc = EvmYul.UInt256.ofNat 0)
    (hAssemblyInitial :
      Assembly.SameRuntimeData cfgState assemblyState.incrPC) :
    ∃ generated :
        Structured.TypedCfgPreservation.Program.GeneratedContext
          source entryShapes cfg,
      Simulation.Interaction.Rel
        (StructuredBytecodeDoneRel source entryShapes cfg generated
          artifact.target sourceState.returns)
        (Structured.InteractionSemantics.Block.openRun
          source sourceFuel source.body sourceState)
        (Assembly.InteractionSemantics.Source.openRunNResult
          artifact.target
          (Structured.InteractionStaticCost.blockBudget
              source sourceFuel source.body *
            TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg)
          assemblyState) := by
  let cfgFuel :=
    Structured.InteractionStaticCost.blockBudget
      source sourceFuel source.body
  let assemblyFuel :=
    cfgFuel * TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg
  obtain ⟨generated, hStructuredFor⟩ :=
    Structured.InteractionTerminalPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_terminal
      hGenerate
      (TypedCfg.Program.compileCertified?_wellTyped hCompile)
      hSourceWF hFrameSafe sourceFuel sourceState hSourceHalted
  have hEntry : cfg.entry = Structured.TypedCfgCompiler.entryLabel := by
    simpa using congrArg TypedCfg.Program.entry generated.cfgEq
  have hStructured := hStructuredFor cfgState hStructuredInitial
  have hCfgSafe :=
    Structured.InteractionTerminalPreservation.OpenOutcome.allDone_assemblySafeHalted
      hStructured hSourceHalted
  have hCfgSafeAtEntry : Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.AssemblySafeHalted
      (TypedCfg.InteractionSemantics.Program.openRunN
        cfg cfgFuel cfg.entry cfgState) := by
    rw [hEntry]
    simpa [cfgFuel] using hCfgSafe
  have hCfgAssembly :=
    TypedCfg.InteractionPreservation.Program.compileCertified?_entry_openRunN_assembly_rel
      cfgFuel hCompile hIndependent hAssemblyPc hAssemblyInitial
        hCfgSafeAtEntry
  refine ⟨generated, ?_⟩
  rw [hEntry] at hCfgAssembly
  simpa [StructuredBytecodeDoneRel, cfgFuel, assemblyFuel] using
    Simulation.Interaction.Rel.trans hStructured hCfgAssembly

/-- End-to-end terminal outcome relation obtained by composing the upper Yul
relation with the lower Structured-to-bytecode relation. -/
def YulBytecodeDoneRel
    (contract : MemoryContract.Contract)
    (structured : Structured.Program)
    (entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg)
    (assembly : Assembly.Program) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State ->
      Assembly.Source.ExecutionOutcome -> Prop :=
  fun sourceDone targetDone =>
    exists structuredDone,
      YulExpressionsDoneRel contract sourceDone structuredDone /\
        StructuredBytecodeDoneRel structured entryShapes cfg generated
          assembly [] structuredDone targetDone

/-- End-to-end terminal relation for the checked stack-allocation route. -/
def YulStackBytecodeDoneRel
    (structured : Structured.Program)
    (entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg)
    (assembly : Assembly.Program) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Assembly.Source.ExecutionOutcome → Prop :=
  fun sourceDone targetDone =>
    ∃ structuredDone,
      YulStackExpressionsDoneRel sourceDone structuredDone ∧
        StructuredBytecodeDoneRel structured entryShapes cfg generated
          assembly [] structuredDone targetDone

theorem YulStackBytecodeDoneRel.targetTerminal
    {structured : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg}
    {assembly : Assembly.Program}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Assembly.Source.ExecutionOutcome}
    (hSourceTerminal :
      Yul.FunctionsInteractionProgram.SourceTerminal sourceDone)
    (hRel : YulStackBytecodeDoneRel structured entryShapes cfg generated
      assembly sourceDone targetDone) :
    Assembly.InteractionSemantics.Terminal targetDone := by
  rcases hRel with
    ⟨structuredDone, ⟨functionsDone, hYul, hStack⟩, hStructured⟩
  have hFunctionsHalted :=
    Yul.FunctionsInteractionProgram.DoneRel.targetHalted_of_sourceTerminal
      hYul hSourceTerminal
  have hStackHalted :
      Functions.StackRecursivePreservation.ProgramTargetHalted
        structuredDone :=
    Functions.StackRecursivePreservation.ControlScopedOutcomeRel.targetHalted_of_sourceHalted
      hStack (by
        simpa [Yul.FunctionsInteractionProgram.TargetHalted,
          Functions.StackRecursivePreservation.ProgramSourceHalted] using
          hFunctionsHalted)
  apply StructuredBytecodeDoneRel.targetTerminal (hRel := hStructured)
  simpa [Functions.StackRecursivePreservation.ProgramTargetHalted,
    Structured.InteractionTerminalPreservation.OpenOutcome.SourceHalted]
    using hStackHalted

theorem YulBytecodeDoneRel.targetTerminal
    {contract : MemoryContract.Contract}
    {structured : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg}
    {assembly : Assembly.Program}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Assembly.Source.ExecutionOutcome}
    (hSourceTerminal :
      Yul.FunctionsInteractionProgram.SourceTerminal sourceDone)
    (hRel : YulBytecodeDoneRel contract structured entryShapes cfg generated
      assembly sourceDone targetDone) :
    Assembly.InteractionSemantics.Terminal targetDone := by
  rcases hRel with
    ⟨structuredDone, ⟨functionsDone, hYul, hAllocation⟩, hStructured⟩
  have hFunctionsHalted :=
    Yul.FunctionsInteractionProgram.DoneRel.targetHalted_of_sourceTerminal
      hYul hSourceTerminal
  have hStructuredHalted :=
    Functions.AllocationInteractionProgram.OpenOutcomeRel.targetHalted_of_sourceHalted
      hAllocation hFunctionsHalted
  exact StructuredBytecodeDoneRel.targetTerminal
    hStructuredHalted hStructured

/-- Checked terminal Yul-to-encoded-bytecode preservation. All semantic
reasoning is delegated to the horizontally composed upper and lower endpoints;
the only target-state adjustment is the compiler entry PC. -/
theorem yulToEncodedBytecode
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {allocation : Locals.Allocation.ProgramPlan}
    {expressions : Expressions.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {bytecode : Assembly.TargetProgram}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
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
    (hGenerate :
      Structured.TypedCfgCompiler.generateWithProcEntryShapes?
          expressions.toStructured entryShapes = some cfg)
    (hCompile : cfg.compileCertified? = some artifact)
    (hStructuredWF : expressions.toStructured.WF)
    (hFrameSafe : expressions.toStructured.FrameSafe)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hAssemblyCompile : Assembly.compile? artifact.target = some bytecode)
    (hByteLength :
      Assembly.Program.byteLength artifact.target < EvmYul.UInt256.size)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    exists structuredFuel,
      Assembly.Accepted artifact.target /\
        exists generated :
            Structured.TypedCfgPreservation.Program.GeneratedContext
              expressions.toStructured entryShapes cfg,
          Simulation.Interaction.Rel
            (YulBytecodeDoneRel objects.toFunctions.memoryContract
              expressions.toStructured entryShapes cfg generated
              artifact.target)
            (Yul.InteractionSemantics.exec (sourceFuel + 1)
              (.Block [sourceProgram.contract.dispatcher])
              (some sourceProgram.contract) source)
            (Assembly.InteractionSemantics.Target.openRunNResult
              bytecode
              (2 *
                (Structured.InteractionStaticCost.blockBudget
                    expressions.toStructured structuredFuel
                    expressions.toStructured.body *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    cfg))
              { expressionsState.evm with
                pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨structuredFuel, hUpper, hStructuredHalted⟩ :=
    yulToStructuredTerminal
      hDecomposition hProgramOk hLower hScoped hSafety hResourceSafe
      hYulInitial hYulDomain hAllocationInitial hTerminal
  have hExpressionsInitial :
      expressionsState = Structured.RunState.initial expressionsState.evm := by
    rcases expressionsState with ⟨evm, returns⟩
    have hReturns : returns = [] := hAllocationInitial.returns
    subst returns
    rfl
  have hStructuredInitial :
      Structured.TypedCfgPreservation.StateRel expressionsState []
        expressionsState.evm := by
    rw [hExpressionsInitial]
    exact Structured.TypedCfgPreservation.StateRel.initial _
  have hAssemblyInitial : Assembly.SameRuntimeData expressionsState.evm
      ({ expressionsState.evm with
          pc := EvmYul.UInt256.ofNat 0 } : Structured.EVMState).incrPC := by
    apply Assembly.SameRuntimeData.incrPC_right
    apply Assembly.SameRuntimeData.with_pc_right
    exact Assembly.SameRuntimeData.refl _
  obtain ⟨hAccepted, generated, hLowerRel⟩ :=
    structuredToEncodedBytecode
      hGenerate hCompile hStructuredWF hFrameSafe hIndependent
      hAssemblyCompile hByteLength hStructuredHalted hStructuredInitial
      rfl hAssemblyInitial
  refine ⟨structuredFuel, hAccepted, generated, ?_⟩
  have hComposed :=
    Simulation.Interaction.Rel.trans hUpper hLowerRel
  have hReturns : expressionsState.returns = [] :=
    hAllocationInitial.returns
  simpa [YulBytecodeDoneRel, hReturns] using hComposed

/-- Checked terminal Yul-to-encoded-bytecode preservation using the new
compiler-owned stack allocator. Lower-pass certificates are computed by their
existing pass owners; no allocation schedule or recursive-call evidence is a
premise. -/
theorem yulStackToEncodedBytecode
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {locals : Locals.Program} {expressions : Expressions.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {bytecode : Assembly.TargetProgram}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
    (hWF : objects.toFunctions.WF)
    (hScoped : objects.toFunctions.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported
        objects.toFunctions)
    (hLower :
      Functions.StackLowering.lowerProgram? objects.toFunctions = some locals)
    (hExpressionsCompile :
      Locals.Program.toExpressions? locals = some expressions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hGenerate :
      Structured.TypedCfgCompiler.generateWithProcEntryShapes?
          expressions.toStructured entryShapes = some cfg)
    (hCompile : cfg.compileCertified? = some artifact)
    (hStructuredWF : expressions.toStructured.WF)
    (hFrameSafe : expressions.toStructured.FrameSafe)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hAssemblyCompile : Assembly.compile? artifact.target = some bytecode)
    (hByteLength :
      Assembly.Program.byteLength artifact.target < EvmYul.UInt256.size)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.target ∧
        ∃ generated :
            Structured.TypedCfgPreservation.Program.GeneratedContext
              expressions.toStructured entryShapes cfg,
          Simulation.Interaction.Rel
            (YulStackBytecodeDoneRel expressions.toStructured entryShapes cfg
              generated artifact.target)
            (Yul.InteractionSemantics.exec (sourceFuel + 1)
              (.Block [sourceProgram.contract.dispatcher])
              (some sourceProgram.contract) source)
            (Assembly.InteractionSemantics.Target.openRunNResult
              bytecode
              (2 *
                (Structured.InteractionStaticCost.blockBudget
                    expressions.toStructured structuredFuel
                    expressions.toStructured.body *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    cfg))
              { expressionsState.evm with
                pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨structuredFuel, hUpper, hStructuredHalted⟩ :=
    yulToStackStructuredTerminal hDecomposition hProgramOk hWF hScoped
      hSupported hLower hExpressionsCompile hYulInitial hYulDomain
      hStackInitial hTerminal
  have hExpressionsInitial :
      expressionsState = Structured.RunState.initial expressionsState.evm := by
    rcases expressionsState with ⟨evm, returns⟩
    have hReturns : returns = [] := hStackInitial.returns
    subst returns
    rfl
  have hStructuredInitial :
      Structured.TypedCfgPreservation.StateRel expressionsState []
        expressionsState.evm := by
    rw [hExpressionsInitial]
    exact Structured.TypedCfgPreservation.StateRel.initial _
  have hAssemblyInitial : Assembly.SameRuntimeData expressionsState.evm
      ({ expressionsState.evm with
          pc := EvmYul.UInt256.ofNat 0 } : Structured.EVMState).incrPC := by
    apply Assembly.SameRuntimeData.incrPC_right
    apply Assembly.SameRuntimeData.with_pc_right
    exact Assembly.SameRuntimeData.refl _
  obtain ⟨hAccepted, generated, hLowerRel⟩ :=
    structuredToEncodedBytecode hGenerate hCompile hStructuredWF hFrameSafe
      hIndependent hAssemblyCompile hByteLength hStructuredHalted
      hStructuredInitial rfl hAssemblyInitial
  refine ⟨structuredFuel, hAccepted, generated, ?_⟩
  have hComposed := Simulation.Interaction.Rel.trans hUpper hLowerRel
  have hReturns : expressionsState.returns = [] := hStackInitial.returns
  simpa [YulStackBytecodeDoneRel, hReturns] using hComposed

/-- Checked stack-allocation route through the logical Assembly source
semantics. Physical byte encodings compose below this theorem. -/
theorem yulStackToAssemblySource
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {locals : Locals.Program} {expressions : Expressions.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
    (hWF : objects.toFunctions.WF)
    (hScoped : objects.toFunctions.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported
        objects.toFunctions)
    (hLower :
      Functions.StackLowering.lowerProgram? objects.toFunctions = some locals)
    (hExpressionsCompile :
      Locals.Program.toExpressions? locals = some expressions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hGenerate :
      Structured.TypedCfgCompiler.generateWithProcEntryShapes?
          expressions.toStructured entryShapes = some cfg)
    (hCompile : cfg.compileCertified? = some artifact)
    (hStructuredWF : expressions.toStructured.WF)
    (hFrameSafe : expressions.toStructured.FrameSafe)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    ∃ structuredFuel,
      ∃ generated :
          Structured.TypedCfgPreservation.Program.GeneratedContext
            expressions.toStructured entryShapes cfg,
        Simulation.Interaction.Rel
          (YulStackBytecodeDoneRel expressions.toStructured entryShapes cfg
            generated artifact.target)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (Assembly.InteractionSemantics.Source.openRunNResult
            artifact.target
            (Structured.InteractionStaticCost.blockBudget
                expressions.toStructured structuredFuel
                expressions.toStructured.body *
              TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg)
            { expressionsState.evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨structuredFuel, hUpper, hStructuredHalted⟩ :=
    yulToStackStructuredTerminal hDecomposition hProgramOk hWF hScoped
      hSupported hLower hExpressionsCompile hYulInitial hYulDomain
      hStackInitial hTerminal
  have hExpressionsInitial :
      expressionsState = Structured.RunState.initial expressionsState.evm := by
    rcases expressionsState with ⟨evm, returns⟩
    have hReturns : returns = [] := hStackInitial.returns
    subst returns
    rfl
  have hStructuredInitial :
      Structured.TypedCfgPreservation.StateRel expressionsState []
        expressionsState.evm := by
    rw [hExpressionsInitial]
    exact Structured.TypedCfgPreservation.StateRel.initial _
  have hAssemblyInitial : Assembly.SameRuntimeData expressionsState.evm
      ({ expressionsState.evm with
          pc := EvmYul.UInt256.ofNat 0 } : Structured.EVMState).incrPC := by
    apply Assembly.SameRuntimeData.incrPC_right
    apply Assembly.SameRuntimeData.with_pc_right
    exact Assembly.SameRuntimeData.refl _
  obtain ⟨generated, hLowerRel⟩ :=
    structuredToAssemblySource hGenerate hCompile hStructuredWF hFrameSafe
      hIndependent hStructuredHalted hStructuredInitial rfl hAssemblyInitial
  refine ⟨structuredFuel, generated, ?_⟩
  have hComposed := Simulation.Interaction.Rel.trans hUpper hLowerRel
  have hReturns : expressionsState.returns = [] := hStackInitial.returns
  simpa [YulStackBytecodeDoneRel, hReturns] using hComposed

/-- Terminal relation after the Assembly-owned compact physical encoding. -/
def YulStackCompactDoneRel
    (structured : Structured.Program)
    (entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg)
    (assembly : Assembly.Program) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Assembly.Source.ExecutionOutcome → Prop :=
  fun sourceDone compactDone =>
    ∃ assemblyDone,
      YulStackBytecodeDoneRel structured entryShapes cfg generated assembly
          sourceDone assemblyDone ∧
        Assembly.Compact.RuntimeOutcomeRel
          compactDone assemblyDone

/-- Compose the logical Assembly source run with the checked compact physical
encoding. The byte suffix is caller-owned object data and is proved irrelevant
to every decoded code instruction by the Assembly pass. -/
theorem stackAssemblyToCompactBytecode
    {sourceProgram : Yul.Program}
    {structured : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg}
    {assembly : Assembly.Program}
    {pinnedPushPcs : List Nat}
    {compact : Assembly.Compact.Artifact}
    {sourceFuel assemblyFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {targetState : Assembly.EVMState}
    (suffix : List UInt8)
    (hRel : Simulation.Interaction.Rel
      (YulStackBytecodeDoneRel structured entryShapes cfg generated assembly)
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Assembly.InteractionSemantics.Source.openRunNResult
        assembly assemblyFuel targetState))
    (hCompile : Assembly.Compact.compile? assembly pinnedPushPcs = some compact)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat 0)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    Simulation.Interaction.Rel
      (YulStackCompactDoneRel structured entryShapes cfg generated assembly)
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList (compact.bytes.toList ++ suffix))
        (2 * assemblyFuel) targetState) := by
  have hStrong := Simulation.Interaction.Rel.strengthen_left hRel hTerminal
  have hAssemblyTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Source.openRunNResult
        assembly assemblyFuel targetState) := by
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro sourceDone assemblyDone hDone
    exact YulStackBytecodeDoneRel.targetTerminal hDone.2 hDone.1
  have hCompact :=
    Assembly.Compact.InteractionSemantics.compile?_source_openRunNResult_terminal_rel
      hCompile suffix assemblyFuel 0 hTargetPc hTargetPc
        (Assembly.SameRuntimeData.refl targetState) hAssemblyTerminal
  have hComposed := Simulation.Interaction.Rel.trans hRel
    (Simulation.Interaction.Rel.symm hCompact)
  simpa [YulStackCompactDoneRel] using hComposed

/-- Final adjacent Assembly-to-raw-bytecode composition for the stack route.
The decoder relation is owned by Assembly; this theorem only rewrites the
terminal interaction tree after proving that every target branch halts. -/
theorem stackEncodedToRawBytecode
    {sourceProgram : Yul.Program}
    {structured : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg}
    {assembly : Assembly.Program}
    {target : Assembly.TargetProgram}
    {bytes : ByteArray}
    {sourceFuel targetFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {targetState : Assembly.EVMState}
    (hRel : Simulation.Interaction.Rel
      (YulStackBytecodeDoneRel structured entryShapes cfg generated assembly)
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Assembly.InteractionSemantics.Target.openRunNResult
        target targetFuel targetState))
    (hDecoding : Assembly.Bytecode.DecodingCorrect target bytes)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    Simulation.Interaction.Rel
      (YulStackBytecodeDoneRel structured entryShapes cfg generated assembly)
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Assembly.Bytecode.InteractionSemantics.openRunNResult
        bytes targetFuel targetState) := by
  have hStrong := Simulation.Interaction.Rel.strengthen_left hRel hTerminal
  have hTargetTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Target.openRunNResult
        target targetFuel targetState) := by
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro sourceDone targetDone hDone
    exact YulStackBytecodeDoneRel.targetTerminal hDone.2 hDone.1
  rw [Assembly.Bytecode.openRunNResult_eq_target_of_decoding_terminal
    hDecoding hTargetTerminal]
  exact hRel

/-- A checked frontend stack-code artifact reaches its exact compact raw
bytes. All compiler equations, frame-safety facts, and lower certificates are
recovered from adjacent pass-owned theorems. -/
theorem compiledVerifiedStackCodeToRawBytecode
    {object : Solidity.Frontend.Object}
    {context : Solidity.Frontend.ObjectBuiltinContext}
    {codeArtifact : Solidity.Frontend.Object.VerifiedStackCodeArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (suffix : List UInt8 := [])
    (hCode : object.compileVerifiedStackCodeArtifactIn? context =
      some codeArtifact)
    (hWF : codeArtifact.lower.toFunctions.WF)
    (hScoped : codeArtifact.lower.toFunctions.Scoped)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [codeArtifact.ordered.program.contract.dispatcher])
        (some codeArtifact.ordered.program.contract) source)) :
    ∃ structuredFuel,
      Assembly.Accepted codeArtifact.compiled.certified.target ∧
        ∃ generated :
            Structured.TypedCfgPreservation.Program.GeneratedContext
              codeArtifact.compiled.expressions.toStructured
              codeArtifact.compiled.entryShapes codeArtifact.compiled.cfg,
          Simulation.Interaction.Rel
            (YulStackCompactDoneRel
              codeArtifact.compiled.expressions.toStructured
              codeArtifact.compiled.entryShapes codeArtifact.compiled.cfg
              generated codeArtifact.compiled.certified.target)
            (Yul.InteractionSemantics.exec (sourceFuel + 1)
              (.Block [codeArtifact.ordered.program.contract.dispatcher])
              (some codeArtifact.ordered.program.contract) source)
            (Assembly.Compact.InteractionSemantics.openRunNResult
              (Assembly.Bytecode.ofList (codeArtifact.bytes ++ suffix))
              (2 *
                (Structured.InteractionStaticCost.blockBudget
                    codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    codeArtifact.compiled.expressions.toStructured.body *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    codeArtifact.compiled.cfg))
              { expressionsState.evm with
                pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨_hResolved, hOrdered, hLower, hStackArtifact, _pinnedPushPcs,
      _hPins, hCompact, hBytes⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  have hSource :=
    Solidity.Frontend.Object.toSolcYulOrderedProgram?_source hOrdered
  let decomposition :=
    Yul.FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?
      hLower hSource.1 hSource.2.1
  have hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries?
          Yul.SolcValidation.defaultDialectProfile
          codeArtifact.ordered.program decomposition.functionEntries = true := by
    simpa [decomposition,
      Yul.FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?]
      using
        Solidity.Frontend.Object.toSolcYulOrderedProgram?_programOkWithEntries
          hOrdered
  obtain ⟨hSupported, hStackLower, hExpressions, hStructuredWF, _hShapes,
      hGenerate, _hWellTyped, hIndependent, hCertified, _hTarget,
      _hWindow⟩ :=
    Compiler.StackArtifact.compile?_parts hStackArtifact
  have hAssembly := Compiler.StackArtifact.compile?_assembly hStackArtifact
  have hFrameSafe :=
    Compiler.StackArtifact.compile?_frameSafe hStackArtifact
  obtain ⟨structuredFuel, generated, hAssemblySource⟩ :=
    yulStackToAssemblySource decomposition hProgramOk hWF hScoped hSupported
      hStackLower hExpressions hYulInitial hYulDomain hStackInitial hGenerate
      hCertified hStructuredWF hFrameSafe hIndependent hTerminal
  have hAccepted : Assembly.Accepted
      codeArtifact.compiled.certified.target :=
    Assembly.Preservation.compile?_some_accepted hAssembly
  have hCompactRel := stackAssemblyToCompactBytecode suffix hAssemblySource
    hCompact rfl hTerminal
  refine ⟨structuredFuel, hAccepted, generated, ?_⟩
  rw [hBytes]
  exact hCompactRel

/-- Recursive Solidity object construction reaches the exact root image. Child
objects and payload layout are computed by the frontend artifact, while the
root code proof remains the adjacent checked stack-code theorem above. -/
theorem compiledVerifiedStackObjectToRawBytecode
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hWF : artifact.codeArtifact.lower.toFunctions.WF)
    (hScoped : artifact.codeArtifact.lower.toFunctions.Scoped)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names
          artifact.codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract) source)) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        ∃ generated :
            Structured.TypedCfgPreservation.Program.GeneratedContext
              artifact.codeArtifact.compiled.expressions.toStructured
              artifact.codeArtifact.compiled.entryShapes
              artifact.codeArtifact.compiled.cfg,
          Simulation.Interaction.Rel
            (YulStackCompactDoneRel
              artifact.codeArtifact.compiled.expressions.toStructured
              artifact.codeArtifact.compiled.entryShapes
              artifact.codeArtifact.compiled.cfg generated
              artifact.codeArtifact.compiled.certified.target)
            (Yul.InteractionSemantics.exec (sourceFuel + 1)
              (.Block
                [artifact.codeArtifact.ordered.program.contract.dispatcher])
              (some artifact.codeArtifact.ordered.program.contract) source)
            (Assembly.Compact.InteractionSemantics.openRunNResult
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (2 *
                (Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              { expressionsState.evm with
                pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      _hArtifactChildren, _hContext, _hChildImages, _hPayload, hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  have hResult :=
    compiledVerifiedStackCodeToRawBytecode
      (suffix := plan.payload) hCode hWF hScoped hYulInitial hYulDomain
      hStackInitial hTerminal
  simpa [hImage] using hResult

/-- The end-to-end relation for a successfully compiled artifact. Intermediate
compiler witnesses are existential and fixed across the whole interaction
tree. -/
def CompiledOpenWorldRel
    (sourceProgram : Yul.Program) (objects : Objects.Program)
    (compiledArtifact : Objects.Program.CompileArtifact)
    (sourceFuel : Nat) (source : Yul.InteractionSemantics.State)
    (expressionsState : Expressions.InteractionSemantics.RunState) : Prop :=
  exists expressions : Expressions.Program,
    exists entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes,
      exists cfgArtifact : TypedCfg.Program.CertifiedArtifact,
        exists structuredFuel,
          Assembly.Accepted cfgArtifact.target /\
            exists generated :
                Structured.TypedCfgPreservation.Program.GeneratedContext
                  expressions.toStructured entryShapes
                  compiledArtifact.metadata.typedCfg,
              Simulation.Interaction.Rel
                (YulBytecodeDoneRel
                  objects.toFunctions.memoryContract
                  expressions.toStructured entryShapes
                  compiledArtifact.metadata.typedCfg generated
                  cfgArtifact.target)
                (Yul.InteractionSemantics.exec (sourceFuel + 1)
                  (.Block [sourceProgram.contract.dispatcher])
                  (some sourceProgram.contract) source)
                (Assembly.InteractionSemantics.Target.openRunNResult
                  compiledArtifact.target
                  (2 *
                    (Structured.InteractionStaticCost.blockBudget
                        expressions.toStructured structuredFuel
                        expressions.toStructured.body *
                      TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                        compiledArtifact.metadata.typedCfg))
                  { expressionsState.evm with
                    pc := EvmYul.UInt256.ofNat 0 })

/-- Terminal outcome relation exposed by the raw-byte branch theorem. All
compiler-owned witnesses remain existential outputs of checked compilation. -/
def CompiledBytecodeDoneRel
    (objects : Objects.Program)
    (compiledArtifact : Objects.Program.CompileArtifact) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State ->
      Assembly.Source.ExecutionOutcome -> Prop :=
  fun sourceDone targetDone =>
    exists expressions : Expressions.Program,
      exists entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes,
        exists cfgArtifact : TypedCfg.Program.CertifiedArtifact,
          exists generated :
              Structured.TypedCfgPreservation.Program.GeneratedContext
                expressions.toStructured entryShapes
                compiledArtifact.metadata.typedCfg,
            YulBytecodeDoneRel
              objects.toFunctions.memoryContract
              expressions.toStructured entryShapes
              compiledArtifact.metadata.typedCfg generated
              cfgArtifact.target sourceDone targetDone

theorem CompiledOpenWorldRel.rawBytecodeRel
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {compiledArtifact : Objects.Program.CompileArtifact}
    {sourceFuel : Nat} {source : Yul.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    {bytes : ByteArray}
    (hCompiled : CompiledOpenWorldRel sourceProgram objects compiledArtifact
      sourceFuel source expressionsState)
    (hDecoding : Assembly.Bytecode.DecodingCorrect compiledArtifact.target
      bytes)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    exists targetFuel,
      Simulation.Interaction.Rel
        (CompiledBytecodeDoneRel objects compiledArtifact)
        (Yul.InteractionSemantics.exec (sourceFuel + 1)
          (.Block [sourceProgram.contract.dispatcher])
          (some sourceProgram.contract) source)
        (Assembly.Bytecode.InteractionSemantics.openRunNResult
          bytes targetFuel
          { expressionsState.evm with
            pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases hCompiled with
    ⟨expressions, entryShapes, cfgArtifact, structuredFuel,
      _hAccepted, generated, hRel⟩
  let targetFuel :=
    2 *
      (Structured.InteractionStaticCost.blockBudget
          expressions.toStructured structuredFuel
          expressions.toStructured.body *
        TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
          compiledArtifact.metadata.typedCfg)
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_left hRel hTerminal
  have hTargetTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (Assembly.InteractionSemantics.Target.openRunNResult
        compiledArtifact.target targetFuel
        { expressionsState.evm with
          pc := EvmYul.UInt256.ofNat 0 }) := by
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro sourceDone targetDone hDone
    exact YulBytecodeDoneRel.targetTerminal hDone.2 hDone.1
  have hRawEq :=
    Assembly.Bytecode.openRunNResult_eq_target_of_decoding_terminal
      hDecoding hTargetTerminal
  have hPublic : Simulation.Interaction.Rel
      (CompiledBytecodeDoneRel objects compiledArtifact)
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Assembly.InteractionSemantics.Target.openRunNResult
        compiledArtifact.target targetFuel
        { expressionsState.evm with
          pc := EvmYul.UInt256.ofNat 0 }) := by
    apply Simulation.Interaction.Rel.mono hRel
    intro sourceDone targetDone hDone
    exact ⟨expressions, entryShapes, cfgArtifact, generated, hDone⟩
  refine ⟨targetFuel, ?_⟩
  rw [hRawEq]
  exact hPublic

/-- Concrete `gas`/`msize` observations combined with universally open
CALL/CREATE-family effects. Every branch of the target observer computation
expands to one exact interleaved transcript, executes on the raw byte image,
and replays to a related source terminal leaf. -/
theorem CompiledOpenWorldRel.observedBytecodeReplay
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {compiledArtifact : Objects.Program.CompileArtifact}
    {sourceFuel : Nat} {source : Yul.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    {bytes : ByteArray}
    (hCompiled : CompiledOpenWorldRel sourceProgram objects compiledArtifact
      sourceFuel source expressionsState)
    (hDecoding : Assembly.Bytecode.DecodingCorrect compiledArtifact.target
      bytes)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    exists targetFuel,
      Simulation.Interaction.Rel
          (CompiledBytecodeDoneRel objects compiledArtifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (Assembly.Bytecode.InteractionSemantics.openRunNResult
            bytes targetFuel
            { expressionsState.evm with
              pc := EvmYul.UInt256.ofNat 0 }) /\
        ∀ {externalTranscript fullTranscript targetResult},
          Simulation.Interaction.Executes
            (Assembly.InteractionConcreteResources.openRunNResult
              compiledArtifact.target targetFuel
              { expressionsState.evm with
                pc := EvmYul.UInt256.ofNat 0 })
            externalTranscript (.ok (targetResult, fullTranscript)) ->
          ∃ sourceDone,
            Simulation.Interaction.Executes
              (Yul.InteractionSemantics.exec (sourceFuel + 1)
                (.Block [sourceProgram.contract.dispatcher])
                (some sourceProgram.contract) source)
              fullTranscript sourceDone /\
            CompiledBytecodeDoneRel objects compiledArtifact
              sourceDone (.ok targetResult) := by
  obtain ⟨targetFuel, hRawRel⟩ :=
    hCompiled.rawBytecodeRel hDecoding hTerminal
  refine ⟨targetFuel, hRawRel, ?_⟩
  intro externalTranscript fullTranscript targetResult hObserved
  have hTarget :=
    Assembly.InteractionConcreteResources.openRunNResult_executes hObserved
  have hRaw :=
    Assembly.Bytecode.target_openRunNResult_executes_of_decoding
      hDecoding hTarget
  obtain ⟨sourceDone, hSource, hDone⟩ :=
    Simulation.Interaction.Rel.executes hRawRel.symm hRaw
  exact ⟨sourceDone, hSource, hDone⟩

theorem CompiledOpenWorldRel.bytecodeExecutes
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {compiledArtifact : Objects.Program.CompileArtifact}
    {sourceFuel : Nat} {source : Yul.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    {bytes : ByteArray}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    (hCompiled : CompiledOpenWorldRel sourceProgram objects compiledArtifact
      sourceFuel source expressionsState)
    (hDecoding : Assembly.Bytecode.DecodingCorrect compiledArtifact.target
      bytes)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source))
    (hSourceExec : Simulation.Interaction.Executes
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      transcript sourceDone) :
    exists targetFuel targetDone,
      Simulation.Interaction.Executes
        (Assembly.Bytecode.InteractionSemantics.openRunNResult
          bytes targetFuel
          { expressionsState.evm with
            pc := EvmYul.UInt256.ofNat 0 })
        transcript targetDone /\
      CompiledBytecodeDoneRel objects compiledArtifact
        sourceDone targetDone := by
  rcases hCompiled with
    ⟨expressions, entryShapes, cfgArtifact, structuredFuel,
      _hAccepted, generated, hRel⟩
  obtain ⟨targetDone, hTargetExec, hDone⟩ :=
    Simulation.Interaction.Rel.executes hRel hSourceExec
  have hSourceTerminal :=
    Simulation.Interaction.AllDone.property_of_executes
      hTerminal hSourceExec
  have hTargetTerminal :=
    YulBytecodeDoneRel.targetTerminal hSourceTerminal hDone
  cases targetDone with
  | error error => cases hTargetTerminal
  | ok result =>
      let targetFuel :=
        2 *
          (Structured.InteractionStaticCost.blockBudget
              expressions.toStructured structuredFuel
              expressions.toStructured.body *
            TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
              compiledArtifact.metadata.typedCfg)
      refine ⟨targetFuel, .ok result, ?_, ?_⟩
      · exact
          Assembly.Bytecode.target_openRunNResult_executes_of_decoding
            hDecoding hTargetExec
      · exact ⟨expressions, entryShapes, cfgArtifact, generated, hDone⟩

/-- Artifact-facing terminal Yul correctness. Every intermediate compiler
artifact is recovered from ordinary top-level lowering and compilation; the
public inputs contain only source validation, initial-state relations, and
source/allocation-facing semantic and resource safety. -/
theorem compiledWithPassToEncodedBytecode
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {compiledArtifact : Objects.Program.CompileArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hDecomposition :
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
    (hCompile :
      Objects.Program.compileArtifact? objects = some compiledArtifact)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        hDecomposition.functionEntries = true)
    (hScoped : objects.toFunctions.Scoped)
    (hSafety : Functions.AllocationInteractionSafety.SourceSafety
      objects.toFunctions.memoryContract)
    (hResourceSafe : Functions.AllocationInteractionProgram.ResourceSafe
      compiledArtifact.metadata.allocation objects.toFunctions
      (Yul.FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1)))
    (hFrameSafe :
      Functions.AllocationInteractionProgram.StructuredFrameSafe
        compiledArtifact.metadata.allocation objects.toFunctions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars)
    (hAllocationInitial :
      Functions.AllocationInteractionProgram.InitialRel
        objects.toFunctions.memoryContract functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    CompiledOpenWorldRel sourceProgram objects compiledArtifact
      sourceFuel source expressionsState := by
  have hCompileWithPolicy :
      Objects.Program.compileArtifactWithPolicy?
          Objects.Program.defaultBackendPolicy objects =
        some compiledArtifact := by
    simpa [Objects.Program.compileArtifact?] using hCompile
  have hLowered :
      compiledArtifact.LoweredFrom objects.toFunctions :=
    (Objects.Program.compileArtifactWithPolicy?_valid
      hCompileWithPolicy).2
  rcases hLowered with
    ⟨expressions, compiled, _hCompatible, _hMemoryAuthorized,
      hExpressions, hStructuredWF, hCfg, hAllocated,
      hExecutable, _hCertificate⟩
  have hLower :
      Functions.AllocationLowering.lowerExpressionsFromAllocation?
          compiledArtifact.metadata.allocation objects.toFunctions =
        some expressions := by
    exact
      Objects.Program.PlannedProgram.lowerWithAllocation?_lowerer_exact
        hExpressions
  have hSelectedFrameSafe : expressions.toStructured.FrameSafe :=
    hFrameSafe expressions hLower
  obtain ⟨entryShapes, sourceArtifact, _hEntryShapes,
      hSourceArtifact, hSourceCfg⟩ :=
    Objects.Program.PlannedProgram.lowerTypedCfg?_sourceArtifact hCfg
  have hGenerate :=
    Structured.TypedCfgCompiler.artifactWithProcEntryShapes?_generate
      hSourceArtifact
  rw [hSourceCfg] at hGenerate
  let cfgArtifact : TypedCfg.Program.CertifiedArtifact :=
    { target := compiled.target
      metadata := compiled.metadata.cfg }
  have hCfgCompile :
      compiledArtifact.metadata.typedCfg.compileCertified? =
        some cfgArtifact := by
    simpa [cfgArtifact] using
      Compiler.AllocatedTypedCfg.Program.compileCertified?_cfg hAllocated
  have hIndependent :
      compiledArtifact.metadata.typedCfg.ProgramCounterIndependent :=
    Objects.Program.PlannedProgram.lowerTypedCfg?_programCounterIndependent
      hCfg
  have hAssemblyCompile :
      Assembly.compile? cfgArtifact.target = some compiledArtifact.target := by
    rw [← Assembly.compileExecutable?_eq_compile?]
    simpa [cfgArtifact] using hExecutable
  have hByteLength :
      Assembly.Program.byteLength cfgArtifact.target <
        EvmYul.UInt256.size :=
    (TypedCfg.Program.compileCertified?_pcFits hCfgCompile).byteLength_lt
  obtain ⟨structuredFuel, hAccepted, generated, hRel⟩ :=
    yulToEncodedBytecode
      hDecomposition
      hProgramOk hLower hScoped hSafety hResourceSafe hYulInitial hYulDomain
      hAllocationInitial hGenerate hCfgCompile hStructuredWF
      hSelectedFrameSafe hIndependent hAssemblyCompile hByteLength hTerminal
  exact ⟨expressions, entryShapes, cfgArtifact, structuredFuel,
    hAccepted, generated, hRel⟩

/-- Compatibility wrapper for canonical map-enumerated Yul lowering. -/
theorem compiledYulToEncodedBytecode
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {compiledArtifact : Objects.Program.CompileArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hObjects :
      Yul.Program.toObjectsCanonical? sourceProgram = some objects)
    (hCompile :
      Objects.Program.compileArtifact? objects = some compiledArtifact)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hScoped : objects.toFunctions.Scoped)
    (hSafety : Functions.AllocationInteractionSafety.SourceSafety
      objects.toFunctions.memoryContract)
    (hResourceSafe : Functions.AllocationInteractionProgram.ResourceSafe
      compiledArtifact.metadata.allocation objects.toFunctions
      (Yul.FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1)))
    (hFrameSafe :
      Functions.AllocationInteractionProgram.StructuredFrameSafe
        compiledArtifact.metadata.allocation objects.toFunctions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars)
    (hAllocationInitial :
      Functions.AllocationInteractionProgram.InitialRel
        objects.toFunctions.memoryContract functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)) :
    CompiledOpenWorldRel sourceProgram objects compiledArtifact
      sourceFuel source expressionsState := by
  let decomposition :=
    Yul.FunctionsCompilerArtifact.passDecomposition_of_toObjectsCanonical?
      hObjects
  have hEntriesOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile sourceProgram
        decomposition.functionEntries = true := by
    simpa [decomposition,
      Yul.FunctionsCompilerArtifact.passDecomposition_of_toObjectsCanonical?,
      Yul.SolcValidation.ProgramOkWithEntries?,
      Yul.SolcValidation.ProgramOkWith?,
      Yul.SolcValidation.ContractOkWith?] using hProgramOk
  exact compiledWithPassToEncodedBytecode decomposition
    hCompile hEntriesOk hScoped hSafety hResourceSafe hFrameSafe
    hYulInitial hYulDomain hAllocationInitial hTerminal

/-- Executable ordered Yul lowering composes through every adjacent pass to
the encoded EVM target. No lower-pass artifact or generated proof premise is
added beyond the ordinary checked compilation result. -/
theorem compiledOrderedYulToEncodedBytecode
    {profile : Yul.SolcValidation.DialectProfile}
    {ordered : Yul.OrderedProgram} {objects : Objects.Program}
    {compiledArtifact : Objects.Program.CompileArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hObjects : ordered.toObjects? = some objects)
    (hRepresents : ordered.RepresentsSource)
    (hNames : ordered.FunctionNamesNodup)
    (hCompile :
      Objects.Program.compileArtifact? objects = some compiledArtifact)
    (hProgramOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile ordered.program
        ordered.functionEntries = true)
    (hScoped : objects.toFunctions.Scoped)
    (hSafety : Functions.AllocationInteractionSafety.SourceSafety
      objects.toFunctions.memoryContract)
    (hResourceSafe : Functions.AllocationInteractionProgram.ResourceSafe
      compiledArtifact.metadata.allocation objects.toFunctions
      (Yul.FunctionsInteractionStaticCost.programBudget
        ordered.program (sourceFuel + 1)))
    (hFrameSafe :
      Functions.AllocationInteractionProgram.StructuredFrameSafe
        compiledArtifact.metadata.allocation objects.toFunctions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names ordered.program.contract)).used
      functionsState.vars)
    (hAllocationInitial :
      Functions.AllocationInteractionProgram.InitialRel
        objects.toFunctions.memoryContract functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [ordered.program.contract.dispatcher])
        (some ordered.program.contract) source)) :
    CompiledOpenWorldRel ordered.program objects compiledArtifact
      sourceFuel source expressionsState := by
  let decomposition :=
    Yul.FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?
      hObjects hRepresents hNames
  have hEntriesOk :
      Yul.SolcValidation.ProgramOkWithEntries? profile ordered.program
        decomposition.functionEntries = true := by
    simpa [decomposition,
      Yul.FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?]
      using hProgramOk
  exact compiledWithPassToEncodedBytecode decomposition
    hCompile hEntriesOk hScoped hSafety hResourceSafe hFrameSafe
    hYulInitial hYulDomain hAllocationInitial hTerminal

/-- One executable Solidity-frontend object code artifact reaches the resolved
Assembly target through the ordered Yul theorem. Conversion, ordered
acceptance, Yul lowering, and lower-pass compilation are all recovered from
the compiler result rather than supplied as public evidence. -/
theorem compiledFrontendCodeToAssemblyTarget
    {object : Solidity.Frontend.Object}
    {context : Solidity.Frontend.ObjectBuiltinContext}
    {codeArtifact : Solidity.Frontend.Object.CompiledCodeArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hCode : object.compileOrderedCodeArtifactIn? context =
      some codeArtifact)
    (hScoped : codeArtifact.lower.toFunctions.Scoped)
    (hSafety : Functions.AllocationInteractionSafety.SourceSafety
      codeArtifact.lower.toFunctions.memoryContract)
    (hResourceSafe : Functions.AllocationInteractionProgram.ResourceSafe
      codeArtifact.compiled.metadata.allocation
      codeArtifact.lower.toFunctions
      (Yul.FunctionsInteractionStaticCost.programBudget
        codeArtifact.ordered.program (sourceFuel + 1)))
    (hFrameSafe :
      Functions.AllocationInteractionProgram.StructuredFrameSafe
        codeArtifact.compiled.metadata.allocation
        codeArtifact.lower.toFunctions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hAllocationInitial :
      Functions.AllocationInteractionProgram.InitialRel
        codeArtifact.lower.toFunctions.memoryContract
        functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [codeArtifact.ordered.program.contract.dispatcher])
        (some codeArtifact.ordered.program.contract) source)) :
    CompiledOpenWorldRel codeArtifact.ordered.program codeArtifact.lower
      codeArtifact.compiled sourceFuel source expressionsState := by
  obtain ⟨hResolved, hOrdered, hLower, hCompile, _hBridge, _hBytes⟩ :=
    Solidity.Frontend.Object.compileOrderedCodeArtifactIn?_parts hCode
  have hSource :=
    Solidity.Frontend.Object.toSolcYulOrderedProgram?_source hOrdered
  have hProgramOk :=
    Solidity.Frontend.Object.toSolcYulOrderedProgram?_programOkWithEntries
      hOrdered
  exact compiledOrderedYulToEncodedBytecode
    hLower hSource.1 hSource.2.1 hCompile hProgramOk hScoped hSafety
    hResourceSafe hFrameSafe hYulInitial hYulDomain hAllocationInitial
    hTerminal

/-- The root code retained by the recursive object-image artifact satisfies the
same ordered Yul-to-Assembly theorem. Child layout, payload, marker, and image
construction remain owned by the frontend artifact compiler. -/
theorem compiledObjectRootToAssemblyTarget
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List (Solidity.Frontend.Name ×
      Solidity.Frontend.Word)}
    {objectArtifact : Solidity.Frontend.Object.CompiledObjectArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hObject : object.compileObjectArtifactWithLinkerSymbols?
      linkerSymbols = some objectArtifact)
    (hScoped : objectArtifact.codeArtifact.lower.toFunctions.Scoped)
    (hSafety : Functions.AllocationInteractionSafety.SourceSafety
      objectArtifact.codeArtifact.lower.toFunctions.memoryContract)
    (hResourceSafe : Functions.AllocationInteractionProgram.ResourceSafe
      objectArtifact.codeArtifact.compiled.metadata.allocation
      objectArtifact.codeArtifact.lower.toFunctions
      (Yul.FunctionsInteractionStaticCost.programBudget
        objectArtifact.codeArtifact.ordered.program (sourceFuel + 1)))
    (hFrameSafe :
      Functions.AllocationInteractionProgram.StructuredFrameSafe
        objectArtifact.codeArtifact.compiled.metadata.allocation
        objectArtifact.codeArtifact.lower.toFunctions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names
          objectArtifact.codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hAllocationInitial :
      Functions.AllocationInteractionProgram.InitialRel
        objectArtifact.codeArtifact.lower.toFunctions.memoryContract
        functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [objectArtifact.codeArtifact.ordered.program.contract.dispatcher])
        (some objectArtifact.codeArtifact.ordered.program.contract) source)) :
    CompiledOpenWorldRel objectArtifact.codeArtifact.ordered.program
      objectArtifact.codeArtifact.lower objectArtifact.codeArtifact.compiled
      sourceFuel source expressionsState := by
  obtain ⟨childArtifacts, plan, hChildren, hPlan, hFinish, hCode,
      hArtifactChildren, hContext, hChildImages, hPayload, hImage⟩ :=
    Solidity.Frontend.Object.compileObjectArtifactWithLinkerSymbols?_parts
      hObject
  exact compiledFrontendCodeToAssemblyTarget hCode hScoped hSafety
    hResourceSafe hFrameSafe hYulInitial hYulDomain hAllocationInitial
    hTerminal

/-- A recursively compiled Solidity object is structurally related to its
exact raw image for every ordered resource/external answer sequence. The
relation may be used in either direction to select a concrete branch. -/
theorem compiledObjectRootToBytecode
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List (Solidity.Frontend.Name ×
      Solidity.Frontend.Word)}
    {objectArtifact : Solidity.Frontend.Object.CompiledObjectArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (hObject : object.compileObjectArtifactWithLinkerSymbols?
      linkerSymbols = some objectArtifact)
    (hScoped : objectArtifact.codeArtifact.lower.toFunctions.Scoped)
    (hSafety : Functions.AllocationInteractionSafety.SourceSafety
      objectArtifact.codeArtifact.lower.toFunctions.memoryContract)
    (hResourceSafe : Functions.AllocationInteractionProgram.ResourceSafe
      objectArtifact.codeArtifact.compiled.metadata.allocation
      objectArtifact.codeArtifact.lower.toFunctions
      (Yul.FunctionsInteractionStaticCost.programBudget
        objectArtifact.codeArtifact.ordered.program (sourceFuel + 1)))
    (hFrameSafe :
      Functions.AllocationInteractionProgram.StructuredFrameSafe
        objectArtifact.codeArtifact.compiled.metadata.allocation
        objectArtifact.codeArtifact.lower.toFunctions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names
          objectArtifact.codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hAllocationInitial :
      Functions.AllocationInteractionProgram.InitialRel
        objectArtifact.codeArtifact.lower.toFunctions.memoryContract
        functionsState expressionsState)
    (hCodeImage : Yul.InteractionSemantics.State.CodeImageInstalled source
      (Assembly.Bytecode.ofList objectArtifact.image.bytes))
    (hTerminal : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [objectArtifact.codeArtifact.ordered.program.contract.dispatcher])
        (some objectArtifact.codeArtifact.ordered.program.contract) source)) :
    Solidity.Frontend.Object.CompiledObjectArtifact.ValidFor
        linkerSymbols object objectArtifact /\
      expressionsState.evm.executionEnv.codeBytes =
          Assembly.Bytecode.ofList objectArtifact.image.bytes /\
        exists targetFuel,
          Simulation.Interaction.Rel
              (CompiledBytecodeDoneRel objectArtifact.codeArtifact.lower
                objectArtifact.codeArtifact.compiled)
              (Yul.InteractionSemantics.exec (sourceFuel + 1)
                (.Block
                  [objectArtifact.codeArtifact.ordered.program.contract.dispatcher])
                (some objectArtifact.codeArtifact.ordered.program.contract)
                source)
              (Assembly.Bytecode.InteractionSemantics.openRunNResult
                (Assembly.Bytecode.ofList objectArtifact.image.bytes)
                targetFuel
                { expressionsState.evm with
                  pc := EvmYul.UInt256.ofNat 0 }) /\
            ∀ {externalTranscript fullTranscript targetResult},
              Simulation.Interaction.Executes
                (Assembly.InteractionConcreteResources.openRunNResult
                  objectArtifact.codeArtifact.compiled.target targetFuel
                  { expressionsState.evm with
                    pc := EvmYul.UInt256.ofNat 0 })
                externalTranscript (.ok (targetResult, fullTranscript)) ->
              ∃ sourceDone,
                Simulation.Interaction.Executes
                  (Yul.InteractionSemantics.exec (sourceFuel + 1)
                    (.Block
                      [objectArtifact.codeArtifact.ordered.program.contract.dispatcher])
                    (some
                      objectArtifact.codeArtifact.ordered.program.contract)
                    source)
                  fullTranscript sourceDone /\
                CompiledBytecodeDoneRel objectArtifact.codeArtifact.lower
                  objectArtifact.codeArtifact.compiled
                  sourceDone (.ok targetResult) := by
  have hValid :=
    Solidity.Frontend.Object.compileObjectArtifactWithLinkerSymbols?_valid
      object linkerSymbols objectArtifact hObject
  have hFunctionsCodeImage := hYulInitial.targetCodeImage hCodeImage
  refine ⟨hValid,
    hAllocationInitial.targetCodeImage hFunctionsCodeImage, ?_⟩
  have hCompiled := compiledObjectRootToAssemblyTarget
    hObject hScoped hSafety hResourceSafe hFrameSafe hYulInitial hYulDomain
    hAllocationInitial hTerminal
  have hDecoding :=
    Solidity.Frontend.Object.compileObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject
  exact hCompiled.observedBytecodeReplay hDecoding hTerminal

/-- Public proposition for open-world terminal compiler correctness. Its
premises are source-facing; all lowering artifacts are hidden inside
`CompiledOpenWorldRel`. -/
def OpenWorldTerminalCorrect : Prop :=
  forall
    (profile : Yul.SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (objects : Objects.Program)
    (compiledArtifact : Objects.Program.CompileArtifact)
    (sourceFuel : Nat)
    (source : Yul.InteractionSemantics.State)
    (functionsState : Functions.InteractionSemantics.State)
    (expressionsState : Expressions.InteractionSemantics.RunState),
    Yul.Program.toObjectsCanonical? sourceProgram = some objects ->
    Objects.Program.compileArtifact? objects = some compiledArtifact ->
    Yul.SolcValidation.ProgramOkWith? profile sourceProgram = true ->
    objects.toFunctions.Scoped ->
    Functions.AllocationInteractionSafety.SourceSafety
      objects.toFunctions.memoryContract ->
    Functions.AllocationInteractionProgram.ResourceSafe
      compiledArtifact.metadata.allocation objects.toFunctions
      (Yul.FunctionsInteractionStaticCost.programBudget
        sourceProgram (sourceFuel + 1)) ->
    Functions.AllocationInteractionProgram.StructuredFrameSafe
      compiledArtifact.metadata.allocation objects.toFunctions ->
    Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState ->
    Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars ->
    Functions.AllocationInteractionProgram.InitialRel
      objects.toFunctions.memoryContract functionsState expressionsState ->
    Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceTerminal
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source) ->
    CompiledOpenWorldRel sourceProgram objects compiledArtifact
      sourceFuel source expressionsState

theorem openWorldTerminalCorrect : OpenWorldTerminalCorrect := by
  intro profile sourceProgram objects compiledArtifact sourceFuel source
    functionsState expressionsState hObjects hCompile hProgramOk hScoped
    hSafety hResourceSafe hFrameSafe hYulInitial hYulDomain
    hAllocationInitial hTerminal
  exact compiledYulToEncodedBytecode
    hObjects hCompile hProgramOk hScoped hSafety hResourceSafe hFrameSafe
    hYulInitial hYulDomain hAllocationInitial hTerminal

end OpenInteractionComposition
end Compiler
end EvmCompiler
