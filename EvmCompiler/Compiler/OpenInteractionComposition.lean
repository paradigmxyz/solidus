import EvmCompiler.Yul.FunctionsInteractionProgram
import EvmCompiler.Functions.AllocationInteractionProgram
import EvmCompiler.Structured.InteractionTerminalPreservation
import EvmCompiler.TypedCfg.InteractionPreservation
import EvmCompiler.Assembly.InteractionPreservation

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

end OpenInteractionComposition
end Compiler
end EvmCompiler
