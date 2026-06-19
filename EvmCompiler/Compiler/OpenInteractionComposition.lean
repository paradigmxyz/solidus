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
      Yul.FunctionsCompilerArtifact.PassDecomposition sourceProgram objects)
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
  exact compiledWithPassToEncodedBytecode
    (Yul.FunctionsCompilerArtifact.passDecomposition_of_toObjectsCanonical?
      hObjects)
    hCompile hProgramOk hScoped hSafety hResourceSafe hFrameSafe
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
      Yul.SolcValidation.ProgramOkWith? profile ordered.program = true)
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
  exact compiledWithPassToEncodedBytecode
    (Yul.FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?
      hObjects hRepresents hNames)
    hCompile hProgramOk hScoped hSafety hResourceSafe hFrameSafe
    hYulInitial hYulDomain hAllocationInitial hTerminal

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
