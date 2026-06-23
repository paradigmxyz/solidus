import EvmCompiler.Yul.FunctionsInteractionProgram
import EvmCompiler.Functions.StackRecursivePreservation
import EvmCompiler.Functions.StackPressureNormalizationProgram
import EvmCompiler.Expressions.InteractionPreservation
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

/-- Terminal Yul preservation through the adjacent Functions normalization
and checked stack allocator. The normalization is compiler-computed and its
exact open-semantics equality bridges the existing Yul and allocation owners. -/
theorem yulToNormalizedStackExpressionsTerminal
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {normalized : Functions.Program}
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
    (hNormalize : normalized =
      Functions.StackPressureNormalization.Program.normalize
        objects.toFunctions)
    (hWF : normalized.WF)
    (hScoped : normalized.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported normalized)
    (hLower :
      Functions.StackLowering.lowerProgram? normalized = some locals)
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
  have hYulRelNormalized : Simulation.Interaction.Rel
      Yul.FunctionsInteractionProgram.DoneRel
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Program.openRunState
        functionsFuel normalized functionsState) := by
    rw [hNormalize,
      Functions.StackPressureNormalization.Program.normalize_openRunState]
    exact hYulRel
  have hFunctionsHalted : Simulation.Interaction.AllDone
      Functions.StackRecursivePreservation.ProgramSourceHalted
      (Functions.InteractionSemantics.Program.openRunState
        functionsFuel normalized functionsState) := by
    rw [hNormalize,
      Functions.StackPressureNormalization.Program.normalize_openRunState]
    apply Simulation.Interaction.AllDone.mono hYulTargetHalted
    intro outcome hOutcome
    simpa [functionsFuel,
      Yul.FunctionsInteractionProgram.TargetHalted,
      Functions.StackRecursivePreservation.ProgramSourceHalted] using hOutcome
  obtain ⟨targetFuel, hStackRel, hStackHalted⟩ :=
    Functions.StackRecursivePreservation.compiledProgramBodyTerminal
      normalized locals expressions functionsFuel hWF hScoped
      hSupported hLower hCompile hStackInitial hFunctionsHalted
  refine ⟨targetFuel, ?_, hStackHalted⟩
  simpa [YulStackExpressionsDoneRel] using
    Simulation.Interaction.Rel.trans hYulRelNormalized hStackRel

/-- Finished Yul preservation through normalization and checked stack
allocation. This adjacent upper theorem includes supported runtime errors; it
does not claim the still-terminal-only Structured-to-bytecode boundary. -/
theorem yulToNormalizedStackExpressionsFinished
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {normalized : Functions.Program}
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
    (hNormalize : normalized =
      Functions.StackPressureNormalization.Program.normalize
        objects.toFunctions)
    (hWF : normalized.WF)
    (hScoped : normalized.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported normalized)
    (hLower :
      Functions.StackLowering.lowerProgram? normalized = some locals)
    (hCompile :
      Locals.Program.toExpressions? locals = some expressions)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial (Yul.Contract.names sourceProgram.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
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
          Functions.StackRecursivePreservation.ProgramTargetFinished
          (Expressions.InteractionSemantics.Block.openRun expressions
            targetFuel expressions.body expressionsState) := by
  let functionsFuel :=
    Yul.FunctionsInteractionStaticCost.programBudget
      sourceProgram (sourceFuel + 1)
  have hYul := Yul.FunctionsInteractionProgram.dispatcherForward
    (sourceFuel := sourceFuel)
    hDecomposition hProgramOk hYulInitial hYulDomain
  obtain ⟨hYulRel, hYulTargetFinished⟩ :=
    Yul.FunctionsInteractionProgram.finishedRel hYul hFinished
  have hYulRelNormalized : Simulation.Interaction.Rel
      Yul.FunctionsInteractionProgram.DoneRel
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Program.openRunState
        functionsFuel normalized functionsState) := by
    rw [hNormalize,
      Functions.StackPressureNormalization.Program.normalize_openRunState]
    exact hYulRel
  have hFunctionsFinished : Simulation.Interaction.AllDone
      Functions.StackRecursivePreservation.ProgramSourceFinished
      (Functions.InteractionSemantics.Program.openRunState
        functionsFuel normalized functionsState) := by
    rw [hNormalize,
      Functions.StackPressureNormalization.Program.normalize_openRunState]
    apply Simulation.Interaction.AllDone.mono hYulTargetFinished
    intro outcome hOutcome
    simpa [functionsFuel,
      Yul.FunctionsInteractionProgram.TargetFinished,
      Functions.StackRecursivePreservation.ProgramSourceFinished] using
      hOutcome
  obtain ⟨targetFuel, hStackRel, hStackFinished⟩ :=
    Functions.StackRecursivePreservation.compiledProgramBodyFinished
      normalized locals expressions functionsFuel hWF hScoped
      hSupported hLower hCompile hStackInitial hFunctionsFinished
  refine ⟨targetFuel, ?_, hStackFinished⟩
  simpa [YulStackExpressionsDoneRel] using
    Simulation.Interaction.Rel.trans hYulRelNormalized hStackRel

/-- Compose the checked Yul-to-Functions whole-program theorem with the
allocation pass's checked whole-main theorem. No compiler recursion or
generated-code reasoning occurs in this module. -/
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

/-- The Expressions-to-Structured adapter is transparent for stopped
outcomes, including errors. -/
theorem stackExpressionsToStructuredStopped
    {expressions : Expressions.Program} {targetFuel : Nat}
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hRel : Simulation.Interaction.Rel
      YulStackExpressionsDoneRel sourceRun
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target))
    (hStopped : Simulation.Interaction.AllDone
      Functions.StackRecursivePreservation.ProgramTargetStopped
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target)) :
    Simulation.Interaction.Rel
        YulStackExpressionsDoneRel sourceRun
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured target) ∧
      Simulation.Interaction.AllDone
        Structured.InteractionTerminalPreservation.OpenOutcome.SourceStopped
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured target) := by
  change Simulation.Interaction.Rel
    YulStackExpressionsDoneRel sourceRun
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hRel
  change Simulation.Interaction.AllDone
    Functions.StackRecursivePreservation.ProgramTargetStopped
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hStopped
  rw [Expressions.InteractionPreservation.Program.openRunState_toStructured]
    at hRel hStopped
  refine ⟨hRel, ?_⟩
  apply Simulation.Interaction.AllDone.mono hStopped
  intro outcome hOutcome
  simpa [Functions.StackRecursivePreservation.ProgramTargetStopped,
    Structured.InteractionTerminalPreservation.OpenOutcome.SourceStopped]
    using hOutcome

/-- The transparent Expressions-to-Structured adapter preserves genuine
completion, excluding structural `OutOfFuel` on both sides. -/
theorem stackExpressionsToStructuredFinished
    {expressions : Expressions.Program} {targetFuel : Nat}
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hRel : Simulation.Interaction.Rel
      YulStackExpressionsDoneRel sourceRun
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target))
    (hFinished : Simulation.Interaction.AllDone
      Functions.StackRecursivePreservation.ProgramTargetFinished
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target)) :
    Simulation.Interaction.Rel
        YulStackExpressionsDoneRel sourceRun
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured target) ∧
      Simulation.Interaction.AllDone
        Structured.InteractionTerminalPreservation.OpenOutcome.SourceFinished
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured target) := by
  change Simulation.Interaction.Rel
    YulStackExpressionsDoneRel sourceRun
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hRel
  change Simulation.Interaction.AllDone
    Functions.StackRecursivePreservation.ProgramTargetFinished
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hFinished
  rw [Expressions.InteractionPreservation.Program.openRunState_toStructured]
    at hRel hFinished
  refine ⟨hRel, ?_⟩
  apply Simulation.Interaction.AllDone.mono hFinished
  intro outcome hOutcome
  simpa [Functions.StackRecursivePreservation.ProgramTargetFinished,
    Structured.InteractionTerminalPreservation.OpenOutcome.SourceFinished]
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

/-- The normalized stack path composed with the transparent
Expressions-to-Structured adapter. -/
theorem yulToNormalizedStackStructuredTerminal
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {normalized : Functions.Program}
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
    (hNormalize : normalized =
      Functions.StackPressureNormalization.Program.normalize
        objects.toFunctions)
    (hWF : normalized.WF)
    (hScoped : normalized.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported normalized)
    (hLower :
      Functions.StackLowering.lowerProgram? normalized = some locals)
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
    yulToNormalizedStackExpressionsTerminal hDecomposition hProgramOk
      hNormalize hWF hScoped hSupported hLower hCompile hYulInitial
      hYulDomain hStackInitial hTerminal
  exact ⟨targetFuel,
    stackExpressionsToStructuredTerminal hRel hHalted⟩

/-- Full terminal Yul-to-Structured open-world preservation, composed only
from the two adjacent upper boundaries and the transparent adapter equality. -/
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

theorem StructuredBytecodeDoneRel.targetFinished
    {source : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      source entryShapes cfg}
    {assembly : Assembly.Program}
    {returns : List Structured.ReturnDest}
    {sourceDone : Except Structured.EVMException Structured.Outcome}
    {targetDone : Assembly.Source.ExecutionOutcome}
    (hSourceFinished :
      Structured.InteractionTerminalPreservation.OpenOutcome.SourceFinished
        sourceDone)
    (hRel : StructuredBytecodeDoneRel source entryShapes cfg generated
      assembly returns sourceDone targetDone) :
    Assembly.InteractionSemantics.Finished targetDone := by
  rcases hRel with ⟨cfgDone, hStructured, hAssembly⟩
  have hSafe :=
    Structured.InteractionTerminalPreservation.OpenOutcome.assemblySafeFinished_of_related
      hStructured hSourceFinished
  exact
    TypedCfg.InteractionPreservation.OpenBlock.finished_of_assemblySafeFinished
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

/-- All-finished Structured-to-Assembly source preservation, composed from the
adjacent generated-CFG and certified-lowering theorems. -/
theorem structuredToAssemblySourceFinished
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
    (hSourceFinished : Simulation.Interaction.AllDone
      Structured.InteractionTerminalPreservation.OpenOutcome.SourceFinished
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
    Structured.InteractionTerminalPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_finished
      hGenerate
      (TypedCfg.Program.compileCertified?_wellTyped hCompile)
      hSourceWF hFrameSafe sourceFuel sourceState hSourceFinished
  have hEntry : cfg.entry = Structured.TypedCfgCompiler.entryLabel := by
    simpa using congrArg TypedCfg.Program.entry generated.cfgEq
  have hStructured := hStructuredFor cfgState hStructuredInitial
  have hCfgSafe :=
    Structured.InteractionTerminalPreservation.OpenOutcome.allDone_assemblySafeFinished
      hStructured hSourceFinished
  have hCfgSafeAtEntry : Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.AssemblySafeFinished
      (TypedCfg.InteractionSemantics.Program.openRunN
        cfg cfgFuel cfg.entry cfgState) := by
    rw [hEntry]
    simpa [cfgFuel] using hCfgSafe
  have hCfgAssembly :=
    TypedCfg.InteractionPreservation.Program.compileCertified?_entry_openRunN_assembly_finished_rel
      cfgFuel hCompile hIndependent hAssemblyPc hAssemblyInitial
        hCfgSafeAtEntry
  refine ⟨generated, ?_⟩
  rw [hEntry] at hCfgAssembly
  simpa [StructuredBytecodeDoneRel, cfgFuel, assemblyFuel] using
    Simulation.Interaction.Rel.trans hStructured hCfgAssembly

/-- End-to-end terminal outcome relation obtained by composing the upper Yul
relation with the lower Structured-to-bytecode relation. -/
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

/-- The checked Functions normalization composed horizontally before the
stack allocator and the existing lower Assembly source theorem. -/
theorem yulNormalizedStackToAssemblySource
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {normalized : Functions.Program}
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
    (hNormalize : normalized =
      Functions.StackPressureNormalization.Program.normalize
        objects.toFunctions)
    (hWF : normalized.WF)
    (hScoped : normalized.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported normalized)
    (hLower :
      Functions.StackLowering.lowerProgram? normalized = some locals)
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
    yulToNormalizedStackStructuredTerminal hDecomposition hProgramOk
      hNormalize hWF hScoped hSupported hLower hExpressionsCompile
      hYulInitial hYulDomain hStackInitial hTerminal
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

/-- All-finished normalized Yul composition through the logical Assembly
source semantics. Every compiler artifact is discharged by its adjacent
owner, and the computed allocation budget cannot truncate a finished source
branch. -/
theorem yulNormalizedStackToAssemblySourceFinished
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {normalized : Functions.Program}
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
    (hNormalize : normalized =
      Functions.StackPressureNormalization.Program.normalize
        objects.toFunctions)
    (hWF : normalized.WF)
    (hScoped : normalized.Scoped)
    (hSupported :
      Functions.InteractionSemantics.Program.OpenSupported normalized)
    (hLower :
      Functions.StackLowering.lowerProgram? normalized = some locals)
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
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
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
                pc := EvmYul.UInt256.ofNat 0 }) ∧
          Simulation.Interaction.AllDone
            Assembly.InteractionSemantics.Finished
            (Assembly.InteractionSemantics.Source.openRunNResult
              artifact.target
              (Structured.InteractionStaticCost.blockBudget
                  expressions.toStructured structuredFuel
                  expressions.toStructured.body *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg)
              { expressionsState.evm with
                pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨structuredFuel, hExpressions, hExpressionsFinished⟩ :=
    yulToNormalizedStackExpressionsFinished hDecomposition hProgramOk
      hNormalize hWF hScoped hSupported hLower hExpressionsCompile
      hYulInitial hYulDomain hStackInitial hFinished
  obtain ⟨hUpper, hStructuredFinished⟩ :=
    stackExpressionsToStructuredFinished hExpressions hExpressionsFinished
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
    structuredToAssemblySourceFinished hGenerate hCompile hStructuredWF
      hFrameSafe hIndependent hStructuredFinished hStructuredInitial rfl
      hAssemblyInitial
  let assemblyFuel :=
    Structured.InteractionStaticCost.blockBudget
        expressions.toStructured structuredFuel
        expressions.toStructured.body *
      TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg
  have hAssemblyFinished : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.target assemblyFuel
        { expressionsState.evm with pc := EvmYul.UInt256.ofNat 0 }) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left
      hLowerRel hStructuredFinished
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro sourceDone targetDone hDone
    exact StructuredBytecodeDoneRel.targetFinished hDone.2 hDone.1
  refine ⟨structuredFuel, generated, ?_, ?_⟩
  · have hComposed := Simulation.Interaction.Rel.trans hUpper hLowerRel
    have hReturns : expressionsState.returns = [] := hStackInitial.returns
    simpa [YulStackBytecodeDoneRel, hReturns, assemblyFuel] using hComposed
  · simpa [assemblyFuel] using hAssemblyFinished

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

/-- Public terminal relation for a checked recursive object artifact. The
TypedCfg generation witness is compiler-produced proof machinery and is hidden
behind the artifact-level relation rather than exposed by the end-to-end API. -/
def VerifiedStackObjectDoneRel
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Assembly.Source.ExecutionOutcome → Prop :=
  fun sourceDone targetDone =>
    ∃ generated :
        Structured.TypedCfgPreservation.Program.GeneratedContext
          artifact.codeArtifact.compiled.expressions.toStructured
          artifact.codeArtifact.compiled.entryShapes
          artifact.codeArtifact.compiled.cfg,
      YulStackCompactDoneRel
        artifact.codeArtifact.compiled.expressions.toStructured
        artifact.codeArtifact.compiled.entryShapes
        artifact.codeArtifact.compiled.cfg generated
        artifact.codeArtifact.compiled.certified.target
        sourceDone targetDone

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

/-- Compose a finished logical Assembly run with compact bytes protected by the
compiler-owned invalid sentinel. -/
theorem stackAssemblyToCompactBytecodeFinished
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
    (payload : List UInt8)
    (hRel : Simulation.Interaction.Rel
      (YulStackBytecodeDoneRel structured entryShapes cfg generated assembly)
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Assembly.InteractionSemantics.Source.openRunNResult
        assembly assemblyFuel targetState))
    (hCompile : Assembly.Compact.compile? assembly pinnedPushPcs = some compact)
    (hTargetPc : targetState.pc = EvmYul.UInt256.ofNat 0)
    (hAssemblyFinished : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        assembly assemblyFuel targetState)) :
    Simulation.Interaction.Rel
      (YulStackCompactDoneRel structured entryShapes cfg generated assembly)
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (compact.bytes.toList ++
            (Assembly.Compact.encodeInstr (.prim .invalid) ++ payload)))
        (2 * assemblyFuel) targetState) := by
  have hCompact :=
    Assembly.Compact.InteractionSemantics.compile?_source_openRunNResult_finished_rel
      hCompile payload assemblyFuel 0 hTargetPc hTargetPc
        (Assembly.SameRuntimeData.refl targetState) hAssemblyFinished
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
      _hPins, hCompact, hBytes, _hMarker⟩ :=
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
  obtain ⟨hNormalize, _hSourceSupported, hNormalizedSupported, hStackLower,
      hExpressions, hStructuredWF, _hShapes, hGenerate, _hWellTyped,
      hIndependent, hCertified, _hTarget, _hWindow, hNormalizedAccepted,
      _hSourceAccepted⟩ :=
    Compiler.StackArtifact.compile?_parts hStackArtifact
  have hAssembly := Compiler.StackArtifact.compile?_assembly hStackArtifact
  have hFrameSafe :=
    Compiler.StackArtifact.compile?_frameSafe hStackArtifact
  obtain ⟨structuredFuel, generated, hAssemblySource⟩ :=
    yulNormalizedStackToAssemblySource decomposition hProgramOk hNormalize
      hNormalizedAccepted.1 hNormalizedAccepted.2 hNormalizedSupported
      hStackLower hExpressions hYulInitial hYulDomain hStackInitial hGenerate
      hCertified hStructuredWF hFrameSafe hIndependent hTerminal
  have hAccepted : Assembly.Accepted
      codeArtifact.compiled.certified.target :=
    Assembly.Preservation.compile?_some_accepted hAssembly
  have hCompactRel := stackAssemblyToCompactBytecode
    (Solidity.Frontend.Object.verifiedCodeSentinel ++ suffix) hAssemblySource
    hCompact rfl hTerminal
  refine ⟨structuredFuel, hAccepted, generated, ?_⟩
  rw [hBytes]
  simpa [List.append_assoc] using hCompactRel

/-- A checked frontend stack-code artifact preserves every genuinely finished
source branch through its sentinel-protected compact bytes. -/
theorem compiledVerifiedStackCodeToRawBytecodeFinished
    {object : Solidity.Frontend.Object}
    {context : Solidity.Frontend.ObjectBuiltinContext}
    {codeArtifact : Solidity.Frontend.Object.VerifiedStackCodeArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (payload : List UInt8 := [])
    (hCode : object.compileVerifiedStackCodeArtifactIn? context =
      some codeArtifact)
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
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
              (Assembly.Bytecode.ofList (codeArtifact.bytes ++ payload))
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
      _hPins, hCompact, hBytes, _hMarker⟩ :=
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
  obtain ⟨hNormalize, _hSourceSupported, hNormalizedSupported, hStackLower,
      hExpressions, hStructuredWF, _hShapes, hGenerate, _hWellTyped,
      hIndependent, hCertified, _hTarget, _hWindow, hNormalizedAccepted,
      _hSourceAccepted⟩ :=
    Compiler.StackArtifact.compile?_parts hStackArtifact
  have hAssembly := Compiler.StackArtifact.compile?_assembly hStackArtifact
  have hFrameSafe :=
    Compiler.StackArtifact.compile?_frameSafe hStackArtifact
  obtain ⟨structuredFuel, generated, hAssemblySource,
      hAssemblyFinished⟩ :=
    yulNormalizedStackToAssemblySourceFinished decomposition hProgramOk
      hNormalize hNormalizedAccepted.1 hNormalizedAccepted.2
      hNormalizedSupported hStackLower hExpressions hYulInitial hYulDomain
      hStackInitial hGenerate hCertified hStructuredWF hFrameSafe
      hIndependent hFinished
  have hAccepted : Assembly.Accepted
      codeArtifact.compiled.certified.target :=
    Assembly.Preservation.compile?_some_accepted hAssembly
  have hCompactRel := stackAssemblyToCompactBytecodeFinished payload
    hAssemblySource hCompact rfl hAssemblyFinished
  refine ⟨structuredFuel, hAccepted, generated, ?_⟩
  rw [hBytes]
  simpa [List.append_assoc] using hCompactRel

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
      (suffix := plan.payload) hCode hYulInitial hYulDomain hStackInitial
      hTerminal
  simpa [hImage] using hResult

/-- Recursive checked object construction preserves all finished source
branches through the exact root image, including its invalid code/data
sentinel and computed payload. -/
theorem compiledVerifiedStackObjectToRawBytecodeFinished
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
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names
          artifact.codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
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
    compiledVerifiedStackCodeToRawBytecodeFinished
      (payload := plan.payload) hCode hYulInitial hYulDomain hStackInitial
      hFinished
  simpa [hImage] using hResult

/-- Public object composition with all compiler-generated TypedCfg evidence
discharged behind `VerifiedStackObjectDoneRel`. -/
theorem compiledVerifiedStackObjectToRawBytecodePublic
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
        Simulation.Interaction.Rel
          (VerifiedStackObjectDoneRel artifact)
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
  obtain ⟨structuredFuel, hAccepted, generated, hRel⟩ :=
    compiledVerifiedStackObjectToRawBytecode hObject hYulInitial hYulDomain
      hStackInitial hTerminal
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact Simulation.Interaction.Rel.mono hRel
    (fun _ _ hDone => ⟨generated, hDone⟩)

/-- Public all-finished object composition. Compiler-generated TypedCfg
evidence remains hidden behind `VerifiedStackObjectDoneRel`. -/
theorem compiledVerifiedStackObjectToRawBytecodeFinishedPublic
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
    (hYulInitial : Yul.FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : Yul.FunctionsInteractionRelation.TargetDomainWithin
      (Yul.Fresh.initial
        (Yul.Contract.names
          artifact.codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract) source)) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (VerifiedStackObjectDoneRel artifact)
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
  obtain ⟨structuredFuel, hAccepted, generated, hRel⟩ :=
    compiledVerifiedStackObjectToRawBytecodeFinished hObject hYulInitial
      hYulDomain hStackInitial hFinished
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact Simulation.Interaction.Rel.mono hRel
    (fun _ _ hDone => ⟨generated, hDone⟩)

end OpenInteractionComposition
end Compiler
end EvmCompiler
