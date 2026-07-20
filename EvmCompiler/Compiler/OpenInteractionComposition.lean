import EvmCompiler.Yul.FunctionsInteractionProgram
import EvmCompiler.Functions.StackRecursivePreservation
import EvmCompiler.Functions.StackPressureNormalizationProgram
import EvmCompiler.Expressions.InteractionPreservation
import EvmCompiler.Structured.InteractionTerminalPreservation
import EvmCompiler.Structured.InteractionTruncationOwnerPreservation
import EvmCompiler.TypedCfg.InteractionPreservation
import EvmCompiler.TypedCfg.InteractionPrefixPreservation
import EvmCompiler.TypedCfg.PeepholeTransfer
import EvmCompiler.Structured.PeepholeSourceCongr
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

/-- Unconditional finite-prefix preservation through Functions normalization
and checked stack allocation. `sourceFuel` selects the observed Yul prefix;
all ordered open effects before source `OutOfFuel` are preserved exactly. -/
theorem yulToNormalizedStackExpressionsForward
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
      Locals.Ctx.initial.layout [] [] functionsState expressionsState) :
    ∃ targetFuel,
      Simulation.Interaction.ForwardRel
        Yul.FunctionsInteractionPrimitive.Truncated
        YulStackExpressionsDoneRel
        (Yul.InteractionSemantics.exec (sourceFuel + 1)
          (.Block [sourceProgram.contract.dispatcher])
          (some sourceProgram.contract) source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          targetFuel expressions.body expressionsState) := by
  let functionsFuel :=
    Yul.FunctionsInteractionStaticCost.programBudget
      sourceProgram (sourceFuel + 1)
  have hYul := Yul.FunctionsInteractionProgram.dispatcherForward
    (sourceFuel := sourceFuel)
    hDecomposition hProgramOk hYulInitial hYulDomain
  have hYulNormalized : Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated
      Yul.FunctionsInteractionProgram.DoneRel
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [sourceProgram.contract.dispatcher])
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Program.openRunState
        functionsFuel normalized functionsState) := by
    rw [hNormalize,
      Functions.StackPressureNormalization.Program.normalize_openRunState]
    exact hYul
  obtain ⟨targetFuel, hStack⟩ :=
    Functions.StackRecursivePreservation.compiledProgramBodyForward
      normalized locals expressions functionsFuel hWF hScoped hSupported
      hLower hCompile hStackInitial
  refine ⟨targetFuel, ?_⟩
  have hComposed := Simulation.Interaction.ForwardRel.trans
    hYulNormalized hStack (fun sourceDone middleError hDone hTruncated => by
      have hOutOfFuel : middleError = .OutOfFuel := hTruncated
      subst middleError
      exact
        Yul.FunctionsInteractionProgram.DoneRel.sourceTruncated_of_targetOutOfFuel
          hDone)
  simpa [YulStackExpressionsDoneRel] using hComposed

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

/-- The transparent Expressions-to-Structured adapter preserves the complete
finite-prefix relation without any terminality premise. -/
theorem stackExpressionsToStructuredForward
    {expressions : Expressions.Program} {targetFuel : Nat}
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {target : Expressions.InteractionSemantics.RunState}
    (hRel : Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated
      YulStackExpressionsDoneRel sourceRun
      (Expressions.InteractionSemantics.Block.openRun expressions
        targetFuel expressions.body target)) :
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated
      YulStackExpressionsDoneRel sourceRun
      (Structured.InteractionSemantics.Program.openRunState
        targetFuel expressions.toStructured target) := by
  change Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    YulStackExpressionsDoneRel sourceRun
    (Expressions.InteractionSemantics.Program.openRunState
      targetFuel expressions target) at hRel
  rw [Expressions.InteractionPreservation.Program.openRunState_toStructured]
    at hRel
  exact hRel

/-- Unconditional finite-prefix preservation through the complete upper
stack-only spine, ending at the Structured owner boundary. -/
theorem yulToNormalizedStackStructuredForward
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
      Locals.Ctx.initial.layout [] [] functionsState expressionsState) :
    ∃ targetFuel,
      Simulation.Interaction.ForwardRel
        Yul.FunctionsInteractionPrimitive.Truncated
        YulStackExpressionsDoneRel
        (Yul.InteractionSemantics.exec (sourceFuel + 1)
          (.Block [sourceProgram.contract.dispatcher])
          (some sourceProgram.contract) source)
        (Structured.InteractionSemantics.Program.openRunState
          targetFuel expressions.toStructured expressionsState) := by
  obtain ⟨targetFuel, hForward⟩ :=
    yulToNormalizedStackExpressionsForward hDecomposition hProgramOk
      hNormalize hWF hScoped hSupported hLower hCompile hYulInitial
      hYulDomain hStackInitial
  exact ⟨targetFuel, stackExpressionsToStructuredForward hForward⟩

/-- Outcome relation obtained by composing the upper stack-only spine with the
checked Structured-to-TypedCfg generation boundary. -/
def YulStackTypedCfgDoneRel
    (structured : Structured.Program)
    (entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Except Structured.EVMException
        TypedCfg.Control.Program.RunResult → Prop :=
  fun sourceDone targetDone =>
    ∃ structuredDone,
      YulStackExpressionsDoneRel sourceDone structuredDone ∧
        Structured.InteractionControlPreservation.OpenOutcome.SegmentDoneRel
          generated.main { procs := structured.procs }
          Structured.ProcLabel.programEnd [] [] .stop
          structuredDone targetDone

/-- Unconditional finite-prefix preservation from validated Yul through
checked Structured generation. Compiler-owned CFG context and target fuel are
existential outputs, never public evidence. -/
theorem yulToNormalizedStackTypedCfgForward
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {normalized : Functions.Program}
    {locals : Locals.Program} {expressions : Expressions.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
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
    (hWellTyped : cfg.WellTyped)
    (hStructuredWF : expressions.toStructured.WF)
    (hFrameSafe : expressions.toStructured.FrameSafe) :
    ∃ structuredFuel,
      ∃ generated :
          Structured.TypedCfgPreservation.Program.GeneratedContext
            expressions.toStructured entryShapes cfg,
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (YulStackTypedCfgDoneRel expressions.toStructured entryShapes cfg
            generated)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (TypedCfg.InteractionSemantics.Program.openRunNResultWithStop
            (Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.topPolicy
              generated expressionsState)
            cfg
            (Structured.InteractionStaticCost.blockBudget
              expressions.toStructured structuredFuel
              expressions.toStructured.body)
            Structured.TypedCfgCompiler.entryLabel expressionsState.evm) := by
  obtain ⟨structuredFuel, hUpper⟩ :=
    yulToNormalizedStackStructuredForward hDecomposition hProgramOk
      hNormalize hWF hScoped hSupported hLower hExpressionsCompile
      hYulInitial hYulDomain hStackInitial
  have hReturns : expressionsState.returns = [] := hStackInitial.returns
  have hExpressionsInitial :
      expressionsState = Structured.RunState.initial expressionsState.evm := by
    rcases expressionsState with ⟨evm, returns⟩
    simp only [Structured.RunState.initial]
    simp only at hReturns
    subst returns
    rfl
  have hStructuredInitial :
      Structured.TypedCfgPreservation.StateRel expressionsState []
        expressionsState.evm := by
    rw [hExpressionsInitial]
    exact Structured.TypedCfgPreservation.StateRel.initial _
  obtain ⟨generated, hLowerFor⟩ :=
    Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_forward
      hGenerate hWellTyped hStructuredWF hFrameSafe structuredFuel
        expressionsState
  have hLower := hLowerFor expressionsState.evm hStructuredInitial
  have hComposed := Simulation.Interaction.ForwardRel.trans
    hUpper hLower (fun sourceDone middleError hDone hTruncated => by
      have hOutOfFuel : middleError = .OutOfFuel := hTruncated
      subst middleError
      rcases hDone with ⟨functionsDone, hYul, hStack⟩
      cases hStack with
      | @error functionsError targetError hError =>
          have hFunctionsOutOfFuel : functionsError = .OutOfFuel :=
            hError rfl
          subst functionsError
          exact
            Yul.FunctionsInteractionProgram.DoneRel.sourceTruncated_of_targetOutOfFuel
              hYul)
  refine ⟨structuredFuel, generated, ?_⟩
  simpa [YulStackTypedCfgDoneRel, hReturns,
    Structured.InteractionSemantics.Program.openRunState,
    Structured.InteractionSemantics.Block.openRun] using hComposed

/-- Outcome relation for the canonical whole-program TypedCfg prefix runner. -/
def YulStackTypedCfgPrefixDoneRel
    (structured : Structured.Program)
    (entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes)
    (cfg : TypedCfg.Program)
    (generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Except Structured.EVMException TypedCfg.Outcome → Prop :=
  fun sourceDone targetDone =>
    ∃ structuredDone,
      YulStackExpressionsDoneRel sourceDone structuredDone ∧
        Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel
          generated structuredDone targetDone

/-- Unconditional validated-Yul preservation to canonical TypedCfg finite
prefixes. The generated context and target budget are compiler outputs. -/
theorem yulToNormalizedStackTypedCfgPrefixForward
    {profile : Yul.SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {objects : Objects.Program}
    {normalized : Functions.Program}
    {locals : Locals.Program} {expressions : Expressions.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
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
    (hWellTyped : cfg.WellTyped)
    (hStructuredWF : expressions.toStructured.WF)
    (hFrameSafe : expressions.toStructured.FrameSafe) :
    ∃ structuredFuel,
      ∃ generated :
          Structured.TypedCfgPreservation.Program.GeneratedContext
            expressions.toStructured entryShapes cfg,
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (YulStackTypedCfgPrefixDoneRel expressions.toStructured entryShapes
            cfg generated)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (TypedCfg.InteractionSemantics.Program.openRunNPrefix cfg
            (Structured.InteractionStaticCost.blockBudget
              expressions.toStructured structuredFuel
              expressions.toStructured.body + 1)
            Structured.TypedCfgCompiler.entryLabel expressionsState.evm) := by
  obtain ⟨structuredFuel, hUpper⟩ :=
    yulToNormalizedStackStructuredForward hDecomposition hProgramOk
      hNormalize hWF hScoped hSupported hLower hExpressionsCompile
      hYulInitial hYulDomain hStackInitial
  have hReturns : expressionsState.returns = [] := hStackInitial.returns
  have hStructuredInitial :
      Structured.TypedCfgPreservation.StateRel expressionsState []
        expressionsState.evm := by
    rcases expressionsState with ⟨evm, returns⟩
    simp only at hReturns
    subst returns
    exact Structured.TypedCfgPreservation.StateRel.initial evm
  let generated :=
    Structured.TypedCfgPreservation.Program.GeneratedContext.of_generate
      hGenerate hWellTyped
  have hLowerPrefix :=
    Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.main_prefix_forward
      generated hStructuredWF hFrameSafe structuredFuel expressionsState
        expressionsState.evm hStructuredInitial
  have hComposed := Simulation.Interaction.ForwardRel.trans
    hUpper hLowerPrefix (fun sourceDone middleError hDone hTruncated => by
      have hOutOfFuel : middleError = .OutOfFuel := hTruncated
      subst middleError
      rcases hDone with ⟨functionsDone, hYul, hStack⟩
      cases hStack with
      | @error functionsError targetError hError =>
          have hFunctionsOutOfFuel : functionsError = .OutOfFuel := hError rfl
          subst functionsError
          exact
            Yul.FunctionsInteractionProgram.DoneRel.sourceTruncated_of_targetOutOfFuel
              hYul)
  refine ⟨structuredFuel, generated, ?_⟩
  simpa [YulStackTypedCfgPrefixDoneRel, hReturns,
    Structured.InteractionSemantics.Program.openRunState,
    Structured.InteractionSemantics.Block.openRun] using hComposed

/-- Outcome relation obtained by composing the canonical generated-CFG prefix
with the adjacent certified Assembly lowering. -/
def YulStackAssemblyPrefixDoneRel
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
    exists cfgDone,
      YulStackTypedCfgPrefixDoneRel structured entryShapes cfg generated
          sourceDone cfgDone /\
        TypedCfg.InteractionPreservation.OpenBlock.RunSimulates
          assembly cfgDone targetDone

/-- Unconditional validated-Yul preservation to Assembly source prefixes.
Only concrete completed CFG branches require terminal safety; a source
truncation preserves its exact ordered transcript and releases the suffix. -/
theorem yulToNormalizedStackAssemblyPrefixForward
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
    {assemblyState : Assembly.EVMState}
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
    (hWellTyped : cfg.WellTyped)
    (hStructuredWF : expressions.toStructured.WF)
    (hFrameSafe : expressions.toStructured.FrameSafe)
    (hCompile : (TypedCfg.Peephole.peepholeProgram cfg).compileCertified? =
      some artifact)
    (hIndependent : cfg.ProgramCounterIndependent)
    (hAssemblyPc : assemblyState.pc = EvmYul.UInt256.ofNat 0)
    (hAssemblyInitial :
      Assembly.SameRuntimeData expressionsState.evm assemblyState.incrPC) :
    exists structuredFuel,
      exists generated :
          Structured.TypedCfgPreservation.Program.GeneratedContext
            expressions.toStructured entryShapes cfg,
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (YulStackAssemblyPrefixDoneRel expressions.toStructured entryShapes
            cfg generated artifact.target)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block [sourceProgram.contract.dispatcher])
            (some sourceProgram.contract) source)
          (Assembly.InteractionSemantics.Source.openRunNResult
            artifact.target
            ((Structured.InteractionStaticCost.blockBudget
                expressions.toStructured structuredFuel
                expressions.toStructured.body + 1) *
              TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg)
            assemblyState) := by
  obtain ⟨structuredFuel, generated, hUpper⟩ :=
    yulToNormalizedStackTypedCfgPrefixForward hDecomposition hProgramOk
      hNormalize hWF hScoped hSupported hLower hExpressionsCompile
      hYulInitial hYulDomain hStackInitial hGenerate hWellTyped
      hStructuredWF hFrameSafe
  have hEntry : cfg.entry = Structured.TypedCfgCompiler.entryLabel := by
    simpa using congrArg TypedCfg.Program.entry generated.cfgEq
  have hIndepPeep :
      (TypedCfg.Peephole.peepholeProgram cfg).ProgramCounterIndependent :=
    TypedCfg.Peephole.peepholeProgram_programCounterIndependent hIndependent
  set budget :=
    Structured.InteractionStaticCost.blockBudget
        expressions.toStructured structuredFuel
        expressions.toStructured.body + 1 with hBudget
  have hFuelLe :
      budget *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
            (TypedCfg.Peephole.peepholeProgram cfg) ≤
        budget *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg :=
    Nat.mul_le_mul_left _
      (TypedCfg.Peephole.fuelBudget_peepholeProgram_le cfg)
  have hEntryReturns : expressionsState.returns = [] := hStackInitial.returns
  have hEntryInit :
      expressionsState = Structured.RunState.initial expressionsState.evm := by
    rcases expressionsState with ⟨evm, returns⟩
    simp only [Structured.RunState.initial]
    simp only at hEntryReturns
    subst returns
    rfl
  have hEntrySeedRel :
      Structured.TypedCfgPreservation.StateRel expressionsState []
        expressionsState.evm := by
    rw [hEntryInit]
    exact Structured.TypedCfgPreservation.StateRel.initial _
  have hEntrySeed :
      Structured.InteractionFrameConsistent.realizedWitnessFC
        expressions.toStructured cfg generated.calls cfg.entry expressionsState.evm :=
    TypedCfg.Peephole.realizedWitnessFC_entry_of_generated generated hEntrySeedRel
  refine ⟨structuredFuel, generated, ?_⟩
  apply Simulation.Interaction.ForwardRel.of_executes_or_follows
  intro transcript sourceDone hSourceExec
  rcases Simulation.Interaction.ForwardRel.executes_or_follows
      hUpper hSourceExec with hUpperTruncated | hUpperDone
  · rcases hUpperTruncated with
      ⟨sourceError, hSourceDone, hSourceTruncated, hCfgFollow⟩
    have hCfgFollowAtEntry : Simulation.Interaction.Follows
        (TypedCfg.InteractionSemantics.Program.openRunNPrefix cfg
          budget cfg.entry expressionsState.evm)
        transcript := by
      simpa [hEntry] using hCfgFollow
    have hCongr :=
      TypedCfg.Peephole.openRunNPrefix_peephole_congr_of_source generated
        hStructuredWF hWellTyped hIndependent
        budget cfg.entry expressionsState.evm expressionsState.evm
        hEntrySeed
        (Assembly.SameRuntimeData.refl _)
    obtain ⟨suffix, cfgDone, hCfgExec⟩ :=
      hCfgFollowAtEntry.exists_executes_extension
    obtain ⟨peepDone, hPeepExec, _hRuntimeRel⟩ :=
      Simulation.Interaction.Rel.executes hCongr hCfgExec
    have hFollowPeep : Simulation.Interaction.Follows
        (TypedCfg.InteractionSemantics.Program.openRunNPrefix
          (TypedCfg.Peephole.peepholeProgram cfg)
          budget cfg.entry expressionsState.evm)
        transcript :=
      Simulation.Interaction.Follows.prefix_of_append transcript suffix
        hPeepExec.follows
    have hAssemblyFollow :=
      TypedCfg.InteractionPrefixPreservation.Program.compileCertified?_entry_openRunNPrefix_assembly_follows
        hCompile hIndepPeep hAssemblyPc hAssemblyInitial hFollowPeep
    have hAssemblyFollowPad :=
      Assembly.InteractionSemantics.Source.openRunNResult_follows_of_le_follows
        hFuelLe hAssemblyFollow
    exact .inl
      ⟨sourceError, hSourceDone, hSourceTruncated, hAssemblyFollowPad⟩
  · rcases hUpperDone with ⟨cfgDone, hCfgExec, hRelated⟩
    rcases hRelated with ⟨structuredDone, hStack, hPrefix⟩
    have hCfgExecAtEntry : Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunNPrefix cfg
          budget cfg.entry expressionsState.evm)
        transcript cfgDone := by
      simpa [hEntry] using hCfgExec
    have hCfgSafe :=
      Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel.targetSafe
        hPrefix
    have hCongr :=
      TypedCfg.Peephole.openRunNPrefix_peephole_congr_of_source generated
        hStructuredWF hWellTyped hIndependent
        budget cfg.entry expressionsState.evm expressionsState.evm
        hEntrySeed
        (Assembly.SameRuntimeData.refl _)
    obtain ⟨peepDone, hPeepExec, hRuntimeRel⟩ :=
      Simulation.Interaction.Rel.executes hCongr hCfgExecAtEntry
    have hSafePeep :
        TypedCfg.InteractionSemantics.Program.PrefixAssemblySafe peepDone :=
      TypedCfg.Peephole.prefixAssemblySafe_of_runtimeRel hRuntimeRel hCfgSafe
    rcases
        TypedCfg.InteractionPrefixPreservation.Program.compileCertified?_entry_openRunNPrefix_assembly_branch
          hCompile hIndepPeep hAssemblyPc hAssemblyInitial
          hPeepExec hSafePeep with hCfgTruncated | hAssemblyDone
    · rcases hCfgTruncated with
        ⟨peepError, hPeepDone, hPeepTruncated, hAssemblyFollow⟩
      subst hPeepDone
      have hCfgErr : cfgDone = Except.error peepError :=
        TypedCfg.Peephole.runtimeOutcomeRel_eq_error_right hRuntimeRel
      subst hCfgErr
      have hCfgOutOfFuel : peepError = .OutOfFuel :=
        (TypedCfg.InteractionSemantics.Program.prefixTruncated_iff peepError).mp
          hPeepTruncated
      have hAssemblyFollowPad :=
        Assembly.InteractionSemantics.Source.openRunNResult_follows_of_le_follows
          hFuelLe hAssemblyFollow
      cases hPrefix with
      | @error structuredError _ hStructural =>
          have hStructuredOutOfFuel : structuredError = .OutOfFuel :=
            hStructural hCfgOutOfFuel
          subst structuredError
          rcases hStack with ⟨functionsDone, hYul, hFunctions⟩
          cases hFunctions with
          | @error functionsError _ hFunctionsError =>
              have hFunctionsOutOfFuel : functionsError = .OutOfFuel :=
                hFunctionsError rfl
              subst functionsError
              obtain ⟨sourceError, hSourceDone, hSourceTruncated⟩ :=
                Yul.FunctionsInteractionProgram.DoneRel.sourceTruncated_of_targetOutOfFuel
                  hYul
              exact .inl
                ⟨sourceError, hSourceDone, hSourceTruncated,
                  hAssemblyFollowPad⟩
    · rcases hAssemblyDone with ⟨assemblyDone, hAssemblyExec, hAssemblyRel⟩
      have hSimCfg :
          TypedCfg.InteractionPreservation.OpenBlock.RunSimulates
            artifact.target cfgDone assemblyDone :=
        TypedCfg.InteractionPreservation.OpenBlock.runtime_left hRuntimeRel
          hAssemblyRel
      have hFinished : Assembly.InteractionSemantics.Finished assemblyDone :=
        TypedCfg.InteractionPreservation.OpenBlock.finished_of_assemblySafeFinished
          (TypedCfg.Peephole.assemblySafeFinished_of_prefixAssemblySafe
            hSafePeep)
          hAssemblyRel
      have hAssemblyExecPad :
          Simulation.Interaction.Executes
            (Assembly.InteractionSemantics.Source.openRunNResult
              artifact.target
              (budget *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg)
              assemblyState)
            transcript assemblyDone := by
        have hEq :
            budget *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  (TypedCfg.Peephole.peepholeProgram cfg) +
              (budget *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg -
                budget *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    (TypedCfg.Peephole.peepholeProgram cfg)) =
              budget *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg :=
          Nat.add_sub_of_le hFuelLe
        rw [← hEq]
        cases assemblyDone with
        | error error =>
            exact
              Assembly.InteractionSemantics.Source.openRunNResult_error_add_executes
                hAssemblyExec
        | ok result =>
            cases result with
            | running s =>
                exact absurd hFinished
                  (by simp [Assembly.InteractionSemantics.Finished])
            | halted halt =>
                exact
                  Assembly.InteractionSemantics.Source.openRunNResult_halted_add_executes
                    hAssemblyExec
      exact .inr
        ⟨assemblyDone, hAssemblyExecPad,
          ⟨cfgDone, ⟨structuredDone, hStack, hPrefix⟩, hSimCfg⟩⟩

theorem YulStackAssemblyPrefixDoneRel.targetFinished
    {structured : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg}
    {assembly : Assembly.Program}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Assembly.Source.ExecutionOutcome}
    (hRel : YulStackAssemblyPrefixDoneRel structured entryShapes cfg
      generated assembly sourceDone targetDone) :
    Assembly.InteractionSemantics.Finished targetDone := by
  rcases hRel with
    ⟨cfgDone, ⟨structuredDone, _hStack, hPrefix⟩, hAssembly⟩
  have hSafe :=
    Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel.targetSafe
      hPrefix
  have hSafeFinished :
      TypedCfg.InteractionSemantics.Program.AssemblySafeFinished cfgDone := by
    cases cfgDone with
    | error error => trivial
    | ok outcome =>
        cases outcome <;> exact hSafe
  exact
    TypedCfg.InteractionPreservation.OpenBlock.finished_of_assemblySafeFinished
      hSafeFinished hAssembly

/-- Outcome relation after the adjacent compact physical encoding. -/
def YulStackCompactPrefixDoneRel
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
    exists assemblyDone,
      YulStackAssemblyPrefixDoneRel structured entryShapes cfg generated
          assembly sourceDone assemblyDone /\
        Assembly.Compact.RuntimeOutcomeRel targetDone assemblyDone

/-- Compose an unconditional Yul-to-Assembly prefix theorem with the
Assembly-owned compact encoder. -/
theorem stackAssemblyPrefixToCompactBytecode
    {structured : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      structured entryShapes cfg}
    {assembly : Assembly.Program}
    {pinnedPushPcs : List Nat}
    {compact : Assembly.Compact.Artifact}
    {sourceRun : Simulation.Interaction
      Yul.InteractionSemantics.Failure Yul.InteractionSemantics.State}
    {assemblyFuel : Nat}
    {assemblyState compactState : Assembly.EVMState}
    (payload : List UInt8)
    (hRel : Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated
      (YulStackAssemblyPrefixDoneRel structured entryShapes cfg generated
        assembly)
      sourceRun
      (Assembly.InteractionSemantics.Source.openRunNResult
        assembly assemblyFuel assemblyState))
    (hCompile : Assembly.Compact.compile? assembly pinnedPushPcs = some compact)
    (hAssemblyPc : assemblyState.pc = EvmYul.UInt256.ofNat 0)
    (hCompactPc : compactState.pc = EvmYul.UInt256.ofNat 0)
    (hInitial : Assembly.SameRuntimeData compactState assemblyState) :
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated
      (YulStackCompactPrefixDoneRel structured entryShapes cfg generated
        assembly)
      sourceRun
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (compact.bytes.toList ++
            (Assembly.Compact.encodeInstr (.prim .invalid) ++ payload)))
        (2 * assemblyFuel) compactState) := by
  apply Simulation.Interaction.ForwardRel.of_executes_or_follows
  intro transcript sourceDone hSourceExec
  rcases Simulation.Interaction.ForwardRel.executes_or_follows
      hRel hSourceExec with hTruncated | hDone
  · rcases hTruncated with
      ⟨sourceError, hSourceDone, hSourceTruncated, hAssemblyFollow⟩
    obtain ⟨suffix, assemblyDone, hAssemblyExec⟩ :=
      hAssemblyFollow.exists_executes_extension
    have hCompactBranch :=
      Assembly.Compact.InteractionSemantics.compile?_source_openRunNResult_branch
        hCompile payload assemblyFuel hCompactPc hAssemblyPc hInitial
          hAssemblyExec
    have hCompactFollow :=
      Assembly.Compact.InteractionSemantics.PrefixBranchResult.follows
        hCompactBranch
    exact .inl
      ⟨sourceError, hSourceDone, hSourceTruncated,
        Simulation.Interaction.Follows.prefix_of_append
          transcript suffix hCompactFollow⟩
  · rcases hDone with ⟨assemblyDone, hAssemblyExec, hAssemblyRel⟩
    have hAssemblyFinished :=
      YulStackAssemblyPrefixDoneRel.targetFinished hAssemblyRel
    have hCompactBranch :=
      Assembly.Compact.InteractionSemantics.compile?_source_openRunNResult_branch
        hCompile payload assemblyFuel hCompactPc hAssemblyPc hInitial
          hAssemblyExec
    cases assemblyDone with
    | error assemblyError =>
        rcases hCompactBranch with
          ⟨compactDone, hCompactExec, hCompactRel⟩
        exact .inr
          ⟨compactDone, hCompactExec,
            ⟨.error assemblyError, hAssemblyRel, hCompactRel⟩⟩
    | ok assemblyResult =>
        cases assemblyResult with
        | running assemblyFinal => cases hAssemblyFinished
        | halted assemblyHalt =>
            rcases hCompactBranch with
              ⟨compactDone, hCompactExec, hCompactRel⟩
            exact .inr
              ⟨compactDone, hCompactExec,
                ⟨.ok (.halted assemblyHalt), hAssemblyRel, hCompactRel⟩⟩

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
    (hCompile : (TypedCfg.Peephole.peepholeProgram cfg).compileCertified? =
      some artifact)
    (hWellTyped : cfg.WellTyped)
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
  have hIndepPeep :
      (TypedCfg.Peephole.peepholeProgram cfg).ProgramCounterIndependent :=
    TypedCfg.Peephole.peepholeProgram_programCounterIndependent hIndependent
  obtain ⟨generated, hStructuredFor⟩ :=
    Structured.InteractionTerminalPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_terminal
      hGenerate hWellTyped
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
  have hBridge :=
    TypedCfg.Peephole.openRunN_peephole_congr_of_source generated hSourceWF
      hWellTyped hIndependent
      cfgFuel cfg.entry cfgState cfgState
      (TypedCfg.Peephole.realizedWitnessFC_entry_of_generated generated
        hStructuredInitial)
      (Assembly.SameRuntimeData.refl _)
  have hCfgSafeAtEntryPeep : Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.AssemblySafeHalted
      (TypedCfg.InteractionSemantics.Program.openRunN
        (TypedCfg.Peephole.peepholeProgram cfg) cfgFuel cfg.entry cfgState) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left hBridge
      hCfgSafeAtEntry
    apply Simulation.Interaction.Rel.allDone_right hStrong
    rintro l r ⟨_hrel, hsafe⟩
    exact TypedCfg.Peephole.assemblySafeHalted_of_runtimeRel _hrel hsafe
  have hCfgAssemblyPeep :=
    TypedCfg.InteractionPreservation.Program.compileCertified?_entry_openRunN_assembly_rel
      cfgFuel hCompile hIndepPeep hAssemblyPc hAssemblyInitial
        hCfgSafeAtEntryPeep
  have hFuelLe :
      cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
            (TypedCfg.Peephole.peepholeProgram cfg) ≤
        cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg :=
    Nat.mul_le_mul_left _
      (TypedCfg.Peephole.fuelBudget_peepholeProgram_le cfg)
  have hFinishedPeep : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.target
        (cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
            (TypedCfg.Peephole.peepholeProgram cfg))
        assemblyState) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left hCfgAssemblyPeep
      hCfgSafeAtEntryPeep
    apply Simulation.Interaction.Rel.allDone_right hStrong
    rintro l r ⟨hsim, hsafe⟩
    have hT :=
      TypedCfg.InteractionPreservation.OpenBlock.terminal_of_assemblySafeHalted
        hsafe hsim
    cases r with
    | error e => exact hT.elim
    | ok res => exact hT
  have hCfgAssemblyPeepPad :=
    TypedCfg.Peephole.rel_openRunNResult_finished_pad hFuelLe hFinishedPeep
      hCfgAssemblyPeep
  have hCfgAssembly :
      Simulation.Interaction.Rel
        (TypedCfg.InteractionPreservation.OpenBlock.RunSimulates artifact.target)
        (TypedCfg.InteractionSemantics.Program.openRunN
          cfg cfgFuel cfg.entry cfgState)
        (Assembly.InteractionSemantics.Source.openRunNResult
          artifact.target assemblyFuel assemblyState) := by
    apply Simulation.Interaction.Rel.mono
      (Simulation.Interaction.Rel.trans hBridge hCfgAssemblyPeepPad)
    rintro l r ⟨m, hrel, hsim⟩
    exact TypedCfg.InteractionPreservation.OpenBlock.runtime_left hrel hsim
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
    (hCompile : (TypedCfg.Peephole.peepholeProgram cfg).compileCertified? =
      some artifact)
    (hWellTyped : cfg.WellTyped)
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
  have hIndepPeep :
      (TypedCfg.Peephole.peepholeProgram cfg).ProgramCounterIndependent :=
    TypedCfg.Peephole.peepholeProgram_programCounterIndependent hIndependent
  obtain ⟨generated, hStructuredFor⟩ :=
    Structured.InteractionTerminalPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_terminal
      hGenerate hWellTyped
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
  have hBridge :=
    TypedCfg.Peephole.openRunN_peephole_congr_of_source generated hSourceWF
      hWellTyped hIndependent
      cfgFuel cfg.entry cfgState cfgState
      (TypedCfg.Peephole.realizedWitnessFC_entry_of_generated generated
        hStructuredInitial)
      (Assembly.SameRuntimeData.refl _)
  have hCfgSafeAtEntryPeep : Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.AssemblySafeHalted
      (TypedCfg.InteractionSemantics.Program.openRunN
        (TypedCfg.Peephole.peepholeProgram cfg) cfgFuel cfg.entry cfgState) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left hBridge
      hCfgSafeAtEntry
    apply Simulation.Interaction.Rel.allDone_right hStrong
    rintro l r ⟨_hrel, hsafe⟩
    exact TypedCfg.Peephole.assemblySafeHalted_of_runtimeRel _hrel hsafe
  have hCfgAssemblyPeep :=
    TypedCfg.InteractionPreservation.Program.compileCertified?_entry_openRunN_assembly_rel
      cfgFuel hCompile hIndepPeep hAssemblyPc hAssemblyInitial
        hCfgSafeAtEntryPeep
  have hFuelLe :
      cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
            (TypedCfg.Peephole.peepholeProgram cfg) ≤
        cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg :=
    Nat.mul_le_mul_left _
      (TypedCfg.Peephole.fuelBudget_peepholeProgram_le cfg)
  have hFinishedPeep : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.target
        (cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
            (TypedCfg.Peephole.peepholeProgram cfg))
        assemblyState) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left hCfgAssemblyPeep
      hCfgSafeAtEntryPeep
    apply Simulation.Interaction.Rel.allDone_right hStrong
    rintro l r ⟨hsim, hsafe⟩
    have hT :=
      TypedCfg.InteractionPreservation.OpenBlock.terminal_of_assemblySafeHalted
        hsafe hsim
    cases r with
    | error e => exact hT.elim
    | ok res => exact hT
  have hCfgAssemblyPeepPad :=
    TypedCfg.Peephole.rel_openRunNResult_finished_pad hFuelLe hFinishedPeep
      hCfgAssemblyPeep
  have hCfgAssembly :
      Simulation.Interaction.Rel
        (TypedCfg.InteractionPreservation.OpenBlock.RunSimulates artifact.target)
        (TypedCfg.InteractionSemantics.Program.openRunN
          cfg cfgFuel cfg.entry cfgState)
        (Assembly.InteractionSemantics.Source.openRunNResult
          artifact.target assemblyFuel assemblyState) := by
    apply Simulation.Interaction.Rel.mono
      (Simulation.Interaction.Rel.trans hBridge hCfgAssemblyPeepPad)
    rintro l r ⟨m, hrel, hsim⟩
    exact TypedCfg.InteractionPreservation.OpenBlock.runtime_left hrel hsim
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
    (hCompile : (TypedCfg.Peephole.peepholeProgram cfg).compileCertified? =
      some artifact)
    (hWellTyped : cfg.WellTyped)
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
  have hIndepPeep :
      (TypedCfg.Peephole.peepholeProgram cfg).ProgramCounterIndependent :=
    TypedCfg.Peephole.peepholeProgram_programCounterIndependent hIndependent
  obtain ⟨generated, hStructuredFor⟩ :=
    Structured.InteractionTerminalPreservation.OpenOutcome.GeneratedProgram.generateWithProcEntryShapes?_main_finished
      hGenerate hWellTyped
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
  have hBridge :=
    TypedCfg.Peephole.openRunN_peephole_congr_of_source generated hSourceWF
      hWellTyped hIndependent
      cfgFuel cfg.entry cfgState cfgState
      (TypedCfg.Peephole.realizedWitnessFC_entry_of_generated generated
        hStructuredInitial)
      (Assembly.SameRuntimeData.refl _)
  have hCfgSafeAtEntryPeep : Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.AssemblySafeFinished
      (TypedCfg.InteractionSemantics.Program.openRunN
        (TypedCfg.Peephole.peepholeProgram cfg) cfgFuel cfg.entry cfgState) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left hBridge
      hCfgSafeAtEntry
    apply Simulation.Interaction.Rel.allDone_right hStrong
    rintro l r ⟨_hrel, hsafe⟩
    exact TypedCfg.Peephole.assemblySafeFinished_of_runtimeRel _hrel hsafe
  have hCfgAssemblyPeep :=
    TypedCfg.InteractionPreservation.Program.compileCertified?_entry_openRunN_assembly_finished_rel
      cfgFuel hCompile hIndepPeep hAssemblyPc hAssemblyInitial
        hCfgSafeAtEntryPeep
  have hFuelLe :
      cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
            (TypedCfg.Peephole.peepholeProgram cfg) ≤
        cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget cfg :=
    Nat.mul_le_mul_left _
      (TypedCfg.Peephole.fuelBudget_peepholeProgram_le cfg)
  have hFinishedPeep : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Finished
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.target
        (cfgFuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
            (TypedCfg.Peephole.peepholeProgram cfg))
        assemblyState) := by
    have hStrong := Simulation.Interaction.Rel.strengthen_left hCfgAssemblyPeep
      hCfgSafeAtEntryPeep
    apply Simulation.Interaction.Rel.allDone_right hStrong
    rintro l r ⟨hsim, hsafe⟩
    exact
      TypedCfg.InteractionPreservation.OpenBlock.finished_of_assemblySafeFinished
        hsafe hsim
  have hCfgAssemblyPeepPad :=
    TypedCfg.Peephole.rel_openRunNResult_finished_pad hFuelLe hFinishedPeep
      hCfgAssemblyPeep
  have hCfgAssembly :
      Simulation.Interaction.Rel
        (TypedCfg.InteractionPreservation.OpenBlock.RunSimulates artifact.target)
        (TypedCfg.InteractionSemantics.Program.openRunN
          cfg cfgFuel cfg.entry cfgState)
        (Assembly.InteractionSemantics.Source.openRunNResult
          artifact.target assemblyFuel assemblyState) := by
    apply Simulation.Interaction.Rel.mono
      (Simulation.Interaction.Rel.trans hBridge hCfgAssemblyPeepPad)
    rintro l r ⟨m, hrel, hsim⟩
    exact TypedCfg.InteractionPreservation.OpenBlock.runtime_left hrel hsim
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
    (hCompile : (TypedCfg.Peephole.peepholeProgram cfg).compileCertified? =
      some artifact)
    (hWellTyped : cfg.WellTyped)
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
    structuredToEncodedBytecode hGenerate hCompile hWellTyped hStructuredWF
      hFrameSafe
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
    (hCompile : (TypedCfg.Peephole.peepholeProgram cfg).compileCertified? =
      some artifact)
    (hWellTyped : cfg.WellTyped)
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
    structuredToAssemblySource hGenerate hCompile hWellTyped hStructuredWF
      hFrameSafe hIndependent hStructuredHalted hStructuredInitial rfl
      hAssemblyInitial
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
    (hCompile : (TypedCfg.Peephole.peepholeProgram cfg).compileCertified? =
      some artifact)
    (hWellTyped : cfg.WellTyped)
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
    structuredToAssemblySource hGenerate hCompile hWellTyped hStructuredWF
      hFrameSafe hIndependent hStructuredHalted hStructuredInitial rfl
      hAssemblyInitial
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
    (hCompile : (TypedCfg.Peephole.peepholeProgram cfg).compileCertified? =
      some artifact)
    (hWellTyped : cfg.WellTyped)
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
    structuredToAssemblySourceFinished hGenerate hCompile hWellTyped
      hStructuredWF
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

/-- Public finite-prefix relation for a checked recursive object artifact.
Compiler-generated CFG context remains an existential implementation detail. -/
def VerifiedStackObjectPrefixDoneRel
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State ->
      Assembly.Source.ExecutionOutcome -> Prop :=
  fun sourceDone targetDone =>
    exists generated :
        Structured.TypedCfgPreservation.Program.GeneratedContext
          artifact.codeArtifact.compiled.expressions.toStructured
          artifact.codeArtifact.compiled.entryShapes
          artifact.codeArtifact.compiled.cfg,
      YulStackCompactPrefixDoneRel
        artifact.codeArtifact.compiled.expressions.toStructured
        artifact.codeArtifact.compiled.entryShapes
        artifact.codeArtifact.compiled.cfg generated
        artifact.codeArtifact.compiled.certified.target
        sourceDone targetDone

/-- A checked frontend stack-code artifact preserves every finite source
prefix through its exact compact bytes, without a terminality premise. -/
theorem compiledVerifiedStackCodeToRawBytecodeForward
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
      Locals.Ctx.initial.layout [] [] functionsState expressionsState) :
    exists structuredFuel,
      Assembly.Accepted codeArtifact.compiled.certified.target /\
        exists generated :
            Structured.TypedCfgPreservation.Program.GeneratedContext
              codeArtifact.compiled.expressions.toStructured
              codeArtifact.compiled.entryShapes codeArtifact.compiled.cfg,
          Simulation.Interaction.ForwardRel
            Yul.FunctionsInteractionPrimitive.Truncated
            (YulStackCompactPrefixDoneRel
              codeArtifact.compiled.expressions.toStructured
              codeArtifact.compiled.entryShapes codeArtifact.compiled.cfg
              generated codeArtifact.compiled.certified.target)
            (Yul.InteractionSemantics.exec (sourceFuel + 1)
              (.Block [codeArtifact.ordered.program.contract.dispatcher])
              (some codeArtifact.ordered.program.contract) source)
            (Assembly.Compact.InteractionSemantics.openRunNResult
              (Assembly.Bytecode.ofList (codeArtifact.bytes ++ payload))
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    codeArtifact.compiled.expressions.toStructured.body + 1) *
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
          codeArtifact.resolved.dialectProfile
          codeArtifact.ordered.program decomposition.functionEntries = true := by
    simpa [decomposition,
      Yul.FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?]
      using
        Solidity.Frontend.Object.toSolcYulOrderedProgram?_programOkWithEntries
          hOrdered
  obtain ⟨hNormalize, _hSourceSupported, hNormalizedSupported, hStackLower,
      hExpressions, hStructuredWF, _hShapes, hGenerate, hWellTyped,
      hIndependent, hCertified, _hTarget, _hWindow, hNormalizedAccepted,
      _hSourceAccepted⟩ :=
    Compiler.StackArtifact.compile?_parts hStackArtifact
  have hAssembly := Compiler.StackArtifact.compile?_assembly hStackArtifact
  have hFrameSafe := Compiler.StackArtifact.compile?_frameSafe hStackArtifact
  let targetState : Assembly.EVMState :=
    { expressionsState.evm with pc := EvmYul.UInt256.ofNat 0 }
  have hAssemblyInitial : Assembly.SameRuntimeData expressionsState.evm
      targetState.incrPC := by
    apply Assembly.SameRuntimeData.incrPC_right
    apply Assembly.SameRuntimeData.with_pc_right
    exact Assembly.SameRuntimeData.refl _
  obtain ⟨structuredFuel, generated, hAssemblyForward⟩ :=
    yulToNormalizedStackAssemblyPrefixForward decomposition hProgramOk
      hNormalize hNormalizedAccepted.1 hNormalizedAccepted.2
      hNormalizedSupported hStackLower hExpressions hYulInitial hYulDomain
      hStackInitial hGenerate hWellTyped hStructuredWF hFrameSafe hCertified
      hIndependent rfl hAssemblyInitial
  have hCompactForward := stackAssemblyPrefixToCompactBytecode payload
    hAssemblyForward hCompact rfl rfl (Assembly.SameRuntimeData.refl targetState)
  have hAccepted : Assembly.Accepted
      codeArtifact.compiled.certified.target :=
    Assembly.Preservation.compile?_some_accepted hAssembly
  refine ⟨structuredFuel, hAccepted, generated, ?_⟩
  rw [hBytes]
  simpa [targetState, List.append_assoc] using hCompactForward

/-- Recursive object construction preserves the root code prefix through the
exact checked object image. Child objects and data remain compiler-owned
payload bytes behind the root sentinel. -/
theorem compiledVerifiedStackObjectToRawBytecodeForward
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
      Locals.Ctx.initial.layout [] [] functionsState expressionsState) :
    exists structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target /\
        exists generated :
            Structured.TypedCfgPreservation.Program.GeneratedContext
              artifact.codeArtifact.compiled.expressions.toStructured
              artifact.codeArtifact.compiled.entryShapes
              artifact.codeArtifact.compiled.cfg,
          Simulation.Interaction.ForwardRel
            Yul.FunctionsInteractionPrimitive.Truncated
            (YulStackCompactPrefixDoneRel
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
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              { expressionsState.evm with
                pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      _hArtifactChildren, _hContext, _hChildImages, _hPayload, hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  have hResult :=
    compiledVerifiedStackCodeToRawBytecodeForward
      (sourceFuel := sourceFuel) (payload := plan.payload)
      hCode hYulInitial hYulDomain hStackInitial
  simpa [hImage] using hResult

/-- Public recursive-object prefix theorem with generated CFG context hidden
behind the artifact-level outcome relation. -/
theorem compiledVerifiedStackObjectToRawBytecodeForwardPublic
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
      Locals.Ctx.initial.layout [] [] functionsState expressionsState) :
    exists structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target /\
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (VerifiedStackObjectPrefixDoneRel artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract) source)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { expressionsState.evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨structuredFuel, hAccepted, generated, hForward⟩ :=
    compiledVerifiedStackObjectToRawBytecodeForward hObject hYulInitial
      hYulDomain hStackInitial
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact Simulation.Interaction.ForwardRel.mono hForward
    (fun _sourceDone _targetDone hDone => ⟨generated, hDone⟩)

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
          codeArtifact.resolved.dialectProfile
          codeArtifact.ordered.program decomposition.functionEntries = true := by
    simpa [decomposition,
      Yul.FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?]
      using
        Solidity.Frontend.Object.toSolcYulOrderedProgram?_programOkWithEntries
          hOrdered
  obtain ⟨hNormalize, _hSourceSupported, hNormalizedSupported, hStackLower,
      hExpressions, hStructuredWF, _hShapes, hGenerate, hWellTyped,
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
      hCertified hWellTyped hStructuredWF hFrameSafe hIndependent hTerminal
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
          codeArtifact.resolved.dialectProfile
          codeArtifact.ordered.program decomposition.functionEntries = true := by
    simpa [decomposition,
      Yul.FunctionsCompilerArtifact.passDecomposition_of_ordered_toObjects?]
      using
        Solidity.Frontend.Object.toSolcYulOrderedProgram?_programOkWithEntries
          hOrdered
  obtain ⟨hNormalize, _hSourceSupported, hNormalizedSupported, hStackLower,
      hExpressions, hStructuredWF, _hShapes, hGenerate, hWellTyped,
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
      hStackInitial hGenerate hCertified hWellTyped hStructuredWF hFrameSafe
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

/-!
Suffix-tolerant object corollaries.

Creation frames execute `image ++ constructorArgs`: the caller appends
ABI-encoded constructor arguments after the checked object image. The generic
cores above are already parametric in an arbitrary trailing payload, so these
corollaries simply instantiate them with `plan.payload ++ suffix` and rewrite
the checked image equation. The exact-image theorems are the `suffix := []`
instances.
-/

/-- Suffix-tolerant variant of `compiledVerifiedStackObjectToRawBytecodeForward`:
the finite-prefix relation holds against the checked image with any appended
caller-owned byte suffix. -/
theorem compiledVerifiedStackObjectToRawBytecodeForwardWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (suffix : List UInt8)
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
      Locals.Ctx.initial.layout [] [] functionsState expressionsState) :
    exists structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target /\
        exists generated :
            Structured.TypedCfgPreservation.Program.GeneratedContext
              artifact.codeArtifact.compiled.expressions.toStructured
              artifact.codeArtifact.compiled.entryShapes
              artifact.codeArtifact.compiled.cfg,
          Simulation.Interaction.ForwardRel
            Yul.FunctionsInteractionPrimitive.Truncated
            (YulStackCompactPrefixDoneRel
              artifact.codeArtifact.compiled.expressions.toStructured
              artifact.codeArtifact.compiled.entryShapes
              artifact.codeArtifact.compiled.cfg generated
              artifact.codeArtifact.compiled.certified.target)
            (Yul.InteractionSemantics.exec (sourceFuel + 1)
              (.Block
                [artifact.codeArtifact.ordered.program.contract.dispatcher])
              (some artifact.codeArtifact.ordered.program.contract) source)
            (Assembly.Compact.InteractionSemantics.openRunNResult
              (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              { expressionsState.evm with
                pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨_children, plan, _codeArtifact, _hChildren, _hPlan, _hFinish, hCode,
      _hArtifactChildren, _hContext, _hChildImages, _hPayload, hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  have hResult :=
    compiledVerifiedStackCodeToRawBytecodeForward
      (sourceFuel := sourceFuel) (payload := plan.payload ++ suffix)
      hCode hYulInitial hYulDomain hStackInitial
  simpa [hImage, List.append_assoc] using hResult

/-- Suffix-tolerant variant of
`compiledVerifiedStackObjectToRawBytecodeForwardPublic`. -/
theorem compiledVerifiedStackObjectToRawBytecodeForwardPublicWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (suffix : List UInt8)
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
      Locals.Ctx.initial.layout [] [] functionsState expressionsState) :
    exists structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target /\
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (VerifiedStackObjectPrefixDoneRel artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract) source)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { expressionsState.evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨structuredFuel, hAccepted, generated, hForward⟩ :=
    compiledVerifiedStackObjectToRawBytecodeForwardWithCodeSuffix suffix
      hObject hYulInitial hYulDomain hStackInitial
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact Simulation.Interaction.ForwardRel.mono hForward
    (fun _sourceDone _targetDone hDone => ⟨generated, hDone⟩)

/-- Suffix-tolerant variant of `compiledVerifiedStackObjectToRawBytecodePublic`
(terminal source runs). -/
theorem compiledVerifiedStackObjectToRawBytecodePublicWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (suffix : List UInt8)
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
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
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
      (suffix := plan.payload ++ suffix) hCode hYulInitial hYulDomain
      hStackInitial hTerminal
  obtain ⟨structuredFuel, hAccepted, generated, hRel⟩ := hResult
  refine ⟨structuredFuel, hAccepted, ?_⟩
  have hRelImage :
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
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (2 *
            (Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body *
              TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                artifact.codeArtifact.compiled.cfg))
          { expressionsState.evm with
            pc := EvmYul.UInt256.ofNat 0 }) := by
    simpa [hImage, List.append_assoc] using hRel
  exact Simulation.Interaction.Rel.mono hRelImage
    (fun _ _ hDone => ⟨generated, hDone⟩)

/-- Suffix-tolerant variant of
`compiledVerifiedStackObjectToRawBytecodeFinishedPublic`. -/
theorem compiledVerifiedStackObjectToRawBytecodeFinishedPublicWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {functionsState : Functions.InteractionSemantics.State}
    {expressionsState : Expressions.InteractionSemantics.RunState}
    (suffix : List UInt8)
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
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
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
      (payload := plan.payload ++ suffix) hCode hYulInitial hYulDomain
      hStackInitial hFinished
  obtain ⟨structuredFuel, hAccepted, generated, hRel⟩ := hResult
  refine ⟨structuredFuel, hAccepted, ?_⟩
  have hRelImage :
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
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (2 *
            (Structured.InteractionStaticCost.blockBudget
                artifact.codeArtifact.compiled.expressions.toStructured
                structuredFuel
                artifact.codeArtifact.compiled.expressions.toStructured.body *
              TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                artifact.codeArtifact.compiled.cfg))
          { expressionsState.evm with
            pc := EvmYul.UInt256.ofNat 0 }) := by
    simpa [hImage, List.append_assoc] using hRel
  exact Simulation.Interaction.Rel.mono hRelImage
    (fun _ _ hDone => ⟨generated, hDone⟩)

end OpenInteractionComposition
end Compiler
end EvmCompiler
