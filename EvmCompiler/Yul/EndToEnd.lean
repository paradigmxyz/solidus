import EvmCompiler.Compiler.OpenInteractionComposition

namespace EvmCompiler
namespace Yul
namespace EndToEnd

/-!
Public optimized-Yul stack-only composition.

The theorem contains no compiler reasoning. Each lowering boundary is owned by
its adjacent pass; this module only exposes the checked recursive object result.
The Solidity-to-optimized-Yul transformation is the declared trusted solc
frontend boundary.
-/

/-- Unconditional optimized-solc-Yul finite-prefix correctness from arbitrary
related initial states. No source completion premise is required. -/
theorem optimizedSolcYulToRawBytecodeOfRelatedInitial
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
    (hYulInitial : FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : FunctionsInteractionRelation.TargetDomainWithin
      (Fresh.initial
        (Contract.names artifact.codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState) :
    exists structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target /\
        Simulation.Interaction.ForwardRel
          FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
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
              pc := EvmYul.UInt256.ofNat 0 }) :=
  Compiler.OpenInteractionComposition.compiledVerifiedStackObjectToRawBytecodeForwardPublic
    hObject hYulInitial hYulDomain hStackInitial

theorem optimizedSolcYulToRawBytecodeTerminalOfRelatedInitial
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
    (hYulInitial : FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : FunctionsInteractionRelation.TargetDomainWithin
      (Fresh.initial
        (Contract.names artifact.codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hTerminal : Simulation.Interaction.AllDone
      FunctionsInteractionProgram.SourceTerminal
      (InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract) source)) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
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
              pc := EvmYul.UInt256.ofNat 0 }) :=
  Compiler.OpenInteractionComposition.compiledVerifiedStackObjectToRawBytecodePublic
    hObject hYulInitial hYulDomain hStackInitial hTerminal

/-- Public optimized-Yul composition for every genuinely finished source
branch, including runtime errors. Structural interpreter `OutOfFuel` remains
excluded and cannot be introduced by the compiler-computed target budgets. -/
theorem optimizedSolcYulToRawBytecodeFinishedOfRelatedInitial
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
    (hYulInitial : FunctionsInteractionRelation.ScopedStateRel
      [] source functionsState)
    (hYulDomain : FunctionsInteractionRelation.TargetDomainWithin
      (Fresh.initial
        (Contract.names artifact.codeArtifact.ordered.program.contract)).used
      functionsState.vars)
    (hStackInitial : Functions.StackRelation.StateRel
      Locals.Ctx.initial.layout [] [] functionsState expressionsState)
    (hFinished : Simulation.Interaction.AllDone
      FunctionsInteractionProgram.SourceFinished
      (InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract) source)) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
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
              pc := EvmYul.UInt256.ofNat 0 }) :=
  Compiler.OpenInteractionComposition.compiledVerifiedStackObjectToRawBytecodeFinishedPublic
    hObject hYulInitial hYulDomain hStackInitial hFinished

/-- Canonical source state for the checked object's active code. The exact raw
byte image is installed before source execution, so source `CODESIZE` and
`CODECOPY` observe the same image decoded by the target machine. -/
def installedSourceState
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact)
    (base : EvmYul.SharedState .Yul) : Yul.InteractionSemantics.State :=
  FunctionsInteractionRelation.ScopedStateRel.installedSourceState
    artifact.codeArtifact.ordered.program.contract
    (Assembly.Bytecode.ofList artifact.image.bytes) base

def initialFunctionsState
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact)
    (base : EvmYul.SharedState .Yul) :
    Functions.InteractionSemantics.State :=
  FunctionsInteractionRelation.ScopedStateRel.initialTarget
    (FunctionsInteractionRelation.ScopedStateRel.installedSourceShared
      artifact.codeArtifact.ordered.program.contract
      (Assembly.Bytecode.ofList artifact.image.bytes) base)

def initialExpressionsState
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact)
    (base : EvmYul.SharedState .Yul) :
    Expressions.InteractionSemantics.RunState :=
  Functions.StackRelation.initialTarget
    (initialFunctionsState artifact base)

/-- Primary public theorem. Checked optimized Yul compilation preserves every
finite ordered open-world prefix, including divergence approximants, from the
canonical installed initial state. -/
theorem optimizedSolcYulToRawBytecode
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceState artifact baseSource))
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
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  apply optimizedSolcYulToRawBytecodeOfRelatedInitial hObject
  · exact FunctionsInteractionRelation.ScopedStateRel.initial _
  · exact
      FunctionsInteractionRelation.ScopedStateRel.initial_targetDomainWithin
        _ _
  · exact Functions.StackRelation.initial _

/-- Every genuinely finished source tree upgrades the unconditional finite-
prefix theorem to a full open-world relation. -/
theorem optimizedSolcYulToRawBytecodeFinished
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hFinished : Simulation.Interaction.AllDone
      FunctionsInteractionProgram.SourceFinished
      (InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (installedSourceState artifact baseSource))) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceState artifact baseSource))
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
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  obtain ⟨structuredFuel, hAccepted, hForward⟩ :=
    optimizedSolcYulToRawBytecode hObject
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact Simulation.Interaction.ForwardRel.rel_of_allDone hForward hFinished
    (fun failure hSourceFinished hTruncated =>
      FunctionsInteractionProgram.SourceFinished.excludes_truncated
        hSourceFinished hTruncated)

/-- Canonical terminal-only theorem retained for callers that require every
source branch to halt. -/
theorem optimizedSolcYulToRawBytecodeTerminal
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hTerminal : Simulation.Interaction.AllDone
      FunctionsInteractionProgram.SourceTerminal
      (InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (installedSourceState artifact baseSource))) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              (Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  apply optimizedSolcYulToRawBytecodeTerminalOfRelatedInitial hObject
  · exact FunctionsInteractionRelation.ScopedStateRel.initial _
  · exact
      FunctionsInteractionRelation.ScopedStateRel.initial_targetDomainWithin
        _ _
  · exact Functions.StackRelation.initial _
  · exact hTerminal

/-- Legacy all-finished theorem retaining the historical completed-run outcome
relation and fuel formula. -/
theorem optimizedSolcYulToRawBytecodeFinishedLegacy
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hFinished : Simulation.Interaction.AllDone
      FunctionsInteractionProgram.SourceFinished
      (InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (installedSourceState artifact baseSource))) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectDoneRel
            artifact)
          (InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              (Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  apply optimizedSolcYulToRawBytecodeFinishedOfRelatedInitial hObject
  · exact FunctionsInteractionRelation.ScopedStateRel.initial _
  · exact
      FunctionsInteractionRelation.ScopedStateRel.initial_targetDomainWithin
        _ _
  · exact Functions.StackRelation.initial _
  · exact hFinished

end EndToEnd
end Yul
end EvmCompiler
