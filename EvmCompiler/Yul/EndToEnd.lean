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

/-- Public optimized-solc-Yul theorem with all initial cross-layer relations
computed canonically. Its only semantic premise is an actual terminal source
execution from an empty top-level lexical frame. -/
theorem optimizedSolcYulToRawBytecode
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
  apply optimizedSolcYulToRawBytecodeOfRelatedInitial hObject
  · exact FunctionsInteractionRelation.ScopedStateRel.initial _
  · exact
      FunctionsInteractionRelation.ScopedStateRel.initial_targetDomainWithin
        _ _
  · exact Functions.StackRelation.initial _
  · exact hTerminal

/-- Canonical-initial-state all-finished theorem for the checked optimized-solc
Yul object path. -/
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
