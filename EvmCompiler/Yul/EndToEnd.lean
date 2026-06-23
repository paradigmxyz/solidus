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

theorem optimizedSolcYulToRawBytecode
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
        ∃ generated :
            Structured.TypedCfgPreservation.Program.GeneratedContext
              artifact.codeArtifact.compiled.expressions.toStructured
              artifact.codeArtifact.compiled.entryShapes
              artifact.codeArtifact.compiled.cfg,
          Simulation.Interaction.Rel
            (Compiler.OpenInteractionComposition.YulStackCompactDoneRel
              artifact.codeArtifact.compiled.expressions.toStructured
              artifact.codeArtifact.compiled.entryShapes
              artifact.codeArtifact.compiled.cfg generated
              artifact.codeArtifact.compiled.certified.target)
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
  Compiler.OpenInteractionComposition.compiledVerifiedStackObjectToRawBytecode
    hObject hYulInitial hYulDomain hStackInitial hTerminal

end EndToEnd
end Yul
end EvmCompiler
