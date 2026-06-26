import EvmCompiler.Yul.EndToEnd
import EvmCompiler.Assembly.GasfulBridgeLayout

namespace EvmCompiler
namespace Yul
namespace EndToEnd

/-!
Gasful optimized-Yul composition.

`EndToEnd` stays as the short public open-bytecode spine.  This sibling module
adds the gasful target boundary by composing that spine with the explicit
`EVM.X`-to-open-bytecode bridge relation.
-/

/-- Composition point for a concrete gasful target run.  The source theorem
remains cost-model-free: `GAS` and `MSIZE` are open observations in the emitted
bytecode semantics, while `hGasful` supplies the concrete charged `EVM.X` run
that resolves those observations and accounts for out-of-gas and external
CALL/CREATE boundaries. -/
theorem optimizedSolcYulToGasfulRawBytecodeOfOpenRunBridge
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel gasFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    {transcript : Simulation.Interaction.Transcript}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hGasful :
      ∀ structuredFuel,
        Assembly.GasfulBridge.RunRefinesOpen
          (EvmYul.EVM.X gasFuel
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
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
              pc := EvmYul.UInt256.ofNat 0 })
          transcript) :
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
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpen
          (EvmYul.EVM.X gasFuel
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
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
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨structuredFuel, hAccepted, hForward⟩ :=
    optimizedSolcYulToRawBytecode (sourceFuel := sourceFuel)
      (baseSource := baseSource) hObject
  exact ⟨structuredFuel, hAccepted, hForward, hGasful structuredFuel⟩

/-- Public composition through the proved recursive frame bridge. Unlike
`optimizedSolcYulToGasfulRawBytecodeOfOpenRunBridge`, this theorem has no
caller-supplied run simulation or external-response oracle: the concrete
`EVM.X` run existentially determines the ordered open transcript. The sole
remaining target-side premise is that reachable parent states remain at
compiler-generated block, branch-midpoint, or checked-sentinel control points. -/
theorem verifiedArtifact_frameCodeInvariant_of_layout
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hLayout :
      Assembly.GasfulBridge.FrameLayoutInvariant
        artifact.codeArtifact.compact.program
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList artifact.image.bytes)
          (EvmYul.UInt256.ofNat 0))
        gasfulInitial) :
    Assembly.GasfulBridge.FrameCodeInvariant
      (Assembly.Bytecode.ofList artifact.image.bytes)
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.UInt256.ofNat 0))
      gasfulInitial := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  have hValid : artifact.codeArtifact.compact.program.Valid :=
    (Assembly.Compact.compile?_valid hCompact).wellFormed.1
  obtain ⟨plan, hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
      hObject
  have hSentinel : Assembly.Compact.decodeAt
      (Assembly.Bytecode.ofList artifact.image.bytes)
      (Assembly.Compact.Program.codeByteLength
        artifact.codeArtifact.compact.program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Solidity.Frontend.Object.verifiedCodeSentinel,
      List.append_assoc] using
      (Assembly.GasfulBridge.compact_compile_sentinel_decodeAt
        hCompact plan.payload)
  exact Assembly.GasfulBridge.frameCodeInvariant_of_layout hValid
    (Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject)
    hSentinel hLayout

theorem verifiedArtifact_frameLayoutInvariant_of_artifactFrameInvariant
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hFrame :
      Assembly.GasfulBridge.ArtifactFrameInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList artifact.image.bytes)
          (EvmYul.UInt256.ofNat 0))
        gasfulInitial) :
    Assembly.GasfulBridge.FrameLayoutInvariant
      artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList artifact.image.bytes)
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.UInt256.ofNat 0))
      gasfulInitial := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  exact Assembly.GasfulBridge.frameLayoutInvariant_of_artifactFrameInvariant
    hCompact hFrame

theorem optimizedSolcYulToGasfulRawBytecodeOfRecursiveFrameBridge
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hFrame :
      Assembly.GasfulBridge.ArtifactFrameInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList artifact.image.bytes)
          (EvmYul.UInt256.ofNat 0))
        gasfulInitial)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    ∃ structuredFuel transcript,
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
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpen
          (EvmYul.EVM.X
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
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
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨structuredFuel, hAccepted, hForward⟩ :=
    optimizedSolcYulToRawBytecode (sourceFuel := sourceFuel)
      (baseSource := baseSource) hObject
  have hLayout :=
    verifiedArtifact_frameLayoutInvariant_of_artifactFrameInvariant
      hObject hFrame
  have hCode := verifiedArtifact_frameCodeInvariant_of_layout hObject hLayout
  obtain ⟨transcript, hGasful⟩ :=
    Assembly.GasfulBridge.runRefinesOpen_recursive hCode
      (2 *
        ((Structured.InteractionStaticCost.blockBudget
            artifact.codeArtifact.compiled.expressions.toStructured
            structuredFuel
            artifact.codeArtifact.compiled.expressions.toStructured.body + 1) *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
            artifact.codeArtifact.compiled.cfg))
      Assembly.GasfulBridge.FrameReachable.initial hInitial
  exact ⟨structuredFuel, transcript, hAccepted, hForward, hGasful⟩

end EndToEnd
end Yul
end EvmCompiler
