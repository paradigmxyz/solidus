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
`EVM.X` run existentially determines the ordered open transcript. Checked
compact layout and one-step preservation derive all reachable block,
branch-midpoint, and sentinel control points from the verified artifact. -/
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

theorem verifiedArtifact_initialArtifactFramePoint
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsState artifact baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    Assembly.GasfulBridge.ArtifactFramePoint
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList artifact.image.bytes)
      gasfulInitial := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  apply Assembly.GasfulBridge.artifactFramePoint_initial hCompact
  · calc
      gasfulInitial.executionEnv.code =
          ({ (initialExpressionsState artifact baseSource).evm with
            pc := EvmYul.UInt256.ofNat 0 } : Assembly.EVMState).executionEnv.code :=
        hInitial.code_eq
      _ = Assembly.Bytecode.ofList artifact.image.bytes := by
        simp [initialExpressionsState, initialFunctionsState,
          Functions.StackRelation.initialTarget, Structured.RunState.initial,
          FunctionsInteractionRelation.ScopedStateRel.initialTarget,
          FunctionsInteractionRelation.ScopedStateRel.installedSourceShared,
          FunctionsInteractionRelation.SharedRel.toEVM,
          FunctionsInteractionRelation.ExecutionEnvRel.toEVM]
        simp [Simulation.OpenWorld.installEVMShared,
          Simulation.OpenWorld.installEVM]
  · simpa using hInitial.pc_eq

theorem verifiedArtifact_frameStepInvariant_of_ordinaryBoundary
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    {validJumps : Array Assembly.Word}
    (hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes)
        validJumps) :
    Assembly.GasfulBridge.ArtifactFrameStepInvariant
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList artifact.image.bytes)
      validJumps := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
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
  intro current next stepFuel hPoint hPrefix hStep hContinues
  exact (Assembly.GasfulBridge.artifactFrameStepInvariant_of_ordinaryBoundary
    (validJumps := validJumps) hCompact
    (Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject)
    hSentinel hOrdinary) hPoint hPrefix hStep hContinues

theorem verifiedArtifact_ordinaryBoundaryInvariant_of_remainingPrim
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    {validJumps : Array Assembly.Word}
    (hRemaining :
      Assembly.GasfulBridge.ArtifactRemainingPrimBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes)
        validJumps) :
    Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList artifact.image.bytes)
      validJumps := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  exact Assembly.GasfulBridge.artifactOrdinaryBoundaryStepInvariant_of_remainingPrim
    hCompact
    (Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject)
    hRemaining

theorem verifiedArtifact_ordinaryBoundaryInvariant
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (validJumps : Array Assembly.Word) :
    Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList artifact.image.bytes)
      validJumps := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  exact Assembly.GasfulBridge.artifactOrdinaryBoundaryStepInvariant_of_compile
    hCompact
    (Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject)

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
  have hInitialPoint :=
    verifiedArtifact_initialArtifactFramePoint hObject hInitial
  have hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList artifact.image.bytes)
          (EvmYul.UInt256.ofNat 0)) :=
    verifiedArtifact_ordinaryBoundaryInvariant hObject
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.UInt256.ofNat 0))
  have hStepInvariant : Assembly.GasfulBridge.ArtifactFrameStepInvariant
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList artifact.image.bytes)
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.UInt256.ofNat 0)) := by
    intro current next stepFuel hPoint hPrefix hStep hContinues
    exact (verifiedArtifact_frameStepInvariant_of_ordinaryBoundary
      (validJumps := EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.UInt256.ofNat 0)) hObject hOrdinary)
      hPoint hPrefix hStep hContinues
  have hFrame := Assembly.GasfulBridge.artifactFrameInvariant_of_step
    hInitialPoint hStepInvariant
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

/-!
Suffix-tolerant gasful endpoints.

Creation frames run the checked image with appended ABI-encoded constructor
arguments, so the concrete `EVM.X` entry is
`X f (D_J (image ++ args) 0) initial` — exactly EvmYul's creation-frame entry
point. `validJumps` is opaque to the bridge core; every wrapper below simply
re-derives the layout facts at the suffixed byte image using the
suffix-tolerant decoding and sentinel facts.
-/

theorem verifiedArtifact_frameCodeInvariant_of_layoutWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hLayout :
      Assembly.GasfulBridge.FrameLayoutInvariant
        artifact.codeArtifact.compact.program
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (EvmYul.UInt256.ofNat 0))
        gasfulInitial) :
    Assembly.GasfulBridge.FrameCodeInvariant
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
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
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (Assembly.Compact.Program.codeByteLength
        artifact.codeArtifact.compact.program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Solidity.Frontend.Object.verifiedCodeSentinel,
      List.append_assoc] using
      (Assembly.GasfulBridge.compact_compile_sentinel_decodeAt
        hCompact (plan.payload ++ suffix))
  exact Assembly.GasfulBridge.frameCodeInvariant_of_layout hValid
    (Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
      hObject suffix)
    hSentinel hLayout

theorem verifiedArtifact_frameLayoutInvariant_of_artifactFrameInvariantWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hFrame :
      Assembly.GasfulBridge.ArtifactFrameInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (EvmYul.UInt256.ofNat 0))
        gasfulInitial) :
    Assembly.GasfulBridge.FrameLayoutInvariant
      artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
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

theorem verifiedArtifact_initialArtifactFramePointWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
          pc := EvmYul.UInt256.ofNat 0 }) :
    Assembly.GasfulBridge.ArtifactFramePoint
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      gasfulInitial := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  apply Assembly.GasfulBridge.artifactFramePoint_initial hCompact
  · calc
      gasfulInitial.executionEnv.code =
          ({ (initialExpressionsStateWithCodeSuffix
              artifact suffix baseSource).evm with
            pc := EvmYul.UInt256.ofNat 0 } : Assembly.EVMState).executionEnv.code :=
        hInitial.code_eq
      _ = Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix) := by
        simp [initialExpressionsStateWithCodeSuffix,
          initialFunctionsStateWithCodeSuffix,
          Functions.StackRelation.initialTarget, Structured.RunState.initial,
          FunctionsInteractionRelation.ScopedStateRel.initialTarget,
          FunctionsInteractionRelation.ScopedStateRel.installedSourceShared,
          FunctionsInteractionRelation.SharedRel.toEVM,
          FunctionsInteractionRelation.ExecutionEnvRel.toEVM]
        simp [Simulation.OpenWorld.installEVMShared,
          Simulation.OpenWorld.installEVM]
  · simpa using hInitial.pc_eq

theorem verifiedArtifact_frameStepInvariant_of_ordinaryBoundaryWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    {validJumps : Array Assembly.Word}
    (hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        validJumps) :
    Assembly.GasfulBridge.ArtifactFrameStepInvariant
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      validJumps := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  obtain ⟨plan, hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
      hObject
  have hSentinel : Assembly.Compact.decodeAt
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (Assembly.Compact.Program.codeByteLength
        artifact.codeArtifact.compact.program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Solidity.Frontend.Object.verifiedCodeSentinel,
      List.append_assoc] using
      (Assembly.GasfulBridge.compact_compile_sentinel_decodeAt
        hCompact (plan.payload ++ suffix))
  intro current next stepFuel hPoint hPrefix hStep hContinues
  exact (Assembly.GasfulBridge.artifactFrameStepInvariant_of_ordinaryBoundary
    (validJumps := validJumps) hCompact
    (Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
      hObject suffix)
    hSentinel hOrdinary) hPoint hPrefix hStep hContinues

theorem verifiedArtifact_ordinaryBoundaryInvariantWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (validJumps : Array Assembly.Word) :
    Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      validJumps := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCode, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStack, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCode
  exact Assembly.GasfulBridge.artifactOrdinaryBoundaryStepInvariant_of_compile
    hCompact
    (Solidity.Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
      hObject suffix)

/-- Suffix-tolerant recursive frame-bridge endpoint. The concrete gasful run
starts at EvmYul's real creation-frame entry
`X f (D_J (image ++ suffix) 0) initial`; bad jumps into the suffix are
absorbed by `RunRefinesOpen.badJumpDestination`, and covered-path jump targets
come from the compact layout inside the checked image. -/
theorem optimizedSolcYulToGasfulRawBytecodeOfRecursiveFrameBridgeWithCodeSuffix
    {object : Solidity.Frontend.Object}
    {linkerSymbols : List
      (Solidity.Frontend.Name × Solidity.Frontend.Word)}
    {artifact : Solidity.Frontend.VerifiedStackObjectArtifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        { (initialExpressionsStateWithCodeSuffix
            artifact suffix baseSource).evm with
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
            (installedSourceStateWithCodeSuffix artifact suffix baseSource))
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
            { (initialExpressionsStateWithCodeSuffix
                artifact suffix baseSource).evm with
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
              (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
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
            { (initialExpressionsStateWithCodeSuffix
                artifact suffix baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨structuredFuel, hAccepted, hForward⟩ :=
    optimizedSolcYulToRawBytecodeWithCodeSuffix (sourceFuel := sourceFuel)
      (baseSource := baseSource) suffix hObject
  have hInitialPoint :=
    verifiedArtifact_initialArtifactFramePointWithCodeSuffix suffix hObject
      hInitial
  have hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (EvmYul.UInt256.ofNat 0)) :=
    verifiedArtifact_ordinaryBoundaryInvariantWithCodeSuffix suffix hObject
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.UInt256.ofNat 0))
  have hStepInvariant : Assembly.GasfulBridge.ArtifactFrameStepInvariant
      artifact.codeArtifact.compact
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.UInt256.ofNat 0)) := by
    intro current next stepFuel hPoint hPrefix hStep hContinues
    exact (verifiedArtifact_frameStepInvariant_of_ordinaryBoundaryWithCodeSuffix
      (validJumps := EvmYul.EVM.D_J
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.UInt256.ofNat 0)) suffix hObject hOrdinary)
      hPoint hPrefix hStep hContinues
  have hFrame := Assembly.GasfulBridge.artifactFrameInvariant_of_step
    hInitialPoint hStepInvariant
  have hLayout :=
    verifiedArtifact_frameLayoutInvariant_of_artifactFrameInvariantWithCodeSuffix
      suffix hObject hFrame
  have hCode :=
    verifiedArtifact_frameCodeInvariant_of_layoutWithCodeSuffix suffix hObject
      hLayout
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
