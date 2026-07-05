import EvmCompiler.Solidity.VerifiedStackObjectArtifact
import EvmCompiler.Assembly.JumpTargetSound

/-!
# Verified-artifact bad-jump exclusion endpoint

Compiled verified stack object artifacts can never make the gasful EVM
interpreter report `BadJumpDestination` when the jump table is the
interpreter's own jumpdest scan of the artifact's byte image -- exactly the
table `EvmYul.EVM.X` is entered with at every code-execution boundary
(`Ξ`/`Θ` install `D_J I.code 0`).

Unlike the stack-headroom endpoint this needs no certificate: the compact
compiler emits fixed-label branches only, every label destination lowers to
a located `JUMPDEST`, and the jumpdest-scan membership theorem
(`Compact.D_J_contains_of_decodingCorrect`) shows EVMYulLean's scanner lists
each of them over the artifact image -- including the creation-frame image
with ABI-encoded constructor arguments appended, because decode facts at
program PCs are suffix-tolerant.

Endpoints:

* `VerifiedStackObjectArtifact.x_ne_badJumpDestination`
  (+ `_withCodeSuffix`): the gasful frame run never returns
  `BadJumpDestination` over the scanned image.
* `VerifiedStackObjectArtifact.runRefinesOpen_noBadJump`
  (+ `_withCodeSuffix`): any `RunRefinesOpen` witness strengthens to the
  variant without the `badJumpDestination` escape constructor.
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend

open EvmCompiler.Assembly

/-- On a compiled artifact image entered anywhere at a generated control
point -- in particular at pc `0` -- the gasful frame interpreter never
reports `BadJumpDestination` when validated against its own jumpdest scan of
that image, for any fuel. -/
theorem VerifiedStackObjectArtifact.x_ne_badJumpDestination
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList artifact.image.bytes)
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0) :
    ∀ fuel,
      EvmYul.EVM.X fuel
          (EvmYul.EVM.D_J
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (EvmYul.UInt256.ofNat 0))
          gasfulInitial ≠
        .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCodeIn, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStackLower, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Object.compileVerifiedStackCodeArtifactIn?_parts hCodeIn
  have hDecode :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject
  obtain ⟨plan, hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
      hObject
  have hSentinel : Assembly.Compact.decodeAt
      (Assembly.Bytecode.ofList artifact.image.bytes)
      (Assembly.Compact.Program.codeByteLength
        artifact.codeArtifact.compact.program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Object.verifiedCodeSentinel, List.append_assoc] using
      (Assembly.GasfulBridge.compact_compile_sentinel_decodeAt
        hCompact plan.payload)
  have hInitialPoint :=
    Assembly.GasfulBridge.artifactFramePoint_initial hCompact hCode hPc
  have hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList artifact.image.bytes)
          (EvmYul.UInt256.ofNat 0)) :=
    Assembly.GasfulBridge.artifactOrdinaryBoundaryStepInvariant_of_compile
      hCompact hDecode
  have hStepInv :
      Assembly.GasfulBridge.ArtifactFrameStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList artifact.image.bytes)
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList artifact.image.bytes)
          (EvmYul.UInt256.ofNat 0)) := by
    intro current next stepFuel hPoint hPrefix hStep hContinues
    exact (Assembly.GasfulBridge.artifactFrameStepInvariant_of_ordinaryBoundary
      hCompact hDecode hSentinel hOrdinary) hPoint hPrefix hStep hContinues
  have hFrame :=
    Assembly.GasfulBridge.artifactFrameInvariant_of_step hInitialPoint
      hStepInv
  exact Assembly.GasfulBridge.x_ne_badJumpDestination_of_frame
    hCompact hDecode hSentinel hFrame
    (Assembly.GasfulBridge.labelTargetsListed_D_J hCompact hDecode)

/-- Suffix-tolerant variant for creation frames: the concrete entry point is
`X fuel (D_J (image.bytes ++ suffix) 0)` over `image.bytes ++ suffix`
(ABI-encoded constructor arguments appended after the checked image). -/
theorem VerifiedStackObjectArtifact.x_ne_badJumpDestination_withCodeSuffix
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0) :
    ∀ fuel,
      EvmYul.EVM.X fuel
          (EvmYul.EVM.D_J
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
            (EvmYul.UInt256.ofNat 0))
          gasfulInitial ≠
        .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
  obtain ⟨_children, _plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCodeIn, _hArtifactChildren, _hContext, _hChildImages, _hPayload,
      _hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
      hObject
  obtain ⟨_hResolved, _hOrdered, _hLower, _hStackLower, _pinnedPushPcs,
      _hPins, hCompact, _hBytes, _hMarker⟩ :=
    Object.compileVerifiedStackCodeArtifactIn?_parts hCodeIn
  have hDecode :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
      hObject suffix
  obtain ⟨plan, hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
      hObject
  have hSentinel : Assembly.Compact.decodeAt
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (Assembly.Compact.Program.codeByteLength
        artifact.codeArtifact.compact.program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Object.verifiedCodeSentinel, List.append_assoc] using
      (Assembly.GasfulBridge.compact_compile_sentinel_decodeAt
        hCompact (plan.payload ++ suffix))
  have hInitialPoint :=
    Assembly.GasfulBridge.artifactFramePoint_initial hCompact hCode hPc
  have hOrdinary :
      Assembly.GasfulBridge.ArtifactOrdinaryBoundaryStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (EvmYul.UInt256.ofNat 0)) :=
    Assembly.GasfulBridge.artifactOrdinaryBoundaryStepInvariant_of_compile
      hCompact hDecode
  have hStepInv :
      Assembly.GasfulBridge.ArtifactFrameStepInvariant
        artifact.codeArtifact.compact
        (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (EvmYul.UInt256.ofNat 0)) := by
    intro current next stepFuel hPoint hPrefix hStep hContinues
    exact (Assembly.GasfulBridge.artifactFrameStepInvariant_of_ordinaryBoundary
      hCompact hDecode hSentinel hOrdinary) hPoint hPrefix hStep hContinues
  have hFrame :=
    Assembly.GasfulBridge.artifactFrameInvariant_of_step hInitialPoint
      hStepInv
  exact Assembly.GasfulBridge.x_ne_badJumpDestination_of_frame
    hCompact hDecode hSentinel hFrame
    (Assembly.GasfulBridge.labelTargetsListed_D_J hCompact hDecode)

/-- Escape-free refinement for compiled artifacts: any `RunRefinesOpen`
witness over the artifact's gasful run against its own jumpdest scan
strengthens to the variant without the `badJumpDestination` constructor. -/
theorem VerifiedStackObjectArtifact.runRefinesOpen_noBadJump
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {gasfulInitial : Assembly.EVMState}
    {fuel : Nat}
    {openRun :
      Simulation.Interaction Assembly.EVMException
        Assembly.StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList artifact.image.bytes)
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hRefines :
      Assembly.GasfulBridge.RunRefinesOpen
        (EvmYul.EVM.X fuel
          (EvmYul.EVM.D_J
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (EvmYul.UInt256.ofNat 0))
          gasfulInitial)
        openRun transcript) :
    Assembly.GasfulBridge.RunRefinesOpenNoBadJump
      (EvmYul.EVM.X fuel
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList artifact.image.bytes)
          (EvmYul.UInt256.ofNat 0))
        gasfulInitial)
      openRun transcript :=
  Assembly.GasfulBridge.runRefinesOpenNoBadJump_of_ne hRefines
    (VerifiedStackObjectArtifact.x_ne_badJumpDestination hObject hCode hPc
      fuel)

/-- Suffix-tolerant escape-free refinement for creation frames. -/
theorem VerifiedStackObjectArtifact.runRefinesOpen_noBadJump_withCodeSuffix
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {gasfulInitial : Assembly.EVMState}
    {fuel : Nat}
    {openRun :
      Simulation.Interaction Assembly.EVMException
        Assembly.StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hRefines :
      Assembly.GasfulBridge.RunRefinesOpen
        (EvmYul.EVM.X fuel
          (EvmYul.EVM.D_J
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
            (EvmYul.UInt256.ofNat 0))
          gasfulInitial)
        openRun transcript) :
    Assembly.GasfulBridge.RunRefinesOpenNoBadJump
      (EvmYul.EVM.X fuel
        (EvmYul.EVM.D_J
          (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
          (EvmYul.UInt256.ofNat 0))
        gasfulInitial)
      openRun transcript :=
  Assembly.GasfulBridge.runRefinesOpenNoBadJump_of_ne hRefines
    (VerifiedStackObjectArtifact.x_ne_badJumpDestination_withCodeSuffix
      suffix hObject hCode hPc fuel)

end Frontend
end Solidity
end EvmCompiler
