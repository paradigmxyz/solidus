import EvmCompiler.Solidity.StackHeadroomEndToEnd
import EvmCompiler.Assembly.RawStackHeadroomSound

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
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList artifact.image.bytes)
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : gasfulInitial.stack = []) :
    ∀ fuel,
      EvmYul.EVM.X fuel
          (EvmYul.EVM.D_J
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (EvmYul.UInt256.ofNat 0))
          gasfulInitial ≠
        .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
  have hDecode :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject
  obtain ⟨hProgram, hLayout, hWindow, hBytes, hSentinelFits⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_selectedCompactProperties
      hObject
  obtain ⟨plan, hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
      hObject
  have hSentinel : Assembly.Compact.decodeAt
      (Assembly.Bytecode.ofList artifact.image.bytes)
      (Assembly.Compact.Program.codeByteLength
        (artifact.codeChoice.compact
          artifact.codeArtifact).program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Object.verifiedCodeSentinel, List.append_assoc] using
      (StackHeadroom.raw_compact_sentinel_decodeAt hBytes
        hSentinelFits plan.payload)
  have hRaw :=
    StackHeadroom.mkRawCert?_rawCheck
      (by
        simpa [VerifiedStackObjectArtifact.stackHeadroomCert?] using
          hCert)
  exact
    StackHeadroom.x_ne_badJumpDestination_of_rawCert hProgram hDecode
      hRaw hSentinel
      (StackHeadroom.rawJumpdestsListed_D_J hLayout hWindow hDecode)
      hCode hPc hStack

/-- Suffix-tolerant variant for creation frames: the concrete entry point is
`X fuel (D_J (image.bytes ++ suffix) 0)` over `image.bytes ++ suffix`
(ABI-encoded constructor arguments appended after the checked image). -/
theorem VerifiedStackObjectArtifact.x_ne_badJumpDestination_withCodeSuffix
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : gasfulInitial.stack = []) :
    ∀ fuel,
      EvmYul.EVM.X fuel
          (EvmYul.EVM.D_J
            (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
            (EvmYul.UInt256.ofNat 0))
          gasfulInitial ≠
        .error EvmYul.EVM.ExecutionException.BadJumpDestination := by
  have hDecode :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
      hObject suffix
  obtain ⟨hProgram, hLayout, hWindow, hBytes, hSentinelFits⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_selectedCompactProperties
      hObject
  obtain ⟨plan, hImage⟩ :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_sentinelImage
      hObject
  have hSentinel : Assembly.Compact.decodeAt
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
      (Assembly.Compact.Program.codeByteLength
        (artifact.codeChoice.compact
          artifact.codeArtifact).program.code)
      (.prim .invalid) := by
    rw [hImage]
    simpa [Object.verifiedCodeSentinel, List.append_assoc] using
      (StackHeadroom.raw_compact_sentinel_decodeAt hBytes
        hSentinelFits (plan.payload ++ suffix))
  have hRaw :=
    StackHeadroom.mkRawCert?_rawCheck
      (by
        simpa [VerifiedStackObjectArtifact.stackHeadroomCert?] using
          hCert)
  exact
    StackHeadroom.x_ne_badJumpDestination_of_rawCert hProgram hDecode
      hRaw hSentinel
      (StackHeadroom.rawJumpdestsListed_D_J hLayout hWindow hDecode)
      hCode hPc hStack

/-- Escape-free refinement for compiled artifacts: any `RunRefinesOpen`
witness over the artifact's gasful run against its own jumpdest scan
strengthens to the variant without the `badJumpDestination` constructor.
Single-branch pruning: unlike the combined crown
(`Yul.EndToEnd.optimizedSolcYulToGasfulRawBytecodeTotal`, concluding
`RunRefinesOpenTotal`), this applies at any fuel and needs no
stack-headroom certificate. -/
theorem VerifiedStackObjectArtifact.runRefinesOpen_noBadJump
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {fuel : Nat}
    {openRun :
      Simulation.Interaction Assembly.EVMException
        Assembly.StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hObject :
      object.compileVerifiedStackObjectArtifactWithLinkerSymbols?
          linkerSymbols = some artifact)
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList artifact.image.bytes)
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : gasfulInitial.stack = [])
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
    (VerifiedStackObjectArtifact.x_ne_badJumpDestination hObject hCert
      hCode hPc hStack fuel)

/-- Suffix-tolerant escape-free refinement for creation frames. -/
theorem VerifiedStackObjectArtifact.runRefinesOpen_noBadJump_withCodeSuffix
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
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
    (hCert : artifact.stackHeadroomCert? = some cert)
    (hCode :
      gasfulInitial.executionEnv.code =
        Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix))
    (hPc : gasfulInitial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : gasfulInitial.stack = [])
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
      suffix hObject hCert hCode hPc hStack fuel)

end Frontend
end Solidity
end EvmCompiler
