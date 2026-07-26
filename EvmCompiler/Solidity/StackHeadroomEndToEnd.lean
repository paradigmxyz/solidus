import EvmCompiler.Solidity.VerifiedStackObjectArtifact
import EvmCompiler.Assembly.RawStackHeadroomSound

/-!
# Verified-artifact stack-headroom endpoint

Standalone stack-headroom certification for compiled verified stack object
artifacts: `stackHeadroomCert?` produces (fail-closed) a validated per-pc
abstract-stack-set certificate for the artifact's compact program, and the
endpoint theorems below turn a successful certificate into

* `EvmYul.EVM.X` never returning `StackOverflow` on the artifact's byte image
  entered with an empty stack (both the exact runtime image and the
  creation-frame image with appended constructor-argument suffix), and
* an escape-free strengthening of any `RunRefinesOpen` witness
  (`RunRefinesOpenNoStackOverflow`).

The certificate producer is deliberately not a blocking compile gate: the
stage-2 checker tracks per-pc SETS of constant-folded abstract stacks, so
shared procedure bodies entered at several stack depths (the emitted
return-dispatch call protocol) are certified per call-site inflow; genuinely
recursive programs, whose operand stacks really are input-unbounded, fail
closed and simply do not receive the strengthened theorems.
-/

namespace EvmCompiler
namespace Solidity
namespace Frontend

open EvmCompiler.Assembly

/-- Fail-closed stack-headroom certificate for a compiled artifact. -/
def VerifiedStackObjectArtifact.stackHeadroomCert?
    (artifact : VerifiedStackObjectArtifact) :
    Option StackHeadroom.Cert :=
  StackHeadroom.mkRawCert?
    (artifact.codeChoice.compact artifact.codeArtifact)

/-- On a certified artifact image entered at pc `0` with an empty stack, the
gasful frame interpreter never reports `StackOverflow`, for any jump-table
and any fuel. -/
theorem VerifiedStackObjectArtifact.x_ne_stackOverflow
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {validJumps : Array Assembly.Word}
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
      EvmYul.EVM.X fuel validJumps gasfulInitial ≠
        .error EvmYul.EVM.ExecutionException.StackOverflow := by
  have hDecode :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect
      hObject
  obtain ⟨hProgram, _hLayout, _hWindow, hBytes, hSentinelFits⟩ :=
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
    StackHeadroom.x_ne_stackOverflow_of_rawCert hProgram hDecode hRaw
      hSentinel hCode hPc hStack

/-- Suffix-tolerant variant for creation frames: the concrete entry point is
`X fuel validJumps` over `image.bytes ++ suffix` (ABI-encoded constructor
arguments appended after the checked image). -/
theorem VerifiedStackObjectArtifact.x_ne_stackOverflow_withCodeSuffix
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {validJumps : Array Assembly.Word}
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
      EvmYul.EVM.X fuel validJumps gasfulInitial ≠
        .error EvmYul.EVM.ExecutionException.StackOverflow := by
  have hDecode :=
    Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
      hObject suffix
  obtain ⟨hProgram, _hLayout, _hWindow, hBytes, hSentinelFits⟩ :=
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
    StackHeadroom.x_ne_stackOverflow_of_rawCert hProgram hDecode hRaw
      hSentinel hCode hPc hStack

/-- Escape-free refinement for certified artifacts: any `RunRefinesOpen`
witness over the artifact's gasful run strengthens to the variant without
the `stackOverflow` constructor. Single-branch pruning: unlike the combined
crown (`Yul.EndToEnd.optimizedSolcYulToGasfulRawBytecodeTotal`, concluding
`RunRefinesOpenTotal`), this applies at any fuel and against any jump table,
without the jumpdest-scan or gas-derived-fuel hypotheses of the other
branches. -/
theorem VerifiedStackObjectArtifact.runRefinesOpen_noStackOverflow
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {validJumps : Array Assembly.Word}
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
        (EvmYul.EVM.X fuel validJumps gasfulInitial) openRun transcript) :
    StackHeadroom.RunRefinesOpenNoStackOverflow
      (EvmYul.EVM.X fuel validJumps gasfulInitial) openRun transcript :=
  StackHeadroom.runRefinesOpenNoStackOverflow_of_ne hRefines
    (VerifiedStackObjectArtifact.x_ne_stackOverflow hObject hCert hCode hPc
      hStack fuel)

/-- Suffix-tolerant escape-free refinement for creation frames. -/
theorem VerifiedStackObjectArtifact.runRefinesOpen_noStackOverflow_withCodeSuffix
    {object : Object}
    {linkerSymbols : List (Name × Word)}
    {artifact : VerifiedStackObjectArtifact}
    {cert : StackHeadroom.Cert}
    {gasfulInitial : Assembly.EVMState}
    {validJumps : Array Assembly.Word}
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
        (EvmYul.EVM.X fuel validJumps gasfulInitial) openRun transcript) :
    StackHeadroom.RunRefinesOpenNoStackOverflow
      (EvmYul.EVM.X fuel validJumps gasfulInitial) openRun transcript :=
  StackHeadroom.runRefinesOpenNoStackOverflow_of_ne hRefines
    (VerifiedStackObjectArtifact.x_ne_stackOverflow_withCodeSuffix suffix
      hObject hCert hCode hPc hStack fuel)

end Frontend
end Solidity
end EvmCompiler
