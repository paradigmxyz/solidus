import EvmCompiler.Correctness
import EvmCompiler.Solidity.SolidusUnlinked

/-!
# Solidus compiler correctness — unlinked-library public surface (DEFERRED)

This module is **NOT part of the v1 freeze**. It carries the two public
correctness theorems for the verified unlinked-library pipeline
(`compile_correct_unlinked` / `compile_correct_unlinked_patch`) together with
their entry `Solidus.compileUnlinked?` (defined, with its decomposition proofs,
in `EvmCompiler/Solidity/SolidusUnlinked.lean`).

## Why these two theorems were deferred from the v1 freeze

Their *statements* irreducibly reference compiler-pipeline vocabulary — the
artifact pipeline itself (`Solidity.Frontend.VerifiedStackObjectArtifact`, its
`codeArtifact`/`ordered`/`compiled` projections), object-level structure
(`toSolcYulOrderedProgram?`, `compileVerifiedStackObjectArtifactUnlinked?`,
`resolveObjectBuiltinsIn?`, `substituteUnlinkedLibraries`,
`patchImmutablesAndLibraries`), and the value-compile machinery
(`compileVerifiedStackCodeArtifactWithImmutableValues?`). A prior closure
analysis established that these symbols cannot be restated in frozen spec
vocabulary without *freezing the very compiler passes contestants must be free
to optimize*. Freezing the four-theorem cone would therefore defeat the point
of the contest. So the v1 freeze covers only the two **linked-image** theorems
in `EvmCompiler/Correctness.lean` (`compile_correct` /
`compile_correct_creation`), whose cone is closed.

These deferred theorems return in a later season once (i) the Yul-AST / Object
relocation and (ii) the object-level value-compile crown exist, at which point
their statements can be phrased over frozen vocabulary and admitted to the
freeze.

## Scoring soundness does not depend on these theorems

The scoring runner calls only the **linked** `Solidus.compile?`:
resolved-library contracts take the linked path covered by `compile_correct`;
missing-library contracts fail compilation (`compile?` returns `none`) and are
never scored on bytes. So the unlinked surface being outside the frozen v1 does
not open any scoring attack — it is an additional (fully proved) guarantee that
simply is not yet hash-frozen.

The two theorems remain fully proved here and are checked in CI (imported by
`EvmCompiler.Verification`, axiom-audited alongside the linked pair).
-/

namespace EvmCompiler
namespace Solidus

/-- Public correctness theorem for the **delivered unlinked image**: the
charged run at the gas-derived fuel refines the open run with no escape
constructor. Because the missing libraries were rewritten to `loadimmutable`,
the source side is the artifact's *own resolved program* (the
rewrite-to-immutable form in which every unresolved library slot reads as the
zero address until patched). This is the exact analog of `compile_correct` for
the bytes the unlinked pipeline emits. DEFERRED from the v1 freeze — see the
module header. -/
theorem compile_correct_unlinked
    {rawJson : String} {selection : Solidity.RawAst.Selection}
    {bytes : List UInt8}
    {refs : List (Solidity.Frontend.Name ×
      List Solidity.Frontend.ImmutableReference)}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hCompile : compileUnlinked? rawJson selection = some (bytes, refs))
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        (installedTarget bytes baseSource)) :
    ∃ (artifact : Solidity.Frontend.VerifiedStackObjectArtifact)
        (structuredFuel : Nat)
        (transcript : Simulation.Interaction.Transcript),
      bytes = artifact.image.bytes ∧
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
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
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) ∧
        Assembly.GasfulBridge.RunRefinesOpenTotal
          (EvmYul.EVM.X
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            (EvmYul.EVM.D_J
              (Assembly.Bytecode.ofList artifact.image.bytes)
              (EvmYul.UInt256.ofNat 0))
            gasfulInitial)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (max
              (2 *
                ((Structured.InteractionStaticCost.blockBudget
                    artifact.codeArtifact.compiled.expressions.toStructured
                    structuredFuel
                    artifact.codeArtifact.compiled.expressions.toStructured.body +
                      1) *
                  TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                    artifact.codeArtifact.compiled.cfg))
              (gasfulInitial.gasAvailable.toNat + 6))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 })
          transcript := by
  obtain ⟨artifact, program, provided, cert, _hDecode, _hLinker, hInner,
      hCert, hBytes, _hRefs⟩ := compileUnlinked?_parts hCompile
  obtain ⟨hInnerWith, _hGate⟩ :=
    Solidity.Frontend.Object.compileVerifiedStackObjectArtifactUnlinked?_parts
      hInner
  subst hBytes
  rw [installedTarget_eq artifact baseSource] at hInitial
  obtain ⟨structuredFuel, transcript, hAccepted, hForward, hTotal⟩ :=
    Yul.EndToEnd.optimizedSolcYulToGasfulRawBytecodeTotal
      (sourceFuel := sourceFuel) (baseSource := baseSource)
      hInnerWith hCert hInitial
  exact ⟨artifact, structuredFuel, transcript, rfl, hAccepted, hForward, hTotal⟩

/-- Link-time bridge for the unlinked pipeline: patching real library
addresses into the unlinked image reproduces, byte for byte, the verified
value-compile of the **original** (un-rewritten) source resolved with those
addresses supplied as linker symbols — its ordered Yul program being the value
compile's own ordered program. So "patching real library addresses into the
unlinked image" and "compiling the original source with those addresses"
produce the same bytes; the guarantee `compile_correct` makes about the value
compile therefore transfers to the patched image. The full statement is
`Solidus.compileUnlinked?_patchImmutablesAndLibraries_resolvesOriginal`.
DEFERRED from the v1 freeze — see the module header. -/
alias compile_correct_unlinked_patch :=
  compileUnlinked?_patchImmutablesAndLibraries_resolvesOriginal

end Solidus
end EvmCompiler
