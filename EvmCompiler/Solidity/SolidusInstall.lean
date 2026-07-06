import EvmCompiler.Solidus.Defs
import EvmCompiler.Yul.EndToEnd

/-!
# Solidus installation lemmas

Bridges between the frozen Solidus spec vocabulary
(`EvmCompiler/Solidus/Defs.lean`) and the compiler-side canonical initial
states used by the end-to-end theorems (`EvmCompiler/Yul/EndToEnd.lean`):

* `compile?_parts` decomposes a successful `Solidus.compile?` run into its
  pipeline artifact, its checked stack-headroom certificate, and the byte
  image equality;
* `installedWorld_eq` shows the AST-free installed open world of the spec
  coincides with the code-erased view of the AST-carrying source install;
* `installedTarget_eq` / `installedTarget_eqWithCodeSuffix` identify the
  spec's canonical target start state with the compiler's canonical
  installed expressions-layer EVM state (pc pinned to `0`);
* `installedSource_witness` / `installedSource_witnessWithCodeSuffix`
  exhibit the compiler's canonical installed source states as witnesses of
  the spec's existential `InstalledSource` predicate.
-/

namespace EvmCompiler
namespace Solidus

/-- A successful `compile?` run decomposes into a pipeline artifact, a
checked stack-headroom certificate, and the artifact's byte image. -/
theorem compile?_parts {rawJson : String}
    {selection : Solidity.RawAst.Selection} {bytes : List UInt8}
    (hCompile : compile? rawJson selection = some bytes) :
    ∃ artifact cert,
      Solidity.RawAst.compileArtifactFromRawSolcIr? rawJson selection =
          some artifact ∧
        artifact.stackHeadroomCert? = some cert ∧
        bytes = artifact.image.bytes := by
  simp only [compile?, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hCompile
  obtain ⟨artifact, hArtifact, cert, hCert, hBytes⟩ := hCompile
  exact ⟨artifact, cert, hArtifact, hCert, hBytes.symm⟩

/-- The AST-free installed open world of the spec equals the code-erased
open world of the AST-carrying source install: `OpenAccount.ofYul` and
`ExecutionEnvRel.toEVM` never read the installed AST slot. -/
theorem installedWorld_eq (contract : Yul.AstContract) (image : ByteArray)
    (base : EvmYul.SharedState .Yul) :
    Simulation.OpenWorld.ofYulShared
        (Yul.Source.Installation.installContractWithCodeImage contract image
          base) =
      installedWorld image base := by
  simp only [Simulation.OpenWorld.ofYulShared, Simulation.OpenWorld.ofYulState,
    Yul.Source.Installation.installContractWithCodeImage, installedWorld]
  rw [Simulation.OpenWorld.mapVal_insert]
  rfl

/-- The spec's canonical target start state is exactly the compiler's
canonical installed expressions-layer EVM state with pc pinned to `0`. -/
theorem installedTarget_eq
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact)
    (base : EvmYul.SharedState .Yul) :
    installedTarget artifact.image.bytes base =
      { (Yul.EndToEnd.initialExpressionsState artifact base).evm with
        pc := EvmYul.UInt256.ofNat 0 } := by
  simp only [installedTarget, Yul.EndToEnd.initialExpressionsState,
    Yul.EndToEnd.initialFunctionsState,
    Functions.StackRelation.initialTarget, Structured.RunState.initial,
    Yul.FunctionsInteractionRelation.ScopedStateRel.initialTarget,
    Yul.FunctionsInteractionRelation.ScopedStateRel.installedSourceShared,
    Yul.FunctionsInteractionRelation.SharedRel.toEVM]
  rw [installedWorld_eq]
  rfl

/-- Suffix-tolerant variant of `installedTarget_eq` for creation frames
whose code image carries an appended caller-owned byte suffix. -/
theorem installedTarget_eqWithCodeSuffix
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact)
    (suffix : List UInt8)
    (base : EvmYul.SharedState .Yul) :
    installedTarget (artifact.image.bytes ++ suffix) base =
      { (Yul.EndToEnd.initialExpressionsStateWithCodeSuffix artifact suffix
          base).evm with
        pc := EvmYul.UInt256.ofNat 0 } := by
  simp only [installedTarget,
    Yul.EndToEnd.initialExpressionsStateWithCodeSuffix,
    Yul.EndToEnd.initialFunctionsStateWithCodeSuffix,
    Functions.StackRelation.initialTarget, Structured.RunState.initial,
    Yul.FunctionsInteractionRelation.ScopedStateRel.initialTarget,
    Yul.FunctionsInteractionRelation.ScopedStateRel.installedSourceShared,
    Yul.FunctionsInteractionRelation.SharedRel.toEVM]
  rw [installedWorld_eq]
  rfl

/-- The compiler's canonical installed source state witnesses the spec's
existential `InstalledSource` predicate. -/
theorem installedSource_witness
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact)
    (base : EvmYul.SharedState .Yul) :
    InstalledSource artifact.image.bytes base
      (Yul.EndToEnd.installedSourceState artifact base) :=
  ⟨artifact.codeArtifact.ordered.program.contract, rfl⟩

/-- Suffix-tolerant variant of `installedSource_witness`. -/
theorem installedSource_witnessWithCodeSuffix
    (artifact : Solidity.Frontend.VerifiedStackObjectArtifact)
    (suffix : List UInt8)
    (base : EvmYul.SharedState .Yul) :
    InstalledSource (artifact.image.bytes ++ suffix) base
      (Yul.EndToEnd.installedSourceStateWithCodeSuffix artifact suffix base) :=
  ⟨artifact.codeArtifact.ordered.program.contract, rfl⟩

end Solidus
end EvmCompiler
