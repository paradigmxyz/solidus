import EvmCompiler.Solidus.Defs
import EvmCompiler.Solidity.SolidusInstall
import EvmCompiler.Solidity.LibraryPatch
import EvmCompiler.Yul.GasfulCrown

/-!
# Unlinked-library public surface — implementation bridge

This module connects the frozen fail-closed unlinked entry
`Solidus.compileUnlinked?` (`EvmCompiler/Solidus/Defs.lean`) to the verified
unlinked-library pipeline:

* `compileUnlinked?_parts` decomposes a successful unlinked compilation into
  its decoded program, the JSON-provided partial library assignment, the
  compiled artifact (through the fail-closed `unlinkedLibraryGate?`), the
  checked stack-headroom certificate, and the byte-image / link-reference
  equalities.
* `compileUnlinked?_unlinkedImageTotal` lifts the object-level gasful crown
  (`Yul.EndToEnd.optimizedSolcYulToGasfulRawBytecodeTotal`) to the unlinked
  image: the delivered bytes carry the full escape-free `RunRefinesOpenTotal`
  tower against their own resolved source program (the rewrite-to-immutable
  form the pipeline actually compiled — library slots read as the zero
  address until patched).
* `compileUnlinked?_patchImmutablesAndLibraries_resolvesOriginal` is the
  link-time bridge: for any address assignment whose library addresses are
  address-sized and for which the deploy-value compile succeeds, patching the
  exported windows reproduces, byte for byte, the verified value-compile of
  the **original** (un-rewritten) source resolved with those addresses.

The final public theorems are stated in `EvmCompiler/Correctness.lean`; this
file is implementation detail.
-/

namespace EvmCompiler
namespace Solidus

open EvmCompiler.Solidity

/-- Decompose a successful `compileUnlinked?` run. -/
theorem compileUnlinked?_parts
    {rawJson : String} {selection : Solidity.RawAst.Selection}
    {bytes : List UInt8}
    {refs : List (Frontend.Name × List Frontend.ImmutableReference)}
    (hCompile : compileUnlinked? rawJson selection = some (bytes, refs)) :
    ∃ (artifact : Frontend.VerifiedStackObjectArtifact)
        (program : Frontend.Program)
        (provided : List (Frontend.Name × Frontend.Word))
        (cert : Assembly.StackHeadroom.Cert),
      Solidity.RawAst.decodeAndElaborateSolcIr? rawJson selection =
          some program ∧
        Solidity.RawAst.decodeLinkerSymbols? rawJson selection = some provided ∧
        program.object.compileVerifiedStackObjectArtifactUnlinked? provided =
          some artifact ∧
        artifact.stackHeadroomCert? = some cert ∧
        bytes = artifact.image.bytes ∧
        refs =
          artifact.image.linkReferences
            (program.object.missingLinkerSymbolNames provided) := by
  simp only [compileUnlinked?, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at hCompile
  obtain ⟨⟨artifact, refs'⟩, hRefs, cert, hCert, hBytes, hRefsEq⟩ := hCompile
  obtain ⟨program, provided, hDecode, hLinker, hInner, hRefs''⟩ :=
    Solidity.RawAst.compileArtifactUnlinkedFromRawSolcIrRefs?_parts hRefs
  refine ⟨artifact, program, provided, cert, hDecode, hLinker, hInner,
    hCert, hBytes.symm, ?_⟩
  rw [← hRefsEq]; exact hRefs''

/-- **Link-time patching is the value compile of the original source.**  For
a successful unlinked compilation producing `bytes` and, for a deploy address
assignment `values` whose library addresses are address-sized, a successful
value compile `withValues`, patching the exported immutable/library windows of
`bytes` with `values` reproduces `withValues.bytes` followed by the unchanged
child payload; and that value compile is exactly the **original**
(un-rewritten) object resolved with those addresses supplied alongside the
JSON-provided ones — its ordered Yul program is the value compile's own
ordered program, so every downstream semantic theorem about the supported
pipeline applies to the patched (linked) image as a compile of the original
source. -/
theorem compileUnlinked?_patchImmutablesAndLibraries_resolvesOriginal
    {rawJson : String} {selection : Solidity.RawAst.Selection}
    {bytes : List UInt8}
    {refs : List (Frontend.Name × List Frontend.ImmutableReference)}
    (hCompile : compileUnlinked? rawJson selection = some (bytes, refs))
    (values : List (Frontend.Name × Frontend.Word)) :
    ∃ (object : Frontend.Object)
        (provided : List (Frontend.Name × Frontend.Word))
        (artifact : Frontend.VerifiedStackObjectArtifact),
      object.compileVerifiedStackObjectArtifactUnlinked? provided =
          some artifact ∧
        bytes = artifact.image.bytes ∧
        ∀ withValues : Frontend.Object.VerifiedStackCodeArtifact,
          Frontend.Object.compileVerifiedStackCodeArtifactWithImmutableValues?
              (object.substituteUnlinkedLibraries
                (object.missingLinkerSymbolNames provided))
              artifact.computed.context values = some withValues →
          (∀ name,
            (object.missingLinkerSymbolNames provided).contains name = true →
            ∀ entry, values.find? (fun v => v.fst == name) = some entry →
              entry.snd.toNat < 2 ^ 160) →
          Frontend.Bytecode.patchImmutablesAndLibraries bytes
              (artifact.ownImmutableReferences
                (object.substituteUnlinkedLibraries
                  (object.missingLinkerSymbolNames provided)))
              (object.missingLinkerSymbolNames provided) values =
            withValues.bytes ++ artifact.computed.payload ∧
          ∃ resolvedOriginal : Frontend.Object,
            object.resolveObjectBuiltinsIn?
                { artifact.computed.context with
                    linkerSymbols :=
                      artifact.computed.context.linkerSymbols ++
                        values.filter (fun entry =>
                          (object.missingLinkerSymbolNames provided).contains
                            entry.fst)
                    immutableValues :=
                      values.filter (fun entry =>
                        !((object.missingLinkerSymbolNames provided).contains
                          entry.fst)) } =
              some resolvedOriginal ∧
            withValues.resolved =
              { resolvedOriginal with
                  objects :=
                    Frontend.Object.List.substituteUnlinkedLibraries
                      (object.missingLinkerSymbolNames provided)
                      object.objects } ∧
            resolvedOriginal.toSolcYulOrderedProgram? = some withValues.ordered := by
  obtain ⟨artifact, program, provided, _cert, _hDecode, _hLinker, hObject,
      _hCert, hBytes, _hRefs⟩ := compileUnlinked?_parts hCompile
  refine ⟨program.object, provided, artifact, hObject, hBytes, ?_⟩
  intro withValues hValues hAddresses
  subst hBytes
  exact
    ⟨Frontend.Object.patchImmutablesAndLibraries_image_ofCompileUnlinked
      hObject hValues hAddresses,
     Frontend.Object.compileVerifiedStackObjectArtifactUnlinked?_withValues_resolvesOriginal
      hObject hValues⟩

end Solidus
end EvmCompiler
