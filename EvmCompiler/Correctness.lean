import EvmCompiler.Solidus.Defs
import EvmCompiler.Solidity.SolidusInstall
import EvmCompiler.Solidity.RawAstTotal
import EvmCompiler.Solidity.SolidusUnlinked
import EvmCompiler.Compiler.SolidusObservable

/-!
# Solidus compiler correctness — the public specification

This file is the public entry point to the proof tower. A reader who trusts

* the pinned `EvmYul` EVM interpreter (`EvmYul.EVM.X` and its jumpdest scan
  `EvmYul.EVM.D_J`),
* the Yul source semantics (`Solidity.RawAst.Raw.SourcePreservation.rawObjectRun`
  over the object decoded from the input JSON),
* the semantic framework (`Simulation.Interaction`, `Simulation.OpenWorld`,
  the open assembly interpreter `Assembly.Compact.InteractionSemantics`, and
  the outcome relations `Assembly.GasfulBridge.RunRefinesOpenTotal` /
  `Solidus.ObservableDoneRel`), and
* the vocabulary in `EvmCompiler/Solidus/Defs.lean`

needs to read nothing else: every other file in the repository is
implementation detail, free to change, and `compile_correct` below is the
complete claim the compiler makes about its output.

## What `compile_correct` says

If the fail-closed public entry `Solidus.compile?` produces `bytes` from raw
solc Standard JSON input, then for ANY gas-charged EVM start state related
(`OpenStateRel` — everything pinned except available gas) to the canonical
installed state `Solidus.installedTarget bytes baseSource`:

1. the input JSON decodes to a source object, and the *decoded* object's
   independent Yul semantics, run from a source state with `bytes` installed
   as the executing contract (`InstalledSource`), forward-refines the open
   bytecode run — with the frozen observable done relation
   `ObservableDoneRel`: matching halt kinds, equal code-erased world
   (storage, transient storage, balances, nonces, code), equal observable
   machine data, equal output bytes, and forwarded errors (with the
   guarantee that a structural out-of-fuel error cannot be manufactured);
2. the gas-charged interpreter run at any sufficient structural fuel
   (`max openFuel (gas + 6)` for the existentially provided `openFuel`)
   refines that same open run with EVERY escape hatch removed
   (`RunRefinesOpenTotal`): it completes in refinement, halts in an
   exceptional frame the source demanded (provably not out-of-fuel, not
   stack-overflow, not bad-jump-destination), or halts out-of-gas with the
   pinned frame-boundary rollback semantics. Nothing else can happen.

`compile_correct_creation` is the same claim for the creation frame: the
image with a constructor-argument suffix appended, checked against the
interpreter's own jumpdest scan of the full installed image.

## Honest caveats (each also documented at its definition)

* The source semantics represents `stop`/`return`/`selfdestruct` with one
  exception constructor, so a finished source value pins the halt kind only
  up to that set; the output bytes — which are what distinguishes those
  kinds observably — are pinned exactly (`ObservableDoneRel`).
* `InstalledSource` leaves the installed contract-AST slot existential, and
  that slot is semantically inert on the public spine: EVM-level calls
  (including self-calls) are open-world requests (`callEval` performs no callee
  check), internal Yul calls resolve from the decoded object's function scopes,
  and code-introspection builtins read the code-erased projection
  (`codeBytes`). The existential is a modeling artifact of the installation
  shape, not a semantic degree of freedom. Every observable field of the
  initial state is pinned.
* Exception identity is not claimed for forwarded errors (all non-revert
  EVM exceptions are observationally identical exceptional halts; reverts
  are pinned by their own constructor) — see `ExceptionRel`.
* A normal source completion is observable as an on-chain STOP: empty
  output, return buffer cleared by the STOP (the source's stale pre-STOP
  buffer scratch is unobservable and excluded from the comparison).
* The structural fuel of the charged run is existential with the explicit
  lower bound `gasAvailable + 6`; the `RunRefinesOpenTotal` outcome excludes
  out-of-fuel, which is precisely the statement that the fuel did not bind.
* For a source execution that diverges at every fuel (for a given calldata),
  the `ForwardRel` truncation arm makes the source-refinement conjunct vacuous:
  the theorem then constrains only crash-safety of the target, not its
  behavior. Terminating executions — any input on which the source halts at
  some fuel — receive the full guarantee. This is the standard finite-fuel
  partial-correctness boundary.

## Freeze contract (Solidus Arena)

For the optimization challenge, this file, `EvmCompiler/Solidus/Defs.lean`,
the semantic-framework modules named above, the `EvmYul` pin, and
`lean-toolchain` are FROZEN: CI refuses any submission whose copies differ
from the canonical hashes, and the scoring runner independently re-checks
the hashes from configuration outside the submission's reach. The theorems
must elaborate against the submitted compiler with axioms contained in
`{propext, Classical.choice, Quot.sound}` (checked by `#print axioms` in
CI, which also rules out `sorry` and `native_decide`).
-/

namespace EvmCompiler
namespace Solidus

/-- Public correctness theorem for the compiled image. See the module
docstring for the full reading. -/
theorem compile_correct
    {rawJson : String} {selection : Solidity.RawAst.Selection}
    {bytes : List UInt8}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (hCompile : compile? rawJson selection = some bytes)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        (installedTarget bytes baseSource)) :
    ∃ (json : Lean.Json) (selected : Solidity.RawAst.SelectedIr)
        (context : Solidity.Frontend.ObjectBuiltinContext)
        (sourceInit : Yul.InteractionSemantics.State)
        (openFuel : Nat)
        (transcript : Simulation.Interaction.Transcript),
      Lean.Json.parse rawJson = .ok json ∧
        Solidity.RawAst.decodeSelectedIr json selection = .ok selected ∧
          InstalledSource bytes baseSource sourceInit ∧
            Simulation.Interaction.ForwardRel
              Yul.FunctionsInteractionPrimitive.Truncated
              ObservableDoneRel
              (Solidity.RawAst.Raw.SourcePreservation.rawObjectRun (sourceFuel + 1)
                context selected.root sourceInit)
              (Assembly.Compact.InteractionSemantics.openRunNResult
                (Assembly.Bytecode.ofList bytes) openFuel
                (installedTarget bytes baseSource)) ∧
              Assembly.GasfulBridge.RunRefinesOpenTotal
                (EvmYul.EVM.X
                  (max openFuel (gasfulInitial.gasAvailable.toNat + 6))
                  (EvmYul.EVM.D_J (Assembly.Bytecode.ofList bytes)
                    (EvmYul.UInt256.ofNat 0))
                  gasfulInitial)
                (Assembly.Compact.InteractionSemantics.openRunNResult
                  (Assembly.Bytecode.ofList bytes)
                  (max openFuel (gasfulInitial.gasAvailable.toNat + 6))
                  (installedTarget bytes baseSource))
                transcript := by
  obtain ⟨artifact, cert, hArtifact, hCert, hBytes⟩ := compile?_parts hCompile
  subst hBytes
  rw [installedTarget_eq artifact baseSource] at hInitial
  obtain ⟨json, selected, context, structuredFuel, transcript,
      hJson, hSelected, _hAccepted, hForward, hTotal⟩ :=
    Solidity.RawAst.optimizedRawSolcIrToGasfulRawBytecodeTotal
      (sourceFuel := sourceFuel) (baseSource := baseSource)
      hArtifact hCert hInitial
  rw [← installedTarget_eq artifact baseSource] at hForward hTotal
  exact ⟨json, selected, context,
    Yul.EndToEnd.installedSourceState artifact baseSource, _, transcript,
    hJson, hSelected, installedSource_witness artifact baseSource,
    hForward.mono fun sourceDone targetDone hDone =>
      Solidity.Raw.SourcePreservation.RawSourceBytecodePrefixDoneRel.observable
        hDone,
    hTotal⟩

/-- Public correctness theorem for the creation frame: the compiled image
with a constructor-argument suffix appended, against the interpreter's own
jumpdest scan of the full installed image. -/
theorem compile_correct_creation
    {rawJson : String} {selection : Solidity.RawAst.Selection}
    {bytes : List UInt8}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    {gasfulInitial : Assembly.EVMState}
    (suffix : List UInt8)
    (hCompile : compile? rawJson selection = some bytes)
    (hInitial :
      Assembly.GasfulBridge.OpenStateRel gasfulInitial
        (installedTarget (bytes ++ suffix) baseSource)) :
    ∃ (json : Lean.Json) (selected : Solidity.RawAst.SelectedIr)
        (context : Solidity.Frontend.ObjectBuiltinContext)
        (sourceInit : Yul.InteractionSemantics.State)
        (openFuel : Nat)
        (transcript : Simulation.Interaction.Transcript),
      Lean.Json.parse rawJson = .ok json ∧
        Solidity.RawAst.decodeSelectedIr json selection = .ok selected ∧
          InstalledSource (bytes ++ suffix) baseSource sourceInit ∧
            Simulation.Interaction.ForwardRel
              Yul.FunctionsInteractionPrimitive.Truncated
              ObservableDoneRel
              (Solidity.RawAst.Raw.SourcePreservation.rawObjectRun (sourceFuel + 1)
                context selected.root sourceInit)
              (Assembly.Compact.InteractionSemantics.openRunNResult
                (Assembly.Bytecode.ofList (bytes ++ suffix)) openFuel
                (installedTarget (bytes ++ suffix) baseSource)) ∧
              Assembly.GasfulBridge.RunRefinesOpenTotal
                (EvmYul.EVM.X
                  (max openFuel (gasfulInitial.gasAvailable.toNat + 6))
                  (EvmYul.EVM.D_J
                    (Assembly.Bytecode.ofList (bytes ++ suffix))
                    (EvmYul.UInt256.ofNat 0))
                  gasfulInitial)
                (Assembly.Compact.InteractionSemantics.openRunNResult
                  (Assembly.Bytecode.ofList (bytes ++ suffix))
                  (max openFuel (gasfulInitial.gasAvailable.toNat + 6))
                  (installedTarget (bytes ++ suffix) baseSource))
                transcript := by
  obtain ⟨artifact, cert, hArtifact, hCert, hBytes⟩ := compile?_parts hCompile
  subst hBytes
  rw [installedTarget_eqWithCodeSuffix artifact suffix baseSource] at hInitial
  obtain ⟨json, selected, context, structuredFuel, transcript,
      hJson, hSelected, _hAccepted, hForward, hTotal⟩ :=
    Solidity.RawAst.optimizedRawSolcIrToGasfulRawBytecodeTotalWithCodeSuffix
      (sourceFuel := sourceFuel) (baseSource := baseSource)
      suffix hArtifact hCert hInitial
  rw [← installedTarget_eqWithCodeSuffix artifact suffix baseSource]
    at hForward hTotal
  exact ⟨json, selected, context,
    Yul.EndToEnd.installedSourceStateWithCodeSuffix artifact suffix baseSource,
    _, transcript,
    hJson, hSelected,
    installedSource_witnessWithCodeSuffix artifact suffix baseSource,
    hForward.mono fun sourceDone targetDone hDone =>
      Solidity.Raw.SourcePreservation.RawSourceBytecodePrefixDoneRel.observable
        hDone,
    hTotal⟩

/-!
## Unlinked-library public surface

The two theorems below extend the public claim to the verified
unlinked-library pipeline (`compileUnlinked?`), which compiles a contract
whose external `linkersymbol` library addresses the input's
`settings.libraries` metadata leaves unresolved.  Missing libraries are
rewritten to `loadimmutable` markers, so the deployed byte image is genuine
compiler output carrying the same fail-closed stack-headroom certificate as
`compile?`, plus a solc-compatible `linkReferences` export (the 20-byte
address windows a linker patches).

* `compile_correct_unlinked` is the escape-free crown for the **delivered
  unlinked image** itself: the charged run at the gas-derived fuel refines the
  open run with no escape constructor.  Because the missing libraries were
  rewritten to `loadimmutable`, the source side of this claim is the
  artifact's *own resolved program* — the rewrite-to-immutable form in which
  every unresolved library slot reads as the zero address until patched.  This
  is the exact analog of `compile_correct` for the bytes the unlinked pipeline
  emits.

* `compile_correct_unlinked_patch` is the **link-time bridge**: for every
  deploy address assignment whose library addresses are address-sized and for
  which the deploy-value compile succeeds, patching the exported windows of the
  unlinked image reproduces, byte for byte, `withValues.bytes` followed by the
  unchanged child payload — and that value compile is exactly the *original*
  (un-rewritten) object resolved with those addresses supplied as linker
  symbols, its ordered Yul program being the value compile's own ordered
  program.  So "patching real library addresses into the unlinked image" and
  "compiling the original source with those addresses" produce the same bytes;
  the guarantee `compile_correct` makes about the value compile therefore
  transfers to the patched image.

### Residual gap (honest)

Fusing the two into a single `RunRefinesOpenTotal` over the *patched* bytes
with the *original* (linkersymbol) source in one statement is not delivered
here: it would require identifying `withValues.bytes ++ payload` as the image
of a full object-level `VerifiedStackObjectArtifact` obtained from the
supported pipeline and re-running the gasful crown over it (an object-level
value-compile crown / pipeline-identification campaign, beyond composition of
the existing endpoints).  The two theorems together are the strongest true
composed statement available from the current tower: the delivered bytes are
fully covered against their own source, and the patch equation pins the linked
bytes to a verified compile of the original source. -/
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
addresses into the unlinked image reproduces the verified value-compile of the
original source with those addresses.  See the module note above; the full
statement is `Solidus.compileUnlinked?_patchImmutablesAndLibraries_resolvesOriginal`. -/
alias compile_correct_unlinked_patch :=
  compileUnlinked?_patchImmutablesAndLibraries_resolvesOriginal

end Solidus
end EvmCompiler
