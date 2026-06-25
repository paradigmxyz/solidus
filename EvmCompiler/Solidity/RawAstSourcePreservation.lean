import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Yul.EndToEnd
import EvmCompiler.Yul.FunctionsInteractionPrimitive

/-!
Semantic interface for preserving accepted raw solc Yul to ordered Yul.

This file intentionally contains the relation shape, not the final source
theorem.  The remaining proof work should discharge `ObjectPreserved` from
`decodeAndElaborateSolcIr?` success and the checked frontend validation facts,
then compose it with `RawAstEndToEnd`.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst
namespace Raw
namespace SourcePreservation

abbrev State := Yul.InteractionSemantics.State
abbrev Failure := Yul.InteractionSemantics.Failure
abbrev Open (α : Type) := Yul.InteractionSemantics.Open α

def SameDoneRel {α : Type} :
    Except Failure α → Except Failure α → Prop :=
  Eq

def rawObjectRun (fuel : Nat) (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (state : State) : Open State :=
  Raw.SourceSemantics.execObjectCode fuel
    (Raw.SourceSemantics.contextForObject context) object state

def orderedRun (fuel : Nat) (ordered : Yul.OrderedProgram)
    (state : State) : Open State :=
  Yul.InteractionSemantics.exec fuel
    (.Block [ordered.program.contract.dispatcher])
    (some ordered.program.contract) state

/-- Finite-prefix preservation from raw solc Yul execution to ordered Yul
execution for one selected object/context/fuel pair. -/
def RunForward (rawFuel orderedFuel : Nat)
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram)
    (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (rawObjectRun rawFuel context object state)
    (orderedRun orderedFuel ordered state)

/-- Whole-object raw-to-ordered preservation surface.

The proof should be private to the Solidity frontend: callers get it by
successful raw decoding/elaboration/compilation, not by providing generated
names, replay traces, layouts, or certificates.
-/
structure ObjectPreserved
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  forward :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel, RunForward rawFuel orderedFuel context object ordered state

theorem forward_refl {α : Type}
    (truncated : Failure → Prop)
    (run : Open α) :
    Simulation.Interaction.ForwardRel truncated SameDoneRel run run := by
  induction run with
  | done result =>
      exact .done rfl
  | request query resume ih =>
      exact .request ih

theorem runForward_of_eq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    {state : State}
    (hRun :
      rawObjectRun rawFuel context object state =
        orderedRun orderedFuel ordered state) :
    RunForward rawFuel orderedFuel context object ordered state := by
  unfold RunForward
  rw [hRun]
  exact
    forward_refl Yul.FunctionsInteractionPrimitive.Truncated
      (orderedRun orderedFuel ordered state)

structure ObjectRunEquivalent
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  run_eq :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        rawObjectRun rawFuel context object state =
          orderedRun orderedFuel ordered state

namespace ObjectRunEquivalent

theorem preserved
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    (hEq : ObjectRunEquivalent context object ordered) :
    ObjectPreserved context object ordered where
  forward := by
    intro rawFuel state
    rcases hEq.run_eq rawFuel state with ⟨orderedFuel, hRun⟩
    exact ⟨orderedFuel, runForward_of_eq hRun⟩

end ObjectRunEquivalent

structure ObjectPositiveRunEquivalent
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  run_eq :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        rawObjectRun (rawFuel + 1) context object state =
          orderedRun (orderedFuel + 1) ordered state

def RawSourceBytecodePrefixDoneRel
    (artifact : Frontend.Program.Artifact) :
    Except Failure State →
      Except Assembly.EVMException Assembly.StepResult →
        Prop :=
  fun rawDone bytecodeDone =>
    ∃ orderedDone,
      SameDoneRel rawDone orderedDone ∧
        Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
          artifact orderedDone bytecodeDone

structure ArtifactRawSourceEquivalent
    (rawJson : String) (selection : Selection)
    (artifact : Frontend.Program.Artifact) where
  json : Lean.Json
  selected : SelectedIr
  program : Frontend.Program
  linkerSymbols : List (Frontend.Name × Frontend.Word)
  context : Frontend.ObjectBuiltinContext
  parse :
    Lean.Json.parse rawJson = .ok json
  selected_ok :
    decodeSelectedIr json selection = .ok selected
  decode :
    decodeAndElaborateSolcIr? rawJson selection = some program
  raw_elaborates :
    selected.root.elaborate? selected.evmVersion = .ok program.object
  linker :
    decodeLinkerSymbols? rawJson selection = some linkerSymbols
  compile :
    program.compileArtifactWithLinkerSymbols? linkerSymbols = some artifact
  codeArtifact :
    program.object.compileVerifiedStackCodeArtifactIn? context =
      some artifact.codeArtifact
  resolved :
    program.object.resolveObjectBuiltinsIn? context =
      some artifact.codeArtifact.resolved
  ordered :
    artifact.codeArtifact.resolved.toSolcYulOrderedProgram? =
      some artifact.codeArtifact.ordered
  sourceRun :
    ObjectPositiveRunEquivalent context selected.root
      artifact.codeArtifact.ordered

theorem rawSourceEquivalentToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hSource :
      ArtifactRawSourceEquivalent rawJson selection artifact) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) hSource.context hSource.selected.root
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
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases hSource.sourceRun.run_eq rawFuel
      (Yul.EndToEnd.installedSourceState artifact baseSource) with
    ⟨orderedFuel, hRawOrdered⟩
  rcases
      Yul.EndToEnd.optimizedSolcYulToRawBytecode
        (object := hSource.program.object)
        (linkerSymbols := hSource.linkerSymbols)
        (artifact := artifact)
        (sourceFuel := orderedFuel)
        (baseSource := baseSource)
        hSource.compile with
    ⟨structuredFuel, hAccepted, hOrderedBytecode⟩
  have hRawOrderedForward :
      Simulation.Interaction.ForwardRel
        Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
        (rawObjectRun (rawFuel + 1) hSource.context hSource.selected.root
          (Yul.EndToEnd.installedSourceState artifact baseSource))
        (orderedRun (orderedFuel + 1) artifact.codeArtifact.ordered
          (Yul.EndToEnd.installedSourceState artifact baseSource)) :=
    runForward_of_eq hRawOrdered
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact
    Simulation.Interaction.ForwardRel.trans
      hRawOrderedForward hOrderedBytecode
      (by
        intro rawDone orderedError hSame hTruncated
        subst rawDone
        exact ⟨orderedError, rfl, hTruncated⟩)

end SourcePreservation
end Raw
end RawAst
end Solidity
end EvmCompiler
