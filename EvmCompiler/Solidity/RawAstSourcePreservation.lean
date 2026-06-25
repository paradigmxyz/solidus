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

end SourcePreservation
end Raw
end RawAst
end Solidity
end EvmCompiler
