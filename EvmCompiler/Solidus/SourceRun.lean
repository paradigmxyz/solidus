import EvmCompiler.Solidity.RawAstSourceSemantics

/-!
# Frozen source-run spec (Solidus Arena freeze cone)

This module holds the statement-level source-side symbols of
`EvmCompiler.Solidus.compile_correct`:

* `Solidity.RawAst.Raw.SourcePreservation.rawObjectRun` (C3) — the entry point
  that runs the *decoded* object's independent Yul semantics. It is the
  source-refinement anchor of the theorem (`ForwardRel ... (rawObjectRun ...)`);
  if it were redefined to ignore its object argument the whole source conjunct
  would be vacuous. It is relocated out of the mutable 15k-line, ~1438-lemma
  `Solidity/RawAstSourcePreservation.lean`. Its callees (`execObjectCode`,
  `contextForObject`) already live in the trusted source interpreter
  `Solidity/RawAstSourceSemantics.lean`, imported here. The `State`/`Failure`/
  `Open` abbreviations it is typed against move with it (they were defined in
  the preservation file).

* `Yul.FunctionsInteractionPrimitive.Truncated` (C4) — the finite-fuel
  divergence predicate whose `ForwardRel.truncated` arm makes the
  source-refinement conjunct vacuous. Relocated out of the mutable
  Yul-functions preservation file `Yul/FunctionsInteractionPrimitive.lean`
  (whose `ErrorRel`/`ResultRel`/`DoneRel` machinery adversaries legitimately
  rewrite) so that `Truncated := fun _ => True` cannot be smuggled in.

All definitions keep their fully-qualified names and namespaces; the original
files now import this module. This module references only the trusted source
interpreter and the frozen source-failure vocabulary.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPrimitive

/-- Structural source-fuel exhaustion for which finite source semantics makes
no target-suffix claim. Validation and scoped preservation derive malformed
source exclusions before this public compiler relation. -/
def Truncated (failure : Yul.InteractionSemantics.Failure) : Prop :=
  match failure.exception with
  | .OutOfFuel => True
  | _ => False

end FunctionsInteractionPrimitive
end Yul

namespace Solidity
namespace RawAst
namespace Raw
namespace SourcePreservation

abbrev State := Yul.InteractionSemantics.State
abbrev Failure := Yul.InteractionSemantics.Failure
abbrev Open (α : Type) := Yul.InteractionSemantics.Open α

def rawObjectRun (fuel : Nat) (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (state : State) : Open State :=
  Raw.SourceSemantics.execObjectCode fuel
    (Raw.SourceSemantics.contextForObject context) object state

end SourcePreservation
end Raw
end RawAst
end Solidity
end EvmCompiler
