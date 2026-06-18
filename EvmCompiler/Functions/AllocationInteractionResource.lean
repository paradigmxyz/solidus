import EvmCompiler.Functions.AllocationInteractionFrame
import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Expressions.InteractionSemantics

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionResource

open AllocationInteractionRelation
open AllocationInteractionFrame

/--
Allocator preservation for one completed Functions-to-Expressions control
result. Semantic outcome matching remains an independent adjacent capability.
-/
abbrev ResultRel
    (config : Config) (allocatorDepth : Nat) (entryMode : ActivationMode)
    (targetInitial : TargetState)
    (_sourceResult :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)
    (targetResult : Expressions.InteractionSemantics.Outcome) : Prop :=
  ActivationEffect config allocatorDepth entryMode
    targetInitial targetResult.state

abbrev OpenResultRel
    (config : Config) (allocatorDepth : Nat) (entryMode : ActivationMode)
    (targetInitial : TargetState) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (ResultRel config allocatorDepth entryMode targetInitial)

end AllocationInteractionResource
end Functions
end EvmCompiler
