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
    (sourceResult :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)
    (targetResult : Expressions.InteractionSemantics.Outcome) : Prop :=
  OutcomeEffect config allocatorDepth entryMode
    targetInitial targetResult.state sourceResult.1.mode

abbrev OpenResultRel
    (config : Config) (allocatorDepth : Nat) (entryMode : ActivationMode)
    (targetInitial : TargetState) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (ResultRel config allocatorDepth entryMode targetInitial)

end AllocationInteractionResource
end Functions
end EvmCompiler
