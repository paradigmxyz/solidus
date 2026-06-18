import EvmCompiler.Functions.AllocationInteractionPrimitive
import EvmCompiler.Functions.InteractionSemantics

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionSafety

abbrev SourceState := AllocationInteractionRelation.SourceState
abbrev Word := Assembly.Word

mutual
  /-- Source-facing safety of an expression for every open-world answer. -/
  def ExprSafe (contract : MemoryContract.Contract) {results : Nat}
      (expr : Functions.Expr results) (source : SourceState) : Prop :=
    match expr with
    | .lit _ => True
    | .var name => ∃ value, source.vars name = some value
    | .code _ => False
    | .prim op args =>
        Locals.InteractionSemantics.Primitive.supportsOpen op = true ∧
          ExprSeqSafe contract args source ∧
          Simulation.Interaction.AllDone
            (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
            (Functions.InteractionSemantics.ExprSeq.openEval args source)

  /-- Source-facing safety of an expression sequence under ordered evaluation. -/
  def ExprSeqSafe (contract : MemoryContract.Contract) {results : Nat}
      (exprs : Locals.ExprSeq results) (source : SourceState) : Prop :=
    match exprs with
    | .nil => True
    | .cons head tail =>
        ExprSafe contract head source ∧
          Simulation.Interaction.AllDone
            (fun outcome =>
              match outcome with
              | .error _ => True
              | .ok result => ExprSeqSafe contract tail result.1)
            (Functions.InteractionSemantics.Expr.openEval head source)
end

/-- Source-facing safety for canonical left-to-right call arguments. -/
def ArgListSafe (contract : MemoryContract.Contract) :
    List (Functions.Expr 1) → SourceState → Prop
  | [], _source => True
  | arg :: rest, source =>
      ExprSafe contract arg source ∧
        Simulation.Interaction.AllDone
          (fun outcome =>
            match outcome with
            | .error _ => True
            | .ok result => ArgListSafe contract rest result.1)
          (Functions.InteractionSemantics.Expr.openEvalOne arg source)

end AllocationInteractionSafety
end Functions
end EvmCompiler
