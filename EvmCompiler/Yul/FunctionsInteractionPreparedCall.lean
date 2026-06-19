import EvmCompiler.Yul.FunctionsInteractionPreparedPrimitive

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedCall

open FunctionsInteractionPreparedArgs

/-- Preservation for the call-specific argument artifact emitted by the
ordinary Yul compiler. Nonempty calls reuse bounded-argument preservation;
the empty-call constructor is the identity computation. -/
theorem ofUncheckedCallArgsLowering
    {fuel targetFuel : Nat}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {initial final : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLowering : Expr.UncheckedCallArgsLowering
      initial args pre lowerArgs final)
    (hBound : RecursiveBoundHeads
      fuel targetFuel codeOverride program layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target)
    (hDomain : FunctionsInteractionRelation.TargetDomainWithin
      initial.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ initial.used)
    (hTargetFuel : pre.length < targetFuel) :
    Simulation.Interaction.ForwardRel
      FunctionsInteractionPrimitive.Truncated
      (DoneRel layout final lowerArgs.reverse target)
      (Yul.InteractionSemantics.evalArgs
        fuel args.reverse codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel { stmts := pre } target) := by
  cases hLowering with
  | empty =>
      cases targetFuel with
      | zero => simp at hTargetFuel
      | succ remaining =>
          simpa using
            (FunctionsInteractionPreparedArgs.nil
              (fuel := fuel) (targetFuel := remaining)
              (codeOverride := codeOverride) (program := program)
              (ctx := ctx) hRel hDomain)
  | bound _hNonempty hArgs =>
      exact FunctionsInteractionPreparedArgs.ofUncheckedLowering
        (ctx := ctx) hArgs hBound hRel hDomain hLayout hTargetFuel

end FunctionsInteractionPreparedCall
end Yul
end EvmCompiler
