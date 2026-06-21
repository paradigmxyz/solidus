import EvmCompiler.Functions.StackExpressionPreservation

namespace EvmCompiler
namespace Functions
namespace StackStatementPreservation

open StackRelation

structure CtxCovers (source : Locals.Source.Ctx)
    (target : Locals.Ctx) : Prop where
  scope : ∀ {name : Name}, name ∈ target.layout → name ∈ source.scope

namespace CtxCovers

theorem prepend
    {source : Locals.Source.Ctx} {target : Locals.Ctx}
    (hCtx : CtxCovers source target) (name : Name) :
    CtxCovers { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) := by
  constructor
  intro candidate hCandidate
  rcases List.mem_cons.mp hCandidate with hName | hTail
  · exact List.mem_cons.mpr (.inl hName)
  · exact List.mem_cons.mpr (.inr (hCtx.scope hTail))

end CtxCovers

structure RegularResultRel (targetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Locals.Source.Ctx)
    (target : Structured.Outcome) : Prop where
  sourceMode : source.1.mode = .regular
  targetMode : target.mode = .regular
  context : CtxCovers source.2 targetCtx
  state :
    StateRel targetCtx.layout suffix returns source.1.state target.state

abbrev RegularOutcomeRel (targetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (RegularResultRel targetCtx suffix returns)

theorem openRun_let_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx : Locals.Ctx)
    (fuel : Nat) {name : Name} (valueExpr : Locals.Expr 1)
    {valueCode : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hValueScoped : Locals.Scope.ExprScoped targetCtx.layout valueExpr)
    (hValueSupported :
      Locals.InteractionSemantics.Expr.OpenSupported valueExpr)
    (hValueCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout (name :: targetCtx.layout)) suffix returns)
      (Locals.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram fuel
        (.code
          (valueCode ++ Locals.bindLocals 0 (name :: targetCtx.layout)))
        target) := by
  have hValue :=
    StackExpressionPreservation.openEvalOne_fresh_compileCode
      valueExpr targetCtx name hFresh hValueScoped hValueSupported
      hValueCompile hInitial
  have hCore :
      Simulation.Interaction.Rel
        (RegularOutcomeRel
          (targetCtx.withLayout (name :: targetCtx.layout)) suffix returns)
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.Expr.openEvalOne valueExpr source)
          (fun result =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular
                (result.1.insert name result.2),
               { sourceCtx with scope := name :: sourceCtx.scope })))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun valueCode target)
          (fun targetAfterValue =>
            Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun
                (Locals.bindLocals 0 (name :: targetCtx.layout))
                targetAfterValue)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.regular final)))) := by
    apply Simulation.Interaction.Rel.bind hValue
    intro sourceAfterValue targetAfterValue hValueResult
    rcases sourceAfterValue with ⟨sourceFinal, value⟩
    rw [show Locals.bindLocals 0 (name :: targetCtx.layout) =
        [.bindLocals 0 (name :: targetCtx.layout)] by rfl,
      Locals.InteractionPreservation.Code.openRun_bindLocals]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx.prepend name
        state := hValueResult }
  unfold Locals.InteractionSemantics.Expr.openEvalOne
    Locals.InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel at hCore
  unfold Locals.InteractionSemantics.Stmt.openRun
    Expressions.InteractionSemantics.Stmt.openRun
    Locals.InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Locals.Source.Effectful.StateModel.insert,
    Expressions.EffectSemantics.Control.Stmt.run]
  change
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout (name :: targetCtx.layout)) suffix returns)
      _
      (Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun
          (valueCode ++ Locals.bindLocals 0 (name :: targetCtx.layout))
          target)
        (fun final =>
          Simulation.Interaction.pure (Structured.Outcome.regular final)))
  rw [Structured.InteractionSemantics.Code.openRun_append]
  simpa [Simulation.Interaction.bind_assoc] using hCore

end StackStatementPreservation
end Functions
end EvmCompiler
