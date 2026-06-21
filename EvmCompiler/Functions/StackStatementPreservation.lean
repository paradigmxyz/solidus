import EvmCompiler.Functions.StackExpressionPreservation
import EvmCompiler.Functions.StackAccessLowering
import EvmCompiler.Functions.StackLowering
import EvmCompiler.Functions.StackTransitionCompilation
import EvmCompiler.Functions.InteractionSemantics

namespace EvmCompiler
namespace Functions
namespace StackStatementPreservation

open StackRelation

structure CtxCovers (source : Functions.Source.Ctx)
    (target : Locals.Ctx) : Prop where
  scope : ∀ {name : Name}, name ∈ target.layout → name ∈ source.scope

namespace CtxCovers

theorem prepend
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    (hCtx : CtxCovers source target) (name : Name) :
    CtxCovers { source with scope := name :: source.scope }
      (target.withLayout (name :: target.layout)) := by
  constructor
  intro candidate hCandidate
  rcases List.mem_cons.mp hCandidate with hName | hTail
  · exact List.mem_cons.mpr (.inl hName)
  · exact List.mem_cons.mpr (.inr (hCtx.scope hTail))

theorem afterTransition
    {source : Functions.Source.Ctx} {target : Locals.Ctx}
    (hCtx : CtxCovers source target)
    (transition : AllocationLayout.Transition)
    (hSource : target.layout = transition.source) :
    CtxCovers source
      (target.withLayout transition.schedule.target) := by
  constructor
  intro name hName
  have hTarget : name ∈ transition.schedule.target := by
    simpa [Locals.Ctx.withLayout] using hName
  have hRetained :
      name ∈ AllocationLayout.retained transition.source transition.live := by
    rwa [← transition.valid.2.1]
  have hOriginal : name ∈ transition.source :=
    (List.mem_filter.mp hRetained).1
  apply hCtx.scope
  rwa [hSource]

end CtxCovers

structure RegularResultRel (targetCtx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Functions.Source.Ctx)
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

theorem openRun_transition_generated
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
      ∃ final,
        Locals.Block.compileOpen targetCtx
            { stmts := transition.schedule.statements } =
          some
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup],
             targetCtx.withLayout transition.schedule.target) ∧
        Structured.InteractionSemantics.Code.openRun
            (artifact.promotionCodes.flatten ++ artifact.cleanup) target =
          .done (.ok final) ∧
        RegularResultRel
          (targetCtx.withLayout transition.schedule.target)
          suffix returns
          (Locals.Source.Effectful.Outcome.regular source, sourceCtx)
          (Structured.Outcome.regular final) := by
  obtain ⟨artifact, final, hCompile, hRun, hFinal⟩ :=
    StackTransitionCompilation.Transition.compiledOpenRun
      transition hSource hInitial
  exact
    ⟨artifact, final, hCompile, hRun,
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx.afterTransition transition hSource
        state := hFinal }⟩

theorem openRun_transition_block_generated
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
      ∃ final,
        Locals.Block.compileOpen targetCtx
            { stmts := transition.schedule.statements } =
          some
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup],
             targetCtx.withLayout transition.schedule.target) ∧
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (artifact.promotionCodes.length + 2)
            { stmts :=
                artifact.promotionCodes.map Expressions.Stmt.code ++
                  [Expressions.Stmt.code artifact.cleanup] }
            target =
          .done (.ok (Structured.Outcome.regular final)) ∧
        RegularResultRel
          (targetCtx.withLayout transition.schedule.target)
          suffix returns
          (Locals.Source.Effectful.Outcome.regular source, sourceCtx)
          (Structured.Outcome.regular final) := by
  obtain ⟨artifact, final, hCompile, hRun, hFinal⟩ :=
    StackTransitionCompilation.Transition.compiledBlockOpenRun
      targetProgram transition hSource hInitial
  exact
    ⟨artifact, final, hCompile, hRun,
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx.afterTransition transition hSource
        state := hFinal }⟩

def RegularPointPreserves
    (targetProgram : Expressions.Program) (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    (sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx))
    (head : Expressions.Stmt)
    (targetFuel : Nat)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (target : Structured.RunState) : Prop :=
  ∃ artifact : StackTransitionCompilation.Artifact targetCtx transition,
    Locals.Block.compileOpen targetCtx
        { stmts := transition.schedule.statements } =
      some
        (artifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.cleanup],
         targetCtx.withLayout transition.schedule.target) ∧
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout transition.schedule.target)
        suffix returns)
      sourceRun
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel
        { stmts :=
            head ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]) }
        target)

theorem regularThenTransition
    (targetProgram : Expressions.Program)
    (targetCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    (sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx))
    (head : Expressions.Stmt)
    (targetFuel : Nat)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hHead : ∀ targetFuel,
      Simulation.Interaction.Rel
        (RegularOutcomeRel targetCtx suffix returns)
        sourceRun
        (Expressions.InteractionSemantics.Stmt.openRun
          targetProgram targetFuel head target)) :
    RegularPointPreserves targetProgram targetCtx transition sourceRun
      head targetFuel suffix returns target := by
  unfold RegularPointPreserves
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact
      transition hSource
  have hCodeLength :
      artifact.promotionCodes.length =
        transition.schedule.promotions.length :=
    artifact.codes.code_length
  have hCodeFuel : artifact.promotionCodes.length + 2 < targetFuel := by
    rw [hCodeLength]
    exact hFuel
  refine ⟨artifact, artifact.compileEq, ?_⟩
  change
    Simulation.Interaction.Rel
      (RegularOutcomeRel
        (targetCtx.withLayout transition.schedule.target)
        suffix returns)
      sourceRun
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel
        { stmts := [head] ++
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup]) }
        target)
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_stmt_of_fuel
    targetProgram targetFuel head target (by omega)]
  rw [← Simulation.Interaction.bind_pure sourceRun]
  apply Simulation.Interaction.Rel.bind
    (hHead (targetFuel - 1))
  intro sourceResult targetResult hResult
  simp only [hResult.targetMode, List.length_cons, List.length_nil,
    Nat.add_zero]
  obtain ⟨final, hRun, hFinalRel⟩ :=
    artifact.blockOpenRun targetProgram (targetFuel - 1) (by omega)
      hResult.state
  rw [hRun]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  exact
    { sourceMode := hResult.sourceMode
      targetMode := rfl
      context := hResult.context.afterTransition transition hSource
      state := hFinalRel }

theorem openRun_expr_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (expr : Locals.Expr 0)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hScoped : Locals.Scope.ExprScoped targetCtx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode targetCtx 0 expr = some code)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram targetFuel (.code code) target) := by
  have hExpr :=
    StackExpressionPreservation.openEvalZero_compileCode
      expr targetCtx hScoped hSupported hCompile hInitial
  have hWrapped :
      Simulation.Interaction.Rel
        (RegularOutcomeRel targetCtx suffix returns)
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.Expr.openEval expr source)
          (fun result =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular result.1,
               sourceCtx)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun code target)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final))) := by
    apply Simulation.Interaction.Rel.bind hExpr
    intro sourceFinal targetFinal hFinal
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx
        state := hFinal }
  unfold Locals.InteractionSemantics.Expr.openEval
    Structured.InteractionSemantics.Code.openRun at hWrapped
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Expressions.InteractionSemantics.Stmt.openRun
    Functions.InteractionSemantics.stateModel
  simp only [Expressions.EffectSemantics.Control.Stmt.run]
  exact hWrapped

theorem openRun_let_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Locals.Expr 1)
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
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram targetFuel
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
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Expressions.InteractionSemantics.Stmt.openRun
    Functions.InteractionSemantics.stateModel
  simp only [Locals.Source.Effectful.StateModel.insert,
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

theorem openRun_assign_generated
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Locals.Expr 1)
    {depth : Nat} {valueCode : Structured.Code}
    {swapOp : Structured.BasicOp} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hDepth :
      Locals.Layout.lookupDepth? name targetCtx.layout = some (depth + 1))
    (hValueScoped : Locals.Scope.ExprScoped targetCtx.layout valueExpr)
    (hValueSupported :
      Locals.InteractionSemantics.Expr.OpenSupported valueExpr)
    (hValueCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hSwap : Locals.StackOp.swap? (depth + 1) = some swapOp)
    (hInitial :
      StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (RegularOutcomeRel targetCtx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Stmt.openRun
        targetProgram targetFuel
        (.code
          (valueCode ++ [.op swapOp, .op .pop] ++
            Locals.bindLocals 0 targetCtx.layout))
        target) := by
  have hValue :=
    StackExpressionPreservation.openEvalOne_compileCode
      valueExpr targetCtx hValueScoped hValueSupported
      hValueCompile hInitial
  have hAt : targetCtx.layout[depth]? = some name :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
  have hMem : name ∈ targetCtx.layout :=
    List.mem_of_getElem? hAt
  obtain ⟨old, hOld⟩ := hInitial.defined hMem
  have hContains : source.vars.contains name = true := by
    simp [Locals.Source.Store.contains, hOld]
  have hContains' :
      (Locals.InteractionSemantics.stateModel.source source).vars.contains
          name = true := by
    simpa [Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel] using hContains
  have hOldStack : target.evm.stack[depth]? = some old := by
    rw [hInitial.stack]
    have hValuesAt := values_getElem?_eq_some (source := source) hAt
    rw [hOld] at hValuesAt
    have hBound : depth < (values source targetCtx.layout).length :=
      List.getElem?_eq_some_iff.mp hValuesAt |>.1
    rw [List.getElem?_append_left hBound]
    exact hValuesAt
  have hCore :
      Simulation.Interaction.Rel
        (RegularOutcomeRel targetCtx suffix returns)
        (Simulation.Interaction.bind
          (Locals.InteractionSemantics.Expr.openEvalOne valueExpr source)
          (fun result =>
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular
                (result.1.insert name result.2), sourceCtx)))
        (Simulation.Interaction.bind
          (Structured.InteractionSemantics.Code.openRun
            (valueCode ++ [.op swapOp, .op .pop] ++
              Locals.bindLocals 0 targetCtx.layout)
            target)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.Outcome.regular final))) := by
    rw [List.append_assoc,
      Structured.InteractionSemantics.Code.openRun_append,
      Simulation.Interaction.bind_assoc]
    apply Simulation.Interaction.Rel.bind hValue
    intro sourceAfterValue targetAfterValue hValueResult
    rcases sourceAfterValue with ⟨sourceFinal, value⟩
    have hValueStack :
        targetAfterValue.evm.stack = value :: target.evm.stack := by
      simpa using hValueResult.stack
    obtain ⟨finalTarget, hSwapRun, hFinalStack,
        hFinalShared, hFinalReturns⟩ :=
      Locals.InteractionPreservation.Code.openRun_swap_pop
        hSwap hOldStack hValueStack
    rw [Structured.InteractionSemantics.Code.openRun_append,
      hSwapRun, Simulation.Interaction.bind_done_ok]
    rw [show Locals.bindLocals 0 targetCtx.layout =
        [.bindLocals 0 targetCtx.layout] by rfl,
      Locals.InteractionPreservation.Code.openRun_bindLocals,
      Simulation.Interaction.bind_done_ok]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      { sourceMode := rfl
        targetMode := rfl
        context := hCtx
        state := StateRel.ofExprResultOneAssign
          hNodup hDepth hInitial hValueResult
            hFinalShared hFinalReturns hFinalStack }
  unfold Locals.InteractionSemantics.Expr.openEvalOne
    Structured.InteractionSemantics.Code.openRun
    Locals.InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel at hCore
  simp only [Locals.Source.State.insert] at hCore
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
    Functions.Source.Effectful.Control.Stmt.run
    Expressions.InteractionSemantics.Stmt.openRun
    Functions.InteractionSemantics.stateModel
  simp only [Locals.Source.Effectful.StateModel.vars,
    Expressions.EffectSemantics.Control.Stmt.run]
  rw [hContains']
  simp only [Locals.Source.Effectful.StateModel.withVars,
    if_true, Locals.Source.State.withVars]
  simpa [Simulation.Interaction.bind_assoc] using hCore

theorem exprThenTransition
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (expr : Functions.Expr 0)
    (transition : AllocationLayout.Transition)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hScoped : Locals.Scope.ExprScoped targetCtx.layout expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hCompile : Locals.Expr.compileCode targetCtx 0 expr = some code)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    RegularPointPreserves targetProgram targetCtx transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (.code code) targetFuel suffix returns target := by
  apply regularThenTransition targetProgram targetCtx transition _ _
    targetFuel hSource hFuel
  intro leafFuel
  exact openRun_expr_generated sourceProgram targetProgram sourceCtx targetCtx
    sourceFuel leafFuel expr hCtx hScoped hSupported hCompile hInitial

theorem letThenTransition
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    {valueCode : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : name :: targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Locals.Scope.ExprScoped targetCtx.layout valueExpr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported valueExpr)
    (hCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    RegularPointPreserves targetProgram
      (targetCtx.withLayout (name :: targetCtx.layout)) transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source)
      (.code (valueCode ++ Locals.bindLocals 0 (name :: targetCtx.layout)))
      targetFuel suffix returns target := by
  apply regularThenTransition targetProgram
    (targetCtx.withLayout (name :: targetCtx.layout)) transition _ _ targetFuel
      (by simpa [Locals.Ctx.withLayout] using hSource) hFuel
  intro leafFuel
  exact openRun_let_generated sourceProgram targetProgram sourceCtx targetCtx
    sourceFuel leafFuel valueExpr hCtx hFresh hScoped hSupported hCompile
    hInitial

theorem assignThenTransition
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    {depth : Nat} {valueCode : Structured.Code}
    {swapOp : Structured.BasicOp} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hDepth :
      Locals.Layout.lookupDepth? name targetCtx.layout = some (depth + 1))
    (hScoped : Locals.Scope.ExprScoped targetCtx.layout valueExpr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported valueExpr)
    (hCompile :
      Locals.Expr.compileCode targetCtx 0 valueExpr = some valueCode)
    (hSwap : Locals.StackOp.swap? (depth + 1) = some swapOp)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    RegularPointPreserves targetProgram targetCtx transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name valueExpr) source)
      (.code
        (valueCode ++ [.op swapOp, .op .pop] ++
          Locals.bindLocals 0 targetCtx.layout))
      targetFuel suffix returns target := by
  apply regularThenTransition targetProgram targetCtx transition _ _
    targetFuel hSource hFuel
  intro leafFuel
  exact openRun_assign_generated sourceProgram targetProgram sourceCtx
    targetCtx sourceFuel leafFuel valueExpr hCtx hNodup hDepth hScoped
    hSupported hCompile hSwap hInitial

theorem RegularPointPreserves.compiledLowered
    (targetProgram : Expressions.Program)
    (beforeCtx pointCtx : Locals.Ctx)
    (transition : AllocationLayout.Transition)
    (sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Functions.Source.Ctx))
    (core : Locals.Stmt) (head : Expressions.Stmt)
    (lowered : List Locals.Stmt) (targetFuel : Nat)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (target : Structured.RunState)
    (hLowered :
      lowered = [core] ++ StackLowering.transitionStmts transition)
    (hCoreCompile :
      Locals.Stmt.compile beforeCtx core = some ([head], pointCtx))
    (hPreserves :
      RegularPointPreserves targetProgram pointCtx transition sourceRun
        head targetFuel suffix returns target) :
    ∃ artifact : StackTransitionCompilation.Artifact pointCtx transition,
      Locals.Block.compileOpen beforeCtx { stmts := lowered } =
          some
            (head ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]),
             pointCtx.withLayout transition.schedule.target) ∧
        Simulation.Interaction.Rel
          (RegularOutcomeRel
            (pointCtx.withLayout transition.schedule.target) suffix returns)
          sourceRun
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel
            { stmts :=
                head ::
                  (artifact.promotionCodes.map Expressions.Stmt.code ++
                    [Expressions.Stmt.code artifact.cleanup]) }
            target) := by
  obtain ⟨artifact, hTransitionCompile, hRun⟩ := hPreserves
  have hCoreBlock :
      Locals.Block.compileOpen beforeCtx { stmts := [core] } =
        some ([head], pointCtx) := by
    simpa [Locals.Block.compileOpen] using hCoreCompile
  have hWhole :=
    Locals.Block.compileOpen_append hCoreBlock hTransitionCompile
  refine ⟨artifact, ?_, hRun⟩
  simpa [hLowered] using hWhole

theorem compiledExprPoint
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (expr : Functions.Expr 0)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt)
    {sourceEnv : List Name}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hScoped : Functions.Scope.ExprScoped sourceEnv expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 expr = some ())
    (hLowered :
      lowered = [.expr expr] ++ StackLowering.transitionStmts transition)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    ∃ code, ∃ artifact :
      StackTransitionCompilation.Artifact targetCtx transition,
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
          some
            ((.code code) ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]),
             targetCtx.withLayout transition.schedule.target) ∧
        Simulation.Interaction.Rel
          (RegularOutcomeRel
            (targetCtx.withLayout transition.schedule.target) suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.expr expr) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel
            { stmts :=
                (.code code) ::
                  (artifact.promotionCodes.map Expressions.Stmt.code ++
                    [Expressions.Stmt.code artifact.cleanup]) }
            target) := by
  have hTargetScoped :=
    StackAccess.Expr.scoped_of_check hAccess hScoped
  obtain ⟨code, hCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check hAccess targetCtx rfl
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.expr expr) =
        some ([.code code], targetCtx) := by
    simp [Locals.Stmt.compile, hCompile, Locals.codeStmt]
  have hPreserves :=
    exprThenTransition sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel expr transition hSource hFuel hCtx hTargetScoped
      hSupported hCompile hInitial
  obtain ⟨artifact, hWhole, hRun⟩ :=
    RegularPointPreserves.compiledLowered targetProgram targetCtx targetCtx
      transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (.expr expr) (.code code) lowered targetFuel suffix returns target
      hLowered hCoreCompile hPreserves
  exact ⟨code, artifact, hWhole, hRun⟩

theorem compiledLetPoint
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (name : Name)
    (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt)
    {sourceEnv : List Name}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : name :: targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 value = some ())
    (hLowered :
      lowered = [.let_ name value] ++
        StackLowering.transitionStmts transition)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    ∃ code, ∃ artifact :
      StackTransitionCompilation.Artifact
        (targetCtx.withLayout (name :: targetCtx.layout)) transition,
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
          some
            ((.code
                (code ++
                  Locals.bindLocals 0 (name :: targetCtx.layout))) ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]),
             (targetCtx.withLayout (name :: targetCtx.layout)).withLayout
               transition.schedule.target) ∧
        Simulation.Interaction.Rel
          (RegularOutcomeRel
            ((targetCtx.withLayout (name :: targetCtx.layout)).withLayout
              transition.schedule.target) suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.let_ name value) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel
            { stmts :=
                (.code
                  (code ++
                    Locals.bindLocals 0 (name :: targetCtx.layout))) ::
                  (artifact.promotionCodes.map Expressions.Stmt.code ++
                    [Expressions.Stmt.code artifact.cleanup]) }
            target) := by
  have hTargetScoped :=
    StackAccess.Expr.scoped_of_check hAccess hScoped
  obtain ⟨code, hCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check hAccess targetCtx rfl
  let pointCtx := targetCtx.withLayout (name :: targetCtx.layout)
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.let_ name value) =
        some
          ([.code
              (code ++ Locals.bindLocals 0 (name :: targetCtx.layout))],
           pointCtx) := by
    simp [Locals.Stmt.compile, hCompile, Locals.codeStmt, pointCtx]
  have hPreserves :=
    letThenTransition sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel value transition hSource hFuel hCtx hFresh
      hTargetScoped hSupported hCompile hInitial
  obtain ⟨artifact, hWhole, hRun⟩ :=
    RegularPointPreserves.compiledLowered targetProgram targetCtx pointCtx
      transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name value) source)
      (.let_ name value)
      (.code (code ++ Locals.bindLocals 0 (name :: targetCtx.layout)))
      lowered targetFuel suffix returns target hLowered hCoreCompile hPreserves
  exact ⟨code, artifact, hWhole, hRun⟩

theorem compiledAssignPoint
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (name : Name)
    (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt)
    {sourceEnv : List Name}
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hSource : targetCtx.layout = transition.source)
    (hFuel : transition.schedule.promotions.length + 2 < targetFuel)
    (hCtx : CtxCovers sourceCtx targetCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.assign? targetCtx.layout name value = some ())
    (hLowered :
      lowered = [.assign name value] ++
        StackLowering.transitionStmts transition)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    ∃ (valueCode : Structured.Code) (swap : Structured.BasicOp),
      ∃ artifact :
      StackTransitionCompilation.Artifact targetCtx transition,
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
          some
            ((.code
                (valueCode ++ [.op swap, .op .pop] ++
                  Locals.bindLocals 0 targetCtx.layout)) ::
              (artifact.promotionCodes.map Expressions.Stmt.code ++
                [Expressions.Stmt.code artifact.cleanup]),
             targetCtx.withLayout transition.schedule.target) ∧
        Simulation.Interaction.Rel
          (RegularOutcomeRel
            (targetCtx.withLayout transition.schedule.target) suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.assign name value) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel
            { stmts :=
                (.code
                  (valueCode ++ [.op swap, .op .pop] ++
                    Locals.bindLocals 0 targetCtx.layout)) ::
                  (artifact.promotionCodes.map Expressions.Stmt.code ++
                    [Expressions.Stmt.code artifact.cleanup]) }
            target) := by
  obtain ⟨depth, swap, hValueAccess, hDepth, hSwap⟩ :=
    StackAccess.assign_components hAccess
  have hTargetScoped :=
    StackAccess.Expr.scoped_of_check hValueAccess hScoped
  obtain ⟨valueCode, hValueCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check
      hValueAccess targetCtx rfl
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.assign name value) =
        some
          ([.code
              (valueCode ++ [.op swap, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)],
           targetCtx) := by
    simp [Locals.Stmt.compile, hDepth, hValueCompile, hSwap,
      Locals.codeStmt]
  have hPreserves :=
    assignThenTransition sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel value transition hSource hFuel hCtx hNodup hDepth
      hTargetScoped hSupported hValueCompile hSwap hInitial
  obtain ⟨artifact, hWhole, hRun⟩ :=
    RegularPointPreserves.compiledLowered targetProgram targetCtx targetCtx
      transition
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.assign name value) source)
      (.assign name value)
      (.code
        (valueCode ++ [.op swap, .op .pop] ++
          Locals.bindLocals 0 targetCtx.layout))
      lowered targetFuel suffix returns target hLowered hCoreCompile hPreserves
  exact ⟨valueCode, swap, artifact, hWhole, hRun⟩

theorem compiledExprPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx : Locals.Ctx)
    (expr : Functions.Expr 0)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : targetCtx.layout = transition.source)
    (hScoped : Functions.Scope.ExprScoped sourceEnv expr)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported expr)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 expr = some ())
    (hLowered :
      lowered = [.expr expr] ++ StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    middleCtx = targetCtx.withLayout transition.schedule.target ∧
      headCode.length = transition.schedule.promotions.length + 2 ∧
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        transition.schedule.promotions.length + 2 < targetFuel →
        CtxCovers sourceCtx targetCtx →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (RegularOutcomeRel middleCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.expr expr) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := headCode } target) := by
  obtain ⟨exprCode, hExprCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check hAccess targetCtx rfl
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact transition hSource
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.expr expr) =
        some ([.code exprCode], targetCtx) := by
    simp [Locals.Stmt.compile, hExprCompile, Locals.codeStmt]
  have hCoreBlock :
      Locals.Block.compileOpen targetCtx { stmts := [.expr expr] } =
        some ([.code exprCode], targetCtx) := by
    simpa [Locals.Block.compileOpen] using hCoreCompile
  have hGenerated :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some
          ((.code exprCode) ::
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup]),
           targetCtx.withLayout transition.schedule.target) := by
    rw [hLowered]
    simpa using
      Locals.Block.compileOpen_append hCoreBlock artifact.compileEq
  have hPair := Option.some.inj (hCompile.symm.trans hGenerated)
  have hCodeEq := congrArg Prod.fst hPair
  have hCtxEq := congrArg Prod.snd hPair
  change
    headCode =
      (.code exprCode) ::
        (artifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.cleanup]) at hCodeEq
  change
    middleCtx = targetCtx.withLayout transition.schedule.target at hCtxEq
  refine ⟨hCtxEq, ?_, ?_⟩
  · rw [hCodeEq]
    simp [artifact.codes.code_length]
  · intro sourceCtx sourceFuel targetFuel suffix returns source target
      hFuel hCtx hInitial
    obtain ⟨_runtimeCode, runtimeArtifact, hRuntimeCompile, hRun⟩ :=
      compiledExprPoint sourceProgram targetProgram sourceCtx targetCtx
        sourceFuel targetFuel expr transition lowered hSource hFuel hCtx
        hScoped hSupported hAccess hLowered hInitial
    have hRuntimePair :=
      Option.some.inj (hCompile.symm.trans hRuntimeCompile)
    have hRuntimeCodeEq := congrArg Prod.fst hRuntimePair
    have hRuntimeCtxEq := congrArg Prod.snd hRuntimePair
    change
      headCode =
        (.code _runtimeCode) ::
          (runtimeArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code runtimeArtifact.cleanup]) at hRuntimeCodeEq
    change middleCtx =
      targetCtx.withLayout transition.schedule.target at hRuntimeCtxEq
    simpa [hRuntimeCodeEq, hRuntimeCtxEq] using hRun

theorem compiledLetPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx : Locals.Ctx)
    (name : Name) (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : name :: targetCtx.layout = transition.source)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.Expr.check? targetCtx.layout 0 value = some ())
    (hLowered :
      lowered = [.let_ name value] ++
        StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    middleCtx =
        (targetCtx.withLayout (name :: targetCtx.layout)).withLayout
          transition.schedule.target ∧
      headCode.length = transition.schedule.promotions.length + 2 ∧
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        transition.schedule.promotions.length + 2 < targetFuel →
        CtxCovers sourceCtx targetCtx →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (RegularOutcomeRel middleCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.let_ name value) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := headCode } target) := by
  obtain ⟨valueCode, hValueCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check hAccess targetCtx rfl
  let pointCtx := targetCtx.withLayout (name :: targetCtx.layout)
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact transition
      (ctx := pointCtx) (by simpa [pointCtx, Locals.Ctx.withLayout] using hSource)
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.let_ name value) =
        some
          ([.code
              (valueCode ++
                Locals.bindLocals 0 (name :: targetCtx.layout))],
           pointCtx) := by
    simp [Locals.Stmt.compile, hValueCompile, Locals.codeStmt, pointCtx]
  have hCoreBlock :
      Locals.Block.compileOpen targetCtx { stmts := [.let_ name value] } =
        some
          ([.code
              (valueCode ++
                Locals.bindLocals 0 (name :: targetCtx.layout))],
           pointCtx) := by
    simpa [Locals.Block.compileOpen] using hCoreCompile
  have hGenerated :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some
          ((.code
              (valueCode ++
                Locals.bindLocals 0 (name :: targetCtx.layout))) ::
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup]),
           pointCtx.withLayout transition.schedule.target) := by
    rw [hLowered]
    simpa using
      Locals.Block.compileOpen_append hCoreBlock artifact.compileEq
  have hPair := Option.some.inj (hCompile.symm.trans hGenerated)
  have hCodeEq := congrArg Prod.fst hPair
  have hCtxEq := congrArg Prod.snd hPair
  change
    headCode =
      (.code
          (valueCode ++
            Locals.bindLocals 0 (name :: targetCtx.layout))) ::
        (artifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.cleanup]) at hCodeEq
  change middleCtx =
    pointCtx.withLayout transition.schedule.target at hCtxEq
  refine ⟨by simpa [pointCtx] using hCtxEq, ?_, ?_⟩
  · rw [hCodeEq]
    simp [artifact.codes.code_length]
  · intro sourceCtx sourceFuel targetFuel suffix returns source target
      hFuel hCtx hInitial
    obtain ⟨_runtimeCode, runtimeArtifact, hRuntimeCompile, hRun⟩ :=
      compiledLetPoint sourceProgram targetProgram sourceCtx targetCtx
        sourceFuel targetFuel name value transition lowered hSource hFuel hCtx
        hFresh hScoped hSupported hAccess hLowered hInitial
    have hRuntimePair :=
      Option.some.inj (hCompile.symm.trans hRuntimeCompile)
    have hRuntimeCodeEq := congrArg Prod.fst hRuntimePair
    have hRuntimeCtxEq := congrArg Prod.snd hRuntimePair
    change
      headCode =
        (.code
            (_runtimeCode ++
              Locals.bindLocals 0 (name :: targetCtx.layout))) ::
          (runtimeArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code runtimeArtifact.cleanup]) at hRuntimeCodeEq
    change middleCtx =
      pointCtx.withLayout transition.schedule.target at hRuntimeCtxEq
    simpa [hRuntimeCodeEq, hRuntimeCtxEq, pointCtx] using hRun

theorem compiledAssignPointOfEquations
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx : Locals.Ctx)
    (name : Name) (value : Functions.Expr 1)
    (transition : AllocationLayout.Transition)
    (lowered : List Locals.Stmt) (headCode : List Expressions.Stmt)
    {sourceEnv : List Name}
    (hSource : targetCtx.layout = transition.source)
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Functions.Scope.ExprScoped sourceEnv value)
    (hSupported : Locals.InteractionSemantics.Expr.OpenSupported value)
    (hAccess : StackAccess.assign? targetCtx.layout name value = some ())
    (hLowered :
      lowered = [.assign name value] ++
        StackLowering.transitionStmts transition)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (headCode, middleCtx)) :
    middleCtx = targetCtx.withLayout transition.schedule.target ∧
      headCode.length = transition.schedule.promotions.length + 2 ∧
      ∀ (sourceCtx : Functions.Source.Ctx)
        (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source : Locals.Source.State} {target : Structured.RunState},
        transition.schedule.promotions.length + 2 < targetFuel →
        CtxCovers sourceCtx targetCtx →
        StateRel targetCtx.layout suffix returns source target →
        Simulation.Interaction.Rel
          (RegularOutcomeRel middleCtx suffix returns)
          (Functions.InteractionSemantics.Stmt.openRun
            sourceProgram sourceCtx sourceFuel (.assign name value) source)
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel { stmts := headCode } target) := by
  obtain ⟨depth, swap, hValueAccess, hDepth, hSwap⟩ :=
    StackAccess.assign_components hAccess
  obtain ⟨valueCode, hValueCompile⟩ :=
    StackAccessLowering.Expr.compileCode_of_check
      hValueAccess targetCtx rfl
  obtain ⟨artifact⟩ :=
    StackTransitionCompilation.Transition.compileArtifact transition hSource
  have hCoreCompile :
      Locals.Stmt.compile targetCtx (.assign name value) =
        some
          ([.code
              (valueCode ++ [.op swap, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)],
           targetCtx) := by
    simp [Locals.Stmt.compile, hDepth, hValueCompile, hSwap,
      Locals.codeStmt]
  have hCoreBlock :
      Locals.Block.compileOpen targetCtx { stmts := [.assign name value] } =
        some
          ([.code
              (valueCode ++ [.op swap, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)],
           targetCtx) := by
    simpa [Locals.Block.compileOpen] using hCoreCompile
  have hGenerated :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some
          ((.code
              (valueCode ++ [.op swap, .op .pop] ++
                Locals.bindLocals 0 targetCtx.layout)) ::
            (artifact.promotionCodes.map Expressions.Stmt.code ++
              [Expressions.Stmt.code artifact.cleanup]),
           targetCtx.withLayout transition.schedule.target) := by
    rw [hLowered]
    simpa using
      Locals.Block.compileOpen_append hCoreBlock artifact.compileEq
  have hPair := Option.some.inj (hCompile.symm.trans hGenerated)
  have hCodeEq := congrArg Prod.fst hPair
  have hCtxEq := congrArg Prod.snd hPair
  change
    headCode =
      (.code
          (valueCode ++ [.op swap, .op .pop] ++
            Locals.bindLocals 0 targetCtx.layout)) ::
        (artifact.promotionCodes.map Expressions.Stmt.code ++
          [Expressions.Stmt.code artifact.cleanup]) at hCodeEq
  change middleCtx =
    targetCtx.withLayout transition.schedule.target at hCtxEq
  refine ⟨hCtxEq, ?_, ?_⟩
  · rw [hCodeEq]
    simp [artifact.codes.code_length]
  · intro sourceCtx sourceFuel targetFuel suffix returns source target
      hFuel hCtx hInitial
    obtain
        ⟨_runtimeValueCode, _runtimeSwap, runtimeArtifact,
          hRuntimeCompile, hRun⟩ :=
      compiledAssignPoint sourceProgram targetProgram sourceCtx targetCtx
        sourceFuel targetFuel name value transition lowered hSource hFuel hCtx
        hNodup hScoped hSupported hAccess hLowered hInitial
    have hRuntimePair :=
      Option.some.inj (hCompile.symm.trans hRuntimeCompile)
    have hRuntimeCodeEq := congrArg Prod.fst hRuntimePair
    have hRuntimeCtxEq := congrArg Prod.snd hRuntimePair
    change
      headCode =
        (.code
            (_runtimeValueCode ++ [.op _runtimeSwap, .op .pop] ++
              Locals.bindLocals 0 targetCtx.layout)) ::
          (runtimeArtifact.promotionCodes.map Expressions.Stmt.code ++
            [Expressions.Stmt.code runtimeArtifact.cleanup]) at hRuntimeCodeEq
    change middleCtx =
      targetCtx.withLayout transition.schedule.target at hRuntimeCtxEq
    simpa [hRuntimeCodeEq, hRuntimeCtxEq] using hRun

end StackStatementPreservation
end Functions
end EvmCompiler
