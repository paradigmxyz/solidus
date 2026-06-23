import EvmCompiler.Yul.FunctionsInteractionPreparedArgsMode
import EvmCompiler.Yul.FunctionsInteractionArityMode
import EvmCompiler.Yul.FunctionsInteractionPreparedCondition

/-!
Mode-parametric prepared-condition preservation. The target result shape and
compiler lowering artifacts are shared with the ordinary adjacent pass; only
the canonical primitive handler is selected by `Mode`.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedConditionMode

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionMode

abbrev TargetResult := FunctionsInteractionPreparedCondition.TargetResult

noncomputable def run (mode : Mode)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (target : Functions.InteractionSemantics.State) :
    Simulation.Interaction EVMException TargetResult :=
  Simulation.Interaction.bind
    (Target.Block.openRun mode program ctx targetFuel
      { stmts := pre } target)
    fun result =>
      match result.1.mode with
      | .regular =>
          Simulation.Interaction.map
            (fun evaluated =>
              FunctionsInteractionPreparedCondition.TargetResult.value
                evaluated.1 evaluated.2
                (evaluated.2 != EvmYul.UInt256.ofNat 0) result.2)
            (Target.Expr.openEvalOne mode lower result.1.state)
      | .brk | .cont | .leave | .halt _ =>
          pure (.terminal result.1 result.2)

theorem run_let (mode : Mode)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (name : Functions.Name) (valueExpr : Locals.Expr 1)
    (target : Functions.InteractionSemantics.State)
    (hFuel : pre.length + 1 < targetFuel) :
    Target.Block.openRun mode program ctx targetFuel
        { stmts := pre ++ [.let_ name valueExpr] } target =
      Simulation.Interaction.bind
        (run mode program ctx targetFuel pre valueExpr target)
        (fun result =>
          match result with
          | .value state value _truth ctxAfter =>
              pure
                (Functions.Source.Effectful.Outcome.regular
                  (state.insert name value),
                  { ctxAfter with scope := name :: ctxAfter.scope })
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  rw [Target.Block.openRun_append]
  unfold run
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre } target))
  intro result _hResult
  cases hMode : result.1.mode with
  | regular =>
      simp only [hMode]
      obtain ⟨remaining, hResidual⟩ :
          ∃ remaining, targetFuel - pre.length = remaining + 2 := by
        refine ⟨targetFuel - pre.length - 2, ?_⟩
        omega
      rw [hResidual,
        show remaining + 2 = (remaining + 1) + 1 by omega,
        Target.Block.openRun_cons]
      change
        Simulation.Interaction.bind
            (Target.Stmt.openRun mode program result.2 (remaining + 1)
              (.let_ name valueExpr) result.1.state)
            _ = _
      rw [Target.Stmt.openRun_let]
      rw [Target.Expr.openEvalOne_eq_bind]
      unfold Simulation.Interaction.map
      conv_lhs => rw [Simulation.Interaction.bind_assoc]
      conv_rhs => rw [Simulation.Interaction.bind_assoc,
        Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Target.Expr.openEval mode valueExpr result.1.state))
      intro evaluated _hEvaluated
      cases hValues : evaluated.2 with
      | nil => rfl
      | cons value rest =>
          cases rest with
          | nil =>
              simp only [Simulation.Interaction.bind_done_ok,
                Simulation.Interaction.monad_pure_bind]
              change
                Target.Block.openRun mode program
                    { result.2 with scope := name :: result.2.scope }
                    (remaining + 1) { stmts := [] }
                    (evaluated.1.insert name value) = _
              rw [Target.Block.openRun_nil]
              rfl
          | cons next tail => rfl
  | brk | cont | leave | halt =>
      simp only [hMode]
      rfl

theorem run_assign_nil (mode : Mode)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (name : Functions.Name)
    (valueExpr : Locals.Expr 1)
    (target : Functions.InteractionSemantics.State)
    (hFuel : 1 < targetFuel)
    (hContains : target.vars.contains name = true) :
    Target.Block.openRun mode program ctx targetFuel
        { stmts := [.assign name valueExpr] } target =
      Simulation.Interaction.bind
        (run mode program ctx targetFuel [] valueExpr target)
        (fun result =>
          match result with
          | .value state value _truth ctxAfter =>
              pure
                (Functions.Source.Effectful.Outcome.regular
                  (state.insert name value), ctxAfter)
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  obtain ⟨remaining, rfl⟩ : ∃ remaining, targetFuel = remaining + 2 :=
    ⟨targetFuel - 2, by omega⟩
  have hRun :
      run mode program ctx (remaining + 2) [] valueExpr target =
        Simulation.Interaction.map
          (fun evaluated =>
            FunctionsInteractionPreparedCondition.TargetResult.value
              evaluated.1 evaluated.2
              (evaluated.2 != EvmYul.UInt256.ofNat 0) ctx)
          (Target.Expr.openEvalOne mode valueExpr target) := by
    unfold run
    rw [Target.Block.openRun_nil]
    rfl
  rw [hRun]
  rw [show remaining + 2 = (remaining + 1) + 1 by omega,
    Target.Block.openRun_cons]
  change
    Simulation.Interaction.bind
        (Target.Stmt.openRun mode program ctx (remaining + 1)
          (.assign name valueExpr) target)
        _ = _
  rw [Target.Stmt.openRun_assign_of_contains
    mode program ctx (remaining + 1) name valueExpr target hContains]
  unfold Simulation.Interaction.map
  conv_lhs => rw [Simulation.Interaction.bind_assoc]
  conv_rhs => rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Target.Expr.openEvalOne mode valueExpr target))
  intro evaluated _hEvaluated
  simp only [Simulation.Interaction.bind_done_ok,
    Simulation.Interaction.monad_pure_bind]
  change
    Target.Block.openRun mode program ctx (remaining + 1)
        { stmts := [] } (evaluated.1.insert name evaluated.2) = _
  rw [Target.Block.openRun_nil]
  rfl

theorem run_if (mode : Mode)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (cond : Locals.Expr 1) (body : Functions.Block)
    (target : Functions.InteractionSemantics.State)
    (hFuel : pre.length + 1 < targetFuel) :
    Target.Block.openRun mode program ctx targetFuel
        { stmts := pre ++ [.if_ cond body] } target =
      Simulation.Interaction.bind
        (run mode program ctx targetFuel pre cond target)
        (fun result =>
          match result with
          | .value state _value truth ctxAfter =>
              if truth then
                Target.Stmt.openRun mode program ctxAfter
                  (targetFuel - pre.length - 2) (.block body) state
              else
                pure
                  (Functions.Source.Effectful.Outcome.regular state,
                    ctxAfter)
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  rw [Target.Block.openRun_append]
  unfold run
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre } target))
  intro result _hResult
  cases hMode : result.1.mode with
  | regular =>
      simp only [hMode]
      obtain ⟨remaining, hResidual⟩ :
          ∃ remaining, targetFuel - pre.length = remaining + 2 := by
        refine ⟨targetFuel - pre.length - 2, ?_⟩
        omega
      rw [hResidual,
        show remaining + 2 = (remaining + 1) + 1 by omega,
        Target.Block.openRun_cons]
      change
        Simulation.Interaction.bind
            (Target.Stmt.openRun mode program result.2 (remaining + 1)
              (.if_ cond body) result.1.state)
            _ = _
      rw [Target.Stmt.openRun_if,
        Simulation.Interaction.bind_assoc]
      rw [Target.Expr.openEvalCondition_eq_map_openEvalOne]
      unfold Simulation.Interaction.map
      rw [Simulation.Interaction.bind_assoc,
        Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Target.Expr.openEvalOne mode cond result.1.state))
      intro evaluated _hEvaluated
      cases hTruth : evaluated.2 != EvmYul.UInt256.ofNat 0 with
      | false =>
          simp only [hTruth, Bool.false_eq_true, ↓reduceIte,
            Simulation.Interaction.bind_done_ok,
            Simulation.Interaction.monad_pure_bind]
          change
            Target.Block.openRun mode program result.2 (remaining + 1)
                { stmts := [] } evaluated.1 = _
          rw [Target.Block.openRun_nil]
          rfl
      | true =>
          simp only [hTruth, ↓reduceIte,
            Simulation.Interaction.monad_pure_bind]
          rw [show remaining + 1 + 1 - 2 = remaining by omega]
          change
            Simulation.Interaction.bind
                (Target.Stmt.openRun mode program result.2 remaining
                  (.block body) evaluated.1)
                _ =
              Target.Stmt.openRun mode program result.2 remaining
                (.block body) evaluated.1
          rw [Target.Stmt.openRun_block,
            Simulation.Interaction.bind_assoc]
          apply Simulation.Interaction.AllDone.bind_congr
            (Simulation.Interaction.AllDone.trivial
              (Target.Block.openRun mode program result.2 remaining
                body evaluated.1))
          intro bodyResult _hBody
          cases hBodyMode : bodyResult.1.mode with
          | regular =>
              simp only [hBodyMode]
              change
                Simulation.Interaction.bind
                    (.done (.ok
                      (Functions.Source.Effectful.Outcome.regular
                        (Functions.InteractionSemantics.stateModel.restrictTo
                          result.2.scope bodyResult.1.state), result.2))) _ =
                  .done (.ok
                    (Functions.Source.Effectful.Outcome.regular
                      (Functions.InteractionSemantics.stateModel.restrictTo
                        result.2.scope bodyResult.1.state), result.2))
              rw [Simulation.Interaction.bind_done_ok]
              rw [Target.Block.openRun_nil]
              change
                Simulation.Interaction.pure
                    (Functions.Source.Effectful.Outcome.regular
                      (Functions.InteractionSemantics.stateModel.restrictTo
                        result.2.scope bodyResult.1.state), result.2) =
                  .done (.ok
                    (Functions.Source.Effectful.Outcome.regular
                      (Functions.InteractionSemantics.stateModel.restrictTo
                        result.2.scope bodyResult.1.state), result.2))
              rfl
          | brk | cont | leave | halt =>
              simp only [hBodyMode]
              change
                Simulation.Interaction.bind
                    (.done (.ok (bodyResult.1, result.2))) _ =
                  .done (.ok (bodyResult.1, result.2))
              rw [Simulation.Interaction.bind_done_ok]
              simp [hBodyMode, Simulation.Interaction.pure]
  | brk | cont | leave | halt =>
      simp only [hMode]
      rfl

theorem run_switch (mode : Mode)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (scrutinee : Locals.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (target : Functions.InteractionSemantics.State)
    (hFuel : pre.length + 1 < targetFuel) :
    Target.Block.openRun mode program ctx targetFuel
        { stmts := pre ++ [.switch scrutinee cases defaultBody] } target =
      Simulation.Interaction.bind
        (run mode program ctx targetFuel pre scrutinee target)
        (fun result =>
          match result with
          | .value state value _truth ctxAfter =>
              match Functions.Source.Switch.select value cases defaultBody with
              | some body =>
                  Target.Stmt.openRun mode program ctxAfter
                    (targetFuel - pre.length - 2) (.block body) state
              | none =>
                  pure
                    (Functions.Source.Effectful.Outcome.regular state,
                      ctxAfter)
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  rw [Target.Block.openRun_append]
  unfold run
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre } target))
  intro result _hResult
  cases hMode : result.1.mode with
  | regular =>
      simp only [hMode]
      obtain ⟨remaining, hResidual⟩ :
          ∃ remaining, targetFuel - pre.length = remaining + 2 := by
        refine ⟨targetFuel - pre.length - 2, ?_⟩
        omega
      rw [hResidual,
        show remaining + 2 = (remaining + 1) + 1 by omega,
        Target.Block.openRun_cons]
      change
        Simulation.Interaction.bind
            (Target.Stmt.openRun mode program result.2 (remaining + 1)
              (.switch scrutinee cases defaultBody) result.1.state)
            _ = _
      rw [Target.Stmt.openRun_switch,
        Simulation.Interaction.bind_assoc]
      unfold Simulation.Interaction.map
      rw [Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Target.Expr.openEvalOne mode scrutinee result.1.state))
      intro evaluated _hEvaluated
      cases hSelected :
          Functions.Source.Switch.select evaluated.2 cases defaultBody with
      | none =>
          simp only [hSelected]
          dsimp only [Simulation.Interaction.pure,
            Simulation.Interaction.bind]
          rw [hSelected]
          change
            Target.Block.openRun mode program result.2 (remaining + 1)
                { stmts := [] } evaluated.1 = _
          rw [Target.Block.openRun_nil]
      | some selectedBody =>
          simp only [hSelected]
          dsimp only [Simulation.Interaction.pure,
            Simulation.Interaction.bind]
          rw [hSelected]
          rw [show remaining + 1 + 1 - 2 = remaining by omega]
          change
            Simulation.Interaction.bind
                (Target.Stmt.openRun mode program result.2 remaining
                  (.block selectedBody) evaluated.1)
                _ =
              Target.Stmt.openRun mode program result.2 remaining
                (.block selectedBody) evaluated.1
          rw [Target.Stmt.openRun_block,
            Simulation.Interaction.bind_assoc]
          apply Simulation.Interaction.AllDone.bind_congr
            (Simulation.Interaction.AllDone.trivial
              (Target.Block.openRun mode program result.2 remaining
                selectedBody evaluated.1))
          intro bodyResult _hBody
          cases hBodyMode : bodyResult.1.mode with
          | regular =>
              simp only [hBodyMode]
              change
                Simulation.Interaction.bind
                    (.done (.ok
                      (Functions.Source.Effectful.Outcome.regular
                        (Functions.InteractionSemantics.stateModel.restrictTo
                          result.2.scope bodyResult.1.state), result.2))) _ =
                  .done (.ok
                    (Functions.Source.Effectful.Outcome.regular
                      (Functions.InteractionSemantics.stateModel.restrictTo
                        result.2.scope bodyResult.1.state), result.2))
              rw [Simulation.Interaction.bind_done_ok]
              rw [Target.Block.openRun_nil]
              change
                Simulation.Interaction.pure
                    (Functions.Source.Effectful.Outcome.regular
                      (Functions.InteractionSemantics.stateModel.restrictTo
                        result.2.scope bodyResult.1.state), result.2) =
                  .done (.ok
                    (Functions.Source.Effectful.Outcome.regular
                      (Functions.InteractionSemantics.stateModel.restrictTo
                        result.2.scope bodyResult.1.state), result.2))
              rfl
          | brk | cont | leave | halt =>
              simp only [hBodyMode]
              change
                Simulation.Interaction.bind
                    (.done (.ok (bodyResult.1, result.2))) _ =
                  .done (.ok (bodyResult.1, result.2))
              rw [Simulation.Interaction.bind_done_ok]
              simp [hBodyMode, Simulation.Interaction.pure]
  | brk | cont | leave | halt =>
      simp only [hMode]
      rfl

theorem run_forGuard (mode : Mode)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (cond : Locals.Expr 1) (rest : List Functions.Stmt)
    (target : Functions.InteractionSemantics.State)
    (hFuel : pre.length + 1 < targetFuel) :
    Target.Block.openRun mode program ctx targetFuel
        { stmts :=
            pre ++
              .if_
                (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                { stmts := [.brk] } ::
              rest } target =
      Simulation.Interaction.bind
        (run mode program ctx targetFuel pre cond target)
        (fun result =>
          match result with
          | .value state value _truth ctxAfter =>
              if value = EvmYul.UInt256.ofNat 0 then
                Simulation.Interaction.bind
                  (Target.Stmt.openRun mode program ctxAfter
                    (targetFuel - pre.length - 2)
                    (.block { stmts := [.brk] }) state)
                  (fun guardResult =>
                    match guardResult.1.mode with
                    | .regular =>
                        Target.Block.openRun mode program guardResult.2
                          (targetFuel - pre.length - 1)
                          { stmts := rest } guardResult.1.state
                    | .brk | .cont | .leave | .halt _ =>
                        pure (guardResult.1, ctxAfter))
              else
                Target.Block.openRun mode program ctxAfter
                  (targetFuel - pre.length - 1)
                  { stmts := rest } state
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  rw [Target.Block.openRun_append]
  unfold run
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Target.Block.openRun mode program ctx targetFuel
        { stmts := pre } target))
  intro result _hResult
  cases hMode : result.1.mode with
  | regular =>
      simp only [hMode]
      obtain ⟨remaining, hResidual⟩ :
          ∃ remaining, targetFuel - pre.length = remaining + 2 := by
        refine ⟨targetFuel - pre.length - 2, ?_⟩
        omega
      rw [hResidual,
        show remaining + 2 = (remaining + 1) + 1 by omega,
        Target.Block.openRun_cons]
      change
        Simulation.Interaction.bind
            (Target.Stmt.openRun mode program result.2 (remaining + 1)
              (.if_
                (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                { stmts := [.brk] })
              result.1.state)
            _ = _
      rw [Target.Stmt.openRun_if,
        Simulation.Interaction.bind_assoc,
        FunctionsInteractionArityMode.Expr.openEvalCondition_iszero_eq_map_openEvalOne]
      unfold Simulation.Interaction.map
      rw [Simulation.Interaction.bind_assoc,
        Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Target.Expr.openEvalOne mode cond result.1.state))
      intro evaluated _hEvaluated
      rcases evaluated with ⟨evaluatedState, evaluatedValue⟩
      by_cases hZero : evaluatedValue = EvmYul.UInt256.ofNat 0
      · have hEqZero :
            (evaluatedValue == EvmYul.UInt256.ofNat 0) = true := by
          have hValue : evaluatedValue.val = 0 := by
            have hCongruence := congrArg EvmYul.UInt256.val hZero
            simpa [EvmYul.UInt256.ofNat, Id.run] using hCongruence
          simpa [EvmYul.instBEqUInt256,
            EvmYul.instBEqUInt256.beq,
            EvmYul.UInt256.ofNat, Id.run] using hValue
        simp only [Simulation.Interaction.pure,
          Simulation.Interaction.bind]
        rw [hEqZero, if_pos hZero]
        simp only [↓reduceIte,
          Simulation.Interaction.bind_done_ok,
          Simulation.Interaction.monad_pure_bind,
          Simulation.Interaction.pure, Simulation.Interaction.bind]
        rw [show remaining + 1 + 1 - 2 = remaining by omega,
          show remaining + 1 + 1 - 1 = remaining + 1 by omega]
        rfl
      · have hEqZero :
            (evaluatedValue == EvmYul.UInt256.ofNat 0) = false := by
          have hValue : evaluatedValue.val ≠ 0 := by
            intro hValue
            apply hZero
            cases evaluatedValue with
            | mk value =>
                change value = 0 at hValue
                change EvmYul.UInt256.mk value = EvmYul.UInt256.mk 0
                exact congrArg EvmYul.UInt256.mk hValue
          simpa [EvmYul.instBEqUInt256,
            EvmYul.instBEqUInt256.beq,
            EvmYul.UInt256.ofNat, Id.run] using hValue
        simp only [Simulation.Interaction.pure,
          Simulation.Interaction.bind]
        rw [hEqZero, if_neg hZero]
        simp only [Bool.false_eq_true, ↓reduceIte,
          Simulation.Interaction.bind_done_ok,
          Simulation.Interaction.monad_pure_bind,
          Simulation.Interaction.pure, Simulation.Interaction.bind,
          Functions.Source.Effectful.Outcome.regular_mode]
        rw [show remaining + 1 + 1 - 1 = remaining + 1 by omega]
        rfl
  | brk | cont | leave | halt =>
      simp only [hMode]
      rfl

abbrev DoneRel := FunctionsInteractionPreparedCondition.DoneRel

theorem ofStablePrepared
    {mode : Mode} {sourceFuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {final : Fresh.State}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgsMode.DoneRel
          mode layout final [lower] target ctx)
        (Source.evalValues mode sourceFuel expr codeOverride source)
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final.used ctx)
      (Source.evalValues mode sourceFuel expr codeOverride source)
      (run mode program ctx targetFuel pre lower target) := by
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout final.used ctx)
        (Simulation.Interaction.bind
          (Source.evalValues mode sourceFuel expr codeOverride source) pure)
        (run mode program ctx targetFuel pre lower target) := by
    unfold run
    apply Simulation.Interaction.ForwardRel.bind_custom hPrepared
    intro sourceDone targetDone hDone
    cases hDone with
    | error hError =>
        exact Simulation.Interaction.ForwardRel.done (.error hError)
    | terminal hTerminal =>
        cases hTerminal with
        | stop hState =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal (.stop hState))
        | return_ hState =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal (.return_ hState))
        | selfdestruct hState =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal (.selfdestruct hState))
        | revert hState =>
            exact Simulation.Interaction.ForwardRel.done
              (.terminal (.revert hState))
    | @regular sourceAfter values targetAfter ctxAfter
        hStable hScoped hDomain _hExtends hScope hControl hTargetScope =>
        have hLength : values.length = 1 := by
          simpa using hStable.length
        obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp hLength
        cases hStable with
        | cons hValue _hNil =>
            have hEval := hValue targetAfter
              (TargetExtends.refl targetAfter.vars)
            have hOne :
                Target.Expr.openEvalOne mode lower targetAfter =
                  .done (.ok (targetAfter, value)) := by
              rw [Target.Expr.openEvalOne_eq_bind, hEval]
              rfl
            simp only [Simulation.Interaction.bind_done_ok,
              Functions.Source.Effectful.Outcome.regular_mode]
            change
              Simulation.Interaction.ForwardRel Truncated
                (DoneRel layout final.used ctx)
                (pure (sourceAfter, [value]))
                (Simulation.Interaction.map
                  (fun evaluated =>
                    FunctionsInteractionPreparedCondition.TargetResult.value
                      evaluated.1 evaluated.2
                      (evaluated.2 != EvmYul.UInt256.ofNat 0) ctxAfter)
                  (Target.Expr.openEvalOne mode lower targetAfter))
            rw [hOne]
            simp only [Simulation.Interaction.map,
              Simulation.Interaction.bind_done_ok,
              Simulation.Interaction.monad_pure_bind]
            exact Simulation.Interaction.ForwardRel.done
              (.regular rfl rfl hScoped hDomain hScope hControl hTargetScope)
  have hSourceBind :
      Simulation.Interaction.bind
          (Source.evalValues mode sourceFuel expr codeOverride source) pure =
        Source.evalValues mode sourceFuel expr codeOverride source :=
    Simulation.Interaction.bind_pure _
  rw [hSourceBind] at hBound
  exact hBound

theorem ofOpenExpression
    {mode : Mode} {lower : Locals.Expr 1}
    {used layout : List Functions.Name}
    {sourceEntry : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    {sourceOpen : Yul.InteractionSemantics.Open
      (Yul.InteractionSemantics.State × List Word)}
    (hScoped : ScopedStateRel layout sourceEntry target)
    (hDomain : TargetDomainWithin used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin used ctx)
    (hEval :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpressionMode.DoneRel sourceEntry 1)
        sourceOpen (Target.Expr.openEval mode lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout used ctx) sourceOpen
      (Simulation.Interaction.map
        (fun evaluated =>
          FunctionsInteractionPreparedCondition.TargetResult.value
            evaluated.1 evaluated.2
            (evaluated.2 != EvmYul.UInt256.ofNat 0) ctx)
        (Target.Expr.openEvalOne mode lower target)) := by
  unfold Simulation.Interaction.map
  rw [Target.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc]
  have hEvalVars := hEval.strengthen_right
    (Target.Expr.openEval_vars_eq mode lower target)
  apply Simulation.Interaction.ForwardRel.bind_right hEvalVars
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hDone, hTargetVars⟩
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | @ok sourceResult targetResult hResult =>
      have hLength := hResult.2.2.1
      obtain ⟨value, hSourceValues⟩ :=
        List.length_eq_one_iff.mp hLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hResult.2.1, hSourceValues]
      simp only [Simulation.Interaction.bind_done_ok]
      rw [hTargetValues]
      simp only [Simulation.Interaction.bind_done_ok,
        Simulation.Interaction.monad_pure_bind]
      have hFinalScoped := ScopedStateRel.of_state_store_eq
        hScoped hResult.1 hResult.2.2.2
      have hTargetVarsEq : targetResult.1.vars = target.vars := by
        simpa using hTargetVars
      have hFinalDomain : TargetDomainWithin used targetResult.1.vars := by
        rw [hTargetVarsEq]
        exact hDomain
      exact Simulation.Interaction.ForwardRel.done
        (.regular hSourceValues rfl hFinalScoped hFinalDomain
          (Functions.Source.Ctx.ScopeExtends.refl ctx)
          (Functions.Source.Ctx.SameControl.refl ctx)
          hTargetScope)

theorem ofDirectExpression
    {mode : Mode} {sourceFuel targetFuel : Nat}
    {expr : AstExpr} {lower : Locals.Expr 1}
    {before after : Fresh.State} {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hTargetFuel : 0 < targetFuel)
    (hExtends : Fresh.Extends before after)
    (hScoped : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx)
    (hEval :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionExpressionMode.DoneRel source 1)
        (Source.evalValues mode sourceFuel expr codeOverride source)
        (Target.Expr.openEval mode lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout after.used ctx)
      (Source.evalValues mode sourceFuel expr codeOverride source)
      (run mode program ctx targetFuel [] lower target) := by
  obtain ⟨remaining, rfl⟩ : ∃ remaining, targetFuel = remaining + 1 :=
    ⟨targetFuel - 1, by omega⟩
  unfold run
  rw [Target.Block.openRun_nil]
  exact ofOpenExpression hScoped (hDomain.mono hExtends)
    (hTargetScope.mono hExtends) hEval

theorem ofDirectPrimitiveLowering
    {mode : Mode} (hPrimitive : CompilerSelected mode)
    {argsFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {lower : Locals.Expr 1} {before : Fresh.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLowering : Expr.UncheckedDirectPrimitiveLowering
      before prim args lower)
    (hTargetFuel : 0 < targetFuel)
    (hScoped : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope :
      FunctionsInteractionControlRelation.TargetScopeWithin before.used ctx) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout before.used ctx)
      (Source.evalValues mode (argsFuel + 1)
        (.Call (.inl prim) args) codeOverride source)
      (run mode program ctx targetFuel [] lower target) := by
  cases hLowering with
  | @primitive op lowerArgs seq hOp hArgs hSeq hOutputs =>
      have hLowerReverse :
          Expr.List.toLocals1? args.reverse = some lowerArgs.reverse :=
        Expr.List.toLocals1?_reverse hArgs
      have hDirectSeq :
          Expr.List.toSeq? lowerArgs.reverse
              (Expressions.Structured.BasicOp.inputs op) = some seq := by
        simpa [Expr.List.toStackSeq?] using hSeq
      have hArgsRel :=
        (FunctionsInteractionExpressionMode.compilerDirectAt
          mode codeOverride argsFuel).evalArgs
          hLowerReverse hDirectSeq hScoped.state
      have hPrimitiveRel :=
        FunctionsInteractionExpressionMode.Expr.primitive_of_args
          mode hPrimitive (primitiveFuel := argsFuel)
          hOp hOutputs hArgsRel
      have hEval :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionExpressionMode.DoneRel source 1)
            (Source.evalValues mode (argsFuel + 1)
              (.Call (.inl prim) args) codeOverride source)
            (Target.Expr.openEval mode
              (Expr.cast hOutputs (.prim op seq)) target) := by
        rw [FunctionsInteractionExpressionMode.expr_openEval_cast]
        simpa [Source.evalValues, Yul.Source.Canonical.evalValues,
          Yul.Source.Effectful.evalValues,
          Target.Expr.openEval,
          Locals.Source.Effectful.Expr.Control.eval,
          FunctionsInteractionExpressionMode.exprSeq_openEval_seqCast] using
          hPrimitiveRel
      exact ofDirectExpression hTargetFuel (Fresh.Extends.refl before)
        hScoped hDomain hTargetScope hEval

theorem ofPreparedPrimitive
    {mode : Mode} (hPrimitive : CompilerSelected mode)
    {argsFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {op : Structured.BasicOp}
    {pre : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    {final : Fresh.State}
    {entry : Functions.InteractionSemantics.State}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hSeq : Expr.List.toStackSeq? lowerArgs
      (Expressions.Structured.BasicOp.inputs op) = some seq)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 1)
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgsMode.DoneRel
          mode layout final lowerArgs.reverse entry ctx)
        (Source.evalArgs mode argsFuel args.reverse codeOverride source)
        (Target.Block.openRun mode program ctx targetFuel
          { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final.used ctx)
      (Source.evalValues mode (argsFuel + 1)
        (.Call (.inl prim) args) codeOverride source)
      (run mode program ctx targetFuel pre
        (Expr.cast hOutputs (.prim op seq)) target) := by
  unfold Source.evalValues Yul.Source.Canonical.evalValues
    Yul.Source.Effectful.evalValues
  unfold run
  apply Simulation.Interaction.ForwardRel.bind_custom hPrepared
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.revert hState))
  | @regular sourceAfter values targetAfter ctxAfter
      hStable hScoped hDomain _hExtends hScope hControl hTargetScope =>
      have hDirectSeq :
          Expr.List.toSeq? lowerArgs.reverse
              (Expressions.Structured.BasicOp.inputs op) = some seq := by
        simpa [Expr.List.toStackSeq?] using hSeq
      have hLength :
          values.length = Expressions.Structured.BasicOp.inputs op :=
        hStable.length.trans (Expr.List.toSeq?_length hDirectSeq)
      have hSeqEval := hStable.exprSeq_openEval hDirectSeq
        (TargetExtends.refl targetAfter.vars)
      have hArgsDone :
          FunctionsInteractionExpressionMode.DoneRel sourceAfter
              (Expressions.Structured.BasicOp.inputs op)
              (.ok (sourceAfter, values)) (.ok (targetAfter, values)) :=
        .ok (FunctionsInteractionExpression.ResultRel.of_state
          hScoped.state hLength)
      have hArgsRel :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionExpressionMode.DoneRel sourceAfter
              (Expressions.Structured.BasicOp.inputs op))
            (pure (sourceAfter, values))
            (Target.ExprSeq.openEval mode seq targetAfter) := by
        rw [hSeqEval]
        exact Simulation.Interaction.ForwardRel.done hArgsDone
      have hExprRelRaw :=
        FunctionsInteractionExpressionMode.Expr.primitive_of_args
          mode hPrimitive (primitiveFuel := argsFuel)
          hOp hOutputs hArgsRel
      have hExprRel :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionExpressionMode.DoneRel sourceAfter 1)
            ((sourcePrimitive mode).eval
              argsFuel sourceAfter prim values.reverse)
            (Target.Expr.openEval mode
              (Expr.cast hOutputs (.prim op seq)) targetAfter) := by
        rw [FunctionsInteractionExpressionMode.expr_openEval_cast]
        simpa [Target.Expr.openEval,
          Locals.Source.Effectful.Expr.Control.eval] using hExprRelRaw
      have hCondition := ofOpenExpression
        (ctx := ctxAfter) hScoped hDomain hTargetScope hExprRel
      exact Simulation.Interaction.ForwardRel.mono hCondition
        (fun _sourceDone _targetDone conditionDone =>
          FunctionsInteractionPreparedCondition.DoneRel.transport_entry
            hScope hControl conditionDone)

end FunctionsInteractionPreparedConditionMode
end Yul
end EvmCompiler
