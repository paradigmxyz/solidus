import EvmCompiler.Yul.FunctionsInteractionPreparedArgs
import EvmCompiler.Functions.InteractionArity

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionPreparedCondition

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation

inductive TargetResult where
  | value (state : Functions.InteractionSemantics.State)
      (value : Word) (truth : Bool) (ctx : Functions.Source.Ctx)
  | terminal (outcome : Functions.InteractionSemantics.Outcome)
      (ctx : Functions.Source.Ctx)

/-- Execute the ordinary generated prelude and then the selected one-result
condition expression. A terminal internal call in the prelude remains an
outcome and skips condition evaluation. -/
def run
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (lower : Locals.Expr 1)
    (target : Functions.InteractionSemantics.State) :
    Simulation.Interaction EVMException TargetResult :=
  Simulation.Interaction.bind
    (Functions.InteractionSemantics.Block.openRun
      program ctx targetFuel { stmts := pre } target)
    fun result =>
      match result.1.mode with
      | .regular =>
          Simulation.Interaction.map
            (fun evaluated => TargetResult.value evaluated.1 evaluated.2
              (evaluated.2 != EvmYul.UInt256.ofNat 0) result.2)
            (Functions.InteractionSemantics.Expr.openEvalOne
              lower result.1.state)
      | .brk | .cont | .leave | .halt _ =>
          pure (.terminal result.1 result.2)

/-- A generated prelude followed by a one-result declaration factors through
the same exact-value prepared computation used by conditions. -/
theorem run_let
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (name : Functions.Name) (valueExpr : Locals.Expr 1)
    (target : Functions.InteractionSemantics.State)
    (hFuel : pre.length + 1 < targetFuel) :
    Functions.InteractionSemantics.Block.openRun program ctx targetFuel
        { stmts := pre ++ [.let_ name valueExpr] } target =
      Simulation.Interaction.bind
        (run program ctx targetFuel pre valueExpr target)
        (fun result =>
          match result with
          | .value state value _truth ctxAfter =>
              pure
                (Functions.Source.Effectful.Outcome.regular
                  (state.insert name value),
                  { ctxAfter with scope := name :: ctxAfter.scope })
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  rw [Functions.InteractionSemantics.Block.openRun_append]
  unfold run
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel { stmts := pre } target))
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
        Functions.InteractionSemantics.Block.openRun_cons]
      change
        Simulation.Interaction.bind
            (Functions.InteractionSemantics.Stmt.openRun
              program result.2 (remaining + 1)
              (.let_ name valueExpr) result.1.state)
            _ = _
      rw [Functions.InteractionSemantics.Stmt.openRun_let]
      unfold Functions.InteractionSemantics.Expr.openEvalOne
      rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind]
      unfold Simulation.Interaction.map
      conv_lhs => rw [Simulation.Interaction.bind_assoc]
      conv_rhs => rw [Simulation.Interaction.bind_assoc,
        Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Functions.InteractionSemantics.Expr.openEval
            valueExpr result.1.state))
      intro evaluated _hEvaluated
      cases hValues : evaluated.2 with
      | nil => rfl
      | cons value rest =>
          cases rest with
          | nil =>
              simp only [Simulation.Interaction.bind_done_ok,
                Simulation.Interaction.monad_pure_bind]
              change
                Functions.InteractionSemantics.Block.openRun
                    program { result.2 with scope := name :: result.2.scope }
                    (remaining + 1) { stmts := [] }
                    (evaluated.1.insert name value) = _
              rw [Functions.InteractionSemantics.Block.openRun_nil]
              rfl
          | cons next tail => rfl
  | brk | cont | leave | halt =>
      simp only [hMode]
      rfl

/-- With no generated prelude, a visible assignment factors through the same
exact-value computation. The destination check remains before expression
evaluation, justified by the source/target scope relation at statement entry. -/
theorem run_assign_nil
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (name : Functions.Name)
    (valueExpr : Locals.Expr 1)
    (target : Functions.InteractionSemantics.State)
    (hFuel : 1 < targetFuel)
    (hContains : target.vars.contains name = true) :
    Functions.InteractionSemantics.Block.openRun program ctx targetFuel
        { stmts := [.assign name valueExpr] } target =
      Simulation.Interaction.bind
        (run program ctx targetFuel [] valueExpr target)
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
      run program ctx (remaining + 2) [] valueExpr target =
        Simulation.Interaction.map
          (fun evaluated => TargetResult.value evaluated.1 evaluated.2
            (evaluated.2 != EvmYul.UInt256.ofNat 0) ctx)
          (Functions.InteractionSemantics.Expr.openEvalOne valueExpr target) := by
    unfold run
    rw [Functions.InteractionSemantics.Block.openRun_nil]
    rfl
  rw [hRun]
  rw [show remaining + 2 = (remaining + 1) + 1 by omega,
    Functions.InteractionSemantics.Block.openRun_cons]
  change
    Simulation.Interaction.bind
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx (remaining + 1) (.assign name valueExpr) target)
        _ = _
  rw [Functions.InteractionSemantics.Stmt.openRun_assign
    program ctx (remaining + 1) name valueExpr target hContains]
  unfold Functions.InteractionSemantics.Expr.openEvalOne
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind]
  unfold Simulation.Interaction.map
  conv_lhs => rw [Simulation.Interaction.bind_assoc]
  conv_rhs => rw [Simulation.Interaction.bind_assoc,
    Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.InteractionSemantics.Expr.openEval valueExpr target))
  intro evaluated _hEvaluated
  cases hValues : evaluated.2 with
  | nil => rfl
  | cons value rest =>
      cases rest with
      | nil =>
          simp only [Simulation.Interaction.bind_done_ok,
            Simulation.Interaction.monad_pure_bind]
          change
            Functions.InteractionSemantics.Block.openRun
                program ctx (remaining + 1) { stmts := [] }
                (evaluated.1.insert name value) = _
          rw [Functions.InteractionSemantics.Block.openRun_nil]
          rfl
      | cons next tail => rfl

/-- The ordinary generated `pre ++ [if]` block factors through `run`.  The
true continuation is exactly the singleton lexical body at the residual fuel;
the false continuation is the regular identity. -/
theorem run_if
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (cond : Locals.Expr 1) (body : Functions.Block)
    (target : Functions.InteractionSemantics.State)
    (hFuel : pre.length + 1 < targetFuel) :
    Functions.InteractionSemantics.Block.openRun program ctx targetFuel
        { stmts := pre ++ [.if_ cond body] } target =
      Simulation.Interaction.bind
        (run program ctx targetFuel pre cond target)
        (fun result =>
          match result with
          | .value state _value truth ctxAfter =>
              if truth then
                Functions.InteractionSemantics.Stmt.openRun
                  program ctxAfter (targetFuel - pre.length - 2)
                  (.block body) state
              else
                pure
                  (Functions.Source.Effectful.Outcome.regular state,
                    ctxAfter)
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  rw [Functions.InteractionSemantics.Block.openRun_append]
  unfold run
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel { stmts := pre } target))
  intro result _hResult
  cases hMode : result.1.mode with
  | regular =>
      simp only [hMode]
      have hResidual :
          ∃ remaining, targetFuel - pre.length = remaining + 2 := by
        refine ⟨targetFuel - pre.length - 2, ?_⟩
        omega
      obtain ⟨remaining, hResidual⟩ := hResidual
      rw [hResidual,
        show remaining + 2 = (remaining + 1) + 1 by omega,
        Functions.InteractionSemantics.Block.openRun_cons]
      change
        Simulation.Interaction.bind
            (Functions.InteractionSemantics.Stmt.openRun
              program result.2 (remaining + 1) (.if_ cond body)
              result.1.state)
            _ = _
      rw [Functions.InteractionSemantics.Stmt.openRun_if,
        Simulation.Interaction.bind_assoc]
      unfold Functions.InteractionSemantics.Expr.openEvalCondition
      rw [Locals.InteractionSemantics.Expr.openEvalCondition_eq_map_openEvalOne]
      unfold Simulation.Interaction.map
      rw [Simulation.Interaction.bind_assoc,
        Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Functions.InteractionSemantics.Expr.openEvalOne
            cond result.1.state))
      intro evaluated _hEvaluated
      cases hTruth : evaluated.2 != EvmYul.UInt256.ofNat 0 with
      | false =>
          simp only [hTruth, Bool.false_eq_true, ↓reduceIte,
            Simulation.Interaction.bind_done_ok,
            Simulation.Interaction.monad_pure_bind]
          change
            Functions.InteractionSemantics.Block.openRun
                program result.2 (remaining + 1) { stmts := [] }
                evaluated.1 = _
          rw [Functions.InteractionSemantics.Block.openRun_nil]
          rfl
      | true =>
          simp only [hTruth, ↓reduceIte,
            Simulation.Interaction.monad_pure_bind]
          rw [show remaining + 1 + 1 - 2 = remaining by omega]
          change
            Simulation.Interaction.bind
                (Functions.InteractionSemantics.Stmt.openRun
                  program result.2 remaining (.block body) evaluated.1)
                _ =
              Functions.InteractionSemantics.Stmt.openRun
                program result.2 remaining (.block body) evaluated.1
          rw [Functions.InteractionSemantics.Stmt.openRun_block,
            Simulation.Interaction.bind_assoc]
          apply Simulation.Interaction.AllDone.bind_congr
            (Simulation.Interaction.AllDone.trivial
              (Functions.InteractionSemantics.Block.openRun
                program result.2 remaining body evaluated.1))
          intro bodyResult _hBody
          cases hBodyMode : bodyResult.1.mode <;>
            simp [hBodyMode,
              Functions.Source.Effectful.Control.Block.runOpen,
              Simulation.Interaction.pure,
              Simulation.Interaction.bind] <;>
            rfl
  | brk | cont | leave | halt =>
      simp only [hMode]
      rfl

/-- The ordinary generated `pre ++ [switch]` block factors through the same
value-rich prepared result. The exact scrutinee selects either one lexical body
or the regular identity. -/
theorem run_switch
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (scrutinee : Locals.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block)
    (target : Functions.InteractionSemantics.State)
    (hFuel : pre.length + 1 < targetFuel) :
    Functions.InteractionSemantics.Block.openRun program ctx targetFuel
        { stmts := pre ++ [.switch scrutinee cases defaultBody] } target =
      Simulation.Interaction.bind
        (run program ctx targetFuel pre scrutinee target)
        (fun result =>
          match result with
          | .value state value _truth ctxAfter =>
              match Functions.Source.Switch.select value cases defaultBody with
              | some body =>
                  Functions.InteractionSemantics.Stmt.openRun
                    program ctxAfter (targetFuel - pre.length - 2)
                    (.block body) state
              | none =>
                  pure
                    (Functions.Source.Effectful.Outcome.regular state,
                      ctxAfter)
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  rw [Functions.InteractionSemantics.Block.openRun_append]
  unfold run
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel { stmts := pre } target))
  intro result _hResult
  cases hMode : result.1.mode with
  | regular =>
      simp only [hMode]
      have hResidual :
          ∃ remaining, targetFuel - pre.length = remaining + 2 := by
        refine ⟨targetFuel - pre.length - 2, ?_⟩
        omega
      obtain ⟨remaining, hResidual⟩ := hResidual
      rw [hResidual,
        show remaining + 2 = (remaining + 1) + 1 by omega,
        Functions.InteractionSemantics.Block.openRun_cons]
      change
        Simulation.Interaction.bind
            (Functions.InteractionSemantics.Stmt.openRun
              program result.2 (remaining + 1)
              (.switch scrutinee cases defaultBody) result.1.state)
            _ = _
      rw [Functions.InteractionSemantics.Stmt.openRun_switch,
        Simulation.Interaction.bind_assoc]
      unfold Simulation.Interaction.map
      rw [Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Functions.InteractionSemantics.Expr.openEvalOne
            scrutinee result.1.state))
      intro evaluated _hEvaluated
      cases hSelected :
          Functions.Source.Switch.select evaluated.2 cases defaultBody with
      | none =>
          simp only [hSelected]
          dsimp only [Simulation.Interaction.pure,
            Simulation.Interaction.bind]
          rw [hSelected]
          change
            Functions.InteractionSemantics.Block.openRun
                program result.2 (remaining + 1) { stmts := [] }
                evaluated.1 = _
          rw [Functions.InteractionSemantics.Block.openRun_nil]
      | some selectedBody =>
          simp only [hSelected]
          dsimp only [Simulation.Interaction.pure,
            Simulation.Interaction.bind]
          rw [hSelected]
          rw [show remaining + 1 + 1 - 2 = remaining by omega]
          change
            Simulation.Interaction.bind
                (Functions.InteractionSemantics.Stmt.openRun
                  program result.2 remaining (.block selectedBody)
                  evaluated.1)
                _ =
              Functions.InteractionSemantics.Stmt.openRun
                program result.2 remaining (.block selectedBody) evaluated.1
          rw [Functions.InteractionSemantics.Stmt.openRun_block,
            Simulation.Interaction.bind_assoc]
          apply Simulation.Interaction.AllDone.bind_congr
            (Simulation.Interaction.AllDone.trivial
              (Functions.InteractionSemantics.Block.openRun
                program result.2 remaining selectedBody evaluated.1))
          intro bodyResult _hBody
          cases hBodyMode : bodyResult.1.mode <;>
            simp [hBodyMode,
              Functions.Source.Effectful.Control.Block.runOpen,
              Simulation.Interaction.pure,
              Simulation.Interaction.bind] <;>
            rfl
  | brk | cont | leave | halt =>
      simp only [hMode]
      rfl

/-- The generated loop guard evaluates the prepared condition once. A zero
value runs the synthetic lexical `break`; a nonzero value continues with the
lowered body at the exact residual block fuel. -/
theorem run_forGuard
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (targetFuel : Nat) (pre : List Functions.Stmt)
    (cond : Locals.Expr 1) (rest : List Functions.Stmt)
    (target : Functions.InteractionSemantics.State)
    (hFuel : pre.length + 1 < targetFuel) :
    Functions.InteractionSemantics.Block.openRun program ctx targetFuel
        { stmts :=
            pre ++
              .if_
                (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                { stmts := [.brk] } ::
              rest } target =
      Simulation.Interaction.bind
        (run program ctx targetFuel pre cond target)
        (fun result =>
          match result with
          | .value state value _truth ctxAfter =>
              if value = EvmYul.UInt256.ofNat 0 then
                Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Stmt.openRun
                    program ctxAfter (targetFuel - pre.length - 2)
                    (.block { stmts := [.brk] }) state)
                  (fun guardResult =>
                    match guardResult.1.mode with
                    | .regular =>
                        Functions.InteractionSemantics.Block.openRun
                          program guardResult.2
                          (targetFuel - pre.length - 1)
                          { stmts := rest } guardResult.1.state
                    | .brk | .cont | .leave | .halt _ =>
                        pure (guardResult.1, ctxAfter))
              else
                Functions.InteractionSemantics.Block.openRun
                  program ctxAfter (targetFuel - pre.length - 1)
                  { stmts := rest } state
          | .terminal outcome ctxAfter => pure (outcome, ctxAfter)) := by
  rw [Functions.InteractionSemantics.Block.openRun_append]
  unfold run
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel { stmts := pre } target))
  intro result _hResult
  cases hMode : result.1.mode with
  | regular =>
      simp only [hMode]
      have hResidual :
          ∃ remaining, targetFuel - pre.length = remaining + 2 := by
        refine ⟨targetFuel - pre.length - 2, ?_⟩
        omega
      obtain ⟨remaining, hResidual⟩ := hResidual
      rw [hResidual,
        show remaining + 2 = (remaining + 1) + 1 by omega,
        Functions.InteractionSemantics.Block.openRun_cons]
      change
        Simulation.Interaction.bind
            (Functions.InteractionSemantics.Stmt.openRun
              program result.2 (remaining + 1)
              (.if_
                (.prim .iszero (Locals.ExprSeq.cons cond .nil))
                { stmts := [.brk] })
              result.1.state)
            _ = _
      rw [Functions.InteractionSemantics.Stmt.openRun_if,
        Simulation.Interaction.bind_assoc,
        Functions.InteractionArity.Expr.openEvalCondition_iszero_eq_map_openEvalOne]
      unfold Simulation.Interaction.map
      rw [Simulation.Interaction.bind_assoc,
        Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Functions.InteractionSemantics.Expr.openEvalOne
            cond result.1.state))
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

inductive DoneRel
    (layout used : List Functions.Name) (entryCtx : Functions.Source.Ctx) :
    Except Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Word) →
      Except EVMException TargetResult → Prop where
  | error {source target} :
      ErrorRel source target →
        DoneRel layout used entryCtx (.error source) (.error target)
  | regular {source values target truth ctx value} :
      values = [value] →
      truth = (value != EvmYul.UInt256.ofNat 0) →
      ScopedStateRel layout source target →
      TargetDomainWithin used target.vars →
      Functions.Source.Ctx.ScopeExtends entryCtx ctx →
      Functions.Source.Ctx.SameControl entryCtx ctx →
      FunctionsInteractionControlRelation.TargetScopeWithin used ctx →
      DoneRel layout used entryCtx (.ok (source, values))
        (.ok (.value target value truth ctx))
  | terminal {source target ctx} :
      TerminalFailureRel source target →
        DoneRel layout used entryCtx (.error source)
          (.ok (.terminal target ctx))

namespace DoneRel

theorem truth_eq_true_of_ne
    {truth : Bool} {value : Word}
    (hTruth : truth = (value != EvmYul.UInt256.ofNat 0))
    (hNe : value ≠ EvmYul.UInt256.ofNat 0) :
    truth = true := by
  rw [hTruth]
  cases value with
  | mk value =>
      simp [bne, EvmYul.instBEqUInt256,
        EvmYul.instBEqUInt256.beq,
        EvmYul.UInt256.ofNat, Id.run] at hNe ⊢
      exact hNe

theorem transport_entry
    {layout used : List Functions.Name}
    {entry middle : Functions.Source.Ctx}
    {sourceDone targetDone}
    (hScope : Functions.Source.Ctx.ScopeExtends entry middle)
    (hControl : Functions.Source.Ctx.SameControl entry middle)
    (hDone : DoneRel layout used middle sourceDone targetDone) :
    DoneRel layout used entry sourceDone targetDone := by
  cases hDone with
  | error hError => exact .error hError
  | regular hValues hTruth hScoped hDomain hFinalScope hFinalControl
      hTargetScope =>
      exact .regular hValues hTruth hScoped hDomain
        (Functions.Source.Ctx.ScopeExtends.trans hScope hFinalScope)
        (Functions.Source.Ctx.SameControl.trans hControl hFinalControl)
        hTargetScope
  | terminal hTerminal => exact .terminal hTerminal

end DoneRel

/-- A compiler prelude that leaves one stable delayed value can be consumed as
a condition without knowing whether the prelude used literals, variables, or
an internal-call result temporary. -/
theorem ofStablePrepared
    {sourceFuel targetFuel : Nat}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {final : Fresh.State}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedArgs.DoneRel
          layout final [lower] target ctx)
        (Yul.InteractionSemantics.evalValues
          sourceFuel expr codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final.used ctx)
      (Yul.InteractionSemantics.evalValues
        sourceFuel expr codeOverride source)
      (run program ctx targetFuel pre lower target) := by
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (DoneRel layout final.used ctx)
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalValues
            sourceFuel expr codeOverride source) pure)
        (run program ctx targetFuel pre lower target) := by
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
                Functions.InteractionSemantics.Expr.openEvalOne
                    lower targetAfter =
                  .done (.ok (targetAfter, value)) := by
              unfold Functions.InteractionSemantics.Expr.openEvalOne
                Locals.InteractionSemantics.Expr.openEvalOne
                Locals.Source.Effectful.Expr.Control.evalOne
              unfold Locals.InteractionSemantics.Expr.openEval at hEval
              rw [hEval]
              rfl
            simp only [Simulation.Interaction.bind_done_ok,
              Functions.Source.Effectful.Outcome.regular_mode]
            change
              Simulation.Interaction.ForwardRel Truncated
                (DoneRel layout final.used ctx)
                (pure (sourceAfter, [value]))
                (Simulation.Interaction.map
                  (fun evaluated => TargetResult.value evaluated.1 evaluated.2
                    (evaluated.2 != EvmYul.UInt256.ofNat 0) ctxAfter)
                  (Functions.InteractionSemantics.Expr.openEvalOne
                    lower targetAfter))
            rw [hOne]
            simp only [Simulation.Interaction.map,
              Simulation.Interaction.bind_done_ok,
              Simulation.Interaction.monad_pure_bind]
            exact Simulation.Interaction.ForwardRel.done
              (.regular rfl rfl hScoped hDomain hScope hControl hTargetScope)
  have hSourceBind :
      Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalValues
            sourceFuel expr codeOverride source) pure =
        Yul.InteractionSemantics.evalValues
          sourceFuel expr codeOverride source :=
    Simulation.Interaction.bind_pure _
  rw [hSourceBind] at hBound
  exact hBound

/- Convert any adjacent one-result expression theorem into a Boolean condition
relation. This is intentionally independent of generated preludes: their owner
can establish the expression relation and then use this boundary. -/
theorem ofOpenExpression
    {lower : Locals.Expr 1} {used layout : List Functions.Name}
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
        (FunctionsInteractionExpression.DoneRel sourceEntry 1)
        sourceOpen
        (Functions.InteractionSemantics.Expr.openEval lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout used ctx) sourceOpen
      (Simulation.Interaction.map
        (fun evaluated => TargetResult.value evaluated.1 evaluated.2
          (evaluated.2 != EvmYul.UInt256.ofNat 0) ctx)
        (Functions.InteractionSemantics.Expr.openEvalOne
          lower target)) := by
  unfold Simulation.Interaction.map
  unfold Functions.InteractionSemantics.Expr.openEvalOne
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc]
  have hEvalVars := hEval.strengthen_right
    (Locals.InteractionSemantics.Expr.openEval_vars_eq lower target)
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

/-- Convert a direct one-result expression theorem into the same prepared
condition interface. This is the effectful primitive path: the expression is
evaluated exactly where the Functions conditional evaluates it. -/
theorem ofDirectExpression
    {sourceFuel targetFuel : Nat}
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
        (FunctionsInteractionExpression.DoneRel source 1)
        (Yul.InteractionSemantics.evalValues
          sourceFuel expr codeOverride source)
        (Functions.InteractionSemantics.Expr.openEval lower target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout after.used ctx)
      (Yul.InteractionSemantics.evalValues
        sourceFuel expr codeOverride source)
      (run program ctx targetFuel [] lower target) := by
  obtain ⟨remaining, rfl⟩ : ∃ remaining, targetFuel = remaining + 1 :=
    ⟨targetFuel - 1, by omega⟩
  unfold run
  rw [Functions.InteractionSemantics.Block.openRun_nil]
  exact ofOpenExpression hScoped (hDomain.mono hExtends)
    (hTargetScope.mono hExtends) hEval

/-- The direct branch of ordinary unchecked primitive lowering, specialized to
condition evaluation. Arguments stay inline, while the primitive effect still
uses the shared compiler-selected open-world theorem. -/
theorem ofDirectPrimitiveLowering
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
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
      (Yul.InteractionSemantics.evalValues
        (argsFuel + 1) (.Call (.inl prim) args) codeOverride source)
      (run program ctx targetFuel [] lower target) := by
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
        (FunctionsInteractionExpression.compilerDirectAt
          codeOverride argsFuel).evalArgs
          hLowerReverse hDirectSeq hScoped.state
      have hPrimitiveRel :=
        FunctionsInteractionExpression.Expr.primitive_of_args
          hPrimitive (primitiveFuel := argsFuel) hOp hOutputs hArgsRel
      have hEval :
          Simulation.Interaction.ForwardRel Truncated
            (FunctionsInteractionExpression.DoneRel source 1)
            (Yul.InteractionSemantics.evalValues
              (argsFuel + 1) (.Call (.inl prim) args) codeOverride source)
            (Functions.InteractionSemantics.Expr.openEval
              (Expr.cast hOutputs (.prim op seq)) target) := by
        rw [FunctionsInteractionExpression.expr_openEval_cast]
        simpa [Yul.InteractionSemantics.evalValues,
          Yul.Source.Canonical.evalValues,
          Yul.Source.Effectful.evalValues,
          Functions.InteractionSemantics.Expr.openEval,
          Locals.InteractionSemantics.Expr.openEval,
          Locals.Source.Effectful.Expr.Control.eval,
          FunctionsInteractionExpression.exprSeq_openEval_seqCast] using
          hPrimitiveRel
      exact ofDirectExpression hTargetFuel (Fresh.Extends.refl before)
        hScoped hDomain hTargetScope hEval

/-- Prepared primitive arguments and the selected primitive effect compose into
the same condition interface. This is the non-direct lowering branch used by
ordinary compiler-selected condition expressions. -/
theorem ofPreparedPrimitive
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
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
        (FunctionsInteractionPreparedArgs.DoneRel
          layout final lowerArgs.reverse entry ctx)
        (Yul.InteractionSemantics.evalArgs
          argsFuel args.reverse codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := pre } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (DoneRel layout final.used ctx)
      (Yul.InteractionSemantics.evalValues
        (argsFuel + 1) (.Call (.inl prim) args) codeOverride source)
      (run program ctx targetFuel pre
        (Expr.cast hOutputs (.prim op seq)) target) := by
  unfold Yul.InteractionSemantics.evalValues
    Yul.Source.Canonical.evalValues Yul.Source.Effectful.evalValues
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
      cases argsFuel with
      | zero =>
          have hTruncated :
              Truncated
                ({ exception := .OutOfFuel, state := sourceAfter } :
                  Yul.InteractionSemantics.Failure) := by
            trivial
          simpa [Yul.InteractionSemantics.Primitive.openEval,
            Yul.InteractionSemantics.Primitive.fail] using
            (Simulation.Interaction.ForwardRel.truncated
              (doneRel := DoneRel layout final.used ctx)
              (right :=
                Simulation.Interaction.map
                  (fun evaluated => TargetResult.value evaluated.1 evaluated.2
                    (evaluated.2 != EvmYul.UInt256.ofNat 0) ctxAfter)
                  (Functions.InteractionSemantics.Expr.openEvalOne
                    (Expr.cast hOutputs (.prim op seq)) targetAfter))
              hTruncated)
      | succ primitiveFuel =>
          have hDirectSeq :
              Expr.List.toSeq? lowerArgs.reverse
                  (Expressions.Structured.BasicOp.inputs op) = some seq := by
            simpa [Expr.List.toStackSeq?] using hSeq
          have hSourceLength :
              values.reverse.length =
                Expressions.Structured.BasicOp.inputs op := by
            simpa [List.length_reverse] using
              hStable.length.trans (Expr.List.toSeq?_length hDirectSeq)
          have hPrimitiveRel :=
            hPrimitive (fuel := primitiveFuel)
              (sourceValues := values.reverse) hOp hSourceLength hScoped.state
          have hPrimitiveRel' :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionPrimitive.PrimitiveDoneRel
                  sourceAfter op)
                (Yul.InteractionSemantics.Primitive.openEval
                  (primitiveFuel + 1) sourceAfter prim values.reverse)
                (Locals.InteractionSemantics.Primitive.openEval
                  op targetAfter values) := by
            simpa using hPrimitiveRel
          have hSeqEval := hStable.exprSeq_openEval hDirectSeq
            (TargetExtends.refl targetAfter.vars)
          unfold Locals.InteractionSemantics.ExprSeq.openEval at hSeqEval
          have hTargetEval :
              Functions.InteractionSemantics.Expr.openEval
                  (Expr.cast hOutputs (.prim op seq)) targetAfter =
                Locals.InteractionSemantics.Primitive.openEval
                  op targetAfter values := by
            rw [FunctionsInteractionExpression.expr_openEval_cast]
            unfold Functions.InteractionSemantics.Expr.openEval
              Locals.InteractionSemantics.Expr.openEval
              Locals.Source.Effectful.Expr.Control.eval
            rw [hSeqEval]
            rfl
          have hExprRel :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionExpression.DoneRel sourceAfter 1)
                (Yul.InteractionSemantics.Primitive.openEval
                  (primitiveFuel + 1) sourceAfter prim values.reverse)
                (Functions.InteractionSemantics.Expr.openEval
                  (Expr.cast hOutputs (.prim op seq)) targetAfter) := by
            rw [hTargetEval]
            apply Simulation.Interaction.ForwardRel.mono hPrimitiveRel'
            intro sourceDone targetDone hDone
            cases hDone with
            | error hError => exact .error hError
            | ok hOk =>
                exact .ok
                  ⟨hOk.1.1, hOk.1.2, hOk.2.1.trans hOutputs, hOk.2.2⟩
          have hCondition := ofOpenExpression
            (ctx := ctxAfter) hScoped hDomain hTargetScope hExprRel
          exact Simulation.Interaction.ForwardRel.mono hCondition
            (fun _sourceDone _targetDone conditionDone =>
              DoneRel.transport_entry hScope hControl conditionDone)

end FunctionsInteractionPreparedCondition
end Yul
end EvmCompiler
