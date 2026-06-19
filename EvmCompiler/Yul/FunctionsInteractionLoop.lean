import EvmCompiler.Yul.FunctionsInteractionPreparedCondition
import EvmCompiler.Yul.FunctionsInteractionStatement

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionLoop

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation

/-- One guarded target-loop body either observes a zero source condition or
executes the source lexical body. The target side retains ordinary control
outcomes so the loop kernel, rather than this adapter, catches `break` and
routes `continue` through the post block. -/
inductive GuardedBodyDoneRel
    (used layout : List Functions.Name)
    (sourceScopes : SourceScopes)
    (canLeave : Bool) :
    Except Yul.InteractionSemantics.Failure
        (Sum Yul.InteractionSemantics.State
          Yul.InteractionSemantics.State) →
      Except EVMException Functions.InteractionSemantics.Outcome → Prop where
  | error {source target} :
      ErrorRel source target →
        GuardedBodyDoneRel used layout sourceScopes canLeave
          (.error source) (.error target)
  | zero {source target} :
      ScopedStateRel layout source target.state →
      TargetDomainWithin used target.state.vars →
      target.mode = .brk →
        GuardedBodyDoneRel used layout sourceScopes canLeave
          (.ok (.inl source)) (.ok target)
  | body {sourceDone targetDone} :
      ControlOutcomeDoneRel used layout sourceScopes
        true true canLeave sourceDone targetDone →
      GuardedBodyDoneRel used layout sourceScopes canLeave
        (sourceDone.map Sum.inr) targetDone
  | terminal {source target} :
      TerminalFailureRel source target →
        GuardedBodyDoneRel used layout sourceScopes canLeave
          (.error source) (.ok target)

/-- Compose the ordinary prepared condition, synthetic `iszero`/`break`, and
one recursively checked lexical body. The target executes under the extended
condition context but regular cleanup returns to the original loop scope. -/
theorem guardedBody
    {conditionFuel bodyFuel targetFuel : Nat}
    {layout conditionUsed finalUsed bodyLayout : List Functions.Name}
    {sourceScopes : SourceScopes} {canLeave : Bool}
    {cond : AstExpr} {body : List AstStmt}
    {pre : List Functions.Stmt} {lowerCond : Locals.Expr 1}
    {lowerBody : Functions.Block}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hTargetFuel : pre.length + 2 < targetFuel)
    (hBreakScope : ctx.breakScope? = some ctx.scope)
    (hControl : ControlContextRel sourceScopes layout
      true true canLeave ctx)
    (hUsedSubset : ∀ name, name ∈ conditionUsed → name ∈ finalUsed)
    (hCondition :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedCondition.DoneRel
          layout conditionUsed ctx)
        (Yul.InteractionSemantics.evalValues
          conditionFuel cond codeOverride source)
        (FunctionsInteractionPreparedCondition.run
          program ctx targetFuel pre lowerCond target))
    (hBodyLayout : ∀ name, name ∈ layout → name ∈ bodyLayout)
    (hBody :
      ∀ {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State}
        {ctxAfter : Functions.Source.Ctx},
      ScopedStateRel layout sourceAfter targetAfter →
      TargetDomainWithin conditionUsed targetAfter.vars →
      ControlContextRel sourceScopes layout
        true true canLeave ctxAfter →
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel finalUsed bodyLayout sourceScopes
          true true canLeave)
        (Yul.InteractionSemantics.execSeq
          bodyFuel body codeOverride sourceAfter)
        (Functions.InteractionSemantics.Block.openRun
          program ctxAfter (targetFuel - pre.length - 1)
          lowerBody targetAfter)) :
    Simulation.Interaction.ForwardRel Truncated
      (GuardedBodyDoneRel finalUsed layout sourceScopes canLeave)
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalValues
          conditionFuel cond codeOverride source)
        (fun result =>
          if result.2.head! = EvmYul.UInt256.ofNat 0 then
            Simulation.Interaction.pure (.inl result.1)
          else
            Simulation.Interaction.map Sum.inr
              (Yul.InteractionSemantics.exec
                (bodyFuel + 1) (.Block body)
                codeOverride result.1)))
      (Functions.InteractionSemantics.Block.openRunScoped
        program ctx
        { stmts :=
            pre ++
              .if_
                (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                { stmts := [.brk] } ::
              lowerBody.stmts }
        targetFuel target) := by
  rcases lowerBody with ⟨lowerBodyStmts⟩
  rw [Functions.InteractionSemantics.Block.openRunScoped_eq_bind,
    FunctionsInteractionPreparedCondition.run_forGuard
    program ctx targetFuel pre lowerCond lowerBodyStmts target (by omega),
    Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.ForwardRel.bind_custom hCondition
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
  | @regular sourceAfter values targetAfter truth ctxAfter value
      hValues _hTruth hScoped hDomain hScope hSameControl =>
      have hControlAfter : ControlContextRel sourceScopes layout
          true true canLeave ctxAfter := by
        apply ControlContextRel.transport hControl
        · exact fun _name hName => hName
        · exact hSameControl
        · intro name hName
          exact hScope name (hControl.scope name hName)
      have hBreakAfter : ctxAfter.breakScope? = some ctx.scope := by
        rw [← hSameControl.breakScope]
        exact hBreakScope
      subst values
      simp only [List.head!_cons, Simulation.Interaction.bind_done_ok]
      by_cases hZero : value = EvmYul.UInt256.ofNat 0
      · simp only [hZero, ↓reduceIte]
        obtain ⟨remaining, hRemaining⟩ :
            ∃ remaining,
              targetFuel - pre.length - 2 = remaining + 1 := by
          refine ⟨targetFuel - pre.length - 3, ?_⟩
          omega
        rw [hRemaining,
          Functions.InteractionSemantics.Stmt.openRun_block_brk
            program ctxAfter remaining targetAfter hBreakAfter]
        exact Simulation.Interaction.ForwardRel.done
          (.zero
            (hScoped.restrictTargetScoped hControl.scope)
            (hDomain.mono hUsedSubset).restrictTo rfl)
      · simp only [hZero, ↓reduceIte]
        have hBodyRaw := hBody hScoped hDomain hControlAfter
        have hClosed :=
          FunctionsInteractionStatement.ControlDoneRel.blockClosedToScope
            hScoped hControlAfter hControl.scope hBodyLayout hBodyRaw
        unfold Simulation.Interaction.map
        have hMapped :=
          Simulation.Interaction.ForwardRel.bind_custom
            (leftNext := fun sourceState =>
              Simulation.Interaction.pure (Sum.inr sourceState))
            (rightNext := fun targetOutcome =>
              Simulation.Interaction.pure targetOutcome)
            hClosed
            (fun sourceDone targetDone hClosedDone => by
              cases sourceDone <;> cases targetDone <;>
                exact Simulation.Interaction.ForwardRel.done
                  (GuardedBodyDoneRel.body hClosedDone))
        simpa [Simulation.Interaction.bind_pure] using hMapped

end FunctionsInteractionLoop
end Yul
end EvmCompiler
