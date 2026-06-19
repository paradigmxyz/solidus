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
    (outerScopes : SourceScopes)
    (canLeave : Bool) :
    Except Yul.InteractionSemantics.Failure
        (Sum Yul.InteractionSemantics.State
          Yul.InteractionSemantics.State) →
      Except EVMException Functions.InteractionSemantics.Outcome → Prop where
  | error {source target} :
      ErrorRel source target →
        GuardedBodyDoneRel used layout outerScopes canLeave
          (.error source) (.error target)
  | zero {source target} :
      ScopedStateRel layout source target.state →
      TargetDomainWithin used target.state.vars →
      target.mode = .brk →
        GuardedBodyDoneRel used layout outerScopes canLeave
          (.ok (.inl source)) (.ok target)
  | body {sourceScope sourceDone targetDone} :
      ControlOutcomeDoneRel used layout
        (ControlContextRel.forBodyScopes sourceScope outerScopes)
        true true canLeave sourceDone targetDone →
      Yul.InteractionSemantics.Exec.DoneRestrictedTo
        sourceScope.store sourceDone →
      sourceScope.targetUsed = used →
      sourceScope.layout = layout →
      GuardedBodyDoneRel used layout outerScopes canLeave
        (sourceDone.map Sum.inr) targetDone
  | terminal {source target} :
      TerminalFailureRel source target →
        GuardedBodyDoneRel used layout outerScopes canLeave
          (.error source) (.ok target)

/-- Compose the ordinary prepared condition, synthetic `iszero`/`break`, and
one recursively checked lexical body. The target executes under the extended
condition context but regular cleanup returns to the original loop scope. -/
theorem guardedBody
    {conditionFuel bodyFuel targetFuel : Nat}
    {entryUsed layout conditionUsed finalUsed bodyLayout : List Functions.Name}
    {outerScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {cond : AstExpr} {body : List AstStmt}
    {pre : List Functions.Stmt} {lowerCond : Locals.Expr 1}
    {lowerBody : Functions.Block}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hTargetFuel : pre.length + 2 < targetFuel)
    (hControl : ControlContextRel outerScopes layout
      canBreak canContinue canLeave ctx)
    (hCtxScopeUsed : ∀ name, name ∈ ctx.scope → name ∈ entryUsed)
    (hCondition :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedCondition.DoneRel
          layout conditionUsed
            (ctx.withLoopControl ctx.scope ctx.scope))
        (Yul.InteractionSemantics.evalValues
          conditionFuel cond codeOverride source)
        (FunctionsInteractionPreparedCondition.run
          program (ctx.withLoopControl ctx.scope ctx.scope)
            targetFuel pre lowerCond target))
    (hBodyLayout : ∀ name, name ∈ layout → name ∈ bodyLayout)
    (hBody :
      ∀ {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State}
        {ctxAfter : Functions.Source.Ctx}
        {sourceScope : SourceScope},
      ScopedStateRel layout sourceAfter targetAfter →
      TargetDomainWithin conditionUsed targetAfter.vars →
      ControlContextRel
          (ControlContextRel.forBodyScopes sourceScope outerScopes)
          layout true true canLeave ctxAfter →
      TargetScopeWithin conditionUsed ctxAfter →
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel finalUsed bodyLayout
          (ControlContextRel.forBodyScopes sourceScope outerScopes)
          true true canLeave)
        (Yul.InteractionSemantics.execSeq
          bodyFuel body codeOverride sourceAfter)
        (Functions.InteractionSemantics.Block.openRun
          program ctxAfter (targetFuel - pre.length - 1)
          lowerBody targetAfter)) :
    Simulation.Interaction.ForwardRel Truncated
      (GuardedBodyDoneRel entryUsed layout outerScopes canLeave)
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
        program (ctx.withLoopControl ctx.scope ctx.scope)
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
    program (ctx.withLoopControl ctx.scope ctx.scope) targetFuel pre lowerCond
      lowerBodyStmts target (by omega),
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
      hValues _hTruth hScoped hDomain hScope hSameControl hTargetScopeAfter =>
      obtain ⟨sourceScope, hScopeStore, hScopeUsed, hScopeLayout,
          hBodyControl⟩ :=
        ControlContextRel.forBody hScoped hControl hCtxScopeUsed
      have hControlAfter :
          ControlContextRel
            (ControlContextRel.forBodyScopes sourceScope outerScopes)
            layout true true canLeave ctxAfter := by
        apply ControlContextRel.transport hBodyControl
        · exact fun _name hName => hName
        · exact hSameControl
        · intro name hName
          exact hScope name (by
            simpa [Functions.Source.Ctx.withLoopControl] using
              hControl.scope name hName)
      have hBreakAfter : ctxAfter.breakScope? = some ctx.scope := by
        rw [← hSameControl.breakScope]
        simp [Functions.Source.Ctx.withLoopControl]
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
            (TargetDomainWithin.restrictTo_scope
              targetAfter hCtxScopeUsed) rfl)
      · simp only [hZero, ↓reduceIte]
        have hBodyRaw := hBody hScoped hDomain hControlAfter hTargetScopeAfter
        have hClosed :=
          FunctionsInteractionStatement.ControlDoneRel.blockClosedToScope
            hScoped hControlAfter hControl.scope
              (fun targetState _hDomain =>
                TargetDomainWithin.restrictTo_scope
                  targetState hCtxScopeUsed)
              hBodyLayout hBodyRaw
        have hRestricted :
            Simulation.Interaction.AllDone
              (Yul.InteractionSemantics.Exec.DoneRestrictedTo
                sourceScope.store)
              (Yul.InteractionSemantics.exec
                (bodyFuel + 1) (.Block body) codeOverride sourceAfter) := by
          rw [hScopeStore]
          exact Yul.InteractionSemantics.Exec.block_allDone_restricted
            bodyFuel body codeOverride sourceAfter
        have hClosedRestricted := hClosed.strengthen_left hRestricted
        unfold Simulation.Interaction.map
        have hMapped :=
          Simulation.Interaction.ForwardRel.bind_custom
            (leftNext := fun sourceState =>
              Simulation.Interaction.pure (Sum.inr sourceState))
            (rightNext := fun targetOutcome =>
              Simulation.Interaction.pure targetOutcome)
            hClosedRestricted
            (fun sourceDone targetDone hClosedDone => by
              rcases hClosedDone with ⟨hClosedDone, hRestrictedDone⟩
              cases sourceDone <;> cases targetDone <;>
                exact Simulation.Interaction.ForwardRel.done
                  (GuardedBodyDoneRel.body hClosedDone hRestrictedDone
                    hScopeUsed hScopeLayout))
        simpa [Simulation.Interaction.bind_pure] using hMapped

abbrev KernelDoneRel
    (used layout : List Functions.Name) (outerScopes : SourceScopes)
    (canLeave : Bool) :=
  ControlOutcomeDoneRel used layout
    (ControlContextRel.forPostScopes outerScopes) false false canLeave

/-- Compose one canonical Yul loop iteration with one canonical Functions loop
iteration. The guarded body, post block, and recursive iteration remain
separate adjacent capabilities supplied by their owning proofs. -/
theorem iteration
    {fuel targetFuel : Nat}
    {used layout : List Functions.Name} {outerScopes : SourceScopes}
    {canLeave : Bool}
    {cond : AstExpr} {post body : List AstStmt}
    {lowerPost lowerGuarded : Functions.Block}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {entryShared : EvmYul.SharedState .Yul}
    {entryVars : EvmYul.Yul.VarStore}
    {target : Functions.InteractionSemantics.State}
    (hGuarded :
      Simulation.Interaction.ForwardRel Truncated
        (GuardedBodyDoneRel used layout outerScopes canLeave)
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalValues fuel cond codeOverride
            (.Ok entryShared entryVars))
          (fun result =>
            if result.2.head! = EvmYul.UInt256.ofNat 0 then
              Simulation.Interaction.pure (.inl result.1)
            else
              Simulation.Interaction.map Sum.inr
                (Yul.InteractionSemantics.exec fuel (.Block body)
                  codeOverride result.1)))
        (Functions.InteractionSemantics.Block.openRunScoped
          program (ctx.withLoopControl ctx.scope ctx.scope)
          lowerGuarded targetFuel target))
    (hPost :
      ∀ {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State},
      ScopedStateRel layout sourceAfter targetAfter →
      TargetDomainWithin used targetAfter.vars →
      Simulation.Interaction.ForwardRel Truncated
        (KernelDoneRel used layout outerScopes canLeave)
        (Yul.InteractionSemantics.exec fuel (.Block post)
          codeOverride sourceAfter)
        (Functions.InteractionSemantics.Block.openRunScoped
          program ctx.withoutLoopControl lowerPost targetFuel targetAfter))
    (hRecurse :
      ∀ {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State},
      ScopedStateRel layout sourceAfter targetAfter →
      TargetDomainWithin used targetAfter.vars →
      Simulation.Interaction.ForwardRel Truncated
        (KernelDoneRel used layout outerScopes canLeave)
        (Yul.InteractionSemantics.exec fuel (.For cond post body)
          codeOverride sourceAfter)
        (Functions.InteractionSemantics.Stmt.openRunForLoop
          program ctx.withoutLoopControl
          (.lit (EvmYul.UInt256.ofNat 1)) ctx.withoutLoopControl lowerPost
          (ctx.withLoopControl ctx.scope ctx.scope) lowerGuarded
          targetFuel targetAfter)) :
    Simulation.Interaction.ForwardRel Truncated
      (KernelDoneRel used layout outerScopes canLeave)
      (Yul.InteractionSemantics.loop (fuel + 1 + 1) cond post body
        codeOverride (.Ok entryShared entryVars))
      (Functions.InteractionSemantics.Stmt.openRunForLoop
        program ctx.withoutLoopControl
        (.lit (EvmYul.UInt256.ofNat 1)) ctx.withoutLoopControl lowerPost
        (ctx.withLoopControl ctx.scope ctx.scope) lowerGuarded
        (targetFuel + 1) target) := by
  have hPostThenRecurse :
      ∀ {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State},
      ScopedStateRel layout sourceAfter targetAfter →
      TargetDomainWithin used targetAfter.vars →
      Simulation.Interaction.ForwardRel Truncated
        (KernelDoneRel used layout outerScopes canLeave)
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.exec fuel (.Block post)
            codeOverride sourceAfter)
          (fun stateAfterPost =>
            match stateAfterPost with
            | .OutOfFuel => Simulation.Interaction.pure .OutOfFuel
            | .Checkpoint (.Leave shared vars) =>
                Simulation.Interaction.pure
                  (.Checkpoint (.Leave shared vars))
            | _ =>
                Yul.InteractionSemantics.exec fuel (.For cond post body)
                  codeOverride stateAfterPost))
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Block.openRunScoped
            program ctx.withoutLoopControl lowerPost targetFuel targetAfter)
          (fun postOutcome =>
            match postOutcome.mode with
            | .regular =>
                Functions.InteractionSemantics.Stmt.openRunForLoop
                  program ctx.withoutLoopControl
                  (.lit (EvmYul.UInt256.ofNat 1)) ctx.withoutLoopControl
                  lowerPost (ctx.withLoopControl ctx.scope ctx.scope)
                  lowerGuarded targetFuel postOutcome.state
            | .brk | .cont =>
                Simulation.Interaction.error .InvalidInstruction
            | .leave | .halt _ =>
                Simulation.Interaction.pure postOutcome)) := by
    intro sourceAfter targetAfter hScoped hDomain
    apply Simulation.Interaction.ForwardRel.bind_custom
      (hPost hScoped hDomain)
    intro sourcePostDone targetPostDone hPostDone
    cases hPostDone with
    | error hError =>
        exact Simulation.Interaction.ForwardRel.done (.error hError)
    | @regular sourceFinal targetFinal hFinalScoped hFinalDomain =>
        rcases hFinalScoped.state with
          ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
        subst sourceFinal
        simpa using hRecurse hFinalScoped hFinalDomain
    | brk hScope _hMode _hAbrupt =>
        simp [ControlContextRel.forPostScopes] at hScope
    | cont hScope _hMode _hAbrupt =>
        simp [ControlContextRel.forPostScopes] at hScope
    | @leave sourceFinal targetFinal scope hScope hMode hAbrupt =>
        obtain ⟨jump, hSource⟩ :=
          ModeRel.target_nonregular_source_checkpoint hAbrupt.mode
            (by simp [hMode])
        subst sourceFinal
        cases jump with
        | Break shared vars =>
            have hModeRel := hAbrupt.mode
            simp [FunctionsInteractionRelation.ModeRel, hMode] at hModeRel
        | Continue shared vars =>
            have hModeRel := hAbrupt.mode
            simp [FunctionsInteractionRelation.ModeRel, hMode] at hModeRel
        | Leave shared vars =>
            simpa [hMode] using
              (Simulation.Interaction.ForwardRel.done
                (ControlOutcomeDoneRel.leave hScope hMode hAbrupt))
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
  rw [Yul.InteractionSemantics.Exec.loop_succ_succ_guarded,
    Functions.InteractionSemantics.Stmt.openRunForLoop_true_succ]
  apply Simulation.Interaction.ForwardRel.bind_custom hGuarded
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | zero hScoped hDomain hMode =>
      simp only [hMode]
      exact Simulation.Interaction.ForwardRel.done
        (.regular hScoped hDomain)
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
  | @body sourceScope sourceDone targetDone hBodyDone hRestricted hScopeUsed
      hScopeLayout =>
      cases hBodyDone with
      | error hError =>
          exact Simulation.Interaction.ForwardRel.done (.error hError)
      | @regular sourceAfter targetAfter hScoped hDomain =>
          rcases hScoped.state with
            ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
          subst sourceAfter
          simpa using hPostThenRecurse hScoped hDomain
      | @brk sourceAfter targetOutcome scope hScope hMode hAbrupt =>
          have hScopeEq : sourceScope = scope := by
            simpa [ControlContextRel.forBodyScopes] using hScope
          subst scope
          obtain ⟨jump, hSource⟩ :=
            ModeRel.target_nonregular_source_checkpoint hAbrupt.mode
              (by simp [hMode])
          subst sourceAfter
          cases jump with
          | Break shared vars =>
              change
                (EvmYul.Yul.State.Checkpoint (.Break shared vars)).restrictStoreTo
                    sourceScope.store =
                  EvmYul.Yul.State.Checkpoint (.Break shared vars)
                at hRestricted
              have hScoped := hAbrupt.state
              rw [hRestricted] at hScoped
              rw [hScopeLayout] at hScoped
              have hEntryDomain := hAbrupt.targetDomain
              rw [hScopeUsed] at hEntryDomain
              simp only [hMode]
              exact Simulation.Interaction.ForwardRel.done
                (.regular hScoped hEntryDomain)
          | Continue shared vars =>
              have hModeRel := hAbrupt.mode
              simp [FunctionsInteractionRelation.ModeRel, hMode] at hModeRel
          | Leave shared vars =>
              have hModeRel := hAbrupt.mode
              simp [FunctionsInteractionRelation.ModeRel, hMode] at hModeRel
      | @cont sourceAfter targetOutcome scope hScope hMode hAbrupt =>
          have hScopeEq : sourceScope = scope := by
            simpa [ControlContextRel.forBodyScopes] using hScope
          subst scope
          obtain ⟨jump, hSource⟩ :=
            ModeRel.target_nonregular_source_checkpoint hAbrupt.mode
              (by simp [hMode])
          subst sourceAfter
          cases jump with
          | Break shared vars =>
              have hModeRel := hAbrupt.mode
              simp [FunctionsInteractionRelation.ModeRel, hMode] at hModeRel
          | Continue shared vars =>
              change
                (EvmYul.Yul.State.Checkpoint (.Continue shared vars)).restrictStoreTo
                    sourceScope.store =
                  EvmYul.Yul.State.Checkpoint (.Continue shared vars)
                at hRestricted
              have hScoped := hAbrupt.state
              rw [hRestricted] at hScoped
              rw [hScopeLayout] at hScoped
              have hEntryDomain := hAbrupt.targetDomain
              rw [hScopeUsed] at hEntryDomain
              simpa [hMode] using
                hPostThenRecurse hScoped hEntryDomain
          | Leave shared vars =>
              have hModeRel := hAbrupt.mode
              simp [FunctionsInteractionRelation.ModeRel, hMode] at hModeRel
      | @leave sourceAfter targetOutcome scope hScope hMode hAbrupt =>
          have hOuterScope : outerScopes.leaveScope? = some scope := by
            simpa [ControlContextRel.forBodyScopes] using hScope
          obtain ⟨jump, hSource⟩ :=
            ModeRel.target_nonregular_source_checkpoint hAbrupt.mode
              (by simp [hMode])
          subst sourceAfter
          cases jump with
          | Break shared vars =>
              have hModeRel := hAbrupt.mode
              simp [FunctionsInteractionRelation.ModeRel, hMode] at hModeRel
          | Continue shared vars =>
              have hModeRel := hAbrupt.mode
              simp [FunctionsInteractionRelation.ModeRel, hMode] at hModeRel
          | Leave shared vars =>
              simp only [hMode]
              exact Simulation.Interaction.ForwardRel.done
                (ControlOutcomeDoneRel.leave (by
                  simpa [ControlContextRel.forPostScopes] using hOuterScope)
                  hMode hAbrupt)
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

end FunctionsInteractionLoop
end Yul
end EvmCompiler
