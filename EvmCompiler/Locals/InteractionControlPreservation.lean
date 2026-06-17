import EvmCompiler.Locals.InteractionPreservation

namespace EvmCompiler
namespace Locals
namespace InteractionPreservation

namespace Stmt.ControlPolicy

def CompatibleOutcome (policy : Stmt.ControlPolicy) :
    Except EVMException
      (Locals.Source.Effectful.Outcome Locals.Source.State ×
        Locals.Source.Ctx) → Prop
  | .error _ => True
  | .ok result => ContextCompatible policy result.2

def NoLoopExitOutcome :
    Except EVMException
      (Locals.Source.Effectful.Outcome Locals.Source.State ×
        Locals.Source.Ctx) → Prop
  | .error _ => True
  | .ok result =>
      result.1.mode ≠ .brk ∧ result.1.mode ≠ .cont

theorem allDone_bind_fixedContext
    {α : Type}
    (policy : Stmt.ControlPolicy)
    (run : Simulation.Interaction EVMException α)
    (finish : α → Locals.Source.Effectful.Outcome Locals.Source.State)
    (ctx : Locals.Source.Ctx)
    (hPolicy : ContextCompatible policy ctx) :
    Simulation.Interaction.AllDone
      (CompatibleOutcome policy)
      (Simulation.Interaction.bind run
        (fun value => Simulation.Interaction.pure (finish value, ctx))) := by
  apply Simulation.Interaction.AllDone.bind
    (Simulation.Interaction.AllDone.trivial run)
  · intro error _
    trivial
  · intro value _
    apply Simulation.Interaction.AllDone.done
    exact hPolicy

/-- Regular source execution changes only the lexical scope, never the
surrounding break, continue, or leave destinations. -/
theorem allDone_openRun
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (sourceCtx : Locals.Source.Ctx)
    (fuel : Nat) (stmt : Locals.Stmt)
    (source : Locals.Source.State)
    (hPolicy : ContextCompatible policy sourceCtx) :
    Simulation.Interaction.AllDone
      (CompatibleOutcome policy)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel stmt source) := by
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  cases stmt with
  | expr expr =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      exact allDone_bind_fixedContext policy _ _ sourceCtx hPolicy
  | exprs exprs =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      exact allDone_bind_fixedContext policy _ _ sourceCtx hPolicy
  | let_ name value =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      exact
        allDone_bind_fixedContext policy _ _ _
          (contextCompatible_scope hPolicy (name :: sourceCtx.scope))
  | assign name value =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      split
      · exact allDone_bind_fixedContext policy _ _ sourceCtx hPolicy
      · apply Simulation.Interaction.AllDone.done
        trivial
  | assignTop name =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.done
      trivial
  | assignTopWithOffset offset name =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.done
      trivial
  | promoteName name =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.done
      trivial
  | cleanupTo targetLayout =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.done
      trivial
  | block body =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      exact allDone_bind_fixedContext policy _ _ sourceCtx hPolicy
  | if_ cond body =>
      cases fuel with
      | zero =>
          simp only [Locals.Source.Effectful.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.done
          trivial
      | succ fuel =>
          simp only [Locals.Source.Effectful.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.bind
            (Simulation.Interaction.AllDone.trivial _)
          · intro error _
            trivial
          · intro result _
            rcases result with ⟨stateAfterCond, condTrue⟩
            by_cases hCond : condTrue = true
            · simp only [hCond]
              exact
                allDone_bind_fixedContext policy _ _ sourceCtx hPolicy
            · simp only [hCond]
              apply Simulation.Interaction.AllDone.done
              exact hPolicy
  | switch scrutinee cases defaultBody =>
      cases fuel with
      | zero =>
          simp only [Locals.Source.Effectful.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.done
          trivial
      | succ fuel =>
          simp only [Locals.Source.Effectful.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.bind
            (Simulation.Interaction.AllDone.trivial _)
          · intro error _
            trivial
          · intro result _
            rcases result with ⟨stateAfterScrutinee, value⟩
            cases Source.Switch.select value cases defaultBody with
            | none =>
                apply Simulation.Interaction.AllDone.done
                exact hPolicy
            | some body =>
                exact
                  allDone_bind_fixedContext policy _ _ sourceCtx hPolicy
  | for_ init cond post body =>
      cases fuel with
      | zero =>
          simp only [Locals.Source.Effectful.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.done
          trivial
      | succ fuel =>
          simp only [Locals.Source.Effectful.Control.Stmt.run]
          apply Simulation.Interaction.AllDone.bind
            (Simulation.Interaction.AllDone.trivial _)
          · intro error _
            trivial
          · intro initResult _
            rcases initResult with ⟨initOutcome, initCtx⟩
            cases hMode : initOutcome.mode with
            | regular =>
                apply Simulation.Interaction.AllDone.bind
                  (Simulation.Interaction.AllDone.trivial _)
                · intro error _
                  trivial
                · intro loopOutcome _
                  cases hLoopMode : loopOutcome.mode <;>
                    apply Simulation.Interaction.AllDone.done
                  all_goals first | exact hPolicy | trivial
            | brk | cont =>
                apply Simulation.Interaction.AllDone.done
                trivial
            | leave | halt =>
                apply Simulation.Interaction.AllDone.done
                exact hPolicy
  | brk =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      cases sourceCtx.breakScope? <;>
        apply Simulation.Interaction.AllDone.done
      · trivial
      · exact hPolicy
  | cont =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      cases sourceCtx.continueScope? <;>
        apply Simulation.Interaction.AllDone.done
      · trivial
      · exact hPolicy
  | leave =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      cases sourceCtx.leaveScope? <;>
        apply Simulation.Interaction.AllDone.done
      · trivial
      · exact hPolicy
  | call name =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.done
      trivial
  | terminal kind =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      exact allDone_bind_fixedContext policy _ _ sourceCtx hPolicy
  | terminalArgs kind args =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.bind
        (Simulation.Interaction.AllDone.trivial _)
      · intro error _
        trivial
      · intro result _
        rcases result with ⟨stateAfterArgs, values⟩
        exact allDone_bind_fixedContext policy _ _ sourceCtx hPolicy

theorem allDone_terminal_noLoopExit
    (sourceProgram : Locals.Program)
    (sourceCtx : Locals.Source.Ctx)
    (fuel : Nat) (kind : Assembly.HaltKind)
    (source : Locals.Source.State) :
    Simulation.Interaction.AllDone NoLoopExitOutcome
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel (.terminal kind) source) := by
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run]
  apply Simulation.Interaction.AllDone.bind
    (Simulation.Interaction.AllDone.trivial _)
  · intro error _
    trivial
  · intro final _
    apply Simulation.Interaction.AllDone.done
    constructor <;> intro hMode <;> cases hMode

theorem allDone_terminalArgs_noLoopExit
    (sourceProgram : Locals.Program)
    (sourceCtx : Locals.Source.Ctx)
    (fuel : Nat) (kind : Assembly.HaltKind)
    (args : Locals.ExprSeq kind.argCount)
    (source : Locals.Source.State) :
    Simulation.Interaction.AllDone NoLoopExitOutcome
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel (.terminalArgs kind args) source) := by
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run]
  apply Simulation.Interaction.AllDone.bind
    (Simulation.Interaction.AllDone.trivial _)
  · intro error _
    trivial
  · intro result _
    rcases result with ⟨stateAfterArgs, values⟩
    apply Simulation.Interaction.AllDone.bind
      (Simulation.Interaction.AllDone.trivial _)
    · intro error _
      trivial
    · intro final _
      apply Simulation.Interaction.AllDone.done
      constructor <;> intro hMode <;> cases hMode

theorem allDone_for_noLoopExit
    (sourceProgram : Locals.Program)
    (sourceCtx : Locals.Source.Ctx)
    (fuel : Nat) (init : Locals.Block) (cond : Locals.Expr 1)
    (post body : Locals.Block)
    (source : Locals.Source.State) :
    Simulation.Interaction.AllDone NoLoopExitOutcome
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx fuel (.for_ init cond post body) source) := by
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  cases fuel with
  | zero =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.done
      trivial
  | succ fuel =>
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.AllDone.bind
        (Simulation.Interaction.AllDone.trivial _)
      · intro error _
        trivial
      · intro initResult _
        rcases initResult with ⟨initOutcome, initCtx⟩
        cases hMode : initOutcome.mode with
        | regular =>
            apply Simulation.Interaction.AllDone.bind
              (Simulation.Interaction.AllDone.trivial _)
            · intro error _
              trivial
            · intro loopOutcome _
              cases hLoopMode : loopOutcome.mode with
              | regular =>
                  apply Simulation.Interaction.AllDone.done
                  constructor <;> intro h <;> cases h
              | brk | cont =>
                  apply Simulation.Interaction.AllDone.done
                  trivial
              | leave | halt =>
                  apply Simulation.Interaction.AllDone.done
                  constructor <;> intro h
                  all_goals rw [hLoopMode] at h
                  all_goals cases h
        | brk | cont =>
            apply Simulation.Interaction.AllDone.done
            trivial
        | leave | halt =>
            apply Simulation.Interaction.AllDone.done
            constructor <;> intro h
            all_goals rw [hMode] at h
            all_goals cases h

end Stmt.ControlPolicy

namespace Stmt

theorem RegularResultRel.toPolicyOpen
    {policy : ControlPolicy}
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Locals.Source.Ctx}
    {target : Structured.Outcome}
    (hRel : RegularResultRel finalCtx suffix returns source target)
    (hPolicy :
      ControlPolicy.ContextCompatible policy source.2) :
    PolicyOpenResultRel policy finalCtx suffix returns source target := by
  rcases source with ⟨sourceOutcome, sourceCtx⟩
  rcases sourceOutcome with ⟨sourceState, sourceMode⟩
  rcases target with ⟨targetState, targetMode⟩
  cases hRel.sourceMode
  cases hRel.targetMode
  exact PolicyOpenResultRel.regular hPolicy hRel.context hRel.state

/-- Add the independently checked source control-policy invariant to a
regular adjacent simulation. -/
theorem policyOpen_of_regular
    {policy : ControlPolicy}
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Locals.Source.Ctx)}
    {targetRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hRel :
      Simulation.Interaction.Rel
        (RegularOutcomeRel finalCtx suffix returns)
        sourceRun targetRun)
    (hPolicy :
      Simulation.Interaction.AllDone
        (ControlPolicy.CompatibleOutcome policy) sourceRun) :
    Simulation.Interaction.Rel
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      sourceRun targetRun := by
  have hStrong :=
    Simulation.Interaction.Rel.strengthen_left hRel hPolicy
  apply Simulation.Interaction.Rel.mono hStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRelated, hCompatible⟩
  cases hRelated with
  | error _ =>
      exact Simulation.Interaction.ExceptRel.error trivial
  | ok hRegular =>
      exact
        Simulation.Interaction.ExceptRel.ok
          (hRegular.toPolicyOpen hCompatible)

theorem policyForward_of_regular
    {policy : ControlPolicy}
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Locals.Source.Ctx)}
    {targetRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hRel :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (RegularOutcomeRel finalCtx suffix returns)
        sourceRun targetRun)
    (hPolicy :
      Simulation.Interaction.AllDone
        (ControlPolicy.CompatibleOutcome policy) sourceRun) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      sourceRun targetRun := by
  have hStrong :=
    Simulation.Interaction.ForwardRel.strengthen_left hRel hPolicy
  apply Simulation.Interaction.ForwardRel.mono hStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRelated, hCompatible⟩
  cases hRelated with
  | error _ =>
      exact Simulation.Interaction.ExceptRel.error trivial
  | ok hRegular =>
      exact
        Simulation.Interaction.ExceptRel.ok
          (hRegular.toPolicyOpen hCompatible)

theorem OpenResultRel.toPolicyOpen_of_noLoopExit
    {policy : ControlPolicy}
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source :
      Locals.Source.Effectful.Outcome Locals.Source.State ×
        Locals.Source.Ctx}
    {target : Structured.Outcome}
    (hRel : OpenResultRel finalCtx suffix returns source target)
    (hPolicy : ControlPolicy.ContextCompatible policy source.2)
    (hNoLoopExit :
      source.1.mode ≠ .brk ∧ source.1.mode ≠ .cont)
    (hLeave : ∀ scope, policy.leave scope) :
    PolicyOpenResultRel policy finalCtx suffix returns source target := by
  cases hRel with
  | regular hCtx hState =>
      exact PolicyOpenResultRel.regular hPolicy hCtx hState
  | brk hState =>
      exact False.elim (hNoLoopExit.1 rfl)
  | cont hState =>
      exact False.elim (hNoLoopExit.2 rfl)
  | leave hState =>
      exact PolicyOpenResultRel.leave hPolicy (hLeave _) hState
  | halt hShared hReturns =>
      exact PolicyOpenResultRel.halt hPolicy hShared hReturns

theorem policyForward_of_open_noLoopExit
    {policy : ControlPolicy}
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {sourceRun :
      Simulation.Interaction EVMException
        (Locals.Source.Effectful.Outcome Locals.Source.State ×
          Locals.Source.Ctx)}
    {targetRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hRel :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (OpenOutcomeRel finalCtx suffix returns)
        sourceRun targetRun)
    (hPolicy :
      Simulation.Interaction.AllDone
        (ControlPolicy.CompatibleOutcome policy) sourceRun)
    (hNoLoopExit :
      Simulation.Interaction.AllDone
        ControlPolicy.NoLoopExitOutcome sourceRun)
    (hLeave : ∀ scope, policy.leave scope) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      sourceRun targetRun := by
  have hWithPolicy :=
    Simulation.Interaction.ForwardRel.strengthen_left hRel hPolicy
  have hStrong :=
    Simulation.Interaction.ForwardRel.strengthen_left
      hWithPolicy hNoLoopExit
  apply Simulation.Interaction.ForwardRel.mono hStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨⟨hRelated, hCompatible⟩, hNoLoop⟩
  cases hRelated with
  | error _ =>
      exact Simulation.Interaction.ExceptRel.error trivial
  | ok hOpen =>
      exact
        Simulation.Interaction.ExceptRel.ok
          (hOpen.toPolicyOpen_of_noLoopExit
            hCompatible hNoLoop hLeave)

end Stmt

namespace Stmt.Forward

theorem policy_expr_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (expr : Locals.Expr 0)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 2 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.expr expr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hScoped : Scope.ExprScoped targetCtx.layout expr)
    (hSupported : InteractionSemantics.Expr.OpenSupported expr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 2
  have hFuelEq : targetFuel = extra + 2 := by
    omega
  have hRel :=
    openRun_expr_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra expr hCompile hCtx hScoped hSupported hInitial
  have hAll :=
    ControlPolicy.allDone_openRun
      policy sourceProgram sourceCtx (extra + 1) (.expr expr) source
      hPolicy
  have hPolicyRel := policyOpen_of_regular hRel hAll
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel (.expr expr) source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx (extra + 1) (.expr expr) source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact Simulation.Interaction.ForwardRel.ofRel hPolicyRel

theorem policy_let_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Locals.Expr 1)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 2 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.let_ name valueExpr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Scope.ExprScoped targetCtx.layout valueExpr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel
          (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 2
  have hFuelEq : targetFuel = extra + 2 := by
    omega
  have hRel :=
    openRun_let_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra valueExpr hCompile hCtx hFresh hScoped hSupported hInitial
  have hAll :=
    ControlPolicy.allDone_openRun
      policy sourceProgram sourceCtx (extra + 1)
      (.let_ name valueExpr) source hPolicy
  have hPolicyRel := policyOpen_of_regular hRel hAll
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel
            (.let_ name valueExpr) source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx (extra + 1)
            (.let_ name valueExpr) source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact Simulation.Interaction.ForwardRel.ofRel hPolicyRel

theorem policy_assign_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {name : Name} (valueExpr : Locals.Expr 1)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 2 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.assign name valueExpr) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Scope.ExprScoped targetCtx.layout valueExpr)
    (hSupported :
      InteractionSemantics.Expr.OpenSupported valueExpr)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel
          (.assign name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  let extra := targetFuel - 2
  have hFuelEq : targetFuel = extra + 2 := by
    omega
  have hRel :=
    openRun_assign_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      extra valueExpr hCompile hCtx hNodup hScoped hSupported hInitial
  have hAll :=
    ControlPolicy.allDone_openRun
      policy sourceProgram sourceCtx (extra + 1)
      (.assign name valueExpr) source hPolicy
  have hPolicyRel := policyOpen_of_regular hRel hAll
  have hSourceEq :
      InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel
            (.assign name valueExpr) source =
        InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx (extra + 1)
            (.assign name valueExpr) source := by
    unfold InteractionSemantics.Stmt.openRun
      InteractionSemantics.stateModel
      Locals.Source.Effectful.Ordinary.stateModel
    simp only [Locals.Source.Effectful.Control.Stmt.run]
  rw [hSourceEq, hFuelEq]
  exact Simulation.Interaction.ForwardRel.ofRel hPolicyRel

theorem policy_terminal_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (kind : Assembly.HaltKind)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.terminal kind) =
        some (stmts, finalCtx))
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hLeave : ∀ scope, policy.leave scope)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hArgCount : kind.argCount = 0)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.terminal kind) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  apply policyForward_of_open_noLoopExit
    (terminal_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel kind hTargetFuel hCompile hCtx
      hArgCount hInitial)
  · exact
      ControlPolicy.allDone_openRun
        policy sourceProgram sourceCtx sourceFuel (.terminal kind)
        source hPolicy
  · exact
      ControlPolicy.allDone_terminal_noLoopExit
        sourceProgram sourceCtx sourceFuel kind source
  · exact hLeave

theorem policy_terminalArgs_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (kind : Assembly.HaltKind)
    (args : Locals.ExprSeq kind.argCount)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 3 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.terminalArgs kind args) =
        some (stmts, finalCtx))
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hLeave : ∀ scope, policy.leave scope)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScoped : Scope.ExprSeqScoped targetCtx.layout args)
    (hSupported : InteractionSemantics.ExprSeq.OpenSupported args)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel
          (.terminalArgs kind args) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  apply policyForward_of_open_noLoopExit
    (terminalArgs_of_compile
      sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel kind args hTargetFuel hCompile hCtx
      hScoped hSupported hInitial)
  · exact
      ControlPolicy.allDone_openRun
        policy sourceProgram sourceCtx sourceFuel
        (.terminalArgs kind args) source hPolicy
  · exact
      ControlPolicy.allDone_terminalArgs_noLoopExit
        sourceProgram sourceCtx sourceFuel kind args source
  · exact hLeave

theorem policy_for_of_forward
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (sourceCtx : Locals.Source.Ctx)
    (sourceFuel : Nat)
    (init : Locals.Block) (cond : Locals.Expr 1)
    (post body : Locals.Block)
    {finalCtx : Locals.Ctx}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {targetRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hLeave : ∀ scope, policy.leave scope)
    (hForward :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (OpenOutcomeRel finalCtx suffix returns)
        (InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx (sourceFuel + 1)
            (.for_ init cond post body) source)
        targetRun) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.for_ init cond post body) source)
      targetRun := by
  apply policyForward_of_open_noLoopExit hForward
  · exact
      ControlPolicy.allDone_openRun
        policy sourceProgram sourceCtx (sourceFuel + 1)
        (.for_ init cond post body) source hPolicy
  · exact
      ControlPolicy.allDone_for_noLoopExit
        sourceProgram sourceCtx (sourceFuel + 1)
        init cond post body source
  · exact hLeave

/-- Policy-indexed scoped cleanup, owned by the Locals control proof layer. -/
theorem policyScopedBlock_generated
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (body : Locals.Block)
    (bodyCode : List Expressions.Stmt) (cleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hLayout : ∃ pre, bodyCtx.layout = pre ++ targetCtx.layout)
    (hCleanup :
      bodyCtx.cleanupTo? targetCtx.layout.length = some cleanup)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (PolicyOpenOutcomeRel policy bodyCtx suffix returns)
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyScopedOutcomeRel policy targetCtx suffix returns)
      (InteractionSemantics.Block.openRunScoped
        sourceProgram sourceCtx body sourceFuel source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := bodyCode ++ Locals.codeStmt cleanup } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  unfold InteractionSemantics.Block.openRunScoped
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  unfold Locals.Source.Effectful.Control.Block.runScoped
  change
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyScopedOutcomeRel policy targetCtx suffix returns)
      (Simulation.Interaction.bind
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        _)
      _
  apply Simulation.Interaction.ForwardRel.bind hBody
  intro sourceResult targetResult hResult
  cases hResult with
  | @regular sourceAfter sourceAfterCtx targetAfter
      hPolicyCtx hInnerCtx hState =>
      obtain ⟨pre, hLayout⟩ := hLayout
      obtain ⟨afterCleanup, hCleanupRun, hFinal⟩ :=
        hState.openRun_cleanupTo hLayout hCleanup
      have hTargetCleanup :=
        TargetBlock.openRun_single_code_done
          targetProgram (targetFuel - bodyCode.length)
          cleanup targetAfter afterCleanup
          hCleanupFuel hCleanupRun
      simp only [Structured.Outcome.regular_mode,
        Structured.Outcome.regular_state,
        Locals.Source.Effectful.Outcome.regular,
        Locals.codeStmt]
      rw [hTargetCleanup]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      apply PolicyScopedResultRel.regular
      simpa [hCtx.layout] using hFinal
  | brk hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyScopedResultRel.brk hPolicy hState
  | cont hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyScopedResultRel.cont hPolicy hState
  | leave hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyScopedResultRel.leave hPolicy hState
  | halt hPolicyCtx hShared hReturns =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyScopedResultRel.halt hShared hReturns

/-- A lexical block is the shared policy-indexed scoped child followed by the
unchanged enclosing source context. -/
theorem policy_block_generated
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (body : Locals.Block)
    (bodyCode : List Expressions.Stmt) (cleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hLayout : ∃ pre, bodyCtx.layout = pre ++ targetCtx.layout)
    (hCleanup :
      bodyCtx.cleanupTo? targetCtx.layout.length = some cleanup)
    (hCleanupFuel : 2 ≤ targetFuel - bodyCode.length)
    (hBody :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (PolicyOpenOutcomeRel policy bodyCtx suffix returns)
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel body source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := bodyCode } target)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.block body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := bodyCode ++ Locals.codeStmt cleanup } target) := by
  have hScoped :=
    policyScopedBlock_generated
      policy sourceProgram targetProgram sourceCtx targetCtx bodyCtx
      sourceFuel targetFuel body bodyCode cleanup
      hCtx hLayout hCleanup hCleanupFuel hBody
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Stmt.run]
  exact policy_forward_scoped_withContext hPolicy hCtx hScoped

theorem policy_block_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat) (body : Locals.Block)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hOwned : Locals.Source.Block.SourceOwned body)
    (hTargetFuel : stmts.length + 1 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx (.block body) =
        some (stmts, finalCtx))
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hBody :
      ∀ {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx body =
            some (bodyCode, bodyCtx) →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel policy bodyCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceCtx sourceFuel body source)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram targetFuel
                { stmts := bodyCode } target)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.block body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  obtain ⟨bodyCode, bodyCtx, lowerBody,
    hBodyCompile, hFinish, hCode, hFinal⟩ :=
    Locals.Stmt.compile_block_components hCompile
  obtain ⟨cleanup, hCleanup, hLowerBody⟩ :=
    Locals.finishScoped_components hFinish
  subst finalCtx
  subst stmts
  rw [hLowerBody] at hTargetFuel ⊢
  have hLayout :=
    Locals.Block.compileOpen_layout_extends_of_sourceOwned
      hOwned hBodyCompile
  have hCleanupFuel : 2 ≤ targetFuel - bodyCode.length := by
    have hLen : bodyCode.length + 2 ≤ targetFuel := by
      simpa [Locals.codeStmt, List.length_append] using hTargetFuel
    omega
  exact
    policy_block_generated
      policy sourceProgram targetProgram sourceCtx targetCtx bodyCtx
      sourceFuel targetFuel body bodyCode cleanup
      hPolicy hCtx hLayout hCleanup hCleanupFuel
      (hBody hBodyCompile)

theorem policy_if_generated
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx bodyCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (cond : Locals.Expr 1) (body : Locals.Block)
    (condCode : Structured.Code)
    (bodyCode : List Expressions.Stmt) (cleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : bodyCode.length + 4 ≤ targetFuel)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hCondScoped : Scope.ExprScoped targetCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode targetCtx 0 cond = some condCode)
    (hLayout : ∃ pre, bodyCtx.layout = pre ++ targetCtx.layout)
    (hCleanup :
      bodyCtx.cleanupTo? targetCtx.layout.length = some cleanup)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hBody :
      ∀ {sourceAfter : Locals.Source.State}
        {targetAfter : Structured.RunState},
        Frame.StateRel targetCtx.layout suffix returns
            sourceAfter targetAfter →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel policy bodyCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceCtx sourceFuel body sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetFuel - 2)
                { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts :=
              [Expressions.Stmt.if_ (.code condCode)
                { stmts :=
                    bodyCode ++ Locals.codeStmt cleanup }] }
          target) := by
  rw [TargetBlock.openRun_single_stmt_of_fuel
    targetProgram targetFuel _ target (by omega)]
  have hTargetStmtFuel :
      targetFuel - 1 = (targetFuel - 2) + 1 := by
    omega
  rw [hTargetStmtFuel]
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
    Expressions.InteractionSemantics.Stmt.openRun
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  have hCond :=
    Expr.openEvalCondition_compileCode
      cond targetCtx hCondScoped hCondSupported hCondCompile hInitial
  apply Simulation.Interaction.ForwardRel.bind
    (Simulation.Interaction.ForwardRel.ofRel hCond)
  intro sourceResult targetResult hResult
  rcases sourceResult with ⟨sourceAfter, sourceCond⟩
  rcases targetResult with ⟨targetAfter, targetCond⟩
  cases hResult.condition
  cases sourceCond with
  | false =>
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact PolicyOpenResultRel.regular hPolicy hCtx hResult.state
  | true =>
      have hCleanupFuel :
          2 ≤ (targetFuel - 2) - bodyCode.length := by
        omega
      have hScoped :=
        policyScopedBlock_generated
          policy sourceProgram targetProgram sourceCtx targetCtx bodyCtx
          sourceFuel (targetFuel - 2) body bodyCode cleanup
          hCtx hLayout hCleanup hCleanupFuel (hBody hResult.state)
      exact policy_forward_scoped_withContext hPolicy hCtx hScoped

theorem policy_if_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (cond : Locals.Expr 1) (body : Locals.Block)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hOwned : Locals.Source.Block.SourceOwned body)
    (hCompile :
      Locals.Stmt.compile targetCtx (.if_ cond body) =
        some (stmts, finalCtx))
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hCondScoped : Scope.ExprScoped targetCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hBody :
      ∀ {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx body =
            some (bodyCode, bodyCtx) →
          bodyCode.length + 4 ≤ targetFuel ∧
          ∀ {sourceAfter : Locals.Source.State}
            {targetAfter : Structured.RunState},
            Frame.StateRel targetCtx.layout suffix returns
                sourceAfter targetAfter →
              Simulation.Interaction.ForwardRel
                Block.FuelTruncated
                (PolicyOpenOutcomeRel policy bodyCtx suffix returns)
                (InteractionSemantics.Block.openRun
                  sourceProgram sourceCtx sourceFuel body sourceAfter)
                (Expressions.InteractionSemantics.Block.openRun
                  targetProgram (targetFuel - 2)
                    { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.if_ cond body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  obtain ⟨condCode, bodyCode, bodyCtx, lowerBody,
    hCondCompile, hBodyCompile, hFinish, hCode, hFinal⟩ :=
    Locals.Stmt.compile_if_components hCompile
  obtain ⟨cleanup, hCleanup, hLowerBody⟩ :=
    Locals.finishScoped_components hFinish
  obtain ⟨hTargetFuel, hBodyForward⟩ := hBody hBodyCompile
  have hLayout :=
    Locals.Block.compileOpen_layout_extends_of_sourceOwned
      hOwned hBodyCompile
  subst finalCtx
  subst stmts
  subst lowerBody
  exact
    policy_if_generated
      policy sourceProgram targetProgram sourceCtx targetCtx bodyCtx
      sourceFuel targetFuel cond body condCode bodyCode cleanup
      hTargetFuel hPolicy hCtx hCondScoped hCondSupported hCondCompile
      hLayout hCleanup hInitial hBodyForward

theorem policy_switch_generated
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (scrutinee : Locals.Expr 1)
    (cases : List (Word × Locals.Block))
    (defaultBody : Option Locals.Block)
    (scrutineeCode : Structured.Code)
    (compiledCases : List (Word × Expressions.Block))
    (compiledDefault : Option Expressions.Block)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 4 ≤ targetFuel)
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScrutineeScoped : Scope.ExprScoped targetCtx.layout scrutinee)
    (hScrutineeSupported :
      InteractionSemantics.Expr.OpenSupported scrutinee)
    (hScrutineeCompile :
      Locals.Expr.compileCode targetCtx 0 scrutinee =
        some scrutineeCode)
    (hCases :
      Locals.CaseList.compile targetCtx cases = some compiledCases)
    (hDefault :
      Locals.Default.compile targetCtx defaultBody =
        some compiledDefault)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hSelected :
      ∀ {selected : Locals.Block}
        {selectedTarget : Expressions.Block}
        {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx}
        (value : Word),
        Locals.Source.Switch.select value cases defaultBody =
            some selected →
        Locals.Block.compileOpen targetCtx selected =
            some (bodyCode, bodyCtx) →
          Locals.finishScoped targetCtx bodyCtx bodyCode =
            some selectedTarget →
          bodyCode.length + 4 ≤ targetFuel ∧
            (∃ pre, bodyCtx.layout = pre ++ targetCtx.layout) ∧
            ∀ {sourceAfter : Locals.Source.State}
              {targetAfter : Structured.RunState},
              Frame.StateRel targetCtx.layout suffix returns
                  sourceAfter targetAfter →
                Simulation.Interaction.ForwardRel
                  Block.FuelTruncated
                  (PolicyOpenOutcomeRel policy bodyCtx suffix returns)
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceCtx sourceFuel selected sourceAfter)
                  (Expressions.InteractionSemantics.Block.openRun
                    targetProgram (targetFuel - 2)
                      { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.switch scrutinee cases defaultBody) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts :=
              [Expressions.Stmt.switch (.code scrutineeCode)
                compiledCases compiledDefault] }
          target) := by
  rw [TargetBlock.openRun_single_stmt_of_fuel
    targetProgram targetFuel _ target (by omega)]
  have hTargetStmtFuel :
      targetFuel - 1 = (targetFuel - 2) + 1 := by
    omega
  rw [hTargetStmtFuel]
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
    Expressions.InteractionSemantics.Stmt.openRun
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  have hScrutinee :=
    Expr.openEvalOne_compileCode
      scrutinee targetCtx 0 hScrutineeScoped hScrutineeSupported
      hScrutineeCompile hInitial.expr
  apply Simulation.Interaction.ForwardRel.bind
    (Simulation.Interaction.ForwardRel.ofRel hScrutinee)
  intro sourceResult targetAfterExpr hExpr
  rcases sourceResult with ⟨sourceAfter, value⟩
  let targetAfter :=
    targetAfterExpr.withEVM
      { targetAfterExpr.evm with stack := target.evm.stack }
  have hTargetStack :
      targetAfterExpr.evm.stack = value :: target.evm.stack := by
    simpa using hExpr.stack
  have hPop :
      (Structured.EffectSemantics.Ordinary.runStateModel.evm
          targetAfterExpr).stack.pop =
        some (target.evm.stack, value) := by
    rw [Structured.EffectSemantics.Ordinary.runStateModel_evm,
      hTargetStack]
    rfl
  rw [hPop]
  simp only [Structured.EffectSemantics.Ordinary.runStateModel_withEVM,
    Structured.EffectSemantics.Ordinary.runStateModel_evm]
  have hSelect :=
    SwitchCompile.selectedRel_of_compile
      targetCtx value hCases hDefault
  cases hSourceSelect :
      Locals.Source.Switch.select value cases defaultBody with
  | none =>
      cases hTargetSelect :
          Expressions.EffectSemantics.Switch.select
            value compiledCases compiledDefault with
      | none =>
          simp only
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          apply PolicyOpenResultRel.regular hPolicy hCtx
          simpa [targetAfter] using
            Frame.StateRel.ofExprResultOnePop hInitial hExpr
      | some selectedTarget =>
          rw [hSourceSelect, hTargetSelect] at hSelect
          cases hSelect
  | some selected =>
      cases hTargetSelect :
          Expressions.EffectSemantics.Switch.select
            value compiledCases compiledDefault with
      | none =>
          rw [hSourceSelect, hTargetSelect] at hSelect
          cases hSelect
      | some selectedTarget =>
          rw [hSourceSelect, hTargetSelect] at hSelect
          cases hSelect with
          | @some _ _ bodyCode bodyCtx hBodyCompile hFinish =>
              simp only
              obtain ⟨hSelectedFuel, hLayout, hBody⟩ :=
                hSelected value hSourceSelect hBodyCompile hFinish
              obtain ⟨cleanup, hCleanup, hSelectedTarget⟩ :=
                Locals.finishScoped_components hFinish
              subst selectedTarget
              have hCleanupFuel :
                  2 ≤ (targetFuel - 2) - bodyCode.length := by
                omega
              have hScoped :=
                policyScopedBlock_generated
                  policy sourceProgram targetProgram sourceCtx targetCtx
                  bodyCtx sourceFuel (targetFuel - 2) selected bodyCode
                  cleanup hCtx hLayout hCleanup hCleanupFuel
                  (hBody (by
                    simpa [targetAfter] using
                      Frame.StateRel.ofExprResultOnePop hInitial hExpr))
              exact
                policy_forward_scoped_withContext hPolicy hCtx hScoped

theorem policy_switch_of_compile
    (policy : ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (scrutinee : Locals.Expr 1)
    (cases : List (Word × Locals.Block))
    (defaultBody : Option Locals.Block)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 4 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile targetCtx
          (.switch scrutinee cases defaultBody) =
        some (stmts, finalCtx))
    (hPolicy : ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hScrutineeScoped : Scope.ExprScoped targetCtx.layout scrutinee)
    (hScrutineeSupported :
      InteractionSemantics.Expr.OpenSupported scrutinee)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target)
    (hSelected :
      ∀ {selected : Locals.Block}
        {selectedTarget : Expressions.Block}
        {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx}
        (value : Word),
        Locals.Source.Switch.select value cases defaultBody =
            some selected →
        Locals.Block.compileOpen targetCtx selected =
            some (bodyCode, bodyCtx) →
          Locals.finishScoped targetCtx bodyCtx bodyCode =
            some selectedTarget →
          bodyCode.length + 4 ≤ targetFuel ∧
            (∃ pre, bodyCtx.layout = pre ++ targetCtx.layout) ∧
            ∀ {sourceAfter : Locals.Source.State}
              {targetAfter : Structured.RunState},
              Frame.StateRel targetCtx.layout suffix returns
                  sourceAfter targetAfter →
                Simulation.Interaction.ForwardRel
                  Block.FuelTruncated
                  (PolicyOpenOutcomeRel policy bodyCtx suffix returns)
                  (InteractionSemantics.Block.openRun
                    sourceProgram sourceCtx sourceFuel selected sourceAfter)
                  (Expressions.InteractionSemantics.Block.openRun
                    targetProgram (targetFuel - 2)
                      { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.switch scrutinee cases defaultBody) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := stmts } target) := by
  obtain ⟨scrutineeCode, compiledCases, compiledDefault,
    hScrutineeCompile, hCases, hDefault, hCode, hFinal⟩ :=
    Locals.Stmt.compile_switch_components hCompile
  subst finalCtx
  subst stmts
  exact
    policy_switch_generated
      policy sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel scrutinee cases defaultBody
      scrutineeCode compiledCases compiledDefault
      hTargetFuel hPolicy hCtx hScrutineeScoped hScrutineeSupported
      hScrutineeCompile hCases hDefault hInitial hSelected

/-- Fuel-aligned recursion for the canonical source and target loop owners. -/
theorem forLoop_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (loopSourceCtx postSourceCtx bodySourceCtx : Locals.Source.Ctx)
    (loopTargetCtx postTargetCtx bodyTargetCtx : Locals.Ctx)
    (postFinalCtx bodyFinalCtx : Locals.Ctx)
    (slack : Nat)
    (cond : Locals.Expr 1) (post body : Locals.Block)
    (condCode : Structured.Code)
    (postCode bodyCode : List Expressions.Stmt)
    (postCleanup bodyCleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    (hLoopCtx : Frame.CtxRel loopSourceCtx loopTargetCtx)
    (hPostCtx : Frame.CtxRel postSourceCtx postTargetCtx)
    (hBodyCtx : Frame.CtxRel bodySourceCtx bodyTargetCtx)
    (hPostTargetLayout :
      postTargetCtx.layout = loopTargetCtx.layout)
    (hBodyTargetLayout :
      bodyTargetCtx.layout = loopTargetCtx.layout)
    (hPostLayout :
      ∃ pre, postFinalCtx.layout = pre ++ postTargetCtx.layout)
    (hBodyLayout :
      ∃ pre, bodyFinalCtx.layout = pre ++ bodyTargetCtx.layout)
    (hPostCleanup :
      postFinalCtx.cleanupTo? postTargetCtx.layout.length =
        some postCleanup)
    (hBodyCleanup :
      bodyFinalCtx.cleanupTo? bodyTargetCtx.layout.length =
        some bodyCleanup)
    (hPostSlack : postCode.length + 2 ≤ slack)
    (hBodySlack : bodyCode.length + 2 ≤ slack)
    (hCondScoped : Scope.ExprScoped loopTargetCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode loopTargetCtx 0 cond = some condCode)
    (hPost :
      ∀ (fuel : Nat)
        {source : Locals.Source.State}
        {target : Structured.RunState},
        Frame.StateRel loopTargetCtx.layout suffix returns source target →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel ControlPolicy.noLoop
              postFinalCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram postSourceCtx fuel post source)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + slack)
                { stmts := postCode } target))
    (hBody :
      ∀ (fuel : Nat)
        {source : Locals.Source.State}
        {target : Structured.RunState},
        Frame.StateRel loopTargetCtx.layout suffix returns source target →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel
              (ControlPolicy.loop loopSourceCtx.scope)
              bodyFinalCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram bodySourceCtx fuel body source)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + slack)
                { stmts := bodyCode } target)) :
    ∀ (fuel : Nat)
      {source : Locals.Source.State}
      {target : Structured.RunState},
      Frame.StateRel loopTargetCtx.layout suffix returns source target →
        Simulation.Interaction.ForwardRel
          Block.FuelTruncated
          (PolicyScopedOutcomeRel ControlPolicy.noLoop
            loopTargetCtx suffix returns)
          (InteractionSemantics.Stmt.openRunForLoop
            sourceProgram loopSourceCtx cond postSourceCtx post
              bodySourceCtx body fuel source)
          (Expressions.InteractionSemantics.Stmt.openRunForLoop
            targetProgram (fuel + slack) (.code condCode)
              { stmts := postCode ++ Locals.codeStmt postCleanup }
              { stmts := bodyCode ++ Locals.codeStmt bodyCleanup }
              target) := by
  intro fuel
  induction fuel with
  | zero =>
      intro source target hInitial
      unfold InteractionSemantics.Stmt.openRunForLoop
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Stmt.runForLoop]
      apply Simulation.Interaction.ForwardRel.truncated
      rfl
  | succ fuel ih =>
      intro source target hInitial
      have hTargetFuel :
          fuel + 1 + slack = (fuel + slack) + 1 := by
        omega
      rw [hTargetFuel]
      unfold InteractionSemantics.Stmt.openRunForLoop
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
        Expressions.InteractionSemantics.Stmt.openRunForLoop
      simp only [Locals.Source.Effectful.Control.Stmt.runForLoop,
        Expressions.EffectSemantics.Control.Stmt.runForLoop]
      have hCond :=
        Expr.openEvalCondition_compileCode
          cond loopTargetCtx hCondScoped hCondSupported
          hCondCompile hInitial
      apply Simulation.Interaction.ForwardRel.bind
        (Simulation.Interaction.ForwardRel.ofRel hCond)
      intro sourceResult targetResult hResult
      rcases sourceResult with ⟨sourceAfterCond, sourceCond⟩
      rcases targetResult with ⟨targetAfterCond, targetCond⟩
      cases hResult.condition
      cases sourceCond with
      | false =>
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          apply PolicyScopedResultRel.regular
          simpa [hLoopCtx.layout] using hResult.state.restrictSelf
      | true =>
          have hBodyCleanupFuel :
              2 ≤ (fuel + slack) - bodyCode.length := by
            omega
          have hBodyScoped :=
            policyScopedBlock_generated
              (ControlPolicy.loop loopSourceCtx.scope)
              sourceProgram targetProgram bodySourceCtx
              bodyTargetCtx bodyFinalCtx fuel (fuel + slack)
              body bodyCode bodyCleanup hBodyCtx hBodyLayout
              hBodyCleanup hBodyCleanupFuel (hBody fuel hResult.state)
          have hPostCleanupFuel :
              2 ≤ (fuel + slack) - postCode.length := by
            omega
          have hContinue :
              ∀ {sourceAfter : Locals.Source.State}
                {targetAfter : Structured.RunState},
                Frame.StateRel loopTargetCtx.layout suffix returns
                    sourceAfter targetAfter →
                  Simulation.Interaction.ForwardRel
                    Block.FuelTruncated
                    (PolicyScopedOutcomeRel ControlPolicy.noLoop
                      loopTargetCtx suffix returns)
                    (Simulation.Interaction.bind
                      (InteractionSemantics.Block.openRunScoped
                        sourceProgram postSourceCtx post fuel sourceAfter)
                      (fun postOutcome =>
                        match postOutcome.mode with
                        | .regular =>
                            InteractionSemantics.Stmt.openRunForLoop
                              sourceProgram loopSourceCtx cond
                              postSourceCtx post bodySourceCtx body
                              fuel postOutcome.state
                        | .brk | .cont =>
                            Simulation.Interaction.error
                              (.InvalidInstruction : EVMException)
                        | .leave | .halt _ =>
                            Simulation.Interaction.pure postOutcome))
                    (Simulation.Interaction.bind
                      (Expressions.InteractionSemantics.Block.openRun
                        targetProgram (fuel + slack)
                          { stmts :=
                              postCode ++ Locals.codeStmt postCleanup }
                          targetAfter)
                      (fun postOutcome =>
                        match postOutcome.mode with
                        | .regular =>
                            Expressions.InteractionSemantics.Stmt.openRunForLoop
                              targetProgram (fuel + slack)
                              (.code condCode)
                              { stmts :=
                                  postCode ++ Locals.codeStmt postCleanup }
                              { stmts :=
                                  bodyCode ++ Locals.codeStmt bodyCleanup }
                              postOutcome.state
                        | .brk | .cont =>
                            Simulation.Interaction.error
                              (.InvalidInstruction : EVMException)
                        | .leave | .halt _ =>
                            Simulation.Interaction.pure postOutcome)) := by
            intro sourceAfter targetAfter hAfter
            have hPostScoped :=
              policyScopedBlock_generated
                ControlPolicy.noLoop sourceProgram targetProgram
                postSourceCtx postTargetCtx postFinalCtx
                fuel (fuel + slack) post postCode postCleanup
                hPostCtx hPostLayout hPostCleanup hPostCleanupFuel
                (hPost fuel (by
                  simpa [hPostTargetLayout] using hAfter))
            apply Simulation.Interaction.ForwardRel.bind hPostScoped
            intro sourcePost targetPost hPostResult
            cases hPostResult with
            | regular hPostState =>
                exact ih (by
                  simpa [hPostTargetLayout] using hPostState)
            | brk hImpossible hPostState =>
                exact False.elim hImpossible
            | cont hImpossible hPostState =>
                exact False.elim hImpossible
            | leave hPolicy hPostState =>
                apply Simulation.Interaction.ForwardRel.done
                apply Simulation.Interaction.ExceptRel.ok
                exact PolicyScopedResultRel.leave trivial hPostState
            | halt hShared hReturns =>
                apply Simulation.Interaction.ForwardRel.done
                apply Simulation.Interaction.ExceptRel.ok
                exact PolicyScopedResultRel.halt hShared hReturns
          apply Simulation.Interaction.ForwardRel.bind hBodyScoped
          intro sourceBody targetBody hBodyResult
          cases hBodyResult with
          | regular hBodyState =>
              exact hContinue (by
                simpa [hBodyTargetLayout] using hBodyState)
          | brk hFrame hBodyState =>
              cases hFrame
              apply Simulation.Interaction.ForwardRel.done
              apply Simulation.Interaction.ExceptRel.ok
              apply PolicyScopedResultRel.regular
              simpa [hLoopCtx.layout] using hBodyState
          | cont hFrame hBodyState =>
              cases hFrame
              exact hContinue (by
                simpa [hLoopCtx.layout] using hBodyState)
          | leave hPolicy hBodyState =>
              apply Simulation.Interaction.ForwardRel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact PolicyScopedResultRel.leave trivial hBodyState
          | halt hShared hReturns =>
              apply Simulation.Interaction.ForwardRel.done
              apply Simulation.Interaction.ExceptRel.ok
              exact PolicyScopedResultRel.halt hShared hReturns

/-- Compose initializer, recursive loop, and outer lexical cleanup. -/
theorem for_generated
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (targetCtx initTargetCtx postFinalCtx bodyFinalCtx : Locals.Ctx)
    (sourceFuel slack : Nat)
    (init : Locals.Block) (cond : Locals.Expr 1)
    (post body : Locals.Block)
    (initCode postCode bodyCode : List Expressions.Stmt)
    (condCode : Structured.Code)
    (postCleanup bodyCleanup outerCleanup : Structured.Code)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hOuterLayout :
      ∃ pre, initTargetCtx.layout = pre ++ targetCtx.layout)
    (hOuterCleanup :
      initTargetCtx.cleanupTo? targetCtx.layout.length =
        some outerCleanup)
    (hPostLayout :
      ∃ pre,
        postFinalCtx.layout =
          pre ++ initTargetCtx.withoutLoopControl.layout)
    (hBodyLayout :
      ∃ pre,
        bodyFinalCtx.layout =
          pre ++
            (initTargetCtx.withLoopControl
              initTargetCtx.layout.length).layout)
    (hPostCleanup :
      postFinalCtx.cleanupTo?
          initTargetCtx.withoutLoopControl.layout.length =
        some postCleanup)
    (hBodyCleanup :
      bodyFinalCtx.cleanupTo?
          (initTargetCtx.withLoopControl
            initTargetCtx.layout.length).layout.length =
        some bodyCleanup)
    (hInitSlack : initCode.length + 1 ≤ slack)
    (hPostSlack : postCode.length + 2 ≤ slack)
    (hBodySlack : bodyCode.length + 2 ≤ slack)
    (hCondScoped : Scope.ExprScoped initTargetCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hCondCompile :
      Locals.Expr.compileCode initTargetCtx 0 cond = some condCode)
    (hInit :
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (PolicyOpenOutcomeRel ControlPolicy.noLoop
          initTargetCtx suffix returns)
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx.withoutLoopControl
            sourceFuel init source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram (sourceFuel + slack)
            { stmts := initCode } target))
    (hPost :
      ∀ {loopSourceCtx : Locals.Source.Ctx}
        (fuel : Nat)
        {sourceAfter : Locals.Source.State}
        {targetAfter : Structured.RunState},
        Frame.CtxRel loopSourceCtx initTargetCtx →
        Frame.StateRel initTargetCtx.layout suffix returns
            sourceAfter targetAfter →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel ControlPolicy.noLoop
              postFinalCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram loopSourceCtx.withoutLoopControl
                fuel post sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + slack)
                { stmts := postCode } targetAfter))
    (hBody :
      ∀ {loopSourceCtx : Locals.Source.Ctx}
        (fuel : Nat)
        {sourceAfter : Locals.Source.State}
        {targetAfter : Structured.RunState},
        Frame.CtxRel loopSourceCtx initTargetCtx →
        Frame.StateRel initTargetCtx.layout suffix returns
            sourceAfter targetAfter →
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel
              (ControlPolicy.loop loopSourceCtx.scope)
              bodyFinalCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram
                (loopSourceCtx.withLoopControl
                  loopSourceCtx.scope loopSourceCtx.scope)
                fuel body sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (fuel + slack)
                { stmts := bodyCode } targetAfter)) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel targetCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.for_ init cond post body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (sourceFuel + slack + 2)
          { stmts :=
              [Expressions.Stmt.for_
                { stmts := initCode } (.code condCode)
                { stmts := postCode ++ Locals.codeStmt postCleanup }
                { stmts := bodyCode ++ Locals.codeStmt bodyCleanup }] ++
                Locals.codeStmt outerCleanup }
          target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  have hHeadFuel :
      sourceFuel + slack + 2 = (sourceFuel + slack) + 2 := by
    omega
  rw [hHeadFuel, TargetBlock.openRun_single_stmt]
  unfold InteractionSemantics.Stmt.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
    Expressions.InteractionSemantics.Stmt.openRun
  simp only [Locals.Source.Effectful.Control.Stmt.run,
    Expressions.EffectSemantics.Control.Stmt.run]
  change
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel targetCtx suffix returns)
      (Simulation.Interaction.bind
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx.withoutLoopControl
            sourceFuel init source)
        _)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Expressions.InteractionSemantics.Block.openRun
            targetProgram (sourceFuel + slack)
              { stmts := initCode } target)
          _)
        _)
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.ForwardRel.bind hInit
  intro sourceInit targetInit hInitResult
  cases hInitResult with
  | @regular sourceAfter sourceAfterCtx targetAfter
      hInitPolicy hInitCtx hInitState =>
      have hLoop :=
        forLoop_generated
          sourceProgram targetProgram sourceAfterCtx
          sourceAfterCtx.withoutLoopControl
          (sourceAfterCtx.withLoopControl
            sourceAfterCtx.scope sourceAfterCtx.scope)
          initTargetCtx initTargetCtx.withoutLoopControl
          (initTargetCtx.withLoopControl initTargetCtx.layout.length)
          postFinalCtx bodyFinalCtx slack cond post body
          condCode postCode bodyCode postCleanup bodyCleanup
          hInitCtx hInitCtx.withoutLoopControl hInitCtx.withLoopControl
          rfl rfl hPostLayout hBodyLayout hPostCleanup hBodyCleanup
          hPostSlack hBodySlack hCondScoped hCondSupported hCondCompile
          (fun fuel {source} {target} hState =>
            hPost (sourceAfter := source) (targetAfter := target)
              fuel hInitCtx hState)
          (fun fuel {source} {target} hState =>
            hBody (sourceAfter := source) (targetAfter := target)
              fuel hInitCtx hState)
          sourceFuel hInitState
      apply Simulation.Interaction.ForwardRel.bind hLoop
      intro sourceLoop targetLoop hLoopResult
      cases hLoopResult with
      | @regular sourceFinal targetFinal hLoopState =>
          obtain ⟨pre, hOuterLayout⟩ := hOuterLayout
          obtain ⟨afterCleanup, hCleanupRun, hFinal⟩ :=
            hLoopState.openRun_cleanupTo hOuterLayout hOuterCleanup
          have hCleanupFuel :
              2 ≤ sourceFuel + slack + 2 - 1 := by
            omega
          have hTargetCleanup :=
            TargetBlock.openRun_single_code_done
              targetProgram (sourceFuel + slack + 2 - 1)
              outerCleanup targetFinal afterCleanup
              hCleanupFuel hCleanupRun
          simp only [Structured.Outcome.regular_mode,
            Structured.Outcome.regular_state,
            Locals.Source.Effectful.Outcome.regular,
            Locals.codeStmt, List.length_singleton]
          rw [hTargetCleanup]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          apply OpenResultRel.regular hCtx
          simpa [hCtx.layout] using hFinal
      | brk hImpossible hState =>
          exact False.elim hImpossible
      | cont hImpossible hState =>
          exact False.elim hImpossible
      | leave hPolicy hState =>
          apply Simulation.Interaction.ForwardRel.ofRel
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact OpenResultRel.leave hState
      | halt hShared hReturns =>
          apply Simulation.Interaction.ForwardRel.ofRel
          apply Simulation.Interaction.Rel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact OpenResultRel.halt hShared hReturns
  | brk hInitPolicy hImpossible hState =>
      exact False.elim hImpossible
  | cont hInitPolicy hImpossible hState =>
      exact False.elim hImpossible
  | leave hInitPolicy hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact OpenResultRel.leave hState
  | halt hInitPolicy hShared hReturns =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact OpenResultRel.halt hShared hReturns

/--
Compiler-facing `for` theorem. Every emitted block, cleanup, layout extension,
and final context is recovered from the ordinary compiler; recursive premises
remain adjacent block-preservation capabilities under explicit control policy.
-/
theorem for_of_compile
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx finalCtx : Locals.Ctx)
    (sourceFuel slack : Nat)
    (init : Locals.Block) (cond : Locals.Expr 1)
    (post body : Locals.Block)
    {stmts : List Expressions.Stmt}
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hOwnedInit : Locals.Source.Block.SourceOwned init)
    (hOwnedPost : Locals.Source.Block.SourceOwned post)
    (hOwnedBody : Locals.Source.Block.SourceOwned body)
    (hCompile :
      Locals.Stmt.compile targetCtx (.for_ init cond post body) =
        some (stmts, finalCtx))
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hCondScoped :
      ∀ {initCode : List Expressions.Stmt} {initCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx.withoutLoopControl init =
            some (initCode, initCtx) →
          Scope.ExprScoped initCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hInit :
      ∀ {initCode : List Expressions.Stmt} {initCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx.withoutLoopControl init =
            some (initCode, initCtx) →
          initCode.length + 1 ≤ slack ∧
          Simulation.Interaction.ForwardRel
            Block.FuelTruncated
            (PolicyOpenOutcomeRel ControlPolicy.noLoop
              initCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceCtx.withoutLoopControl
                sourceFuel init source)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (sourceFuel + slack)
                { stmts := initCode } target))
    (hPost :
      ∀ {initCode : List Expressions.Stmt} {initCtx : Locals.Ctx}
        {postCode : List Expressions.Stmt} {postCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx.withoutLoopControl init =
            some (initCode, initCtx) →
        Locals.Block.compileOpen initCtx.withoutLoopControl post =
            some (postCode, postCtx) →
          postCode.length + 2 ≤ slack ∧
          (∀ {loopSourceCtx : Locals.Source.Ctx}
            (fuel : Nat)
            {sourceAfter : Locals.Source.State}
            {targetAfter : Structured.RunState},
            Frame.CtxRel loopSourceCtx initCtx →
            Frame.StateRel initCtx.layout suffix returns
                sourceAfter targetAfter →
              Simulation.Interaction.ForwardRel
                Block.FuelTruncated
                (PolicyOpenOutcomeRel ControlPolicy.noLoop
                  postCtx suffix returns)
                (InteractionSemantics.Block.openRun
                  sourceProgram loopSourceCtx.withoutLoopControl
                    fuel post sourceAfter)
                (Expressions.InteractionSemantics.Block.openRun
                  targetProgram (fuel + slack)
                    { stmts := postCode } targetAfter)))
    (hBody :
      ∀ {initCode : List Expressions.Stmt} {initCtx : Locals.Ctx}
        {bodyCode : List Expressions.Stmt} {bodyCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx.withoutLoopControl init =
            some (initCode, initCtx) →
        Locals.Block.compileOpen
            (initCtx.withLoopControl initCtx.layout.length) body =
          some (bodyCode, bodyCtx) →
          bodyCode.length + 2 ≤ slack ∧
          (∀ {loopSourceCtx : Locals.Source.Ctx}
            (fuel : Nat)
            {sourceAfter : Locals.Source.State}
            {targetAfter : Structured.RunState},
            Frame.CtxRel loopSourceCtx initCtx →
            Frame.StateRel initCtx.layout suffix returns
                sourceAfter targetAfter →
              Simulation.Interaction.ForwardRel
                Block.FuelTruncated
                (PolicyOpenOutcomeRel
                  (ControlPolicy.loop loopSourceCtx.scope)
                  bodyCtx suffix returns)
                (InteractionSemantics.Block.openRun
                  sourceProgram
                    (loopSourceCtx.withLoopControl
                      loopSourceCtx.scope loopSourceCtx.scope)
                    fuel body sourceAfter)
                (Expressions.InteractionSemantics.Block.openRun
                  targetProgram (fuel + slack)
                    { stmts := bodyCode } targetAfter))) :
    Simulation.Interaction.ForwardRel
      Block.FuelTruncated
      (OpenOutcomeRel finalCtx suffix returns)
      (InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          (.for_ init cond post body) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (sourceFuel + slack + 2)
          { stmts := stmts } target) := by
  obtain ⟨initCode, initCtx, condCode,
    postCode, postCtx, compiledPost,
    bodyCode, bodyCtx, compiledBody, outerCleanup,
    hInitCompile, hCondCompile, hPostCompile, hFinishPost,
    hBodyCompile, hFinishBody, hOuterCleanup, hCode, hFinal⟩ :=
    Locals.Stmt.compile_for_components hCompile
  obtain ⟨postCleanup, hPostCleanup, hCompiledPost⟩ :=
    Locals.finishScoped_components hFinishPost
  obtain ⟨bodyCleanup, hBodyCleanup, hCompiledBody⟩ :=
    Locals.finishScoped_components hFinishBody
  obtain ⟨hInitSlack, hInitForward⟩ := hInit hInitCompile
  obtain ⟨hPostSlack, hPostForward⟩ :=
    hPost hInitCompile hPostCompile
  obtain ⟨hBodySlack, hBodyForward⟩ :=
    hBody hInitCompile hBodyCompile
  have hOuterLayout :=
    Locals.Block.compileOpen_layout_extends_of_sourceOwned
      hOwnedInit hInitCompile
  have hPostLayout :=
    Locals.Block.compileOpen_layout_extends_of_sourceOwned
      hOwnedPost hPostCompile
  have hBodyLayout :=
    Locals.Block.compileOpen_layout_extends_of_sourceOwned
      hOwnedBody hBodyCompile
  subst finalCtx
  subst stmts
  subst compiledPost
  subst compiledBody
  exact
    for_generated
      sourceProgram targetProgram sourceCtx targetCtx initCtx postCtx bodyCtx
      sourceFuel slack init cond post body initCode postCode bodyCode
      condCode postCleanup bodyCleanup outerCleanup
      hCtx hOuterLayout hOuterCleanup hPostLayout hBodyLayout
      hPostCleanup hBodyCleanup hInitSlack hPostSlack hBodySlack
      (hCondScoped hInitCompile) hCondSupported hCondCompile
      hInitForward hPostForward hBodyForward

end Stmt.Forward

namespace Block

theorem policy_openRun_empty
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx) (targetCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hTargetFuel : 1 ≤ targetFuel)
    (hPolicy :
      Stmt.ControlPolicy.ContextCompatible policy sourceCtx)
    (hCtx : Frame.CtxRel sourceCtx targetCtx)
    (hInitial :
      Frame.StateRel targetCtx.layout suffix returns source target) :
    Simulation.Interaction.ForwardRel
      FuelTruncated
      (Stmt.PolicyOpenOutcomeRel policy targetCtx suffix returns)
      (InteractionSemantics.Block.openRun
        sourceProgram sourceCtx sourceFuel { stmts := [] } source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel { stmts := [] } target) := by
  cases sourceFuel with
  | zero =>
      unfold InteractionSemantics.Block.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Block.runOpen]
      apply Simulation.Interaction.ForwardRel.truncated
      rfl
  | succ sourceFuel =>
      cases targetFuel with
      | zero => omega
      | succ targetFuel =>
          unfold InteractionSemantics.Block.openRun
            Expressions.InteractionSemantics.Block.openRun
            InteractionSemantics.stateModel
            Locals.Source.Effectful.Ordinary.stateModel
          simp only [Locals.Source.Effectful.Control.Block.runOpen,
            Expressions.EffectSemantics.Control.Block.run]
          apply Simulation.Interaction.ForwardRel.done
          apply Simulation.Interaction.ExceptRel.ok
          exact
            Stmt.PolicyOpenResultRel.regular
              hPolicy hCtx hInitial

/-- Policy-indexed sequence composition for exact abrupt frames. -/
theorem policy_forward_cons
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (middleCtx finalCtx : Locals.Ctx)
    (sourceFuel targetFuel : Nat)
    (stmt : Locals.Stmt) (rest : List Locals.Stmt)
    (headCode tailCode : List Expressions.Stmt)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hEntryPolicy : Stmt.ControlPolicy.ContextCompatible policy sourceCtx)
    (hHead :
      Simulation.Interaction.ForwardRel
        FuelTruncated
        (Stmt.PolicyOpenOutcomeRel policy middleCtx suffix returns)
        (InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := headCode } target))
    (hTail :
      ∀ {sourceMid : Locals.Source.State}
        {targetMid : Structured.RunState}
        {sourceMidCtx : Locals.Source.Ctx},
        Stmt.ControlPolicy.ContextCompatible policy sourceMidCtx →
        Frame.CtxRel sourceMidCtx middleCtx →
        Frame.StateRel middleCtx.layout suffix returns
            sourceMid targetMid →
          Simulation.Interaction.ForwardRel
            FuelTruncated
            (Stmt.PolicyOpenOutcomeRel policy finalCtx suffix returns)
            (InteractionSemantics.Block.openRun
              sourceProgram sourceMidCtx sourceFuel
                { stmts := rest } sourceMid)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram (targetFuel - headCode.length)
                { stmts := tailCode } targetMid)) :
    Simulation.Interaction.ForwardRel
      FuelTruncated
      (Stmt.PolicyOpenOutcomeRel policy finalCtx suffix returns)
      (InteractionSemantics.Block.openRun
        sourceProgram sourceCtx (sourceFuel + 1)
          { stmts := stmt :: rest } source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram targetFuel
          { stmts := headCode ++ tailCode } target) := by
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  unfold InteractionSemantics.Block.openRun
    InteractionSemantics.stateModel
    Locals.Source.Effectful.Ordinary.stateModel
  simp only [Locals.Source.Effectful.Control.Block.runOpen]
  apply Simulation.Interaction.ForwardRel.bind hHead
  intro sourceResult targetResult hResult
  cases hResult with
  | regular hPolicyCtx hCtx hState =>
      exact hTail hPolicyCtx hCtx hState
  | brk hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.PolicyOpenResultRel.brk hEntryPolicy hPolicy hState
  | cont hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.PolicyOpenResultRel.cont hEntryPolicy hPolicy hState
  | leave hPolicyCtx hPolicy hState =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.PolicyOpenResultRel.leave hEntryPolicy hPolicy hState
  | halt hPolicyCtx hShared hReturns =>
      apply Simulation.Interaction.ForwardRel.ofRel
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact Stmt.PolicyOpenResultRel.halt hEntryPolicy hShared hReturns

/-- Additive-cost wrapper around policy-indexed sequence composition. -/
theorem policy_forward_cons_bounded
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Locals.Source.Ctx)
    (middleCtx finalCtx : Locals.Ctx)
    (stmt : Locals.Stmt) (rest : List Locals.Stmt)
    (headCode tailCode : List Expressions.Stmt)
    (headCost tailCost : Nat)
    {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State}
    {target : Structured.RunState}
    (hEntryPolicy :
      Stmt.ControlPolicy.ContextCompatible policy sourceCtx)
    (hHead :
      ∀ (sourceFuel targetFuel : Nat),
        sourceFuel + headCost ≤ targetFuel →
          Simulation.Interaction.ForwardRel
            FuelTruncated
            (Stmt.PolicyOpenOutcomeRel policy middleCtx suffix returns)
            (InteractionSemantics.Stmt.openRun
              sourceProgram sourceCtx sourceFuel stmt source)
            (Expressions.InteractionSemantics.Block.openRun
              targetProgram targetFuel { stmts := headCode } target))
    (hTail :
      ∀ {sourceMid : Locals.Source.State}
        {targetMid : Structured.RunState}
        {sourceMidCtx : Locals.Source.Ctx},
        Stmt.ControlPolicy.ContextCompatible policy sourceMidCtx →
        Frame.CtxRel sourceMidCtx middleCtx →
        Frame.StateRel middleCtx.layout suffix returns
            sourceMid targetMid →
        ∀ (sourceFuel targetFuel : Nat),
          sourceFuel + tailCost ≤ targetFuel →
            Simulation.Interaction.ForwardRel
              FuelTruncated
              (Stmt.PolicyOpenOutcomeRel policy finalCtx suffix returns)
              (InteractionSemantics.Block.openRun
                sourceProgram sourceMidCtx sourceFuel
                  { stmts := rest } sourceMid)
              (Expressions.InteractionSemantics.Block.openRun
                targetProgram targetFuel
                  { stmts := tailCode } targetMid)) :
    ∀ (sourceFuel targetFuel : Nat),
      sourceFuel +
          (Nat.max headCost (headCode.length + tailCost) + 1) ≤
        targetFuel →
        Simulation.Interaction.ForwardRel
          FuelTruncated
          (Stmt.PolicyOpenOutcomeRel policy finalCtx suffix returns)
          (InteractionSemantics.Block.openRun
            sourceProgram sourceCtx sourceFuel
              { stmts := stmt :: rest } source)
          (Expressions.InteractionSemantics.Block.openRun
            targetProgram targetFuel
              { stmts := headCode ++ tailCode } target) := by
  intro sourceFuel targetFuel hFuel
  cases sourceFuel with
  | zero =>
      unfold InteractionSemantics.Block.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Block.runOpen]
      apply Simulation.Interaction.ForwardRel.truncated
      rfl
  | succ sourceFuel =>
      have hHeadCost :
          headCost ≤ Nat.max headCost (headCode.length + tailCost) :=
        Nat.le_max_left _ _
      have hTailCost :
          headCode.length + tailCost ≤
            Nat.max headCost (headCode.length + tailCost) :=
        Nat.le_max_right _ _
      apply policy_forward_cons
        policy sourceProgram targetProgram sourceCtx middleCtx finalCtx
        sourceFuel targetFuel stmt rest headCode tailCode
        hEntryPolicy
      · apply hHead sourceFuel targetFuel
        omega
      · intro sourceMid targetMid sourceMidCtx
          hPolicy hCtx hState
        apply hTail hPolicy hCtx hState
          sourceFuel (targetFuel - headCode.length)
        omega

end Block

namespace Recursive

def StmtForwardBound
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (stmt : Locals.Stmt)
    (code : List Expressions.Stmt)
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (cost : Nat) : Prop :=
  ∀ (sourceCtx : Locals.Source.Ctx)
    (source : Locals.Source.State)
    (target : Structured.RunState)
    (sourceFuel targetFuel : Nat),
    Stmt.ControlPolicy.ContextCompatible policy sourceCtx →
    Frame.CtxRel sourceCtx targetCtx →
    Frame.StateRel targetCtx.layout suffix returns source target →
    sourceFuel + cost ≤ targetFuel →
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (Stmt.PolicyOpenOutcomeRel policy finalCtx suffix returns)
        (InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := code } target)

def BlockForwardBound
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (block : Locals.Block)
    (code : List Expressions.Stmt)
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (cost : Nat) : Prop :=
  ∀ (sourceCtx : Locals.Source.Ctx)
    (source : Locals.Source.State)
    (target : Structured.RunState)
    (sourceFuel targetFuel : Nat),
    Stmt.ControlPolicy.ContextCompatible policy sourceCtx →
    Frame.CtxRel sourceCtx targetCtx →
    Frame.StateRel targetCtx.layout suffix returns source target →
    sourceFuel + cost ≤ targetFuel →
      Simulation.Interaction.ForwardRel
        Block.FuelTruncated
        (Stmt.PolicyOpenOutcomeRel policy finalCtx suffix returns)
        (InteractionSemantics.Block.openRun
          sourceProgram sourceCtx sourceFuel block source)
        (Expressions.InteractionSemantics.Block.openRun
          targetProgram targetFuel { stmts := code } target)

theorem expr_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (expr : Locals.Expr 0)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hCompile :
      Locals.Stmt.compile targetCtx (.expr expr) =
        some (code, finalCtx))
    (hScoped : Scope.ExprScoped targetCtx.layout expr)
    (hSupported : InteractionSemantics.Expr.OpenSupported expr) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx (.expr expr) code suffix returns 2 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Stmt.Forward.policy_expr_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel expr (by omega) hCompile hCtx hPolicy
      hScoped hSupported hInitial

theorem let_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    {name : Name} (value : Locals.Expr 1)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hCompile :
      Locals.Stmt.compile targetCtx (.let_ name value) =
        some (code, finalCtx))
    (hFresh : name ∉ targetCtx.layout)
    (hScoped : Scope.ExprScoped targetCtx.layout value)
    (hSupported : InteractionSemantics.Expr.OpenSupported value) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx (.let_ name value) code suffix returns 2 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Stmt.Forward.policy_let_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel value (by omega) hCompile hCtx hPolicy
      hFresh hScoped hSupported hInitial

theorem assign_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    {name : Name} (value : Locals.Expr 1)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hCompile :
      Locals.Stmt.compile targetCtx (.assign name value) =
        some (code, finalCtx))
    (hNodup : targetCtx.layout.Nodup)
    (hScoped : Scope.ExprScoped targetCtx.layout value)
    (hSupported : InteractionSemantics.Expr.OpenSupported value) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx (.assign name value) code suffix returns 2 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Stmt.Forward.policy_assign_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel value (by omega) hCompile hCtx hPolicy
      hNodup hScoped hSupported hInitial

theorem brk_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hCompile :
      Locals.Stmt.compile targetCtx .brk = some (code, finalCtx)) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx .brk code suffix returns 3 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Stmt.Forward.policy_brk_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel (by omega) hCompile hCtx hPolicy hInitial

theorem cont_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hCompile :
      Locals.Stmt.compile targetCtx .cont = some (code, finalCtx)) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx .cont code suffix returns 3 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Stmt.Forward.policy_cont_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel (by omega) hCompile hCtx hPolicy hInitial

theorem leave_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hReturns : returns ≠ [])
    (hCompile :
      Locals.Stmt.compile targetCtx .leave = some (code, finalCtx)) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx .leave code suffix returns 3 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Stmt.Forward.policy_leave_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel (by omega) hCompile hCtx hPolicy
      hReturns hInitial

theorem terminal_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (kind : Assembly.HaltKind)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hLeave : ∀ scope, policy.leave scope)
    (hArgCount : kind.argCount = 0)
    (hCompile :
      Locals.Stmt.compile targetCtx (.terminal kind) =
        some (code, finalCtx)) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx (.terminal kind) code suffix returns 3 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Stmt.Forward.policy_terminal_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel kind (by omega) hCompile hPolicy hLeave
      hCtx hArgCount hInitial

theorem terminalArgs_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (kind : Assembly.HaltKind)
    (args : Locals.ExprSeq kind.argCount)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hLeave : ∀ scope, policy.leave scope)
    (hScoped : Scope.ExprSeqScoped targetCtx.layout args)
    (hSupported : InteractionSemantics.ExprSeq.OpenSupported args)
    (hCompile :
      Locals.Stmt.compile targetCtx (.terminalArgs kind args) =
        some (code, finalCtx)) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx (.terminalArgs kind args)
        code suffix returns 3 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Stmt.Forward.policy_terminalArgs_of_compile
      policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
      sourceFuel targetFuel kind args (by omega) hCompile hPolicy
      hLeave hCtx hScoped hSupported hInitial

theorem block_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (body : Locals.Block)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hOwned : Locals.Source.Block.SourceOwned body)
    (hCompile :
      Locals.Stmt.compile targetCtx (.block body) =
        some (code, finalCtx))
    (hBody :
      ∀ {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx body =
            some (bodyCode, bodyCtx) →
          ∃ bodyCost,
            BlockForwardBound policy sourceProgram targetProgram
              targetCtx bodyCtx body bodyCode suffix returns bodyCost) :
    ∃ cost,
      StmtForwardBound policy sourceProgram targetProgram
        targetCtx finalCtx (.block body) code suffix returns cost := by
  obtain ⟨bodyCode, bodyCtx, lowerBody,
    hBodyCompile, hFinish, hCode, hFinal⟩ :=
    Locals.Stmt.compile_block_components hCompile
  obtain ⟨bodyCost, hBodyBound⟩ := hBody hBodyCompile
  let cost := Nat.max bodyCost (code.length + 1)
  refine ⟨cost, ?_⟩
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  have hBodyCost : bodyCost ≤ cost := Nat.le_max_left _ _
  have hCodeCost : code.length + 1 ≤ cost := Nat.le_max_right _ _
  apply Stmt.Forward.policy_block_of_compile
    policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
    sourceFuel targetFuel body hOwned
  · omega
  · exact hCompile
  · exact hPolicy
  · exact hCtx
  · intro actualCode actualCtx hActualCompile
    rw [hBodyCompile] at hActualCompile
    rcases hActualCompile with ⟨rfl, rfl⟩
    apply hBodyBound sourceCtx source target sourceFuel targetFuel
      hPolicy hCtx hInitial
    omega

theorem if_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (cond : Locals.Expr 1) (body : Locals.Block)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hOwned : Locals.Source.Block.SourceOwned body)
    (hCompile :
      Locals.Stmt.compile targetCtx (.if_ cond body) =
        some (code, finalCtx))
    (hCondScoped : Scope.ExprScoped targetCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hBody :
      ∀ {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx body =
            some (bodyCode, bodyCtx) →
          ∃ bodyCost,
            BlockForwardBound policy sourceProgram targetProgram
              targetCtx bodyCtx body bodyCode suffix returns bodyCost) :
    ∃ cost,
      StmtForwardBound policy sourceProgram targetProgram
        targetCtx finalCtx (.if_ cond body) code suffix returns cost := by
  obtain ⟨condCode, bodyCode, bodyCtx, lowerBody,
    hCondCompile, hBodyCompile, hFinish, hCode, hFinal⟩ :=
    Locals.Stmt.compile_if_components hCompile
  obtain ⟨bodyCost, hBodyBound⟩ := hBody hBodyCompile
  let cost := Nat.max (bodyCost + 1) (bodyCode.length + 3)
  refine ⟨cost, ?_⟩
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  cases sourceFuel with
  | zero =>
      unfold InteractionSemantics.Stmt.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.ForwardRel.truncated
      rfl
  | succ sourceFuel =>
      have hBodyCost : bodyCost + 1 ≤ cost := Nat.le_max_left _ _
      have hCodeCost : bodyCode.length + 3 ≤ cost :=
        Nat.le_max_right _ _
      apply Stmt.Forward.policy_if_of_compile
        policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
        sourceFuel targetFuel cond body hOwned hCompile hPolicy hCtx
        hCondScoped hCondSupported hInitial
      intro actualCode actualCtx hActualCompile
      rw [hBodyCompile] at hActualCompile
      rcases hActualCompile with ⟨rfl, rfl⟩
      constructor
      · omega
      · intro sourceAfter targetAfter hAfter
        apply hBodyBound sourceCtx sourceAfter targetAfter
          sourceFuel (targetFuel - 2) hPolicy hCtx hAfter
        omega

theorem selected_switch_bound_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx : Locals.Ctx)
    (cases : List (Word × Locals.Block))
    (defaultBody : Option Locals.Block)
    (compiledCases : List (Word × Expressions.Block))
    (compiledDefault : Option Expressions.Block)
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hCasesCompile :
      Locals.CaseList.compile targetCtx cases = some compiledCases)
    (hDefaultCompile :
      Locals.Default.compile targetCtx defaultBody = some compiledDefault)
    (hCase :
      ∀ {value body}, (value, body) ∈ cases →
        ∀ {bodyCode : List Expressions.Stmt} {bodyCtx : Locals.Ctx},
          Locals.Block.compileOpen targetCtx body =
              some (bodyCode, bodyCtx) →
            ∃ bodyCost,
              BlockForwardBound policy sourceProgram targetProgram
                targetCtx bodyCtx body bodyCode suffix returns bodyCost)
    (hDefault :
      ∀ {body}, defaultBody = some body →
        ∀ {bodyCode : List Expressions.Stmt} {bodyCtx : Locals.Ctx},
          Locals.Block.compileOpen targetCtx body =
              some (bodyCode, bodyCtx) →
            ∃ bodyCost,
              BlockForwardBound policy sourceProgram targetProgram
                targetCtx bodyCtx body bodyCode suffix returns bodyCost) :
    ∃ branchCost,
      ∀ {selected : Locals.Block}
        {selectedTarget : Expressions.Block}
        {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx}
        (value : Word),
        Locals.Source.Switch.select value cases defaultBody =
            some selected →
        Locals.Block.compileOpen targetCtx selected =
            some (bodyCode, bodyCtx) →
        Locals.finishScoped targetCtx bodyCtx bodyCode =
            some selectedTarget →
          ∃ bodyCost,
            bodyCode.length + 3 ≤ branchCost ∧
            bodyCost + 1 ≤ branchCost ∧
            BlockForwardBound policy sourceProgram targetProgram
              targetCtx bodyCtx selected bodyCode suffix returns bodyCost := by
  induction cases generalizing compiledCases with
  | nil =>
      simp [Locals.CaseList.compile] at hCasesCompile
      subst compiledCases
      cases defaultBody with
      | none =>
          refine ⟨0, ?_⟩
          intro selected selectedTarget bodyCode bodyCtx value
            hSelect hBodyCompile hFinish
          simp [Locals.Source.Switch.select] at hSelect
      | some default =>
          obtain ⟨defaultCode, defaultCtx, lowerDefault,
            hDefaultBody, hDefaultFinish, hCompiledDefault⟩ :=
            Locals.Default.compile_some_components hDefaultCompile
          obtain ⟨defaultCost, hDefaultBound⟩ :=
            hDefault rfl hDefaultBody
          let branchCost :=
            Nat.max (defaultCode.length + 3) (defaultCost + 1)
          refine ⟨branchCost, ?_⟩
          intro selected selectedTarget bodyCode bodyCtx value
            hSelect hBodyCompile hFinish
          simp [Locals.Source.Switch.select] at hSelect
          subst selected
          rw [hDefaultBody] at hBodyCompile
          rcases hBodyCompile with ⟨rfl, rfl⟩
          refine ⟨defaultCost, ?_, ?_, hDefaultBound⟩
          · exact Nat.le_max_left _ _
          · exact Nat.le_max_right _ _
  | cons head rest ih =>
      rcases head with ⟨caseValue, caseBody⟩
      obtain ⟨caseCode, caseCtx, lowerCase, lowerRest,
        hCaseBody, hCaseFinish, hRestCompile, hCompiledCases⟩ :=
        Locals.CaseList.compile_cons_components hCasesCompile
      obtain ⟨caseCost, hCaseBound⟩ :=
        hCase (value := caseValue) (body := caseBody)
          (by simp) hCaseBody
      obtain ⟨restCost, hRestBound⟩ :=
        ih lowerRest hRestCompile
          (fun {value body} hMem =>
            hCase (value := value) (body := body) (by simp [hMem]))
      let caseBound :=
        Nat.max (caseCode.length + 3) (caseCost + 1)
      let branchCost := Nat.max caseBound restCost
      refine ⟨branchCost, ?_⟩
      intro selected selectedTarget bodyCode bodyCtx value
        hSelect hBodyCompile hFinish
      by_cases hMatch : caseValue = value
      · simp [Locals.Source.Switch.select, hMatch] at hSelect
        subst selected
        rw [hCaseBody] at hBodyCompile
        rcases hBodyCompile with ⟨rfl, rfl⟩
        refine ⟨caseCost, ?_, ?_, hCaseBound⟩
        · have hLocal : caseCode.length + 3 ≤ caseBound :=
            Nat.le_max_left _ _
          have hOuter : caseBound ≤ branchCost := Nat.le_max_left _ _
          omega
        · have hLocal : caseCost + 1 ≤ caseBound :=
            Nat.le_max_right _ _
          have hOuter : caseBound ≤ branchCost := Nat.le_max_left _ _
          omega
      · simp [Locals.Source.Switch.select, hMatch] at hSelect
        obtain ⟨bodyCost, hCodeCost, hBodyCost, hBound⟩ :=
          hRestBound value hSelect hBodyCompile hFinish
        refine ⟨bodyCost, ?_, ?_, hBound⟩
        · have hOuter : restCost ≤ branchCost := Nat.le_max_right _ _
          omega
        · have hOuter : restCost ≤ branchCost := Nat.le_max_right _ _
          omega

theorem switch_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (scrutinee : Locals.Expr 1)
    (cases : List (Word × Locals.Block))
    (defaultBody : Option Locals.Block)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (branchCost : Nat)
    (hCompile :
      Locals.Stmt.compile targetCtx
          (.switch scrutinee cases defaultBody) =
        some (code, finalCtx))
    (hScrutineeScoped : Scope.ExprScoped targetCtx.layout scrutinee)
    (hScrutineeSupported :
      InteractionSemantics.Expr.OpenSupported scrutinee)
    (hSelectedOwned :
      ∀ {value selected},
        Locals.Source.Switch.select value cases defaultBody =
            some selected →
          Locals.Source.Block.SourceOwned selected)
    (hSelected :
      ∀ {selected : Locals.Block}
        {selectedTarget : Expressions.Block}
        {bodyCode : List Expressions.Stmt}
        {bodyCtx : Locals.Ctx}
        (value : Word),
        Locals.Source.Switch.select value cases defaultBody =
            some selected →
        Locals.Block.compileOpen targetCtx selected =
            some (bodyCode, bodyCtx) →
        Locals.finishScoped targetCtx bodyCtx bodyCode =
            some selectedTarget →
          ∃ bodyCost,
            bodyCode.length + 3 ≤ branchCost ∧
            bodyCost + 1 ≤ branchCost ∧
            BlockForwardBound policy sourceProgram targetProgram
              targetCtx bodyCtx selected bodyCode suffix returns bodyCost) :
    StmtForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx (.switch scrutinee cases defaultBody)
        code suffix returns (Nat.max branchCost 3) := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  cases sourceFuel with
  | zero =>
      unfold InteractionSemantics.Stmt.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.ForwardRel.truncated
      rfl
  | succ sourceFuel =>
      have hBranchCost : branchCost ≤ Nat.max branchCost 3 :=
        Nat.le_max_left _ _
      have hBaseCost : 3 ≤ Nat.max branchCost 3 :=
        Nat.le_max_right _ _
      apply Stmt.Forward.policy_switch_of_compile
        policy sourceProgram targetProgram sourceCtx targetCtx finalCtx
        sourceFuel targetFuel scrutinee cases defaultBody
        (by omega) hCompile hPolicy hCtx hScrutineeScoped
        hScrutineeSupported hInitial
      intro selected selectedTarget bodyCode bodyCtx
        value hSelect hBodyCompile hFinish
      obtain ⟨bodyCost, hCodeCost, hBodyCost, hBodyBound⟩ :=
        hSelected value hSelect hBodyCompile hFinish
      refine ⟨?_, ?_, ?_⟩
      · omega
      · exact
          Locals.Block.compileOpen_layout_extends_of_sourceOwned
            (hSelectedOwned hSelect) hBodyCompile
      · intro sourceAfter targetAfter hAfter
        apply hBodyBound sourceCtx sourceAfter targetAfter
          sourceFuel (targetFuel - 2) hPolicy hCtx hAfter
        omega

theorem for_of_compile
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (init : Locals.Block) (cond : Locals.Expr 1)
    (post body : Locals.Block)
    {code : List Expressions.Stmt}
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hLeave : ∀ scope, policy.leave scope)
    (hOwnedInit : Locals.Source.Block.SourceOwned init)
    (hOwnedPost : Locals.Source.Block.SourceOwned post)
    (hOwnedBody : Locals.Source.Block.SourceOwned body)
    (hCompile :
      Locals.Stmt.compile targetCtx (.for_ init cond post body) =
        some (code, finalCtx))
    (hCondScoped :
      ∀ {initCode : List Expressions.Stmt} {initCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx.withoutLoopControl init =
            some (initCode, initCtx) →
          Scope.ExprScoped initCtx.layout cond)
    (hCondSupported : InteractionSemantics.Expr.OpenSupported cond)
    (hInit :
      ∀ {initCode : List Expressions.Stmt} {initCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx.withoutLoopControl init =
            some (initCode, initCtx) →
          ∃ initCost,
            BlockForwardBound Stmt.ControlPolicy.noLoop
              sourceProgram targetProgram targetCtx.withoutLoopControl
              initCtx init initCode suffix returns initCost)
    (hPost :
      ∀ {initCode : List Expressions.Stmt} {initCtx : Locals.Ctx}
        {postCode : List Expressions.Stmt} {postCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx.withoutLoopControl init =
            some (initCode, initCtx) →
        Locals.Block.compileOpen initCtx.withoutLoopControl post =
            some (postCode, postCtx) →
          ∃ postCost,
            BlockForwardBound Stmt.ControlPolicy.noLoop
              sourceProgram targetProgram initCtx.withoutLoopControl
              postCtx post postCode suffix returns postCost)
    (hBody :
      ∀ {initCode : List Expressions.Stmt} {initCtx : Locals.Ctx}
        {bodyCode : List Expressions.Stmt} {bodyCtx : Locals.Ctx},
        Locals.Block.compileOpen targetCtx.withoutLoopControl init =
            some (initCode, initCtx) →
        Locals.Block.compileOpen
            (initCtx.withLoopControl initCtx.layout.length) body =
          some (bodyCode, bodyCtx) →
          ∃ bodyCost,
            BlockForwardBound
              (Stmt.ControlPolicy.loop initCtx.layout)
              sourceProgram targetProgram
              (initCtx.withLoopControl initCtx.layout.length)
              bodyCtx body bodyCode suffix returns bodyCost) :
    ∃ cost,
      StmtForwardBound policy sourceProgram targetProgram
        targetCtx finalCtx (.for_ init cond post body)
          code suffix returns cost := by
  obtain ⟨initCode, initCtx, condCode,
    postCode, postCtx, compiledPost,
    bodyCode, bodyCtx, compiledBody, outerCleanup,
    hInitCompile, hCondCompile, hPostCompile, hFinishPost,
    hBodyCompile, hFinishBody, hOuterCleanup, hCode, hFinal⟩ :=
    Locals.Stmt.compile_for_components hCompile
  obtain ⟨initCost, hInitBound⟩ := hInit hInitCompile
  obtain ⟨postCost, hPostBound⟩ :=
    hPost hInitCompile hPostCompile
  obtain ⟨bodyCost, hBodyBound⟩ :=
    hBody hInitCompile hBodyCompile
  let needed :=
    (initCode.length + 1) + initCost +
      (postCode.length + 2) + postCost +
      (bodyCode.length + 2) + bodyCost
  let cost := needed + 1
  refine ⟨cost, ?_⟩
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  cases sourceFuel with
  | zero =>
      unfold InteractionSemantics.Stmt.openRun
        InteractionSemantics.stateModel
        Locals.Source.Effectful.Ordinary.stateModel
      simp only [Locals.Source.Effectful.Control.Stmt.run]
      apply Simulation.Interaction.ForwardRel.truncated
      rfl
  | succ sourceFuel =>
      let slack := targetFuel - sourceFuel - 2
      have hTargetEq :
          targetFuel = sourceFuel + slack + 2 := by
        dsimp [slack, cost, needed] at *
        omega
      have hInitCode : initCode.length + 1 ≤ slack := by
        dsimp [slack, cost, needed] at *
        omega
      have hInitCost : initCost ≤ slack := by
        dsimp [slack, cost, needed] at *
        omega
      have hPostCode : postCode.length + 2 ≤ slack := by
        dsimp [slack, cost, needed] at *
        omega
      have hPostCost : postCost ≤ slack := by
        dsimp [slack, cost, needed] at *
        omega
      have hBodyCode : bodyCode.length + 2 ≤ slack := by
        dsimp [slack, cost, needed] at *
        omega
      have hBodyCost : bodyCost ≤ slack := by
        dsimp [slack, cost, needed] at *
        omega
      rw [hTargetEq]
      apply Stmt.Forward.policy_for_of_forward
        policy sourceProgram sourceCtx sourceFuel init cond post body
        hPolicy hLeave
      apply Stmt.Forward.for_of_compile
        sourceProgram targetProgram sourceCtx targetCtx finalCtx
        sourceFuel slack init cond post body
        hOwnedInit hOwnedPost hOwnedBody hCompile hCtx
        hCondScoped hCondSupported
      · intro actualCode actualCtx hActualCompile
        rw [hInitCompile] at hActualCompile
        rcases hActualCompile with ⟨rfl, rfl⟩
        constructor
        · exact hInitCode
        · apply hInitBound sourceCtx.withoutLoopControl
            source target sourceFuel (sourceFuel + slack)
            (Stmt.ControlPolicy.noLoop_contextCompatible_withoutLoopControl
              sourceCtx)
            hCtx.withoutLoopControl hInitial
          omega
      · intro actualInitCode actualInitCtx actualPostCode actualPostCtx
          hActualInit hActualPost
        rw [hInitCompile] at hActualInit
        rcases hActualInit with ⟨rfl, rfl⟩
        rw [hPostCompile] at hActualPost
        rcases hActualPost with ⟨rfl, rfl⟩
        constructor
        · exact hPostCode
        · intro loopSourceCtx fuel sourceAfter targetAfter
            hLoopCtx hAfter
          apply hPostBound loopSourceCtx.withoutLoopControl
            sourceAfter targetAfter fuel (fuel + slack)
            (Stmt.ControlPolicy.noLoop_contextCompatible_withoutLoopControl
              loopSourceCtx)
            hLoopCtx.withoutLoopControl hAfter
          omega
      · intro actualInitCode actualInitCtx actualBodyCode actualBodyCtx
          hActualInit hActualBody
        rw [hInitCompile] at hActualInit
        rcases hActualInit with ⟨rfl, rfl⟩
        rw [hBodyCompile] at hActualBody
        rcases hActualBody with ⟨rfl, rfl⟩
        constructor
        · exact hBodyCode
        · intro loopSourceCtx fuel sourceAfter targetAfter
            hLoopCtx hAfter
          have hBodyPolicy :
              Stmt.ControlPolicy.ContextCompatible
                (Stmt.ControlPolicy.loop initCtx.layout)
                (loopSourceCtx.withLoopControl
                  loopSourceCtx.scope loopSourceCtx.scope) := by
            rw [hLoopCtx.layout]
            exact
              Stmt.ControlPolicy.loop_contextCompatible
                loopSourceCtx loopSourceCtx.scope
          have hForward :=
            hBodyBound
              (loopSourceCtx.withLoopControl
                loopSourceCtx.scope loopSourceCtx.scope)
              sourceAfter targetAfter fuel (fuel + slack)
              hBodyPolicy hLoopCtx.withLoopControl hAfter (by omega)
          simpa [hLoopCtx.layout] using hForward

theorem empty
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx : Locals.Ctx)
    (suffix : List Word)
    (returns : List Structured.ReturnDest) :
    BlockForwardBound policy sourceProgram targetProgram
      targetCtx targetCtx { stmts := [] } [] suffix returns 1 := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  exact
    Block.policy_openRun_empty
      policy sourceProgram targetProgram sourceCtx targetCtx
      sourceFuel targetFuel (by omega) hPolicy hCtx hInitial

theorem cons
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx middleCtx finalCtx : Locals.Ctx)
    (stmt : Locals.Stmt) (rest : List Locals.Stmt)
    (headCode tailCode : List Expressions.Stmt)
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (headCost tailCost : Nat)
    (hHead :
      StmtForwardBound policy sourceProgram targetProgram
        targetCtx middleCtx stmt headCode suffix returns headCost)
    (hTail :
      BlockForwardBound policy sourceProgram targetProgram
        middleCtx finalCtx { stmts := rest } tailCode
        suffix returns tailCost) :
    BlockForwardBound policy sourceProgram targetProgram
      targetCtx finalCtx { stmts := stmt :: rest }
        (headCode ++ tailCode) suffix returns
        (Nat.max headCost (headCode.length + tailCost) + 1) := by
  intro sourceCtx source target sourceFuel targetFuel
    hPolicy hCtx hInitial hFuel
  apply Block.policy_forward_cons_bounded
    policy sourceProgram targetProgram sourceCtx middleCtx finalCtx
    stmt rest headCode tailCode headCost tailCost hPolicy
  · intro sourceFuel targetFuel hBound
    exact
      hHead sourceCtx source target sourceFuel targetFuel
        hPolicy hCtx hInitial hBound
  · intro sourceMid targetMid sourceMidCtx
      hMidPolicy hMidCtx hMidState sourceFuel targetFuel hBound
    exact
      hTail sourceMidCtx sourceMid targetMid sourceFuel targetFuel
        hMidPolicy hMidCtx hMidState hBound
  · exact hFuel

structure VerifiedStmt
    (canLeave : Bool)
    (stmt : Locals.Stmt) : Prop where
  forward : ∀ (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (code : List Expressions.Stmt)
    (suffix : List Word)
    (returns : List Structured.ReturnDest),
    (∀ scope, policy.leave scope) →
    targetCtx.layout.Nodup →
    (canLeave = true → returns ≠ []) →
    Locals.Source.Stmt.SourceOwned stmt →
    Scope.Stmt.Scoped targetCtx.layout stmt →
    InteractionSemantics.Stmt.OpenSupported stmt →
    Locals.Stmt.compile targetCtx stmt = some (code, finalCtx) →
      ∃ cost,
        StmtForwardBound policy sourceProgram targetProgram
          targetCtx finalCtx stmt code suffix returns cost

structure VerifiedBlock
    (canLeave : Bool)
    (block : Locals.Block) : Prop where
  forward : ∀ (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (code : List Expressions.Stmt)
    (suffix : List Word)
    (returns : List Structured.ReturnDest),
    (∀ scope, policy.leave scope) →
    targetCtx.layout.Nodup →
    (canLeave = true → returns ≠ []) →
    Locals.Source.Block.SourceOwned block →
    Scope.Block.Scoped targetCtx.layout block →
    InteractionSemantics.Block.OpenSupported block →
    Locals.Block.compileOpen targetCtx block = some (code, finalCtx) →
      ∃ cost,
        BlockForwardBound policy sourceProgram targetProgram
          targetCtx finalCtx block code suffix returns cost

private theorem sizeOf_lt_list_of_mem
    {α : Type} [SizeOf α] {x : α} {xs : List α}
    (hMem : x ∈ xs) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => simp at hMem
  | cons head tail ih =>
      cases hMem <;> rw [List.cons.sizeOf_spec]
      · omega
      · specialize ih ‹x ∈ tail›
        omega

inductive OwnerInput : Type where
  | stmt (canBreak canContinue canLeave : Bool) (stmt : Locals.Stmt)
      (hWF : Locals.Stmt.WF canBreak canContinue canLeave stmt)
  | block (canBreak canContinue canLeave : Bool) (block : Locals.Block)
      (hWF : Locals.Block.WF canBreak canContinue canLeave block)

namespace OwnerInput

noncomputable def size : OwnerInput → Nat
  | .stmt _ _ _ sourceStmt _ => sizeOf sourceStmt
  | .block _ _ _ sourceBlock _ => sizeOf sourceBlock

def Verified : OwnerInput → Prop
  | .stmt _ _ canLeave sourceStmt _ => VerifiedStmt canLeave sourceStmt
  | .block _ _ canLeave sourceBlock _ => VerifiedBlock canLeave sourceBlock

end OwnerInput

theorem sourceOwned (input : OwnerInput) : input.Verified := by
  cases input with
  | stmt canBreak canContinue canLeave stmt hWF =>
    simp only [OwnerInput.Verified]
    constructor
    cases hWF with
    | expr =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        rcases hOwned with ⟨hResults, hExprOwned⟩
        subst hResults
        exact
          ⟨2, expr_of_compile policy sourceProgram targetProgram
            targetCtx finalCtx _ suffix returns hCompile
            hScoped hSupported⟩
    | exprs =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned
        simp [Locals.Source.Stmt.SourceOwned] at hOwned
    | let_ =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        exact
          ⟨2, let_of_compile policy sourceProgram targetProgram
            targetCtx finalCtx _ suffix returns hCompile
            hScoped.1 hScoped.2 hSupported⟩
    | assign =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        exact
          ⟨2, assign_of_compile policy sourceProgram targetProgram
            targetCtx finalCtx _ suffix returns hCompile
            hNodup hScoped.2 hSupported⟩
    | assignTop =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns hOwned
        simp [Locals.Source.Stmt.SourceOwned] at hOwned
    | assignTopWithOffset =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns hOwned
        simp [Locals.Source.Stmt.SourceOwned] at hOwned
    | promoteName =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns hOwned
        simp [Locals.Source.Stmt.SourceOwned] at hOwned
    | cleanupTo =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns hOwned
        simp [Locals.Source.Stmt.SourceOwned] at hOwned
    | block hBody =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        apply block_of_compile policy sourceProgram targetProgram
          targetCtx finalCtx _ suffix returns hOwned hCompile
        intro bodyCode bodyCtx hBodyCompile
        exact
          VerifiedBlock.forward
            (sourceOwned
              (.block canBreak canContinue canLeave _ hBody))
            policy sourceProgram targetProgram
            targetCtx bodyCtx bodyCode suffix returns hLeave hNodup
            hLeaveReturns hOwned hScoped hSupported hBodyCompile
    | if_ hBody =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        apply if_of_compile policy sourceProgram targetProgram
          targetCtx finalCtx _ _ suffix returns hOwned.2 hCompile
          hScoped.1 hSupported.1
        intro bodyCode bodyCtx hBodyCompile
        exact
          VerifiedBlock.forward
            (sourceOwned
              (.block canBreak canContinue canLeave _ hBody))
            policy sourceProgram targetProgram
            targetCtx bodyCtx bodyCode suffix returns hLeave hNodup
            hLeaveReturns hOwned.2 hScoped.2 hSupported.2 hBodyCompile
    | @switch canBreak canContinue canLeave
        scrutinee cases defaultBody hCases hDefault =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        obtain ⟨scrutineeCode, compiledCases, compiledDefault,
          hScrutineeCompile, hCasesCompile, hDefaultCompile,
          hCode, hFinal⟩ :=
          Locals.Stmt.compile_switch_components hCompile
        obtain ⟨branchCost, hSelectedBound⟩ :=
          selected_switch_bound_of_compile
            policy sourceProgram targetProgram targetCtx _ _
            compiledCases compiledDefault suffix returns
            hCasesCompile hDefaultCompile
            (fun {value body} hMem {bodyCode bodyCtx} hBodyCompile =>
              VerifiedBlock.forward
                (sourceOwned
                  (.block canBreak canContinue canLeave body
                    (hCases value body hMem)))
                policy sourceProgram targetProgram targetCtx bodyCtx
                bodyCode suffix returns hLeave hNodup hLeaveReturns
                (Locals.Source.Switch.case_sourceOwned_of_mem
                  hOwned hMem)
                (Scope.CaseList.scoped_of_mem hScoped.2.1 hMem)
                (InteractionSemantics.CaseList.openSupported_of_mem
                  hSupported.2.1 hMem)
                hBodyCompile)
            (fun {body} hDefaultEq {bodyCode bodyCtx} hBodyCompile =>
              VerifiedBlock.forward
                (sourceOwned
                  (.block canBreak canContinue canLeave body
                    (hDefault body hDefaultEq)))
                policy sourceProgram targetProgram targetCtx bodyCtx
                bodyCode suffix returns hLeave hNodup hLeaveReturns
                (Locals.Source.Switch.default_sourceOwned_of_eq
                  hOwned hDefaultEq)
                (by simpa [hDefaultEq] using hScoped.2.2)
                (by simpa [hDefaultEq] using hSupported.2.2)
                hBodyCompile)
        refine
          ⟨Nat.max branchCost 3,
            switch_of_compile policy sourceProgram targetProgram
              targetCtx finalCtx _ _ _ suffix returns branchCost
              hCompile hScoped.1 hSupported.1 ?_ hSelectedBound⟩
        · intro value selected hSelect
          apply Locals.Source.Switch.property_of_select
            (scrutinee := value) (cases := cases)
            (defaultBody := defaultBody) (selected := selected)
          · intro caseValue caseBody hMem
            exact
              Locals.Source.Switch.case_sourceOwned_of_mem
                hOwned hMem
          · intro default hDefaultEq
            exact
              Locals.Source.Switch.default_sourceOwned_of_eq
                hOwned hDefaultEq
          · exact hSelect
    | for_ hInitWF hPostWF hBodyWF =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        apply for_of_compile policy sourceProgram targetProgram
          targetCtx finalCtx _ _ _ _ suffix returns hLeave
          hOwned.1 hOwned.2.2.1 hOwned.2.2.2 hCompile
        · intro initCode initCtx hInitCompile
          have hLayout :=
            Locals.Block.compileOpen_layout_eq_outEnv_of_sourceOwned
              hOwned.1 hInitCompile
          simpa [hLayout] using hScoped.2.1
        · exact hSupported.2.1
        · intro initCode initCtx hInitCompile
          exact
            VerifiedBlock.forward
              (sourceOwned (.block false false canLeave _ hInitWF))
              Stmt.ControlPolicy.noLoop
              sourceProgram targetProgram targetCtx.withoutLoopControl
              initCtx initCode suffix returns (fun _ => trivial)
              (by simpa [Locals.Ctx.withoutLoopControl] using hNodup)
              hLeaveReturns hOwned.1
              (by simpa [Locals.Ctx.withoutLoopControl] using hScoped.1)
              hSupported.1 hInitCompile
        · intro initCode initCtx postCode postCtx
            hInitCompile hPostCompile
          have hLayout :=
            Locals.Block.compileOpen_layout_eq_outEnv_of_sourceOwned
              hOwned.1 hInitCompile
          have hLoopNodup : initCtx.layout.Nodup := by
            rw [hLayout]
            exact Locals.Block.scoped_outEnv_nodup hNodup hScoped.1
          exact
            VerifiedBlock.forward
              (sourceOwned (.block false false canLeave _ hPostWF))
              Stmt.ControlPolicy.noLoop
              sourceProgram targetProgram initCtx.withoutLoopControl
              postCtx postCode suffix returns (fun _ => trivial)
              (by simpa [Locals.Ctx.withoutLoopControl] using hLoopNodup)
              hLeaveReturns hOwned.2.2.1
              (by
                simpa [Locals.Ctx.withoutLoopControl, hLayout] using
                  hScoped.2.2.1)
              hSupported.2.2.1 hPostCompile
        · intro initCode initCtx bodyCode bodyCtx
            hInitCompile hBodyCompile
          have hLayout :=
            Locals.Block.compileOpen_layout_eq_outEnv_of_sourceOwned
              hOwned.1 hInitCompile
          have hLoopNodup : initCtx.layout.Nodup := by
            rw [hLayout]
            exact Locals.Block.scoped_outEnv_nodup hNodup hScoped.1
          exact
            VerifiedBlock.forward
              (sourceOwned (.block true true canLeave _ hBodyWF))
              (Stmt.ControlPolicy.loop initCtx.layout)
              sourceProgram targetProgram
              (initCtx.withLoopControl initCtx.layout.length)
              bodyCtx bodyCode suffix returns (fun _ => trivial)
              (by
                simpa [Locals.Ctx.withLoopControl] using hLoopNodup)
              hLeaveReturns hOwned.2.2.2
              (by
                simpa [Locals.Ctx.withLoopControl, hLayout] using
                  hScoped.2.2.2)
              hSupported.2.2.2 hBodyCompile
    | brk hAllowed =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        exact
          ⟨3, brk_of_compile policy sourceProgram targetProgram
            targetCtx finalCtx suffix returns hCompile⟩
    | cont hAllowed =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        exact
          ⟨3, cont_of_compile policy sourceProgram targetProgram
            targetCtx finalCtx suffix returns hCompile⟩
    | leave hAllowed =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        exact
          ⟨3, leave_of_compile policy sourceProgram targetProgram
            targetCtx finalCtx suffix returns
            (hLeaveReturns hAllowed) hCompile⟩
    | call =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns hOwned
        simp [Locals.Source.Stmt.SourceOwned] at hOwned
    | terminal =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        exact
          ⟨3, terminal_of_compile policy sourceProgram targetProgram
            targetCtx finalCtx _ suffix returns hLeave hOwned hCompile⟩
    | terminalArgs =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        exact
          ⟨3, terminalArgs_of_compile policy sourceProgram targetProgram
            targetCtx finalCtx _ _ suffix returns hLeave
            hScoped hSupported hCompile⟩
  | block canBreak canContinue canLeave block hWF =>
    simp only [OwnerInput.Verified]
    constructor
    cases hWF with
    | nil =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        simp [Locals.Block.compileOpen] at hCompile
        rcases hCompile with ⟨rfl, rfl⟩
        exact ⟨1, empty policy sourceProgram targetProgram
          targetCtx suffix returns⟩
    | cons hStmtWF hRestWF =>
        intro policy sourceProgram targetProgram targetCtx finalCtx
          code suffix returns hLeave hNodup hLeaveReturns
          hOwned hScoped hSupported hCompile
        obtain ⟨headCode, middleCtx, tailCode,
          hHeadCompile, hTailCompile, hCode⟩ :=
          Locals.Block.compileOpen_cons_components hCompile
        have hMiddleLayout :=
          Locals.Stmt.compile_layout_eq_outEnv_of_sourceOwned
            hOwned.1 hHeadCompile
        have hMiddleNodup : middleCtx.layout.Nodup := by
          rw [hMiddleLayout]
          exact Locals.Stmt.scoped_outEnv_nodup hNodup hScoped.1
        obtain ⟨headCost, hHeadBound⟩ :=
          VerifiedStmt.forward
            (sourceOwned
              (.stmt canBreak canContinue canLeave _ hStmtWF))
            policy sourceProgram targetProgram
            targetCtx middleCtx headCode suffix returns hLeave hNodup
            hLeaveReturns hOwned.1 hScoped.1 hSupported.1 hHeadCompile
        obtain ⟨tailCost, hTailBound⟩ :=
          VerifiedBlock.forward
            (sourceOwned
              (.block canBreak canContinue canLeave _ hRestWF))
            policy sourceProgram targetProgram
            middleCtx finalCtx tailCode suffix returns hLeave
            hMiddleNodup hLeaveReturns hOwned.2
            (by rw [hMiddleLayout]; exact hScoped.2)
            hSupported.2 hTailCompile
        subst code
        exact
          ⟨Nat.max headCost (headCode.length + tailCost) + 1,
            cons policy sourceProgram targetProgram targetCtx middleCtx
              finalCtx _ _ headCode tailCode suffix returns
              headCost tailCost hHeadBound hTailBound⟩
termination_by input.size
decreasing_by
  all_goals try simp [OwnerInput.size]
  all_goals subst_vars
  all_goals try simp_wf
  all_goals
    first
    | omega
    | have hSize := sizeOf_lt_list_of_mem (by assumption)
      simp only [Prod.mk.sizeOf_spec] at hSize
      omega

theorem sourceOwned_stmt
    (stmt : Locals.Stmt)
    {canBreak canContinue canLeave : Bool}
    (hWF : Locals.Stmt.WF canBreak canContinue canLeave stmt) :
    VerifiedStmt canLeave stmt :=
  sourceOwned (.stmt canBreak canContinue canLeave stmt hWF)

theorem sourceOwned_block
    (block : Locals.Block)
    {canBreak canContinue canLeave : Bool}
    (hWF : Locals.Block.WF canBreak canContinue canLeave block) :
    VerifiedBlock canLeave block :=
  sourceOwned (.block canBreak canContinue canLeave block hWF)

/-- Compiler-facing source-statement preservation. Recursive control evidence
is discharged internally from the source `WF` derivation. -/
theorem sourceOwned_stmt_of_compile
    {canBreak canContinue canLeave : Bool}
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (stmt : Locals.Stmt)
    (code : List Expressions.Stmt)
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hLeave : ∀ scope, policy.leave scope)
    (hNodup : targetCtx.layout.Nodup)
    (hLeaveReturns : canLeave = true → returns ≠ [])
    (hWF : Locals.Stmt.WF canBreak canContinue canLeave stmt)
    (hOwned : Locals.Source.Stmt.SourceOwned stmt)
    (hScoped : Scope.Stmt.Scoped targetCtx.layout stmt)
    (hSupported : InteractionSemantics.Stmt.OpenSupported stmt)
    (hCompile :
      Locals.Stmt.compile targetCtx stmt = some (code, finalCtx)) :
    ∃ cost,
      StmtForwardBound policy sourceProgram targetProgram
        targetCtx finalCtx stmt code suffix returns cost :=
  (sourceOwned_stmt stmt hWF).forward
    policy sourceProgram targetProgram targetCtx finalCtx code suffix returns
    hLeave hNodup hLeaveReturns hOwned hScoped hSupported hCompile

/-- Compiler-facing source-block preservation. The result has no branch,
loop, or recursive-block callback premise. -/
theorem sourceOwned_block_of_compile
    {canBreak canContinue canLeave : Bool}
    (policy : Stmt.ControlPolicy)
    (sourceProgram : Locals.Program)
    (targetProgram : Expressions.Program)
    (targetCtx finalCtx : Locals.Ctx)
    (block : Locals.Block)
    (code : List Expressions.Stmt)
    (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (hLeave : ∀ scope, policy.leave scope)
    (hNodup : targetCtx.layout.Nodup)
    (hLeaveReturns : canLeave = true → returns ≠ [])
    (hWF : Locals.Block.WF canBreak canContinue canLeave block)
    (hOwned : Locals.Source.Block.SourceOwned block)
    (hScoped : Scope.Block.Scoped targetCtx.layout block)
    (hSupported : InteractionSemantics.Block.OpenSupported block)
    (hCompile :
      Locals.Block.compileOpen targetCtx block = some (code, finalCtx)) :
    ∃ cost,
      BlockForwardBound policy sourceProgram targetProgram
        targetCtx finalCtx block code suffix returns cost :=
  (sourceOwned_block block hWF).forward
    policy sourceProgram targetProgram targetCtx finalCtx code suffix returns
    hLeave hNodup hLeaveReturns hOwned hScoped hSupported hCompile

end Recursive
end InteractionPreservation
end Locals
end EvmCompiler
