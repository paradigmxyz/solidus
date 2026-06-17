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
end InteractionPreservation
end Locals
end EvmCompiler
