import EvmCompiler.Yul.CompilerStatementDecomposition
import EvmCompiler.Yul.CompilerExpressionDecomposition
import EvmCompiler.Yul.FunctionsInteractionExpression
import EvmCompiler.Yul.FunctionsInteractionTerminal
import EvmCompiler.Yul.FunctionsInteractionControlRelation

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionStatement

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation

def ResultRel (ctx : Functions.Source.Ctx)
    (source : Yul.InteractionSemantics.State)
    (target :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) : Prop :=
  FunctionsInteractionRelation.OutcomeRel source target.1 ∧
    target.2 = ctx

abbrev DoneRel (ctx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel ErrorRel (ResultRel ctx)

def ScopedResultRel (layout : List Functions.Name)
    (ctx : Functions.Source.Ctx)
    (source : Yul.InteractionSemantics.State)
    (target :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) : Prop :=
  FunctionsInteractionRelation.ScopedOutcomeRel layout source target.1 ∧
    target.2 = ctx

abbrev ScopedDoneRel (layout : List Functions.Name)
    (ctx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel ErrorRel (ScopedResultRel layout ctx)

/-- Path-sensitive scoped result for recursive statement/list composition.
Abrupt control may skip declarations in the static suffix, so only regular
completion must reach `regularLayout`. -/
def PathScopedResultRel (regularLayout : List Functions.Name)
    (source : Yul.InteractionSemantics.State)
    (target :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) : Prop :=
  ∃ finalLayout,
    FunctionsInteractionRelation.ScopedOutcomeRel
        finalLayout source target.1 ∧
      (target.1.mode = .regular → finalLayout = regularLayout)

inductive PathScopedDoneRel (regularLayout : List Functions.Name) :
    Except Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State →
      Except EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Prop where
  | error {source target} :
      ErrorRel source target →
        PathScopedDoneRel regularLayout (.error source) (.error target)
  | ok {source target} :
      PathScopedResultRel regularLayout source target →
        PathScopedDoneRel regularLayout (.ok source) (.ok target)
  | terminal {source target ctx} :
      FunctionsInteractionRelation.TerminalFailureRel source target →
        PathScopedDoneRel regularLayout (.error source) (.ok (target, ctx))

namespace PathScopedResultRel

theorem of_fixed
    {layout : List Functions.Name} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target :
      Functions.InteractionSemantics.Outcome × Functions.Source.Ctx}
    (hRel : ScopedResultRel layout ctx source target) :
    PathScopedResultRel layout source target :=
  ⟨layout, hRel.1, fun _ => rfl⟩

theorem regular_state
    {regularLayout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hRel : PathScopedResultRel regularLayout source
      (Functions.Source.Effectful.Outcome.regular target, ctx)) :
    FunctionsInteractionRelation.ScopedStateRel
      regularLayout source target := by
  rcases hRel with ⟨finalLayout, hScoped, hFinal⟩
  have hLayout : finalLayout = regularLayout := hFinal rfl
  subst finalLayout
  exact hScoped.of_regular_target

end PathScopedResultRel

namespace PathScopedDoneRel

theorem of_fixed
    {layout : List Functions.Name} {ctx : Functions.Source.Ctx}
    {sourceOpen :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State}
    {targetOpen :
      Simulation.Interaction EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx)}
    (hRel : Simulation.Interaction.ForwardRel Truncated
      (ScopedDoneRel layout ctx) sourceOpen targetOpen) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout) sourceOpen targetOpen := by
  apply Simulation.Interaction.ForwardRel.mono hRel
  intro source target hDone
  cases hDone with
  | error hError => exact .error hError
  | ok hResult => exact .ok (PathScopedResultRel.of_fixed hResult)

theorem nil
    {layout : List Functions.Name} {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.execSeq
        (fuel + 1) [] codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 1) { stmts := [] } target) := by
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ,
    Functions.InteractionSemantics.Block.openRun_nil]
  exact Simulation.Interaction.ForwardRel.done
    (.ok
      ⟨layout,
        FunctionsInteractionRelation.ScopedOutcomeRel.regular hRel,
        by simp⟩)

theorem singleton
    {layout : List Functions.Name} {targetFuel : Nat}
    {sourceOpen :
      Simulation.Interaction Yul.InteractionSemantics.Failure
        Yul.InteractionSemantics.State}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {stmt : Functions.Stmt}
    {target : Functions.InteractionSemantics.State}
    (hStmt :
      Simulation.Interaction.ForwardRel Truncated
        (PathScopedDoneRel layout) sourceOpen
        (Functions.InteractionSemantics.Stmt.openRun
          program ctx (targetFuel + 1) stmt target)) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout) sourceOpen
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := [stmt] } target) := by
  have hBound :
      Simulation.Interaction.ForwardRel Truncated
        (PathScopedDoneRel layout)
        (Simulation.Interaction.bind sourceOpen fun sourceResult =>
          pure sourceResult)
        (Simulation.Interaction.bind
          (Functions.InteractionSemantics.Stmt.openRun
            program ctx (targetFuel + 1) stmt target)
          fun targetResult =>
            match targetResult.1.mode with
            | .regular =>
                Functions.InteractionSemantics.Block.openRun
                  program targetResult.2 (targetFuel + 1)
                    { stmts := [] } targetResult.1.state
            | .brk | .cont | .leave | .halt _ =>
                pure (targetResult.1, ctx)) := by
    apply Simulation.Interaction.ForwardRel.bind_custom hStmt
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
    | @ok sourceResult targetResult hResult =>
        rcases targetResult with ⟨targetOutcome, ctxMid⟩
        rcases targetOutcome with ⟨targetMid, mode⟩
        rcases hResult with ⟨finalLayout, hScoped, hRegular⟩
        cases mode with
        | regular =>
            dsimp
            rw [Functions.InteractionSemantics.Block.openRun_nil]
            exact Simulation.Interaction.ForwardRel.done
              (PathScopedDoneRel.ok
                ⟨finalLayout, hScoped, hRegular⟩)
        | brk =>
            dsimp
            exact Simulation.Interaction.ForwardRel.done
              (PathScopedDoneRel.ok
                ⟨finalLayout, hScoped, by simp⟩)
        | cont =>
            dsimp
            exact Simulation.Interaction.ForwardRel.done
              (PathScopedDoneRel.ok
                ⟨finalLayout, hScoped, by simp⟩)
        | leave =>
            dsimp
            exact Simulation.Interaction.ForwardRel.done
              (PathScopedDoneRel.ok
                ⟨finalLayout, hScoped, by simp⟩)
        | halt kind =>
            dsimp
            exact Simulation.Interaction.ForwardRel.done
              (PathScopedDoneRel.ok
                ⟨finalLayout, hScoped, by simp⟩)
  rw [show targetFuel + 2 = (targetFuel + 1) + 1 by omega,
    Functions.InteractionSemantics.Block.openRun_cons]
  have hSourceBind :
      Simulation.Interaction.bind sourceOpen
          (fun sourceResult => pure sourceResult) = sourceOpen := by
    change Simulation.Interaction.bind sourceOpen pure = sourceOpen
    exact EvmCompiler.Simulation.Interaction.bind_pure sourceOpen
  rw [hSourceBind] at hBound
  simpa [Functions.InteractionSemantics.Stmt.openRun,
    Functions.InteractionSemantics.Block.openRun_nil] using hBound

/-- Compose one source statement with its residual source list while allowing
the ordinary compiler to emit an arbitrary target prefix for that statement. -/
theorem cons
    {headLayout finalLayout : List Functions.Name}
    {fuel targetFuel : Nat}
    {stmt : AstStmt} {rest : List AstStmt}
    {lowerHead lowerRest : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hHead :
      Simulation.Interaction.ForwardRel Truncated
        (PathScopedDoneRel headLayout)
        (Yul.InteractionSemantics.exec fuel stmt codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := lowerHead } target))
    (hTail :
      ∀ {sourceMid : Yul.InteractionSemantics.State}
        {targetMid : Functions.InteractionSemantics.State}
        {ctxMid : Functions.Source.Ctx},
        FunctionsInteractionRelation.ScopedStateRel
            headLayout sourceMid targetMid →
          Simulation.Interaction.ForwardRel Truncated
            (PathScopedDoneRel finalLayout)
            (Yul.InteractionSemantics.execSeq
              fuel rest codeOverride sourceMid)
            (Functions.InteractionSemantics.Block.openRun
              program ctxMid (targetFuel - lowerHead.length)
                { stmts := lowerRest } targetMid)) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel finalLayout)
      (Yul.InteractionSemantics.execSeq
        (fuel + 1) (stmt :: rest) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
          { stmts := lowerHead ++ lowerRest } target) := by
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ,
    Functions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind_custom hHead
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
  | @ok sourceMid targetResult hResult =>
    rcases targetResult with ⟨targetOutcome, ctxMid⟩
    rcases targetOutcome with ⟨targetMid, mode⟩
    cases mode with
    | regular =>
      have hState := PathScopedResultRel.regular_state hResult
      rcases hState.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst sourceMid
      simpa using hTail hState
    | brk =>
      rcases hResult with ⟨branchLayout, hScoped, hRegular⟩
      have hMode := hScoped.outcome.mode
      cases sourceMid with
      | Ok sourceShared sourceVars => simp [ModeRel] at hMode
      | OutOfFuel => simp [ModeRel] at hMode
      | Checkpoint checkpoint =>
          cases checkpoint with
          | Break sourceShared sourceVars =>
              exact Simulation.Interaction.ForwardRel.done
                (.ok ⟨branchLayout, hScoped, by simp⟩)
          | Continue sourceShared sourceVars => simp [ModeRel] at hMode
          | Leave sourceShared sourceVars => simp [ModeRel] at hMode
    | cont =>
      rcases hResult with ⟨branchLayout, hScoped, hRegular⟩
      have hMode := hScoped.outcome.mode
      cases sourceMid with
      | Ok sourceShared sourceVars => simp [ModeRel] at hMode
      | OutOfFuel => simp [ModeRel] at hMode
      | Checkpoint checkpoint =>
          cases checkpoint with
          | Break sourceShared sourceVars => simp [ModeRel] at hMode
          | Continue sourceShared sourceVars =>
              exact Simulation.Interaction.ForwardRel.done
                (.ok ⟨branchLayout, hScoped, by simp⟩)
          | Leave sourceShared sourceVars => simp [ModeRel] at hMode
    | leave =>
      rcases hResult with ⟨branchLayout, hScoped, hRegular⟩
      have hMode := hScoped.outcome.mode
      cases sourceMid with
      | Ok sourceShared sourceVars => simp [ModeRel] at hMode
      | OutOfFuel => simp [ModeRel] at hMode
      | Checkpoint checkpoint =>
          cases checkpoint with
          | Break sourceShared sourceVars => simp [ModeRel] at hMode
          | Continue sourceShared sourceVars => simp [ModeRel] at hMode
          | Leave sourceShared sourceVars =>
              exact Simulation.Interaction.ForwardRel.done
                (.ok ⟨branchLayout, hScoped, by simp⟩)
    | halt kind =>
      rcases hResult with ⟨branchLayout, hScoped, hRegular⟩
      have hMode := hScoped.outcome.mode
      cases sourceMid with
      | Ok sourceShared sourceVars => simp [ModeRel] at hMode
      | OutOfFuel => simp [ModeRel] at hMode
      | Checkpoint checkpoint =>
          cases checkpoint <;> simp [ModeRel] at hMode

end PathScopedDoneRel

namespace ControlDoneRel

theorem nil
    {layout : List Functions.Name} {sourceFuel targetFuel : Nat}
    {sourceScopes : SourceScopes}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : ScopedStateRel layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel layout sourceScopes)
      (Yul.InteractionSemantics.execSeq
        (sourceFuel + 1) [] codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 1) { stmts := [] } target) := by
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ,
    Functions.InteractionSemantics.Block.openRun_nil]
  exact Simulation.Interaction.ForwardRel.done (.regular hRel)

/-- Compose one compiler-owned target prefix with the residual source list.
Regular completion continues under the dynamically returned target context;
abrupt and terminal completion skip the unreachable suffix. -/
theorem cons
    {headLayout finalLayout : List Functions.Name}
    {sourceFuel targetFuel : Nat}
    {sourceScopes : SourceScopes}
    {stmt : AstStmt} {rest : List AstStmt}
    {lowerHead lowerRest : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hHead :
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel headLayout sourceScopes)
        (Yul.InteractionSemantics.exec
          sourceFuel stmt codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := lowerHead } target))
    (hTail :
      ∀ {sourceMid : Yul.InteractionSemantics.State}
        {targetMid : Functions.InteractionSemantics.State}
        {ctxMid : Functions.Source.Ctx},
        ScopedStateRel headLayout sourceMid targetMid →
          Simulation.Interaction.ForwardRel Truncated
            (ControlDoneRel finalLayout sourceScopes)
            (Yul.InteractionSemantics.execSeq
              sourceFuel rest codeOverride sourceMid)
            (Functions.InteractionSemantics.Block.openRun
              program ctxMid (targetFuel - lowerHead.length)
                { stmts := lowerRest } targetMid)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel finalLayout sourceScopes)
      (Yul.InteractionSemantics.execSeq
        (sourceFuel + 1) (stmt :: rest) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
          { stmts := lowerHead ++ lowerRest } target) := by
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ,
    Functions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind_custom hHead
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | @regular sourceMid targetMid ctxMid hState =>
      rcases hState.state with
        ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
      subst sourceMid
      simpa using hTail hState
  | @brk sourceMid targetOutcome ctxMid scope hScope hMode hAbrupt =>
      obtain ⟨jump, hSource⟩ :=
        ModeRel.target_nonregular_source_checkpoint
          hAbrupt.mode (by simpa [hMode])
      subst sourceMid
      simpa [hMode] using
        (Simulation.Interaction.ForwardRel.done
          (ControlDoneRel.brk hScope hMode hAbrupt))
  | @cont sourceMid targetOutcome ctxMid scope hScope hMode hAbrupt =>
      obtain ⟨jump, hSource⟩ :=
        ModeRel.target_nonregular_source_checkpoint
          hAbrupt.mode (by simpa [hMode])
      subst sourceMid
      simpa [hMode] using
        (Simulation.Interaction.ForwardRel.done
          (ControlDoneRel.cont hScope hMode hAbrupt))
  | @leave sourceMid targetOutcome ctxMid scope hScope hMode hAbrupt =>
      obtain ⟨jump, hSource⟩ :=
        ModeRel.target_nonregular_source_checkpoint
          hAbrupt.mode (by simpa [hMode])
      subst sourceMid
      simpa [hMode] using
        (Simulation.Interaction.ForwardRel.done
          (ControlDoneRel.leave hScope hMode hAbrupt))
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          simpa using
            (Simulation.Interaction.ForwardRel.done
              (ControlDoneRel.terminal
                (TerminalFailureRel.stop hState)))
      | return_ hState =>
          simpa using
            (Simulation.Interaction.ForwardRel.done
              (ControlDoneRel.terminal
                (TerminalFailureRel.return_ hState)))
      | selfdestruct hState =>
          simpa using
            (Simulation.Interaction.ForwardRel.done
              (ControlDoneRel.terminal
                (TerminalFailureRel.selfdestruct hState)))
      | revert hState =>
          simpa using
            (Simulation.Interaction.ForwardRel.done
              (ControlDoneRel.terminal
                (TerminalFailureRel.revert hState)))

end ControlDoneRel

/-- Adjacent result interface for a compiler-owned terminal argument prelude.
Regular completion supplies the exact typed argument-sequence result; an
internal call may instead propagate a related terminal outcome. -/
inductive PreparedArgsDoneRel
    (layout : List Functions.Name) {results : Nat}
    (seq : Locals.ExprSeq results) :
    Except Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Word) →
      Except EVMException
        (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Prop where
  | error {source target} :
      ErrorRel source target →
        PreparedArgsDoneRel layout seq (.error source) (.error target)
  | regular {source values target targetAfter ctx} :
      values.length = results →
      Locals.InteractionSemantics.ExprSeq.openEval seq target =
        .done (.ok (targetAfter, values)) →
      FunctionsInteractionRelation.ScopedStateRel
        layout source targetAfter →
      PreparedArgsDoneRel layout seq (.ok (source, values))
        (.ok (Functions.Source.Effectful.Outcome.regular target, ctx))
  | terminal {source target ctx} :
      FunctionsInteractionRelation.TerminalFailureRel source target →
        PreparedArgsDoneRel layout seq (.error source) (.ok (target, ctx))

namespace PreparedArgsDoneRel

theorem regular_of_stable
    {layout : List Functions.Name} {results : Nat}
    {lower : List (Locals.Expr 1)} {seq : Locals.ExprSeq results}
    {source : Yul.InteractionSemantics.State}
    {values : List Word}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hSeq : Expr.List.toSeq? lower results = some seq)
    (hStable : FunctionsInteractionExpression.StableArgs
      lower target values)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    PreparedArgsDoneRel layout seq (.ok (source, values))
      (.ok (Functions.Source.Effectful.Outcome.regular target, ctx)) := by
  apply PreparedArgsDoneRel.regular
  · exact hStable.length.trans (Expr.List.toSeq?_length hSeq)
  · exact hStable.exprSeq_openEval hSeq
      (FunctionsInteractionRelation.TargetExtends.refl target.vars)
  · exact hRel

end PreparedArgsDoneRel

/-- Final terminal leaf after a compiler-owned argument prelude has produced
the exact target values. Prelude construction and internal calls are separate
capabilities; this theorem owns only the terminal boundary. -/
theorem terminal_after_args
    {primitiveFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {kind : Assembly.HaltKind}
    {values : List Word} {seq : Locals.ExprSeq kind.argCount}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target targetAfter : Functions.InteractionSemantics.State}
    (hTerminal : Prim.terminal? prim = some kind)
    (hLength : values.length = kind.argCount)
    (hEval :
      Locals.InteractionSemantics.ExprSeq.openEval seq target =
        .done (.ok (targetAfter, values)))
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source targetAfter) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.Primitive.openEval
          primitiveFuel source prim values.reverse)
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [] result.1 result.2)))
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel (.terminalArgs kind seq) target) := by
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  change
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Simulation.Interaction.bind
        (Yul.InteractionSemantics.Primitive.openEval
          primitiveFuel source prim values.reverse)
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [] result.1 result.2)))
      (Simulation.Interaction.bind
        (Locals.InteractionSemantics.ExprSeq.openEval seq target)
        (fun argsResult =>
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.primitiveSemantics.terminal
              kind argsResult.1 argsResult.2)
            (fun final =>
              pure
                (Functions.Source.Effectful.Outcome.halt kind final, ctx))))
  rw [hEval, Simulation.Interaction.bind_done_ok]
  cases primitiveFuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      simpa [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := PathScopedDoneRel layout)
          (right :=
            Simulation.Interaction.bind
              (Functions.InteractionSemantics.primitiveSemantics.terminal
                kind targetAfter values)
              (fun final =>
                pure
                  (Functions.Source.Effectful.Outcome.halt kind final, ctx)))
          hTruncated)
  | succ fuel =>
      cases fuel with
      | zero =>
          have hTruncated :
              Truncated
                ({ exception := .OutOfFuel, state := source } :
                  Yul.InteractionSemantics.Failure) := by
            trivial
          rw [FunctionsInteractionTerminal.openEval_one_of_terminal?
            hTerminal source values.reverse]
          simpa [Yul.InteractionSemantics.Primitive.fail] using
            (Simulation.Interaction.ForwardRel.truncated
              (doneRel := PathScopedDoneRel layout)
              (right :=
                Simulation.Interaction.bind
                  (Functions.InteractionSemantics.primitiveSemantics.terminal
                    kind targetAfter values)
                  (fun final =>
                    pure
                      (Functions.Source.Effectful.Outcome.halt kind final,
                        ctx)))
              hTruncated)
      | succ fuel =>
          have hSourceLength : values.reverse.length = kind.argCount := by
            simpa [List.length_reverse] using hLength
          have hPrimitive :=
            FunctionsInteractionTerminal.of_terminal?
              fuel values.reverse hTerminal hSourceLength hRel.state
          have hPrimitive' :
              Simulation.Interaction.ForwardRel Truncated
                (FunctionsInteractionTerminal.PrimitiveDoneRel kind)
                (Yul.InteractionSemantics.Primitive.openEval
                  (fuel + 2) source prim values.reverse)
                (Functions.InteractionSemantics.primitiveSemantics.terminal
                  kind targetAfter values) := by
            simpa using hPrimitive
          apply Simulation.Interaction.ForwardRel.bind_custom hPrimitive'
          intro sourceDone targetDone hDone
          cases hDone with
          | error hError =>
              exact Simulation.Interaction.ForwardRel.done (.error hError)
          | terminal hTerminalState =>
              exact Simulation.Interaction.ForwardRel.done
                (.terminal hTerminalState)

/-- Compose any adjacent prepared-argument implementation with the terminal
leaf. The prelude proof remains independently owned and may use declarations,
primitive expressions, or internal calls. -/
theorem terminal_of_prepared_args
    {argsFuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {preArgs : List Functions.Stmt}
    {seq : Locals.ExprSeq kind.argCount}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hTerminal : Prim.terminal? prim = some kind)
    (hTailFuel : 2 ≤ targetFuel - preArgs.length)
    (hPrepared :
      Simulation.Interaction.ForwardRel Truncated
        (PreparedArgsDoneRel layout seq)
        (Yul.InteractionSemantics.evalArgs
          argsFuel args.reverse codeOverride source)
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := preArgs } target)) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec (argsFuel + 1)
        (.ExprStmtCall (.Call (.inl prim) args)) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx targetFuel
          { stmts := preArgs ++ [.terminalArgs kind seq] } target) := by
  rw [Yul.InteractionSemantics.Exec.expr_primitive,
    Functions.InteractionSemantics.Block.openRun_append]
  unfold Yul.InteractionSemantics.evalValues
    Yul.Source.Canonical.evalValues
    Yul.Source.Effectful.evalValues
  change
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.evalArgs
            argsFuel args.reverse codeOverride source)
          (fun argsResult =>
            Yul.InteractionSemantics.Primitive.openEval
              argsFuel argsResult.1 prim argsResult.2.reverse))
        (fun result =>
          pure
            (Yul.InteractionSemantics.stateModel.multifill
              [] result.1 result.2)))
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun
          program ctx targetFuel { stmts := preArgs } target)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Functions.InteractionSemantics.Block.openRun
                program result.2 (targetFuel - preArgs.length)
                  { stmts := [.terminalArgs kind seq] } result.1.state
          | .brk | .cont | .leave | .halt _ => pure result))
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.ForwardRel.bind_custom hPrepared
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | @terminal sourceFailure targetOutcome targetCtx hTerminalState =>
      cases hTerminalState with
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
  | @regular sourceAfter values targetAfterPre targetAfter ctxAfter
      hLength hEval hRel =>
      simp only [Simulation.Interaction.bind_done_ok]
      have hStmt :=
        terminal_after_args
          (primitiveFuel := argsFuel)
          (targetFuel := (targetFuel - preArgs.length - 2) + 1)
          (program := program) (ctx := ctxAfter)
          hTerminal hLength hEval hRel
      have hSingleton :=
        PathScopedDoneRel.singleton
          (targetFuel := targetFuel - preArgs.length - 2) hStmt
      simpa [hTailFuel] using hSingleton

namespace InitNames

theorem openRun_extra
    (names : List Functions.Name)
    (program : Functions.Program)
    (target : Functions.InteractionSemantics.State)
    (ctx : Functions.Source.Ctx) (extra : Nat) :
    ∃ finalVars,
      Functions.Source.Store.insertMany names
          (names.map fun _name => Functions.Source.zero)
          target.vars = some finalVars ∧
      Functions.InteractionSemantics.Block.openRun
          program ctx (names.length + extra + 1)
          { stmts := Stmt.initNames names } target =
        pure
          (Functions.Source.Effectful.Outcome.regular
            { shared := target.shared, vars := finalVars },
            { ctx with scope := names.reverse ++ ctx.scope }) := by
  induction names generalizing target ctx with
  | nil =>
      refine ⟨target.vars, rfl, ?_⟩
      simpa [Stmt.initNames] using
        (Functions.InteractionSemantics.Block.openRun_nil
          program ctx extra target)
  | cons name rest ih =>
      let targetHead := target.insert name Functions.Source.zero
      let ctxHead := { ctx with scope := name :: ctx.scope }
      obtain ⟨finalVars, hInsert, hTail⟩ :=
        ih (target := targetHead) (ctx := ctxHead)
      refine ⟨finalVars, ?_, ?_⟩
      · simpa [Functions.Source.Store.insertMany, targetHead,
          Locals.Source.State.insert] using hInsert
      · change
          Functions.InteractionSemantics.Block.openRun
              program ctx ((name :: rest).length + extra + 1)
                { stmts :=
                    .let_ name (.lit Stmt.zero) :: Stmt.initNames rest }
                target = _
        have hHead :=
          Functions.InteractionSemantics.Stmt.openRun_let_lit
            program ctx (rest.length + extra + 1)
            name Stmt.zero target
        change
          Functions.Source.Effectful.Control.Stmt.run
              Functions.InteractionSemantics.stateModel
              Functions.InteractionSemantics.primitiveSemantics
              program ctx (rest.length + extra + 1)
                (.let_ name (.lit Stmt.zero)) target = _ at hHead
        rw [show (name :: rest).length + extra + 1 =
              (rest.length + extra + 1) + 1 by simp; omega,
          Functions.InteractionSemantics.Block.openRun_cons, hHead]
        change
          Functions.Source.Effectful.Control.Block.runOpen
              Functions.InteractionSemantics.stateModel
              Functions.InteractionSemantics.primitiveSemantics
              program ctxHead (rest.length + extra + 1)
                { stmts := Stmt.initNames rest } targetHead = _
        unfold Functions.InteractionSemantics.Block.openRun
          Functions.Source.Canonical.Block.runOpen at hTail
        rw [hTail]
        simp [targetHead, ctxHead, Stmt.initNames,
          List.reverse_cons, List.append_assoc]

theorem openRun
    (names : List Functions.Name)
    (program : Functions.Program)
    (target : Functions.InteractionSemantics.State)
    (ctx : Functions.Source.Ctx) :
    ∃ finalVars,
      Functions.Source.Store.insertMany names
          (names.map fun _name => Functions.Source.zero)
          target.vars = some finalVars ∧
      Functions.InteractionSemantics.Block.openRun
          program ctx (names.length + 1)
          { stmts := Stmt.initNames names } target =
        pure
          (Functions.Source.Effectful.Outcome.regular
            { shared := target.shared, vars := finalVars },
            { ctx with scope := names.reverse ++ ctx.scope }) := by
  induction names generalizing target ctx with
  | nil =>
      refine ⟨target.vars, rfl, ?_⟩
      change
        Functions.InteractionSemantics.Block.openRun
            program ctx 1 { stmts := [] } target =
          pure
            (Functions.Source.Effectful.Outcome.regular
              { shared := target.shared, vars := target.vars }, ctx)
      rw [Functions.InteractionSemantics.Block.openRun_nil]
  | cons name rest ih =>
      let targetHead := target.insert name Functions.Source.zero
      let ctxHead := { ctx with scope := name :: ctx.scope }
      obtain ⟨finalVars, hInsert, hTail⟩ :=
        ih (target := targetHead) (ctx := ctxHead)
      refine ⟨finalVars, ?_, ?_⟩
      · simpa [Functions.Source.Store.insertMany, targetHead,
          Locals.Source.State.insert] using hInsert
      · change
          Functions.InteractionSemantics.Block.openRun
              program ctx ((name :: rest).length + 1)
                { stmts :=
                    .let_ name (.lit Stmt.zero) :: Stmt.initNames rest }
                target = _
        have hHead :=
          Functions.InteractionSemantics.Stmt.openRun_let_lit
            program ctx (rest.length + 1) name Stmt.zero target
        change
          Functions.Source.Effectful.Control.Stmt.run
              Functions.InteractionSemantics.stateModel
              Functions.InteractionSemantics.primitiveSemantics
              program ctx (rest.length + 1)
                (.let_ name (.lit Stmt.zero)) target = _ at hHead
        rw [show (name :: rest).length + 1 = (rest.length + 1) + 1 by simp,
          Functions.InteractionSemantics.Block.openRun_cons, hHead]
        change
          Functions.Source.Effectful.Control.Block.runOpen
              Functions.InteractionSemantics.stateModel
              Functions.InteractionSemantics.primitiveSemantics
              program ctxHead (rest.length + 1)
                { stmts := Stmt.initNames rest } targetHead = _
        unfold Functions.InteractionSemantics.Block.openRun
          Functions.Source.Canonical.Block.runOpen at hTail
        rw [hTail]
        simp [targetHead, ctxHead, Stmt.initNames,
          List.reverse_cons, List.append_assoc]

end InitNames

theorem expr
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {fuel targetFuel : Nat}
    {expr : AstExpr} {lower : Locals.Expr 0}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 0 expr = some lower)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
      (Yul.InteractionSemantics.exec fuel (.ExprStmtCall expr)
        codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel (.expr lower) target) := by
  cases expr with
  | Lit value =>
      simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
  | Var name =>
      simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
  | Call callee args =>
      cases callee with
      | inr functionName =>
          simp [EvmCompiler.Yul.Expr.toLocals?] at hLower
      | inl prim =>
          rw [Yul.InteractionSemantics.Exec.expr_primitive,
            Functions.InteractionSemantics.Stmt.openRun_expr]
          have hEval :=
            (FunctionsInteractionExpression.directAt
              hPrimitive codeOverride fuel).evalValues hLower hRel.state
          apply Simulation.Interaction.ForwardRel.bind hEval
          intro sourceResult targetResult hResult
          have hMultifill :
              Yul.InteractionSemantics.stateModel.multifill []
                  sourceResult.1 sourceResult.2 =
                sourceResult.1 := by
            cases sourceResult.1 <;> rfl
          simpa [hMultifill] using
            (Simulation.Interaction.ForwardRel.done
              (truncated := Truncated)
              (Simulation.Interaction.ExceptRel.ok
                (show
                  ScopedResultRel layout ctx sourceResult.1
                    (Functions.Source.Effectful.Outcome.regular
                      targetResult.1, ctx) from
                  ⟨FunctionsInteractionRelation.ScopedOutcomeRel.regular
                      (FunctionsInteractionRelation.ScopedStateRel.of_state_store_eq
                        hRel hResult.1 hResult.2.2.2),
                    rfl⟩)))

theorem let_one
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {fuel targetFuel : Nat}
    {name : EvmYul.Identifier} {valueExpr : AstExpr}
    {lower : Locals.Expr 1}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 1 valueExpr = some lower)
    (hFresh : name ∉ layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (ScopedDoneRel (name :: layout)
        { ctx with scope := name :: ctx.scope })
      (Yul.InteractionSemantics.exec fuel
        (.Let [name] (some valueExpr)) codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel (.let_ name lower) target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ScopedDoneRel (name :: layout)
            { ctx with scope := name :: ctx.scope })
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel (.let_ name lower) target)
          hTruncated)
  | succ exprFuel =>
      have hCheck :=
        FunctionsInteractionRelation.ScopedStateRel.declarationCheck
          hRel hFresh
      rw [Yul.InteractionSemantics.Exec.let_one_succ
          exprFuel name valueExpr codeOverride source hCheck,
        Functions.InteractionSemantics.Stmt.openRun_let]
      have hEval :=
        (FunctionsInteractionExpression.directAt
          hPrimitive codeOverride exprFuel).evalValues hLower hRel.state
      apply Simulation.Interaction.ForwardRel.bind
        (by simpa [Functions.InteractionSemantics.Expr.openEval] using hEval)
      intro sourceResult targetResult hResult
      rcases hResult with ⟨hState, hValues, hLength, hStore⟩
      obtain ⟨value, hSourceValues⟩ := List.length_eq_one_iff.mp hLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hValues, hSourceValues]
      have hScopedAfterExpr :=
        FunctionsInteractionRelation.ScopedStateRel.of_state_store_eq
          hRel hState hStore
      have hFinal :=
        FunctionsInteractionRelation.ScopedStateRel.multifill_single_cons
          hScopedAfterExpr name value
      have hDone :
          ScopedDoneRel (name :: layout)
              { ctx with scope := name :: ctx.scope }
            (.ok (sourceResult.1.multifill [name] [value]))
            (.ok
              (Functions.Source.Effectful.Outcome.regular
                  (targetResult.1.insert name value),
                { ctx with scope := name :: ctx.scope })) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.regular hFinal,
            rfl⟩
      rw [hSourceValues, hTargetValues]
      simpa [Yul.InteractionSemantics.stateModel,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.insert] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)

theorem assign_one
    (hPrimitive : FunctionsInteractionPrimitive.CompilerSelected)
    {fuel targetFuel : Nat}
    {name : EvmYul.Identifier} {valueExpr : AstExpr}
    {lower : Locals.Expr 1}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower : EvmCompiler.Yul.Expr.toLocals? 1 valueExpr = some lower)
    (hName : name ∈ layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
      (Yul.InteractionSemantics.exec fuel
        (.Assign [name] valueExpr) codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel (.assign name lower) target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ScopedDoneRel layout ctx)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel (.assign name lower) target)
          hTruncated)
  | succ exprFuel =>
      have hCheck :=
        FunctionsInteractionRelation.ScopedStateRel.assignmentCheck
          hRel hName
      have hContains :=
        FunctionsInteractionRelation.ScopedStateRel.targetContains
          hRel hName
      rw [Yul.InteractionSemantics.Exec.assign_one_succ
          exprFuel name valueExpr codeOverride source hCheck,
        Functions.InteractionSemantics.Stmt.openRun_assign
          program ctx targetFuel name lower target hContains]
      have hEval :=
        (FunctionsInteractionExpression.directAt
          hPrimitive codeOverride exprFuel).evalValues hLower hRel.state
      apply Simulation.Interaction.ForwardRel.bind
        (by simpa [Functions.InteractionSemantics.Expr.openEval] using hEval)
      intro sourceResult targetResult hResult
      rcases hResult with ⟨hState, hValues, hLength, hStore⟩
      obtain ⟨value, hSourceValues⟩ := List.length_eq_one_iff.mp hLength
      have hTargetValues : targetResult.2 = [value] := by
        rw [← hValues, hSourceValues]
      have hScopedAfterExpr :=
        FunctionsInteractionRelation.ScopedStateRel.of_state_store_eq
          hRel hState hStore
      have hFinal :=
        FunctionsInteractionRelation.ScopedStateRel.multifill_single_visible
          hScopedAfterExpr hName value
      have hDone :
          ScopedDoneRel layout ctx
            (.ok (sourceResult.1.multifill [name] [value]))
            (.ok
              (Functions.Source.Effectful.Outcome.regular
                  (targetResult.1.insert name value), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.regular hFinal,
            rfl⟩
      rw [hSourceValues, hTargetValues]
      simpa [Yul.InteractionSemantics.stateModel,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.withVars,
        Locals.Source.State.withVars] using
        (Simulation.Interaction.ForwardRel.done
          (truncated := Truncated) hDone)

theorem brk
    {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hScope : ctx.breakScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
      (Yul.InteractionSemantics.exec fuel .Break codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel .brk target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.brk_zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ScopedDoneRel layout ctx)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel .brk target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hRestricted :
          FunctionsInteractionRelation.StateRel
            (.Ok sourceShared sourceVars) (target.restrictTo scope) :=
        hRel.restrictTarget hSubset
      have hDone :
          ScopedDoneRel layout ctx
            (.ok (.Checkpoint (.Break sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.brk
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.brk_restrict
              { state := ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
                domain := hRel.domain
                defined := hRel.defined }
              hSubset,
            rfl⟩
      rw [Yul.InteractionSemantics.Exec.brk_succ,
        Functions.InteractionSemantics.Stmt.openRun_brk
          program ctx targetFuel target hScope]
      exact Simulation.Interaction.ForwardRel.done hDone

theorem cont
    {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hScope : ctx.continueScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
      (Yul.InteractionSemantics.exec fuel .Continue codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel .cont target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ScopedDoneRel layout ctx)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel .cont target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hRestricted :
          FunctionsInteractionRelation.StateRel
            (.Ok sourceShared sourceVars) (target.restrictTo scope) :=
        hRel.restrictTarget hSubset
      have hDone :
          ScopedDoneRel layout ctx
            (.ok (.Checkpoint (.Continue sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.cont
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.cont_restrict
              { state := ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
                domain := hRel.domain
                defined := hRel.defined }
              hSubset,
            rfl⟩
      rw [Yul.InteractionSemantics.Exec.cont_succ,
        Functions.InteractionSemantics.Stmt.openRun_cont
          program ctx targetFuel target hScope]
      exact Simulation.Interaction.ForwardRel.done hDone

theorem leave
    {fuel targetFuel : Nat}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hScope : ctx.leaveScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated (ScopedDoneRel layout ctx)
      (Yul.InteractionSemantics.exec fuel .Leave codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel .leave target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := ScopedDoneRel layout ctx)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel .leave target)
          hTruncated)
  | succ fuel =>
      rcases hRel.state with
        ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
      subst source
      have hRestricted :
          FunctionsInteractionRelation.StateRel
            (.Ok sourceShared sourceVars) (target.restrictTo scope) :=
        hRel.restrictTarget hSubset
      have hDone :
          ScopedDoneRel layout ctx
            (.ok (.Checkpoint (.Leave sourceShared sourceVars)))
            (.ok
              (Functions.Source.Effectful.Outcome.leave
                (target.restrictTo scope), ctx)) :=
        .ok
          ⟨FunctionsInteractionRelation.ScopedOutcomeRel.leave_restrict
              { state := ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
                domain := hRel.domain
                defined := hRel.defined }
              hSubset,
            rfl⟩
      rw [Yul.InteractionSemantics.Exec.leave_succ,
        Functions.InteractionSemantics.Stmt.openRun_leave
          program ctx targetFuel target hScope]
      exact Simulation.Interaction.ForwardRel.done hDone

/-- Terminal statement preservation when the compiler can use the direct
argument sequence. Generated argument preludes compose through the same final
leaf theorem once their prepared-state relation is available. -/
theorem terminal_direct
    {fuel targetFuel : Nat}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq kind.argCount}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hTerminal : Prim.terminal? prim = some kind)
    (hArgsLower : Expr.List.toLocals1? args = some lowerArgs)
    (hSeq : Expr.List.toStackSeq? lowerArgs kind.argCount = some seq)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel
        (.ExprStmtCall (.Call (.inl prim) args)) codeOverride source)
      (Functions.InteractionSemantics.Stmt.openRun
        program ctx targetFuel (.terminalArgs kind seq) target) := by
  cases fuel with
  | zero =>
      have hTruncated :
          Truncated
            ({ exception := .OutOfFuel, state := source } :
              Yul.InteractionSemantics.Failure) := by
        trivial
      rw [Yul.InteractionSemantics.Exec.zero]
      simpa [Yul.InteractionSemantics.Primitive.fail] using
        (Simulation.Interaction.ForwardRel.truncated
          (doneRel := PathScopedDoneRel layout)
          (right := Functions.InteractionSemantics.Stmt.openRun
            program ctx targetFuel (.terminalArgs kind seq) target)
          hTruncated)
  | succ argsFuel =>
      have hLowerReverse :
          Expr.List.toLocals1? args.reverse =
            some lowerArgs.reverse :=
        Expr.List.toLocals1?_reverse hArgsLower
      have hDirectSeq :
          Expr.List.toSeq? lowerArgs.reverse kind.argCount = some seq := by
        simpa [Expr.List.toStackSeq?] using hSeq
      have hArgs :=
        (FunctionsInteractionExpression.compilerDirectAt
          codeOverride argsFuel).evalArgs hLowerReverse hDirectSeq hRel.state
      rw [Yul.InteractionSemantics.Exec.expr_primitive]
      unfold Yul.InteractionSemantics.evalValues
        Yul.Source.Canonical.evalValues
        Yul.Source.Effectful.evalValues
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run
      simp only [Functions.Source.Effectful.Control.Stmt.run]
      change
        Simulation.Interaction.ForwardRel Truncated
          (PathScopedDoneRel layout)
          (Simulation.Interaction.bind
            (Simulation.Interaction.bind
              (Yul.Source.Effectful.evalArgs
                Yul.InteractionSemantics.stateModel
                Yul.InteractionSemantics.primitiveSemantics
                argsFuel args.reverse codeOverride source)
              (fun argsResult =>
                Yul.InteractionSemantics.primitiveSemantics.eval
                  argsFuel argsResult.1 prim argsResult.2.reverse))
            (fun result =>
              pure
                (Yul.InteractionSemantics.stateModel.multifill
                  [] result.1 result.2)))
          (Simulation.Interaction.bind
            (Locals.Source.Effectful.Expr.Control.ExprSeq.eval
              Functions.InteractionSemantics.stateModel
              Functions.InteractionSemantics.primitiveSemantics
              seq target)
            (fun argsResult =>
              Simulation.Interaction.bind
                (Functions.InteractionSemantics.primitiveSemantics.terminal
                  kind argsResult.1 argsResult.2)
                (fun final =>
                  pure
                    (Functions.Source.Effectful.Outcome.halt kind final,
                      ctx))))
      rw [Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.ForwardRel.bind_custom hArgs
      intro sourceDone targetDone hDone
      cases hDone with
      | error hError =>
          exact Simulation.Interaction.ForwardRel.done (.error hError)
      | @ok sourceResult targetResult hResult =>
          rcases hResult with ⟨hState, hValues, hLength, hStore⟩
          simp only [Simulation.Interaction.bind_done_ok]
          cases argsFuel with
          | zero =>
              have hTruncated :
                  Truncated
                    ({ exception := .OutOfFuel, state := sourceResult.1 } :
                      Yul.InteractionSemantics.Failure) := by
                trivial
              simpa [Yul.InteractionSemantics.Primitive.openEval,
                Yul.InteractionSemantics.Primitive.fail] using
                (Simulation.Interaction.ForwardRel.truncated
                  (doneRel := PathScopedDoneRel layout)
                  (right :=
                    Simulation.Interaction.bind
                      (Functions.InteractionSemantics.primitiveSemantics.terminal
                        kind targetResult.1 targetResult.2)
                      (fun final =>
                        pure
                          (Functions.Source.Effectful.Outcome.halt kind final,
                            ctx)))
                  hTruncated)
          | succ primitiveFuel =>
              cases primitiveFuel with
              | zero =>
                  have hTruncated :
                      Truncated
                        ({ exception := .OutOfFuel,
                            state := sourceResult.1 } :
                          Yul.InteractionSemantics.Failure) := by
                    trivial
                  rw [show
                    Yul.InteractionSemantics.primitiveSemantics.eval
                        1 sourceResult.1 prim sourceResult.2.reverse =
                      Yul.InteractionSemantics.Primitive.fail
                        sourceResult.1 .OutOfFuel by
                    exact
                      FunctionsInteractionTerminal.openEval_one_of_terminal?
                        hTerminal sourceResult.1 sourceResult.2.reverse]
                  simpa [Yul.InteractionSemantics.Primitive.fail] using
                    (Simulation.Interaction.ForwardRel.truncated
                      (doneRel := PathScopedDoneRel layout)
                      (right :=
                        Simulation.Interaction.bind
                          (Functions.InteractionSemantics.primitiveSemantics.terminal
                            kind targetResult.1 targetResult.2)
                          (fun final =>
                            pure
                              (Functions.Source.Effectful.Outcome.halt kind
                                final, ctx)))
                      hTruncated)
              | succ terminalFuel =>
                  have hSourceLength :
                      sourceResult.2.reverse.length = kind.argCount := by
                    simpa [List.length_reverse] using hLength
                  have hTerminalRel :=
                    FunctionsInteractionTerminal.of_terminal?
                      terminalFuel sourceResult.2.reverse
                      hTerminal hSourceLength hState
                  have hTerminalRel' :
                      Simulation.Interaction.ForwardRel Truncated
                        (FunctionsInteractionTerminal.PrimitiveDoneRel kind)
                        (Yul.InteractionSemantics.Primitive.openEval
                          (terminalFuel + 2) sourceResult.1 prim
                            sourceResult.2.reverse)
                        (Functions.InteractionSemantics.primitiveSemantics.terminal
                          kind targetResult.1 targetResult.2) := by
                    simpa [hValues] using hTerminalRel
                  apply Simulation.Interaction.ForwardRel.bind_custom
                    hTerminalRel'
                  intro sourceTerminalDone targetTerminalDone hTerminalDone
                  cases hTerminalDone with
                  | error hError =>
                      exact Simulation.Interaction.ForwardRel.done
                        (.error hError)
                  | terminal hTerminalState =>
                      exact Simulation.Interaction.ForwardRel.done
                        (.terminal hTerminalState)

/-- Compiler-selected terminal statement for the stable direct argument
window. The ordinary compiler decomposition and bounded-argument inversion
construct the exact singleton target block internally. -/
theorem compiled_terminal_direct
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {prim : EvmYul.Operation .Yul} {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hTerminal : Prim.terminal? prim = some kind)
    (hDirect : ∀ expr, expr ∈ args → Expr.deferredBoundArgSafe? expr = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.ExprStmtCall (.Call (.inl prim) args)) = some (lower, after))
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel
        (.ExprStmtCall (.Call (.inl prim) args)) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  obtain ⟨preArgs, lowerArgs, seq, hLowerArgs, hSeq, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_terminal_parts
      hTerminal hLower
  have hLowerLength : lowerArgs.length = args.length :=
    Expr.List.lowerBound1Unchecked?_length_lowerArgs_eq hLowerArgs
  have hSeq' :
      Expr.List.toSeq? lowerArgs.reverse kind.argCount = some seq := by
    simpa [Expr.List.toStackSeq?] using hSeq
  have hSeqLength : lowerArgs.length = kind.argCount := by
    simpa [List.length_reverse] using Expr.List.toSeq?_length hSeq'
  have hArgsLength : args.length = kind.argCount :=
    hLowerLength.symm.trans hSeqLength
  have hWindow : args.length < 5 := by
    rw [hArgsLength]
    cases kind <;> decide
  obtain ⟨rfl, _hAfter, hArgsDirect⟩ :=
    Expr.lowerBound1Unchecked?_direct_parts
      hLowerArgs hDirect hWindow
  simp only [List.nil_append] at hLowerStmts
  subst lower
  apply PathScopedDoneRel.singleton
  exact terminal_direct hTerminal hArgsDirect hSeq hRel

theorem compiled_let_none
    {compilerFuel fuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {names : List EvmYul.Identifier}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Let names none) = some (lower, after))
    (hNoDup : (identNames names).Nodup)
    (hFresh : ∀ name, name ∈ identNames names → name ∉ layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel (identNames names ++ layout))
      (Yul.InteractionSemantics.exec
        (fuel + 1) (.Let names none) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (names.length + 1) { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_let_none_parts hLower with
    ⟨rfl, rfl⟩
  have hCheck : EvmYul.Yul.checkDeclaration source names = .ok () := by
    simpa [identNames_eq_self] using
      FunctionsInteractionRelation.ScopedStateRel.declarationCheck_many
        hRel hNoDup hFresh
  obtain ⟨finalVars, hInsert, hTargetRun⟩ :=
    InitNames.openRun (identNames names) program target ctx
  have hFinalRel :
      FunctionsInteractionRelation.ScopedStateRel
        (identNames names ++ layout) (source.zeroFill names)
          { shared := target.shared, vars := finalVars } := by
    simpa [identNames_eq_self] using
      FunctionsInteractionRelation.ScopedStateRel.zeroFill_insertMany
        hRel hNoDup hFresh hInsert
  have hDone :
      PathScopedDoneRel (identNames names ++ layout)
        (.ok (source.zeroFill names))
        (.ok
          (Functions.Source.Effectful.Outcome.regular
            { shared := target.shared, vars := finalVars },
            { ctx with scope := (identNames names).reverse ++ ctx.scope })) :=
    .ok
      ⟨identNames names ++ layout,
        FunctionsInteractionRelation.ScopedOutcomeRel.regular hFinalRel,
        fun _ => rfl⟩
  rw [Yul.InteractionSemantics.Exec.let_none_succ
      fuel names codeOverride source hCheck]
  rw [identNames_eq_self]
  simp only [identNames_eq_self] at hTargetRun
  rw [hTargetRun]
  simpa [identNames_eq_self] using
    (Simulation.Interaction.ForwardRel.done hDone :
      Simulation.Interaction.ForwardRel Truncated
        (PathScopedDoneRel (identNames names ++ layout))
        (pure (source.zeroFill names))
        (pure
          (Functions.Source.Effectful.Outcome.regular
            { shared := target.shared, vars := finalVars },
            { ctx with scope := (identNames names).reverse ++ ctx.scope })))

theorem compiled_let_one_direct
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {name : EvmYul.Identifier} {valueExpr : AstExpr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        valueExpr ≠ .Call (.inr functionName) functionArgs)
    (hDirect : Expr.directPureArgSafeAt? 0 valueExpr = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Let [name] (some valueExpr)) = some (lower, after))
    (hFresh : identName name ∉ layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel (identName name :: layout))
      (Yul.InteractionSemantics.exec fuel
        (.Let [name] (some valueExpr)) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  obtain ⟨pre, lowerValue, hValueLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_let_one_parts
      hNotFunctionCall hLower
  obtain ⟨rfl, rfl, hValueDirect⟩ :=
    Expr.lower1Unchecked?_direct_parts hDirect hValueLower
  simp only [List.nil_append] at hLowerStmts
  subst lower
  apply PathScopedDoneRel.singleton
  apply PathScopedDoneRel.of_fixed
  exact let_one FunctionsInteractionClosedPrimitive.compilerSelected
    hValueDirect hFresh hRel

theorem compiled_assign_one_direct
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {name : EvmYul.Identifier} {valueExpr : AstExpr}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hNotFunctionCall :
      ∀ functionName functionArgs,
        valueExpr ≠ .Call (.inr functionName) functionArgs)
    (hDirect : Expr.directPureArgSafeAt? 0 valueExpr = true)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.Assign [name] valueExpr) = some (lower, after))
    (hName : identName name ∈ layout)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel
        (.Assign [name] valueExpr) codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  obtain ⟨pre, lowerValue, hValueLower, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_assign_one_parts
      hNotFunctionCall hLower
  obtain ⟨rfl, rfl, hValueDirect⟩ :=
    Expr.lower1Unchecked?_direct_parts hDirect hValueLower
  simp only [List.nil_append] at hLowerStmts
  subst lower
  apply PathScopedDoneRel.singleton
  apply PathScopedDoneRel.of_fixed
  exact assign_one FunctionsInteractionClosedPrimitive.compilerSelected
    hValueDirect hName hRel

theorem compiled_brk
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Break =
        some (lower, after))
    (hScope : ctx.breakScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel .Break codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_break_parts hLower with
    ⟨rfl, rfl⟩
  apply PathScopedDoneRel.singleton
  apply PathScopedDoneRel.of_fixed
  exact brk hScope hSubset hRel

theorem compiled_cont
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Continue =
        some (lower, after))
    (hScope : ctx.continueScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel .Continue codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_continue_parts hLower with
    ⟨rfl, rfl⟩
  apply PathScopedDoneRel.singleton
  apply PathScopedDoneRel.of_fixed
  exact cont hScope hSubset hRel

theorem compiled_leave
    {compilerFuel fuel targetFuel : Nat}
    {before after : Fresh.State} {lower : List Functions.Stmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {program : Functions.Program} {ctx : Functions.Source.Ctx}
    {layout scope : List Functions.Name}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before .Leave =
        some (lower, after))
    (hScope : ctx.leaveScope? = some scope)
    (hSubset : ∀ name, name ∈ layout → name ∈ scope)
    (hRel : FunctionsInteractionRelation.ScopedStateRel
      layout source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PathScopedDoneRel layout)
      (Yul.InteractionSemantics.exec fuel .Leave codeOverride source)
      (Functions.InteractionSemantics.Block.openRun
        program ctx (targetFuel + 2) { stmts := lower } target) := by
  rcases Stmt.toFunctionsListUncheckedFuel?_leave_parts hLower with
    ⟨rfl, rfl⟩
  apply PathScopedDoneRel.singleton
  apply PathScopedDoneRel.of_fixed
  exact leave hScope hSubset hRel

end FunctionsInteractionStatement
end Yul
end EvmCompiler
