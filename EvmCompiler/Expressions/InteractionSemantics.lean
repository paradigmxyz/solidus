import EvmCompiler.Expressions.EffectSemantics
import EvmCompiler.Structured.InteractionSemantics

namespace EvmCompiler
namespace Expressions
namespace InteractionSemantics

abbrev Open (α : Type) :=
  Simulation.Interaction EVMException α

abbrev RunState := Structured.RunState
abbrev Outcome := Structured.Outcome

namespace Expr

def openRun {results : Nat} (expr : Expressions.Expr results)
    (state : RunState) : Open RunState :=
  EffectSemantics.Control.Expr.run
    Structured.InteractionSemantics.handler expr state

def openRunCondition (cond : Expressions.Expr 1)
    (state : RunState) : Open (RunState × Bool) :=
  EffectSemantics.Control.Expr.runCondition
    Structured.EffectSemantics.Ordinary.runStateModel
    Structured.InteractionSemantics.handler cond state

end Expr

namespace ExprSeq

def openRun {results : Nat} (exprs : Expressions.ExprSeq results)
    (state : RunState) : Open RunState :=
  EffectSemantics.Control.ExprSeq.run
    Structured.InteractionSemantics.handler exprs state

end ExprSeq

namespace Block

def openRun (program : Expressions.Program) (fuel : Nat)
    (block : Expressions.Block) (state : RunState) : Open Outcome :=
  EffectSemantics.Control.Block.run
    Structured.EffectSemantics.Ordinary.runStateModel
    Structured.InteractionSemantics.handler
    program fuel block state

/-- One target statement followed by its exact residual block. -/
theorem openRun_cons
    (program : Expressions.Program) (fuel : Nat)
    (stmt : Expressions.Stmt) (rest : List Expressions.Stmt)
    (state : RunState) :
    openRun program (fuel + 1) { stmts := stmt :: rest } state =
      Simulation.Interaction.bind
        (EffectSemantics.Control.Stmt.run
          Structured.EffectSemantics.Ordinary.runStateModel
          Structured.InteractionSemantics.handler
          program fuel stmt state)
        (fun outcome =>
          match outcome.mode with
          | .regular =>
              openRun program fuel { stmts := rest } outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome) := by
  cases fuel <;> rfl

/-- A nonzero-fuel empty target block is the regular identity. -/
theorem openRun_nil
    (program : Expressions.Program) (fuel : Nat) (state : RunState) :
    openRun program (fuel + 1) { stmts := [] } state =
      Simulation.Interaction.pure (Structured.Outcome.regular state) := by
  cases fuel <;> rfl

/-- A singleton target block exposes its statement at residual fuel. -/
theorem openRun_single_stmt
    (program : Expressions.Program) (fuel : Nat)
    (stmt : Expressions.Stmt) (state : RunState) :
    openRun program (fuel + 2) { stmts := [stmt] } state =
      EffectSemantics.Control.Stmt.run
        Structured.EffectSemantics.Ordinary.runStateModel
        Structured.InteractionSemantics.handler
        program (fuel + 1) stmt state := by
  unfold openRun
  simp only [EffectSemantics.Control.Block.run]
  change
    Simulation.Interaction.bind
        (EffectSemantics.Control.Stmt.run
          Structured.EffectSemantics.Ordinary.runStateModel
          Structured.InteractionSemantics.handler
          program (fuel + 1) stmt state) _ =
      EffectSemantics.Control.Stmt.run
        Structured.EffectSemantics.Ordinary.runStateModel
        Structured.InteractionSemantics.handler
        program (fuel + 1) stmt state
  conv_rhs =>
    rw [← Simulation.Interaction.bind_pure
      (EffectSemantics.Control.Stmt.run
        Structured.EffectSemantics.Ordinary.runStateModel
        Structured.InteractionSemantics.handler
        program (fuel + 1) stmt state)]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (EffectSemantics.Control.Stmt.run
        Structured.EffectSemantics.Ordinary.runStateModel
        Structured.InteractionSemantics.handler
        program (fuel + 1) stmt state))
  intro outcome _
  rcases outcome with ⟨outcomeState, outcomeMode⟩
  cases outcomeMode <;> rfl

/-- A singleton conditional exposes its condition and selected body. -/
theorem openRun_single_if
    (program : Expressions.Program) (fuel : Nat)
    (cond : Expressions.Expr 1) (body : Expressions.Block)
    (state : RunState) :
    openRun program (fuel + 2) { stmts := [.if_ cond body] } state =
      Simulation.Interaction.bind
        (Expr.openRunCondition cond state)
        (fun result =>
          if result.2 then
            openRun program fuel body result.1
          else
            Simulation.Interaction.pure
              (Structured.Outcome.regular result.1)) := by
  rw [openRun_single_stmt]
  unfold Expr.openRunCondition EffectSemantics.Control.Expr.runCondition
  simp only [EffectSemantics.Control.Stmt.run]
  rfl

/--
Executing an appended block factors through the left block. A regular left
outcome continues with the exact residual list fuel; abrupt outcomes skip the
right block. This is the interaction-owner sequence law used by adjacent
compiler passes.
-/
theorem openRun_append
    (program : Expressions.Program) :
    ∀ (left right : List Expressions.Stmt) (fuel : Nat)
      (state : RunState),
      openRun program fuel { stmts := left ++ right } state =
        Simulation.Interaction.bind
          (openRun program fuel { stmts := left } state)
          (fun outcome =>
            match outcome.mode with
            | .regular =>
                openRun program (fuel - left.length)
                  { stmts := right } outcome.state
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure outcome) := by
  intro left
  induction left with
  | nil =>
      intro right fuel state
      cases fuel <;> rfl
  | cons stmt rest ih =>
      intro right fuel state
      cases fuel with
      | zero =>
          rfl
      | succ fuel =>
          unfold openRun
          simp only [EffectSemantics.Control.Block.run,
            List.length_cons, Nat.succ_sub_succ_eq_sub]
          change
            Simulation.Interaction.bind
                (EffectSemantics.Control.Stmt.run
                  Structured.EffectSemantics.Ordinary.runStateModel
                  Structured.InteractionSemantics.handler
                  program fuel stmt state)
                _ =
              Simulation.Interaction.bind
                (Simulation.Interaction.bind
                  (EffectSemantics.Control.Stmt.run
                    Structured.EffectSemantics.Ordinary.runStateModel
                    Structured.InteractionSemantics.handler
                    program fuel stmt state)
                  _)
                _
          rw [Simulation.Interaction.bind_assoc]
          congr 1
          funext outcome
          cases hMode : outcome.mode with
          | regular =>
              simpa [hMode] using
                ih right fuel outcome.state
          | brk =>
              change
                Simulation.Interaction.pure outcome =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.pure outcome) _
              unfold Simulation.Interaction.pure
              rw [Simulation.Interaction.bind_done_ok]
              simp [hMode]
          | cont =>
              change
                Simulation.Interaction.pure outcome =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.pure outcome) _
              unfold Simulation.Interaction.pure
              rw [Simulation.Interaction.bind_done_ok]
              simp [hMode]
          | leave =>
              change
                Simulation.Interaction.pure outcome =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.pure outcome) _
              unfold Simulation.Interaction.pure
              rw [Simulation.Interaction.bind_done_ok]
              simp [hMode]
          | halt kind =>
              change
                Simulation.Interaction.pure outcome =
                  Simulation.Interaction.bind
                    (Simulation.Interaction.pure outcome) _
              unfold Simulation.Interaction.pure
              rw [Simulation.Interaction.bind_done_ok]
              simp [hMode]

end Block

namespace Stmt

def openRunForLoop (program : Expressions.Program) (fuel : Nat)
    (cond : Expressions.Expr 1) (post body : Expressions.Block)
    (state : RunState) : Open Outcome :=
  EffectSemantics.Control.Stmt.runForLoop
    Structured.EffectSemantics.Ordinary.runStateModel
    Structured.InteractionSemantics.handler
    program fuel cond post body state

def openRun (program : Expressions.Program) (fuel : Nat)
    (stmt : Expressions.Stmt) (state : RunState) : Open Outcome :=
  EffectSemantics.Control.Stmt.run
    Structured.EffectSemantics.Ordinary.runStateModel
    Structured.InteractionSemantics.handler
    program fuel stmt state

end Stmt

namespace Program

def openRunState (fuel : Nat) (program : Expressions.Program)
    (state : RunState) : Open Outcome :=
  EffectSemantics.Control.Program.runState
    Structured.EffectSemantics.Ordinary.runStateModel
    Structured.InteractionSemantics.handler
    fuel program state

def openRun (fuel : Nat) (program : Expressions.Program)
    (state : EVMState) : Open Outcome :=
  openRunState fuel program (Structured.Program.initialState state)

end Program

end InteractionSemantics
end Expressions
end EvmCompiler
