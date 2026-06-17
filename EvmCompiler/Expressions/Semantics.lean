import EvmCompiler.Expressions.EffectSemantics

namespace EvmCompiler
namespace Expressions

abbrev RunState := Structured.RunState
abbrev Outcome := Structured.Outcome

abbrev invalid {α : Type} : Except EVMException α :=
  Structured.invalid

namespace Outcome

abbrev regular := Structured.Outcome.regular
abbrev brk := Structured.Outcome.brk
abbrev cont := Structured.Outcome.cont
abbrev leave := Structured.Outcome.leave
abbrev halt := Structured.Outcome.halt

end Outcome

mutual
  def Expr.run {results : Nat} (expr : Expr results)
      (state : EVMState) : Except EVMException EVMState :=
    EffectSemantics.Control.Expr.run
      EffectSemantics.Ordinary.evmHandler expr state

  def ExprSeq.run {results : Nat} (exprs : ExprSeq results)
      (state : EVMState) : Except EVMException EVMState :=
    EffectSemantics.Control.ExprSeq.run
      EffectSemantics.Ordinary.evmHandler exprs state
end

namespace Expr

def runState {results : Nat} (expr : Expr results) (state : RunState) :
    Except EVMException RunState :=
  EffectSemantics.Control.Expr.run
    EffectSemantics.Ordinary.runStateHandler expr state

def runCondition (cond : Expr 1) (state : EVMState) :
    Except EVMException (EVMState × Bool) :=
  EffectSemantics.Control.Expr.runCondition
    Structured.EffectSemantics.Ordinary.evmStateModel
    EffectSemantics.Ordinary.evmHandler cond state

def runConditionState (cond : Expr 1) (state : RunState) :
    Except EVMException (RunState × Bool) :=
  EffectSemantics.Control.Expr.runCondition
    Structured.EffectSemantics.Ordinary.runStateModel
    EffectSemantics.Ordinary.runStateHandler cond state

end Expr

abbrev ProcList.lookup? := EffectSemantics.ProcList.lookup?
abbrev Switch.select := EffectSemantics.Switch.select

mutual
  def Block.run (program : Program) : Nat → Block → RunState →
      Except EVMException Outcome
    | fuel, block, state =>
        EffectSemantics.Control.Block.run
          Structured.EffectSemantics.Ordinary.runStateModel
          EffectSemantics.Ordinary.runStateHandler
          program fuel block state

  def Stmt.runForLoop (program : Program) (fuel : Nat) (cond : Expr 1)
      (post body : Block) (state : RunState) :
      Except EVMException Outcome :=
    EffectSemantics.Control.Stmt.runForLoop
      Structured.EffectSemantics.Ordinary.runStateModel
      EffectSemantics.Ordinary.runStateHandler
      program fuel cond post body state

  def Stmt.run (program : Program) : Nat → Stmt → RunState →
      Except EVMException Outcome
    | fuel, stmt, state =>
        EffectSemantics.Control.Stmt.run
          Structured.EffectSemantics.Ordinary.runStateModel
          EffectSemantics.Ordinary.runStateHandler
          program fuel stmt state
end

namespace Program

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  Block.run program fuel program.body (Structured.Program.initialState state)

inductive Eval :
    Nat → Program → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program} {initial : EVMState}
      {outcome : Outcome}
      (hRun : program.run fuel initial = .ok outcome) :
      Eval fuel program initial outcome

theorem eval_of_run {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hRun : run fuel program initial = .ok outcome) :
    Eval fuel program initial outcome := by
  exact Eval.ofRun hRun

end Program

end Expressions
end EvmCompiler
