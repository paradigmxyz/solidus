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
