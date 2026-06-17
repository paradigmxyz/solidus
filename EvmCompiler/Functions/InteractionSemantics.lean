import EvmCompiler.Functions.EffectSemantics
import EvmCompiler.Locals.InteractionSemantics

namespace EvmCompiler
namespace Functions
namespace InteractionSemantics

abbrev Open (α : Type) :=
  Simulation.Interaction EVMException α

abbrev State := Locals.InteractionSemantics.State
abbrev Outcome := Functions.Source.Effectful.Outcome State
abbrev CallResult := Functions.Source.Effectful.CallResult State

def stateModel : Functions.Source.Canonical.StateModel State :=
  Locals.InteractionSemantics.stateModel

def primitiveSemantics :
    Functions.Source.Canonical.PrimitiveSemantics Open State :=
  Locals.InteractionSemantics.primitiveSemantics

namespace ArgList

def openEval (args : List (Functions.Expr 1)) (state : State) :
    Open (State × List Word) :=
  Functions.Source.Canonical.ArgList.eval
    stateModel primitiveSemantics args state

def OpenSupported (args : List (Functions.Expr 1)) : Prop :=
  ∀ expr, expr ∈ args →
    Locals.InteractionSemantics.Expr.OpenSupported expr

end ArgList

namespace Block

def openRun (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (block : Functions.Block) (state : State) :
    Open (Outcome × Functions.Source.Ctx) :=
  Functions.Source.Canonical.Block.runOpen
    stateModel primitiveSemantics program ctx fuel block state

def openRunScoped (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (block : Functions.Block)
    (fuel : Nat) (state : State) : Open Outcome :=
  Functions.Source.Canonical.Block.runScoped
    stateModel primitiveSemantics program ctx block fuel state

end Block

namespace FunDef

def openRunBody (program : Functions.Program) (fn : Functions.FunDef)
    (args : List Word) (fuel : Nat) (state : State) : Open CallResult :=
  Functions.Source.Canonical.FunDef.runBody
    stateModel primitiveSemantics program fn args fuel state

end FunDef

namespace Stmt

def openRunForLoop (program : Functions.Program)
    (loopCtx : Functions.Source.Ctx) (cond : Functions.Expr 1)
    (postBase : Functions.Source.Ctx) (post : Functions.Block)
    (bodyBase : Functions.Source.Ctx) (body : Functions.Block)
    (fuel : Nat) (state : State) : Open Outcome :=
  Functions.Source.Canonical.Stmt.runForLoop
    stateModel primitiveSemantics program loopCtx cond
    postBase post bodyBase body fuel state

def openRun (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (stmt : Functions.Stmt) (state : State) :
    Open (Outcome × Functions.Source.Ctx) :=
  Functions.Source.Canonical.Stmt.run
    stateModel primitiveSemantics program ctx fuel stmt state

end Stmt

mutual
  def Block.OpenSupported : Functions.Block → Prop
    | ⟨stmts⟩ => StmtList.OpenSupported stmts

  def Stmt.OpenSupported : Functions.Stmt → Prop
    | .expr expr => Locals.InteractionSemantics.Expr.OpenSupported expr
    | .let_ _name value =>
        Locals.InteractionSemantics.Expr.OpenSupported value
    | .assign _name value =>
        Locals.InteractionSemantics.Expr.OpenSupported value
    | .block body => Block.OpenSupported body
    | .if_ cond body =>
        Locals.InteractionSemantics.Expr.OpenSupported cond ∧
          Block.OpenSupported body
    | .switch scrutinee cases defaultBody =>
        Locals.InteractionSemantics.Expr.OpenSupported scrutinee ∧
          CaseList.OpenSupported cases ∧ Default.OpenSupported defaultBody
    | .for_ init cond post body =>
        Block.OpenSupported init ∧
          Locals.InteractionSemantics.Expr.OpenSupported cond ∧
          Block.OpenSupported post ∧ Block.OpenSupported body
    | .brk | .cont | .leave | .terminal _kind => True
    | .call _targets _functionName args => ArgList.OpenSupported args
    | .terminalArgs _kind args =>
        Locals.InteractionSemantics.ExprSeq.OpenSupported args

  def StmtList.OpenSupported : List Functions.Stmt → Prop
    | [] => True
    | stmt :: rest =>
        Stmt.OpenSupported stmt ∧ StmtList.OpenSupported rest

  def CaseList.OpenSupported : List (Word × Functions.Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        Block.OpenSupported body ∧ CaseList.OpenSupported rest

  def Default.OpenSupported : Option Functions.Block → Prop
    | none => True
    | some body => Block.OpenSupported body
end

namespace Program

def openRunState (fuel : Nat) (program : Functions.Program)
    (state : State) : Open Outcome :=
  Functions.Source.Canonical.Program.runState
    stateModel primitiveSemantics fuel program state

def OpenSupported (program : Functions.Program) : Prop :=
  (∀ fn, fn ∈ program.functions → Block.OpenSupported fn.body) ∧
    Block.OpenSupported program.body

end Program

end InteractionSemantics
end Functions
end EvmCompiler
