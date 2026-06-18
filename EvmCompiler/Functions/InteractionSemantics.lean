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

namespace Expr

def openEval {results : Nat} (expr : Functions.Expr results)
    (state : State) : Open (State × List Word) :=
  Locals.InteractionSemantics.Expr.openEval expr state

def openEvalOne (expr : Functions.Expr 1)
    (state : State) : Open (State × Word) :=
  Locals.InteractionSemantics.Expr.openEvalOne expr state

def openEvalCondition (expr : Functions.Expr 1)
    (state : State) : Open (State × Bool) :=
  Locals.InteractionSemantics.Expr.openEvalCondition expr state

abbrev OpenSupported {results : Nat} (expr : Functions.Expr results) : Prop :=
  Locals.InteractionSemantics.Expr.OpenSupported expr

end Expr

namespace ExprSeq

def openEval {results : Nat} (exprs : Locals.ExprSeq results)
    (state : State) : Open (State × List Word) :=
  Locals.InteractionSemantics.ExprSeq.openEval exprs state

abbrev OpenSupported {results : Nat}
    (exprs : Locals.ExprSeq results) : Prop :=
  Locals.InteractionSemantics.ExprSeq.OpenSupported exprs

end ExprSeq

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

/-- One source statement followed by its exact residual block. -/
theorem openRun_cons
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (stmt : Functions.Stmt) (rest : List Functions.Stmt)
    (state : State) :
    openRun program ctx (fuel + 1) { stmts := stmt :: rest } state =
      Simulation.Interaction.bind
        (Functions.Source.Effectful.Control.Stmt.run
          stateModel primitiveSemantics program ctx fuel stmt state)
        (fun result =>
        match result.1.mode with
        | .regular =>
            Functions.Source.Effectful.Control.Block.runOpen
              stateModel primitiveSemantics program result.2 fuel
              { stmts := rest } result.1.state
        | .brk | .cont | .leave | .halt _ =>
            Simulation.Interaction.pure (result.1, ctx)) := by
  change
    Functions.Source.Effectful.Control.Block.runOpen
        stateModel primitiveSemantics program ctx (fuel + 1)
        { stmts := stmt :: rest } state = _
  rw [Nat.add_one]
  simp only [Functions.Source.Effectful.Control.Block.runOpen]
  change
    Simulation.Interaction.bind
        (Functions.Source.Effectful.Control.Stmt.run
          stateModel primitiveSemantics program ctx fuel stmt state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Functions.Source.Effectful.Control.Block.runOpen
                stateModel primitiveSemantics program result.2 fuel
                { stmts := rest } result.1.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, ctx)) = _
  rfl

/-- A nonzero-fuel empty source block is the regular identity. -/
theorem openRun_nil
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (state : State) :
    openRun program ctx (fuel + 1) { stmts := [] } state =
      (pure (Functions.Source.Effectful.Outcome.regular state, ctx) :
        Open (Outcome × Functions.Source.Ctx)) := by
  change
    Functions.Source.Effectful.Control.Block.runOpen
        stateModel primitiveSemantics program ctx (fuel + 1)
        { stmts := [] } state = _
  rw [Nat.add_one]
  simp only [Functions.Source.Effectful.Control.Block.runOpen]

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

/-- A lexical block restricts its state only after regular body completion. -/
theorem openRun_block
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (body : Functions.Block) (state : State) :
    openRun program ctx fuel (.block body) state =
      Simulation.Interaction.bind
        (Block.openRun program ctx fuel body state)
        (fun result =>
          match result.1.mode with
          | .regular =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular
                  (stateModel.restrictTo ctx.scope result.1.state), ctx)
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure (result.1, ctx)) := by
  unfold openRun Block.openRun Functions.Source.Canonical.Stmt.run
    Functions.Source.Canonical.Block.runOpen
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Functions.Source.Effectful.Control.Block.runScoped
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Functions.Source.Effectful.Control.Block.runOpen
            stateModel primitiveSemantics program ctx fuel body state)
          (fun result =>
            match result.1.mode with
            | .regular =>
                Simulation.Interaction.pure
                  (Functions.Source.Effectful.Outcome.regular
                    (stateModel.restrictTo ctx.scope result.1.state))
            | .brk | .cont | .leave | .halt _ =>
                Simulation.Interaction.pure result.1))
        (fun outcome => Simulation.Interaction.pure (outcome, ctx)) = _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Functions.Source.Effectful.Control.Block.runOpen
        stateModel primitiveSemantics program ctx fuel body state))
  intro result _
  cases hMode : result.1.mode <;> rfl

/-- A positive-fuel conditional exposes condition evaluation and one branch. -/
theorem openRun_if
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (cond : Functions.Expr 1) (body : Functions.Block)
    (state : State) :
    openRun program ctx (fuel + 1) (.if_ cond body) state =
      Simulation.Interaction.bind
        (Expr.openEvalCondition cond state)
        (fun result =>
          if result.2 then
            openRun program ctx fuel (.block body) result.1
          else
            Simulation.Interaction.pure
              (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Expr.openEvalCondition
    Locals.InteractionSemantics.Expr.openEvalCondition
  rfl

/-- A positive-fuel switch exposes one scrutinee and its selected branch. -/
theorem openRun_switch
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (fuel : Nat) (scrutinee : Functions.Expr 1)
    (cases : List (Word × Functions.Block))
    (defaultBody : Option Functions.Block) (state : State) :
    openRun program ctx (fuel + 1)
        (.switch scrutinee cases defaultBody) state =
      Simulation.Interaction.bind
        (Expr.openEvalOne scrutinee state)
        (fun result =>
          match Functions.Source.Switch.select
              result.2 cases defaultBody with
          | some body => openRun program ctx fuel (.block body) result.1
          | none =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.regular result.1, ctx)) := by
  unfold openRun Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  unfold Expr.openEvalOne
    Locals.InteractionSemantics.Expr.openEvalOne stateModel primitiveSemantics
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Locals.Source.Effectful.Expr.Control.evalOne
        Locals.InteractionSemantics.stateModel
        Locals.InteractionSemantics.primitiveSemantics scrutinee state))
  intro result _
  cases Functions.Source.Switch.select result.2 cases defaultBody <;> rfl

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
