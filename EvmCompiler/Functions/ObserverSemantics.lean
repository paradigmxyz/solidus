import EvmCompiler.Functions.EffectSemantics
import EvmCompiler.Locals.ObserverSemantics

namespace EvmCompiler
namespace Functions
namespace ObserverSemantics

abbrev Trace := Assembly.ResourceTrace
abbrev State := Locals.ObserverSemantics.State
abbrev Outcome := Locals.Source.Effectful.Outcome

def stateModel (transcript : Trace) :
    Functions.Source.Effectful.StateModel (State transcript) :=
  Locals.ObserverSemantics.stateModel transcript

def primitiveSemantics (transcript : Trace) :
    Functions.Source.Effectful.PrimitiveSemantics (State transcript) :=
  Locals.ObserverSemantics.primitiveSemantics transcript

namespace Program

def runState (fuel : Nat) (program : Functions.Program)
    {transcript : Trace} (state : State transcript) :
    Except EVMException (Outcome (State transcript)) :=
  Functions.Source.Effectful.Program.runState
    (stateModel transcript) (primitiveSemantics transcript)
    fuel program state

end Program

@[simp] theorem stmt_run_let_gas_cons
    (fuel : Nat) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (source : Locals.Source.State)
    (name : Functions.Name) (value : Assembly.Word) (rest : Trace) :
    Functions.Source.Effectful.Stmt.run
        (stateModel ({ kind := .gas, value := value } :: rest))
        (primitiveSemantics ({ kind := .gas, value := value } :: rest))
        program ctx fuel
        (.let_ name (.prim .gas .nil : Functions.Expr 1))
        { source := source } =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          { source := source.insert name value, cursor := 1 },
          { ctx with scope := name :: ctx.scope }) := by
  simp [Functions.Source.Effectful.Stmt.run,
    Functions.Source.Effectful.Expr.evalOne,
    Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    primitiveSemantics, Locals.ObserverSemantics.primitiveSemantics,
    Locals.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Functions.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.StateModel.insert,
    Locals.Source.State.insert,
    stateModel, Locals.ObserverSemantics.stateModel,
    Simulation.ResourceReplay.State.withSource,
    Simulation.ResourceReplay.consume?]

@[simp] theorem runBody_let_gas_cons
    (fuel : Nat) (program : Functions.Program)
    (source : Locals.Source.State) (functionName localName : Functions.Name)
    (value : Assembly.Word) (rest : Trace) :
    Functions.Source.Effectful.FunDef.runBody
        (stateModel ({ kind := .gas, value := value } :: rest))
        (primitiveSemantics ({ kind := .gas, value := value } :: rest))
        program
        { name := functionName
          params := []
          returns := []
          body :=
            { stmts :=
                [.let_ localName
                  (.prim .gas .nil : Functions.Expr 1)] } }
        [] fuel.succ.succ.succ { source := source } =
      .ok
        (.returned
          { source :=
              { shared := source.shared,
                vars :=
                  Locals.Source.Store.insert
                    Locals.Source.Store.empty localName value },
            cursor := 1 }
          []) := by
  simp [Functions.Source.Effectful.FunDef.runBody,
    Functions.Source.Effectful.Block.runOpen,
    Functions.Source.Effectful.Stmt.run,
    Functions.Source.Effectful.Expr.evalOne,
    Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    Functions.Source.Store.insertMany, Functions.Source.Store.initReturns,
    Functions.Source.Store.lookupMany,
    primitiveSemantics, Locals.ObserverSemantics.primitiveSemantics,
    Locals.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Functions.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.StateModel.insert,
    Locals.Source.State.insert,
    stateModel, Locals.ObserverSemantics.stateModel,
    Simulation.ResourceReplay.State.withSource,
    Simulation.ResourceReplay.consume?]

@[simp] theorem stmt_run_call_let_gas_cons
    (fuel : Nat) (source : Locals.Source.State)
    (functionName localName : Functions.Name)
    (value : Assembly.Word) (rest : Trace) :
    let fn : Functions.FunDef :=
      { name := functionName
        params := []
        returns := []
        body :=
          { stmts :=
              [.let_ localName
                (.prim .gas .nil : Functions.Expr 1)] } }
    let program : Functions.Program :=
      { functions := [fn], body := { stmts := [] } }
    Functions.Source.Effectful.Stmt.run
        (stateModel ({ kind := .gas, value := value } :: rest))
        (primitiveSemantics ({ kind := .gas, value := value } :: rest))
        program Functions.Source.Ctx.initial fuel.succ.succ.succ.succ
        (.call [] functionName []) { source := source } =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          { source := source, cursor := 1 },
          Functions.Source.Ctx.initial) := by
  cases source
  simp [Functions.Source.Effectful.Stmt.run,
    Functions.Source.Effectful.ArgList.eval,
    Functions.Source.FunList.find?,
    Functions.Source.Effectful.FunDef.runBody,
    Functions.Source.Effectful.Block.runOpen,
    Functions.Source.Effectful.Expr.evalOne,
    Functions.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.evalOne,
    Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval,
    Functions.Source.Store.insertMany, Functions.Source.Store.initReturns,
    Functions.Source.Store.lookupMany, Functions.Source.Store.assignMany,
    primitiveSemantics, Locals.ObserverSemantics.primitiveSemantics,
    Locals.ObserverSemantics.basicOpObserver?,
    Structured.BasicOp.toPrimOp,
    Assembly.ResourceObserver.ofPrimOp?,
    Functions.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.Outcome.regular,
    Locals.Source.Effectful.StateModel.vars,
    Locals.Source.Effectful.StateModel.insert,
    Locals.Source.State.insert,
    stateModel, Locals.ObserverSemantics.stateModel,
    Simulation.ResourceReplay.State.withSource,
    Simulation.ResourceReplay.consume?]

end ObserverSemantics
end Functions
end EvmCompiler
