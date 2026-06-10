import EvmCompiler.Objects.Syntax
import EvmCompiler.Functions.SourceSemantics

namespace EvmCompiler
namespace Objects

/-
Source-facing object semantics.

At this layer objects are still a transparent root-code wrapper: data and
nested object layout are checked structurally but do not yet affect execution.
The important boundary repair is that this transparent adapter points at the
stack-free `Functions.Source` interpreter, not at the direct function backend.
-/
namespace Source

abbrev State := Functions.Source.State
abbrev PrimitiveSemantics := Functions.Source.PrimitiveSemantics
abbrev Outcome := Functions.Source.Outcome

namespace Object

def runState (prim : PrimitiveSemantics) (fuel : Nat) (object : Object)
    (state : State) : Except EVMException Outcome :=
  Functions.Source.Program.runState prim fuel object.code state

def run (prim : PrimitiveSemantics) (fuel : Nat) (object : Object)
    (state : EVMState) : Except EVMException Outcome :=
  Functions.Source.Program.run prim fuel object.code state

inductive Eval (prim : PrimitiveSemantics) :
    Nat → Object → State → Outcome → Prop where
  | ofRun {fuel : Nat} {object : Object}
      {initial : State} {outcome : Outcome}
      (hRun : runState prim fuel object initial = .ok outcome) :
      Eval prim fuel object initial outcome

theorem eval_of_run {prim : PrimitiveSemantics} {fuel : Nat}
    {object : Object} {initial : State} {outcome : Outcome}
    (hRun : runState prim fuel object initial = .ok outcome) :
    Eval prim fuel object initial outcome := by
  exact Eval.ofRun hRun

theorem runState_toFunctions {prim : PrimitiveSemantics} {fuel : Nat}
    {object : Object} {initial : State} :
    runState prim fuel object initial =
      Functions.Source.Program.runState prim fuel object.toFunctions initial := by
  cases object
  rfl

theorem eval_toFunctions {prim : PrimitiveSemantics} {fuel : Nat}
    {object : Object} {initial : State} {outcome : Outcome}
    (hEval : Eval prim fuel object initial outcome) :
    Functions.Source.Program.Eval prim fuel object.toFunctions initial
      outcome := by
  cases hEval with
  | ofRun hRun =>
      exact Functions.Source.Program.eval_of_run
        (by simpa [runState_toFunctions] using hRun)

end Object

namespace Program

def runState (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : State) : Except EVMException Outcome :=
  Source.Object.runState prim fuel program.root state

def run (prim : PrimitiveSemantics) (fuel : Nat) (program : Program)
    (state : EVMState) : Except EVMException Outcome :=
  Source.Object.run prim fuel program.root state

inductive Eval (prim : PrimitiveSemantics) :
    Nat → Program → State → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program}
      {initial : State} {outcome : Outcome}
      (hRun : runState prim fuel program initial = .ok outcome) :
      Eval prim fuel program initial outcome

theorem eval_of_run {prim : PrimitiveSemantics} {fuel : Nat}
    {program : Program} {initial : State} {outcome : Outcome}
    (hRun : runState prim fuel program initial = .ok outcome) :
    Eval prim fuel program initial outcome := by
  exact Eval.ofRun hRun

theorem runState_toFunctions {prim : PrimitiveSemantics} {fuel : Nat}
    {program : Program} {initial : State} :
    runState prim fuel program initial =
      Functions.Source.Program.runState prim fuel program.toFunctions
        initial := by
  cases program
  rfl

theorem eval_toFunctions {prim : PrimitiveSemantics} {fuel : Nat}
    {program : Program} {initial : State} {outcome : Outcome}
    (hEval : Eval prim fuel program initial outcome) :
    Functions.Source.Program.Eval prim fuel program.toFunctions initial
      outcome := by
  cases hEval with
  | ofRun hRun =>
      exact Functions.Source.Program.eval_of_run
        (by simpa [runState_toFunctions] using hRun)

end Program

end Source

end Objects
end EvmCompiler
