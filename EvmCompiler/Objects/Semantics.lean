import EvmCompiler.Objects.Syntax
import EvmCompiler.Functions.Semantics

namespace EvmCompiler
namespace Objects

abbrev Outcome := Functions.Outcome

namespace Object

def run (fuel : Nat) : Object → EVMState → Except EVMException Outcome
  | .mk _name code _data _objects, state =>
      Functions.Program.run fuel code state

inductive Eval :
    Nat → Object → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {object : Object}
      {initial : EVMState} {outcome : Outcome}
      (hRun : object.run fuel initial = .ok outcome) :
      Eval fuel object initial outcome

theorem eval_of_run {fuel : Nat} {object : Object}
    {initial : EVMState} {outcome : Outcome}
    (hRun : object.run fuel initial = .ok outcome) :
    Eval fuel object initial outcome := by
  exact Eval.ofRun hRun

end Object

namespace Program

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  program.root.run fuel state

inductive Eval :
    Nat → Program → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program}
      {initial : EVMState} {outcome : Outcome}
      (hRun : run fuel program initial = .ok outcome) :
      Eval fuel program initial outcome

theorem eval_of_run {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hRun : run fuel program initial = .ok outcome) :
    Eval fuel program initial outcome := by
  exact Eval.ofRun hRun

end Program

end Objects
end EvmCompiler
