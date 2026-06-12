import EvmCompiler.Expressions.Compiler
import EvmCompiler.Simulation.ObserverPass
import EvmCompiler.Structured.ObserverSemantics

namespace EvmCompiler
namespace Expressions
namespace ObserverPreservation

/-!
Observer preservation for the transparent Expressions-to-Structured adapter.

Expressions adds expression grouping but no new control or effect construct.
Its ordinary semantics is independent (`Expressions.Semantics`); observer
execution deliberately reuses the canonical parameterized Structured
interpreter on the pass-owned `toStructured` translation. This avoids a
duplicated observer-aware control interpreter.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev State (transcript : Trace) :=
  Structured.ObserverSemantics.State transcript
abbrev Outcome (transcript : Trace) :=
  Structured.ObserverSemantics.Outcome (transcript := transcript)

namespace Program

def runState (fuel : Nat) (program : Expressions.Program)
    {transcript : Trace} (state : State transcript) :
    Except EVMException (Outcome transcript) :=
  Structured.ObserverSemantics.Program.runState
    fuel program.toStructured state

theorem runState_toStructured
    {fuel : Nat} {program : Expressions.Program}
    {transcript : Trace} {state : State transcript}
    {outcome : Outcome transcript} :
    runState fuel program state = .ok outcome ↔
      Structured.ObserverSemantics.Program.runState
        fuel program.toStructured state = .ok outcome :=
  Iff.rfl

end Program

structure Input (transcript : Trace) where
  fuel : Nat
  state : State transcript

def SourceRuns {transcript : Trace}
    (program : Expressions.Program) (input : Input transcript)
    (outcome : Outcome transcript) : Prop :=
  Program.runState input.fuel program input.state = .ok outcome

def TargetRuns {transcript : Trace}
    (program : Structured.Program) (input : Input transcript)
    (outcome : Outcome transcript) : Prop :=
  Structured.ObserverSemantics.Program.runState
    input.fuel program input.state = .ok outcome

def pass (transcript : Trace) :
    Simulation.ObserverPass.Interface
      Expressions.Program Structured.Program
      (Input transcript) (Input transcript)
      (Outcome transcript)
      (Outcome transcript) where
  lower? program := some program.toStructured
  InputRel := Eq
  SourceRuns := SourceRuns
  TargetRuns := TargetRuns
  OutcomeRel := Eq

theorem forward (transcript : Trace) :
    Simulation.ObserverPass.ForwardPreservation (pass transcript) := by
  intro source target sourceInput targetInput sourceOutcome
    hLower hInput hRun
  simp only [pass, Option.some.injEq] at hLower
  subst target
  subst targetInput
  exact ⟨sourceOutcome, hRun, rfl⟩

theorem backward (transcript : Trace) :
    Simulation.ObserverPass.BackwardAdequacy (pass transcript) := by
  intro source target sourceInput targetInput targetOutcome
    hLower hInput hRun
  simp only [pass, Option.some.injEq] at hLower
  subst target
  subst targetInput
  exact ⟨targetOutcome, hRun, rfl⟩

theorem verified (transcript : Trace) :
    Simulation.ObserverPass.Verified (pass transcript) :=
  ⟨forward transcript, backward transcript⟩

end ObserverPreservation
end Expressions
end EvmCompiler
