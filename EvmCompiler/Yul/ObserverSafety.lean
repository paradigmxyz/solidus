import EvmCompiler.Simulation.MemorySafety
import EvmCompiler.Yul.EffectRefinement
import EvmCompiler.Yul.ObserverSemantics

namespace EvmCompiler
namespace Yul
namespace ObserverSafety

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word
abbrev State := ObserverSemantics.SourceReplay.State
abbrev Result := ObserverSemantics.SourceReplay.Result

/--
Source-facing safety for one imported-Yul primitive application.

Terminals use the shared terminal range contract; all other supported
primitives use the exact Structured basic operation selected by the ordinary
Yul-to-Functions compiler. External call/create operations are rejected by the
shared closed-world primitive contract.
-/
def PrimitiveSafe (contract : MemoryContract.Contract)
    (prim : EvmYul.Operation .Yul) (machine : EvmYul.MachineState)
    (values : List Word) : Prop :=
  match Prim.terminal? prim with
  | some kind =>
      Simulation.MemorySafety.TerminalMemorySafe contract kind values
  | none =>
      match Prim.toUncheckedBasicOp? prim with
      | some op =>
          Simulation.MemorySafety.PrimitiveMemorySafe
            contract op machine values
      | none => False

@[simp] theorem primitiveSafe_gas
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState) :
    PrimitiveSafe contract
      (.StackMemFlow .GAS : EvmYul.Operation .Yul) machine [] := by
  simp [PrimitiveSafe, Prim.terminal?, Prim.toUncheckedBasicOp?,
    Simulation.MemorySafety.primitiveMemorySafe_gas]

@[simp] theorem primitiveSafe_msize
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState) :
    PrimitiveSafe contract
      (.StackMemFlow .MSIZE : EvmYul.Operation .Yul) machine [] := by
  simp [PrimitiveSafe, Prim.terminal?, Prim.toUncheckedBasicOp?,
    Simulation.MemorySafety.primitiveMemorySafe_msize]

@[simp] theorem primitiveSafe_stop
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState) :
    PrimitiveSafe contract
      (.StopArith .STOP : EvmYul.Operation .Yul) machine [] := by
  simp [PrimitiveSafe, Prim.terminal?,
    Simulation.MemorySafety.terminalMemorySafe_stop]

namespace SafeSemantics

/--
The canonical observer-aware imported-Yul semantics guarded at its primitive
boundary by the shared spill-reservation contract.

Only the primitive handler is specialized. Expression evaluation, function
calls, statement sequencing, lexical scope, switch, loop, and fuel behavior
remain those of `Yul.Source.Effectful`.
-/
noncomputable def primitiveSemantics
    (contract : MemoryContract.Contract) (transcript : Trace) :
    Yul.Source.Effectful.PrimitiveSemantics (State transcript) := by
  classical
  exact
    { eval := fun fuel state prim values =>
        if PrimitiveSafe contract prim
            state.source.sharedState.toMachineState values then
          ObserverSemantics.SourceReplay.primCall
            fuel state prim values
        else
          Yul.Source.Effectful.fail state .InvalidInstruction }

theorem eval_ok_parts
    {contract : MemoryContract.Contract} {transcript : Trace}
    {fuel : Nat} {state final : State transcript}
    {prim : EvmYul.Operation .Yul} {values outputs : List Word}
    (hEval :
      (primitiveSemantics contract transcript).eval
          fuel state prim values =
        .ok (final, outputs)) :
    PrimitiveSafe contract prim
        state.source.sharedState.toMachineState values ∧
      ObserverSemantics.SourceReplay.primCall
          fuel state prim values =
        .ok (final, outputs) := by
  classical
  by_cases hSafe :
      PrimitiveSafe contract prim
        state.source.sharedState.toMachineState values
  · exact ⟨hSafe, by simpa [primitiveSemantics, hSafe] using hEval⟩
  · simp [primitiveSemantics, hSafe, Yul.Source.Effectful.fail] at hEval

theorem eval_yulHalt_parts
    {contract : MemoryContract.Contract} {transcript : Trace}
    {fuel : Nat} {state failureState : State transcript}
    {prim : EvmYul.Operation .Yul} {values : List Word}
    {source : EvmYul.Yul.State} {value : Word}
    (hEval :
      (primitiveSemantics contract transcript).eval
          fuel state prim values =
        .error
          { exception := .YulHalt source value
            state := failureState }) :
    PrimitiveSafe contract prim
        state.source.sharedState.toMachineState values ∧
      ObserverSemantics.SourceReplay.primCall
          fuel state prim values =
        .error
          { exception := .YulHalt source value
            state := failureState } := by
  classical
  by_cases hSafe :
      PrimitiveSafe contract prim
        state.source.sharedState.toMachineState values
  · exact ⟨hSafe, by simpa [primitiveSemantics, hSafe] using hEval⟩
  · simp [primitiveSemantics, hSafe, Yul.Source.Effectful.fail] at hEval

theorem eval_revert_parts
    {contract : MemoryContract.Contract} {transcript : Trace}
    {fuel : Nat} {state failureState : State transcript}
    {prim : EvmYul.Operation .Yul} {values : List Word}
    {source : EvmYul.Yul.State}
    (hEval :
      (primitiveSemantics contract transcript).eval
          fuel state prim values =
        .error
          { exception := .Revert source
            state := failureState }) :
    PrimitiveSafe contract prim
        state.source.sharedState.toMachineState values ∧
      ObserverSemantics.SourceReplay.primCall
          fuel state prim values =
        .error
          { exception := .Revert source
            state := failureState } := by
  classical
  by_cases hSafe :
      PrimitiveSafe contract prim
        state.source.sharedState.toMachineState values
  · exact ⟨hSafe, by simpa [primitiveSemantics, hSafe] using hEval⟩
  · simp [primitiveSemantics, hSafe, Yul.Source.Effectful.fail] at hEval

theorem observableRefines
    (contract : MemoryContract.Contract) (transcript : Trace) :
    (primitiveSemantics contract transcript).ObservableRefines
      (ObserverSemantics.SourceReplay.primitiveSemantics transcript) := by
  constructor
  intro fuel state prim values result hObservable hEval
  cases result with
  | ok result =>
      rcases result with ⟨final, outputs⟩
      exact (eval_ok_parts hEval).2
  | error failure =>
      rcases failure with ⟨exception, failureState⟩
      cases exception with
      | YulHalt source value =>
          exact (eval_yulHalt_parts hEval).2
      | Revert source =>
          exact (eval_revert_parts hEval).2
      | _ =>
          simp [Yul.Source.Effectful.Result.Observable,
            Yul.Source.Effectful.Exception.Observable] at hObservable

namespace Program

noncomputable def run (contract : MemoryContract.Contract) (fuel : Nat)
    (program : Yul.Program) (source : EvmYul.Yul.State)
    (transcript : Trace) :
    Except EvmYul.Yul.Exception (Result transcript) :=
  ObserverSemantics.SourceReplay.Program.runWith
    transcript (primitiveSemantics contract transcript)
    fuel program source

def ExactReplay (contract : MemoryContract.Contract) (fuel : Nat)
    (program : Yul.Program) (source : EvmYul.Yul.State)
    (transcript : Trace) (result : Result transcript) : Prop :=
  run contract fuel program source transcript = .ok result ∧
    result.ConsumedExactly

def ExactTerminates (contract : MemoryContract.Contract)
    (program : Yul.Program) (source : EvmYul.Yul.State)
    (transcript : Trace) (result : Result transcript) : Prop :=
  ∃ fuel, ExactReplay contract fuel program source transcript result

end Program
end SafeSemantics

end ObserverSafety
end Yul
end EvmCompiler
