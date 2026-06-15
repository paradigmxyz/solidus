import EvmCompiler.Simulation.MemorySafety
import EvmCompiler.Yul.EffectRefinement.Recursive
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
      Simulation.MemorySafety.TerminalMemorySafe contract kind values.reverse
  | none =>
      match Prim.toUncheckedBasicOp? prim with
      | some op =>
          Simulation.MemorySafety.PrimitiveMemorySafe
            contract op machine values.reverse
      | none => False

theorem primitiveSafe_basicOp
    {contract : MemoryContract.Contract}
    {prim : EvmYul.Operation .Yul} {machine : EvmYul.MachineState}
    {values : List Word} {op : Structured.BasicOp}
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op) :
    PrimitiveSafe contract prim machine values ↔
      Simulation.MemorySafety.PrimitiveMemorySafe
        contract op machine values.reverse := by
  simp [PrimitiveSafe, hTerminal, hOp]

theorem primitiveSafe_terminal
    {contract : MemoryContract.Contract}
    {prim : EvmYul.Operation .Yul} {machine : EvmYul.MachineState}
    {values : List Word} {kind : Assembly.HaltKind}
    (hTerminal : Prim.terminal? prim = some kind) :
    PrimitiveSafe contract prim machine values ↔
      Simulation.MemorySafety.TerminalMemorySafe
        contract kind values.reverse := by
  simp [PrimitiveSafe, hTerminal]

theorem primitiveSafe_mstore_iff
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState)
    (address value : Word) :
    PrimitiveSafe contract
        (.StackMemFlow .MSTORE : EvmYul.Operation .Yul)
        machine [address, value] ↔
      Simulation.MemorySafety.PrimitiveMemorySafe
        contract .mstore machine [value, address] := by
  simpa using
    (primitiveSafe_basicOp
      (contract := contract) (machine := machine)
      (values := [address, value]) (op := .mstore)
      (prim := (.StackMemFlow .MSTORE : EvmYul.Operation .Yul))
      (by rfl) (by rfl))

theorem primitiveSafe_return_iff
    (contract : MemoryContract.Contract) (machine : EvmYul.MachineState)
    (address size : Word) :
    PrimitiveSafe contract
        (.System .RETURN : EvmYul.Operation .Yul)
        machine [address, size] ↔
      Simulation.MemorySafety.TerminalMemorySafe
        contract .return [size, address] := by
  simpa using
    (primitiveSafe_terminal
      (contract := contract) (machine := machine)
      (values := [address, size]) (kind := .return)
      (prim := (.System .RETURN : EvmYul.Operation .Yul))
      (by rfl))

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

private theorem step_error_of_terminal
    {prim : EvmYul.Operation .Yul} {kind : Assembly.HaltKind}
    (hTerminal : Prim.terminal? prim = some kind)
    (source : EvmYul.Yul.State) (values : List Word) :
    ∃ err,
      (EvmYul.step (τ := .Yul) prim (arg := none)) source values =
        .error err := by
  cases prim <;> rename_i primitive <;> cases primitive <;>
    simp [Prim.terminal?] at hTerminal
  all_goals
    cases values with
    | nil => exact ⟨_, rfl⟩
    | cons first rest =>
        cases rest with
        | nil => exact ⟨_, rfl⟩
        | cons second rest =>
            cases rest with
            | nil => exact ⟨_, rfl⟩
            | cons third rest => exact ⟨_, rfl⟩

theorem terminal_none_of_eval_ok
    {contract : MemoryContract.Contract} {transcript : Trace}
    {fuel : Nat} {state final : State transcript}
    {prim : EvmYul.Operation .Yul} {values outputs : List Word}
    (hEval :
      (primitiveSemantics contract transcript).eval
          fuel state prim values =
        .ok (final, outputs)) :
    Prim.terminal? prim = none := by
  cases hTerminal : Prim.terminal? prim with
  | none => rfl
  | some kind =>
      obtain ⟨err, hStep⟩ :=
        step_error_of_terminal hTerminal state.source values
      obtain ⟨_hSafe, hRun⟩ := eval_ok_parts hEval
      cases prim <;> rename_i primitive <;> cases primitive <;>
        simp [Prim.terminal?] at hTerminal ⊢
      all_goals
        cases fuel with
        | zero =>
            simp [ObserverSemantics.SourceReplay.primCall,
              Yul.Source.Effectful.fail] at hRun
        | succ previous =>
            simp only [ObserverSemantics.SourceReplay.primCall,
              ObserverSemantics.yulPrimObserver?,
              Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
              EvmYul.Yul.primCall.eq_def] at hRun
            cases previous with
            | zero =>
                simp [Yul.Source.Effectful.fail] at hRun
            | succ previous =>
                by_cases hPerm :
                    state.source.executionEnv.perm = false <;>
                  simp [hStep, hPerm, Yul.Source.Effectful.fail] at hRun <;>
                  cases hRun

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

private theorem finish_ok_observable
    {transcript : Trace}
    {sourceResult :
      Yul.Source.Effectful.Result (State transcript)
        (State transcript × List Word)}
    {result : Result transcript}
    (hFinish :
      ObserverSemantics.SourceReplay.Program.finish sourceResult =
        .ok result) :
    Yul.Source.Effectful.Result.Observable sourceResult := by
  cases sourceResult with
  | ok value =>
      simp [Yul.Source.Effectful.Result.Observable]
  | error failure =>
      rcases failure with ⟨exception, failureState⟩
      cases exception <;>
        simp [ObserverSemantics.SourceReplay.Program.finish,
          Yul.Source.Effectful.Result.Observable,
          Yul.Source.Effectful.Exception.Observable] at hFinish ⊢

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

theorem run_eq_observer_of_ok
    {contract : MemoryContract.Contract} {fuel : Nat}
    {program : Yul.Program} {source : EvmYul.Yul.State}
    {transcript : Trace} {result : Result transcript}
    (hRun :
      run contract fuel program source transcript = .ok result) :
    ObserverSemantics.SourceReplay.Program.run
      fuel program source transcript = .ok result := by
  change
    ObserverSemantics.SourceReplay.Program.finish
        (Yul.Source.Effectful.callDispatcher
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (primitiveSemantics contract transcript)
          fuel (some program.contract)
          (ObserverSemantics.SourceReplay.Program.installContract
            program { source := source })) =
      .ok result at hRun
  change
    ObserverSemantics.SourceReplay.Program.finish
        (Yul.Source.Effectful.callDispatcher
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSemantics.SourceReplay.primitiveSemantics transcript)
          fuel (some program.contract)
          (ObserverSemantics.SourceReplay.Program.installContract
            program { source := source })) =
      .ok result
  have hCallRefines :=
    Yul.Source.Effectful.callDispatcher_refines
      (ObserverSemantics.SourceReplay.stateModel transcript)
      (observableRefines contract transcript)
      fuel (some program.contract)
      (ObserverSemantics.SourceReplay.Program.installContract
        program { source := source })
  have hCallEq :=
    hCallRefines (finish_ok_observable hRun)
  rw [hCallEq]
  exact hRun

theorem ExactReplay.observerReplay
    {contract : MemoryContract.Contract} {fuel : Nat}
    {program : Yul.Program} {source : EvmYul.Yul.State}
    {transcript : Trace} {result : Result transcript}
    (hReplay :
      ExactReplay contract fuel program source transcript result) :
    ObserverSemantics.SourceReplay.Program.ExactReplay
      fuel program source transcript result :=
  ⟨run_eq_observer_of_ok hReplay.1, hReplay.2⟩

theorem ExactTerminates.observerTerminates
    {contract : MemoryContract.Contract}
    {program : Yul.Program} {source : EvmYul.Yul.State}
    {transcript : Trace} {result : Result transcript}
    (hTerminates :
      ExactTerminates contract program source transcript result) :
    ObserverSemantics.SourceReplay.Program.ExactTerminates
      program source transcript result := by
  rcases hTerminates with ⟨fuel, hReplay⟩
  exact ⟨fuel, hReplay.observerReplay⟩

end Program
end SafeSemantics

end ObserverSafety
end Yul
end EvmCompiler
