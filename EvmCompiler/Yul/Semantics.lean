import EvmCompiler.Yul.SolcValidation
import EvmCompiler.Yul.Installation
import EvmCompiler.Objects.Semantics
import EvmCompiler.Objects.SourceSemantics
import EvmYul.Yul.Interpreter

namespace EvmCompiler
namespace Yul

abbrev ReferenceState := EvmYul.Yul.State
abbrev ReferenceException := EvmYul.Yul.Exception
abbrev Outcome := Objects.Outcome

inductive ReferenceResult where
  | regular (state : ReferenceState)
  | yulHalt (state : ReferenceState) (value : Word)
  | revert (stateBeforeRevert : ReferenceState)

namespace Program

def installContract (program : Program) : ReferenceState → ReferenceState
  | .Ok shared store =>
      .Ok
        (Source.Installation.installContract program.contract shared)
        store
  | .OutOfFuel => .OutOfFuel
  | .Checkpoint jump => .Checkpoint jump

def installContractWithCodeImage (program : Program) (codeImage : ByteArray) :
    ReferenceState → ReferenceState
  | .Ok shared store =>
      .Ok
        (Source.Installation.installContractWithCodeImage
          program.contract codeImage shared)
        store
  | .OutOfFuel => .OutOfFuel
  | .Checkpoint jump => .Checkpoint jump

def runRegular (fuel : Nat) (program : Program) (state : ReferenceState) :
    Except ReferenceException ReferenceState :=
  match
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) with
  | .ok (state', _rets) => .ok state'
  | .error exception => .error exception

/--
Independent Yul source interpreter for the imported Nethermind AST.

This is the public source run boundary for the Yul layer.  The old
compiler-facing execution through object lowering is intentionally quarantined
below as `Lowered.run`.
-/
def run (fuel : Nat) (program : Program) (state : ReferenceState) :
    Except ReferenceException ReferenceResult :=
  match
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) with
  | .ok (state', _rets) => .ok (.regular state')
  | .error (.YulHalt state' value) => .ok (.yulHalt state' value)
  | .error (.Revert stateBeforeRevert) => .ok (.revert stateBeforeRevert)
  | .error exception => .error exception

def runWithCodeImage (fuel : Nat) (program : Program)
    (codeImage : ByteArray) (state : ReferenceState) :
    Except ReferenceException ReferenceResult :=
  match
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContractWithCodeImage program codeImage state) with
  | .ok (state', _rets) => .ok (.regular state')
  | .error (.YulHalt state' value) => .ok (.yulHalt state' value)
  | .error (.Revert stateBeforeRevert) => .ok (.revert stateBeforeRevert)
  | .error exception => .error exception

noncomputable def runSolcChecked? (fuel : Nat) (program : Program)
    (state : ReferenceState) :
    Option (Except ReferenceException ReferenceResult) :=
  if SolcValidation.ProgramOk? program then
    some (run fuel program state)
  else
    none

theorem runSolcChecked?_eq_some {fuel : Nat} {program : Program}
    {state : ReferenceState} {result : Except ReferenceException ReferenceResult}
    (hRun : runSolcChecked? fuel program state = some result) :
    SolcValidation.ProgramOk program ∧
      run fuel program state = result := by
  unfold runSolcChecked? at hRun
  cases hValid : SolcValidation.ProgramOk? program <;> simp [hValid] at hRun
  exact ⟨hValid, hRun⟩

end Program

namespace Lowered

noncomputable def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  match program.toObjects? with
  | none => .error .InvalidInstruction
  | some lower => lower.run fuel state

inductive Eval :
    Nat → Program → EVMState → Outcome → Prop where
  | ofObjects {fuel : Nat} {program : Program}
      {initial : EVMState} {outcome : Outcome} {lower : Objects.Program}
      (hToObjects : program.toObjects? = some lower)
      (hRun : lower.run fuel initial = .ok outcome) :
      Eval fuel program initial outcome

end Lowered

namespace SourceLowered

noncomputable def runState (prim : Objects.Source.PrimitiveSemantics) (fuel : Nat)
    (program : Program) (state : Objects.Source.State) :
    Except EVMException Objects.Source.Outcome :=
  match program.toObjects? with
  | none => .error .InvalidInstruction
  | some lower => Objects.Source.Program.runState prim fuel lower state

noncomputable def run (prim : Objects.Source.PrimitiveSemantics) (fuel : Nat)
    (program : Program) (state : EVMState) :
    Except EVMException Objects.Source.Outcome :=
  match program.toObjects? with
  | none => .error .InvalidInstruction
  | some lower => Objects.Source.Program.run prim fuel lower state

theorem runState_of_toObjects? {prim : Objects.Source.PrimitiveSemantics}
    {fuel : Nat} {program : Program} {state : Objects.Source.State}
    {lower : Objects.Program}
    (hLower : program.toObjects? = some lower) :
    runState prim fuel program state =
      Objects.Source.Program.runState prim fuel lower state := by
  simp [runState, hLower]

theorem run_of_toObjects? {prim : Objects.Source.PrimitiveSemantics}
    {fuel : Nat} {program : Program} {state : EVMState}
    {lower : Objects.Program}
    (hLower : program.toObjects? = some lower) :
    run prim fuel program state =
      Objects.Source.Program.run prim fuel lower state := by
  simp [run, hLower]

inductive Eval (prim : Objects.Source.PrimitiveSemantics) :
    Nat → Program → Objects.Source.State → Objects.Source.Outcome → Prop where
  | ofObjects {fuel : Nat} {program : Program}
      {initial : Objects.Source.State} {outcome : Objects.Source.Outcome}
      {lower : Objects.Program}
      (hToObjects : program.toObjects? = some lower)
      (hRun :
        Objects.Source.Program.runState prim fuel lower initial = .ok outcome) :
      Eval prim fuel program initial outcome

end SourceLowered

end Yul
end EvmCompiler
