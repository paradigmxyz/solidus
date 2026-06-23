import EvmCompiler.Functions.AllocationInteractionPrimitive
import EvmCompiler.Yul.InteractionSemantics

/-!
Canonical Yul semantics with allocation memory safety enforced only at the
primitive boundary. Control, internal calls, lexical scope, switches, loops,
and open effects remain the shared parameterized Yul interpreter.

This is the source-owned counterpart of
`Functions.AllocationInteractionSafeSemantics`. It is intentionally independent
of allocation schedules and target code. A successful/terminal execution says
only that every primitive actually reached on every open-world answer branch is
compatible with the source program's memory reservation contract.
-/

namespace EvmCompiler
namespace Yul
namespace AllocationInteractionSafeSemantics

noncomputable section

abbrev Open (alpha : Type) :=
  Simulation.Interaction Yul.InteractionSemantics.Failure alpha
abbrev State := Yul.InteractionSemantics.State
abbrev Failure := Yul.InteractionSemantics.Failure

/-- Memory safety for one reached Yul primitive, expressed in source argument
order. The adjacent Yul-to-Functions pass reverses these values once, so each
case is definitionally the same contract consumed by the Functions allocator.
-/
def PrimitiveSafe (contract : MemoryContract.Contract)
    (prim : EvmYul.Operation .Yul) (state : State)
    (values : List Assembly.Word) : Prop :=
  match Prim.terminal? prim with
  | some kind =>
      Simulation.MemorySafety.TerminalMemorySafe contract kind values.reverse
  | none =>
      match Simulation.ExternalKind.ofYulOperation? prim with
      | some (.call kind) =>
          Functions.AllocationInteractionPrimitive.CallMemorySafe
            contract kind values.reverse
      | some (.create kind) =>
          Functions.AllocationInteractionPrimitive.CreateMemorySafe
            contract kind values.reverse
      | none =>
          match Prim.toUncheckedBasicOp? prim with
          | some op =>
              Simulation.MemorySafety.OpenPrimitiveMemorySafe contract op
                state.sharedState.toMachineState values.reverse
          | none => False

noncomputable def openEval (contract : MemoryContract.Contract)
    (fuel : Nat) (state : State) (prim : EvmYul.Operation .Yul)
    (values : List Assembly.Word) : Open (State × List Assembly.Word) := by
  classical
  exact
    if PrimitiveSafe contract prim state values then
      Yul.InteractionSemantics.Primitive.openEval fuel state prim values
    else
      Yul.InteractionSemantics.Primitive.fail state .InvalidInstruction

noncomputable def primitiveSemantics (contract : MemoryContract.Contract) :
    Yul.Source.Canonical.PrimitiveSemantics Open State where
  eval := openEval contract

namespace Primitive

theorem safe_of_completed
    {contract : MemoryContract.Contract} {fuel : Nat} {state : State}
    {prim : EvmYul.Operation .Yul} {values : List Assembly.Word}
    {property : Except Failure (State × List Assembly.Word) → Prop}
    (hInvalid : property
      (.error { exception := .InvalidInstruction, state := state }) → False)
    (hCompleted : Simulation.Interaction.AllDone property
      (openEval contract fuel state prim values)) :
    PrimitiveSafe contract prim state values := by
  by_contra hUnsafe
  unfold openEval at hCompleted
  simp only [hUnsafe, ↓reduceIte] at hCompleted
  cases hCompleted with
  | done hDone => exact hInvalid hDone

theorem openEval_eq_ordinary
    {contract : MemoryContract.Contract} {fuel : Nat} {state : State}
    {prim : EvmYul.Operation .Yul} {values : List Assembly.Word}
    (hSafe : PrimitiveSafe contract prim state values) :
    openEval contract fuel state prim values =
      Yul.InteractionSemantics.Primitive.openEval fuel state prim values := by
  simp [openEval, hSafe]

end Primitive

abbrev evalArgs (contract : MemoryContract.Contract) :=
  Yul.Source.Canonical.evalArgs Yul.InteractionSemantics.stateModel
    (primitiveSemantics contract)

abbrev evalValues (contract : MemoryContract.Contract) :=
  Yul.Source.Canonical.evalValues Yul.InteractionSemantics.stateModel
    (primitiveSemantics contract)

abbrev eval (contract : MemoryContract.Contract) :=
  Yul.Source.Canonical.eval Yul.InteractionSemantics.stateModel
    (primitiveSemantics contract)

abbrev call (contract : MemoryContract.Contract) :=
  Yul.Source.Canonical.call Yul.InteractionSemantics.stateModel
    (primitiveSemantics contract)

abbrev execSeq (contract : MemoryContract.Contract) :=
  Yul.Source.Canonical.execSeq Yul.InteractionSemantics.stateModel
    (primitiveSemantics contract)

abbrev exec (contract : MemoryContract.Contract) :=
  Yul.Source.Canonical.exec Yul.InteractionSemantics.stateModel
    (primitiveSemantics contract)

abbrev loop (contract : MemoryContract.Contract) :=
  Yul.Source.Canonical.loop Yul.InteractionSemantics.stateModel
    (primitiveSemantics contract)

/-- Source outcomes accepted by the compiler's terminal preservation theorem.
Ordinary completion and explicit Yul halts are valid; runtime/control failures
and a rejected memory-safety guard are not. -/
def Completed {alpha : Type} : Except Failure alpha → Prop
  | .ok _ => True
  | .error failure =>
      match failure.exception with
      | .YulHalt _ _ | .Revert _ => True
      | _ => False

namespace Completed

@[simp] theorem ok {alpha : Type} (value : alpha) :
    Completed (.ok value : Except Failure alpha) := by
  trivial

@[simp] theorem invalidInstruction_false {alpha : Type} (state : State) :
    Completed
        (.error { exception := .InvalidInstruction, state := state } :
          Except Failure alpha) = False := by
  rfl

end Completed

/-- Equality of guarded and ordinary prefixes composes through the canonical
open bind whenever every reached guarded leaf is a valid completion. -/
theorem bind_eq_of_completed
    {source target : Type}
    {prefixGuarded prefixOrdinary : Open source}
    {nextGuarded nextOrdinary : source → Open target}
    (hCompleted : Simulation.Interaction.AllDone Completed
      (Simulation.Interaction.bind prefixGuarded nextGuarded))
    (hPrefix : Simulation.Interaction.AllDone Completed prefixGuarded →
      prefixGuarded = prefixOrdinary)
    (hNext : ∀ value,
      Simulation.Interaction.AllDone Completed (nextGuarded value) →
        nextGuarded value = nextOrdinary value) :
    Simulation.Interaction.bind prefixGuarded nextGuarded =
      Simulation.Interaction.bind prefixOrdinary nextOrdinary := by
  have hInv := Simulation.Interaction.AllDone.bind_inv hCompleted
  have hPrefixCompleted :
      Simulation.Interaction.AllDone Completed prefixGuarded := by
    apply Simulation.Interaction.AllDone.mono hInv
    intro outcome hOutcome
    cases outcome with
    | error _ => exact hOutcome
    | ok _ => trivial
  have hPrefixEq := hPrefix hPrefixCompleted
  rw [← hPrefixEq]
  apply Simulation.Interaction.AllDone.bind_congr hInv
  intro value hValue
  exact hNext value hValue

namespace Primitive

theorem openEval_eq_ordinary_of_completed
    {contract : MemoryContract.Contract} {fuel : Nat} {state : State}
    {prim : EvmYul.Operation .Yul} {values : List Assembly.Word}
    (hCompleted : Simulation.Interaction.AllDone Completed
      (openEval contract fuel state prim values)) :
    openEval contract fuel state prim values =
      Yul.InteractionSemantics.Primitive.openEval fuel state prim values := by
  apply openEval_eq_ordinary
  exact safe_of_completed
    (by simp [Completed]) hCompleted

end Primitive

namespace Stmt

/-- Actual-tree source safety for one canonical Yul statement execution. -/
def ExecutionSafe (contract : MemoryContract.Contract) (fuel : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (code : Option EvmYul.Yul.Ast.YulContract) (state : State) : Prop :=
  Simulation.Interaction.AllDone Completed
    (exec contract fuel stmt code state)

end Stmt

namespace Program

noncomputable def openRun (contract : MemoryContract.Contract) (fuel : Nat)
    (code : EvmYul.Yul.Ast.YulContract) (state : State) :
    Open (State × List Assembly.Word) :=
  Yul.Source.Canonical.Program.run Yul.InteractionSemantics.stateModel
    (primitiveSemantics contract) fuel code state

/-- Actual-tree source safety for the canonical installed-program entry. -/
def ExecutionSafe (contract : MemoryContract.Contract) (fuel : Nat)
    (code : EvmYul.Yul.Ast.YulContract) (state : State) : Prop :=
  Simulation.Interaction.AllDone Completed
    (openRun contract fuel code state)

end Program

end
end AllocationInteractionSafeSemantics
end Yul
end EvmCompiler
