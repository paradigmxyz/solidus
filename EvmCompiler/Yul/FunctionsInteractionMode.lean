import EvmCompiler.Yul.AllocationInteractionSafeRefinement
import EvmCompiler.Yul.FunctionsAllocationInteractionSafety
import EvmCompiler.Yul.FunctionsInteractionTerminal

/-!
Primitive-semantics mode for the adjacent Yul-to-Functions proof.

Both modes use the canonical parameterized control interpreters. The mode
selects only primitive handlers: ordinary compiler semantics, or allocation-
guarded semantics under one source memory contract. This lets one recursive
pass theorem serve both public capabilities without duplicating control or the
compiler.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionMode

noncomputable section

inductive Mode where
  | ordinary
  | guarded (contract : MemoryContract.Contract)

def sourcePrimitive : Mode →
    Yul.Source.Canonical.PrimitiveSemantics
      Yul.InteractionSemantics.Open Yul.InteractionSemantics.State
  | .ordinary => Yul.InteractionSemantics.primitiveSemantics
  | .guarded contract =>
      Yul.AllocationInteractionSafeSemantics.primitiveSemantics contract

def targetPrimitive : Mode →
    Functions.Source.Canonical.PrimitiveSemantics
      Functions.InteractionSemantics.Open
      Functions.InteractionSemantics.State
  | .ordinary => Functions.InteractionSemantics.primitiveSemantics
  | .guarded contract =>
      Functions.AllocationInteractionSafeSemantics.primitiveSemantics contract

namespace Source

def evalArgs (mode : Mode) :=
  Yul.Source.Canonical.evalArgs Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def evalValues (mode : Mode) :=
  Yul.Source.Canonical.evalValues Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def eval (mode : Mode) :=
  Yul.Source.Canonical.eval Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def call (mode : Mode) :=
  Yul.Source.Canonical.call Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def execSeq (mode : Mode) :=
  Yul.Source.Canonical.execSeq Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def exec (mode : Mode) :=
  Yul.Source.Canonical.exec Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

def loop (mode : Mode) :=
  Yul.Source.Canonical.loop Yul.InteractionSemantics.stateModel
    (sourcePrimitive mode)

/-- One argument followed by exhausted list fuel, uniformly for both
primitive-semantics modes. -/
theorem evalArgs_one_cons (mode : Mode)
    (head : EvmYul.Yul.Ast.Expr) (rest : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (state : Yul.InteractionSemantics.State) :
    evalArgs mode 1 (head :: rest) code state =
      Simulation.Interaction.bind
        (evalValues mode 0 head code state) fun result =>
          Yul.InteractionSemantics.Primitive.fail result.1 .OutOfFuel := by
  unfold evalArgs evalValues Yul.Source.Canonical.evalArgs
    Yul.Source.Canonical.evalValues
  simp only [Yul.Source.Effectful.evalArgs,
    Yul.Source.Effectful.evalTail, Yul.Source.Effectful.eval]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.Source.Effectful.evalValues Yul.InteractionSemantics.stateModel
            (sourcePrimitive mode) 0 head code state)
          (fun result => pure (result.1, result.2.head!)))
        (fun result =>
          Yul.InteractionSemantics.Primitive.fail result.1 .OutOfFuel) = _
  rw [Simulation.Interaction.bind_assoc]
  rfl

/-- Positive residual list fuel exposes the head value and exact tail for both
primitive-semantics modes. -/
theorem evalArgs_succ_succ_cons (mode : Mode) (fuel : Nat)
    (head : EvmYul.Yul.Ast.Expr) (rest : List EvmYul.Yul.Ast.Expr)
    (code : Option EvmYul.Yul.Ast.YulContract)
    (state : Yul.InteractionSemantics.State) :
    evalArgs mode (fuel + 2) (head :: rest) code state =
      Simulation.Interaction.bind
        (evalValues mode (fuel + 1) head code state) fun headResult =>
          Simulation.Interaction.bind
            (evalArgs mode fuel rest code headResult.1) fun tailResult =>
              pure
                (tailResult.1, headResult.2.head! :: tailResult.2) := by
  unfold evalArgs evalValues Yul.Source.Canonical.evalArgs
    Yul.Source.Canonical.evalValues
  simp only [Yul.Source.Effectful.evalArgs,
    Yul.Source.Effectful.evalTail, Yul.Source.Effectful.eval]
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.Source.Effectful.evalValues Yul.InteractionSemantics.stateModel
            (sourcePrimitive mode) (fuel + 1) head code state)
          (fun result => pure (result.1, result.2.head!)))
        (fun headResult =>
          Simulation.Interaction.bind
            (Yul.Source.Effectful.evalArgs Yul.InteractionSemantics.stateModel
              (sourcePrimitive mode) fuel rest code headResult.1)
            (fun tailResult =>
              pure (tailResult.1, headResult.2 :: tailResult.2))) = _
  rw [Simulation.Interaction.bind_assoc]
  rfl

end Source

namespace Target

namespace Expr

def openEval {results : Nat} (mode : Mode)
    (expr : Functions.Expr results)
    (state : Functions.InteractionSemantics.State) :=
  Locals.Source.Effectful.Expr.Control.eval
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    expr state

end Expr

namespace ExprSeq

def openEval {results : Nat} (mode : Mode)
    (exprs : Locals.ExprSeq results)
    (state : Functions.InteractionSemantics.State) :=
  Locals.Source.Effectful.Expr.Control.ExprSeq.eval
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    exprs state

end ExprSeq

namespace ArgList

def openEval (mode : Mode) (args : List (Functions.Expr 1))
    (state : Functions.InteractionSemantics.State) :=
  Functions.Source.Canonical.ArgList.eval
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    args state

end ArgList

namespace Block

def openRun (mode : Mode) (program : Functions.Program)
    (ctx : Functions.Source.Ctx) (fuel : Nat) (block : Functions.Block)
    (state : Functions.InteractionSemantics.State) :=
  Functions.Source.Canonical.Block.runOpen
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    program ctx fuel block state

end Block

namespace Program

def openRunState (mode : Mode) (fuel : Nat) (program : Functions.Program)
    (state : Functions.InteractionSemantics.State) :=
  Functions.Source.Canonical.Program.runState
    Functions.InteractionSemantics.stateModel (targetPrimitive mode)
    fuel program state

end Program

end Target

open FunctionsInteractionPrimitive

/-- The one primitive capability consumed by the mode-parametric recursive
Yul-to-Functions proof. -/
def CompilerSelected (mode : Mode) : Prop :=
  ∀ {fuel : Nat}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues : List Assembly.Word},
    Prim.toUncheckedBasicOp? prim = some op →
    sourceValues.length = Expressions.Structured.BasicOp.inputs op →
    FunctionsInteractionRelation.StateRel source target →
    Simulation.Interaction.ForwardRel Truncated (PrimitiveDoneRel source op)
      ((sourcePrimitive mode).eval
        (fuel + 1) source prim sourceValues)
      ((targetPrimitive mode).eval op target sourceValues.reverse)

theorem compilerSelected (mode : Mode) : CompilerSelected mode := by
  cases mode with
  | ordinary =>
      exact FunctionsInteractionClosedPrimitive.compilerSelected
  | guarded contract =>
      exact FunctionsAllocationInteractionSafety.compilerSelectedSafe contract

/-- Terminal counterpart of `CompilerSelected`, shared by direct and prepared
terminal statements. -/
def TerminalSelected (mode : Mode) : Prop :=
  ∀ {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {kind : Assembly.HaltKind} {sourceValues : List Assembly.Word}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State},
    Prim.terminal? prim = some kind →
    sourceValues.length = kind.argCount →
    FunctionsInteractionRelation.StateRel source target →
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionTerminal.PrimitiveDoneRel kind)
      ((sourcePrimitive mode).eval
        (fuel + 2) source prim sourceValues)
      ((targetPrimitive mode).terminal kind target sourceValues.reverse)

theorem terminalSelected (mode : Mode) : TerminalSelected mode := by
  cases mode with
  | ordinary =>
      intro fuel prim kind values source target hTerminal hLength hRel
      exact FunctionsInteractionTerminal.of_terminal?
        fuel values hTerminal hLength hRel
  | guarded contract =>
      intro fuel prim kind values source target hTerminal hLength hRel
      change Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionTerminal.PrimitiveDoneRel kind)
        (AllocationInteractionSafeSemantics.openEval
          contract (fuel + 2) source prim values)
        (Functions.AllocationInteractionSafeSemantics.openTerminal
          contract kind target values.reverse)
      by_cases hSourceSafe :
          AllocationInteractionSafeSemantics.PrimitiveSafe
            contract prim source values
      · have hTargetSafe :=
          FunctionsAllocationInteractionSafety.Primitive.terminalSafe_to_functions
            hTerminal hSourceSafe
        rw [AllocationInteractionSafeSemantics.Primitive.openEval_eq_ordinary
            hSourceSafe,
          Functions.AllocationInteractionSafeSemantics.Primitive.openTerminal_eq_ordinary
            hTargetSafe]
        exact FunctionsInteractionTerminal.of_terminal?
          fuel values hTerminal hLength hRel
      · have hTargetUnsafe :
            ¬ Simulation.MemorySafety.TerminalMemorySafe
              contract kind values.reverse := by
          intro hTargetSafe
          apply hSourceSafe
          simpa [AllocationInteractionSafeSemantics.PrimitiveSafe, hTerminal]
            using hTargetSafe
        unfold AllocationInteractionSafeSemantics.openEval
          Functions.AllocationInteractionSafeSemantics.openTerminal
        simp only [hSourceSafe, hTargetUnsafe, ↓reduceIte]
        exact Simulation.Interaction.ForwardRel.done
          (.error (by simp [FunctionsInteractionPrimitive.ErrorRel]))

end
end FunctionsInteractionMode
end Yul
end EvmCompiler
