import EvmCompiler.TypedCfg.InteractionSemantics
import EvmCompiler.TypedCfg.PeepholeStackRealizes
import EvmCompiler.Assembly.InteractionPreservation

/-!
# The `openRunAt` AllDone-`StackRealizes` bridge (Step D gating lemma)

This is the standalone, banked module supplying the missing infrastructure for
the `swap d ; swap d → ε` peephole arm (item (1) of the session-52 frontier in
`PEEPHOLE_PROGRESS.md`).

The swap cancellation is only sound when the runtime stack is deep enough to
perform the swap.  `PeepholeStackRealizes.lean` already threads that depth fact
(`StackRealizes`) across the ordinary straight-line runners (`runState`,
`runAt`, `runBody`).  The peephole *open* runner (`openRunAt`) additionally
suspends at CALL/CREATE/resource requests, so its `StackRealizes` preservation
must quantify over every open-world response — i.e. it is an `AllDone` fact, not
a single-leaf equation.

This module proves exactly that bridge:

* `openRunState_stackRealizes` — every terminal leaf of the open one-instruction
  state step realizes the output shape.  The prim case delegates to the
  Assembly-owned `openStep_realizesStackArity` (which already covers `callStep`,
  `createStep`, `resourceStep`, and the closed `op.step` outcome); the
  bookkeeping cases delegate to `runState_stackRealizes`.
* `openRunAt_stackRealizes` — the `runAt`-level bridge, obtained by mapping the
  state-level fact through the `type?` shape pairing, exactly mirroring
  `InteractionPreservation.Instr.openRunAt_atLoweredEnd`.
-/

namespace EvmCompiler
namespace TypedCfg

open Simulation.Interaction (AllDone)

/-- Terminal-leaf property for the open one-instruction *state* step: every
successful branch realizes the (fixed) output shape; error branches are
vacuously fine. -/
def StackRealizesState (output : Shape) :
    Except EVMException EVMState → Prop
  | .error _ => True
  | .ok final => StackRealizes output final

/-- Terminal-leaf property for the open one-instruction step (`openRunAt`),
which returns the `(state, shape)` pair.  The reported shape is always the
typed `output`, so we realize `output` against the final state. -/
def StackRealizesPair (output : Shape) :
    Except EVMException (EVMState × Shape) → Prop
  | .error _ => True
  | .ok (final, _actualOutput) => StackRealizes output final

/-- **State-level open `StackRealizes` bridge.** Every terminal leaf of the open
one-instruction state step realizes the output shape.  Quantifies over every
CALL/CREATE/resource response through `AllDone`. -/
theorem openRunState_stackRealizes
    {instr : TypedCfg.Instr} {input output : Shape} {state : EVMState}
    (hType : instr.type? input = some output)
    (hReal : StackRealizes input state) :
    AllDone (StackRealizesState output)
      (InteractionSemantics.Instr.openRunState instr input state) := by
  cases instr with
  | prim op =>
      -- Open prim delegates to the Assembly `openStep`; use the arity contract.
      show AllDone (StackRealizesState output)
        (Assembly.InteractionSemantics.PrimOp.openStep op state)
      cases hArity : op.stackArity? with
      | none =>
          simp [TypedCfg.Instr.type?, hArity] at hType
      | some arity =>
          rcases arity with ⟨inArity, outArity⟩
          obtain ⟨hIn, hOutLen⟩ :=
            TypedCfg.Instr.length_of_type?_prim hArity hType
          have hStack :=
            Assembly.InteractionPreservation.PrimOp.openStep_realizesStackArity
              (state := state) hArity
          apply AllDone.mono hStack
          intro outcome hR
          cases outcome with
          | error err => exact True.intro
          | ok final =>
              simp only
                [Assembly.InteractionPreservation.PrimOp.RealizesStackArity]
                at hR
              show StackRealizes output final
              unfold StackRealizes at *
              omega
  | push _ | returnToken _ | pop | dup _ | swap _
  | bindLocals _ _ | bindScratch _ _ _ | relabel _ | unwind _ =>
      rw [InteractionSemantics.Instr.openRunState_eq_done_of_not_prim
        (by intro op h; cases h)]
      cases hRun : TypedCfg.Instr.runState _ input state with
      | error err => exact AllDone.done True.intro
      | ok final =>
          exact AllDone.done (runState_stackRealizes hType hRun hReal)

/-- **`runAt`-level open `StackRealizes` bridge (the Step D gating lemma).**
Every terminal leaf of the open one-instruction step (`openRunAt`) realizes the
typed output shape against the returned state.  Obtained by mapping the
state-level fact through the `type?` pairing, mirroring
`InteractionPreservation.Instr.openRunAt_atLoweredEnd`. -/
theorem openRunAt_stackRealizes
    {instr : TypedCfg.Instr} {input output : Shape} {state : EVMState}
    (hType : instr.type? input = some output)
    (hReal : StackRealizes input state) :
    AllDone (StackRealizesPair output)
      (InteractionSemantics.Instr.openRunAt instr input state) := by
  have hState := openRunState_stackRealizes hType hReal
  have hMapped :
      AllDone (StackRealizesPair output)
        (Simulation.Interaction.map
          (fun final => (final, output))
          (InteractionSemantics.Instr.openRunState instr input state)) := by
    apply AllDone.map (fun final => (final, output)) hState
    · intro err _hErr; exact True.intro
    · intro final hFinal; exact hFinal
  simpa [InteractionSemantics.Instr.openRunAt,
    TypedCfg.Control.Instr.runAt, hType,
    Simulation.Interaction.map] using hMapped

end TypedCfg
end EvmCompiler
