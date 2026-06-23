import EvmCompiler.Assembly.InteractionFuelSafety
import EvmCompiler.TypedCfg.InteractionSemantics
import Mathlib.Tactic.IntervalCases

namespace EvmCompiler
namespace TypedCfg
namespace InteractionFuelSafety

open Assembly.InteractionFuelSafety

namespace Instr

private theorem continuingStep
    {op : Assembly.PrimOp} {step : Assembly.PrimStep}
    (hStep : op.continuingStep? = some step) (state : EVMState) :
    NotOutOfFuel (op.step state) := by
  rw [Assembly.PrimOp.step_eq_continuingStep_run hStep]
  exact Assembly.InteractionFuelSafety.PrimStep.run step state

private theorem runPops (count : Nat) (state : EVMState) :
    NotOutOfFuel (TypedCfg.Instr.runPops count state) := by
  induction count generalizing state with
  | zero => trivial
  | succ count ih =>
      unfold TypedCfg.Instr.runPops
      cases hPop : Assembly.PrimOp.pop.step state with
      | error error =>
          have hSafe := continuingStep (op := Assembly.PrimOp.pop) rfl state
          rw [hPop] at hSafe
          exact hSafe
      | ok next =>
          exact ih next

/-- TypedCfg instructions may raise EVM runtime errors, but never the
interpreter-owned structural `OutOfFuel` marker. -/
theorem openRunState (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (InteractionSemantics.Instr.openRunState instr shape state) := by
  cases instr with
  | prim op =>
      exact Assembly.InteractionFuelSafety.PrimOp.openStep op state
  | push value
  | returnToken value
  | bindLocals offset names
  | bindScratch baseDepth name slot
  | relabel targetShape =>
      exact .done (by
        simp [InteractionSemantics.Instr.openRunState,
          Assembly.InteractionFuelSafety.NotOutOfFuel,
          TypedCfg.Instr.runState])
  | pop =>
      exact .done (continuingStep (op := Assembly.PrimOp.pop) rfl state)
  | dup depth =>
      exact .done (by
        by_cases hDepth : depth < 16
        · interval_cases depth <;>
            simp only [TypedCfg.Instr.runState] <;>
            apply continuingStep <;> rfl
        · have hLe : 16 <= depth := Nat.le_of_not_gt hDepth
          obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le hLe
          rw [Nat.add_comm 16 rest]
          simp [TypedCfg.Instr.runState, NotOutOfFuel])
  | swap depth =>
      exact .done (by
        by_cases hDepth : depth < 16
        · interval_cases depth <;>
            simp only [TypedCfg.Instr.runState] <;>
            apply continuingStep <;> rfl
        · have hLe : 16 <= depth := Nat.le_of_not_gt hDepth
          obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le hLe
          rw [Nat.add_comm 16 rest]
          simp [TypedCfg.Instr.runState, NotOutOfFuel])
  | unwind targetShape =>
      exact .done (runPops (shape.length - targetShape.length) state)

theorem openRunAt (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (InteractionSemantics.Instr.openRunAt instr shape state) := by
  unfold InteractionSemantics.Instr.openRunAt Control.Instr.runAt
  cases hType : instr.type? shape with
  | none =>
      exact .done (by simp [hType, NotOutOfFuel])
  | some output =>
      simp only [hType, Option.elim_some,
        Simulation.Interaction.bind_done_ok]
      exact NotOutOfFuel.map (fun next => (next, output))
        (openRunState instr shape state)

end Instr

namespace Block

private theorem runTermChecked (shape : Shape) (term : TypedCfg.Terminator)
    (state : EVMState) :
    NotOutOfFuel (TypedCfg.Block.runTermChecked shape term state) := by
  cases term with
  | halt kind =>
      cases kind <;> try trivial
      by_cases hPermission : state.executionEnv.perm = true <;>
        simp [TypedCfg.Block.runTermChecked, hPermission, NotOutOfFuel]
  | fallthrough target
  | jump target
  | jumpi target fallthrough
  | returnDispatch returnCount sites
  | invalid => trivial

theorem openRunBody (body : List TypedCfg.Instr) (shape : Shape)
    (state : EVMState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (InteractionSemantics.Block.openRunBody body shape state) := by
  induction body generalizing shape state with
  | nil => exact .done trivial
  | cons instr rest ih =>
      unfold InteractionSemantics.Block.openRunBody Control.Block.runBody
      exact NotOutOfFuel.bind (Instr.openRunAt instr shape state)
        (fun result => ih result.2 result.1)

theorem openRun (block : TypedCfg.Block) (state : EVMState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (InteractionSemantics.Block.openRun block state) := by
  unfold InteractionSemantics.Block.openRun Control.Block.run
  exact NotOutOfFuel.bind
    (openRunBody block.body block.input state) (fun result => by
      rcases result with ⟨state, output⟩
      by_cases hOutput : output = block.output
      · simp only [hOutput, ↓reduceIte]
        cases hTerm :
            TypedCfg.Block.runTermChecked block.output block.term state with
        | error error =>
            have hSafe := runTermChecked block.output block.term state
            rw [hTerm] at hSafe
            exact .done hSafe
        | ok outcome => exact .done trivial
      · simp only [hOutput, ↓reduceIte]
        exact .done (by simp [NotOutOfFuel]))

end Block

namespace Program

theorem openStep (program : TypedCfg.Program) (label : Label)
    (state : EVMState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (InteractionSemantics.Program.openStep program label state) := by
  unfold InteractionSemantics.Program.openStep Control.Program.step
  cases hBlock : program.findBlock? label with
  | none => exact .done trivial
  | some block =>
      simpa only [hBlock] using Block.openRun block state

theorem openRunNResultWithStop
    (stopJump : Label -> EVMState -> Bool)
    (program : TypedCfg.Program) (fuel : Nat)
    (label : Label) (state : EVMState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (InteractionSemantics.Program.openRunNResultWithStop
        stopJump program fuel label state) := by
  induction fuel generalizing label state with
  | zero => exact .done trivial
  | succ fuel ih =>
      rw [InteractionSemantics.Program.openRunNResultWithStop_succ]
      exact NotOutOfFuel.bind (openStep program label state) (fun outcome => by
        cases outcome with
        | jump next nextState =>
            by_cases hStop : stopJump next nextState
            · simp only [hStop, ↓reduceIte]
              exact .done trivial
            · simp only [hStop, ↓reduceIte]
              exact ih next nextState
        | fallthrough final
        | returnDispatch final
        | halt kind final
        | invalid final => exact .done trivial)

end Program
end InteractionFuelSafety
end TypedCfg
end EvmCompiler
