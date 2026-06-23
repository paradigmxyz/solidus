import EvmCompiler.Assembly.InteractionFuelSafety
import EvmCompiler.Structured.InteractionSemantics

namespace EvmCompiler
namespace Structured
namespace InteractionFuelSafety

open Assembly.InteractionFuelSafety

namespace BasicInstr

theorem openStepEVM (instr : Structured.BasicInstr) (state : EVMState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Structured.InteractionSemantics.BasicInstr.openStepEVM instr state) := by
  cases instr with
  | push value => exact .done trivial
  | op op => exact Assembly.InteractionFuelSafety.PrimOp.openStep op.toPrimOp state
  | bindLocals offset names => exact .done trivial
  | bindScratch baseDepth name slot => exact .done trivial

theorem openStep (instr : Structured.BasicInstr) (state : RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Structured.InteractionSemantics.BasicInstr.openStep instr state) := by
  exact NotOutOfFuel.map state.withEVM (openStepEVM instr state.evm)

end BasicInstr

namespace Terminal

theorem openStep (kind : Assembly.HaltKind) (state : RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Structured.InteractionSemantics.Terminal.openStep kind state) := by
  exact NotOutOfFuel.map state.withEVM
    (Assembly.InteractionFuelSafety.PrimOp.openStep kind.toPrimOp state.evm)

end Terminal

namespace Code

theorem openRun (code : Structured.Code) (state : RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Structured.InteractionSemantics.Code.openRun code state) := by
  induction code generalizing state with
  | nil => exact .done trivial
  | cons instr rest ih =>
      unfold Structured.InteractionSemantics.Code.openRun
      simp only [Structured.EffectSemantics.Control.Code.run]
      exact NotOutOfFuel.bind (BasicInstr.openStep instr state)
        (fun next => ih next)

theorem openPopCondition (state : RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Structured.InteractionSemantics.Code.openPopCondition state) := by
  unfold Structured.InteractionSemantics.Code.openPopCondition
    Structured.EffectSemantics.Control.Code.popCondition
  cases hPop : state.evm.stack.pop with
  | none =>
      simp only [Structured.EffectSemantics.Ordinary.runStateModel_evm,
        hPop]
      exact .done (by simp [NotOutOfFuel])
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp only [Structured.EffectSemantics.Ordinary.runStateModel_evm,
        hPop, Structured.EffectSemantics.Ordinary.runStateModel_withEVM]
      exact .done trivial

theorem openRunCondition (code : Structured.Code) (state : RunState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Structured.InteractionSemantics.Code.openRunCondition code state) := by
  unfold Structured.InteractionSemantics.Code.openRunCondition
    Structured.EffectSemantics.Control.Code.runCondition
  exact NotOutOfFuel.bind (openRun code state) openPopCondition

end Code
end InteractionFuelSafety
end Structured
end EvmCompiler
