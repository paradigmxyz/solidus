import EvmCompiler.Assembly.InteractionSemantics

namespace EvmCompiler
namespace Assembly
namespace InteractionFuelSafety

def NotOutOfFuel {α : Type} : Except EVMException α -> Prop
  | .error error => error ≠ .OutOfFuel
  | .ok _ => True

/-- The target may report any runtime error, but target structural truncation
must come only from source structural truncation. -/
def StructuralErrorRel (source target : EVMException) : Prop :=
  target = .OutOfFuel → source = .OutOfFuel

namespace StructuralErrorRel

theorem of_target_not {source target : EVMException}
    (hTarget : target ≠ .OutOfFuel) : StructuralErrorRel source target := by
  intro hOutOfFuel
  exact False.elim (hTarget hOutOfFuel)

theorem refl (error : EVMException) : StructuralErrorRel error error := by
  intro hOutOfFuel
  exact hOutOfFuel

end StructuralErrorRel

namespace NotOutOfFuel

theorem bind {α β : Type}
    {interaction : Simulation.Interaction EVMException α}
    {next : α → Simulation.Interaction EVMException β}
    (hInteraction : Simulation.Interaction.AllDone NotOutOfFuel interaction)
    (hNext : ∀ value,
      Simulation.Interaction.AllDone NotOutOfFuel (next value)) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Simulation.Interaction.bind interaction next) := by
  exact Simulation.Interaction.AllDone.bind hInteraction
    (fun _ hError => hError) (fun value _ => hNext value)

theorem map {α β : Type} (f : α → β)
    {interaction : Simulation.Interaction EVMException α}
    (hInteraction : Simulation.Interaction.AllDone NotOutOfFuel interaction) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Simulation.Interaction.map f interaction) := by
  exact Simulation.Interaction.AllDone.map f hInteraction
    (fun _ hError => hError) (fun _ _ => trivial)

/-- Refine a legacy coarse error relation once the target owner has proved
that its interaction cannot produce structural `OutOfFuel`. -/
theorem refineExceptRel {α β : Type} {valueRel : α → β → Prop}
    {source : Simulation.Interaction EVMException α}
    {target : Simulation.Interaction EVMException β}
    (hRel : Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel (fun _ _ => True) valueRel)
      source target)
    (hTarget : Simulation.Interaction.AllDone NotOutOfFuel target) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel StructuralErrorRel valueRel)
      source target := by
  apply Simulation.Interaction.Rel.mono
    (Simulation.Interaction.Rel.strengthen_right hRel hTarget)
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRelated, hSafe⟩
  cases hRelated with
  | error _ =>
      exact Simulation.Interaction.ExceptRel.error
        (StructuralErrorRel.of_target_not hSafe)
  | ok hValue =>
      exact Simulation.Interaction.ExceptRel.ok hValue

end NotOutOfFuel

namespace PrimStep

theorem run (step : Assembly.PrimStep) (state : EVMState) :
    NotOutOfFuel (step.run state) := by
  cases step <;>
    simp only [Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.EVM.execUnOp,
      EvmYul.EVM.execTriOp, EvmYul.EVM.executionEnvOp,
      EvmYul.EVM.unaryExecutionEnvOp, EvmYul.EVM.machineStateOp,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.dup, EvmYul.swap]
  all_goals
    repeat' first | split
    all_goals simp [Id.run, NotOutOfFuel]

end PrimStep

namespace PrimOp

private theorem stopStep (state : EVMState) :
    NotOutOfFuel (Assembly.PrimOp.stop.step state) := by
  cases hRun : Assembly.PrimOp.stop.step state with
  | ok final => trivial
  | error error =>
      by_cases hError : error = .OutOfFuel
      · subst error
        unfold Assembly.PrimOp.step at hRun
        change EvmYul.step (τ := .EVM) .STOP none state =
          .error .OutOfFuel at hRun
        cases state
        cases hRun
      · exact hError

private theorem pcStep (state : EVMState) :
    NotOutOfFuel (Assembly.PrimOp.pc.step state) := by
  cases hRun : Assembly.PrimOp.pc.step state with
  | ok final => trivial
  | error error =>
      by_cases hError : error = .OutOfFuel
      · subst error
        unfold Assembly.PrimOp.step at hRun
        change EvmYul.step (τ := .EVM) .PC none state =
          .error .OutOfFuel at hRun
        cases state
        cases hRun
      · exact hError

private theorem returnStep (state : EVMState) :
    NotOutOfFuel (Assembly.PrimOp.return.step state) := by
  cases hRun : Assembly.PrimOp.return.step state with
  | ok final => trivial
  | error error =>
      by_cases hError : error = .OutOfFuel
      · subst error
        unfold Assembly.PrimOp.step at hRun
        change EvmYul.step (τ := .EVM) .RETURN none state =
          .error .OutOfFuel at hRun
        cases state with
        | mk shared pc stack execLength =>
            cases stack with
            | nil => cases hRun
            | cons address rest =>
                cases rest with
                | nil => cases hRun
                | cons size tail => cases hRun
      · exact hError

private theorem revertStep (state : EVMState) :
    NotOutOfFuel (Assembly.PrimOp.revert.step state) := by
  cases hRun : Assembly.PrimOp.revert.step state with
  | ok final => trivial
  | error error =>
      by_cases hError : error = .OutOfFuel
      · subst error
        unfold Assembly.PrimOp.step at hRun
        change EvmYul.step (τ := .EVM) .REVERT none state =
          .error .OutOfFuel at hRun
        cases state with
        | mk shared pc stack execLength =>
            cases stack with
            | nil => cases hRun
            | cons address rest =>
                cases rest with
                | nil => cases hRun
                | cons size tail => cases hRun
      · exact hError

private theorem selfdestructStep (state : EVMState) :
    NotOutOfFuel (Assembly.PrimOp.selfdestruct.step state) := by
  cases hRun : Assembly.PrimOp.selfdestruct.step state with
  | ok final => trivial
  | error error =>
      by_cases hError : error = .OutOfFuel
      · subst error
        cases hPermission : state.executionEnv.perm with
        | false =>
            rw [Assembly.PrimOp.step_selfdestruct_of_static state hPermission]
              at hRun
            cases hRun
        | true =>
            rw [Assembly.PrimOp.step_selfdestruct_of_permitted state hPermission]
              at hRun
            cases state with
            | mk shared pc stack execLength =>
                cases stack with
                | nil => cases hRun
                | cons recipient rest => cases hRun
      · exact hError

theorem openStep (op : Assembly.PrimOp) (state : EVMState) :
    Simulation.Interaction.AllDone NotOutOfFuel
      (Assembly.InteractionSemantics.PrimOp.openStep op state) := by
  cases hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM with
  | some external =>
      cases external with
      | call kind =>
          rw [show
            Assembly.InteractionSemantics.PrimOp.openStep op state =
              Assembly.InteractionSemantics.PrimOp.callStep kind state by
                simp [Assembly.InteractionSemantics.PrimOp.openStep,
                  hExternal]]
          unfold Assembly.InteractionSemantics.PrimOp.callStep
          split
          · exact .done (by simp [NotOutOfFuel])
          · dsimp only
            split
            · exact .request fun _ => .done trivial
            · exact .done (by simp [NotOutOfFuel])
      | create kind =>
          rw [show
            Assembly.InteractionSemantics.PrimOp.openStep op state =
              Assembly.InteractionSemantics.PrimOp.createStep kind state by
                simp [Assembly.InteractionSemantics.PrimOp.openStep,
                  hExternal]]
          unfold Assembly.InteractionSemantics.PrimOp.createStep
          split
          · exact .done (by simp [NotOutOfFuel])
          · dsimp only
            split
            · exact .request fun _ => .done trivial
            · exact .done (by simp [NotOutOfFuel])
  | none =>
      by_cases hGas : op = .gas
      · subst op
        exact .request fun _ => .done trivial
      · by_cases hMsize : op = .msize
        · subst op
          exact .request fun _ => .done trivial
        · cases hStep : op.continuingStep? with
          | some step =>
              rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
                hStep hGas hMsize]
              exact .done (PrimStep.run step state)
          | none =>
              cases op <;>
                simp [Assembly.PrimOp.continuingStep?] at hStep
              all_goals have hClosed := hExternal
              all_goals
                simp [Assembly.PrimOp.toEVM,
                  Simulation.ExternalKind.ofEVMOperation?,
                  Simulation.CallKind.ofEVMOperation?,
                  Simulation.CreateKind.ofEVMOperation?] at hExternal
              all_goals try contradiction
              all_goals
                rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
                  hClosed hGas hMsize]
                apply Simulation.Interaction.AllDone.done
              all_goals first
                | exact stopStep state
                | exact pcStep state
                | exact returnStep state
                | exact revertStep state
                | exact selfdestructStep state

end PrimOp
end InteractionFuelSafety
end Assembly
end EvmCompiler
