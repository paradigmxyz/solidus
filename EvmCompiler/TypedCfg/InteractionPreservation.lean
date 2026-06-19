import EvmCompiler.Assembly.StackShuffleInteractionPreservation
import EvmCompiler.TypedCfg.InteractionCongruence
import EvmCompiler.TypedCfg.InteractionSemantics
import EvmCompiler.TypedCfg.Preservation

namespace EvmCompiler
namespace TypedCfg
namespace InteractionPreservation

open Assembly.InteractionPreservation

namespace OpenOutcome

/--
TypedCfg outcomes related to compiled Assembly outcomes under open effects.
The halt case is stable under compiler-owned PC changes, while all other cases
reuse the ordinary pass-owned outcome relation.
-/
def Simulates (program : Assembly.Program) :
    TypedCfg.Outcome → Assembly.Source.ExecutionOutcome → Prop
  | .fallthrough state, target =>
      Preservation.Outcome.Simulates program
        (.fallthrough state) target
  | .jump label state, target =>
      Preservation.Outcome.Simulates program
        (.jump label state) target
  | .returnDispatch state, target =>
      Preservation.Outcome.Simulates program
        (.returnDispatch state) target
  | .halt kind state, target =>
      ∃ simulated,
        Assembly.SameRuntimeData simulated state ∧
          target =
            Assembly.Target.stepInstrResult
              (.prim kind.toPrimOp) simulated
  | .invalid state, target =>
      Preservation.Outcome.Simulates program
        (.invalid state) target

theorem of_preservation
    {program : Assembly.Program}
    {source : TypedCfg.Outcome}
    {target : Assembly.Source.ExecutionOutcome}
    (hSim :
      Preservation.Outcome.Simulates program source target) :
    Simulates program source target := by
  cases source with
  | fallthrough state =>
      exact hSim
  | jump label state =>
      exact hSim
  | returnDispatch state =>
      exact hSim
  | halt kind state =>
      exact
        ⟨state, Assembly.SameRuntimeData.refl state, hSim⟩
  | invalid state =>
      exact hSim

theorem runtime_left
    {program : Assembly.Program}
    {left middle : TypedCfg.Outcome}
    {target : Assembly.Source.ExecutionOutcome}
    (hRuntime :
      InteractionCongruence.Outcome.RuntimeRel left middle)
    (hSim : Simulates program middle target) :
    Simulates program left target := by
  cases hRuntime with
  | fallthrough hState =>
      unfold Simulates Preservation.Outcome.Simulates
        Preservation.Outcome.RunningData at hSim ⊢
      cases target with
      | error error =>
          exact hSim.elim
      | ok result =>
          cases result with
          | running targetState =>
              exact
                Assembly.SameRuntimeData.trans hSim hState.symm
          | halted halt =>
              exact hSim.elim
  | jump label hState =>
      unfold Simulates Preservation.Outcome.Simulates
        Preservation.Outcome.RunningAt at hSim ⊢
      rcases hSim with ⟨dest, hLabel, hTarget⟩
      refine ⟨dest, hLabel, ?_⟩
      cases target with
      | error error =>
          exact hTarget.elim
      | ok result =>
          cases result with
          | running targetState =>
              exact
                ⟨hTarget.1,
                  Assembly.SameRuntimeData.trans
                    hTarget.2 hState.symm⟩
          | halted halt =>
              exact hTarget.elim
  | returnDispatch hState =>
      unfold Simulates Preservation.Outcome.Simulates
        Preservation.Outcome.RunningData at hSim ⊢
      cases target with
      | error error =>
          exact hSim.elim
      | ok result =>
          cases result with
          | running targetState =>
              exact
                Assembly.SameRuntimeData.trans hSim hState.symm
          | halted halt =>
              exact hSim.elim
  | halt kind hState =>
      rcases hSim with ⟨simulated, hData, hTarget⟩
      exact
        ⟨simulated,
          Assembly.SameRuntimeData.trans hData hState.symm,
          hTarget⟩
  | invalid hState =>
      exact hSim

end OpenOutcome

namespace OpenBlock

def RunSimulates (program : Assembly.Program) :
    Except EVMException TypedCfg.Outcome →
      Assembly.Source.ExecutionOutcome → Prop
  | .error error, target => target = .error error
  | .ok source, target =>
      OpenOutcome.Simulates program source target

theorem of_preservation
    {program : Assembly.Program}
    {source : Except EVMException TypedCfg.Outcome}
    {target : Assembly.Source.ExecutionOutcome}
    (hSim : Preservation.Block.RunSimulates program source target) :
    RunSimulates program source target := by
  cases source with
  | error error =>
      exact hSim
  | ok outcome =>
      exact OpenOutcome.of_preservation hSim

theorem runtime_left
    {program : Assembly.Program}
    {left middle : Except EVMException TypedCfg.Outcome}
    {target : Assembly.Source.ExecutionOutcome}
    (hRuntime :
      Simulation.Interaction.ExceptRel
        (fun left right : EVMException => left = right)
        InteractionCongruence.Outcome.RuntimeRel
        left middle)
    (hSim : RunSimulates program middle target) :
    RunSimulates program left target := by
  cases hRuntime with
  | error hError =>
      subst hError
      exact hSim
  | ok hOutcome =>
      exact OpenOutcome.runtime_left hOutcome hSim

/-- A source-safe TypedCfg halt is realized as a terminal Assembly result by
the adjacent lowering relation. -/
theorem terminal_of_assemblySafeHalted
    {program : Assembly.Program}
    {source : Except EVMException TypedCfg.Outcome}
    {target : Assembly.Source.ExecutionOutcome}
    (hSafe :
      TypedCfg.InteractionSemantics.Program.AssemblySafeHalted source)
    (hSim : RunSimulates program source target) :
    Assembly.InteractionSemantics.Terminal target := by
  cases source with
  | error sourceError => cases hSafe
  | ok sourceOutcome =>
      cases sourceOutcome with
      | fallthrough state => cases hSafe
      | jump label state => cases hSafe
      | returnDispatch state => cases hSafe
      | invalid state => cases hSafe
      | halt kind state =>
          unfold RunSimulates OpenOutcome.Simulates at hSim
          rcases hSim with ⟨simulated, hRuntime, hTarget⟩
          obtain ⟨simulatedFinal, hStep⟩ :=
            Assembly.InteractionSemantics.Terminal.SafeAt.of_sameRuntimeData
              hRuntime hSafe
          subst target
          unfold Assembly.Target.stepInstrResult
          rw [hStep]
          have hKind :
              (Assembly.TargetInstr.prim kind.toPrimOp).haltKind? =
                some kind := by
            cases kind <;> rfl
          rw [hKind]
          trivial

end OpenBlock

theorem runPops_source_openRunNResult
    (count : Nat) {pre post : Assembly.Program} {state : EVMState}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (List.replicate count (.prim .pop)))
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ List.replicate count (.prim .pop) ++ post)
        count state =
      .done
        ((TypedCfg.Instr.runPops count state).map
          Assembly.StepResult.running) := by
  induction count generalizing pre state with
  | zero =>
      rfl
  | succ count ih =>
      rcases hFits with ⟨hFitsHere, hFitsRest⟩
      rw [List.replicate_succ]
      simp only [List.append_assoc]
      change
        Assembly.InteractionSemantics.Source.openRunNResult
            (pre ++ Assembly.Instr.prim Assembly.PrimOp.pop ::
              (List.replicate count
                (Assembly.Instr.prim Assembly.PrimOp.pop) ++ post))
            (count + 1) state =
          .done
            ((TypedCfg.Instr.runPops (count + 1) state).map
              Assembly.StepResult.running)
      unfold
        Assembly.InteractionSemantics.Source.openRunNResult
        Assembly.Control.runNResultWith
        TypedCfg.Instr.runPops
      rw [source_openStepResult_at_boundary hFitsHere hPc]
      have hExternal :
          Simulation.ExternalKind.ofEVMOperation?
              Assembly.PrimOp.pop.toEVM =
            none := by
        rfl
      cases hStep : Assembly.PrimOp.pop.step state with
      | error err =>
          simp [Assembly.InteractionSemantics.Source.openStepAtResult,
            Assembly.InteractionSemantics.Source.openStepAt,
            Assembly.InteractionSemantics.PrimOp.openStep,
            hExternal, hStep,
            Simulation.Interaction.bind]
          change
            (Simulation.Interaction.done (.error err) :
              Simulation.Interaction EVMException
                Assembly.StepResult) =
              Simulation.Interaction.done (.error err)
          rfl
      | ok state' =>
          simp only [
            Assembly.InteractionSemantics.Source.openStepAtResult,
            Assembly.InteractionSemantics.Source.openStepAt,
            Assembly.InteractionSemantics.PrimOp.openStep,
            hExternal,
            Assembly.Instr.haltKind?,
            Assembly.PrimOp.haltKind?,
            hStep,
            Simulation.Interaction.bind_done_ok,
            Except.map]
          have hPc' :
              state'.pc =
                (pre ++
                  [Assembly.Instr.prim Assembly.PrimOp.pop]).pcAfter := by
            calc
              state'.pc =
                  state.pc + EvmYul.UInt256.ofNat 1 :=
                Preservation.pop_step_pc hStep
              _ = pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
                rw [hPc]
              _ =
                  (pre ++
                    [Assembly.Instr.prim Assembly.PrimOp.pop]).pcAfter := by
                simpa [Assembly.Instr.byteSize] using
                  (Assembly.Program.pcAfter_snoc pre
                    (Assembly.Instr.prim Assembly.PrimOp.pop)).symm
          have hTail :=
            ih (pre := pre ++ [Assembly.Instr.prim .pop])
              (state := state') hFitsRest hPc'
          simpa [List.append_assoc] using hTail

namespace Instr

theorem interaction_map_done
    {α β : Type} (f : α → β)
    (result : Except EVMException α) :
    Simulation.Interaction.map f (.done result) =
      .done (result.map f) := by
  cases result <;> rfl

def StateAtLoweredEnd (state : EVMState)
    (code : Assembly.Program) :
    Except EVMException EVMState → Prop
  | .error _ => True
  | .ok final =>
      final.pc =
        state.pc + EvmYul.UInt256.ofNat code.byteLength

def AtLoweredEnd (state : EVMState)
    (code : Assembly.Program) (output : Shape) :
    Except EVMException (EVMState × Shape) → Prop
  | .error _ => True
  | .ok (final, actualOutput) =>
      final.pc =
          state.pc + EvmYul.UInt256.ofNat code.byteLength ∧
        actualOutput = output

theorem openRunState_atLoweredEnd_of_done
    {instr : TypedCfg.Instr} {shape output : Shape}
    {code : Assembly.Program} {state : EVMState}
    (hLower : instr.lowerAt? shape = some (code, output))
    (hOpen :
      TypedCfg.InteractionSemantics.Instr.openRunState
          instr shape state =
        .done (TypedCfg.Instr.runState instr shape state)) :
    Simulation.Interaction.AllDone (StateAtLoweredEnd state code)
      (TypedCfg.InteractionSemantics.Instr.openRunState
        instr shape state) := by
  rw [hOpen]
  cases hRun : TypedCfg.Instr.runState instr shape state with
  | error err =>
      exact .done trivial
  | ok final =>
      exact
        .done
          (Preservation.Instr.runState_pc_of_lowerAt
            hLower hRun)

/--
Every successful branch of a lowered typed instruction reaches the end of its
Assembly fragment. This includes every answer to resource and open-world
requests.
-/
theorem openRunState_atLoweredEnd
    {instr : TypedCfg.Instr} {shape output : Shape}
    {code : Assembly.Program} {state : EVMState}
    (hLower : instr.lowerAt? shape = some (code, output)) :
    Simulation.Interaction.AllDone (StateAtLoweredEnd state code)
      (TypedCfg.InteractionSemantics.Instr.openRunState
        instr shape state) := by
  cases instr with
  | prim op =>
      cases hType : TypedCfg.Instr.type? (.prim op) shape with
      | none =>
          simp [TypedCfg.Instr.lowerAt?, hType] at hLower
      | some typedOutput =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          cases hArity : op.stackArity? with
          | none =>
              simp [TypedCfg.Instr.type?, hArity] at hType
          | some arity =>
              rcases arity with ⟨input, outputArity⟩
              have hOpen :=
                Assembly.InteractionPreservation.PrimOp.openStep_advancesPC
                  (state := state) hArity
              simpa [TypedCfg.InteractionSemantics.Instr.openRunState,
                StateAtLoweredEnd,
                Assembly.InteractionPreservation.PrimOp.AdvancesPC,
                Assembly.Program.byteLength,
                Assembly.Instr.byteSize] using hOpen
  | push value =>
      exact openRunState_atLoweredEnd_of_done hLower rfl
  | returnToken value =>
      exact openRunState_atLoweredEnd_of_done hLower rfl
  | pop =>
      exact openRunState_atLoweredEnd_of_done hLower rfl
  | dup depth =>
      exact openRunState_atLoweredEnd_of_done hLower rfl
  | swap depth =>
      exact openRunState_atLoweredEnd_of_done hLower rfl
  | bindLocals offset names =>
      exact openRunState_atLoweredEnd_of_done hLower rfl
  | bindScratch baseDepth name slot =>
      exact openRunState_atLoweredEnd_of_done hLower rfl
  | relabel target =>
      exact openRunState_atLoweredEnd_of_done hLower rfl
  | unwind target =>
      exact openRunState_atLoweredEnd_of_done hLower rfl

theorem openRunAt_atLoweredEnd
    {instr : TypedCfg.Instr} {shape output : Shape}
    {code : Assembly.Program} {state : EVMState}
    (hLower : instr.lowerAt? shape = some (code, output)) :
    Simulation.Interaction.AllDone
      (AtLoweredEnd state code output)
      (TypedCfg.InteractionSemantics.Instr.openRunAt
        instr shape state) := by
  have hType :
      instr.type? shape = some output :=
    Preservation.Instr.type?_eq_some_of_lowerAt? hLower
  have hState :=
    openRunState_atLoweredEnd (state := state) hLower
  have hMapped :
      Simulation.Interaction.AllDone
        (AtLoweredEnd state code output)
        (Simulation.Interaction.map
          (fun final => (final, output))
          (TypedCfg.InteractionSemantics.Instr.openRunState
            instr shape state)) := by
    apply Simulation.Interaction.AllDone.map
      (fun final => (final, output)) hState
    · intro err hError
      trivial
    · intro final hPc
      exact ⟨hPc, rfl⟩
  simpa [TypedCfg.InteractionSemantics.Instr.openRunAt,
    TypedCfg.Control.Instr.runAt, hType,
    Simulation.Interaction.map] using hMapped

theorem openRunAt_eq_done_of_runState
    {instr : TypedCfg.Instr} {shape : Shape} {state : EVMState}
    (hOpen :
      TypedCfg.InteractionSemantics.Instr.openRunState
          instr shape state =
        .done (TypedCfg.Instr.runState instr shape state)) :
    TypedCfg.InteractionSemantics.Instr.openRunAt
        instr shape state =
      .done (TypedCfg.Instr.runAt instr shape state) := by
  unfold
    TypedCfg.InteractionSemantics.Instr.openRunAt
    TypedCfg.Control.Instr.runAt
    TypedCfg.Instr.runAt
  cases hType : instr.type? shape with
  | none =>
      rfl
  | some output =>
      rw [hOpen]
      cases hRun : TypedCfg.Instr.runState instr shape state with
      | error err =>
          rfl
      | ok state' =>
          rfl

theorem lowerAt_single_closed
    {instr : TypedCfg.Instr} {shape output : Shape}
    {asmInstr : Assembly.Instr}
    {pre post : Assembly.Program} {state : EVMState}
    (hLower :
      instr.lowerAt? shape = some ([asmInstr], output))
    (hFits :
      Assembly.Program.PCFitsFrom pre [asmInstr])
    (hPc : state.pc = pre.pcAfter)
    (hSourceOpen :
      TypedCfg.InteractionSemantics.Instr.openRunState
          instr shape state =
        .done (TypedCfg.Instr.runState instr shape state))
    (hTargetOpen :
      Assembly.InteractionSemantics.Source.openStepAt
          (pre ++ asmInstr :: post) pre.byteLength asmInstr state =
        .done
          (Assembly.Source.stepAt
            (pre ++ asmInstr :: post) pre.byteLength asmInstr state)) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ [asmInstr] ++ post) [asmInstr].length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          instr shape state) := by
  have hTarget :=
    source_openRunNResult_one_eq_done
      (pre := pre) (post := post) (instr := asmInstr)
      hFits.1 hPc hTargetOpen
  have hPlain :=
    Preservation.Instr.lowerAt_source_runNResult
      (post := post) hLower hFits hPc
  have hSource :=
    openRunAt_eq_done_of_runState hSourceOpen
  calc
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ [asmInstr] ++ post) [asmInstr].length state =
        .done
          (Assembly.Source.runNResult
            (pre ++ [asmInstr] ++ post) [asmInstr].length state) := by
      simpa [List.append_assoc] using hTarget
    _ =
        .done
          ((TypedCfg.Instr.runAt instr shape state).map
            (fun result => Assembly.StepResult.running result.1)) := by
      rw [hPlain]
    _ =
        Simulation.Interaction.map
          (fun result => Assembly.StepResult.running result.1)
          (TypedCfg.InteractionSemantics.Instr.openRunAt
            instr shape state) := by
      rw [hSource]
      rw [interaction_map_done]

theorem lowerAt_empty_closed
    {instr : TypedCfg.Instr} {shape output : Shape}
    {pre post : Assembly.Program} {state : EVMState}
    (hLower : instr.lowerAt? shape = some ([], output))
    (hFits : Assembly.Program.PCFitsFrom pre [])
    (hPc : state.pc = pre.pcAfter)
    (hSourceOpen :
      TypedCfg.InteractionSemantics.Instr.openRunState
          instr shape state =
        .done (TypedCfg.Instr.runState instr shape state)) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ [] ++ post) ([] : Assembly.Program).length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          instr shape state) := by
  have hPlain :=
    Preservation.Instr.lowerAt_source_runNResult
      (post := post) hLower hFits hPc
  have hSource :=
    openRunAt_eq_done_of_runState hSourceOpen
  calc
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ [] ++ post) ([] : Assembly.Program).length state =
        .done
          (Assembly.Source.runNResult
            (pre ++ [] ++ post) ([] : Assembly.Program).length state) := rfl
    _ =
        .done
          ((TypedCfg.Instr.runAt instr shape state).map
            (fun result => Assembly.StepResult.running result.1)) := by
      rw [hPlain]
    _ =
        Simulation.Interaction.map
          (fun result => Assembly.StepResult.running result.1)
          (TypedCfg.InteractionSemantics.Instr.openRunAt
            instr shape state) := by
      rw [hSource]
      rw [interaction_map_done]

/--
A typed primitive and its one-instruction Assembly lowering expose exactly the
same open interaction. This theorem covers resource queries and all six
CALL/CREATE-family operations because both layers use the Assembly-owned
primitive step.
-/
theorem prim_lowerAt_openRunNResult_eq
    {op : Assembly.PrimOp} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower :
      (TypedCfg.Instr.prim op).lowerAt? shape =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          (.prim op) shape state) := by
  cases hType : TypedCfg.Instr.type? (.prim op) shape with
  | none =>
      simp [TypedCfg.Instr.lowerAt?, hType] at hLower
  | some typedOutput =>
      simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
        at hLower
      rcases hLower with ⟨rfl, rfl⟩
      have hNoHalt : op.haltKind? = none := by
        cases hArity : op.stackArity? with
        | none =>
            simp [TypedCfg.Instr.type?, hArity] at hType
        | some arity =>
            cases op <;>
              simp [Assembly.PrimOp.stackArity?,
                Assembly.PrimOp.haltKind?] at hArity ⊢
      simp only [List.length_cons, List.length_nil, Nat.zero_add,
        List.append_assoc]
      have hOne :=
        source_openRunNResult_one_at_boundary
          (pre := pre) (post := post)
          (instr := Assembly.Instr.prim op)
          hFits.1 hPc
      rw [show
        Assembly.InteractionSemantics.Source.openRunNResult
            (pre ++ ([Assembly.Instr.prim op] ++ post)) 1 state =
          Assembly.InteractionSemantics.Source.openStepAtResult
            (pre ++ Assembly.Instr.prim op :: post)
            pre.byteLength (.prim op) state by
        simpa using hOne]
      unfold
        Assembly.InteractionSemantics.Source.openStepAtResult
        Assembly.InteractionSemantics.Source.openStepAt
        TypedCfg.InteractionSemantics.Instr.openRunAt
        TypedCfg.Control.Instr.runAt
        TypedCfg.InteractionSemantics.Instr.openRunState
        Simulation.Interaction.map
      rw [hType]
      simp only [Assembly.Instr.haltKind?, hNoHalt]
      simp only [Option.elim_some]
      change
        Simulation.Interaction.bind
            (Assembly.InteractionSemantics.PrimOp.openStep op state)
            (fun state' =>
              Simulation.Interaction.pure
                (Assembly.StepResult.running state')) =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind
              (Simulation.Interaction.pure typedOutput)
              (fun output =>
                Simulation.Interaction.bind
                  (Assembly.InteractionSemantics.PrimOp.openStep op state)
                  (fun state' =>
                    Simulation.Interaction.pure (state', output))))
            (fun value =>
              Simulation.Interaction.pure
                (Assembly.StepResult.running value.1))
      simp only [Simulation.Interaction.pure,
        Simulation.Interaction.bind]
      rw [Simulation.Interaction.bind_assoc]
      rfl

/--
Every TypedCfg instruction preserves the complete open interaction tree of its
ordinary Assembly lowering.
-/
theorem lowerAt_openRunNResult_eq
    {instr : TypedCfg.Instr} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower : instr.lowerAt? shape = some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          instr shape state) := by
  cases hType : instr.type? shape with
  | none =>
      simp [TypedCfg.Instr.lowerAt?, hType] at hLower
  | some typedOutput =>
      cases instr with
      | prim op =>
          exact prim_lowerAt_openRunNResult_eq hLower hFits hPc
      | push value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          refine
            lowerAt_single_closed
              (instr := .push value)
              (output := typedOutput)
              (asmInstr := .push value)
              ?_ hFits hPc rfl rfl
          simp [TypedCfg.Instr.lowerAt?,
            TypedCfg.Instr.lower?, hType]
      | returnToken value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          refine
            lowerAt_single_closed
              (instr := .returnToken value)
              (output := typedOutput)
              (asmInstr := .push value)
              ?_ hFits hPc rfl rfl
          simp [TypedCfg.Instr.lowerAt?,
            TypedCfg.Instr.lower?, hType]
      | pop =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          refine
            lowerAt_single_closed
              (instr := .pop)
              (output := typedOutput)
              (asmInstr := .prim .pop)
              ?_ hFits hPc rfl ?_
          · simp [TypedCfg.Instr.lowerAt?,
              TypedCfg.Instr.lower?, hType]
          · exact
              source_openStepAt_prim_closed
                (by rfl) (by simp) (by simp)
      | bindLocals offset names =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          refine
            lowerAt_empty_closed
              (instr := .bindLocals offset names)
              (output := typedOutput)
              ?_ hFits hPc rfl
          simp [TypedCfg.Instr.lowerAt?,
            TypedCfg.Instr.lower?, hType]
      | bindScratch baseDepth name slot =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          refine
            lowerAt_empty_closed
              (instr := .bindScratch baseDepth name slot)
              (output := typedOutput)
              ?_ hFits hPc rfl
          simp [TypedCfg.Instr.lowerAt?,
            TypedCfg.Instr.lower?, hType]
      | relabel target =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          refine
            lowerAt_empty_closed
              (instr := .relabel target)
              (output := typedOutput)
              ?_ hFits hPc rfl
          simp [TypedCfg.Instr.lowerAt?,
            TypedCfg.Instr.lower?, hType]
      | dup depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            refine
              lowerAt_single_closed
                (shape := shape)
                (output := typedOutput)
                (pre := pre) (post := post) (state := state)
                ?_ hFits hPc rfl ?_
          all_goals
            first
            | exact source_openStepAt_prim_closed
                (by rfl) (by simp) (by simp)
            | simp [TypedCfg.Instr.lowerAt?,
                TypedCfg.Instr.lower?, hType]
      | swap depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            refine
              lowerAt_single_closed
                (shape := shape)
                (output := typedOutput)
                (pre := pre) (post := post) (state := state)
                ?_ hFits hPc rfl ?_
          all_goals
            first
            | exact source_openStepAt_prim_closed
                (by rfl) (by simp) (by simp)
            | simp [TypedCfg.Instr.lowerAt?,
                TypedCfg.Instr.lower?, hType]
      | unwind target =>
          have hPlain :=
            Preservation.Instr.lowerAt_source_runNResult
              (post := post) hLower hFits hPc
          simp [TypedCfg.Instr.lowerAt?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_replicate] at hPlain ⊢
          have hOrdinaryPops :=
            Preservation.runPops_source_runNResult
              (shape.length - target.length)
              (post := post) hFits hPc
          rw [runPops_source_openRunNResult
            (shape.length - target.length)
            (post := post) hFits hPc]
          rw [← hOrdinaryPops]
          rw [hPlain]
          rw [openRunAt_eq_done_of_runState (by rfl)]
          rw [interaction_map_done]

theorem call_lowerAt_openRunNResult_eq
    {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower :
      (TypedCfg.Instr.prim .call).lowerAt? shape =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          (.prim .call) shape state) :=
  prim_lowerAt_openRunNResult_eq hLower hFits hPc

theorem callcode_lowerAt_openRunNResult_eq
    {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower :
      (TypedCfg.Instr.prim .callcode).lowerAt? shape =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          (.prim .callcode) shape state) :=
  prim_lowerAt_openRunNResult_eq hLower hFits hPc

theorem delegatecall_lowerAt_openRunNResult_eq
    {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower :
      (TypedCfg.Instr.prim .delegatecall).lowerAt? shape =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          (.prim .delegatecall) shape state) :=
  prim_lowerAt_openRunNResult_eq hLower hFits hPc

theorem staticcall_lowerAt_openRunNResult_eq
    {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower :
      (TypedCfg.Instr.prim .staticcall).lowerAt? shape =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          (.prim .staticcall) shape state) :=
  prim_lowerAt_openRunNResult_eq hLower hFits hPc

theorem create_lowerAt_openRunNResult_eq
    {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower :
      (TypedCfg.Instr.prim .create).lowerAt? shape =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          (.prim .create) shape state) :=
  prim_lowerAt_openRunNResult_eq hLower hFits hPc

theorem create2_lowerAt_openRunNResult_eq
    {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower :
      (TypedCfg.Instr.prim .create2).lowerAt? shape =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Instr.openRunAt
          (.prim .create2) shape state) :=
  prim_lowerAt_openRunNResult_eq hLower hFits hPc

end Instr

namespace Terminator

/--
When no return token matches, every generated dispatch probe falls through.
The exact fuel is the generated test-list length; the policy keeps each
conditional edge inside the return-dispatch region.
-/
theorem returnDispatchTestCases_openRunUntilTransfer_of_all_ne
    {depth : Nat} {sites : List ReturnSite}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {state : EVMState}
    (fuel : Nat)
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hNe : ∀ site, site ∈ sites → site.token ≠ token)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchTestCases depth sites))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++
          TypedCfg.Terminator.returnDispatchTestCases depth sites ++ post)
        sites) :
    let code :=
      TypedCfg.Terminator.returnDispatchTestCases depth sites
    let final : EVMState :=
      { state with
        stack := front ++ token :: suffix
        pc := (pre ++ code).pcAfter }
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++ code ++ post) (fuel + code.length)
        { state with stack := front ++ token :: suffix } =
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++ code ++ post) fuel final := by
  dsimp only
  induction sites generalizing pre state fuel with
  | nil =>
      have hPc' : state.pc = pre.pcAfter := by
        simpa using hPc
      simp [TypedCfg.Terminator.returnDispatchTestCases, hPc']
  | cons site rest ih =>
      let headCode :=
        TypedCfg.Terminator.returnDispatchTest depth site
      let tailCode :=
        TypedCfg.Terminator.returnDispatchTestCases depth rest
      have hCodeEq :
          TypedCfg.Terminator.returnDispatchTestCases depth (site :: rest) =
            headCode ++ tailCode := by
        simp [TypedCfg.Terminator.returnDispatchTestCases,
          headCode, tailCode]
      have hFitsAppend :
          Assembly.Program.PCFitsFrom pre (headCode ++ tailCode) := by
        simpa [hCodeEq] using hFits
      have hHeadFits :
          Assembly.Program.PCFitsFrom pre headCode :=
        Assembly.Program.PCFitsFrom.left hFitsAppend
      have hTailFits :
          Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode :=
        Assembly.Program.PCFitsFrom.right hFitsAppend
      have hSiteNe : site.token ≠ token :=
        hNe site (by simp)
      rcases hResolved site (by simp) with ⟨dest, hDest⟩
      have hDest' :
          (pre ++ headCode ++ (tailCode ++ post)).labelPc
              site.caseLabel =
            some dest := by
        simpa [hCodeEq, List.append_assoc] using hDest
      have hHead :=
        Assembly.StackShuffle.InteractionPreservation.dispatchTest_openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (front := front) (suffix := suffix) (token := token)
            (probe := site.token) (label := site.caseLabel)
            (dest := dest) (pre := pre) (post := tailCode ++ post)
            (state := state) (fuel := fuel + tailCode.length)
            (by rfl)
            (by
              simpa [headCode,
                TypedCfg.Terminator.returnDispatchTest, hFront] using
                hHeadFits)
            hPc
            (by omega)
            (by
              simpa [headCode,
                TypedCfg.Terminator.returnDispatchTest, hFront,
                List.append_assoc] using hDest')
      let mid : EVMState :=
        { state with
          stack := front ++ token :: suffix
          pc := (pre ++ headCode).pcAfter }
      have hHead' :
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              (pre ++ headCode ++ tailCode ++ post)
              ((fuel + tailCode.length) + headCode.length)
              { state with stack := front ++ token :: suffix } =
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              (pre ++ headCode ++ tailCode ++ post)
              (fuel + tailCode.length) mid := by
        simpa [headCode, TypedCfg.Terminator.returnDispatchTest,
          hFront, hSiteNe, mid, List.append_assoc] using hHead
      rw [show
        fuel +
            (TypedCfg.Terminator.returnDispatchTestCases depth
              (site :: rest)).length =
          (fuel + tailCode.length) + headCode.length by
        simp [hCodeEq, headCode,
          TypedCfg.Terminator.returnDispatchTest]
        omega]
      rw [show
        pre ++
            TypedCfg.Terminator.returnDispatchTestCases depth
              (site :: rest) ++ post =
          pre ++ headCode ++ tailCode ++ post by
        rw [hCodeEq]
        simp [List.append_assoc]]
      rw [hHead']
      have hRestNe :
          ∀ restSite, restSite ∈ rest → restSite.token ≠ token := by
        intro restSite hMem
        exact hNe restSite (by simp [hMem])
      have hRestResolved :
          Preservation.Terminator.ResolvedCaseLabels
            ((pre ++ headCode) ++ tailCode ++ post) rest := by
        intro restSite hMem
        rcases hResolved restSite (by simp [hMem]) with
          ⟨restDest, hRestDest⟩
        exact
          ⟨restDest,
            by
              simpa [hCodeEq, List.append_assoc] using hRestDest⟩
      have hTail :=
        ih (pre := pre ++ headCode) (state := mid)
          (fuel := fuel)
          hRestNe hTailFits
          (by simp [mid])
          hRestResolved
      simpa [tailCode, mid, hCodeEq, List.append_assoc] using hTail

/--
A selected return token consumes the preceding failed probes and the matching
probe, then continues at the selected case label with all later-test fuel
untouched.
-/
theorem returnDispatchTestCases_openRunUntilTransfer_of_selected
    {depth : Nat} {before after : List ReturnSite} {site : ReturnSite}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {state : EVMState}
    (fuel : Nat)
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hBefore :
      ∀ prior, prior ∈ before → prior.token ≠ token)
    (hToken : site.token = token)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchTestCases depth
          (before ++ site :: after)))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++
          TypedCfg.Terminator.returnDispatchTestCases depth
            (before ++ site :: after) ++ post)
        (before ++ site :: after)) :
    let code :=
      TypedCfg.Terminator.returnDispatchTestCases depth
        (before ++ site :: after)
    let tailCode :=
      TypedCfg.Terminator.returnDispatchTestCases depth after
    ∃ caseDest,
      (pre ++ code ++ post).labelPc site.caseLabel = some caseDest ∧
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) (fuel + code.length)
          { state with stack := front ++ token :: suffix } =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) (fuel + tailCode.length)
          { state with
            stack := front ++ token :: suffix
            pc := EvmYul.UInt256.ofNat caseDest } := by
  dsimp only
  let prefixCode :=
    TypedCfg.Terminator.returnDispatchTestCases depth before
  let siteCode :=
    TypedCfg.Terminator.returnDispatchTest depth site
  let tailCode :=
    TypedCfg.Terminator.returnDispatchTestCases depth after
  let code :=
    TypedCfg.Terminator.returnDispatchTestCases depth
      (before ++ site :: after)
  have hCodeEq : code = prefixCode ++ siteCode ++ tailCode := by
    simp [code, prefixCode, siteCode, tailCode,
      TypedCfg.Terminator.returnDispatchTestCases,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ (siteCode ++ tailCode)) := by
    have hFits' :
        Assembly.Program.PCFitsFrom pre code := by
      simpa [code] using hFits
    rw [hCodeEq] at hFits'
    simpa [List.append_assoc] using hFits'
  have hPrefixFits :
      Assembly.Program.PCFitsFrom pre prefixCode :=
    Assembly.Program.PCFitsFrom.left hFitsAll
  have hAfterPrefixFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        (siteCode ++ tailCode) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hSiteFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode) siteCode :=
    Assembly.Program.PCFitsFrom.left hAfterPrefixFits
  rcases hResolved site (by simp) with ⟨caseDest, hCaseDest⟩
  have hPrefixResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ prefixCode ++ (siteCode ++ tailCode ++ post))
        before := by
    intro prior hMem
    rcases hResolved prior (by simp [hMem]) with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [code, hCodeEq, List.append_assoc] using hDest⟩
  let mid : EVMState :=
    { state with
      stack := front ++ token :: suffix
      pc := (pre ++ prefixCode).pcAfter }
  have hPrefix :=
    returnDispatchTestCases_openRunUntilTransfer_of_all_ne
      (depth := depth) (sites := before)
      (front := front) (suffix := suffix) (token := token)
      (pre := pre) (post := siteCode ++ tailCode ++ post)
      (state := state)
      ((fuel + tailCode.length) + siteCode.length)
      hBound hFront hBefore hPrefixFits hPc hPrefixResolved
  have hPrefix' :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post)
          (((fuel + tailCode.length) + siteCode.length) +
            prefixCode.length)
          { state with stack := front ++ token :: suffix } =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post)
          ((fuel + tailCode.length) + siteCode.length) mid := by
    simpa [code, hCodeEq, mid, List.append_assoc] using hPrefix
  have hCaseDest' :
      ((pre ++ prefixCode) ++ siteCode ++ (tailCode ++ post)).labelPc
          site.caseLabel =
        some caseDest := by
    simpa [code, hCodeEq, List.append_assoc] using hCaseDest
  have hSite :=
    Assembly.StackShuffle.InteractionPreservation.dispatchTest_openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (front := front) (suffix := suffix) (token := token)
        (probe := site.token) (label := site.caseLabel)
        (dest := caseDest) (pre := pre ++ prefixCode)
        (post := tailCode ++ post) (state := mid)
        (fuel := fuel + tailCode.length)
        (by rfl)
        (by
          simpa [siteCode, TypedCfg.Terminator.returnDispatchTest,
            hFront] using hSiteFits)
        (by simp [mid])
        (by omega)
        (by
          simpa [siteCode, TypedCfg.Terminator.returnDispatchTest,
            hFront, List.append_assoc] using hCaseDest')
  let selected : EVMState :=
    { state with
      stack := front ++ token :: suffix
      pc := EvmYul.UInt256.ofNat caseDest }
  have hSite' :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post)
          ((fuel + tailCode.length) + siteCode.length) mid =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post)
          (fuel + tailCode.length) selected := by
    simpa [code, hCodeEq, siteCode,
      TypedCfg.Terminator.returnDispatchTest, hFront, hToken,
      mid, selected, List.append_assoc] using hSite
  refine ⟨caseDest, ?_, ?_⟩
  · simpa [code] using hCaseDest
  · rw [show
      fuel + code.length =
        ((fuel + tailCode.length) + siteCode.length) +
          prefixCode.length by
      rw [hCodeEq]
      simp
      omega]
    exact hPrefix'.trans hSite'

/--
Starting at a selected generated case, return dispatch removes the buried
return token and exits at the source-visible target jump.
-/
theorem returnDispatchCase_openRunUntilTransfer
    {depth : Nat} {before after : List ReturnSite} {site : ReturnSite}
    {front suffix : List Word}
    {pre post : Assembly.Program} {state : EVMState}
    (fuel : Nat)
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after)))
    (hPc :
      ({ state with stack := front ++ site.token :: suffix }).pc =
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth before).pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedTargets
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        (.returnDispatch depth (before ++ site :: after))) :
    ∃ targetDest,
      (pre ++
        TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after) ++ post).labelPc site.target =
        some targetDest ∧
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCases depth
              (before ++ site :: after) ++ post)
          (fuel +
            (TypedCfg.Terminator.returnDispatchCase depth site).length)
          { state with stack := front ++ site.token :: suffix } =
        .done
          (.ok
            (.running
              (Assembly.Source.jumpPc targetDest
                { state with stack := front ++ suffix }))) := by
  let prefixCode :=
    TypedCfg.Terminator.returnDispatchCases depth before
  let siteCode :=
    TypedCfg.Terminator.returnDispatchCase depth site
  let tailCode :=
    TypedCfg.Terminator.returnDispatchCases depth after
  let cleanup :=
    Assembly.StackShuffle.removeBuriedUnder depth
  let start : EVMState :=
    { state with stack := front ++ site.token :: suffix }
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after) =
        prefixCode ++ siteCode ++ tailCode := by
    simp [prefixCode, siteCode, tailCode,
      TypedCfg.Terminator.returnDispatchCases,
      List.append_assoc]
  have hSiteCodeEq :
      siteCode =
        [Assembly.Instr.label site.caseLabel] ++ cleanup ++
          [Assembly.Instr.jump site.target] := by
    simp [siteCode, cleanup, TypedCfg.Terminator.returnDispatchCase,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ (siteCode ++ tailCode)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hAfterPrefixFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        (siteCode ++ tailCode) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hSiteFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode) siteCode :=
    Assembly.Program.PCFitsFrom.left hAfterPrefixFits
  have hSiteFits' :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        ([Assembly.Instr.label site.caseLabel] ++ cleanup ++
          [Assembly.Instr.jump site.target]) := by
    simpa [hSiteCodeEq] using hSiteFits
  have hLabelFit : (pre ++ prefixCode).PCFits :=
    Assembly.Program.PCFitsFrom.start hSiteFits'
  have hAfterLabelFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        (cleanup ++ [Assembly.Instr.jump site.target]) := by
    simpa [List.append_assoc] using hSiteFits'.2
  have hCleanupFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        cleanup :=
    Assembly.Program.PCFitsFrom.left hAfterLabelFits
  have hJumpFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel] ++
          cleanup)
        [Assembly.Instr.jump site.target] := by
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right hAfterLabelFits)
  rcases hResolved site.target
      (by simp [TypedCfg.Terminator.targets]) with
    ⟨targetDest, hTargetDest⟩
  let afterLabel : EVMState := start.incrPC
  have hAfterLabelPc :
      afterLabel.pc =
        (pre ++ prefixCode ++
          [Assembly.Instr.label site.caseLabel]).pcAfter := by
    calc
      afterLabel.pc = start.pc + EvmYul.UInt256.ofNat 1 := by
        simp [afterLabel, EvmYul.EVM.State.incrPC]
      _ = (pre ++ prefixCode).pcAfter +
          EvmYul.UInt256.ofNat 1 := by
        rw [show start.pc = (pre ++ prefixCode).pcAfter by
          simpa [start, prefixCode] using hPc]
      _ =
          EvmYul.UInt256.ofNat
            ((pre ++ prefixCode).byteLength + 1) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ =
          (pre ++ prefixCode ++
            [Assembly.Instr.label site.caseLabel]).pcAfter := by
        simp [Assembly.Program.pcAfter,
          Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, Assembly.Instr.byteSize,
          Nat.add_assoc]
  have hLabelOpen :
      Assembly.InteractionSemantics.Source.openStepAtResult
          ((pre ++ prefixCode) ++
            Assembly.Instr.label site.caseLabel ::
              (cleanup ++
                Assembly.Instr.jump site.target :: tailCode ++ post))
          (pre ++ prefixCode).byteLength
          (.label site.caseLabel) start =
        .done (.ok (.running afterLabel)) := by
    rw [source_openStepAtResult_eq_done_of_stepAt (by rfl)]
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      Assembly.Instr.haltKind?, Assembly.Target.stepInstr,
      afterLabel]
  have hLabelFlow :
      (Assembly.Instr.label site.caseLabel).classifyFlowWith
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          start (.running afterLabel) =
        .next afterLabel := by
    rfl
  have hLabelRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCases depth
              (before ++ site :: after) ++ post)
          (((fuel + 1) + cleanup.length) + 1) start =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCases depth
              (before ++ site :: after) ++ post)
          ((fuel + 1) + cleanup.length) afterLabel := by
    have hRun :=
      source_openRunUntilTransferWithPolicy_succ_of_step_running
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        ((fuel + 1) + cleanup.length)
        hLabelFit
        (by simpa [start, prefixCode] using hPc)
        hLabelOpen hLabelFlow
    simpa [hCodeEq, hSiteCodeEq, List.append_assoc] using hRun
  let cleaned : EVMState :=
    { afterLabel with
      stack := front ++ suffix
      pc :=
        (pre ++ prefixCode ++
          [Assembly.Instr.label site.caseLabel] ++ cleanup).pcAfter }
  have hCleanup :=
    Assembly.StackShuffle.InteractionPreservation.removeBuriedUnder_openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (front := front) (suffix := suffix) (token := site.token)
        (pre :=
          pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        (post := [Assembly.Instr.jump site.target] ++ tailCode ++ post)
        (state := afterLabel) (fuel := fuel + 1)
        (by simpa [cleanup, hFront] using hCleanupFits)
        (by simpa [hFront] using hAfterLabelPc)
        (by omega)
  have hCleanupRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCases depth
              (before ++ site :: after) ++ post)
          ((fuel + 1) + cleanup.length) afterLabel =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCases depth
              (before ++ site :: after) ++ post)
          (fuel + 1) cleaned := by
    simpa [hCodeEq, hSiteCodeEq, cleanup, cleaned, hFront,
      List.append_assoc] using hCleanup
  have hTargetDest' :
      ((pre ++ prefixCode ++
          [Assembly.Instr.label site.caseLabel] ++ cleanup) ++
        Assembly.Instr.jump site.target :: tailCode ++ post).labelPc
          site.target =
        some targetDest := by
    simpa [hCodeEq, hSiteCodeEq, List.append_assoc] using hTargetDest
  let jumpPre :=
    pre ++ prefixCode ++
      [Assembly.Instr.label site.caseLabel] ++ cleanup
  have hTargetDestActual :
      (jumpPre ++
        Assembly.Instr.jump site.target :: (tailCode ++ post)).labelPc
          site.target =
        some targetDest := by
    simpa [jumpPre, List.append_assoc] using hTargetDest'
  have hJumpOpen :
      Assembly.InteractionSemantics.Source.openStepAtResult
          (jumpPre ++
            Assembly.Instr.jump site.target :: (tailCode ++ post))
          jumpPre.byteLength
          (.jump site.target) cleaned =
        .done
          (.ok
            (.running
              (Assembly.Source.jumpPc targetDest cleaned))) := by
    rw [source_openStepAtResult_eq_done_of_stepAt (by rfl)]
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      Assembly.Instr.haltKind?, hTargetDestActual,
      Assembly.Source.invalid]
  have hJumpFlow :
      (Assembly.Instr.jump site.target).classifyFlowWith
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          cleaned
          (.running (Assembly.Source.jumpPc targetDest cleaned)) =
        .exit (.running (Assembly.Source.jumpPc targetDest cleaned)) := by
    rfl
  have hJumpRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCases depth
              (before ++ site :: after) ++ post)
          (fuel + 1) cleaned =
        .done
          (.ok
            (.running
              (Assembly.Source.jumpPc targetDest cleaned))) := by
    have hRun :=
      source_openRunUntilTransferWithPolicy_succ_of_step_exit
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre := jumpPre) (post := tailCode ++ post)
        (instr := Assembly.Instr.jump site.target)
        (state := cleaned)
        (result :=
          .running (Assembly.Source.jumpPc targetDest cleaned))
        fuel
        (Assembly.Program.PCFitsFrom.start hJumpFits)
        (by simp [jumpPre, cleaned])
        hJumpOpen hJumpFlow
    simpa [jumpPre, hCodeEq, hSiteCodeEq, List.append_assoc] using hRun
  have hFinal :
      Assembly.Source.jumpPc targetDest cleaned =
        Assembly.Source.jumpPc targetDest
          { state with stack := front ++ suffix } := by
    simp [Assembly.Source.jumpPc, cleaned, afterLabel, start,
      EvmYul.EVM.State.incrPC]
  refine ⟨targetDest, hTargetDest, ?_⟩
  change
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        (fuel + siteCode.length) start =
      _
  rw [show
    fuel + siteCode.length =
      (((fuel + 1) + cleanup.length) + 1) by
    simp [hSiteCodeEq]
    omega]
  rw [hLabelRun, hCleanupRun, hJumpRun, hFinal]

/--
When return dispatch finds a token, the generated Assembly region consumes the
same token and exits at the same source-visible target.
-/
theorem returnDispatch_selected_openRunUntilTransfer_rel
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word} {target : Label}
    {code pre post : Assembly.Program} {state : EVMState}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = some token)
    (hFind : TypedCfg.Block.ReturnSite.findTarget? token sites =
      some target)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolvedTargets :
      Preservation.Terminator.ResolvedTargets
        (pre ++ code ++ post)
        (.returnDispatch returnCount sites))
    (hResolvedCases :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ code ++ post) sites)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Simulation.Interaction.Rel
      (Preservation.Block.RunSimulates (pre ++ code ++ post))
      (.done
        (.ok
          (TypedCfg.Block.runTerm shape
            (.returnDispatch returnCount sites) state)))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) code.length state) := by
  subst code
  subst returnCount
  rcases Preservation.List.getElem?_eq_some_split hGet with
    ⟨front, suffix, hStack, hFront⟩
  rcases Preservation.ReturnSite.findTarget?_eq_some_split hFind with
    ⟨before, site, after, hSites, hBefore, hToken, hTarget⟩
  subst sites
  let testCases :=
    TypedCfg.Terminator.returnDispatchTestCases depth
      (before ++ site :: after)
  let tailTests :=
    TypedCfg.Terminator.returnDispatchTestCases depth after
  let cases :=
    TypedCfg.Terminator.returnDispatchCases depth
      (before ++ site :: after)
  let casePrefix :=
    TypedCfg.Terminator.returnDispatchCases depth before
  let siteCase :=
    TypedCfg.Terminator.returnDispatchCase depth site
  let caseTail :=
    TypedCfg.Terminator.returnDispatchCases depth after
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCode depth
          (before ++ site :: after) =
        testCases ++ [Assembly.Instr.prim .invalid] ++ cases := by
    simp [TypedCfg.Terminator.returnDispatchCode,
      TypedCfg.Terminator.returnDispatchTests,
      testCases, cases, List.append_assoc]
  have hCasesEq :
      cases = casePrefix ++ siteCase ++ caseTail := by
    simp [cases, casePrefix, siteCase, caseTail,
      TypedCfg.Terminator.returnDispatchCases,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (testCases ++ ([Assembly.Instr.prim .invalid] ++ cases)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hTestCasesFits :
      Assembly.Program.PCFitsFrom pre testCases :=
    Assembly.Program.PCFitsFrom.left hFitsAll
  have hAfterTestsFits :
      Assembly.Program.PCFitsFrom (pre ++ testCases)
        ([Assembly.Instr.prim .invalid] ++ cases) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  let caseBase :=
    pre ++ testCases ++ [Assembly.Instr.prim .invalid]
  have hCasesFits :
      Assembly.Program.PCFitsFrom caseBase cases := by
    simpa [caseBase, List.append_assoc] using hAfterTestsFits.2
  have hResolvedCases' :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ testCases ++
          ([Assembly.Instr.prim .invalid] ++ cases ++ post))
        (before ++ site :: after) := by
    intro resolvedSite hMem
    rcases hResolvedCases resolvedSite hMem with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hStart :
      { state with stack := front ++ token :: suffix } = state := by
    rw [← hStack]
  have hSelected :=
    returnDispatchTestCases_openRunUntilTransfer_of_selected
      (depth := depth) (before := before) (after := after)
      (site := site) (front := front) (suffix := suffix)
      (token := token) (pre := pre)
      (post := [Assembly.Instr.prim .invalid] ++ cases ++ post)
      (state := state) (fuel := 1 + cases.length)
      hBound hFront hBefore hToken hTestCasesFits
      (by simpa [hStart] using hPc)
      (by simpa [testCases, List.append_assoc] using hResolvedCases')
  rcases hSelected with ⟨caseDest, hCaseDest, hSelectedRun⟩
  let selected : EVMState :=
    { state with
      stack := front ++ token :: suffix
      pc := EvmYul.UInt256.ofNat caseDest }
  have hSelectedRun' :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCode depth
              (before ++ site :: after) ++ post)
          (TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after)).length
          state =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCode depth
              (before ++ site :: after) ++ post)
          ((1 + cases.length) + tailTests.length)
          selected := by
    rw [show
      (TypedCfg.Terminator.returnDispatchCode depth
        (before ++ site :: after)).length =
        (1 + cases.length) + testCases.length by
      rw [hCodeEq]
      simp
      omega]
    simpa [hCodeEq, testCases, tailTests, selected,
      hStart, List.append_assoc] using hSelectedRun
  have hProgramAtCase :
      pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post =
        (caseBase ++ casePrefix) ++
          Assembly.Instr.label site.caseLabel ::
            (Assembly.StackShuffle.removeBuriedUnder depth ++
              Assembly.Instr.jump site.target :: caseTail ++ post) := by
    simp [hCodeEq, testCases, cases, hCasesEq, caseBase,
      casePrefix, siteCase, caseTail,
      TypedCfg.Terminator.returnDispatchCase,
      List.append_assoc]
  have hInternalLabel :
      (pre ++
        TypedCfg.Terminator.returnDispatchCode depth
          (before ++ site :: after) ++ post).labelPc site.caseLabel =
        some (caseBase ++ casePrefix).byteLength := by
    rw [hProgramAtCase]
    exact
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        (caseBase ++ casePrefix)
        (Assembly.StackShuffle.removeBuriedUnder depth ++
          Assembly.Instr.jump site.target :: caseTail ++ post)
        (by simpa [hProgramAtCase] using hLabels)
  have hCaseDestEq :
      caseDest = (caseBase ++ casePrefix).byteLength := by
    have hCaseDest' :
        (pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post).labelPc site.caseLabel =
          some caseDest := by
      simpa [hCodeEq, testCases, cases,
        List.append_assoc] using hCaseDest
    rw [hInternalLabel] at hCaseDest'
    exact (Option.some.inj hCaseDest').symm
  have hResolvedTargets' :
      Preservation.Terminator.ResolvedTargets
        (caseBase ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        (.returnDispatch depth (before ++ site :: after)) := by
    intro resolvedTarget hMem
    rcases hResolvedTargets resolvedTarget
        (by
          simpa [TypedCfg.Terminator.targets] using hMem) with
      ⟨dest, hDest⟩
    exact
      ⟨dest,
        by
          simpa [hCodeEq, testCases, cases, caseBase,
            List.append_assoc] using hDest⟩
  let extraFuel :=
    tailTests.length + 1 + casePrefix.length + caseTail.length
  have hCaseRun :=
    returnDispatchCase_openRunUntilTransfer
      (depth := depth) (before := before) (after := after)
      (site := site) (front := front) (suffix := suffix)
      (pre := caseBase) (post := post) (state := selected)
      (fuel := extraFuel)
      hBound hFront hCasesFits
      (by
        simp [selected, hToken, hCaseDestEq, casePrefix,
          Assembly.Program.pcAfter])
      hResolvedTargets'
  rcases hCaseRun with ⟨targetDest, hTargetDest, hCaseRun⟩
  have hTargetDest' :
      (pre ++
        TypedCfg.Terminator.returnDispatchCode depth
          (before ++ site :: after) ++ post).labelPc target =
        some targetDest := by
    simpa [hTarget, hCodeEq, testCases, cases, caseBase,
      List.append_assoc] using hTargetDest
  have hRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCode depth
              (before ++ site :: after) ++ post)
          (TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after)).length state =
        .done
          (.ok
            (.running
              (Assembly.Source.jumpPc targetDest
                { selected with stack := front ++ suffix }))) := by
    rw [hSelectedRun']
    rw [show
      (1 + cases.length) + tailTests.length =
        extraFuel + siteCase.length by
      rw [hCasesEq]
      simp [extraFuel]
      omega]
    rw [show
      pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post =
        caseBase ++ cases ++ post by
      simp [hCodeEq, caseBase, List.append_assoc]]
    simpa [cases, siteCase, selected, hToken] using hCaseRun
  rw [hRun]
  apply Simulation.Interaction.Rel.done
  simp [Preservation.Block.RunSimulates,
    TypedCfg.Block.runTerm, hDepth, hGet, hFind,
    Preservation.Outcome.Simulates]
  have hTargetDestActual :
      (pre ++
        (TypedCfg.Terminator.returnDispatchCode depth
          (before ++ site :: after) ++ post)).labelPc target =
        some targetDest := by
    simpa [List.append_assoc] using hTargetDest'
  refine ⟨targetDest, hTargetDestActual, rfl, ?_⟩
  have hErase :
      state.stack.eraseIdx depth = front ++ suffix := by
    rw [hStack, ← hFront]
    exact
      Preservation.List.eraseIdx_append_at_length
        front suffix token
  simp [Assembly.SameRuntimeData, Assembly.eraseRuntimeControl,
    Assembly.Source.jumpPc, selected, hErase]

/--
When no return token matches, every generated probe falls through and the
generated `INVALID` refines TypedCfg's invalid outcome.
-/
theorem returnDispatch_unknown_token_openRunUntilTransfer_rel
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word}
    {code pre post : Assembly.Program} {state : EVMState}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = some token)
    (hFind : TypedCfg.Block.ReturnSite.findTarget? token sites = none)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolvedCases :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ code ++ post) sites) :
    Simulation.Interaction.Rel
      (Preservation.Block.RunSimulates (pre ++ code ++ post))
      (.done
        (.ok
          (TypedCfg.Block.runTerm shape
            (.returnDispatch returnCount sites) state)))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++ code ++ post) code.length state) := by
  subst code
  subst returnCount
  rcases Preservation.List.getElem?_eq_some_split hGet with
    ⟨front, suffix, hStack, hFront⟩
  let testCases :=
    TypedCfg.Terminator.returnDispatchTestCases depth sites
  let cases :=
    TypedCfg.Terminator.returnDispatchCases depth sites
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCode depth sites =
        testCases ++ [Assembly.Instr.prim .invalid] ++ cases := by
    simp [TypedCfg.Terminator.returnDispatchCode,
      TypedCfg.Terminator.returnDispatchTests,
      testCases, cases, List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (testCases ++ ([Assembly.Instr.prim .invalid] ++ cases)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hTestCasesFits :
      Assembly.Program.PCFitsFrom pre testCases :=
    Assembly.Program.PCFitsFrom.left hFitsAll
  have hAfterTestsFits :
      Assembly.Program.PCFitsFrom (pre ++ testCases)
        ([Assembly.Instr.prim .invalid] ++ cases) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hResolvedCases' :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ testCases ++
          ([Assembly.Instr.prim .invalid] ++ cases ++ post))
        sites := by
    intro site hMem
    rcases hResolvedCases site hMem with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hStart :
      { state with stack := front ++ token :: suffix } = state := by
    rw [← hStack]
  have hTests :=
    returnDispatchTestCases_openRunUntilTransfer_of_all_ne
      (depth := depth) (sites := sites)
      (front := front) (suffix := suffix) (token := token)
      (pre := pre)
      (post := [Assembly.Instr.prim .invalid] ++ cases ++ post)
      (state := state) (fuel := 1 + cases.length)
      hBound hFront
      (Preservation.ReturnSite.findTarget?_eq_none_all_ne hFind)
      hTestCasesFits
      (by simpa [hStart] using hPc)
      hResolvedCases'
  let tested : EVMState :=
    { state with
      stack := front ++ token :: suffix
      pc := (pre ++ testCases).pcAfter }
  have hTestsRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCode depth sites ++ post)
          (TypedCfg.Terminator.returnDispatchCode depth sites).length
          state =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCode depth sites ++ post)
          (1 + cases.length) tested := by
    rw [show
      (TypedCfg.Terminator.returnDispatchCode depth sites).length =
        (1 + cases.length) + testCases.length by
      rw [hCodeEq]
      simp
      omega]
    simpa [hCodeEq, testCases, tested, hStart,
      List.append_assoc] using hTests
  have hInvalidOpen :
      Assembly.InteractionSemantics.Source.openStepAtResult
          ((pre ++ testCases) ++
            Assembly.Instr.prim .invalid :: (cases ++ post))
          (pre ++ testCases).byteLength
          (.prim .invalid) tested =
        .done (.error .InvalidInstruction) := by
    rw [source_openStepAtResult_eq_done_of_stepAt
      (source_openStepAt_prim_closed
        (by rfl) (by decide) (by decide))]
    rfl
  have hInvalidRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            TypedCfg.Terminator.returnDispatchCode depth sites ++ post)
          (1 + cases.length) tested =
        .done (.error .InvalidInstruction) := by
    have hRun :=
      source_openRunUntilTransferWithPolicy_succ_of_step_error
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre := pre ++ testCases) (post := cases ++ post)
        (instr := Assembly.Instr.prim .invalid)
        (state := tested) (err := .InvalidInstruction)
        cases.length
        (Assembly.Program.PCFitsFrom.start hAfterTestsFits)
        (by simp [tested])
        hInvalidOpen
    simpa [hCodeEq, Nat.add_comm, List.append_assoc] using hRun
  rw [hTestsRun, hInvalidRun]
  apply Simulation.Interaction.Rel.done
  simp [Preservation.Block.RunSimulates,
    TypedCfg.Block.runTerm, hDepth, hGet, hFind,
    Preservation.Outcome.Simulates]

/--
When the return token is missing, the first generated `DUP` fails with stack
underflow and refines TypedCfg's invalid outcome.
-/
theorem returnDispatch_missing_token_openRunUntilTransfer_rel
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite}
    {code pre post : Assembly.Program} {state : EVMState}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hSites : sites ≠ [])
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = none)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Simulation.Interaction.Rel
      (Preservation.Block.RunSimulates (pre ++ code ++ post))
      (.done
        (.ok
          (TypedCfg.Block.runTerm shape
            (.returnDispatch returnCount sites) state)))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++ code ++ post) code.length state) := by
  subst code
  subst returnCount
  cases sites with
  | nil =>
      exact (hSites rfl).elim
  | cons site rest =>
      let duplicate :=
        Assembly.StackShuffle.dupInstr (depth + 1)
      let restCode : Assembly.Program :=
        [ Assembly.Instr.push site.token
        , Assembly.Instr.prim .eq
        , Assembly.Instr.jumpi site.caseLabel
        ] ++
          TypedCfg.Terminator.returnDispatchTestCases depth rest ++
          [Assembly.Instr.prim .invalid] ++
          TypedCfg.Terminator.returnDispatchCases depth (site :: rest)
      have hCodeHead :
          TypedCfg.Terminator.returnDispatchCode depth (site :: rest) =
            duplicate :: restCode := by
        simp [duplicate, restCode,
          TypedCfg.Terminator.returnDispatchCode,
          TypedCfg.Terminator.returnDispatchTests,
          TypedCfg.Terminator.returnDispatchTestCases,
          TypedCfg.Terminator.returnDispatchTest,
          List.append_assoc]
      have hFitsHead :
          Assembly.Program.PCFitsFrom pre (duplicate :: restCode) := by
        simpa [hCodeHead] using hFits
      have hLen : state.stack.length ≤ depth := by
        rw [List.getElem?_eq_none_iff] at hGet
        exact hGet
      have hDupError :
          Assembly.Target.stepInstr
              (Assembly.StackShuffle.targetInstr duplicate)
              state =
            .error .StackUnderflow := by
        rw [show
          duplicate =
            Assembly.StackShuffle.dupInstr (depth + 1) from rfl]
        rw [Assembly.StackShuffle.dupInstr_step_eq_dup
          (by omega) (by omega)]
        simp [EvmYul.dup,
          show ¬depth + 1 ≤ state.stack.length by omega]
      have hDupOpen :
          Assembly.InteractionSemantics.Source.openStepAtResult
              (pre ++ duplicate :: (restCode ++ post))
              pre.byteLength duplicate state =
            .done (.error .StackUnderflow) := by
        rw [source_openStepAtResult_eq_done_of_stepAt
          (Assembly.StackShuffle.InteractionPreservation.openStepAt_dupInstr_eq_done
              (n := depth + 1) (by omega) (by omega))]
        simp [Assembly.Source.stepAtResult,
          Assembly.StackShuffle.source_stepAt_eq_targetInstr
            (Assembly.StackShuffle.dupInstr_sourceLocal
              (n := depth + 1) (by omega) (by omega)),
          duplicate, hDupError]
      have hRunBase :=
        source_openRunUntilTransferWithPolicy_succ_of_step_error
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre := pre) (post := restCode ++ post)
          (instr := duplicate) (state := state)
          (err := .StackUnderflow)
          restCode.length hFitsHead.1 hPc hDupOpen
      have hRun :
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              (pre ++
                TypedCfg.Terminator.returnDispatchCode depth
                  (site :: rest) ++ post)
              (TypedCfg.Terminator.returnDispatchCode depth
                (site :: rest)).length state =
            .done (.error .StackUnderflow) := by
        rw [hCodeHead]
        simpa [List.append_assoc] using hRunBase
      rw [hRun]
      apply Simulation.Interaction.Rel.done
      simp [Preservation.Block.RunSimulates,
        TypedCfg.Block.runTerm, hDepth, hGet,
        Preservation.Outcome.Simulates]

/--
Direct TypedCfg terminators are related to the Assembly-owned runner that
stops at the first taken control transfer or halt.
-/
theorem lowerAt?_openRunUntilTransfer_rel_of_direct
    {shape : Shape} {term : TypedCfg.Terminator}
    {code pre post : Assembly.Program} {state : EVMState}
    (hDirect : Preservation.Terminator.Direct term)
    (hLower : term.lowerAt? shape = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedTargets
        (pre ++ code ++ post) term) :
    Simulation.Interaction.Rel
      (Preservation.Block.RunSimulates
        (pre ++ code ++ post))
      (.done (TypedCfg.Block.runTermChecked shape term state))
      (Assembly.InteractionSemantics.Source.openRunUntilTransfer
        (pre ++ code ++ post) code.length state) := by
  cases term with
  | fallthrough next =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved next
          (by simp [TypedCfg.Terminator.targets]) with
        ⟨dest, hDest⟩
      have hDest' :
          (pre ++ Assembly.Instr.jump next :: post).labelPc next =
            some dest := by
        simpa using hDest
      have hRun :
          Assembly.InteractionSemantics.Source.openRunUntilTransfer
              (pre ++ [Assembly.Instr.jump next] ++ post)
              1 state =
            .done
              (.ok
                (.running
                  (Assembly.Source.jumpPc dest state))) := by
        rw [show
          pre ++ [Assembly.Instr.jump next] ++ post =
            pre ++ Assembly.Instr.jump next :: post by simp]
        rw [source_openRunUntilTransfer_one_at_boundary
          hFits.1 hPc]
        simp [Assembly.InteractionSemantics.Source.openStepAtResult,
          Assembly.InteractionSemantics.Source.openStepAt,
          Assembly.Source.stepAt,
          Assembly.Instr.haltKind?,
          Assembly.Instr.classifyFlow,
          Assembly.Instr.classifyFlowWith,
          Assembly.FlowStep.result,
          hDest', Assembly.Source.invalid,
          Simulation.Interaction.bind_done_ok,
          Simulation.Interaction.bind_done_error]
        rfl
      rw [show
        ([Assembly.Instr.jump next] : Assembly.Program).length = 1 by
          rfl]
      rw [hRun]
      apply Simulation.Interaction.Rel.done
      exact
        ⟨dest, hDest, rfl,
          Assembly.SameRuntimeData.jumpPc dest state⟩
  | jump target =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved target
          (by simp [TypedCfg.Terminator.targets]) with
        ⟨dest, hDest⟩
      have hDest' :
          (pre ++ Assembly.Instr.jump target :: post).labelPc target =
            some dest := by
        simpa using hDest
      have hRun :
          Assembly.InteractionSemantics.Source.openRunUntilTransfer
              (pre ++ [Assembly.Instr.jump target] ++ post)
              1 state =
            .done
              (.ok
                (.running
                  (Assembly.Source.jumpPc dest state))) := by
        rw [show
          pre ++ [Assembly.Instr.jump target] ++ post =
            pre ++ Assembly.Instr.jump target :: post by simp]
        rw [source_openRunUntilTransfer_one_at_boundary
          hFits.1 hPc]
        simp [Assembly.InteractionSemantics.Source.openStepAtResult,
          Assembly.InteractionSemantics.Source.openStepAt,
          Assembly.Source.stepAt,
          Assembly.Instr.haltKind?,
          Assembly.Instr.classifyFlow,
          Assembly.Instr.classifyFlowWith,
          Assembly.FlowStep.result,
          hDest', Assembly.Source.invalid,
          Simulation.Interaction.bind_done_ok,
          Simulation.Interaction.bind_done_error]
        rfl
      rw [show
        ([Assembly.Instr.jump target] : Assembly.Program).length = 1 by
          rfl]
      rw [hRun]
      apply Simulation.Interaction.Rel.done
      exact
        ⟨dest, hDest, rfl,
          Assembly.SameRuntimeData.jumpPc dest state⟩
  | jumpi target next =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved target
          (by simp [TypedCfg.Terminator.targets]) with
        ⟨targetDest, hTargetDest⟩
      rcases hResolved next
          (by simp [TypedCfg.Terminator.targets]) with
        ⟨nextDest, hNextDest⟩
      have hTargetDest' :
          (pre ++ Assembly.Instr.jumpi target ::
              Assembly.Instr.jump next :: post).labelPc target =
            some targetDest := by
        simpa using hTargetDest
      have hNextDest' :
          (pre ++ Assembly.Instr.jumpi target ::
              Assembly.Instr.jump next :: post).labelPc next =
            some nextDest := by
        simpa using hNextDest
      cases hPop : state.stack.pop with
      | none =>
          have hRun :
              Assembly.InteractionSemantics.Source.openRunUntilTransfer
                  (pre ++
                    [Assembly.Instr.jumpi target,
                      Assembly.Instr.jump next] ++ post)
                  2 state =
                .done (.error .StackUnderflow) := by
            rw [show
              pre ++
                    [Assembly.Instr.jumpi target,
                      Assembly.Instr.jump next] ++ post =
                  pre ++ Assembly.Instr.jumpi target ::
                    Assembly.Instr.jump next :: post by simp]
            rw [show 2 = 1 + 1 by omega]
            rw [source_openRunUntilTransfer_succ_at_boundary
              1 hFits.1 hPc]
            simp [Assembly.InteractionSemantics.Source.openStepAtResult,
              Assembly.InteractionSemantics.Source.openStepAt,
              Assembly.Source.stepAt,
              Assembly.Instr.haltKind?,
              Assembly.Instr.classifyFlow,
              Assembly.Instr.classifyFlowWith,
              Assembly.FlowStep.result,
              hTargetDest', hPop,
              Assembly.Source.invalid,
              Simulation.Interaction.bind_done_ok,
              Simulation.Interaction.bind_done_error]
            rfl
          rw [show
            ([Assembly.Instr.jumpi target,
              Assembly.Instr.jump next] :
                Assembly.Program).length = 2 by rfl]
          rw [hRun]
          apply Simulation.Interaction.Rel.done
          simp [Preservation.Block.RunSimulates,
            TypedCfg.Block.runTerm, hPop,
            Preservation.Outcome.Simulates]
      | some popResult =>
          rcases popResult with ⟨stack, cond⟩
          let popped : EVMState := { state with stack := stack }
          by_cases hZero : cond = EvmYul.UInt256.ofNat 0
          · subst cond
            let mid : EVMState :=
              { popped with
                pc := Assembly.Source.jumpiFallthroughPc state }
            have hMidPc :
                mid.pc =
                  (pre ++ [Assembly.Instr.jumpi target]).pcAfter := by
              calc
                mid.pc =
                    (state.pc +
                      EvmYul.UInt256.ofNat
                        Assembly.Instr.push32Size) +
                      EvmYul.UInt256.ofNat 1 := rfl
                _ =
                    (pre.pcAfter +
                      EvmYul.UInt256.ofNat
                        Assembly.Instr.push32Size) +
                      EvmYul.UInt256.ofNat 1 := by
                  rw [hPc]
                _ =
                    pre.pcAfter +
                      (EvmYul.UInt256.ofNat
                        Assembly.Instr.push32Size +
                        EvmYul.UInt256.ofNat 1) := by
                  exact Preservation.uint256_add_assoc _ _ _
                _ =
                    pre.pcAfter +
                      EvmYul.UInt256.ofNat
                        (Assembly.Instr.push32Size + 1) := by
                  rw [Assembly.UInt256_ofNat_add]
                _ =
                    (pre ++
                      [Assembly.Instr.jumpi target]).pcAfter := by
                  simpa [Assembly.Instr.byteSize,
                    Assembly.Instr.jumpSize] using
                    (Assembly.Program.pcAfter_snoc pre
                      (Assembly.Instr.jumpi target)).symm
            have hRun :
                Assembly.InteractionSemantics.Source.openRunUntilTransfer
                    (pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++ post)
                    2 state =
                  .done
                    (.ok
                      (.running
                        (Assembly.Source.jumpPc nextDest popped))) := by
              rw [show
                pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++ post =
                    pre ++ Assembly.Instr.jumpi target ::
                      Assembly.Instr.jump next :: post by simp]
              rw [show 2 = 1 + 1 by omega]
              rw [source_openRunUntilTransfer_succ_at_boundary
                1 hFits.1 hPc]
              simp only [
                Assembly.InteractionSemantics.Source.openStepAtResult,
                Assembly.InteractionSemantics.Source.openStepAt,
                Assembly.Instr.haltKind?,
                Assembly.Instr.classifyFlow,
                Assembly.Instr.classifyFlowWith]
              simp [Assembly.Source.stepAt,
                hTargetDest', hPop,
                Assembly.Source.invalid, mid, popped,
                Preservation.uint256_bne_zero_self,
                Simulation.Interaction.bind_done_ok,
                Simulation.Interaction.bind_done_error]
              change
                Assembly.InteractionSemantics.Source.openRunUntilTransfer
                    (pre ++ Assembly.Instr.jumpi target ::
                      Assembly.Instr.jump next :: post)
                    1 mid =
                  .done
                    (.ok
                      (.running
                        (Assembly.Source.jumpPc nextDest popped)))
              rw [show
                pre ++ Assembly.Instr.jumpi target ::
                    Assembly.Instr.jump next :: post =
                  (pre ++ [Assembly.Instr.jumpi target]) ++
                    Assembly.Instr.jump next :: post by simp]
              rw [source_openRunUntilTransfer_one_at_boundary
                hFits.2.1 hMidPc]
              simp [Assembly.InteractionSemantics.Source.openStepAtResult,
                Assembly.InteractionSemantics.Source.openStepAt,
                Assembly.Source.stepAt,
                Assembly.Instr.haltKind?,
                Assembly.Instr.classifyFlow,
                Assembly.Instr.classifyFlowWith,
                Assembly.FlowStep.result,
                hNextDest', Assembly.Source.invalid,
                mid, popped,
                Simulation.Interaction.bind_done_ok,
                Simulation.Interaction.bind_done_error]
              simp [Assembly.Source.jumpPc, mid, popped]
              rfl
            rw [show
              ([Assembly.Instr.jumpi target,
                Assembly.Instr.jump next] :
                  Assembly.Program).length = 2 by rfl]
            rw [hRun]
            apply Simulation.Interaction.Rel.done
            simp [Preservation.Block.RunSimulates,
              TypedCfg.Block.runTerm, hPop, popped,
              Preservation.Outcome.Simulates]
            exact
              ⟨nextDest, hNextDest', rfl,
                Assembly.SameRuntimeData.jumpPc nextDest popped⟩
          · have hBne :
                (cond != EvmYul.UInt256.ofNat 0) = true :=
              Preservation.uint256_bne_zero_of_ne cond hZero
            have hRun :
                Assembly.InteractionSemantics.Source.openRunUntilTransfer
                    (pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++ post)
                    2 state =
                  .done
                    (.ok
                      (.running
                        (Assembly.Source.jumpPc targetDest popped))) := by
              rw [show
                pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++ post =
                    pre ++ Assembly.Instr.jumpi target ::
                      Assembly.Instr.jump next :: post by simp]
              rw [show 2 = 1 + 1 by omega]
              rw [source_openRunUntilTransfer_succ_at_boundary
                1 hFits.1 hPc]
              simp [Assembly.InteractionSemantics.Source.openStepAtResult,
                Assembly.InteractionSemantics.Source.openStepAt,
                Assembly.Source.stepAt,
                Assembly.Instr.haltKind?,
                Assembly.Instr.classifyFlow,
                Assembly.Instr.classifyFlowWith,
                hTargetDest', hPop, hZero, hBne,
                Assembly.Source.invalid, popped,
                Assembly.Source.jumpPc,
                Assembly.FlowStep.result,
                Simulation.Interaction.bind_done_ok,
                Simulation.Interaction.bind_done_error]
              rfl
            rw [show
              ([Assembly.Instr.jumpi target,
                Assembly.Instr.jump next] :
                  Assembly.Program).length = 2 by rfl]
            rw [hRun]
            apply Simulation.Interaction.Rel.done
            simp [Preservation.Block.RunSimulates,
              TypedCfg.Block.runTerm, hPop, hZero, popped,
              Preservation.Outcome.Simulates]
            exact
              ⟨targetDest, hTargetDest', rfl,
                Assembly.SameRuntimeData.jumpPc targetDest popped⟩
  | returnDispatch returnCount sites =>
      simp [Preservation.Terminator.Direct] at hDirect
  | halt kind =>
      cases kind with
      | stop =>
          simp [TypedCfg.Terminator.lowerAt?] at hLower
          subst code
          have hRun :
              Assembly.InteractionSemantics.Source.openRunUntilTransfer
                  (pre ++ [Assembly.Instr.prim .stop] ++ post)
                  1 state =
                .done
                  (Assembly.Target.stepInstrResult
                    (.prim .stop) state) := by
            rw [show
              pre ++ [Assembly.Instr.prim .stop] ++ post =
                pre ++ Assembly.Instr.prim .stop :: post by simp]
            exact
              source_openRunUntilTransfer_one_prim_closed
                hFits.1 hPc (by rfl) (by decide) (by decide)
          rw [show
            ([Assembly.Instr.prim .stop] :
              Assembly.Program).length = 1 by rfl]
          rw [hRun]
          apply Simulation.Interaction.Rel.done
          rw [Preservation.Block.runTermChecked_simulates_iff]
          rfl
      | «return» =>
          simp [TypedCfg.Terminator.lowerAt?] at hLower
          subst code
          have hRun :
              Assembly.InteractionSemantics.Source.openRunUntilTransfer
                  (pre ++ [Assembly.Instr.prim .return] ++ post)
                  1 state =
                .done
                  (Assembly.Target.stepInstrResult
                    (.prim .return) state) := by
            rw [show
              pre ++ [Assembly.Instr.prim .return] ++ post =
                pre ++ Assembly.Instr.prim .return :: post by simp]
            exact
              source_openRunUntilTransfer_one_prim_closed
                hFits.1 hPc (by rfl) (by decide) (by decide)
          rw [show
            ([Assembly.Instr.prim .return] :
              Assembly.Program).length = 1 by rfl]
          rw [hRun]
          apply Simulation.Interaction.Rel.done
          rfl
      | revert =>
          simp [TypedCfg.Terminator.lowerAt?] at hLower
          subst code
          have hRun :
              Assembly.InteractionSemantics.Source.openRunUntilTransfer
                  (pre ++ [Assembly.Instr.prim .revert] ++ post)
                  1 state =
                .done
                  (Assembly.Target.stepInstrResult
                    (.prim .revert) state) := by
            rw [show
              pre ++ [Assembly.Instr.prim .revert] ++ post =
                pre ++ Assembly.Instr.prim .revert :: post by simp]
            exact
              source_openRunUntilTransfer_one_prim_closed
                hFits.1 hPc (by rfl) (by decide) (by decide)
          rw [show
            ([Assembly.Instr.prim .revert] :
              Assembly.Program).length = 1 by rfl]
          rw [hRun]
          apply Simulation.Interaction.Rel.done
          rfl
      | selfdestruct =>
          simp [TypedCfg.Terminator.lowerAt?] at hLower
          subst code
          have hRun :
              Assembly.InteractionSemantics.Source.openRunUntilTransfer
                  (pre ++ [Assembly.Instr.prim .selfdestruct] ++ post)
                  1 state =
                .done
                  (Assembly.Target.stepInstrResult
                    (.prim .selfdestruct) state) := by
            rw [show
              pre ++ [Assembly.Instr.prim .selfdestruct] ++ post =
                pre ++ Assembly.Instr.prim .selfdestruct :: post by simp]
            exact
              source_openRunUntilTransfer_one_prim_closed
                hFits.1 hPc (by rfl) (by decide) (by decide)
          rw [show
            ([Assembly.Instr.prim .selfdestruct] :
              Assembly.Program).length = 1 by rfl]
          rw [hRun]
          apply Simulation.Interaction.Rel.done
          rw [Preservation.Block.runTermChecked_simulates_iff]
          rfl
  | invalid =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      have hRun :
          Assembly.InteractionSemantics.Source.openRunUntilTransfer
              (pre ++ [Assembly.Instr.prim .invalid] ++ post)
              1 state =
            .done (.error .InvalidInstruction) := by
        rw [show
          pre ++ [Assembly.Instr.prim .invalid] ++ post =
            pre ++ Assembly.Instr.prim .invalid :: post by simp]
        simpa [Assembly.Target.stepInstrResult] using
          (source_openRunUntilTransfer_one_prim_closed
            (pre := pre) (post := post) (op := .invalid)
            (state := state) hFits.1 hPc
            (by rfl) (by decide) (by decide))
      rw [show
        ([Assembly.Instr.prim .invalid] :
          Assembly.Program).length = 1 by rfl]
      rw [hRun]
      apply Simulation.Interaction.Rel.done
      exact ⟨.InvalidInstruction, rfl⟩

/--
Adjacent open-world preservation for every successfully lowered TypedCfg
terminator. The policy is selected by the source terminator and remains private
to this pass boundary.
-/
theorem lowerAt?_openRunUntilTransfer_rel
    {shape : Shape} {term : TypedCfg.Terminator}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower : term.lowerAt? shape = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedControl
        (pre ++ code ++ post) term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Simulation.Interaction.Rel
      (Preservation.Block.RunSimulates (pre ++ code ++ post))
      (.done (TypedCfg.Block.runTermChecked shape term state))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy term)
        (pre ++ code ++ post) code.length state) := by
  cases term with
  | fallthrough next =>
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (lowerAt?_openRunUntilTransfer_rel_of_direct
          (term := .fallthrough next)
          (by simp [Preservation.Terminator.Direct])
          hLower hFits hPc hResolved.1)
  | jump target =>
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (lowerAt?_openRunUntilTransfer_rel_of_direct
          (term := .jump target)
          (by simp [Preservation.Terminator.Direct])
          hLower hFits hPc hResolved.1)
  | jumpi target next =>
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (lowerAt?_openRunUntilTransfer_rel_of_direct
          (term := .jumpi target next)
          (by simp [Preservation.Terminator.Direct])
          hLower hFits hPc hResolved.1)
  | halt kind =>
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (lowerAt?_openRunUntilTransfer_rel_of_direct
          (term := .halt kind)
          (by simp [Preservation.Terminator.Direct])
          hLower hFits hPc hResolved.1)
  | invalid =>
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (lowerAt?_openRunUntilTransfer_rel_of_direct
          (term := .invalid)
          (by simp [Preservation.Terminator.Direct])
          hLower hFits hPc hResolved.1)
  | returnDispatch returnCount sites =>
      cases hDepth : shape.returnTokenDepth? with
      | none =>
          simp [TypedCfg.Terminator.lowerAt?, hDepth] at hLower
      | some depth =>
          by_cases hBound : depth < 16
          · have hFacts :
                (sites ≠ [] ∧ depth = returnCount) ∧
                  TypedCfg.Terminator.returnDispatchCode depth sites =
                    code := by
              simpa [TypedCfg.Terminator.lowerAt?, hDepth,
                TypedCfg.Terminator.returnDispatchCode?, hBound] using
                hLower
            have hGood : sites ≠ [] ∧ depth = returnCount :=
              hFacts.1
            have hCodeEq :
                code =
                  TypedCfg.Terminator.returnDispatchCode depth sites :=
              hFacts.2.symm
            have hResolvedCases :
                Preservation.Terminator.ResolvedCaseLabels
                  (pre ++ code ++ post) sites := by
              intro site hMem
              exact hResolved.2 site.caseLabel
                (by
                  simp only [TypedCfg.Terminator.definedLabels]
                  exact List.mem_map.mpr ⟨site, hMem, rfl⟩)
            cases hGet : state.stack[depth]? with
            | none =>
                simpa [
                  TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy] using
                  (returnDispatch_missing_token_openRunUntilTransfer_rel
                    hDepth hGood.2 hGood.1 hCodeEq hBound hGet
                    hFits hPc)
            | some token =>
                cases hFind :
                    TypedCfg.Block.ReturnSite.findTarget? token sites with
                | none =>
                    simpa [
                      TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy] using
                      (returnDispatch_unknown_token_openRunUntilTransfer_rel
                        hDepth hGood.2 hCodeEq hBound hGet hFind
                        hFits hPc hResolvedCases)
                | some target =>
                    simpa [
                      TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy] using
                      (returnDispatch_selected_openRunUntilTransfer_rel
                        hDepth hGood.2 hCodeEq hBound hGet hFind
                        hFits hPc hResolved.1 hResolvedCases hLabels)
          · simp [TypedCfg.Terminator.lowerAt?, hDepth,
              TypedCfg.Terminator.returnDispatchCode?, hBound] at hLower

end Terminator

namespace Block

/--
Every successful open branch of a lowered body reaches the end of the emitted
body fragment with the compiler-computed output shape.
-/
theorem openRunBody_atLoweredEnd
    {body : List TypedCfg.Instr} {shape output : Shape}
    {code : Assembly.Program} {state : EVMState}
    (hLower :
      TypedCfg.Block.lowerBodyFrom? body shape =
        some (code, output)) :
    Simulation.Interaction.AllDone
      (Instr.AtLoweredEnd state code output)
      (TypedCfg.InteractionSemantics.Block.openRunBody
        body shape state) := by
  induction body generalizing shape code output state with
  | nil =>
      simp [TypedCfg.Block.lowerBodyFrom?] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      apply Simulation.Interaction.AllDone.done
      change
        state.pc =
            state.pc + EvmYul.UInt256.ofNat 0 ∧
          shape = shape
      exact
        ⟨(Preservation.uint256_add_zero state.pc).symm, rfl⟩
  | cons instr rest ih =>
      unfold TypedCfg.Block.lowerBodyFrom? at hLower
      cases hHead : instr.lowerAt? shape with
      | none =>
          simp [hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, headOutput⟩
          cases hTail :
              TypedCfg.Block.lowerBodyFrom? rest headOutput with
          | none =>
              simp [hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailOutput⟩
              simp [hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hHeadEnd :=
                Instr.openRunAt_atLoweredEnd
                  (state := state) hHead
              have hBound :
                  Simulation.Interaction.AllDone
                    (Instr.AtLoweredEnd state
                      (head ++ tail) tailOutput)
                    (Simulation.Interaction.bind
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        instr shape state)
                      (fun result =>
                        TypedCfg.InteractionSemantics.Block.openRunBody
                          rest result.2 result.1)) := by
                apply Simulation.Interaction.AllDone.bind hHeadEnd
                · intro err hError
                  trivial
                · intro result hResult
                  rcases result with ⟨mid, actualOutput⟩
                  change
                    mid.pc =
                        state.pc +
                          EvmYul.UInt256.ofNat head.byteLength ∧
                      actualOutput = headOutput at hResult
                  rcases hResult with ⟨hMidPc, hOutput⟩
                  subst actualOutput
                  apply
                    Simulation.Interaction.AllDone.mono
                      (ih (state := mid) hTail)
                  intro outcome hOutcome
                  cases outcome with
                  | error err =>
                      trivial
                  | ok value =>
                      rcases value with ⟨final, actualTailOutput⟩
                      change
                        final.pc =
                            mid.pc +
                              EvmYul.UInt256.ofNat tail.byteLength ∧
                          actualTailOutput = tailOutput at hOutcome
                      rcases hOutcome with ⟨hFinalPc, hTailOutput⟩
                      change
                        final.pc =
                            state.pc +
                              EvmYul.UInt256.ofNat
                                (head ++ tail).byteLength ∧
                          actualTailOutput = tailOutput
                      refine ⟨?_, hTailOutput⟩
                      calc
                        final.pc =
                            mid.pc +
                              EvmYul.UInt256.ofNat tail.byteLength :=
                          hFinalPc
                        _ =
                            (state.pc +
                              EvmYul.UInt256.ofNat head.byteLength) +
                              EvmYul.UInt256.ofNat tail.byteLength := by
                          rw [hMidPc]
                        _ =
                            state.pc +
                              (EvmYul.UInt256.ofNat head.byteLength +
                                EvmYul.UInt256.ofNat tail.byteLength) := by
                          exact
                            Assembly.UInt256_add_assoc
                              state.pc
                              (EvmYul.UInt256.ofNat head.byteLength)
                              (EvmYul.UInt256.ofNat tail.byteLength)
                        _ =
                            state.pc +
                              EvmYul.UInt256.ofNat
                                (head.byteLength + tail.byteLength) := by
                          rw [Assembly.UInt256_ofNat_add]
                        _ =
                            state.pc +
                              EvmYul.UInt256.ofNat
                                (head ++ tail).byteLength := by
                          simp [Assembly.Program.byteLength_append]
              simpa [TypedCfg.InteractionSemantics.Block.openRunBody,
                TypedCfg.Control.Block.runBody] using hBound

private theorem bind_self_rel_of_allDone
    {Error Source LeftTarget RightTarget : Type}
    {property : Except Error Source → Prop}
    {doneRel :
      Except Error LeftTarget → Except Error RightTarget → Prop}
    {interaction : Simulation.Interaction Error Source}
    {leftNext :
      Source → Simulation.Interaction Error LeftTarget}
    {rightNext :
      Source → Simulation.Interaction Error RightTarget}
    (hInteraction :
      Simulation.Interaction.AllDone property interaction)
    (hError :
      ∀ err, property (.error err) →
        doneRel (.error err) (.error err))
    (hNext :
      ∀ value, property (.ok value) →
        Simulation.Interaction.Rel doneRel
          (leftNext value) (rightNext value)) :
    Simulation.Interaction.Rel doneRel
      (Simulation.Interaction.bind interaction leftNext)
      (Simulation.Interaction.bind interaction rightNext) := by
  induction hInteraction with
  | @done outcome hDone =>
      cases outcome with
      | error err =>
          exact .done (hError err hDone)
      | ok value =>
          exact hNext value hDone
  | request hResume ih =>
      exact .request ih

/--
The Assembly fragment produced for a TypedCfg body exposes exactly the same
open interaction tree as the typed body, for every resource answer and every
external-world response.
-/
theorem lowerBodyFrom?_source_openRunNResult
    {body : List TypedCfg.Instr} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower :
      TypedCfg.Block.lowerBodyFrom? body shape =
        some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunNResult
        (pre ++ code ++ post) code.length state =
      Simulation.Interaction.map
        (fun result => Assembly.StepResult.running result.1)
        (TypedCfg.InteractionSemantics.Block.openRunBody
          body shape state) := by
  induction body generalizing shape code output pre state with
  | nil =>
      simp [TypedCfg.Block.lowerBodyFrom?] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      rfl
  | cons instr rest ih =>
      unfold TypedCfg.Block.lowerBodyFrom? at hLower
      cases hHead : instr.lowerAt? shape with
      | none =>
          simp [hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, headOutput⟩
          cases hTail :
              TypedCfg.Block.lowerBodyFrom? rest headOutput with
          | none =>
              simp [hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailOutput⟩
              simp [hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hHeadFits :
                  Assembly.Program.PCFitsFrom pre head :=
                Assembly.Program.PCFitsFrom.left hFits
              have hTailFits :
                  Assembly.Program.PCFitsFrom (pre ++ head) tail :=
                Assembly.Program.PCFitsFrom.right hFits
              have hHeadRun :=
                Instr.lowerAt_openRunNResult_eq
                  (post := tail ++ post) hHead hHeadFits hPc
              have hHeadEnd :=
                Instr.openRunAt_atLoweredEnd
                  (state := state) hHead
              rw [List.length_append,
                Assembly.InteractionSemantics.Source.openRunNResult_add]
              rw [show
                Assembly.InteractionSemantics.Source.openRunNResult
                    (pre ++ (head ++ tail) ++ post)
                    head.length state =
                  Simulation.Interaction.map
                    (fun result =>
                      Assembly.StepResult.running result.1)
                    (TypedCfg.InteractionSemantics.Instr.openRunAt
                      instr shape state) by
                simpa [List.append_assoc] using hHeadRun]
              have hBound :
                  Simulation.Interaction.bind
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        instr shape state)
                      (fun result =>
                        Assembly.InteractionSemantics.Source.openRunNResult
                          ((pre ++ head) ++ tail ++ post)
                          tail.length result.1) =
                    Simulation.Interaction.bind
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        instr shape state)
                      (fun result =>
                        Simulation.Interaction.map
                          (fun tailResult =>
                            Assembly.StepResult.running tailResult.1)
                          (TypedCfg.InteractionSemantics.Block.openRunBody
                            rest result.2 result.1)) := by
                apply
                  Simulation.Interaction.AllDone.bind_congr
                    hHeadEnd
                intro result hEnd
                rcases result with ⟨mid, actualOutput⟩
                change
                  mid.pc =
                      state.pc +
                        EvmYul.UInt256.ofNat head.byteLength ∧
                    actualOutput = headOutput at hEnd
                rcases hEnd with ⟨hMidDelta, hOutput⟩
                subst actualOutput
                have hMidPc :
                    mid.pc = (pre ++ head).pcAfter := by
                  calc
                    mid.pc =
                        state.pc +
                          EvmYul.UInt256.ofNat head.byteLength :=
                      hMidDelta
                    _ =
                        pre.pcAfter +
                          EvmYul.UInt256.ofNat head.byteLength := by
                      rw [hPc]
                    _ = (pre ++ head).pcAfter := by
                      exact
                        (Assembly.Program.pcAfter_append
                          pre head).symm
                simpa [List.append_assoc] using
                  ih (shape := headOutput)
                    (pre := pre ++ head) (state := mid)
                    hTail hTailFits hMidPc
              change
                Simulation.Interaction.bind
                    (Simulation.Interaction.map
                      (fun result =>
                        Assembly.StepResult.running result.1)
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        instr shape state))
                    (fun result =>
                      match result with
                      | .running mid =>
                          Assembly.InteractionSemantics.Source.openRunNResult
                            (pre ++ (head ++ tail) ++ post)
                            tail.length mid
                      | .halted halt =>
                          Simulation.Interaction.pure
                            (Assembly.StepResult.halted halt)) =
                  Simulation.Interaction.map
                    (fun result =>
                      Assembly.StepResult.running result.1)
                    (Simulation.Interaction.bind
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        instr shape state)
                      (fun result =>
                        TypedCfg.InteractionSemantics.Block.openRunBody
                          rest result.2 result.1))
              calc
                _ =
                    Simulation.Interaction.bind
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        instr shape state)
                      (fun result =>
                        Assembly.InteractionSemantics.Source.openRunNResult
                          ((pre ++ head) ++ tail ++ post)
                          tail.length result.1) := by
                    unfold Simulation.Interaction.map
                    rw [Simulation.Interaction.bind_assoc]
                    congr 1
                    funext result
                    simp [Simulation.Interaction.pure,
                      Simulation.Interaction.bind,
                      List.append_assoc]
                _ =
                    Simulation.Interaction.bind
                      (TypedCfg.InteractionSemantics.Instr.openRunAt
                        instr shape state)
                      (fun result =>
                        Simulation.Interaction.map
                          (fun tailResult =>
                            Assembly.StepResult.running tailResult.1)
                          (TypedCfg.InteractionSemantics.Block.openRunBody
                            rest result.2 result.1)) :=
                  hBound
                _ =
                    Simulation.Interaction.map
                      (fun result =>
                        Assembly.StepResult.running result.1)
                      (Simulation.Interaction.bind
                        (TypedCfg.InteractionSemantics.Instr.openRunAt
                          instr shape state)
                        (fun result =>
                          TypedCfg.InteractionSemantics.Block.openRunBody
                            rest result.2 result.1)) := by
                    unfold Simulation.Interaction.map
                    rw [Simulation.Interaction.bind_assoc]

/--
Open body execution followed by its lowered terminator is an adjacent
TypedCfg-to-Assembly simulation. Both target phases use the canonical Assembly
runners; the compiler-provided partition is discharged by `lowerBodyFrom?` and
`lowerAt?`.
-/
theorem lowerBodyThenTerm_openRun_rel
    {body : List TypedCfg.Instr} {input output : Shape}
    {term : TypedCfg.Terminator}
    {bodyCode termCode pre post : Assembly.Program}
    {state : EVMState}
    (hBody :
      TypedCfg.Block.lowerBodyFrom? body input =
        some (bodyCode, output))
    (hTerm : term.lowerAt? output = some termCode)
    (hBodyFits :
      Assembly.Program.PCFitsFrom pre bodyCode)
    (hTermFits :
      Assembly.Program.PCFitsFrom (pre ++ bodyCode) termCode)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedControl
        (pre ++ bodyCode ++ termCode ++ post) term)
    (hLabels :
      ((pre ++ bodyCode ++ termCode ++ post).labels).Nodup) :
    Simulation.Interaction.Rel
      (Preservation.Block.RunSimulates
        (pre ++ bodyCode ++ termCode ++ post))
      (do
        let (mid, actualOutput) ←
          TypedCfg.InteractionSemantics.Block.openRunBody
            body input state
        if actualOutput = output then
          match TypedCfg.Block.runTermChecked output term mid with
          | .ok outcome => pure outcome
          | .error err => throw err
        else
          throw .InvalidInstruction)
      (do
        let bodyResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            (pre ++ bodyCode ++ termCode ++ post)
            bodyCode.length state
        match bodyResult with
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              (pre ++ bodyCode ++ termCode ++ post)
              termCode.length mid
        | .halted halt =>
            pure (.halted halt)) := by
  let program := pre ++ bodyCode ++ termCode ++ post
  let sourceBody :=
    TypedCfg.InteractionSemantics.Block.openRunBody
      body input state
  have hBodyRun :=
    lowerBodyFrom?_source_openRunNResult
      (pre := pre) (post := termCode ++ post)
      hBody hBodyFits hPc
  have hBodyRun' :
      Assembly.InteractionSemantics.Source.openRunNResult
          program bodyCode.length state =
        Simulation.Interaction.map
          (fun result => Assembly.StepResult.running result.1)
          sourceBody := by
    simpa [program, sourceBody, List.append_assoc] using hBodyRun
  have hTargetEq :
      (do
        let bodyResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            program bodyCode.length state
        match bodyResult with
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              program termCode.length mid
        | .halted halt =>
            pure (.halted halt)) =
        Simulation.Interaction.bind sourceBody
          (fun result =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              program termCode.length result.1) := by
    rw [hBodyRun']
    change
      Simulation.Interaction.bind
          (Simulation.Interaction.bind sourceBody
            (fun result =>
              Simulation.Interaction.pure
                (Assembly.StepResult.running result.1)))
          (fun bodyResult =>
            match bodyResult with
            | .running mid =>
                Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                  (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                    term)
                  program termCode.length mid
            | .halted halt =>
                pure (.halted halt)) =
        Simulation.Interaction.bind sourceBody
          (fun result =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              program termCode.length result.1)
    rw [Simulation.Interaction.bind_assoc]
    congr 1
  rw [show
    pre ++ bodyCode ++ termCode ++ post = program by
    rfl]
  rw [hTargetEq]
  have hBodyEnd :=
    openRunBody_atLoweredEnd (state := state) hBody
  have hRel :
      Simulation.Interaction.Rel
        (Preservation.Block.RunSimulates program)
        (Simulation.Interaction.bind sourceBody
          (fun result =>
            if result.2 = output then
              match TypedCfg.Block.runTermChecked
                  output term result.1 with
              | .ok outcome => pure outcome
              | .error err => throw err
            else
              throw .InvalidInstruction))
        (Simulation.Interaction.bind sourceBody
          (fun result =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              program termCode.length result.1)) := by
    refine
      bind_self_rel_of_allDone
        (property := Instr.AtLoweredEnd state bodyCode output)
        (doneRel := Preservation.Block.RunSimulates program)
        (interaction := sourceBody)
        (leftNext := fun result =>
          if result.2 = output then
            match TypedCfg.Block.runTermChecked
                output term result.1 with
            | .ok outcome => pure outcome
            | .error err => throw err
          else
            throw .InvalidInstruction)
        (rightNext := fun result =>
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
              term)
            program termCode.length result.1)
        (by simpa [sourceBody] using hBodyEnd) ?_ ?_
    · intro err hError
      rfl
    · intro result hResult
      rcases result with ⟨mid, actualOutput⟩
      change
        mid.pc =
            state.pc +
              EvmYul.UInt256.ofNat bodyCode.byteLength ∧
          actualOutput = output at hResult
      rcases hResult with ⟨hMidDelta, hOutput⟩
      subst actualOutput
      have hMidPc :
          mid.pc = (pre ++ bodyCode).pcAfter := by
        calc
          mid.pc =
              state.pc +
                EvmYul.UInt256.ofNat bodyCode.byteLength :=
            hMidDelta
          _ =
              pre.pcAfter +
                EvmYul.UInt256.ofNat bodyCode.byteLength := by
            rw [hPc]
          _ = (pre ++ bodyCode).pcAfter := by
            exact
              (Assembly.Program.pcAfter_append pre bodyCode).symm
      have hTermRun :=
        Terminator.lowerAt?_openRunUntilTransfer_rel
          (pre := pre ++ bodyCode) (post := post)
          hTerm hTermFits hMidPc
          (by simpa [program, List.append_assoc] using hResolved)
          (by simpa [program, List.append_assoc] using hLabels)
      cases hChecked : TypedCfg.Block.runTermChecked output term mid with
      | error err => simpa [program, hChecked] using hTermRun
      | ok outcome => simpa [program, hChecked] using hTermRun
  simpa [sourceBody] using hRel

/--
Whole-block adjacent preservation. Successful ordinary lowering supplies every
compiler-owned fragment internally; callers provide no body split, policy
certificate, or generated-code premise beyond the existing lowering equation.
-/
theorem lower?_openRun_rel
    {block : TypedCfg.Block} {code pre post : Assembly.Program}
    {state : EVMState}
    (hLower : block.lower? = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedControl
        (pre ++ code ++ post) block.term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Simulation.Interaction.Rel
      (Preservation.Block.RunSimulates (pre ++ code ++ post))
      (TypedCfg.InteractionSemantics.Block.openRun
        block state.incrPC)
      (TypedCfg.InteractionSemantics.CompiledBlock.openRun
        block (pre ++ code ++ post) state) := by
  unfold TypedCfg.Block.lower? at hLower
  cases hBody :
      TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm : block.term.lowerAt? block.output with
        | none =>
            simp [hBody, hTerm] at hLower
        | some termCode =>
            simp [hBody, hTerm] at hLower
            subst code
            let program :=
              pre ++
                (Assembly.Instr.label block.label ::
                  bodyCode ++ termCode) ++ post
            let entry := state.incrPC
            have hLabelOpen :
                Assembly.InteractionSemantics.Source.openStepAtResult
                    (pre ++ Assembly.Instr.label block.label ::
                      ((bodyCode ++ termCode) ++ post))
                    pre.byteLength
                    (.label block.label) state =
                  .done (.ok (.running entry)) := by
              rw [source_openStepAtResult_eq_done_of_stepAt (by rfl)]
              simp [Assembly.Source.stepAtResult,
                Assembly.Source.stepAt,
                Assembly.Instr.haltKind?,
                Assembly.Target.stepInstr, entry]
            have hLabelRun :
                Assembly.InteractionSemantics.Source.openRunNResult
                    program 1 state =
                  .done (.ok (.running entry)) := by
              rw [show
                program =
                  pre ++ Assembly.Instr.label block.label ::
                    ((bodyCode ++ termCode) ++ post) by
                simp [program, List.append_assoc]]
              rw [source_openRunNResult_one_at_boundary hFits.1 hPc]
              exact hLabelOpen
            have hEntryPc :
                entry.pc =
                  (pre ++
                    [Assembly.Instr.label block.label]).pcAfter := by
              calc
                entry.pc =
                    state.pc + EvmYul.UInt256.ofNat 1 := rfl
                _ =
                    pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
                  rw [hPc]
                _ =
                    (pre ++
                      [Assembly.Instr.label block.label]).pcAfter := by
                  simp [Assembly.Program.pcAfter,
                    Assembly.Program.byteLength_append,
                    Assembly.Program.byteLength,
                    Assembly.Instr.byteSize,
                    Assembly.UInt256_ofNat_add]
            have hBodyFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label])
                  bodyCode :=
              Assembly.Program.PCFitsFrom.left hFits.2
            have hTermFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label] ++
                    bodyCode)
                  termCode := by
              simpa [List.append_assoc] using
                Assembly.Program.PCFitsFrom.right hFits.2
            have hRest :=
              lowerBodyThenTerm_openRun_rel
                (body := block.body) (input := block.input)
                (output := block.output) (term := block.term)
                (bodyCode := bodyCode) (termCode := termCode)
                (pre :=
                  pre ++ [Assembly.Instr.label block.label])
                (post := post) (state := entry)
                hBody hTerm hBodyFits hTermFits hEntryPc
                (by simpa [program, List.append_assoc] using hResolved)
                (by simpa [program, List.append_assoc] using hLabels)
            have hCompiledRun :
                TypedCfg.InteractionSemantics.CompiledBlock.openRun
                    block program state =
                  (do
                    let bodyResult ←
                      Assembly.InteractionSemantics.Source.openRunNResult
                        program bodyCode.length entry
                    match bodyResult with
                    | .running mid =>
                        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                          (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                            block.term)
                          program termCode.length mid
                    | .halted halt =>
                        pure (.halted halt)) := by
              simp [
                TypedCfg.InteractionSemantics.CompiledBlock.openRun,
                hBody, hTerm, hLabelRun]
              change
                Simulation.Interaction.bind
                    ((.done
                      (.ok (Assembly.StepResult.running entry))) :
                        Assembly.InteractionSemantics.OpenStepResult)
                    (fun labelResult =>
                      match labelResult with
                      | Assembly.StepResult.halted halt =>
                          pure (Assembly.StepResult.halted halt)
                      | Assembly.StepResult.running entry =>
                          do
                            let bodyResult ←
                              Assembly.InteractionSemantics.Source.openRunNResult
                                program bodyCode.length entry
                            match bodyResult with
                            | Assembly.StepResult.halted halt =>
                                pure (Assembly.StepResult.halted halt)
                            | Assembly.StepResult.running mid =>
                                Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                                  (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                                    block.term)
                                  program termCode.length mid) =
                  (do
                    let bodyResult ←
                      Assembly.InteractionSemantics.Source.openRunNResult
                        program bodyCode.length entry
                    match bodyResult with
                    | Assembly.StepResult.running mid =>
                        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                          (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                            block.term)
                          program termCode.length mid
                    | Assembly.StepResult.halted halt =>
                        pure (Assembly.StepResult.halted halt))
              rw [Simulation.Interaction.bind_done_ok]
              change
                Simulation.Interaction.bind
                    (Assembly.InteractionSemantics.Source.openRunNResult
                      program bodyCode.length entry)
                    (fun bodyResult =>
                      match bodyResult with
                      | Assembly.StepResult.halted halt =>
                          pure (Assembly.StepResult.halted halt)
                      | Assembly.StepResult.running mid =>
                          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                            (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                              block.term)
                            program termCode.length mid) =
                  Simulation.Interaction.bind
                    (Assembly.InteractionSemantics.Source.openRunNResult
                      program bodyCode.length entry)
                    (fun bodyResult =>
                      match bodyResult with
                      | Assembly.StepResult.running mid =>
                          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                            (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                              block.term)
                            program termCode.length mid
                      | Assembly.StepResult.halted halt =>
                          pure (Assembly.StepResult.halted halt))
              congr 1
              funext bodyResult
              cases bodyResult <;> rfl
            change
              Simulation.Interaction.Rel
                (Preservation.Block.RunSimulates program)
                (TypedCfg.InteractionSemantics.Block.openRun
                  block entry)
                (TypedCfg.InteractionSemantics.CompiledBlock.openRun
                  block program state)
            rw [hCompiledRun]
            simpa [
              TypedCfg.InteractionSemantics.Block.openRun,
              TypedCfg.InteractionSemantics.Block.openRunBody,
              TypedCfg.Control.Block.run,
              program, entry, List.append_assoc] using hRest
      · simp [hBody, hOutput] at hLower

end Block

namespace Program

/--
One source CFG step is simulated by the compiler-selected block fragment in
the accepted Assembly program. The fragment is derived from ordinary lowering,
not accepted as public evidence.
-/
theorem lower?_step_open_rel
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : EVMState} {entryPc : Nat}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    Simulation.Interaction.Rel
      (Preservation.Block.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openStep
        program label state.incrPC)
      (TypedCfg.InteractionSemantics.CompiledBlock.openRun
        block target state) := by
  rcases
      TypedCfg.Program.lower?_fragment_of_findBlock?
        hLower hFind with
    ⟨fragment⟩
  have hBlockLabel : block.label = label := by
    have hFound :
        (block.label == label) = true :=
      @List.find?_some TypedCfg.Block
        (fun candidate : TypedCfg.Block =>
          candidate.label == label)
        block program.blocks hFind
    exact beq_iff_eq.mp hFound
  subst label
  have hLabels : target.labels.Nodup :=
    Assembly.Program.labels_nodup_of_accepted hAccepted
  have hCodeFits :
      Assembly.Program.PCFitsFrom fragment.pre fragment.code := by
    apply Assembly.Program.PCFitsFrom.of_append
    rw [← fragment.target_eq]
    exact hFits
  have hResolved :
      Preservation.Terminator.ResolvedControl
        target block.term := by
    constructor
    · intro symbolic hSymbolic
      rcases
          TypedCfg.Block.target_instr_mem_of_lower?
            fragment.lower hSymbolic with
        ⟨instr, hInstr, hInstrTarget⟩
      have hInstrGlobal : instr ∈ target := by
        rw [fragment.target_eq]
        simp [hInstr]
      exact
        Assembly.Program.target_resolves_of_accepted
          hAccepted hInstrGlobal hInstrTarget
    · intro internal hInternal
      have hInstr :
          Assembly.Instr.label internal ∈ fragment.code :=
        TypedCfg.Block.definedLabel_instr_mem_of_lower?
          fragment.lower hInternal
      have hInstrGlobal :
          Assembly.Instr.label internal ∈ target := by
        rw [fragment.target_eq]
        simp [hInstr]
      exact
        Assembly.Program.labelPc_exists_of_mem_labels target
          (Assembly.Program.mem_labels_of_label_mem hInstrGlobal)
  rcases
      TypedCfg.Block.lower?_starts_with_label fragment.lower with
    ⟨tail, hCode⟩
  have hEntryLabel :
      target.labelPc block.label =
        some fragment.pre.byteLength := by
    have hNodup :
        (fragment.pre ++
          Assembly.Instr.label block.label ::
            (tail ++ fragment.post)).labels.Nodup := by
      simpa [fragment.target_eq, hCode, List.append_assoc] using
        hLabels
    have hAt :=
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        fragment.pre (tail ++ fragment.post) hNodup
    simpa [fragment.target_eq, hCode, List.append_assoc] using hAt
  have hEntryPcEq :
      entryPc = fragment.pre.byteLength := by
    rw [hEntryLabel] at hLabelPc
    exact (Option.some.inj hLabelPc).symm
  have hStatePc : state.pc = fragment.pre.pcAfter := by
    calc
      state.pc = EvmYul.UInt256.ofNat entryPc := hPc
      _ =
          EvmYul.UInt256.ofNat fragment.pre.byteLength := by
        rw [hEntryPcEq]
      _ = fragment.pre.pcAfter := rfl
  have hResolvedFragment :
      Preservation.Terminator.ResolvedControl
        (fragment.pre ++ fragment.code ++ fragment.post)
        block.term := by
    rw [← fragment.target_eq]
    exact hResolved
  have hLabelsFragment :
      ((fragment.pre ++ fragment.code ++
        fragment.post).labels).Nodup := by
    rw [← fragment.target_eq]
    exact hLabels
  have hRun :=
    Block.lower?_openRun_rel
      (block := block) (code := fragment.code)
      (pre := fragment.pre) (post := fragment.post)
      (state := state) fragment.lower hCodeFits hStatePc
      hResolvedFragment hLabelsFragment
  rw [fragment.target_eq]
  simpa [TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind] using hRun

/--
The existing adjacent step theorem weakened to the runtime-stable open outcome
relation used by whole-program control composition.
-/
theorem lower?_step_openRunSimulates_rel
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : EVMState} {entryPc : Nat}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    Simulation.Interaction.Rel
      (OpenBlock.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openStep
        program label state.incrPC)
      (TypedCfg.InteractionSemantics.CompiledBlock.openRun
        block target state) := by
  apply Simulation.Interaction.Rel.mono
    (lower?_step_open_rel
      hLower hAccepted hFits hFind hLabelPc hPc)
  intro sourceDone targetDone hSim
  exact OpenBlock.of_preservation hSim

/--
One compiler-selected block step from runtime-related source and target states.
Only program-counter independence is required; all open external effects remain
available.
-/
theorem lower?_step_openRunSimulates_rel_of_related
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {targetState sourceState : EVMState} {entryPc : Nat}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc :
      targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC) :
    Simulation.Interaction.Rel
      (OpenBlock.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openStep
        program label sourceState)
      (TypedCfg.InteractionSemantics.CompiledBlock.openRun
        block target targetState) := by
  have hSource :=
    InteractionCongruence.Program.openStep_runtimeRel
      (label := label) (target := sourceState)
      (source := targetState.incrPC)
      hTyped hIndependent hRuntime
  have hCompiled :=
    lower?_step_openRunSimulates_rel
      hLower hAccepted hFits hFind hLabelPc hPc
  have hTrans :=
    Simulation.Interaction.Rel.trans hSource hCompiled
  apply Simulation.Interaction.Rel.mono hTrans
  intro sourceDone targetDone hComposite
  rcases hComposite with
    ⟨middleDone, hSourceRuntime, hTargetSim⟩
  exact
    OpenBlock.runtime_left hSourceRuntime hTargetSim

theorem compiled_openStep_eq_of_labelPc
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : EVMState} {entryPc : Nat}
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    TypedCfg.InteractionSemantics.CompiledProgram.openStep
        program target state =
      TypedCfg.InteractionSemantics.CompiledBlock.openRun
        block target state := by
  have hToNat :=
    Assembly.Program.toNat_ofNat_labelPc hFits hLabelPc
  have hAt :=
    Assembly.Program.instrAtPc_of_labelPc hLabelPc
  unfold TypedCfg.InteractionSemantics.CompiledProgram.openStep
  rw [hPc, hToNat, hAt]
  simp [hFind]

theorem compiled_openStep_eq_error_of_labelPc
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {state : EVMState} {entryPc : Nat}
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = none)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    TypedCfg.InteractionSemantics.CompiledProgram.openStep
        program target state =
      .done (.error .InvalidInstruction) := by
  have hToNat :=
    Assembly.Program.toNat_ofNat_labelPc hFits hLabelPc
  have hAt :=
    Assembly.Program.instrAtPc_of_labelPc hLabelPc
  unfold TypedCfg.InteractionSemantics.CompiledProgram.openStep
  rw [hPc, hToNat, hAt]
  simp [hFind]

/--
One concrete compiled-program step. Dispatch is recovered from the Assembly
instruction at the target PC; no source label is replayed into the target
runner.
-/
theorem lower?_compiledStep_open_rel
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {targetState sourceState : EVMState}
    {entryPc : Nat}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc :
      targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC) :
    Simulation.Interaction.Rel
      (OpenBlock.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openStep
        program label sourceState)
      (TypedCfg.InteractionSemantics.CompiledProgram.openStep
        program target targetState) := by
  cases hFind : program.findBlock? label with
  | none =>
      rw [compiled_openStep_eq_error_of_labelPc
        hFits hFind hLabelPc hPc]
      simp only [
        TypedCfg.InteractionSemantics.Program.openStep,
        TypedCfg.Control.Program.step, hFind]
      change
        Simulation.Interaction.Rel
          (OpenBlock.RunSimulates target)
          (.done (.ok (.invalid sourceState)))
          (.done (.error .InvalidInstruction))
      apply Simulation.Interaction.Rel.done
      exact
        ⟨.InvalidInstruction, rfl⟩
  | some block =>
      rw [compiled_openStep_eq_of_labelPc
        hFits hFind hLabelPc hPc]
      exact
        lower?_step_openRunSimulates_rel_of_related
          hLower hAccepted hFits hTyped hIndependent
          hFind hLabelPc hPc hRuntime

/--
Fuel-indexed whole-program TypedCfg-to-Assembly open preservation.

The source follows symbolic CFG labels. The compiled runner follows only the
concrete Assembly instruction at its current PC. Their interaction trees remain
structurally related for every resource answer and every admissible external
world continuation.
-/
theorem lower?_openRunN_rel
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {targetState sourceState : EVMState}
    {entryPc : Nat} (fuel : Nat)
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc :
      targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC) :
    Simulation.Interaction.Rel
      (OpenBlock.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openRunN
        program fuel label sourceState)
      (TypedCfg.InteractionSemantics.CompiledProgram.openRunN
        program target fuel targetState) := by
  induction fuel generalizing label targetState sourceState entryPc with
  | zero =>
      simp only [
        TypedCfg.InteractionSemantics.Program.openRunN_zero,
        TypedCfg.InteractionSemantics.CompiledProgram.openRunN_zero]
      apply Simulation.Interaction.Rel.done
      have hTargetRuntime :
          Assembly.SameRuntimeData targetState sourceState :=
        Assembly.SameRuntimeData.trans
          (Assembly.SameRuntimeData.incrPC_right
            (Assembly.SameRuntimeData.refl targetState))
          hRuntime.symm
      exact
        ⟨entryPc, hLabelPc, hPc, hTargetRuntime⟩
  | succ fuel ih =>
      rw [
        TypedCfg.InteractionSemantics.Program.openRunN_succ,
        TypedCfg.InteractionSemantics.CompiledProgram.openRunN_succ]
      have hStepBase :=
        lower?_compiledStep_open_rel
          hLower hAccepted hFits hTyped hIndependent
          hLabelPc hPc hRuntime
      have hStep :=
        Simulation.Interaction.Rel.strengthen_left hStepBase
          (InteractionCongruence.Program.openStep_admissibleProgramStep
            program label sourceState)
      apply Simulation.Interaction.Rel.bind_custom hStep
      intro sourceDone targetDone hDone
      rcases hDone with ⟨hSim, hAdmissible⟩
      cases sourceDone with
      | error sourceError =>
          cases targetDone with
          | error targetError =>
              unfold OpenBlock.RunSimulates at hSim
              cases hSim
              exact .done rfl
          | ok targetResult =>
              unfold OpenBlock.RunSimulates at hSim
              cases hSim
      | ok sourceOutcome =>
          cases sourceOutcome with
          | fallthrough final =>
              exact hAdmissible.elim
          | returnDispatch final =>
              exact hAdmissible.elim
          | jump next sourceAfter =>
              cases targetDone with
              | error targetError =>
                  unfold OpenBlock.RunSimulates OpenOutcome.Simulates
                    Preservation.Outcome.Simulates
                    Preservation.Outcome.RunningAt at hSim
                  rcases hSim with ⟨dest, hDest, hImpossible⟩
                  exact hImpossible.elim
              | ok targetResult =>
                  cases targetResult with
                  | halted halt =>
                      unfold OpenBlock.RunSimulates OpenOutcome.Simulates
                        Preservation.Outcome.Simulates
                        Preservation.Outcome.RunningAt at hSim
                      rcases hSim with
                        ⟨dest, hDest, hImpossible⟩
                      exact hImpossible.elim
                  | running targetAfter =>
                      unfold OpenBlock.RunSimulates OpenOutcome.Simulates
                        Preservation.Outcome.Simulates
                        Preservation.Outcome.RunningAt at hSim
                      rcases hSim with
                        ⟨dest, hDest, hTargetPc, hData⟩
                      exact
                        ih hDest hTargetPc
                          (Assembly.SameRuntimeData.incrPC_right
                            hData.symm)
          | halt kind sourceFinal =>
              cases targetDone with
              | error targetError =>
                  exact .done hSim
              | ok targetResult =>
                  cases targetResult with
                  | halted halt =>
                      exact .done hSim
                  | running targetAfter =>
                      unfold OpenBlock.RunSimulates
                        OpenOutcome.Simulates at hSim
                      rcases hSim with
                        ⟨simulated, hData, hTarget⟩
                      unfold Assembly.Target.stepInstrResult at hTarget
                      cases hRun :
                          Assembly.Target.stepInstr
                            (.prim kind.toPrimOp) simulated with
                      | error error =>
                          rw [hRun] at hTarget
                          cases hTarget
                      | ok final =>
                          rw [hRun] at hTarget
                          have hKind :
                              (Assembly.TargetInstr.prim
                                kind.toPrimOp).haltKind? =
                                some kind := by
                            cases kind <;> rfl
                          rw [hKind] at hTarget
                          cases hTarget
          | invalid sourceFinal =>
              cases targetDone with
              | error targetError =>
                  exact .done hSim
              | ok targetResult =>
                  unfold OpenBlock.RunSimulates OpenOutcome.Simulates
                    Preservation.Outcome.Simulates at hSim
                  rcases hSim with ⟨error, hError⟩
                  cases hError

/--
Certified entry-point open preservation. All compiler-selected facts are
derived from the checked artifact; callers provide only the source-facing
program-counter-independence condition and related initial runtime states.
-/
theorem compileCertified?_entry_openRunN_rel
    {program : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {targetState sourceState : EVMState} (fuel : Nat)
    (hCompile : program.compileCertified? = some artifact)
    (hIndependent : program.ProgramCounterIndependent)
    (hPc :
      targetState.pc = EvmYul.UInt256.ofNat 0)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC) :
    Simulation.Interaction.Rel
      (OpenBlock.RunSimulates artifact.target)
      (TypedCfg.InteractionSemantics.Program.openRunN
        program fuel program.entry sourceState)
      (TypedCfg.InteractionSemantics.CompiledProgram.openRunN
        program artifact.target fuel targetState) := by
  have hLower :
      program.lower? = some artifact.target :=
    TypedCfg.Program.compileCertified?_target hCompile
  exact
    lower?_openRunN_rel fuel
      hLower
      (TypedCfg.Program.compileCertified?_targetAccepted hCompile)
      (TypedCfg.Program.compileCertified?_pcFits hCompile)
      (TypedCfg.Program.compileCertified?_wellTyped hCompile)
      hIndependent
      (TypedCfg.Program.lower?_entry_labelPc_zero hLower)
      hPc
      hRuntime

/-- Certified entry preservation to the ordinary Assembly source runner.
Compiler-selected block execution is eliminated internally; callers provide
only the source-facing safety of terminal CFG outcomes. -/
theorem compileCertified?_entry_openRunN_assembly_rel
    {program : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {targetState sourceState : EVMState} (fuel : Nat)
    (hCompile : program.compileCertified? = some artifact)
    (hIndependent : program.ProgramCounterIndependent)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat 0)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC)
    (hSafe : Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.AssemblySafeHalted
      (TypedCfg.InteractionSemantics.Program.openRunN
        program fuel program.entry sourceState)) :
    Simulation.Interaction.Rel
      (OpenBlock.RunSimulates artifact.target)
      (TypedCfg.InteractionSemantics.Program.openRunN
        program fuel program.entry sourceState)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.target
        (fuel *
          TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget program)
        targetState) := by
  have hBlocks :=
    compileCertified?_entry_openRunN_rel fuel
      hCompile hIndependent hPc hRuntime
  have hBlockTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (TypedCfg.InteractionSemantics.CompiledProgram.openRunN
        program artifact.target fuel targetState) := by
    have hStrong :=
      Simulation.Interaction.Rel.strengthen_left hBlocks hSafe
    apply Simulation.Interaction.Rel.allDone_right hStrong
    intro sourceDone targetDone hDone
    rcases hDone with ⟨hSim, hSafeDone⟩
    exact OpenBlock.terminal_of_assemblySafeHalted
      hSafeDone hSim
  have hFlatten :=
    TypedCfg.InteractionSemantics.CompiledProgram.openRunN_rel_source_terminal
      hBlockTerminal
  exact Simulation.Interaction.Rel.trans_eq_right hBlocks hFlatten

end Program

end InteractionPreservation
end TypedCfg
end EvmCompiler
