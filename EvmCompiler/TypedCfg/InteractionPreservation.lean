import EvmCompiler.Assembly.InteractionPreservation
import EvmCompiler.TypedCfg.InteractionSemantics
import EvmCompiler.TypedCfg.Preservation

namespace EvmCompiler
namespace TypedCfg
namespace InteractionPreservation

open Assembly.InteractionPreservation

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
      (.done (.ok
        (TypedCfg.Block.runTerm shape term state)))
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
                Assembly.Instr.classifyFlow]
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

end Terminator

namespace Block

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

end Block

end InteractionPreservation
end TypedCfg
end EvmCompiler
