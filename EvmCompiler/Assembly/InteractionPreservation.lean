import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.Assembly.Preservation

namespace EvmCompiler
namespace Assembly
namespace InteractionPreservation

open InteractionSemantics

namespace EVMState

@[simp] theorem finishCall_pc
    (state : EVMState) (rest : EvmYul.Stack Word)
    (callLocal : Simulation.CallLocal)
    (response : Simulation.CallResponse) :
    (InteractionSemantics.EVMState.finishCall
      state rest callLocal response).pc =
        state.pc + EvmYul.UInt256.ofNat 1 := by
  simp [InteractionSemantics.EVMState.finishCall,
    InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC]

@[simp] theorem finishCreate_pc
    (state : EVMState) (rest : EvmYul.Stack Word)
    (createLocal : Simulation.CreateLocal)
    (response : Simulation.CreateResponse) :
    (InteractionSemantics.EVMState.finishCreate
      state rest createLocal response).pc =
        state.pc + EvmYul.UInt256.ofNat 1 := by
  simp [InteractionSemantics.EVMState.finishCreate,
    InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC]

end EVMState

namespace PrimOp

def AdvancesPC (state : EVMState) :
    Except EVMException EVMState → Prop
  | .error _ => True
  | .ok final =>
      final.pc = state.pc + EvmYul.UInt256.ofNat 1

theorem resourceStep_advancesPC
    (kind : Simulation.ResourceQuery) (state : EVMState) :
    Simulation.Interaction.AllDone (AdvancesPC state)
      (InteractionSemantics.PrimOp.resourceStep kind state) := by
  apply Simulation.Interaction.AllDone.request
  intro value
  apply Simulation.Interaction.AllDone.done
  simp [AdvancesPC,
    InteractionSemantics.PrimOp.resourceStep,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem callStep_advancesPC
    (kind : Simulation.CallKind) (state : EVMState) :
    Simulation.Interaction.AllDone (AdvancesPC state)
      (InteractionSemantics.PrimOp.callStep kind state) := by
  unfold InteractionSemantics.PrimOp.callStep
  cases hOperands : kind.evmOperands? state.stack with
  | none =>
      exact .done trivial
  | some result =>
      rcases result with ⟨rest, operands⟩
      simp only [hOperands]
      split
      · apply Simulation.Interaction.AllDone.request
        intro response
        exact .done (EVMState.finishCall_pc _ _ _ _)
      · exact .done trivial

theorem createStep_advancesPC
    (kind : Simulation.CreateKind) (state : EVMState) :
    Simulation.Interaction.AllDone (AdvancesPC state)
      (InteractionSemantics.PrimOp.createStep kind state) := by
  unfold InteractionSemantics.PrimOp.createStep
  cases hOperands : kind.evmOperands? state.stack with
  | none =>
      exact .done trivial
  | some result =>
      rcases result with ⟨rest, operands⟩
      simp only [hOperands]
      split
      · apply Simulation.Interaction.AllDone.request
        intro response
        exact .done (EVMState.finishCreate_pc _ _ _ _)
      · exact .done trivial

/--
Every successful branch of an open, well-typed Assembly primitive advances
the program counter by its one-byte instruction width. The theorem quantifies
over every resource answer and every external-world response.
-/
theorem openStep_advancesPC
    {op : Assembly.PrimOp} {input output : Nat}
    {state : EVMState}
    (hArity : op.stackArity? = some (input, output)) :
    Simulation.Interaction.AllDone (AdvancesPC state)
      (InteractionSemantics.PrimOp.openStep op state) := by
  cases hExternal :
      Simulation.ExternalKind.ofEVMOperation? op.toEVM with
  | some external =>
      cases external with
      | call kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op state =
              InteractionSemantics.PrimOp.callStep kind state by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          exact callStep_advancesPC kind state
      | create kind =>
          rw [show
            InteractionSemantics.PrimOp.openStep op state =
              InteractionSemantics.PrimOp.createStep kind state by
                simp [InteractionSemantics.PrimOp.openStep, hExternal]]
          exact createStep_advancesPC kind state
  | none =>
      by_cases hGas : op = .gas
      · subst op
        exact resourceStep_advancesPC .gas state
      · by_cases hMsize : op = .msize
        · subst op
          exact resourceStep_advancesPC .msize state
        · rw [InteractionSemantics.PrimOp.openStep_closed
            hExternal hGas hMsize]
          cases hRun : op.step state with
          | error err =>
              exact .done trivial
          | ok final =>
              exact
                .done
                  (Assembly.PrimOp.step_pc_of_stackArity
                    hArity hRun)

end PrimOp

theorem openRunList_single (instr : TargetInstr) (state : EVMState) :
    InteractionSemantics.Target.openRunList [instr] state =
      InteractionSemantics.Target.openStepInstr instr state := by
  unfold InteractionSemantics.Target.openRunList Target.runListWith
  change
    Simulation.Interaction.bind
        (InteractionSemantics.Target.openStepInstr instr state)
        Simulation.Interaction.pure =
      InteractionSemantics.Target.openStepInstr instr state
  exact Simulation.Interaction.bind_pure _

theorem open_run_push_jump (dest : Nat) (state : EVMState) :
    InteractionSemantics.Target.openRunList
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state =
      .done (.ok (Source.jumpPc dest state)) := by
  unfold InteractionSemantics.Target.openRunList Target.runListWith
    InteractionSemantics.Target.openStepInstr Target.stepInstrWith
  rfl

theorem open_run_push_jumpi (dest : Nat) (state : EVMState) :
    InteractionSemantics.Target.openRunList
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state =
      .done
        (match state.stack.pop with
        | some (stack, cond) =>
            .ok
              { state with
                pc :=
                  if cond != EvmYul.UInt256.ofNat 0 then
                    EvmYul.UInt256.ofNat dest
                  else
                    Source.jumpiFallthroughPc state
                stack := stack }
        | none => .error .StackUnderflow) := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons cond rest => rfl

theorem openRunListResult_single (instr : TargetInstr) (state : EVMState) :
    InteractionSemantics.Target.openRunListResult [instr] state =
      InteractionSemantics.Target.openStepInstrResult instr state := by
  unfold InteractionSemantics.Target.openRunListResult
    Target.runListResultWith
  change
    Simulation.Interaction.bind
        (InteractionSemantics.Target.openStepInstrResult instr state)
        (fun result =>
          match result with
          | .running state' =>
              Simulation.Interaction.pure
                (Error := EVMException) (.running state')
          | .halted halt =>
              Simulation.Interaction.pure
                (Error := EVMException) (.halted halt)) =
      InteractionSemantics.Target.openStepInstrResult instr state
  have hContinuation :
      (fun result : StepResult =>
        match result with
        | .running state' =>
            Simulation.Interaction.pure
              (Error := EVMException) (.running state')
        | .halted halt =>
            Simulation.Interaction.pure
              (Error := EVMException) (.halted halt)) =
        (Simulation.Interaction.pure (Error := EVMException) :
          StepResult → InteractionSemantics.OpenStepResult) := by
    funext result
    cases result <;> rfl
  rw [hContinuation]
  exact Simulation.Interaction.bind_pure _

theorem target_openRunNResult_single_of_fetch
    {target : TargetProgram} {state : EVMState} {instr : TargetInstr}
    (hFetch : TargetProgram.fetch target state.pc.toNat = some instr) :
    InteractionSemantics.Target.openRunNResult target 1 state =
      InteractionSemantics.Target.openRunListResult [instr] state := by
  rw [openRunListResult_single]
  unfold InteractionSemantics.Target.openRunNResult
    Assembly.Target.runNResultWith Assembly.Control.runNResultWith
    Assembly.Target.stepResultWith
  rw [hFetch]
  change
    Simulation.Interaction.bind
        (InteractionSemantics.Target.openStepInstrResult instr state)
        (fun result =>
          match result with
          | .running state' =>
              Simulation.Interaction.pure
                (Error := EVMException) (.running state')
          | .halted halt =>
              Simulation.Interaction.pure
                (Error := EVMException) (.halted halt)) =
      InteractionSemantics.Target.openStepInstrResult instr state
  have hContinuation :
      (fun result : StepResult =>
        match result with
        | .running state' =>
            Simulation.Interaction.pure
              (Error := EVMException) (.running state')
        | .halted halt =>
            Simulation.Interaction.pure
              (Error := EVMException) (.halted halt)) =
        (Simulation.Interaction.pure (Error := EVMException) :
          StepResult → InteractionSemantics.OpenStepResult) := by
    funext result
    cases result <;> rfl
  rw [hContinuation]
  exact Simulation.Interaction.bind_pure _

theorem target_openRunNResult_push_jump_of_fetch
    {target : TargetProgram} {state : EVMState} {dest : Nat}
    (hFetchPush :
      TargetProgram.fetch target state.pc.toNat =
        some (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)))
    (hFetchJump :
      TargetProgram.fetch target (state.pc.toNat + Instr.push32Size) =
        some TargetInstr.jump)
    (hNoOverflow :
      state.pc.toNat + Instr.push32Size < EvmYul.UInt256.size) :
    InteractionSemantics.Target.openRunNResult target 2 state =
      InteractionSemantics.Target.openRunListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state := by
  let post :=
    state.replaceStackAndIncrPC
      (state.stack.push (EvmYul.UInt256.ofNat dest)) (pcΔ := 33)
  have hPostPc :
      post.pc.toNat = state.pc.toNat + 33 :=
    Preservation.replaceStackAndIncrPC_pc_toNat_of_no_overflow
      (state := state)
      (stack := state.stack.push (EvmYul.UInt256.ofNat dest))
      (pcΔ := 33) (by simpa [Instr.push32Size] using hNoOverflow)
  have hFetchJump' :
      TargetProgram.fetch target post.pc.toNat =
        some TargetInstr.jump := by
    rw [hPostPc]
    simpa [Instr.push32Size] using hFetchJump
  have hPush :
      InteractionSemantics.Target.openStepInstrResult
          (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)) state =
        .done (.ok (.running post)) := by
    rfl
  calc
    InteractionSemantics.Target.openRunNResult target 2 state =
        InteractionSemantics.Target.openRunNResult target 1 post := by
      change
        (do
          let result ←
            InteractionSemantics.Target.openStepResult target state
          match result with
          | .running state' =>
              InteractionSemantics.Target.openRunNResult target 1 state'
          | .halted halt =>
              pure (.halted halt)) =
          InteractionSemantics.Target.openRunNResult target 1 post
      unfold InteractionSemantics.Target.openStepResult
        Assembly.Target.stepResultWith
      rw [hFetchPush]
      simp only [hPush, Simulation.Interaction.bind_done_ok]
      rfl
    _ =
        InteractionSemantics.Target.openRunListResult
          [TargetInstr.jump] post :=
      target_openRunNResult_single_of_fetch hFetchJump'
    _ =
        InteractionSemantics.Target.openRunListResult
          [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
          state := by
      change
        InteractionSemantics.Target.openRunListResult
            [TargetInstr.jump] post =
          (do
            let result ←
              InteractionSemantics.Target.openStepInstrResult
                (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)) state
            match result with
            | .running state' =>
                InteractionSemantics.Target.openRunListResult
                  [TargetInstr.jump] state'
            | .halted halt =>
                pure (.halted halt))
      simp only [hPush, Simulation.Interaction.bind_done_ok]
      rfl

theorem target_openRunNResult_push_jumpi_of_fetch
    {target : TargetProgram} {state : EVMState} {dest : Nat}
    (hFetchPush :
      TargetProgram.fetch target state.pc.toNat =
        some (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)))
    (hFetchJumpi :
      TargetProgram.fetch target (state.pc.toNat + Instr.push32Size) =
        some TargetInstr.jumpi)
    (hNoOverflow :
      state.pc.toNat + Instr.push32Size < EvmYul.UInt256.size) :
    InteractionSemantics.Target.openRunNResult target 2 state =
      InteractionSemantics.Target.openRunListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state := by
  let post :=
    state.replaceStackAndIncrPC
      (state.stack.push (EvmYul.UInt256.ofNat dest)) (pcΔ := 33)
  have hPostPc :
      post.pc.toNat = state.pc.toNat + 33 :=
    Preservation.replaceStackAndIncrPC_pc_toNat_of_no_overflow
      (state := state)
      (stack := state.stack.push (EvmYul.UInt256.ofNat dest))
      (pcΔ := 33) (by simpa [Instr.push32Size] using hNoOverflow)
  have hFetchJumpi' :
      TargetProgram.fetch target post.pc.toNat =
        some TargetInstr.jumpi := by
    rw [hPostPc]
    simpa [Instr.push32Size] using hFetchJumpi
  have hPush :
      InteractionSemantics.Target.openStepInstrResult
          (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)) state =
        .done (.ok (.running post)) := by
    rfl
  calc
    InteractionSemantics.Target.openRunNResult target 2 state =
        InteractionSemantics.Target.openRunNResult target 1 post := by
      change
        (do
          let result ←
            InteractionSemantics.Target.openStepResult target state
          match result with
          | .running state' =>
              InteractionSemantics.Target.openRunNResult target 1 state'
          | .halted halt =>
              pure (.halted halt)) =
          InteractionSemantics.Target.openRunNResult target 1 post
      unfold InteractionSemantics.Target.openStepResult
        Assembly.Target.stepResultWith
      rw [hFetchPush]
      simp only [hPush, Simulation.Interaction.bind_done_ok]
      rfl
    _ =
        InteractionSemantics.Target.openRunListResult
          [TargetInstr.jumpi] post :=
      target_openRunNResult_single_of_fetch hFetchJumpi'
    _ =
        InteractionSemantics.Target.openRunListResult
          [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
          state := by
      change
        InteractionSemantics.Target.openRunListResult
            [TargetInstr.jumpi] post =
          (do
            let result ←
              InteractionSemantics.Target.openStepInstrResult
                (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)) state
            match result with
            | .running state' =>
                InteractionSemantics.Target.openRunListResult
                  [TargetInstr.jumpi] state'
            | .halted halt =>
                pure (.halted halt))
      simp only [hPush, Simulation.Interaction.bind_done_ok]
      rfl

theorem open_run_push_jump_result (dest : Nat) (state : EVMState) :
    InteractionSemantics.Target.openRunListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state =
      .done (.ok (.running (Source.jumpPc dest state))) := by
  unfold InteractionSemantics.Target.openRunListResult
    Target.runListResultWith
    InteractionSemantics.Target.openStepInstrResult
    Target.stepInstrResultWith
    InteractionSemantics.Target.openStepInstr
    Target.stepInstrWith
  rfl

theorem open_run_push_jumpi_result (dest : Nat) (state : EVMState) :
    InteractionSemantics.Target.openRunListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state =
      .done
        (match state.stack.pop with
        | some (stack, cond) =>
            .ok
              (.running
                { state with
                  pc :=
                    if cond != EvmYul.UInt256.ofNat 0 then
                      EvmYul.UInt256.ofNat dest
                    else
                      Source.jumpiFallthroughPc state
                  stack := stack })
        | none => .error .StackUnderflow) := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons cond rest => rfl

/--
Resolving and emitting one Assembly instruction preserves its complete open
interaction tree. In particular, an emitted CALL/CREATE-family primitive
exposes the same request and the same continuation for every shared answer.
-/
theorem stepAt_emit_open_eq
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    (hEmit : emitInstr? program pc instr = some located) :
    InteractionSemantics.Source.openStepAt program pc instr state =
      InteractionSemantics.Target.openRunList
        (located.map LocatedTarget.instr) state := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAt program pc (.label name) state =
          InteractionSemantics.Target.openRunList
            [TargetInstr.jumpdest] state
      rw [openRunList_single]
      rfl
  | prim op =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAt program pc (.prim op) state =
          InteractionSemantics.Target.openRunList
            [TargetInstr.prim op] state
      rw [openRunList_single]
      rfl
  | push value =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAt program pc (.push value) state =
          InteractionSemantics.Target.openRunList
            [TargetInstr.push32 value] state
      rw [openRunList_single]
      rfl
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            InteractionSemantics.Source.openStepAt program pc
                (.jump target) state =
              InteractionSemantics.Target.openRunList
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jump]
                state
          rw [open_run_push_jump]
          simp [InteractionSemantics.Source.openStepAt, Source.stepAt,
            hDest, Source.jumpPc]
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            InteractionSemantics.Source.openStepAt program pc
                (.jumpi target) state =
              InteractionSemantics.Target.openRunList
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jumpi]
                state
          rw [open_run_push_jumpi]
          simp [InteractionSemantics.Source.openStepAt, Source.stepAt, hDest]
          rfl

theorem stepAt_emit_open_rel
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    (hEmit : emitInstr? program pc instr = some located) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openStepAt program pc instr state)
      (InteractionSemantics.Target.openRunList
        (located.map LocatedTarget.instr) state) := by
  rw [stepAt_emit_open_eq hEmit]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

theorem stepAt_emit_open_result_eq
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    (hEmit : emitInstr? program pc instr = some located) :
    InteractionSemantics.Source.openStepAtResult program pc instr state =
      InteractionSemantics.Target.openRunListResult
        (located.map LocatedTarget.instr) state := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAtResult program pc
            (.label name) state =
          InteractionSemantics.Target.openRunListResult
            [TargetInstr.jumpdest] state
      rw [openRunListResult_single]
      rfl
  | prim op =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAtResult program pc
            (.prim op) state =
          InteractionSemantics.Target.openRunListResult
            [TargetInstr.prim op] state
      rw [openRunListResult_single]
      rfl
  | push value =>
      simp [emitInstr?] at hEmit
      subst located
      change
        InteractionSemantics.Source.openStepAtResult program pc
            (.push value) state =
          InteractionSemantics.Target.openRunListResult
            [TargetInstr.push32 value] state
      rw [openRunListResult_single]
      rfl
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            InteractionSemantics.Source.openStepAtResult program pc
                (.jump target) state =
              InteractionSemantics.Target.openRunListResult
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jump]
                state
          rw [open_run_push_jump_result]
          simp [InteractionSemantics.Source.openStepAtResult,
            InteractionSemantics.Source.openStepAt, Source.stepAt,
            Instr.haltKind?, hDest, Source.jumpPc]
          change Simulation.Interaction.bind _ _ = _
          rfl
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst located
          change
            InteractionSemantics.Source.openStepAtResult program pc
                (.jumpi target) state =
              InteractionSemantics.Target.openRunListResult
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
                  TargetInstr.jumpi]
                state
          rw [open_run_push_jumpi_result]
          simp [InteractionSemantics.Source.openStepAtResult,
            InteractionSemantics.Source.openStepAt, Source.stepAt,
            Instr.haltKind?, hDest]
          change Simulation.Interaction.bind _ _ = _
          cases hPop : state.stack.pop <;> simp [hPop]
          change Simulation.Interaction.pure _ = _
          rfl

theorem stepAt_emit_open_result_rel
    {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState}
    (hEmit : emitInstr? program pc instr = some located) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openStepAtResult program pc instr state)
      (InteractionSemantics.Target.openRunListResult
        (located.map LocatedTarget.instr) state) := by
  rw [stepAt_emit_open_result_eq hEmit]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

/--
Executing one emitted source instruction through resolved target fetches is
exactly the same open interaction as executing its emitted block directly.
-/
theorem target_openRunNResult_eq_openRunList_of_emitInstr?
    {program : Program} {target : TargetProgram}
    {state : EVMState} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hSafe : Preservation.TargetBlockPcSafe instr state) :
    InteractionSemantics.Target.openRunNResult
        target emitted.length state =
      InteractionSemantics.Target.openRunListResult
        (emitted.map LocatedTarget.instr) state := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .label name)
            (emitted := [{ pc := pc, instr := TargetInstr.jumpdest }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_openRunNResult_single_of_fetch hFetch
  | prim op =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .prim op)
            (emitted := [{ pc := pc, instr := TargetInstr.prim op }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_openRunNResult_single_of_fetch hFetch
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      rcases
          assemble?_fetch_first_of_instrAtPc
            (program := program) (target := target)
            (query := state.pc.toNat) (pc := pc)
            (instr := .push value)
            (emitted := [{ pc := pc, instr := TargetInstr.push32 value }])
            hAsm hAt (by simp [emitInstr?]) with
        ⟨targetInstr, restEmitted, hFirst, hFetch⟩
      cases hFirst
      exact target_openRunNResult_single_of_fetch hFetch
  | jump targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          rcases
              assemble?_fetch_first_of_instrAtPc
                (program := program) (target := target)
                (query := state.pc.toNat) (pc := pc)
                (instr := .jump targetLabel)
                (emitted :=
                  [ { pc := pc,
                      instr := TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest) }
                  , { pc := pc + Instr.push32Size,
                      instr := TargetInstr.jump }
                  ])
                hAsm hAt (by simp [emitInstr?, hDest]) with
            ⟨targetInstr, restEmitted, hFirst, hFetchPush⟩
          cases hFirst
          have hFetchJump :
              TargetProgram.fetch target
                  (state.pc.toNat + Instr.push32Size) =
                some TargetInstr.jump :=
            assemble?_fetch_jump_second_of_instrAtPc
              (program := program) (targetProgram := target)
              (query := state.pc.toNat) (pc := state.pc.toNat)
              (target := targetLabel)
              (emitted :=
                [ { pc := state.pc.toNat,
                    instr := TargetInstr.push32
                      (EvmYul.UInt256.ofNat dest) }
                , { pc := state.pc.toNat + Instr.push32Size,
                    instr := TargetInstr.jump }
                ])
              hAsm hAt (by simp [emitInstr?, hDest])
          have hNoOverflow :
              state.pc.toNat + Instr.push32Size <
                EvmYul.UInt256.size := by
            simpa [Preservation.TargetBlockPcSafe] using hSafe
          exact
            target_openRunNResult_push_jump_of_fetch
              hFetchPush hFetchJump hNoOverflow
  | jumpi targetLabel =>
      cases hDest : Program.labelPc program targetLabel with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          rcases
              assemble?_fetch_first_of_instrAtPc
                (program := program) (target := target)
                (query := state.pc.toNat) (pc := pc)
                (instr := .jumpi targetLabel)
                (emitted :=
                  [ { pc := pc,
                      instr := TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest) }
                  , { pc := pc + Instr.push32Size,
                      instr := TargetInstr.jumpi }
                  ])
                hAsm hAt (by simp [emitInstr?, hDest]) with
            ⟨targetInstr, restEmitted, hFirst, hFetchPush⟩
          cases hFirst
          have hFetchJumpi :
              TargetProgram.fetch target
                  (state.pc.toNat + Instr.push32Size) =
                some TargetInstr.jumpi :=
            assemble?_fetch_jumpi_second_of_instrAtPc
              (program := program) (targetProgram := target)
              (query := state.pc.toNat) (pc := state.pc.toNat)
              (target := targetLabel)
              (emitted :=
                [ { pc := state.pc.toNat,
                    instr := TargetInstr.push32
                      (EvmYul.UInt256.ofNat dest) }
                , { pc := state.pc.toNat + Instr.push32Size,
                    instr := TargetInstr.jumpi }
                ])
              hAsm hAt (by simp [emitInstr?, hDest])
          have hNoOverflow :
              state.pc.toNat + Instr.push32Size <
                EvmYul.UInt256.size := by
            simpa [Preservation.TargetBlockPcSafe] using hSafe
          exact
            target_openRunNResult_push_jumpi_of_fetch
              hFetchPush hFetchJumpi hNoOverflow

/--
One concrete branch through emitted-block execution. The transcript is the
external world's exact ordered query/answer history; the trace stores only
pass-owned block decomposition facts.
-/
inductive OpenBlockTraceResult
    (program : Program) (target : TargetProgram) :
    Nat → EVMState → Simulation.Interaction.Transcript → StepResult → Prop where
  | done (state : EVMState) :
      OpenBlockTraceResult program target 0 state [] (.running state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {headTranscript restTranscript : Simulation.Interaction.Transcript}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Simulation.Interaction.Executes
          (InteractionSemantics.Target.openRunListResult
            (emitted.map LocatedTarget.instr) state)
          headTranscript (.ok (.running mid)))
      (hRest :
        OpenBlockTraceResult program target fuel mid restTranscript result) :
      OpenBlockTraceResult program target (fuel + 1) state
        (headTranscript ++ restTranscript) result
  | stepHalted {fuel : Nat} {state : EVMState}
      {transcript : Simulation.Interaction.Transcript} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Simulation.Interaction.Executes
          (InteractionSemantics.Target.openRunListResult
            (emitted.map LocatedTarget.instr) state)
          transcript (.ok (.halted halt))) :
      OpenBlockTraceResult program target (fuel + 1) state transcript
        (.halted halt)

namespace OpenBlockTraceResult

/--
Every emitted-block branch is realized by the ordinary fetched target runner.
The target instruction fuel is derived internally from emitted block lengths.
-/
theorem target_executes_exists
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hTrace :
      OpenBlockTraceResult program target fuel state transcript result)
    (hLen : Program.byteLength program < EvmYul.UInt256.size) :
    ∃ targetFuel,
      Simulation.Interaction.Executes
        (InteractionSemantics.Target.openRunNResult
          target targetFuel state)
        transcript (.ok result) := by
  induction hTrace with
  | done state =>
      refine ⟨0, ?_⟩
      change
        Simulation.Interaction.Executes
          (.done (.ok (StepResult.running state))) []
          (.ok (StepResult.running state))
      exact Simulation.Interaction.Executes.done _
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid headTranscript restTranscript result
        pc instr emitted before after
      have hSafe : Preservation.TargetBlockPcSafe instr state :=
        Preservation.targetBlockPcSafe_of_instrAtPc_of_byteLength_lt
          hAt hLen
      have hHead :
          Simulation.Interaction.Executes
            (InteractionSemantics.Target.openRunNResult
              target emitted.length state)
            headTranscript (.ok (.running mid)) := by
        rw [target_openRunNResult_eq_openRunList_of_emitInstr?
          hAsm hAt hEmit hSafe]
        exact hRun
      rcases ih with ⟨tailFuel, hTail⟩
      refine ⟨emitted.length + tailFuel, ?_⟩
      rw [InteractionSemantics.Target.openRunNResult_add]
      exact Simulation.Interaction.Executes.bind_ok hHead hTail
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state transcript halt pc instr emitted before after
      have hSafe : Preservation.TargetBlockPcSafe instr state :=
        Preservation.targetBlockPcSafe_of_instrAtPc_of_byteLength_lt
          hAt hLen
      refine ⟨emitted.length, ?_⟩
      rw [target_openRunNResult_eq_openRunList_of_emitInstr?
        hAsm hAt hEmit hSafe]
      exact hRun

end OpenBlockTraceResult

theorem assemble_compiled_openStepResult_executes
    {program : Program} {target : TargetProgram}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hExec :
      Simulation.Interaction.Executes
        (InteractionSemantics.Compiled.openStepResult program state)
        transcript (.ok result)) :
    ∃ pc instr emitted before after,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
          target.code = before ++ emitted ++ after ∧
            Simulation.Interaction.Executes
              (InteractionSemantics.Target.openRunListResult
                (emitted.map LocatedTarget.instr) state)
              transcript (.ok result) := by
  unfold InteractionSemantics.Compiled.openStepResult
    Assembly.Compiled.stepResultWith at hExec
  cases hCurrent : emitCurrent? program state with
  | none =>
      rw [hCurrent] at hExec
      change
        Simulation.Interaction.Executes
          (.done (.error (.InvalidInstruction : EVMException)))
          transcript (.ok result) at hExec
      cases hExec
  | some code =>
      rw [hCurrent] at hExec
      unfold emitCurrent? at hCurrent
      cases hAt : Program.instrAtPc program state.pc.toNat with
      | none =>
          simp [hAt] at hCurrent
      | some current =>
          rcases current with ⟨pc, instr⟩
          simp only [hAt, Option.bind_some] at hCurrent
          cases hEmit : emitInstr? program pc instr with
          | none =>
              simp [hEmit] at hCurrent
          | some emitted =>
              simp [hEmit] at hCurrent
              subst code
              rcases Preservation.assemble_covers_current_pc hAsm hAt with
                ⟨before, assembled, after, hTargetBlock, hAssembled⟩
              rw [hEmit] at hAssembled
              cases hAssembled
              exact
                ⟨pc, instr, emitted, before, after, rfl, hEmit,
                  hTargetBlock, hExec⟩

theorem source_openStep_eq_compiled (program : Program) (state : EVMState) :
    InteractionSemantics.Source.openStep program state =
      InteractionSemantics.Compiled.openStep program state := by
  unfold InteractionSemantics.Source.openStep
    InteractionSemantics.Compiled.openStep
    Assembly.Source.stepWith Assembly.Compiled.stepWith emitCurrent?
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt]
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp only [hAt]
      cases hEmit : emitInstr? program pc instr with
      | none =>
          cases instr with
          | label name =>
              simp [emitInstr?] at hEmit
          | prim op =>
              simp [emitInstr?] at hEmit
          | push value =>
              simp [emitInstr?] at hEmit
          | jump target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [hEmit, InteractionSemantics.Source.openStepAt,
                    Assembly.Source.stepAt, Assembly.Source.invalid,
                    emitInstr?, hDest, Simulation.Interaction.error]
                  change
                    Simulation.Interaction.error
                        (Error := EVMException) (Result := EVMState)
                        .InvalidInstruction =
                      Simulation.Interaction.error
                        (Error := EVMException) (Result := EVMState)
                        .InvalidInstruction
                  rfl
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
          | jumpi target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [hEmit, InteractionSemantics.Source.openStepAt,
                    Assembly.Source.stepAt, Assembly.Source.invalid,
                    emitInstr?, hDest, Simulation.Interaction.error]
                  change
                    Simulation.Interaction.error
                        (Error := EVMException) (Result := EVMState)
                        .InvalidInstruction =
                      Simulation.Interaction.error
                        (Error := EVMException) (Result := EVMState)
                        .InvalidInstruction
                  rfl
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
      | some located =>
          simpa [hEmit] using stepAt_emit_open_eq hEmit

theorem source_openStep_rel_compiled (program : Program) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openStep program state)
      (InteractionSemantics.Compiled.openStep program state) := by
  rw [source_openStep_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

theorem source_openStepResult_eq_compiled
    (program : Program) (state : EVMState) :
    InteractionSemantics.Source.openStepResult program state =
      InteractionSemantics.Compiled.openStepResult program state := by
  unfold InteractionSemantics.Source.openStepResult
    InteractionSemantics.Compiled.openStepResult
    Assembly.Source.stepResultWith Assembly.Compiled.stepResultWith
    emitCurrent?
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt]
  | some current =>
      rcases current with ⟨pc, instr⟩
      simp only [hAt]
      cases hEmit : emitInstr? program pc instr with
      | none =>
          cases instr with
          | label name =>
              simp [emitInstr?] at hEmit
          | prim op =>
              simp [emitInstr?] at hEmit
          | push value =>
              simp [emitInstr?] at hEmit
          | jump target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [hEmit, InteractionSemantics.Source.openStepAtResult,
                    InteractionSemantics.Source.openStepAt,
                    Assembly.Source.stepAt, Assembly.Source.invalid,
                    Instr.haltKind?, emitInstr?, hDest,
                    Simulation.Interaction.error,
                    Simulation.Interaction.bind]
                  change
                    Simulation.Interaction.error
                        (Error := EVMException) (Result := StepResult)
                        .InvalidInstruction =
                      Simulation.Interaction.error
                        (Error := EVMException) (Result := StepResult)
                        .InvalidInstruction
                  rfl
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
          | jumpi target =>
              cases hDest : Program.labelPc program target with
              | none =>
                  simp [hEmit, InteractionSemantics.Source.openStepAtResult,
                    InteractionSemantics.Source.openStepAt,
                    Assembly.Source.stepAt, Assembly.Source.invalid,
                    Instr.haltKind?, emitInstr?, hDest,
                    Simulation.Interaction.error,
                    Simulation.Interaction.bind]
                  change
                    Simulation.Interaction.error
                        (Error := EVMException) (Result := StepResult)
                        .InvalidInstruction =
                      Simulation.Interaction.error
                        (Error := EVMException) (Result := StepResult)
                        .InvalidInstruction
                  rfl
              | some dest =>
                  simp [emitInstr?, hDest] at hEmit
      | some located =>
          simpa [hEmit] using stepAt_emit_open_result_eq hEmit

theorem source_openStepResult_rel_compiled
    (program : Program) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openStepResult program state)
      (InteractionSemantics.Compiled.openStepResult program state) := by
  rw [source_openStepResult_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

/--
Whole-program open Assembly execution is exactly the execution of the target
instruction blocks selected by the existing emitter. Both sides use the shared
control kernel, so the equality covers every request continuation rather than
only a particular replay strategy.
-/
theorem source_openRunN_eq_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    InteractionSemantics.Source.openRunN program fuel state =
      InteractionSemantics.Compiled.openRunN program fuel state := by
  unfold InteractionSemantics.Source.openRunN
    InteractionSemantics.Compiled.openRunN
  have hStep :
      InteractionSemantics.Source.openStep program =
        InteractionSemantics.Compiled.openStep program := by
    funext current
    exact source_openStep_eq_compiled program current
  rw [hStep]

theorem source_openRunN_rel_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openRunN program fuel state)
      (InteractionSemantics.Compiled.openRunN program fuel state) := by
  rw [source_openRunN_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

theorem source_openRunNResult_eq_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    InteractionSemantics.Source.openRunNResult program fuel state =
      InteractionSemantics.Compiled.openRunNResult program fuel state := by
  unfold InteractionSemantics.Source.openRunNResult
    InteractionSemantics.Compiled.openRunNResult
  have hStep :
      InteractionSemantics.Source.openStepResult program =
        InteractionSemantics.Compiled.openStepResult program := by
    funext current
    exact source_openStepResult_eq_compiled program current
  rw [hStep]

theorem source_openRunNResult_rel_compiled
    (program : Program) (fuel : Nat) (state : EVMState) :
    Simulation.Interaction.Rel Eq
      (InteractionSemantics.Source.openRunNResult program fuel state)
      (InteractionSemantics.Compiled.openRunNResult program fuel state) := by
  rw [source_openRunNResult_eq_compiled]
  apply Simulation.Interaction.Rel.refl
  intro result
  rfl

/--
Every concrete source branch induces a pass-owned trace of the emitted
instruction blocks. The structural relation supplies the same external-world
answers; the trace records only the assembler decomposition needed by the
adjacent target boundary.
-/
theorem assemble_source_openRunNResult_block_trace
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hExec :
      Simulation.Interaction.Executes
        (InteractionSemantics.Source.openRunNResult program fuel state)
        transcript (.ok result)) :
    OpenBlockTraceResult program target fuel state transcript result := by
  obtain ⟨compiledOutcome, hCompiled, hOutcome⟩ :=
    Simulation.Interaction.Rel.executes
      (source_openRunNResult_rel_compiled program fuel state) hExec
  cases hOutcome
  induction fuel generalizing state transcript result with
  | zero =>
      change
        Simulation.Interaction.Executes
          (.done (.ok (StepResult.running state)))
          transcript (.ok result) at hCompiled
      cases hCompiled
      exact OpenBlockTraceResult.done state
  | succ fuel ih =>
      change
        Simulation.Interaction.Executes
          (Simulation.Interaction.bind
            (InteractionSemantics.Compiled.openStepResult program state)
            (fun stepResult =>
              match stepResult with
              | .running mid =>
                  InteractionSemantics.Compiled.openRunNResult
                    program fuel mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt)))
          transcript (.ok result) at hCompiled
      rcases Simulation.Interaction.Executes.bind_cases hCompiled with
        hError | hOk
      · rcases hError with ⟨err, hOutcome, hStep⟩
        cases hOutcome
      · rcases hOk with
          ⟨stepResult, headTranscript, restTranscript,
            hTranscript, hStep, hRest⟩
        rcases assemble_compiled_openStepResult_executes hAsm hStep with
          ⟨pc, instr, emitted, before, after,
            hAt, hEmit, hTargetBlock, hBlock⟩
        subst transcript
        cases stepResult with
        | running mid =>
            have hSourceRest :
                Simulation.Interaction.Executes
                  (InteractionSemantics.Source.openRunNResult
                    program fuel mid)
                  restTranscript (.ok result) := by
              rw [source_openRunNResult_eq_compiled]
              exact hRest
            exact
              OpenBlockTraceResult.stepRunning
                hAt hEmit hTargetBlock hBlock (ih hSourceRest hRest)
        | halted halt =>
            change
              Simulation.Interaction.Executes
                (.done (.ok (StepResult.halted halt)))
                restTranscript (.ok result) at hRest
            cases hRest
            simpa using
              (OpenBlockTraceResult.stepHalted
                (fuel := fuel) hAt hEmit hTargetBlock hBlock)

/--
Compiler-artifact form of the whole-program open Assembly theorem.

The generated target program is connected to the block interpreter by the
existing emitter equation; no generated proof object is accepted as a premise.
-/
theorem compile_openRunNResult_block_rel
    {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target)
    (fuel : Nat) (state : EVMState) :
    Accepted program ∧
      ∃ code,
        emit? program = some code ∧
          target.code = code ∧
            Simulation.Interaction.Rel Eq
              (InteractionSemantics.Source.openRunNResult
                program fuel state)
              (InteractionSemantics.Compiled.openRunNResult
                program fuel state) := by
  refine ⟨Preservation.compile?_some_accepted hCompile, ?_⟩
  obtain ⟨code, hEmit, hCode⟩ :=
    Preservation.assemble_emits_code
      (Preservation.compile?_some_assemble hCompile)
  exact
    ⟨code, hEmit, hCode,
      source_openRunNResult_rel_compiled program fuel state⟩

/--
Concrete-branch form of Assembly compiler correctness.

For every branch selected by an external world on the accepted source
program, the fetched target program realizes the exact same dependent
query/answer transcript and terminal result. The target instruction budget is
derived from the emitted blocks rather than supplied as compiler evidence.
-/
theorem compile_openRunNResult_target_executes
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hLen : Program.byteLength program < EvmYul.UInt256.size)
    (hExec :
      Simulation.Interaction.Executes
        (InteractionSemantics.Source.openRunNResult program fuel state)
        transcript (.ok result)) :
    Accepted program ∧
      ∃ targetFuel,
        Simulation.Interaction.Executes
          (InteractionSemantics.Target.openRunNResult
            target targetFuel state)
          transcript (.ok result) := by
  have hAsm : assemble? program = some target :=
    Preservation.compile?_some_assemble hCompile
  refine ⟨Preservation.compile?_some_accepted hCompile, ?_⟩
  exact
    OpenBlockTraceResult.target_executes_exists
      hAsm
      (assemble_source_openRunNResult_block_trace hAsm hExec)
      hLen

end InteractionPreservation
end Assembly
end EvmCompiler
