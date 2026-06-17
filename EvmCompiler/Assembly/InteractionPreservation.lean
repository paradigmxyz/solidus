import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.Assembly.Preservation

namespace EvmCompiler
namespace Assembly
namespace InteractionPreservation

open InteractionSemantics

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

end InteractionPreservation
end Assembly
end EvmCompiler
