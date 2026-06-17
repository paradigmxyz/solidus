import EvmCompiler.Assembly.Accepted
import EvmCompiler.Assembly.Semantics

namespace EvmCompiler
namespace Assembly

namespace Preservation

theorem run_push_jump (dest : Nat) (state : EVMState) :
    Target.runList
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state =
      .ok (Source.jumpPc dest state) := by
  rfl

theorem run_push_jumpi (dest : Nat) (state : EVMState) :
    Target.runList
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state =
      match state.stack.pop with
      | some (stack, cond) =>
          .ok
            { state with
              pc :=
                if cond != EvmYul.UInt256.ofNat 0 then
                  EvmYul.UInt256.ofNat dest
                else
                  Source.jumpiFallthroughPc state
              stack := stack
            }
      | none =>
          .error .StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
  cases stack with
  | nil => rfl
  | cons _ _ => rfl

theorem runList_single (instr : TargetInstr) (state : EVMState) :
    Target.runList [instr] state = Target.stepInstr instr state := by
  change
    Target.runListWith Target.stepInstr [instr] state =
      Target.stepInstr instr state
  cases h : Target.stepInstr instr state with
  | error e =>
      simp [Target.runListWith, h]
  | ok state' =>
      simp [Target.runListWith, h]

theorem run_push_jump_result (dest : Nat) (state : EVMState) :
    Target.runListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
        state =
      .ok (.running (Source.jumpPc dest state)) := by
  rfl

theorem run_push_jumpi_result (dest : Nat) (state : EVMState) :
    Target.runListResult
        [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
        state =
      match state.stack.pop with
      | some (stack, cond) =>
          .ok
            (.running
              { state with
                pc :=
                  if cond != EvmYul.UInt256.ofNat 0 then
                    EvmYul.UInt256.ofNat dest
                  else
                    Source.jumpiFallthroughPc state
                stack := stack
              })
      | none =>
          .error .StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
  cases stack with
  | nil => rfl
  | cons _ _ => rfl

theorem runListResult_single (instr : TargetInstr) (state : EVMState) :
    Target.runListResult [instr] state = Target.stepInstrResult instr state := by
  change
    Target.runListResultWith Target.stepInstrResult [instr] state =
      Target.stepInstrResult instr state
  cases h : Target.stepInstrResult instr state with
  | error e =>
      simp [Target.runListResultWith, h]
  | ok result =>
      cases result <;> simp [Target.runListResultWith, h]

theorem stepAt_emit_sound {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state sourceState : EVMState}
    (hEmit : emitInstr? program pc instr = some located)
    (hStep : Source.stepAt program pc instr state = .ok sourceState) :
    Target.runList (located.map LocatedTarget.instr) state = .ok sourceState := by
  cases instr with
  | label name =>
      simp [emitInstr?, Source.stepAt] at hEmit hStep
      subst located
      simpa [runList_single] using hStep
  | prim op =>
      simp [emitInstr?, Source.stepAt] at hEmit hStep
      subst located
      simpa [runList_single] using hStep
  | push value =>
      simp [emitInstr?, Source.stepAt] at hEmit hStep
      subst located
      simpa [runList_single] using hStep
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest, Source.stepAt, Source.jumpPc] at hEmit hStep
          subst located
          change
            Target.runList
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
                state =
              .ok sourceState
          rw [run_push_jump dest state]
          exact congrArg (fun result => Except.ok result) hStep
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest, Source.stepAt] at hEmit hStep
          subst located
          change
            Target.runList
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
                state =
              .ok sourceState
          rw [run_push_jumpi dest state]
          exact hStep

theorem stepAt_emit_result_sound {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc instr = some located)
    (hStep : Source.stepAtResult program pc instr state = .ok result) :
    Target.runListResult (located.map LocatedTarget.instr) state = .ok result := by
  cases instr with
  | label name =>
      simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hStep
      subst located
      simpa [runListResult_single] using hStep
  | prim op =>
      simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hStep
      subst located
      simpa [runListResult_single] using hStep
  | push value =>
      simp [emitInstr?, Source.stepAtResult, Source.stepAt] at hEmit hStep
      subst located
      simpa [runListResult_single] using hStep
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest, Source.stepAtResult, Source.stepAt,
            Source.jumpPc, Instr.haltKind?] at hEmit hStep
          subst located
          change
            Target.runListResult
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jump]
                state =
              .ok result
          rw [run_push_jump_result dest state]
          simpa [Source.jumpPc] using
            congrArg (fun r => (Except.ok r : Except EVMException StepResult)) hStep
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest, Source.stepAtResult, Source.stepAt,
            Instr.haltKind?] at hEmit hStep
          subst located
          change
            Target.runListResult
                [TargetInstr.push32 (EvmYul.UInt256.ofNat dest), TargetInstr.jumpi]
                state =
              .ok result
          rw [run_push_jumpi_result dest state]
          cases hPop : state.stack.pop with
          | none =>
              simp [hPop] at hStep
          | some pair =>
              cases pair with
              | mk stack cond =>
                  simp [hPop] at hStep ⊢
                  exact hStep

theorem stepAt_emit_projected_sound {program : Program} {pc : Nat} {instr : Instr}
    {located : List LocatedTarget} {state sourceState : EVMState}
    (hEmit : emitInstr? program pc instr = some located)
    (hStep : Source.stepAt program pc instr state = .ok sourceState) :
    ∃ targetState,
      Target.runList (located.map LocatedTarget.instr) state = .ok targetState ∧
        eraseGas targetState = eraseGas sourceState := by
  refine ⟨sourceState, ?_, rfl⟩
  exact stepAt_emit_sound hEmit hStep

theorem source_step_current_emit_result_sound {program : Program}
    {state : EVMState} {result : StepResult} {code : List TargetInstr}
    (hEmit : emitCurrent? program state = some code)
    (hStep : Source.stepResult program state = .ok result) :
    Target.runListResult code state = .ok result := by
  unfold emitCurrent? at hEmit
  unfold Source.stepResult at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hEmit
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hEmit hStep
          cases hEmitInstr : emitInstr? program pc instr with
          | none =>
              simp [hEmitInstr] at hEmit
          | some located =>
              simp [hEmitInstr] at hEmit
              subst code
              exact stepAt_emit_result_sound hEmitInstr hStep

theorem source_step_current_emit_sound {program : Program} {state sourceState : EVMState}
    {code : List TargetInstr}
    (hEmit : emitCurrent? program state = some code)
    (hStep : Source.step program state = .ok sourceState) :
        Target.runList code state = .ok sourceState := by
  unfold emitCurrent? at hEmit
  unfold Source.step at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hEmit
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hEmit hStep
          cases hEmitInstr : emitInstr? program pc instr with
          | none =>
              simp [hEmitInstr] at hEmit
          | some located =>
              simp [hEmitInstr] at hEmit
              subst code
              exact stepAt_emit_sound hEmitInstr hStep

theorem source_step_current_projected_sound {program : Program}
    {state sourceState : EVMState} {code : List TargetInstr}
    (hEmit : emitCurrent? program state = some code)
    (hStep : Source.step program state = .ok sourceState) :
    ∃ targetState,
      Target.runList code state = .ok targetState ∧
        eraseGas targetState = eraseGas sourceState := by
  refine ⟨sourceState, ?_, rfl⟩
  exact source_step_current_emit_sound hEmit hStep

theorem assemble_emits_code {program : Program} {target : TargetProgram}
    (hAsm : assemble? program = some target) :
    ∃ code, emit? program = some code ∧ target.code = code := by
  unfold assemble? at hAsm
  cases hEmit : emit? program with
  | none =>
      simp [hEmit] at hAsm
  | some code =>
      simp [hEmit] at hAsm
      cases hAsm
      exact ⟨code, rfl, rfl⟩

theorem emitFrom_block_for_instrAtPc {full suffix : Program}
    {base query pc : Nat} {instr : Instr} {code : List LocatedTarget}
    (hEmit : emitFrom? full suffix base = some code)
    (hAt : Program.instrAtPcFrom suffix base query = some (pc, instr)) :
    ∃ before emitted after,
      code = before ++ emitted ++ after ∧
        emitInstr? full pc instr = some emitted := by
  induction suffix generalizing base code with
  | nil =>
      simp [Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      unfold emitFrom? at hEmit
      cases hHere : emitInstr? full base head with
      | none =>
          simp [hHere] at hEmit
      | some here =>
          cases hThere : emitFrom? full rest (base + head.byteSize) with
          | none =>
              simp [hHere, hThere] at hEmit
          | some there =>
              simp [hHere, hThere] at hEmit
              cases hEmit
              by_cases hQuery : query = base
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                have hPair : (base, head) = (pc, instr) := by
                  simpa using hAt
                cases hPair
                exact ⟨[], here, there, rfl, hHere⟩
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                obtain ⟨before, emitted, after, hDecomp, hEmitInstr⟩ :=
                  ih hThere hAt
                exact
                  ⟨here ++ before, emitted, after,
                    by simp [hDecomp, List.append_assoc], hEmitInstr⟩

theorem emit_block_for_instrAtPc {program : Program}
    {query pc : Nat} {instr : Instr} {code : List LocatedTarget}
    (hEmit : emit? program = some code)
    (hAt : Program.instrAtPc program query = some (pc, instr)) :
    ∃ before emitted after,
      code = before ++ emitted ++ after ∧
        emitInstr? program pc instr = some emitted := by
  exact emitFrom_block_for_instrAtPc (full := program) (suffix := program)
    (base := 0) (query := query) hEmit hAt

theorem assemble_covers_current_pc {program : Program} {target : TargetProgram}
    {query pc : Nat} {instr : Instr}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program query = some (pc, instr)) :
    ∃ before emitted after,
      target.code = before ++ emitted ++ after ∧
        emitInstr? program pc instr = some emitted := by
  obtain ⟨code, hEmit, hTargetCode⟩ := assemble_emits_code hAsm
  obtain ⟨before, emitted, after, hDecomp, hEmitInstr⟩ :=
    emit_block_for_instrAtPc hEmit hAt
  exact ⟨before, emitted, after, hTargetCode.trans hDecomp, hEmitInstr⟩

theorem assemble_source_step_current_result_sound {program : Program}
    {target : TargetProgram} {state : EVMState} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hStep : Source.stepResult program state = .ok result) :
    ∃ pc instr emitted before after,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
        target.code = before ++ emitted ++ after ∧
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok result := by
  unfold Source.stepResult at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hStep
          obtain ⟨before, emitted, after, hTargetBlock, hEmitInstr⟩ :=
            assemble_covers_current_pc hAsm hAt
          exact
            ⟨pc, instr, emitted, before, after,
              rfl, hEmitInstr, hTargetBlock,
              stepAt_emit_result_sound hEmitInstr hStep⟩

theorem assemble_source_step_current_projected_sound {program : Program}
    {target : TargetProgram} {state sourceState : EVMState}
    (hAsm : assemble? program = some target)
    (hStep : Source.step program state = .ok sourceState) :
    ∃ pc instr emitted before after targetState,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
        target.code = before ++ emitted ++ after ∧
        Target.runList (emitted.map LocatedTarget.instr) state = .ok targetState ∧
        eraseGas targetState = eraseGas sourceState := by
  unfold Source.step at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hStep
          obtain ⟨before, emitted, after, hTargetBlock, hEmitInstr⟩ :=
            assemble_covers_current_pc hAsm hAt
          obtain ⟨targetState, hRun, hErase⟩ :=
            stepAt_emit_projected_sound hEmitInstr hStep
          exact
            ⟨pc, instr, emitted, before, after, targetState,
              rfl, hEmitInstr, hTargetBlock, hRun, hErase⟩

theorem assemble_source_step_current_sound {program : Program}
    {target : TargetProgram} {state sourceState : EVMState}
    (hAsm : assemble? program = some target)
    (hStep : Source.step program state = .ok sourceState) :
    ∃ pc instr emitted before after,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
        target.code = before ++ emitted ++ after ∧
        Target.runList (emitted.map LocatedTarget.instr) state = .ok sourceState := by
  unfold Source.step at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hStep
          obtain ⟨before, emitted, after, hTargetBlock, hEmitInstr⟩ :=
            assemble_covers_current_pc hAsm hAt
          exact
            ⟨pc, instr, emitted, before, after,
              rfl, hEmitInstr, hTargetBlock, stepAt_emit_sound hEmitInstr hStep⟩

theorem compile?_some_accepted {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target) :
    Accepted program := by
  unfold compile? at hCompile
  cases hAccepted : Program.accepted program <;> simp [hAccepted] at hCompile
  exact ⟨hAccepted⟩

theorem compile?_some_assemble {program : Program} {target : TargetProgram}
    (hCompile : compile? program = some target) :
    assemble? program = some target := by
  unfold compile? at hCompile
  cases hAccepted : Program.accepted program <;> simp [hAccepted] at hCompile
  exact hCompile

theorem compile_source_step_current_sound {program : Program}
    {target : TargetProgram} {state sourceState : EVMState}
    (hCompile : compile? program = some target)
    (hStep : Source.step program state = .ok sourceState) :
    ∃ pc instr emitted before after,
      Program.instrAtPc program state.pc.toNat = some (pc, instr) ∧
        emitInstr? program pc instr = some emitted ∧
        target.code = before ++ emitted ++ after ∧
        Target.runList (emitted.map LocatedTarget.instr) state = .ok sourceState := by
  exact assemble_source_step_current_sound (compile?_some_assemble hCompile) hStep

theorem source_compiled_step_sound {program : Program}
    {state sourceState : EVMState}
    (hStep : Source.step program state = .ok sourceState) :
    Compiled.step program state = .ok sourceState := by
  unfold Source.step at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hStep
          cases hEmitInstr : emitInstr? program pc instr with
          | none =>
              cases instr with
              | label name =>
                  simp [emitInstr?] at hEmitInstr
              | prim op =>
                  simp [emitInstr?] at hEmitInstr
              | push value =>
                  simp [emitInstr?] at hEmitInstr
              | jump target =>
                  cases hDest : Program.labelPc program target with
                  | none =>
                      simp [emitInstr?, hDest] at hEmitInstr
                      have hBad : False := by
                        simp [Source.stepAt, hDest, Source.invalid] at hStep
                      cases hBad
                  | some dest =>
                      simp [emitInstr?, hDest] at hEmitInstr
              | jumpi target =>
                  cases hDest : Program.labelPc program target with
                  | none =>
                      simp [emitInstr?, hDest] at hEmitInstr
                      unfold Source.stepAt at hStep
                      simp [hDest, Source.invalid] at hStep
                  | some dest =>
                      simp [emitInstr?, hDest] at hEmitInstr
          | some emitted =>
              unfold Compiled.step emitCurrent?
              simp [hAt, hEmitInstr]
              exact stepAt_emit_sound hEmitInstr hStep

theorem source_compiled_step_result_sound {program : Program}
    {state : EVMState} {result : StepResult}
    (hStep : Source.stepResult program state = .ok result) :
    Compiled.stepResult program state = .ok result := by
  unfold Source.stepResult at hStep
  cases hAt : Program.instrAtPc program state.pc.toNat with
  | none =>
      simp [hAt] at hStep
  | some current =>
      cases current with
      | mk pc instr =>
          simp [hAt] at hStep
          cases hEmitInstr : emitInstr? program pc instr with
          | none =>
              cases instr with
              | label name =>
                  simp [emitInstr?] at hEmitInstr
              | prim op =>
                  simp [emitInstr?] at hEmitInstr
              | push value =>
                  simp [emitInstr?] at hEmitInstr
              | jump target =>
                  cases hDest : Program.labelPc program target with
                  | none =>
                      simp [emitInstr?, hDest] at hEmitInstr
                      have hBad : False := by
                        unfold Source.stepAtResult Source.stepAt Source.invalid at hStep
                        simp [hDest, Instr.haltKind?] at hStep
                      cases hBad
                  | some dest =>
                      simp [emitInstr?, hDest] at hEmitInstr
              | jumpi target =>
                  cases hDest : Program.labelPc program target with
                  | none =>
                      simp [emitInstr?, hDest] at hEmitInstr
                      have hBad : False := by
                        unfold Source.stepAtResult Source.stepAt Source.invalid at hStep
                        simp [hDest, Instr.haltKind?] at hStep
                      cases hBad
                  | some dest =>
                      simp [emitInstr?, hDest] at hEmitInstr
          | some emitted =>
              unfold Compiled.stepResult emitCurrent?
              simp [hAt, hEmitInstr]
              exact stepAt_emit_result_sound hEmitInstr hStep

theorem source_compiled_runN_sound {program : Program}
    {fuel : Nat} {state sourceState : EVMState}
    (hRun : Source.runN program fuel state = .ok sourceState) :
    Compiled.runN program fuel state = .ok sourceState := by
  induction fuel generalizing state with
  | zero =>
      simp [Source.runN] at hRun
      simpa [Compiled.runN] using hRun
  | succ fuel ih =>
      unfold Source.runN at hRun
      cases hStep : Source.step program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok mid =>
          simp [hStep] at hRun
          unfold Compiled.runN
          rw [source_compiled_step_sound hStep]
          exact ih hRun

theorem source_compiled_runN_result_sound {program : Program}
    {fuel : Nat} {state : EVMState} {result : StepResult}
    (hRun : Source.runNResult program fuel state = .ok result) :
    Compiled.runNResult program fuel state = .ok result := by
  induction fuel generalizing state with
  | zero =>
      simp [Source.runNResult] at hRun
      simpa [Compiled.runNResult] using hRun
  | succ fuel ih =>
      unfold Source.runNResult at hRun
      cases hStep : Source.stepResult program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepResult =>
          rw [hStep] at hRun
          unfold Compiled.runNResult
          rw [source_compiled_step_result_sound hStep]
          cases stepResult with
          | running mid =>
              exact ih hRun
          | halted halt =>
              exact hRun

theorem source_compiled_runN_projected_sound {program : Program}
    {fuel : Nat} {state sourceState : EVMState}
    (hRun : Source.runN program fuel state = .ok sourceState) :
    ∃ targetState,
      Compiled.runN program fuel state = .ok targetState ∧
        eraseGas targetState = eraseGas sourceState := by
  exact ⟨sourceState, source_compiled_runN_sound hRun, rfl⟩

inductive BlockTrace (program : Program) (target : TargetProgram) :
    Nat → EVMState → EVMState → Prop where
  | done (state : EVMState) :
      BlockTrace program target 0 state state
  | step {fuel : Nat} {state mid final : EVMState}
      {pc : Nat} {instr : Instr} {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun : Target.runList (emitted.map LocatedTarget.instr) state = .ok mid)
      (hRest : BlockTrace program target fuel mid final) :
      BlockTrace program target (fuel + 1) state final

inductive BlockTraceResult (program : Program) (target : TargetProgram) :
    Nat → EVMState → StepResult → Prop where
  | done (state : EVMState) :
      BlockTraceResult program target 0 state (.running state)
  | stepRunning {fuel : Nat} {state mid : EVMState} {result : StepResult}
      {pc : Nat} {instr : Instr} {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest : BlockTraceResult program target fuel mid result) :
      BlockTraceResult program target (fuel + 1) state result
  | stepHalted {fuel : Nat} {state : EVMState} {halt : Halt}
      {pc : Nat} {instr : Instr} {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt)) :
      BlockTraceResult program target (fuel + 1) state (.halted halt)

theorem Target.stepInstrResult_halted_output
    {instr : TargetInstr} {state : EVMState} {halt : Halt}
    (hStep :
      Target.stepInstrResult instr state = .ok (.halted halt)) :
    halt.output = halt.kind.output halt.state := by
  unfold Target.stepInstrResult at hStep
  cases hRun : Target.stepInstr instr state with
  | error err =>
      rw [hRun] at hStep
      cases hStep
  | ok state' =>
      rw [hRun] at hStep
      cases hKind : instr.haltKind? with
      | none =>
          rw [hKind] at hStep
          cases hStep
      | some kind =>
          rw [hKind] at hStep
          cases hStep
          rfl

theorem Target.stepInstrResult_terminal_output_eq_H_return
    {kind : HaltKind} {state : EVMState} {halt : Halt}
    (hStep :
      Target.stepInstrResult (.prim kind.toPrimOp) state =
        .ok (.halted halt)) :
    halt.output = halt.state.toMachineState.H_return := by
  unfold Target.stepInstrResult at hStep
  cases hRun :
      Target.stepInstr (.prim kind.toPrimOp) state with
  | error err =>
      rw [hRun] at hStep
      cases hStep
  | ok final =>
      rw [hRun] at hStep
      have hKind :
          (TargetInstr.prim kind.toPrimOp).haltKind? = some kind := by
        cases kind <;> rfl
      rw [hKind] at hStep
      cases hStep
      cases kind with
      | stop =>
          change PrimOp.stop.step state = .ok final at hRun
          unfold PrimOp.step at hRun
          change EvmYul.step (τ := .EVM) .STOP none state =
            .ok final at hRun
          cases state
          cases hRun
          rfl
      | «return» =>
          rfl
      | revert =>
          rfl
      | selfdestruct =>
          change PrimOp.selfdestruct.step state = .ok final at hRun
          unfold PrimOp.step at hRun
          change EvmYul.step (τ := .EVM) .SELFDESTRUCT none state =
            .ok final at hRun
          cases state with
          | mk shared pc stack execLength =>
              cases stack with
              | nil =>
                  contradiction
              | cons recipient rest =>
                  have hSelfdestruct :
                      EvmYul.step (τ := .EVM) .SELFDESTRUCT none
                          { toSharedState := shared
                            pc := pc
                            stack := recipient :: rest
                            execLength := execLength } =
                        .ok (EvmYul.EVM.selfdestructState
                          { toSharedState := shared
                            pc := pc
                            stack := recipient :: rest
                            execLength := execLength }
                          recipient rest) :=
                    EvmYul.EVM.step_selfdestruct_of_stack
                      _ recipient rest rfl
                  rw [hSelfdestruct] at hRun
                  cases hRun
                  simp [HaltKind.output, EvmYul.EVM.selfdestructState,
                    EvmYul.MachineState.setHReturn]

theorem Target.runListResult_halted_output
    {code : List TargetInstr} {state : EVMState} {halt : Halt}
    (hRun :
      Target.runListResult code state = .ok (.halted halt)) :
    halt.output = halt.kind.output halt.state := by
  induction code generalizing state with
  | nil =>
      simp [Target.runListResult, Target.runListResultWith] at hRun
  | cons instr rest ih =>
      cases hStep :
          Target.stepInstrResult instr state with
      | error err =>
          simp [Target.runListResult, Target.runListResultWith, hStep] at hRun
      | ok result =>
          simp only [Target.runListResult, Target.runListResultWith,
            hStep, Bind.bind, Except.bind] at hRun
          cases result with
          | running mid =>
              exact ih hRun
          | halted halt' =>
              cases hRun
              exact Target.stepInstrResult_halted_output hStep

def StepResultOutputMatchesKind : StepResult → Prop
  | .running _ => True
  | .halted halt => halt.output = halt.kind.output halt.state

theorem BlockTraceResult.output_eq_kind
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {result : StepResult}
    (hTrace :
      BlockTraceResult program target fuel state result) :
    StepResultOutputMatchesKind result := by
  induction fuel generalizing state result with
  | zero =>
      cases hTrace
      trivial
  | succ fuel ih =>
      cases hTrace with
      | stepRunning hAt hEmit hTargetBlock hRun hRest =>
          exact ih hRest
      | stepHalted hAt hEmit hTargetBlock hRun =>
          exact Target.runListResult_halted_output hRun

theorem BlockTraceResult.halted_output
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {halt : Halt}
    (hTrace :
      BlockTraceResult program target fuel state (.halted halt)) :
    halt.output = halt.kind.output halt.state := by
  simpa [StepResultOutputMatchesKind] using hTrace.output_eq_kind

theorem BlockTraceResult.revert_output_eq_H_return
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {halt : Halt}
    (hTrace :
      BlockTraceResult program target fuel state (.halted halt))
    (hRevert : halt.kind = .revert) :
    halt.output = halt.state.toMachineState.H_return := by
  have hOutput := hTrace.halted_output
  simpa [HaltKind.output, hRevert] using hOutput

theorem BlockTraceResult.return_output_eq_H_return
    {program : Program} {target : TargetProgram}
    {fuel : Nat} {state : EVMState} {halt : Halt}
    (hTrace :
      BlockTraceResult program target fuel state (.halted halt))
    (hReturn : halt.kind = .return) :
    halt.output = halt.state.toMachineState.H_return := by
  have hOutput := hTrace.halted_output
  simpa [HaltKind.output, hReturn] using hOutput

theorem assemble_runN_block_trace_sound {program : Program}
    {target : TargetProgram} {fuel : Nat} {state sourceState : EVMState}
    (hAsm : assemble? program = some target)
    (hRun : Source.runN program fuel state = .ok sourceState) :
    BlockTrace program target fuel state sourceState := by
  induction fuel generalizing state with
  | zero =>
      simp [Source.runN] at hRun
      subst sourceState
      exact BlockTrace.done state
  | succ fuel ih =>
      unfold Source.runN at hRun
      cases hStep : Source.step program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok mid =>
          simp [hStep] at hRun
          obtain
            ⟨pc, instr, emitted, before, after,
              hAt, hEmit, hTargetBlock, hBlockRun⟩ :=
            assemble_source_step_current_sound hAsm hStep
          exact
            BlockTrace.step hAt hEmit hTargetBlock hBlockRun (ih hRun)

theorem assemble_runN_result_block_trace_sound {program : Program}
    {target : TargetProgram} {fuel : Nat} {state : EVMState}
    {result : StepResult}
    (hAsm : assemble? program = some target)
    (hRun : Source.runNResult program fuel state = .ok result) :
    BlockTraceResult program target fuel state result := by
  induction fuel generalizing state with
  | zero =>
      simp [Source.runNResult] at hRun
      subst result
      exact BlockTraceResult.done state
  | succ fuel ih =>
      unfold Source.runNResult at hRun
      cases hStep : Source.stepResult program state with
      | error err =>
          rw [hStep] at hRun
          cases hRun
      | ok stepResult =>
          rw [hStep] at hRun
          obtain
            ⟨pc, instr, emitted, before, after,
              hAt, hEmit, hTargetBlock, hBlockRun⟩ :=
            assemble_source_step_current_result_sound hAsm hStep
          cases stepResult with
          | running mid =>
              exact
                BlockTraceResult.stepRunning hAt hEmit hTargetBlock hBlockRun
                  (ih hRun)
          | halted halt =>
              cases hRun
              exact
                BlockTraceResult.stepHalted hAt hEmit hTargetBlock hBlockRun

/--
Whole-program AST-level compiler theorem for the current assembly layer.

For every successful source execution of the accepted labeled assembly program,
`compile?` produces a resolved target program whose emitted EVM-instruction
blocks replay the same run exactly.  The final projection is stated explicitly
so later gas-aware lowerings can reuse this theorem under a gas-erasing
observation relation.
-/
theorem compile_runN_block_trace_projected_sound {program : Program}
    {target : TargetProgram} {fuel : Nat} {state sourceState : EVMState}
    (hCompile : compile? program = some target)
    (hRun : Source.runN program fuel state = .ok sourceState) :
    Accepted program ∧
      ∃ targetState,
        BlockTrace program target fuel state targetState ∧
          eraseGas targetState = eraseGas sourceState := by
  refine ⟨compile?_some_accepted hCompile, sourceState, ?_, rfl⟩
  exact assemble_runN_block_trace_sound (compile?_some_assemble hCompile) hRun

/--
Outcome-aware assembly theorem.

This is the terminal-opcode-aware sibling of
`compile_runN_block_trace_projected_sound`: `STOP`, `RETURN`, `REVERT`, and
`SELFDESTRUCT` halt the gasless source runner with a named result, and the
compiled target block trace produces the same result.
-/
theorem compile_runN_result_block_trace_sound {program : Program}
    {target : TargetProgram} {fuel : Nat} {state : EVMState}
    {result : StepResult}
    (hCompile : compile? program = some target)
    (hRun : Source.runNResult program fuel state = .ok result) :
    Accepted program ∧
      BlockTraceResult program target fuel state result := by
  exact
    ⟨compile?_some_accepted hCompile,
      assemble_runN_result_block_trace_sound (compile?_some_assemble hCompile)
        hRun⟩

end Preservation

end Assembly
end EvmCompiler
