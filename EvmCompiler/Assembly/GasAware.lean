import EvmCompiler.Assembly.TopLevel

namespace EvmCompiler
namespace Assembly

namespace GasAware

def installCodeAndGas (target : TargetProgram) (gas : Nat)
    (state : EVMState) : EVMState :=
  { state with
    gasAvailable := EvmYul.UInt256.ofNat gas
    executionEnv := { state.executionEnv with code := Bytecode.encodeTarget target }
  }

theorem installCodeAndGas_gasAvailable_toNat {target : TargetProgram}
    {gas : Nat} {state : EVMState}
    (hGasFits : gas < EvmYul.UInt256.size) :
    (installCodeAndGas target gas state).gasAvailable.toNat = gas := by
  simp [installCodeAndGas,
    Bytecode.uint256_ofNat_toNat_of_lt_size hGasFits]

theorem installCodeAndGas_idempotent (target : TargetProgram) (gas : Nat)
    (state : EVMState) :
    installCodeAndGas target gas (installCodeAndGas target gas state) =
      installCodeAndGas target gas state := by
  simp [installCodeAndGas]

theorem uint256_sub_toNat_of_le {left right : Word}
    (hLe : right.toNat ≤ left.toNat) :
    (left - right).toNat = left.toNat - right.toNat := by
  change (EvmYul.UInt256.sub left right).toNat =
    left.toNat - right.toNat
  unfold EvmYul.UInt256.toNat EvmYul.UInt256.sub
  exact Fin.sub_val_of_le hLe

def validJumps (target : TargetProgram) : Array EvmYul.UInt256 :=
  EvmYul.EVM.D_J (Bytecode.encodeTarget target) (EvmYul.UInt256.ofNat 0)

def targetInstrUsesCallCreate : TargetInstr → Bool
  | .prim op => op.isCallCreate
  | .push32 _ | .jump | .jumpi | .jumpdest => false

theorem targetInstr_op_isCreate_false_of_usesCallCreate_false
    {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false) :
    instr.op.isCreate = false := by
  cases instr with
  | push32 value =>
      rfl
  | jump =>
      rfl
  | jumpi =>
      rfl
  | jumpdest =>
      rfl
  | prim op =>
      cases op <;>
        simp [targetInstrUsesCallCreate, PrimOp.isCallCreate,
          TargetInstr.op, PrimOp.toEVM, EvmYul.Operation.isCreate]
          at hNoCallCreate ⊢

def targetInstrUsesReturnDataCopy : TargetInstr → Bool
  | .prim .returndatacopy => true
  | .prim _ | .push32 _ | .jump | .jumpi | .jumpdest => false

def targetInstrNoReturnDataCopy (instr : TargetInstr) : Bool :=
  !targetInstrUsesReturnDataCopy instr

def targetProgramNoReturnDataCopy (target : TargetProgram) : Prop :=
  ∀ {located : LocatedTarget}, located ∈ target.code →
    targetInstrNoReturnDataCopy located.instr = true

def targetProgramNoReturnDataCopy? (target : TargetProgram) : Bool :=
  target.code.all fun located =>
    targetInstrNoReturnDataCopy located.instr

theorem targetProgramNoReturnDataCopy_of_check
    {target : TargetProgram}
    (hCheck : targetProgramNoReturnDataCopy? target = true) :
    targetProgramNoReturnDataCopy target := by
  intro located hMem
  exact
    (List.all_eq_true.mp hCheck) located hMem

theorem targetInstr_op_ne_returnDataCopy_of_noReturnDataCopy
    {instr : TargetInstr}
    (hNoReturnDataCopy : targetInstrNoReturnDataCopy instr = true) :
    instr.op ≠ EvmYul.Operation.RETURNDATACOPY := by
  cases instr with
  | push32 value =>
      simp [targetInstrNoReturnDataCopy, targetInstrUsesReturnDataCopy,
        TargetInstr.op] at hNoReturnDataCopy ⊢
  | jump =>
      simp [targetInstrNoReturnDataCopy, targetInstrUsesReturnDataCopy,
        TargetInstr.op] at hNoReturnDataCopy ⊢
  | jumpi =>
      simp [targetInstrNoReturnDataCopy, targetInstrUsesReturnDataCopy,
        TargetInstr.op] at hNoReturnDataCopy ⊢
  | jumpdest =>
      simp [targetInstrNoReturnDataCopy, targetInstrUsesReturnDataCopy,
        TargetInstr.op] at hNoReturnDataCopy ⊢
  | prim op =>
      cases op <;>
        simp [targetInstrNoReturnDataCopy, targetInstrUsesReturnDataCopy,
          TargetInstr.op, PrimOp.toEVM] at hNoReturnDataCopy ⊢

theorem instr_usesCallCreate_false_of_instrAtPcFrom
    {program : Program} {base query pc : Nat} {instr : Instr}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hAt : Program.instrAtPcFrom program base query = some (pc, instr)) :
    Instr.usesCallCreate instr = false := by
  induction program generalizing base with
  | nil =>
      simp [Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      have hSplit :
          Instr.usesCallCreate head = false ∧
            Program.usesCallCreate rest = false := by
        simpa [Program.usesCallCreate] using hNoCallCreate
      by_cases hQuery : query = base
      · simp [Program.instrAtPcFrom, hQuery] at hAt
        have hPair : (base, head) = (pc, instr) := by
          simpa using hAt
        cases hPair
        exact hSplit.1
      · simp [Program.instrAtPcFrom, hQuery] at hAt
        exact ih hSplit.2 hAt

theorem instr_usesCallCreate_false_of_instrAtPc
    {program : Program} {query pc : Nat} {instr : Instr}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hAt : Program.instrAtPc program query = some (pc, instr)) :
    Instr.usesCallCreate instr = false :=
  instr_usesCallCreate_false_of_instrAtPcFrom hNoCallCreate hAt

theorem targetInstr_usesCallCreate_false_of_emitInstr_mem
    {program : Program} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget} {located : LocatedTarget}
    (hNoInstr : Instr.usesCallCreate instr = false)
    (hEmit : emitInstr? program pc instr = some emitted)
    (hMem : located ∈ emitted) :
    targetInstrUsesCallCreate located.instr = false := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst emitted
      simp [targetInstrUsesCallCreate] at hMem ⊢
      cases hMem
      rfl
  | prim op =>
      simp [emitInstr?, Instr.usesCallCreate] at hEmit hNoInstr
      subst emitted
      simp [targetInstrUsesCallCreate] at hMem ⊢
      cases hMem
      simpa [PrimOp.isCallCreate] using hNoInstr
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      simp [targetInstrUsesCallCreate] at hMem ⊢
      cases hMem
      rfl
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          simp [targetInstrUsesCallCreate] at hMem ⊢
          rcases hMem with rfl | hMem
          · rfl
          · rcases hMem with rfl | hFalse
            · rfl
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          simp [targetInstrUsesCallCreate] at hMem ⊢
          rcases hMem with rfl | hMem
          · rfl
          · rcases hMem with rfl | hFalse
            · rfl

theorem targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
    {program : Program} {query pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget} {located : LocatedTarget}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hAt : Program.instrAtPc program query = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hMem : located ∈ emitted) :
    targetInstrUsesCallCreate located.instr = false :=
  targetInstr_usesCallCreate_false_of_emitInstr_mem
    (instr_usesCallCreate_false_of_instrAtPc hNoCallCreate hAt)
    hEmit hMem

theorem emitInstr?_exists_head_pc
    {program : Program} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget}
    (hEmit : emitInstr? program pc instr = some emitted) :
    ∃ located rest,
      emitted = located :: rest ∧ located.pc = pc := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst emitted
      exact ⟨{ pc := pc, instr := TargetInstr.jumpdest }, [], rfl, rfl⟩
  | prim op =>
      simp [emitInstr?] at hEmit
      subst emitted
      exact ⟨{ pc := pc, instr := TargetInstr.prim op }, [], rfl, rfl⟩
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      exact ⟨{ pc := pc, instr := TargetInstr.push32 value }, [], rfl, rfl⟩
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          exact
            ⟨{ pc := pc,
                instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) },
              [{ pc := pc + Instr.push32Size, instr := TargetInstr.jump }],
              rfl, rfl⟩
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          exact
            ⟨{ pc := pc,
                instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) },
              [{ pc := pc + Instr.push32Size, instr := TargetInstr.jumpi }],
              rfl, rfl⟩

theorem EVM_step_targetInstr_eq_of_no_call_create {fuel gasCost : Nat}
    {state : EVMState} {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false) :
    EvmYul.EVM.step fuel.succ gasCost
        (some (instr.op, instr.arg)) state =
      EvmYul.step instr.op instr.arg
        { state with
          gasAvailable := state.gasAvailable - EvmYul.UInt256.ofNat gasCost,
          execLength := state.execLength + 1 } := by
  cases instr with
  | push32 value => rfl
  | jump => rfl
  | jumpi => rfl
  | jumpdest => rfl
  | prim op =>
      cases op <;>
        simp [targetInstrUsesCallCreate, PrimOp.isCallCreate] at hNoCallCreate
      all_goals rfl

theorem EvmYul_step_eq_continuingStep_run {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    (hNotReturndatacopy : step ≠ PrimStep.returndatacopy)
    (hNotPop : step ≠ PrimStep.pop)
    (hNotMload : step ≠ PrimStep.mload)
    (hNotLog0 : step ≠ PrimStep.log0)
    (hNotLog1 : step ≠ PrimStep.log1)
    (hNotLog2 : step ≠ PrimStep.log2)
    (hNotLog3 : step ≠ PrimStep.log3)
    (hNotLog4 : step ≠ PrimStep.log4)
    (state : EVMState) :
    EvmYul.step op.toEVM none state = step.run state := by
  cases op <;> simp [PrimOp.continuingStep?] at hStep
  all_goals cases hStep
  case returndatacopy.refl => exact False.elim (hNotReturndatacopy rfl)
  case pop.refl => exact False.elim (hNotPop rfl)
  case mload.refl => exact False.elim (hNotMload rfl)
  case log0.refl => exact False.elim (hNotLog0 rfl)
  case log1.refl => exact False.elim (hNotLog1 rfl)
  case log2.refl => exact False.elim (hNotLog2 rfl)
  case log3.refl => exact False.elim (hNotLog3 rfl)
  case log4.refl => exact False.elim (hNotLog4 rfl)
  all_goals rfl

theorem EvmYul_step_pop_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.POP none state =
      PrimStep.pop.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack <;> rfl

theorem EvmYul_step_mload_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.MLOAD none state =
      PrimStep.mload.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack <;> rfl

theorem EvmYul_step_returndatacopy_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.RETURNDATACOPY none state =
      PrimStep.returndatacopy.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest => rfl

theorem EvmYul_step_log0_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG0 none state =
      PrimStep.log0.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest => rfl

theorem EvmYul_step_log1_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG1 none state =
      PrimStep.log1.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest => rfl

theorem EvmYul_step_log2_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG2 none state =
      PrimStep.log2.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest =>
                  cases rest with
                  | nil => rfl
                  | cons fourth rest => rfl

theorem EvmYul_step_log3_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG3 none state =
      PrimStep.log3.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest =>
                  cases rest with
                  | nil => rfl
                  | cons fourth rest =>
                      cases rest with
                      | nil => rfl
                      | cons fifth rest => rfl

theorem EvmYul_step_log4_eq_PrimStep_run (state : EVMState) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.LOG4 none state =
      PrimStep.log4.run state := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest =>
              cases rest with
              | nil => rfl
              | cons third rest =>
                  cases rest with
                  | nil => rfl
                  | cons fourth rest =>
                      cases rest with
                      | nil => rfl
                      | cons fifth rest =>
                          cases rest with
                          | nil => rfl
                          | cons sixth rest => rfl

theorem EvmYul_step_eq_continuingStep_run_exact
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) (state : EVMState) :
    EvmYul.step op.toEVM none state = step.run state := by
  cases step with
  | bin f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | un f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | tri f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | executionEnv f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | unaryExecutionEnv f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | machineState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | binaryMachineState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | binaryMachineStateWithResult f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | ternaryMachineState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | state f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | unaryState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | binaryState f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | ternaryCopy f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | quaternaryCopy f =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | pop =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_pop_eq_PrimStep_run state
  | mload =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_mload_eq_PrimStep_run state
  | returndatacopy =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_returndatacopy_eq_PrimStep_run state
  | dup n =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | swap n =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state
  | log0 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log0_eq_PrimStep_run state
  | log1 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log1_eq_PrimStep_run state
  | log2 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log2_eq_PrimStep_run state
  | log3 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log3_eq_PrimStep_run state
  | log4 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log4_eq_PrimStep_run state
  | invalid =>
      exact EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) state

theorem mem_target_of_mem_emitted
    {target : TargetProgram} {located : LocatedTarget}
    {before emitted after : List LocatedTarget}
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted) :
    located ∈ target.code := by
  rw [hTargetBlock]
  simp [hMem]

theorem decode_installed_of_mem
    {target : TargetProgram} {state : EVMState} {gas : Nat}
    {located : LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hMem : located ∈ target.code) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        (EvmYul.UInt256.ofNat located.pc) =
      some (located.instr.op, located.instr.arg) := by
  simpa [installCodeAndGas, Bytecode.decodeAt] using
    hEncoding.decodes located hMem

theorem decode_installed_of_mem_emitted
    {target : TargetProgram} {state : EVMState} {gas : Nat}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        (EvmYul.UInt256.ofNat located.pc) =
      some (located.instr.op, located.instr.arg) := by
  exact decode_installed_of_mem hEncoding
    (mem_target_of_mem_emitted hTargetBlock hMem)

theorem program_instrAtPcFrom_eq_query
    {program : Program} {base query pc : Nat} {instr : Instr}
    (hAt : Program.instrAtPcFrom program base query = some (pc, instr)) :
    pc = query := by
  induction program generalizing base with
  | nil =>
      simp [Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      by_cases hEq : query = base
      · simp [Program.instrAtPcFrom, hEq] at hAt
        exact hAt.1.symm.trans hEq.symm
      · simp [Program.instrAtPcFrom, hEq] at hAt
        exact ih hAt

theorem program_instrAtPc_eq_query
    {program : Program} {query pc : Nat} {instr : Instr}
    (hAt : Program.instrAtPc program query = some (pc, instr)) :
    pc = query :=
  program_instrAtPcFrom_eq_query hAt

theorem uint256_eq_of_toNat_eq_ofNat_toNat
    {pc : Word} {n : Nat}
    (hPc : pc.toNat = n)
    (hNoWrap : (EvmYul.UInt256.ofNat n).toNat = n) :
    pc = EvmYul.UInt256.ofNat n := by
  cases pc with
  | mk pcVal =>
      unfold EvmYul.UInt256.toNat at hPc hNoWrap
      unfold EvmYul.UInt256.ofNat at hNoWrap ⊢
      simp only at hPc hNoWrap ⊢
      apply congrArg EvmYul.UInt256.mk
      exact Fin.ext (hPc.trans hNoWrap.symm)

theorem state_pc_eq_of_instrAt_of_noWrap
    {program : Program} {state : EVMState} {pc : Nat} {instr : Instr}
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hNoWrap : (EvmYul.UInt256.ofNat pc).toNat = pc) :
    state.pc = EvmYul.UInt256.ofNat pc := by
  exact
      uint256_eq_of_toNat_eq_ofNat_toNat
      (pc := state.pc) (n := pc)
      (program_instrAtPc_eq_query
        (program := program) (query := state.pc.toNat) (pc := pc)
        (instr := instr) hAt).symm
      hNoWrap

theorem decode_installed_of_state_pc_mem
    {target : TargetProgram} {state : EVMState} {gas : Nat}
    {located : LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hMem : located ∈ target.code)
    (hPc : state.pc = EvmYul.UInt256.ofNat located.pc) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        state.pc =
      some (located.instr.op, located.instr.arg) := by
  rw [hPc]
  exact decode_installed_of_mem hEncoding hMem

theorem decode_installed_of_state_pc_mem_emitted
    {target : TargetProgram} {state : EVMState} {gas : Nat}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted)
    (hPc : state.pc = EvmYul.UInt256.ofNat located.pc) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        state.pc =
      some (located.instr.op, located.instr.arg) := by
  exact
    decode_installed_of_state_pc_mem hEncoding
      (mem_target_of_mem_emitted hTargetBlock hMem) hPc

theorem decode_of_code_eq_state_pc_mem
    {target : TargetProgram} {full : EVMState}
    {located : LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hMem : located ∈ target.code)
    (hCode : full.executionEnv.code = Bytecode.encodeTarget target)
    (hPc : full.pc = EvmYul.UInt256.ofNat located.pc) :
    EvmYul.EVM.decode full.executionEnv.code full.pc =
      some (located.instr.op, located.instr.arg) := by
  rw [hCode, hPc]
  simpa [Bytecode.decodeAt] using hEncoding.decodes located hMem

theorem decode_of_code_eq_state_pc_mem_emitted
    {target : TargetProgram} {full : EVMState}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted)
    (hCode : full.executionEnv.code = Bytecode.encodeTarget target)
    (hPc : full.pc = EvmYul.UInt256.ofNat located.pc) :
    EvmYul.EVM.decode full.executionEnv.code full.pc =
      some (located.instr.op, located.instr.arg) := by
  exact
    decode_of_code_eq_state_pc_mem hEncoding
      (mem_target_of_mem_emitted hTargetBlock hMem) hCode hPc

theorem decode_installed_of_instrAt_mem_emitted
    {program : Program} {target : TargetProgram} {state : EVMState}
    {gas : Nat} {pc : Nat} {instr : Instr}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted)
    (hLocatedPc : located.pc = pc)
    (hNoWrap : (EvmYul.UInt256.ofNat located.pc).toNat = located.pc) :
    EvmYul.EVM.decode
        (installCodeAndGas target gas state).executionEnv.code
        state.pc =
      some (located.instr.op, located.instr.arg) := by
  have hNoWrapPc : (EvmYul.UInt256.ofNat pc).toNat = pc := by
    simpa [hLocatedPc] using hNoWrap
  have hPc := state_pc_eq_of_instrAt_of_noWrap hAt hNoWrapPc
  exact
    decode_installed_of_state_pc_mem_emitted hEncoding hTargetBlock hMem
      (by simpa [hLocatedPc] using hPc)

def staticWriteSensitive (op : EVMOp) (stack : EvmYul.Stack Word) : Prop :=
  op = EvmYul.Operation.CREATE ∨
    op = EvmYul.Operation.CREATE2 ∨
    op = EvmYul.Operation.SSTORE ∨
    op = EvmYul.Operation.SELFDESTRUCT ∨
    op = EvmYul.Operation.LOG0 ∨
    op = EvmYul.Operation.LOG1 ∨
    op = EvmYul.Operation.LOG2 ∨
    op = EvmYul.Operation.LOG3 ∨
    op = EvmYul.Operation.LOG4 ∨
    op = EvmYul.Operation.TSTORE ∨
    (op = EvmYul.Operation.CALL ∧ stack[2]? ≠ some ⟨0⟩)

def memoryGasState (state : EVMState) (op : EVMOp) : EVMState :=
  { state with
    gasAvailable :=
      state.gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }

/--
`full` and `target` are the same EVM state up to the gasful runner's bookkeeping
fields.  This is stronger than `eraseGas full = eraseGas target`, and is the
right local invariant for replaying gas-aware `EVM.X` steps against the gasless
target interpreter.
-/
def GasExecRel (full target : EVMState) : Prop :=
  full =
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }

namespace GasExecRel

theorem refl (state : EVMState) : GasExecRel state state := by
  simp [GasExecRel]

theorem eraseGas_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    eraseGas full = eraseGas target := by
  rw [hRel]
  simp [eraseGas]

theorem of_eraseGas_eq {full target : EVMState}
    (hErase : eraseGas full = eraseGas target) :
    GasExecRel full target := by
  cases full with
  | mk fullShared fullPc fullStack fullExecLength =>
      cases target with
      | mk targetShared targetPc targetStack targetExecLength =>
          cases fullShared with
          | mk fullState fullMachine =>
              cases targetShared with
              | mk targetState targetMachine =>
                  cases fullMachine
                  cases targetMachine
                  simp [GasExecRel, eraseGas] at hErase ⊢
                  exact hErase

theorem incrPC {full target : EVMState}
    (hRel : GasExecRel full target) :
    GasExecRel
      (EvmYul.EVM.State.incrPC full)
      (EvmYul.EVM.State.incrPC target) := by
  rw [hRel]
  simp [GasExecRel, EvmYul.EVM.State.incrPC]

theorem trans {left mid right : EVMState}
    (hLeft : GasExecRel left mid)
    (hRight : GasExecRel mid right) :
    GasExecRel left right := by
  rw [hLeft, hRight]
  simp [GasExecRel]

theorem pc_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.pc = target.pc := by
  rw [hRel]

theorem stack_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.stack = target.stack := by
  rw [hRel]

theorem executionEnv_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.executionEnv = target.executionEnv := by
  rw [hRel]

theorem perm_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.executionEnv.perm = target.executionEnv.perm := by
  rw [hRel]

theorem perm_true {full target : EVMState}
    (hRel : GasExecRel full target)
    (hPerm : target.executionEnv.perm = true) :
    full.executionEnv.perm = true := by
  rw [perm_eq hRel]
  exact hPerm

theorem code_eq {full target : EVMState}
    (hRel : GasExecRel full target) :
    full.executionEnv.code = target.executionEnv.code := by
  rw [hRel]

theorem installCodeAndGas_of_code_eq {target : TargetProgram}
    {gas : Nat} {initial : EVMState}
    (hCode :
      initial.executionEnv.code = Bytecode.encodeTarget target) :
    GasExecRel (installCodeAndGas target gas initial) initial := by
  cases initial with
  | mk shared pc stack execLength =>
      cases shared with
      | mk state machine =>
          cases state with
          | mk accountMap σ₀ totalGasUsedInBlock transactionReceipts substate
              executionEnv blocks genesisBlockHeader createdAccounts =>
              cases executionEnv
              simp [GasExecRel, installCodeAndGas] at hCode ⊢
              exact hCode.symm

theorem memoryGasState_left {full target : EVMState} {op : EVMOp}
    (hRel : GasExecRel full target) :
    GasExecRel (memoryGasState full op) target := by
  rw [hRel]
  simp [GasExecRel, memoryGasState]

theorem memoryGasState_both {full target : EVMState} {op : EVMOp}
    (hRel : GasExecRel full target) :
    GasExecRel (memoryGasState full op) (memoryGasState target op) := by
  rw [hRel]
  simp [GasExecRel, memoryGasState]

theorem charge_left {full target : EVMState} {cost : Nat}
    (hRel : GasExecRel full target) :
    GasExecRel
      { full with
        gasAvailable := full.gasAvailable - EvmYul.UInt256.ofNat cost,
        execLength := full.execLength + 1 }
      target := by
  rw [hRel]
  simp [GasExecRel]

theorem xCharged_left {full target : EVMState} {op : EVMOp} {cost : Nat}
    (hRel : GasExecRel full target) :
    GasExecRel
      { memoryGasState full op with
        gasAvailable :=
          (memoryGasState full op).gasAvailable - EvmYul.UInt256.ofNat cost,
        execLength := (memoryGasState full op).execLength + 1 }
      target := by
  exact (hRel.memoryGasState_left (op := op)).charge_left (cost := cost)

theorem replaceStackAndIncrPC_left {full target : EVMState}
    (hRel : GasExecRel full target) (stack : EvmYul.Stack Word)
    (pcΔ : Nat := 1) :
    GasExecRel
      (EvmYul.EVM.State.replaceStackAndIncrPC full stack pcΔ)
      (EvmYul.EVM.State.replaceStackAndIncrPC target stack pcΔ) := by
  rw [hRel]
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem set_pc_stack_left {full target : EVMState}
    (hRel : GasExecRel full target) (pc : Word)
    (stack : EvmYul.Stack Word) :
    GasExecRel
      { full with pc := pc, stack := stack }
      { target with pc := pc, stack := stack } := by
  rw [hRel]
  simp [GasExecRel]

end GasExecRel

theorem decode_of_gasExecRel_instrAt_mem_emitted
    {program : Program} {target : TargetProgram}
    {targetState fullState : EVMState}
    {pc : Nat} {instr : Instr}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hAt : Program.instrAtPc program targetState.pc.toNat = some (pc, instr))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted)
    (hLocatedPc : located.pc = pc)
    (hNoWrap : (EvmYul.UInt256.ofNat located.pc).toNat = located.pc)
    (hRel : GasExecRel fullState targetState)
    (hCode : fullState.executionEnv.code = Bytecode.encodeTarget target) :
    EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
      some (located.instr.op, located.instr.arg) := by
  have hNoWrapPc : (EvmYul.UInt256.ofNat pc).toNat = pc := by
    simpa [hLocatedPc] using hNoWrap
  have hTargetPc := state_pc_eq_of_instrAt_of_noWrap hAt hNoWrapPc
  have hFullPc :
      fullState.pc = EvmYul.UInt256.ofNat located.pc := by
    rw [hRel.pc_eq]
    simpa [hLocatedPc] using hTargetPc
  exact
    decode_of_code_eq_state_pc_mem_emitted hEncoding hTargetBlock hMem
      hCode hFullPc

theorem decode_of_gasExecRel_instrAt_mem_emitted_of_safety
    {program : Program} {target : TargetProgram}
    {targetState fullState : EVMState}
    {pc : Nat} {instr : Instr}
    {located : LocatedTarget} {before emitted after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hAt : Program.instrAtPc program targetState.pc.toNat = some (pc, instr))
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hMem : located ∈ emitted)
    (hLocatedPc : located.pc = pc)
    (hRel : GasExecRel fullState targetState)
    (hCode : fullState.executionEnv.code = Bytecode.encodeTarget target) :
    EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
      some (located.instr.op, located.instr.arg) := by
  exact
    decode_of_gasExecRel_instrAt_mem_emitted hEncoding hAt hTargetBlock hMem
      hLocatedPc
      (hSafety.pcNoWrap located
        (mem_target_of_mem_emitted hTargetBlock hMem))
      hRel hCode

theorem block_start_decode_of_emitInstr
    {program : Program} {target : TargetProgram}
    {targetState fullState : EVMState}
    {pc : Nat} {instr : Instr}
    {emitted before after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hAt : Program.instrAtPc program targetState.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hRel : GasExecRel fullState targetState)
    (hCode : fullState.executionEnv.code = Bytecode.encodeTarget target) :
    ∃ targetInstr rest,
      emitted.map LocatedTarget.instr = targetInstr :: rest ∧
        EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
          some (targetInstr.op, targetInstr.arg) := by
  obtain ⟨located, rest, hEmitted, hLocatedPc⟩ :=
    emitInstr?_exists_head_pc hEmit
  have hMem : located ∈ emitted := by
    rw [hEmitted]
    simp
  have hDecode :
      EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
        some (located.instr.op, located.instr.arg) :=
    decode_of_gasExecRel_instrAt_mem_emitted_of_safety hEncoding hSafety hAt
      hTargetBlock hMem hLocatedPc hRel hCode
  exact
    ⟨located.instr, rest.map LocatedTarget.instr, by simp [hEmitted],
      hDecode⟩

theorem EVM_step_push32_preserves_code_and_pc
    {full fullPost : EVMState} {value : Word} {gasCost stepFuel : Nat}
    (hStep :
      EvmYul.EVM.step stepFuel.succ gasCost
        (some ((TargetInstr.push32 value).op, (TargetInstr.push32 value).arg))
        (memoryGasState full (TargetInstr.push32 value).op) = .ok fullPost) :
    fullPost.executionEnv.code = full.executionEnv.code ∧
      fullPost.pc = full.pc + EvmYul.UInt256.ofNat 33 := by
  rw [EVM_step_targetInstr_eq_of_no_call_create
    (fuel := stepFuel) (gasCost := gasCost)
    (state := memoryGasState full (TargetInstr.push32 value).op)
    (instr := TargetInstr.push32 value) rfl] at hStep
  simp [memoryGasState] at hStep
  cases hStep
  simp [EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem decode_next_after_push32_step_of_emitted_pair
    {target : TargetProgram} {full fullPost : EVMState}
    {pc gasCost stepFuel : Nat} {value : Word} {next : TargetInstr}
    {rest before after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hTargetBlock :
      target.code =
        before ++
          ({ pc := pc, instr := TargetInstr.push32 value } ::
            { pc := pc + Instr.push32Size, instr := next } :: rest) ++
          after)
    (hCode : full.executionEnv.code = Bytecode.encodeTarget target)
    (hPc : full.pc = EvmYul.UInt256.ofNat pc)
    (hStep :
      EvmYul.EVM.step stepFuel.succ gasCost
        (some ((TargetInstr.push32 value).op, (TargetInstr.push32 value).arg))
        (memoryGasState full (TargetInstr.push32 value).op) = .ok fullPost) :
    EvmYul.EVM.decode fullPost.executionEnv.code fullPost.pc =
      some (next.op, next.arg) := by
  have hStepProps := EVM_step_push32_preserves_code_and_pc hStep
  have hCodePost : fullPost.executionEnv.code = Bytecode.encodeTarget target := by
    rw [hStepProps.1, hCode]
  have hPcPost :
      fullPost.pc = EvmYul.UInt256.ofNat (pc + Instr.push32Size) := by
    rw [hStepProps.2, hPc]
    rw [UInt256_ofNat_add]
    rfl
  exact
    decode_of_code_eq_state_pc_mem_emitted hEncoding hTargetBlock
      (located := { pc := pc + Instr.push32Size, instr := next })
      (by simp) hCodePost hPcPost

theorem decode_jump_after_push32_step_of_emitInstr
    {program : Program} {target : TargetProgram}
    {targetState fullState fullPost : EVMState}
    {pc dest gasCost stepFuel : Nat} {label : Label}
    {emitted before after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hAt :
      Program.instrAtPc program targetState.pc.toNat =
        some (pc, Instr.jump label))
    (hDest : Program.labelPc program label = some dest)
    (hEmit : emitInstr? program pc (Instr.jump label) = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hRel : GasExecRel fullState targetState)
    (hCode : fullState.executionEnv.code = Bytecode.encodeTarget target)
    (hStep :
      EvmYul.EVM.step stepFuel.succ gasCost
        (some ((TargetInstr.push32
          (EvmYul.UInt256.ofNat dest)).op,
          (TargetInstr.push32
            (EvmYul.UInt256.ofNat dest)).arg))
        (memoryGasState fullState
          (TargetInstr.push32
            (EvmYul.UInt256.ofNat dest)).op) =
        .ok fullPost) :
    EvmYul.EVM.decode fullPost.executionEnv.code fullPost.pc =
      some (TargetInstr.jump.op, TargetInstr.jump.arg) := by
  simp [emitInstr?, hDest] at hEmit
  subst emitted
  have hFirstMem :
      ({ pc := pc,
          instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) } :
        LocatedTarget) ∈
        ([ { pc := pc,
              instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) },
            { pc := pc + Instr.push32Size, instr := TargetInstr.jump } ] :
          List LocatedTarget) := by
    simp
  have hNoWrapPc :
      (EvmYul.UInt256.ofNat pc).toNat = pc := by
    have hNoWrap :=
      hSafety.pcNoWrap
        ({ pc := pc,
            instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) } :
          LocatedTarget)
        (mem_target_of_mem_emitted hTargetBlock hFirstMem)
    simpa using hNoWrap
  have hTargetPc := state_pc_eq_of_instrAt_of_noWrap hAt hNoWrapPc
  have hFullPc : fullState.pc = EvmYul.UInt256.ofNat pc := by
    rw [hRel.pc_eq]
    exact hTargetPc
  exact
    decode_next_after_push32_step_of_emitted_pair
      (target := target)
      (full := fullState)
      (fullPost := fullPost)
      (pc := pc)
      (gasCost := gasCost)
      (stepFuel := stepFuel)
      (value := EvmYul.UInt256.ofNat dest)
      (next := TargetInstr.jump)
      (rest := [])
      hEncoding
      (by simpa using hTargetBlock)
      hCode hFullPc hStep

theorem decode_jumpi_after_push32_step_of_emitInstr
    {program : Program} {target : TargetProgram}
    {targetState fullState fullPost : EVMState}
    {pc dest gasCost stepFuel : Nat} {label : Label}
    {emitted before after : List LocatedTarget}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hAt :
      Program.instrAtPc program targetState.pc.toNat =
        some (pc, Instr.jumpi label))
    (hDest : Program.labelPc program label = some dest)
    (hEmit : emitInstr? program pc (Instr.jumpi label) = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hRel : GasExecRel fullState targetState)
    (hCode : fullState.executionEnv.code = Bytecode.encodeTarget target)
    (hStep :
      EvmYul.EVM.step stepFuel.succ gasCost
        (some ((TargetInstr.push32
          (EvmYul.UInt256.ofNat dest)).op,
          (TargetInstr.push32
            (EvmYul.UInt256.ofNat dest)).arg))
        (memoryGasState fullState
          (TargetInstr.push32
            (EvmYul.UInt256.ofNat dest)).op) =
        .ok fullPost) :
    EvmYul.EVM.decode fullPost.executionEnv.code fullPost.pc =
      some (TargetInstr.jumpi.op, TargetInstr.jumpi.arg) := by
  simp [emitInstr?, hDest] at hEmit
  subst emitted
  have hFirstMem :
      ({ pc := pc,
          instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) } :
        LocatedTarget) ∈
        ([ { pc := pc,
              instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) },
            { pc := pc + Instr.push32Size, instr := TargetInstr.jumpi } ] :
          List LocatedTarget) := by
    simp
  have hNoWrapPc :
      (EvmYul.UInt256.ofNat pc).toNat = pc := by
    have hNoWrap :=
      hSafety.pcNoWrap
        ({ pc := pc,
            instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) } :
          LocatedTarget)
        (mem_target_of_mem_emitted hTargetBlock hFirstMem)
    simpa using hNoWrap
  have hTargetPc := state_pc_eq_of_instrAt_of_noWrap hAt hNoWrapPc
  have hFullPc : fullState.pc = EvmYul.UInt256.ofNat pc := by
    rw [hRel.pc_eq]
    exact hTargetPc
  exact
    decode_next_after_push32_step_of_emitted_pair
      (target := target)
      (full := fullState)
      (fullPost := fullPost)
      (pc := pc)
      (gasCost := gasCost)
      (stepFuel := stepFuel)
      (value := EvmYul.UInt256.ofNat dest)
      (next := TargetInstr.jumpi)
      (rest := [])
      hEncoding
      (by simpa using hTargetBlock)
      hCode hFullPc hStep

theorem EvmYul_step_push32_preserves_gasExecRel
    {full target fullPost targetPost : EVMState} {value : Word}
    (hRel : GasExecRel full target)
    (hTarget :
      Target.stepInstr (TargetInstr.push32 value) target = .ok targetPost)
    (hFull :
      EvmYul.step (TargetInstr.push32 value).op
        (TargetInstr.push32 value).arg full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp [Target.stepInstr] at hTarget
  cases hTarget
  change
    Except.ok
      (EvmYul.EVM.State.replaceStackAndIncrPC
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
        (target.stack.push value) (pcΔ := 33)) = .ok fullPost at hFull
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem EvmYul_step_jump_of_stack
    (state : EVMState) (stack : EvmYul.Stack Word) (dest : Word)
    (hStack : state.stack = dest :: stack) :
    EvmYul.step EvmYul.Operation.JUMP none state =
      .ok { state with pc := dest, stack := stack } := by
  cases state with
  | mk shared pc stateStack execLength =>
      simp at hStack
      subst stateStack
      rfl

theorem stack_eq_cons_of_pop {stack rest : EvmYul.Stack Word} {head : Word}
    (hPop : EvmYul.Stack.pop stack = some (rest, head)) :
    stack = head :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop] at hPop
  | cons hd tl =>
      simp [EvmYul.Stack.pop] at hPop
      rcases hPop with ⟨hRest, hHead⟩
      subst rest
      subst head
      rfl

theorem EvmYul_step_jumpi_of_stack
    (state : EVMState) (stack : EvmYul.Stack Word)
    (dest cond : Word)
    (hStack : state.stack = dest :: cond :: stack) :
    EvmYul.step EvmYul.Operation.JUMPI none state =
      .ok
        { state with
          pc :=
            if cond != EvmYul.UInt256.ofNat 0 then
              dest
            else
              state.pc + EvmYul.UInt256.ofNat 1,
          stack := stack } := by
  cases state with
  | mk shared pc stateStack execLength =>
      simp at hStack
      subst stateStack
      rfl

theorem stack_eq_cons_cons_of_pop2
    {stack rest : EvmYul.Stack Word} {first second : Word}
    (hPop : EvmYul.Stack.pop2 stack = some (rest, first, second)) :
    stack = first :: second :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop2] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop2] at hPop
      | cons hd₁ tl₁ =>
          simp [EvmYul.Stack.pop2] at hPop
          rcases hPop with ⟨hRest, hFirst, hSecond⟩
          subst rest
          subst first
          subst second
          rfl

theorem EvmYul_step_jumpdest_eq (state : EVMState) :
    EvmYul.step EvmYul.Operation.JUMPDEST none state =
      .ok (EvmYul.EVM.State.incrPC state) := by
  cases state
  rfl

theorem EvmYul_step_jump_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr TargetInstr.jump target = .ok targetPost)
    (hFull :
      EvmYul.step TargetInstr.jump.op TargetInstr.jump.arg full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp only [TargetInstr.op, TargetInstr.arg] at hFull
  let fullGas : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  change
    EvmYul.step
        (EvmYul.Operation.StackMemFlow EvmYul.Operation.SMSFOp.JUMP)
        none fullGas = .ok fullPost at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [Target.stepInstr, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, dest⟩
      simp [Target.stepInstr, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, dest) := by
        simpa using hPop
      have hStackTarget : target.stack = dest :: stack :=
        stack_eq_cons_of_pop hPop
      have hStackFull : fullGas.stack = dest :: stack := by
        simpa [fullGas] using hStackTarget
      rw [EvmYul_step_jump_of_stack fullGas stack dest hStackFull] at hFull
      cases hFull
      simp [GasExecRel, fullGas]

theorem EvmYul_step_jumpi_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr TargetInstr.jumpi target = .ok targetPost)
    (hFull :
      EvmYul.step TargetInstr.jumpi.op TargetInstr.jumpi.arg full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp only [TargetInstr.op, TargetInstr.arg] at hFull
  let fullGas : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  change
    EvmYul.step
        (EvmYul.Operation.StackMemFlow EvmYul.Operation.SMSFOp.JUMPI)
        none fullGas = .ok fullPost at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [Target.stepInstr, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, dest, cond⟩
      simp [Target.stepInstr, hPop] at hTarget
      cases hTarget
      have hStackTarget : target.stack = dest :: cond :: stack :=
        stack_eq_cons_cons_of_pop2 hPop
      have hStackFull : fullGas.stack = dest :: cond :: stack := by
        simpa [fullGas] using hStackTarget
      rw [EvmYul_step_jumpi_of_stack fullGas stack dest cond hStackFull] at hFull
      cases hFull
      simp [GasExecRel, fullGas]

theorem EvmYul_step_jumpdest_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr TargetInstr.jumpdest target = .ok targetPost)
    (hFull :
      EvmYul.step TargetInstr.jumpdest.op TargetInstr.jumpdest.arg full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp only [TargetInstr.op, TargetInstr.arg] at hFull
  simp [Target.stepInstr] at hTarget
  cases hTarget
  rw [EvmYul_step_jumpdest_eq
    ({ target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength } : EVMState)] at hFull
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.incrPC]

theorem PrimStep_run_bin_preserves_gasExecRel
    (f : EvmYul.Primop.Binary)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.bin f).run target = .ok targetPost)
    (hFull : (PrimStep.bin f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop2 =
            some (stack, left, right) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_un_preserves_gasExecRel
    (f : EvmYul.Primop.Unary)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.un f).run target = .ok targetPost)
    (hFull : (PrimStep.un f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, value) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_tri_preserves_gasExecRel
    (f : EvmYul.Primop.Ternary)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.tri f).run target = .ok targetPost)
    (hFull : (PrimStep.tri f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop3 =
            some (stack, first, second, third) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_executionEnv_preserves_gasExecRel
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.executionEnv f).run target = .ok targetPost)
    (hFull : (PrimStep.executionEnv f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp [PrimStep.run, EvmYul.EVM.executionEnvOp] at hTarget hFull
  cases hTarget
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem PrimStep_run_state_preserves_gasExecRel
    (f : EvmYul.State EvmYul.OperationType.EVM → Word)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.state f).run target = .ok targetPost)
    (hFull : (PrimStep.state f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  simp [PrimStep.run, EvmYul.EVM.stateOp] at hTarget hFull
  cases hTarget
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem PrimStep_run_unaryExecutionEnv_preserves_gasExecRel
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.unaryExecutionEnv f).run target = .ok targetPost)
    (hFull : (PrimStep.unaryExecutionEnv f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, value) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_unaryState_preserves_gasExecRel
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word →
        EvmYul.State EvmYul.OperationType.EVM × Word)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.unaryState f).run target = .ok targetPost)
    (hFull : (PrimStep.unaryState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, value) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_binaryState_preserves_gasExecRel
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word → Word →
        EvmYul.State EvmYul.OperationType.EVM)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.binaryState f).run target = .ok targetPost)
    (hFull : (PrimStep.binaryState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop2 =
            some (stack, left, right) := by
        simpa using hPop
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_pop_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.pop.run target = .ok targetPost)
    (hFull : PrimStep.pop.run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      have hPopFull :
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).stack.pop =
            some (stack, value) := by
        simpa using hPop
      simp [PrimStep.run, hPopFull] at hFull
      cases hFull
      simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_bin_exists_gasExecRel
    (f : EvmYul.Primop.Binary)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.bin f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.bin f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
            (stack.push (f left right)),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop, fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_un_exists_gasExecRel
    (f : EvmYul.Primop.Unary)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.un f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.un f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
            (stack.push (f value)),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop, fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_tri_exists_gasExecRel
    (f : EvmYul.Primop.Ternary)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.tri f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.tri f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
            (stack.push (f first second third)),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop, fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_executionEnv_exists_gasExecRel
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.executionEnv f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.executionEnv f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  simp [PrimStep.run, EvmYul.EVM.executionEnvOp] at hTarget
  cases hTarget
  let fullState : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  refine
    ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
        (target.stack.push (f target.executionEnv)),
      ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.executionEnvOp, fullState]
    rfl
  · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_state_exists_gasExecRel
    (f : EvmYul.State EvmYul.OperationType.EVM → Word)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.state f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.state f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  simp [PrimStep.run, EvmYul.EVM.stateOp] at hTarget
  cases hTarget
  let fullState : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  refine
    ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
        (target.stack.push (f target.toState)),
      ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.stateOp, fullState]
    rfl
  · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_unaryExecutionEnv_exists_gasExecRel
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.unaryExecutionEnv f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.unaryExecutionEnv f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
            (stack.push (f target.executionEnv value)),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop,
          fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_unaryState_exists_gasExecRel
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word →
        EvmYul.State EvmYul.OperationType.EVM × Word)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.unaryState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.unaryState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hTarget
      cases hTarget
      let result := f target.toState value
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullState with toState := result.1 }
            (stack.push result.2),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop, fullState,
          result]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState, result]

theorem PrimStep_run_binaryState_exists_gasExecRel
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word → Word →
        EvmYul.State EvmYul.OperationType.EVM)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.binaryState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.binaryState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullState with toState := f target.toState left right }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop, fullState]
        rfl
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_pop_exists_gasExecRel
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.pop.run target = .ok targetPost) :
    ∃ fullPost,
      PrimStep.pop.run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, _value⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullState : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      refine ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState stack, ?_, ?_⟩
      · simp [PrimStep.run, hPop, fullState]
      · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_machineState_preserves_gasExecRel_of_eq
    (f : EvmYul.MachineState → Word)
    {full target fullPost targetPost : EVMState}
    (hValue : f full.toMachineState = f target.toMachineState)
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.machineState f).run target = .ok targetPost)
    (hFull : (PrimStep.machineState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  have hValue' :
      f
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).toMachineState =
        f target.toMachineState := by
    have hValue'' := hValue
    rw [hRel] at hValue''
    simpa using hValue''
  rw [hRel] at hFull
  simp [PrimStep.run, EvmYul.EVM.machineStateOp] at hTarget hFull
  rw [hValue'] at hFull
  cases hTarget
  cases hFull
  simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem PrimStep_run_machineState_exists_gasExecRel_of_eq
    (f : EvmYul.MachineState → Word)
    {full target targetPost : EVMState}
    (hValue : f full.toMachineState = f target.toMachineState)
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.machineState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.machineState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  have hValue' :
      f
          ({ target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength } : EVMState).toMachineState =
        f target.toMachineState := by
    have hValue'' := hValue
    rw [hRel] at hValue''
    simpa using hValue''
  rw [hRel]
  simp [PrimStep.run, EvmYul.EVM.machineStateOp] at hTarget
  cases hTarget
  let fullState : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  refine
    ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
        (target.stack.push (f target.toMachineState)),
      ?_, ?_⟩
  · simp [PrimStep.run, EvmYul.EVM.machineStateOp, fullState, hValue']
    rfl
  · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, fullState]

theorem PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
    (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
    {full target fullPost targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {left right : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        f fullMachine left right =
          { f targetMachine left right with
            gasAvailable := (f fullMachine left right).gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.binaryMachineState f).run target = .ok targetPost)
    (hFull : (PrimStep.binaryMachineState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop2 = some (stack, left, right) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.binaryMachineState f).run fullGas = .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPopFull] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (left := left) (right := right) hMachineRel
      rw [hMachine']
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
    (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
    {full target targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {left right : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        f fullMachine left right =
          { f targetMachine left right with
            gasAvailable := (f fullMachine left right).gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.binaryMachineState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.binaryMachineState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (left := left) (right := right) hMachineRel
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toMachineState := f fullGas.toMachineState left right }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop,
          fullGas]
        rfl
      · rw [hMachine']
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_binaryMachineStateWithResult_preserves_gasExecRel_of_rel
    (f : EvmYul.MachineState → Word → Word →
      Word × EvmYul.MachineState)
    {full target fullPost targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {left right : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        (f fullMachine left right).1 = (f targetMachine left right).1 ∧
          (f fullMachine left right).2 =
            { (f targetMachine left right).2 with
              gasAvailable := (f fullMachine left right).2.gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget :
      (PrimStep.binaryMachineStateWithResult f).run target = .ok targetPost)
    (hFull :
      (PrimStep.binaryMachineStateWithResult f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop2 = some (stack, left, right) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.binaryMachineStateWithResult f).run fullGas =
          .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPopFull] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (left := left) (right := right) hMachineRel
      rcases hMachine' with ⟨hValue, hState⟩
      rw [hValue, hState]
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_binaryMachineStateWithResult_exists_gasExecRel_of_rel
    (f : EvmYul.MachineState → Word → Word →
      Word × EvmYul.MachineState)
    {full target targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {left right : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        (f fullMachine left right).1 = (f targetMachine left right).1 ∧
          (f fullMachine left right).2 =
            { (f targetMachine left right).2 with
              gasAvailable := (f fullMachine left right).2.gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget :
      (PrimStep.binaryMachineStateWithResult f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.binaryMachineStateWithResult f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, left, right⟩
      simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (left := left) (right := right) hMachineRel
      rcases hMachine' with ⟨hValue, hState⟩
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toMachineState := (f fullGas.toMachineState left right).2 }
            (stack.push (f fullGas.toMachineState left right).1),
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop,
          fullGas]
        rfl
      · rw [hValue, hState]
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_ternaryMachineState_preserves_gasExecRel_of_rel
    (f :
      EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
    {full target fullPost targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {first second third : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        f fullMachine first second third =
          { f targetMachine first second third with
            gasAvailable :=
              (f fullMachine first second third).gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.ternaryMachineState f).run target = .ok targetPost)
    (hFull : (PrimStep.ternaryMachineState f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop3 = some (stack, first, second, third) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.ternaryMachineState f).run fullGas = .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPopFull] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (first := first) (second := second) (third := third)
          hMachineRel
      rw [hMachine']
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_ternaryMachineState_exists_gasExecRel_of_rel
    (f :
      EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
    {full target targetPost : EVMState}
    (hMachine :
      ∀ {fullMachine targetMachine : EvmYul.MachineState}
        {first second third : Word},
        fullMachine =
          { targetMachine with gasAvailable := fullMachine.gasAvailable } →
        f fullMachine first second third =
          { f targetMachine first second third with
            gasAvailable :=
              (f fullMachine first second third).gasAvailable })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.ternaryMachineState f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.ternaryMachineState f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMachine' :=
        hMachine (first := first) (second := second) (third := third)
          hMachineRel
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toMachineState :=
                f fullGas.toMachineState first second third }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop,
          fullGas]
        rfl
      · rw [hMachine']
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_ternaryCopy_preserves_gasExecRel_of_rel
    (f :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM)
    {full target fullPost targetPost : EVMState}
    (hShared :
      ∀ {fullShared targetShared : EvmYul.SharedState .EVM}
        {first second third : Word},
        fullShared =
          { targetShared with
            toMachineState :=
              { targetShared.toMachineState with
                gasAvailable := fullShared.toMachineState.gasAvailable } } →
        f fullShared first second third =
          { f targetShared first second third with
            toMachineState :=
              { (f targetShared first second third).toMachineState with
                gasAvailable :=
                  (f fullShared first second third).toMachineState.gasAvailable } })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.ternaryCopy f).run target = .ok targetPost)
    (hFull : (PrimStep.ternaryCopy f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop3 = some (stack, first, second, third) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.ternaryCopy f).run fullGas = .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPopFull] at hFull
      cases hFull
      have hSharedRel :
          fullGas.toSharedState =
            { target.toSharedState with
              toMachineState :=
                { target.toSharedState.toMachineState with
                  gasAvailable :=
                    fullGas.toSharedState.toMachineState.gasAvailable } } := by
        simp [fullGas]
      have hShared' :=
        hShared (first := first) (second := second) (third := third)
          hSharedRel
      rw [hShared']
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_ternaryCopy_exists_gasExecRel_of_rel
    (f :
      EvmYul.SharedState .EVM → Word → Word → Word →
        EvmYul.SharedState .EVM)
    {full target targetPost : EVMState}
    (hShared :
      ∀ {fullShared targetShared : EvmYul.SharedState .EVM}
        {first second third : Word},
        fullShared =
          { targetShared with
            toMachineState :=
              { targetShared.toMachineState with
                gasAvailable := fullShared.toMachineState.gasAvailable } } →
        f fullShared first second third =
          { f targetShared first second third with
            toMachineState :=
              { (f targetShared first second third).toMachineState with
                gasAvailable :=
                  (f fullShared first second third).toMachineState.gasAvailable } })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.ternaryCopy f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.ternaryCopy f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third⟩
      simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hSharedRel :
          fullGas.toSharedState =
            { target.toSharedState with
              toMachineState :=
                { target.toSharedState.toMachineState with
                  gasAvailable :=
                    fullGas.toSharedState.toMachineState.gasAvailable } } := by
        simp [fullGas]
      have hShared' :=
        hShared (first := first) (second := second) (third := third)
          hSharedRel
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toSharedState :=
                f fullGas.toSharedState first second third }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop, fullGas]
        rfl
      · rw [hShared']
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_quaternaryCopy_preserves_gasExecRel_of_rel
    (f :
      EvmYul.SharedState .EVM → Word → Word → Word → Word →
        EvmYul.SharedState .EVM)
    {full target fullPost targetPost : EVMState}
    (hShared :
      ∀ {fullShared targetShared : EvmYul.SharedState .EVM}
        {first second third fourth : Word},
        fullShared =
          { targetShared with
            toMachineState :=
              { targetShared.toMachineState with
                gasAvailable := fullShared.toMachineState.gasAvailable } } →
        f fullShared first second third fourth =
          { f targetShared first second third fourth with
            toMachineState :=
              { (f targetShared first second third fourth).toMachineState with
                gasAvailable :=
                  (f fullShared first second third fourth).toMachineState.gasAvailable } })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.quaternaryCopy f).run target = .ok targetPost)
    (hFull : (PrimStep.quaternaryCopy f).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop4 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third, fourth⟩
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hPopFull :
          fullGas.stack.pop4 = some (stack, first, second, third, fourth) := by
        simpa [fullGas] using hPop
      change
        (PrimStep.quaternaryCopy f).run fullGas = .ok fullPost at hFull
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPopFull] at hFull
      cases hFull
      have hSharedRel :
          fullGas.toSharedState =
            { target.toSharedState with
              toMachineState :=
                { target.toSharedState.toMachineState with
                  gasAvailable :=
                    fullGas.toSharedState.toMachineState.gasAvailable } } := by
        simp [fullGas]
      have hShared' :=
        hShared (first := first) (second := second) (third := third)
          (fourth := fourth) hSharedRel
      rw [hShared']
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem PrimStep_run_quaternaryCopy_exists_gasExecRel_of_rel
    (f :
      EvmYul.SharedState .EVM → Word → Word → Word → Word →
        EvmYul.SharedState .EVM)
    {full target targetPost : EVMState}
    (hShared :
      ∀ {fullShared targetShared : EvmYul.SharedState .EVM}
        {first second third fourth : Word},
        fullShared =
          { targetShared with
            toMachineState :=
              { targetShared.toMachineState with
                gasAvailable := fullShared.toMachineState.gasAvailable } } →
        f fullShared first second third fourth =
          { f targetShared first second third fourth with
            toMachineState :=
              { (f targetShared first second third fourth).toMachineState with
                gasAvailable :=
                  (f fullShared first second third fourth).toMachineState.gasAvailable } })
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.quaternaryCopy f).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.quaternaryCopy f).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  cases hPop : target.stack.pop4 with
  | none =>
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, first, second, third, fourth⟩
      simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      have hSharedRel :
          fullGas.toSharedState =
            { target.toSharedState with
              toMachineState :=
                { target.toSharedState.toMachineState with
                  gasAvailable :=
                    fullGas.toSharedState.toMachineState.gasAvailable } } := by
        simp [fullGas]
      have hShared' :=
        hShared (first := first) (second := second) (third := third)
          (fourth := fourth) hSharedRel
      refine
        ⟨EvmYul.EVM.State.replaceStackAndIncrPC
            { fullGas with
              toSharedState :=
                f fullGas.toSharedState first second third fourth }
            stack,
          ?_, ?_⟩
      · simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop, fullGas]
        rfl
      · rw [hShared']
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem PrimStep_run_dup_preserves_gasExecRel
    (n : Nat)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.dup n).run target = .ok targetPost)
    (hFull : (PrimStep.dup n).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  by_cases hLen : n ≤ target.stack.length
  · simp [PrimStep.run, EvmYul.dup, hLen] at hTarget hFull
    cases hTarget
    cases hFull
    simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [PrimStep.run, EvmYul.dup, hLen] at hTarget

theorem PrimStep_run_dup_exists_gasExecRel
    (n : Nat)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.dup n).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.dup n).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  by_cases hLen : n ≤ target.stack.length
  · simp [PrimStep.run, EvmYul.dup, hLen] at hTarget
    cases hTarget
    let fullState : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    refine
      ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
          ((target.stack.take n).getLast! :: target.stack),
        ?_, ?_⟩
    · simp [PrimStep.run, EvmYul.dup, hLen, fullState]
    · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, fullState]
  · simp [PrimStep.run, EvmYul.dup, hLen] at hTarget

theorem PrimStep_run_swap_preserves_gasExecRel
    (n : Nat)
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.swap n).run target = .ok targetPost)
    (hFull : (PrimStep.swap n).run full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  by_cases hLen : n + 1 ≤ target.stack.length
  · simp [PrimStep.run, EvmYul.swap, hLen] at hTarget hFull
    cases hTarget
    cases hFull
    simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [PrimStep.run, EvmYul.swap, hLen] at hTarget

theorem PrimStep_run_swap_exists_gasExecRel
    (n : Nat)
    {full target targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : (PrimStep.swap n).run target = .ok targetPost) :
    ∃ fullPost,
      (PrimStep.swap n).run full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [hRel]
  by_cases hLen : n + 1 ≤ target.stack.length
  · simp [PrimStep.run, EvmYul.swap, hLen] at hTarget
    cases hTarget
    let fullState : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    let top := target.stack.take (n + 1)
    let bottom := target.stack.drop (n + 1)
    refine
      ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullState
          (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom),
        ?_, ?_⟩
    · simp [PrimStep.run, EvmYul.swap, hLen, fullState, top, bottom]
    · simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, fullState, top, bottom]
  · simp [PrimStep.run, EvmYul.swap, hLen] at hTarget

theorem PrimStep_run_invalid_preserves_gasExecRel
    {target fullPost targetPost : EVMState}
    (hTarget : PrimStep.invalid.run target = .ok targetPost) :
    GasExecRel fullPost targetPost := by
  simp [PrimStep.run] at hTarget

theorem machine_mload_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState} {offset : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    (fullMachine.mload offset).1 = (targetMachine.mload offset).1 ∧
      (fullMachine.mload offset).2 =
        { (targetMachine.mload offset).2 with
          gasAvailable := (fullMachine.mload offset).2.gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.mload, EvmYul.MachineState.lookupMemory]

theorem machine_mstore_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {offset value : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.mstore fullMachine offset value =
      { EvmYul.MachineState.mstore targetMachine offset value with
        gasAvailable :=
          (EvmYul.MachineState.mstore fullMachine offset value).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    EvmYul.writeBytes]

theorem machine_mstore8_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {offset value : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.mstore8 fullMachine offset value =
      { EvmYul.MachineState.mstore8 targetMachine offset value with
        gasAvailable :=
          (EvmYul.MachineState.mstore8 fullMachine offset value).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.mstore8, EvmYul.writeBytes]

theorem machine_mcopy_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {writeStart readStart size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.mcopy fullMachine writeStart readStart size =
      { EvmYul.MachineState.mcopy targetMachine writeStart readStart size with
        gasAvailable :=
          (EvmYul.MachineState.mcopy fullMachine writeStart readStart size).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.mcopy, EvmYul.writeBytes]

theorem machine_keccak256_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {offset size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    (EvmYul.MachineState.keccak256 fullMachine offset size).1 =
        (EvmYul.MachineState.keccak256 targetMachine offset size).1 ∧
      (EvmYul.MachineState.keccak256 fullMachine offset size).2 =
        { (EvmYul.MachineState.keccak256 targetMachine offset size).2 with
          gasAvailable :=
            (EvmYul.MachineState.keccak256 fullMachine offset size).2.gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.keccak256]

theorem machine_returndatacopy_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {mstart rstart size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    fullMachine.returndatacopy mstart rstart size =
      { targetMachine.returndatacopy mstart rstart size with
        gasAvailable :=
          (fullMachine.returndatacopy mstart rstart size).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.returndatacopy, EvmYul.writeBytes]

theorem machine_evmReturn_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {mstart size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.evmReturn fullMachine mstart size =
      { EvmYul.MachineState.evmReturn targetMachine mstart size with
        gasAvailable :=
          (EvmYul.MachineState.evmReturn fullMachine mstart size).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.evmReturn]

theorem machine_evmRevert_gasAvailable_rel
    {fullMachine targetMachine : EvmYul.MachineState}
    {mstart size : Word}
    (hRel :
      fullMachine =
        { targetMachine with gasAvailable := fullMachine.gasAvailable }) :
    EvmYul.MachineState.evmRevert fullMachine mstart size =
      { EvmYul.MachineState.evmRevert targetMachine mstart size with
        gasAvailable :=
          (EvmYul.MachineState.evmRevert fullMachine mstart size).gasAvailable } := by
  rw [hRel]
  simp [EvmYul.MachineState.evmRevert, EvmYul.MachineState.evmReturn]

theorem shared_calldatacopy_gasAvailable_rel
    {fullShared targetShared : EvmYul.SharedState .EVM}
    {mstart datastart size : Word}
    (hRel :
      fullShared =
        { targetShared with
          toMachineState :=
            { targetShared.toMachineState with
              gasAvailable := fullShared.toMachineState.gasAvailable } }) :
    EvmYul.SharedState.calldatacopy fullShared mstart datastart size =
      { EvmYul.SharedState.calldatacopy targetShared mstart datastart size with
        toMachineState :=
          { (EvmYul.SharedState.calldatacopy targetShared mstart datastart
              size).toMachineState with
            gasAvailable :=
              (EvmYul.SharedState.calldatacopy fullShared mstart datastart
                size).toMachineState.gasAvailable } } := by
  rw [hRel]
  simp [EvmYul.SharedState.calldatacopy]

theorem shared_codeCopy_gasAvailable_rel
    {fullShared targetShared : EvmYul.SharedState .EVM}
    {mstart cstart size : Word}
    (hRel :
      fullShared =
        { targetShared with
          toMachineState :=
            { targetShared.toMachineState with
              gasAvailable := fullShared.toMachineState.gasAvailable } }) :
    EvmYul.SharedState.codeCopy fullShared mstart cstart size =
      { EvmYul.SharedState.codeCopy targetShared mstart cstart size with
        toMachineState :=
          { (EvmYul.SharedState.codeCopy targetShared mstart cstart
              size).toMachineState with
            gasAvailable :=
              (EvmYul.SharedState.codeCopy fullShared mstart cstart
                size).toMachineState.gasAvailable } } := by
  rw [hRel]
  simp [EvmYul.SharedState.codeCopy]

theorem shared_extCodeCopy'_gasAvailable_rel
    {fullShared targetShared : EvmYul.SharedState .EVM}
    {account mstart cstart size : Word}
    (hRel :
      fullShared =
        { targetShared with
          toMachineState :=
            { targetShared.toMachineState with
              gasAvailable := fullShared.toMachineState.gasAvailable } }) :
    EvmYul.SharedState.extCodeCopy' fullShared account mstart cstart size =
      { EvmYul.SharedState.extCodeCopy' targetShared account mstart cstart
          size with
        toMachineState :=
          { (EvmYul.SharedState.extCodeCopy' targetShared account mstart
              cstart size).toMachineState with
            gasAvailable :=
              (EvmYul.SharedState.extCodeCopy' fullShared account mstart
                cstart size).toMachineState.gasAvailable } } := by
  rw [hRel]
  simp [EvmYul.SharedState.extCodeCopy']

theorem machine_mstore_gasAvailable_eq
    {machine : EvmYul.MachineState} {offset value : Word} :
    (EvmYul.MachineState.mstore machine offset value).gasAvailable =
      machine.gasAvailable := by
  simp [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    EvmYul.writeBytes]

theorem machine_mstore8_gasAvailable_eq
    {machine : EvmYul.MachineState} {offset value : Word} :
    (EvmYul.MachineState.mstore8 machine offset value).gasAvailable =
      machine.gasAvailable := by
  simp [EvmYul.MachineState.mstore8, EvmYul.writeBytes]

theorem machine_mcopy_gasAvailable_eq
    {machine : EvmYul.MachineState} {writeStart readStart size : Word} :
    (EvmYul.MachineState.mcopy machine writeStart readStart size).gasAvailable =
      machine.gasAvailable := by
  simp [EvmYul.MachineState.mcopy, EvmYul.writeBytes]

theorem machine_keccak256_gasAvailable_eq
    {machine : EvmYul.MachineState} {offset size : Word} :
    (EvmYul.MachineState.keccak256 machine offset size).2.gasAvailable =
      machine.gasAvailable := by
  simp [EvmYul.MachineState.keccak256]

theorem shared_calldatacopy_gasAvailable_eq
    {shared : EvmYul.SharedState .EVM} {mstart datastart size : Word} :
    (EvmYul.SharedState.calldatacopy shared mstart datastart
      size).toMachineState.gasAvailable =
      shared.toMachineState.gasAvailable := by
  simp [EvmYul.SharedState.calldatacopy]

theorem shared_codeCopy_gasAvailable_eq
    {shared : EvmYul.SharedState .EVM} {mstart cstart size : Word} :
    (EvmYul.SharedState.codeCopy shared mstart cstart
      size).toMachineState.gasAvailable =
      shared.toMachineState.gasAvailable := by
  simp [EvmYul.SharedState.codeCopy]

theorem shared_extCodeCopy'_gasAvailable_eq
    {shared : EvmYul.SharedState .EVM}
    {account mstart cstart size : Word} :
    (EvmYul.SharedState.extCodeCopy' shared account mstart cstart
      size).toMachineState.gasAvailable =
      shared.toMachineState.gasAvailable := by
  simp [EvmYul.SharedState.extCodeCopy']

theorem PrimStep_run_bin_gasAvailable_eq
    (f : EvmYul.Primop.Binary) {state post : EVMState}
    (hRun : (PrimStep.bin f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.execBinOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_un_gasAvailable_eq
    (f : EvmYul.Primop.Unary) {state post : EVMState}
    (hRun : (PrimStep.un f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.execUnOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_tri_gasAvailable_eq
    (f : EvmYul.Primop.Ternary) {state post : EVMState}
    (hRun : (PrimStep.tri f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.execTriOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_executionEnv_gasAvailable_eq
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word)
    {state post : EVMState}
    (hRun : (PrimStep.executionEnv f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.executionEnvOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  cases hRun
  rfl

theorem PrimStep_run_unaryExecutionEnv_gasAvailable_eq
    (f : EvmYul.ExecutionEnv EvmYul.OperationType.EVM → Word → Word)
    {state post : EVMState}
    (hRun : (PrimStep.unaryExecutionEnv f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_machineState_gasAvailable_eq
    (f : EvmYul.MachineState → Word) {state post : EVMState}
    (hRun : (PrimStep.machineState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.machineStateOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  cases hRun
  rfl

theorem PrimStep_run_binaryMachineState_gasAvailable_eq
    (f : EvmYul.MachineState → Word → Word → EvmYul.MachineState)
    (hGas :
      ∀ machine left right,
        (f machine left right).gasAvailable = machine.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.binaryMachineState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_binaryMachineStateWithResult_gasAvailable_eq
    (f : EvmYul.MachineState → Word → Word → Word × EvmYul.MachineState)
    (hGas :
      ∀ machine left right,
        (f machine left right).2.gasAvailable = machine.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.binaryMachineStateWithResult f).run state =
      .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp'] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_ternaryMachineState_gasAvailable_eq
    (f : EvmYul.MachineState → Word → Word → Word → EvmYul.MachineState)
    (hGas :
      ∀ machine first second third,
        (f machine first second third).gasAvailable =
          machine.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.ternaryMachineState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_state_gasAvailable_eq
    (f : EvmYul.State EvmYul.OperationType.EVM → Word)
    {state post : EVMState}
    (hRun : (PrimStep.state f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.stateOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  cases hRun
  rfl

theorem PrimStep_run_unaryState_gasAvailable_eq
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word →
        EvmYul.State EvmYul.OperationType.EVM × Word)
    {state post : EVMState}
    (hRun : (PrimStep.unaryState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.unaryStateOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_binaryState_gasAvailable_eq
    (f :
      EvmYul.State EvmYul.OperationType.EVM → Word → Word →
        EvmYul.State EvmYul.OperationType.EVM)
    {state post : EVMState}
    (hRun : (PrimStep.binaryState f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.binaryStateOp] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_ternaryCopy_gasAvailable_eq
    (f :
      EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
        Word → EvmYul.SharedState EvmYul.OperationType.EVM)
    (hGas :
      ∀ shared first second third,
        (f shared first second third).toMachineState.gasAvailable =
          shared.toMachineState.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.ternaryCopy f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_quaternaryCopy_gasAvailable_eq
    (f :
      EvmYul.SharedState EvmYul.OperationType.EVM → Word → Word →
        Word → Word → EvmYul.SharedState EvmYul.OperationType.EVM)
    (hGas :
      ∀ shared first second third fourth,
        (f shared first second third fourth).toMachineState.gasAvailable =
          shared.toMachineState.gasAvailable)
    {state post : EVMState}
    (hRun : (PrimStep.quaternaryCopy f).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp] at hRun
  split at hRun <;> cases hRun
  · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, hGas]

theorem PrimStep_run_pop_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.pop.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_mload_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.mload.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.MachineState.mload,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_returndatacopy_gasAvailable_eq
    {state post : EVMState}
    (hRun : PrimStep.returndatacopy.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.MachineState.returndatacopy,
    EvmYul.writeBytes, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun
  · split at hRun
    · simp at hRun
    · cases hRun
      rfl
  · simp at hRun

theorem PrimStep_run_dup_gasAvailable_eq (n : Nat)
    {state post : EVMState}
    (hRun : (PrimStep.dup n).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.dup] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_swap_gasAvailable_eq (n : Nat)
    {state post : EVMState}
    (hRun : (PrimStep.swap n).run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.swap] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log0_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log0.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log1_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log1.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log2_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log2.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log3_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log3.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_log4_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.log4.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run, EvmYul.SharedState.logOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC] at hRun
  split at hRun <;> cases hRun <;> rfl

theorem PrimStep_run_invalid_gasAvailable_eq {state post : EVMState}
    (hRun : PrimStep.invalid.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  simp [PrimStep.run] at hRun

set_option maxHeartbeats 1200000 in
theorem PrimStep_run_of_continuing_prim_gasAvailable_eq
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    {state post : EVMState}
    (hRun : step.run state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  cases step with
  | bin f => exact PrimStep_run_bin_gasAvailable_eq f hRun
  | un f => exact PrimStep_run_un_gasAvailable_eq f hRun
  | tri f => exact PrimStep_run_tri_gasAvailable_eq f hRun
  | executionEnv f =>
      exact PrimStep_run_executionEnv_gasAvailable_eq f hRun
  | unaryExecutionEnv f =>
      exact PrimStep_run_unaryExecutionEnv_gasAvailable_eq f hRun
  | machineState f =>
      exact PrimStep_run_machineState_gasAvailable_eq f hRun
  | binaryMachineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · exact PrimStep_run_binaryMachineState_gasAvailable_eq
          EvmYul.MachineState.mstore
          (fun machine left right =>
            machine_mstore_gasAvailable_eq (machine := machine)
              (offset := left) (value := right)) hRun
      · exact PrimStep_run_binaryMachineState_gasAvailable_eq
          EvmYul.MachineState.mstore8
          (fun machine left right =>
            machine_mstore8_gasAvailable_eq (machine := machine)
              (offset := left) (value := right)) hRun
  | binaryMachineStateWithResult f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact PrimStep_run_binaryMachineStateWithResult_gasAvailable_eq
        EvmYul.MachineState.keccak256
        (fun machine left right =>
          machine_keccak256_gasAvailable_eq (machine := machine)
            (offset := left) (size := right)) hRun
  | ternaryMachineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact PrimStep_run_ternaryMachineState_gasAvailable_eq
        EvmYul.MachineState.mcopy
        (fun machine first second third =>
          machine_mcopy_gasAvailable_eq (machine := machine)
            (writeStart := first) (readStart := second) (size := third)) hRun
  | state f => exact PrimStep_run_state_gasAvailable_eq f hRun
  | unaryState f => exact PrimStep_run_unaryState_gasAvailable_eq f hRun
  | binaryState f => exact PrimStep_run_binaryState_gasAvailable_eq f hRun
  | ternaryCopy f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · exact PrimStep_run_ternaryCopy_gasAvailable_eq
          EvmYul.SharedState.calldatacopy
          (fun shared first second third =>
            shared_calldatacopy_gasAvailable_eq (shared := shared)
              (mstart := first) (datastart := second) (size := third))
          hRun
      · exact PrimStep_run_ternaryCopy_gasAvailable_eq
          EvmYul.SharedState.codeCopy
          (fun shared first second third =>
            shared_codeCopy_gasAvailable_eq (shared := shared)
              (mstart := first) (cstart := second) (size := third)) hRun
  | quaternaryCopy f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact PrimStep_run_quaternaryCopy_gasAvailable_eq
        EvmYul.SharedState.extCodeCopy'
        (fun shared first second third fourth =>
          shared_extCodeCopy'_gasAvailable_eq (shared := shared)
            (account := first) (mstart := second) (cstart := third)
            (size := fourth)) hRun
  | pop => exact PrimStep_run_pop_gasAvailable_eq hRun
  | mload => exact PrimStep_run_mload_gasAvailable_eq hRun
  | returndatacopy =>
      exact PrimStep_run_returndatacopy_gasAvailable_eq hRun
  | dup n => exact PrimStep_run_dup_gasAvailable_eq n hRun
  | swap n => exact PrimStep_run_swap_gasAvailable_eq n hRun
  | log0 => exact PrimStep_run_log0_gasAvailable_eq hRun
  | log1 => exact PrimStep_run_log1_gasAvailable_eq hRun
  | log2 => exact PrimStep_run_log2_gasAvailable_eq hRun
  | log3 => exact PrimStep_run_log3_gasAvailable_eq hRun
  | log4 => exact PrimStep_run_log4_gasAvailable_eq hRun
  | invalid => exact PrimStep_run_invalid_gasAvailable_eq hRun

theorem EvmYul_step_continuing_prim_gasAvailable_eq
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step)
    {state post : EVMState}
    (hRun : EvmYul.step op.toEVM none state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  have hRunStep : step.run state = .ok post := by
    rw [← EvmYul_step_eq_continuingStep_run_exact hStep state]
    exact hRun
  exact PrimStep_run_of_continuing_prim_gasAvailable_eq hStep hRunStep

theorem EvmYul_step_pop_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.pop.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.POP none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, value⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.POP none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = value :: stack :=
        stack_eq_cons_of_pop hPop
      have hStackFull : fullGas.stack = value :: stack := by
        simpa [fullGas] using hStackTarget
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.POP none fullGas =
            .ok (EvmYul.EVM.State.replaceStackAndIncrPC fullGas stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem EvmYul_step_mload_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.mload.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.MLOAD none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.MLOAD none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = offset :: stack :=
        stack_eq_cons_of_pop hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.MLOAD none fullGas =
            .ok
              (let loaded := fullGas.toMachineState.mload offset
               EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with toMachineState := loaded.2 }
                (stack.push loaded.1)) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      have hMachineRel :
          fullGas.toMachineState =
            { target.toMachineState with
              gasAvailable := fullGas.toMachineState.gasAvailable } := by
        simp [fullGas]
      have hMload :=
        machine_mload_gasAvailable_rel (offset := offset) hMachineRel
      rcases hMload with ⟨hMloadValue, hMloadState⟩
      dsimp
      rw [hMloadValue, hMloadState]
      simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]

theorem stack_eq_cons_cons_cons_of_pop3
    {stack rest : EvmYul.Stack Word} {first second third : Word}
    (hPop : EvmYul.Stack.pop3 stack = some (rest, first, second, third)) :
    stack = first :: second :: third :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop3] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop3] at hPop
      | cons hd₁ tl₁ =>
          cases tl₁ with
          | nil =>
              simp [EvmYul.Stack.pop3] at hPop
          | cons hd₂ tl₂ =>
              simp [EvmYul.Stack.pop3] at hPop
              rcases hPop with ⟨hRest, hFirst, hSecond, hThird⟩
              subst rest
              subst first
              subst second
              subst third
              rfl

theorem EvmYul_step_returndatacopy_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.returndatacopy.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.RETURNDATACOPY none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, mstart, rstart, size⟩
      simp [PrimStep.run, hPop] at hTarget
      by_cases hBounds :
          target.returnData.size < rstart.toNat + size.toNat
      · simp [hBounds] at hTarget
      · simp [hBounds] at hTarget
        cases hTarget
        let fullGas : EVMState :=
          { target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength }
        change
          EvmYul.step (τ := .EVM) EvmYul.Operation.RETURNDATACOPY none
            fullGas = .ok fullPost at hFull
        have hStackTarget :
            target.stack = mstart :: rstart :: size :: stack :=
          stack_eq_cons_cons_cons_of_pop3 hPop
        have hStep :
            EvmYul.step (τ := .EVM) EvmYul.Operation.RETURNDATACOPY none
                fullGas =
              .ok
                (EvmYul.EVM.State.replaceStackAndIncrPC
                  { fullGas with
                    toMachineState :=
                      fullGas.toMachineState.returndatacopy mstart rstart size }
                  stack) := by
          dsimp [fullGas]
          rw [hStackTarget]
          rw [EvmYul_step_returndatacopy_eq_PrimStep_run]
          simp [PrimStep.run, EvmYul.Stack.pop3, hBounds]
        rw [hStep] at hFull
        cases hFull
        have hMachineRel :
            fullGas.toMachineState =
              { target.toMachineState with
                gasAvailable := fullGas.toMachineState.gasAvailable } := by
          simp [fullGas]
        have hCopy :=
          machine_returndatacopy_gasAvailable_rel
            (mstart := mstart) (rstart := rstart) (size := size) hMachineRel
        dsimp
        rw [hCopy]
        simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem EvmYul_step_log0_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log0.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG0 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop2 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset, size⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG0 none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = offset :: size :: stack :=
        stack_eq_cons_cons_of_pop2 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG0 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[]
                      fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem stack_eq_cons_cons_cons_cons_of_pop4
    {stack rest : EvmYul.Stack Word}
    {first second third fourth : Word}
    (hPop :
      EvmYul.Stack.pop4 stack = some (rest, first, second, third, fourth)) :
    stack = first :: second :: third :: fourth :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop4] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop4] at hPop
      | cons hd₁ tl₁ =>
          cases tl₁ with
          | nil =>
              simp [EvmYul.Stack.pop4] at hPop
          | cons hd₂ tl₂ =>
              cases tl₂ with
              | nil =>
                  simp [EvmYul.Stack.pop4] at hPop
              | cons hd₃ tl₃ =>
                  simp [EvmYul.Stack.pop4] at hPop
                  rcases hPop with ⟨hRest, hFirst, hSecond, hThird, hFourth⟩
                  subst rest
                  subst first
                  subst second
                  subst third
                  subst fourth
                  rfl

theorem stack_eq_cons_cons_cons_cons_cons_of_pop5
    {stack rest : EvmYul.Stack Word}
    {first second third fourth fifth : Word}
    (hPop :
      EvmYul.Stack.pop5 stack =
        some (rest, first, second, third, fourth, fifth)) :
    stack = first :: second :: third :: fourth :: fifth :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop5] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop5] at hPop
      | cons hd₁ tl₁ =>
          cases tl₁ with
          | nil =>
              simp [EvmYul.Stack.pop5] at hPop
          | cons hd₂ tl₂ =>
              cases tl₂ with
              | nil =>
                  simp [EvmYul.Stack.pop5] at hPop
              | cons hd₃ tl₃ =>
                  cases tl₃ with
                  | nil =>
                      simp [EvmYul.Stack.pop5] at hPop
                  | cons hd₄ tl₄ =>
                      simp [EvmYul.Stack.pop5] at hPop
                      rcases hPop with
                        ⟨hRest, hFirst, hSecond, hThird, hFourth, hFifth⟩
                      subst rest
                      subst first
                      subst second
                      subst third
                      subst fourth
                      subst fifth
                      rfl

theorem stack_eq_cons_cons_cons_cons_cons_cons_of_pop6
    {stack rest : EvmYul.Stack Word}
    {first second third fourth fifth sixth : Word}
    (hPop :
      EvmYul.Stack.pop6 stack =
        some (rest, first, second, third, fourth, fifth, sixth)) :
    stack = first :: second :: third :: fourth :: fifth :: sixth :: rest := by
  cases stack with
  | nil =>
      simp [EvmYul.Stack.pop6] at hPop
  | cons hd tl =>
      cases tl with
      | nil =>
          simp [EvmYul.Stack.pop6] at hPop
      | cons hd₁ tl₁ =>
          cases tl₁ with
          | nil =>
              simp [EvmYul.Stack.pop6] at hPop
          | cons hd₂ tl₂ =>
              cases tl₂ with
              | nil =>
                  simp [EvmYul.Stack.pop6] at hPop
              | cons hd₃ tl₃ =>
                  cases tl₃ with
                  | nil =>
                      simp [EvmYul.Stack.pop6] at hPop
                  | cons hd₄ tl₄ =>
                      cases tl₄ with
                      | nil =>
                          simp [EvmYul.Stack.pop6] at hPop
                      | cons hd₅ tl₅ =>
                          simp [EvmYul.Stack.pop6] at hPop
                          rcases hPop with
                            ⟨hRest, hFirst, hSecond, hThird, hFourth,
                              hFifth, hSixth⟩
                          subst rest
                          subst first
                          subst second
                          subst third
                          subst fourth
                          subst fifth
                          subst sixth
                          rfl

theorem EvmYul_step_log1_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log1.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG1 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop3 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset, size, topic0⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG1 none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = offset :: size :: topic0 :: stack :=
        stack_eq_cons_cons_cons_of_pop3 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG1 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[topic0]
                      fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_log2_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log2.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG2 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop4 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset, size, topic0, topic1⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG2 none fullGas =
          .ok fullPost at hFull
      have hStackTarget :
          target.stack = offset :: size :: topic0 :: topic1 :: stack :=
        stack_eq_cons_cons_cons_cons_of_pop4 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG2 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[topic0, topic1]
                      fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_log3_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log3.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG3 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop5 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with ⟨stack, offset, size, topic0, topic1, topic2⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG3 none fullGas =
          .ok fullPost at hFull
      have hStackTarget :
          target.stack =
            offset :: size :: topic0 :: topic1 :: topic2 :: stack :=
        stack_eq_cons_cons_cons_cons_cons_of_pop5 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG3 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size
                      #[topic0, topic1, topic2] fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_log4_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget : PrimStep.log4.run target = .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.LOG4 none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop6 with
  | none =>
      simp [PrimStep.run, hPop] at hTarget
  | some popped =>
      rcases popped with
        ⟨stack, offset, size, topic0, topic1, topic2, topic3⟩
      simp [PrimStep.run, hPop] at hTarget
      cases hTarget
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.LOG4 none fullGas =
          .ok fullPost at hFull
      have hStackTarget :
          target.stack =
            offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: stack :=
        stack_eq_cons_cons_cons_cons_cons_cons_of_pop6 hPop
      have hStep :
          EvmYul.step (τ := .EVM) EvmYul.Operation.LOG4 none fullGas =
            .ok
              (EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size
                      #[topic0, topic1, topic2, topic3]
                      fullGas.toSharedState }
                stack) := by
        dsimp [fullGas]
        rw [hStackTarget]
        rfl
      rw [hStep] at hFull
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_stop_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  have hTargetStep :
      EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none target =
        .ok
          { target with
            toMachineState :=
              (target.toMachineState.setReturnData ByteArray.empty).setHReturn
                ByteArray.empty } := by
    rfl
  rw [hTargetStep] at hTarget
  cases hTarget
  let fullGas : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  change
    EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none fullGas =
      .ok fullPost at hFull
  have hFullStep :
      EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none fullGas =
        .ok
          { fullGas with
            toMachineState :=
              (fullGas.toMachineState.setReturnData ByteArray.empty).setHReturn
                ByteArray.empty } := by
    rfl
  rw [hFullStep] at hFull
  cases hFull
  simp [GasExecRel, fullGas, EvmYul.MachineState.setReturnData,
    EvmYul.MachineState.setHReturn]

theorem EvmYul_step_pc_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.PC none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.PC none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  have hTargetStep :
      EvmYul.step (τ := .EVM) EvmYul.Operation.PC none target =
        .ok
          (EvmYul.EVM.State.replaceStackAndIncrPC target
            (target.stack.push target.pc)) := by
    rfl
  rw [hTargetStep] at hTarget
  cases hTarget
  let fullGas : EVMState :=
    { target with
      gasAvailable := full.gasAvailable,
      execLength := full.execLength }
  change
    EvmYul.step (τ := .EVM) EvmYul.Operation.PC none fullGas =
      .ok fullPost at hFull
  have hFullStep :
      EvmYul.step (τ := .EVM) EvmYul.Operation.PC none fullGas =
        .ok
          (EvmYul.EVM.State.replaceStackAndIncrPC fullGas
            (fullGas.stack.push fullGas.pc)) := by
    rfl
  rw [hFullStep] at hFull
  cases hFull
  simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]

theorem EvmYul_step_return_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.RETURN none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.RETURN none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  change
    (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run target =
      .ok targetPost at hTarget
  change
    (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run full =
      .ok fullPost at hFull
  exact
    PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
      EvmYul.MachineState.evmReturn
      (fun hMachine => machine_evmReturn_gasAvailable_rel hMachine)
      hRel hTarget hFull

theorem EvmYul_step_revert_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.REVERT none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.REVERT none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  change
    (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run target =
      .ok targetPost at hTarget
  change
    (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run full =
      .ok fullPost at hFull
  exact
    PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
      EvmYul.MachineState.evmRevert
      (fun hMachine => machine_evmRevert_gasAvailable_rel hMachine)
      hRel hTarget hFull

theorem EvmYul_step_selfdestruct_stackUnderflow_of_pop_none
    {state : EVMState}
    (hPop : state.stack.pop = none) :
    EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none state =
      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil =>
          rfl
      | cons hd tl =>
          simp [EvmYul.Stack.pop] at hPop

theorem EvmYul_step_selfdestruct_preserves_gasExecRel
    {full target fullPost targetPost : EVMState}
    (hRel : GasExecRel full target)
    (hTarget :
      EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none target =
        .ok targetPost)
    (hFull :
      EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [hRel] at hFull
  cases hPop : target.stack.pop with
  | none =>
      rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop] at hTarget
      cases hTarget
  | some popped =>
      rcases popped with ⟨stack, recipient⟩
      let fullGas : EVMState :=
        { target with
          gasAvailable := full.gasAvailable,
          execLength := full.execLength }
      change
        EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none fullGas =
          .ok fullPost at hFull
      have hStackTarget : target.stack = recipient :: stack :=
        stack_eq_cons_of_pop hPop
      have hStackFull : fullGas.stack = recipient :: stack := by
        simpa [fullGas] using hStackTarget
      rw [EvmYul.EVM.step_selfdestruct_of_stack target recipient stack
        hStackTarget] at hTarget
      rw [EvmYul.EVM.step_selfdestruct_of_stack fullGas recipient stack
        hStackFull] at hFull
      cases hTarget
      cases hFull
      simp [GasExecRel, fullGas, EvmYul.EVM.selfdestructState,
        EvmYul.selfdestructAccountMap, EvmYul.MachineState.setHReturn,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

set_option maxHeartbeats 800000 in
theorem EvmYul_step_noncontinuing_prim_gasAvailable_eq
    {op : PrimOp}
    (hStep : op.continuingStep? = none)
    (hNoCallCreate : op.isCallCreate = false)
    {state post : EVMState}
    (hRun : EvmYul.step op.toEVM none state = .ok post) :
    post.gasAvailable = state.gasAvailable := by
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.isCallCreate] at hStep hNoCallCreate
  · change EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none state =
      .ok post at hRun
    have hStop :
        EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none state =
          .ok
            { state with
              toMachineState :=
                (state.toMachineState.setReturnData ByteArray.empty).setHReturn
                  ByteArray.empty } := by
      rfl
    rw [hStop] at hRun
    cases hRun
    simp [EvmYul.MachineState.setReturnData,
      EvmYul.MachineState.setHReturn]
  · change EvmYul.step (τ := .EVM) EvmYul.Operation.PC none state =
      .ok post at hRun
    have hPc :
        EvmYul.step (τ := .EVM) EvmYul.Operation.PC none state =
          .ok
            (EvmYul.EVM.State.replaceStackAndIncrPC state
              (state.stack.push state.pc)) := by
      rfl
    rw [hPc] at hRun
    cases hRun
    simp [EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · change
      (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run
          state = .ok post at hRun
    exact PrimStep_run_binaryMachineState_gasAvailable_eq
      EvmYul.MachineState.evmReturn
      (fun machine mstart size => by
        simp [EvmYul.MachineState.evmReturn]) hRun
  · change
      (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run
          state = .ok post at hRun
    exact PrimStep_run_binaryMachineState_gasAvailable_eq
      EvmYul.MachineState.evmRevert
      (fun machine mstart size => by
        simp [EvmYul.MachineState.evmRevert,
          EvmYul.MachineState.evmReturn]) hRun
  · change EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none
      state = .ok post at hRun
    cases hPop : state.stack.pop with
    | none =>
        rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop] at hRun
        cases hRun
    | some popped =>
        rcases popped with ⟨stack, recipient⟩
        have hStack : state.stack = recipient :: stack :=
          stack_eq_cons_of_pop hPop
        rw [EvmYul.EVM.step_selfdestruct_of_stack state recipient stack
          hStack] at hRun
        cases hRun
        simp [EvmYul.EVM.selfdestructState, EvmYul.selfdestructAccountMap,
          EvmYul.MachineState.setHReturn,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

set_option maxHeartbeats 800000 in
theorem EvmYul_step_continuing_prim_preserves_gasExecRel
    {op : PrimOp} {step : PrimStep}
    {full target fullPost targetPost : EVMState}
    (hStep : op.continuingStep? = some step)
    (hRel : GasExecRel full target)
    (hTarget : step.run target = .ok targetPost)
    (hFull : EvmYul.step op.toEVM none full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  cases step with
  | bin f =>
      have hFullRun : (PrimStep.bin f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_bin_preserves_gasExecRel f hRel hTarget hFullRun
  | un f =>
      have hFullRun : (PrimStep.un f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_un_preserves_gasExecRel f hRel hTarget hFullRun
  | tri f =>
      have hFullRun : (PrimStep.tri f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_tri_preserves_gasExecRel f hRel hTarget hFullRun
  | executionEnv f =>
      have hFullRun :
          (PrimStep.executionEnv f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact
        PrimStep_run_executionEnv_preserves_gasExecRel f hRel hTarget
          hFullRun
  | unaryExecutionEnv f =>
      have hFullRun :
          (PrimStep.unaryExecutionEnv f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact
        PrimStep_run_unaryExecutionEnv_preserves_gasExecRel f hRel hTarget
          hFullRun
  | machineState f =>
      have hFullRun :
          (PrimStep.machineState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      all_goals
        exact
          PrimStep_run_machineState_preserves_gasExecRel_of_eq _
            (by
              rw [hRel]
              simp [EvmYul.MachineState.returndatasize,
                EvmYul.MachineState.msize])
            hRel hTarget hFullRun
  | binaryMachineState f =>
      have hFullRun :
          (PrimStep.binaryMachineState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · exact
          PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
            EvmYul.MachineState.mstore
            (fun hMachine =>
              machine_mstore_gasAvailable_rel hMachine)
            hRel hTarget hFullRun
      · exact
          PrimStep_run_binaryMachineState_preserves_gasExecRel_of_rel
            EvmYul.MachineState.mstore8
            (fun hMachine =>
              machine_mstore8_gasAvailable_rel hMachine)
            hRel hTarget hFullRun
  | binaryMachineStateWithResult f =>
      have hFullRun :
          (PrimStep.binaryMachineStateWithResult f).run full =
            .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact
        PrimStep_run_binaryMachineStateWithResult_preserves_gasExecRel_of_rel
          EvmYul.MachineState.keccak256
          (fun hMachine =>
            machine_keccak256_gasAvailable_rel hMachine)
          hRel hTarget hFullRun
  | ternaryMachineState f =>
      have hFullRun :
          (PrimStep.ternaryMachineState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact
        PrimStep_run_ternaryMachineState_preserves_gasExecRel_of_rel
          EvmYul.MachineState.mcopy
          (fun hMachine =>
            machine_mcopy_gasAvailable_rel hMachine)
          hRel hTarget hFullRun
  | state f =>
      have hFullRun : (PrimStep.state f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_state_preserves_gasExecRel f hRel hTarget hFullRun
  | unaryState f =>
      have hFullRun :
          (PrimStep.unaryState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact
        PrimStep_run_unaryState_preserves_gasExecRel f hRel hTarget
          hFullRun
  | binaryState f =>
      have hFullRun :
          (PrimStep.binaryState f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact
        PrimStep_run_binaryState_preserves_gasExecRel f hRel hTarget
          hFullRun
  | ternaryCopy f =>
      have hFullRun :
          (PrimStep.ternaryCopy f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · exact
          PrimStep_run_ternaryCopy_preserves_gasExecRel_of_rel
            EvmYul.SharedState.calldatacopy
            (fun hShared =>
              shared_calldatacopy_gasAvailable_rel hShared)
            hRel hTarget hFullRun
      · exact
          PrimStep_run_ternaryCopy_preserves_gasExecRel_of_rel
            EvmYul.SharedState.codeCopy
            (fun hShared =>
              shared_codeCopy_gasAvailable_rel hShared)
            hRel hTarget hFullRun
  | quaternaryCopy f =>
      have hFullRun :
          (PrimStep.quaternaryCopy f).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact
        PrimStep_run_quaternaryCopy_preserves_gasExecRel_of_rel
          EvmYul.SharedState.extCodeCopy'
          (fun hShared =>
            shared_extCodeCopy'_gasAvailable_rel hShared)
          hRel hTarget hFullRun
  | pop =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_pop_preserves_gasExecRel hRel hTarget hFull
  | mload =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_mload_preserves_gasExecRel hRel hTarget hFull
  | returndatacopy =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_returndatacopy_preserves_gasExecRel hRel hTarget hFull
  | dup n =>
      have hFullRun : (PrimStep.dup n).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_dup_preserves_gasExecRel n hRel hTarget hFullRun
  | swap n =>
      have hFullRun : (PrimStep.swap n).run full = .ok fullPost := by
        rw [EvmYul_step_eq_continuingStep_run hStep
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)] at hFull
        exact hFull
      exact PrimStep_run_swap_preserves_gasExecRel n hRel hTarget hFullRun
  | log0 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log0_preserves_gasExecRel hRel hTarget hFull
  | log1 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log1_preserves_gasExecRel hRel hTarget hFull
  | log2 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log2_preserves_gasExecRel hRel hTarget hFull
  | log3 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log3_preserves_gasExecRel hRel hTarget hFull
  | log4 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      exact EvmYul_step_log4_preserves_gasExecRel hRel hTarget hFull
  | invalid =>
      exact PrimStep_run_invalid_preserves_gasExecRel hTarget

theorem EvmYul_step_noncontinuing_prim_preserves_gasExecRel
    {op : PrimOp}
    {full target fullPost targetPost : EVMState}
    (hStep : op.continuingStep? = none)
    (hNoCallCreate : op.isCallCreate = false)
    (hRel : GasExecRel full target)
    (hTarget : op.step target = .ok targetPost)
    (hFull : EvmYul.step op.toEVM none full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [PrimOp.step_eq_evm_step_of_not_continuing
    hStep hNoCallCreate] at hTarget
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.isCallCreate] at hStep hNoCallCreate
  · exact EvmYul_step_stop_preserves_gasExecRel hRel hTarget hFull
  · exact EvmYul_step_pc_preserves_gasExecRel hRel hTarget hFull
  · exact EvmYul_step_return_preserves_gasExecRel hRel hTarget hFull
  · exact EvmYul_step_revert_preserves_gasExecRel hRel hTarget hFull
  · exact EvmYul_step_selfdestruct_preserves_gasExecRel hRel hTarget hFull

set_option maxHeartbeats 1200000 in
theorem EvmYul_step_continuing_prim_exists_gasExecRel
    {op : PrimOp} {step : PrimStep}
    {full target targetPost : EVMState}
    (hStep : op.continuingStep? = some step)
    (hRel : GasExecRel full target)
    (hTarget : step.run target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.step op.toEVM none full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  cases step with
  | bin f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_bin_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | un f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_un_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | tri f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_tri_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | executionEnv f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_executionEnv_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | unaryExecutionEnv f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_unaryExecutionEnv_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | machineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      all_goals
        obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_machineState_exists_gasExecRel_of_eq _
            (by
              rw [hRel]
              simp [EvmYul.MachineState.returndatasize,
                EvmYul.MachineState.msize])
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | binaryMachineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
            EvmYul.MachineState.mstore
            (fun hMachine => machine_mstore_gasAvailable_rel hMachine)
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
      · obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
            EvmYul.MachineState.mstore8
            (fun hMachine => machine_mstore8_gasAvailable_rel hMachine)
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | binaryMachineStateWithResult f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_binaryMachineStateWithResult_exists_gasExecRel_of_rel
          EvmYul.MachineState.keccak256
          (fun hMachine => machine_keccak256_gasAvailable_rel hMachine)
          hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | ternaryMachineState f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_ternaryMachineState_exists_gasExecRel_of_rel
          EvmYul.MachineState.mcopy
          (fun hMachine => machine_mcopy_gasAvailable_rel hMachine)
          hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | state f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_state_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | unaryState f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_unaryState_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | binaryState f =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_binaryState_exists_gasExecRel f hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | ternaryCopy f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      · obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_ternaryCopy_exists_gasExecRel_of_rel
            EvmYul.SharedState.calldatacopy
            (fun hShared => shared_calldatacopy_gasAvailable_rel hShared)
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
      · obtain ⟨fullPost, hRun, hRelPost⟩ :=
          PrimStep_run_ternaryCopy_exists_gasExecRel_of_rel
            EvmYul.SharedState.codeCopy
            (fun hShared => shared_codeCopy_gasAvailable_rel hShared)
            hRel hTarget
        refine ⟨fullPost, ?_, hRelPost⟩
        simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | quaternaryCopy f =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_quaternaryCopy_exists_gasExecRel_of_rel
          EvmYul.SharedState.extCodeCopy'
          (fun hShared => shared_extCodeCopy'_gasAvailable_rel hShared)
          hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [PrimOp.toEVM, PrimStep.run] using hRun
  | pop =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget : target.stack = value :: stack :=
            stack_eq_cons_of_pop hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullGas stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | mload =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget : target.stack = offset :: stack :=
            stack_eq_cons_of_pop hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨(let loaded := fullGas.toMachineState.mload offset;
               EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with toMachineState := loaded.2 }
                (stack.push loaded.1)),
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · have hMachineRel :
                fullGas.toMachineState =
                  { target.toMachineState with
                    gasAvailable := fullGas.toMachineState.gasAvailable } := by
              simp [fullGas]
            have hMload :=
              machine_mload_gasAvailable_rel (offset := offset) hMachineRel
            rcases hMload with ⟨hMloadValue, hMloadState⟩
            dsimp
            rw [hMloadValue, hMloadState]
            simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | returndatacopy =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop3 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, mstart, rstart, size⟩
          simp [PrimStep.run, hPop] at hTarget
          by_cases hBounds :
              target.returnData.size < rstart.toNat + size.toNat
          · simp [hBounds] at hTarget
          · simp [hBounds] at hTarget
            cases hTarget
            have hStackTarget :
                target.stack = mstart :: rstart :: size :: stack :=
              stack_eq_cons_cons_cons_of_pop3 hPop
            let fullGas : EVMState :=
              { target with
                gasAvailable := full.gasAvailable,
                execLength := full.execLength }
            refine
              ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                  { fullGas with
                    toMachineState :=
                      fullGas.toMachineState.returndatacopy mstart rstart size }
                  stack,
                ?_, ?_⟩
            · dsimp [fullGas]
              rw [hStackTarget]
              simp only [PrimOp.toEVM]
              rw [EvmYul_step_returndatacopy_eq_PrimStep_run]
              simp [PrimStep.run, EvmYul.Stack.pop3, hBounds]
            · have hMachineRel :
                  fullGas.toMachineState =
                    { target.toMachineState with
                      gasAvailable := fullGas.toMachineState.gasAvailable } := by
                simp [fullGas]
              have hCopy :=
                machine_returndatacopy_gasAvailable_rel
                  (mstart := mstart) (rstart := rstart) (size := size)
                  hMachineRel
              dsimp
              rw [hCopy]
              simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
                EvmYul.EVM.State.incrPC]
  | dup n =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_dup_exists_gasExecRel n hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | swap n =>
      obtain ⟨fullPost, hRun, hRelPost⟩ :=
        PrimStep_run_swap_exists_gasExecRel n hRel hTarget
      refine ⟨fullPost, ?_, hRelPost⟩
      simpa [EvmYul_step_eq_continuingStep_run hStep
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)] using hRun
  | log0 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop2 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset, size⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget : target.stack = offset :: size :: stack :=
            stack_eq_cons_cons_of_pop2 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[]
                      fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | log1 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop3 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset, size, topic0⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget : target.stack = offset :: size :: topic0 :: stack :=
            stack_eq_cons_cons_cons_of_pop3 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[topic0]
                      fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | log2 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop4 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset, size, topic0, topic1⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget :
              target.stack = offset :: size :: topic0 :: topic1 :: stack :=
            stack_eq_cons_cons_cons_cons_of_pop4 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size #[topic0, topic1]
                      fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | log3 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop5 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with ⟨stack, offset, size, topic0, topic1, topic2⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget :
              target.stack =
                offset :: size :: topic0 :: topic1 :: topic2 :: stack :=
            stack_eq_cons_cons_cons_cons_cons_of_pop5 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size
                      #[topic0, topic1, topic2] fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | log4 =>
      cases op <;> simp [PrimOp.continuingStep?] at hStep
      all_goals cases hStep
      rw [hRel]
      cases hPop : target.stack.pop6 with
      | none =>
          simp [PrimStep.run, hPop] at hTarget
      | some popped =>
          rcases popped with
            ⟨stack, offset, size, topic0, topic1, topic2, topic3⟩
          simp [PrimStep.run, hPop] at hTarget
          cases hTarget
          have hStackTarget :
              target.stack =
                offset :: size :: topic0 :: topic1 :: topic2 :: topic3 ::
                  stack :=
            stack_eq_cons_cons_cons_cons_cons_cons_of_pop6 hPop
          let fullGas : EVMState :=
            { target with
              gasAvailable := full.gasAvailable,
              execLength := full.execLength }
          refine
            ⟨EvmYul.EVM.State.replaceStackAndIncrPC
                { fullGas with
                  toSharedState :=
                    EvmYul.SharedState.logOp offset size
                      #[topic0, topic1, topic2, topic3]
                      fullGas.toSharedState }
                stack,
              ?_, ?_⟩
          · dsimp [fullGas]
            rw [hStackTarget]
            rfl
          · simp [GasExecRel, fullGas, EvmYul.SharedState.logOp,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | invalid =>
      simp [PrimStep.run] at hTarget

theorem EvmYul_step_noncontinuing_prim_exists_gasExecRel
    {op : PrimOp}
    {full target targetPost : EVMState}
    (hStep : op.continuingStep? = none)
    (hNoCallCreate : op.isCallCreate = false)
    (hRel : GasExecRel full target)
    (hTarget : op.step target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.step op.toEVM none full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rw [PrimOp.step_eq_evm_step_of_not_continuing
    hStep hNoCallCreate] at hTarget
  cases op <;>
    simp [PrimOp.continuingStep?, PrimOp.isCallCreate] at hStep hNoCallCreate
  · rw [hRel]
    cases hTarget
    let fullGas : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    refine
      ⟨{ fullGas with
          toMachineState :=
            (fullGas.toMachineState.setReturnData ByteArray.empty).setHReturn
              ByteArray.empty },
        ?_, ?_⟩
    · rfl
    · simp [GasExecRel, fullGas, EvmYul.MachineState.setReturnData,
        EvmYul.MachineState.setHReturn]
  · rw [hRel]
    cases hTarget
    let fullGas : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    refine
      ⟨EvmYul.EVM.State.replaceStackAndIncrPC fullGas
          (fullGas.stack.push fullGas.pc),
        ?_, ?_⟩
    · rfl
    · simp [GasExecRel, fullGas, EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  · change
      (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run target =
        .ok targetPost at hTarget
    exact
      PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
        EvmYul.MachineState.evmReturn
        (fun hMachine => machine_evmReturn_gasAvailable_rel hMachine)
        hRel hTarget
  · change
      (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run target =
        .ok targetPost at hTarget
    exact
      PrimStep_run_binaryMachineState_exists_gasExecRel_of_rel
        EvmYul.MachineState.evmRevert
        (fun hMachine => machine_evmRevert_gasAvailable_rel hMachine)
        hRel hTarget
  · rw [hRel]
    change
      EvmYul.step (τ := .EVM) EvmYul.Operation.SELFDESTRUCT none target =
        .ok targetPost at hTarget
    cases hPop : target.stack.pop with
    | none =>
        rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop] at hTarget
        cases hTarget
    | some popped =>
        rcases popped with ⟨stack, recipient⟩
        have hStackTarget : target.stack = recipient :: stack :=
          stack_eq_cons_of_pop hPop
        rw [EvmYul.EVM.step_selfdestruct_of_stack target recipient stack
          hStackTarget] at hTarget
        cases hTarget
        let fullGas : EVMState :=
          { target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength }
        have hStackFull : fullGas.stack = recipient :: stack := by
          simpa [fullGas] using hStackTarget
        refine
          ⟨{ (EvmYul.EVM.selfdestructState fullGas recipient stack) with
              toMachineState :=
                (EvmYul.EVM.selfdestructState fullGas recipient stack).toMachineState.setHReturn
                  ByteArray.empty },
            ?_, ?_⟩
        · simpa [fullGas] using
            EvmYul.EVM.step_selfdestruct_of_stack fullGas recipient stack
              hStackFull
        · simp [GasExecRel, fullGas, EvmYul.EVM.selfdestructState,
            EvmYul.selfdestructAccountMap, EvmYul.MachineState.setHReturn,
            EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]

theorem EvmYul_step_targetInstr_preserves_gasExecRel
    {instr : TargetInstr}
    {full target fullPost targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost)
    (hFull : EvmYul.step instr.op instr.arg full = .ok fullPost) :
    GasExecRel fullPost targetPost := by
  cases instr with
  | push32 value =>
      exact EvmYul_step_push32_preserves_gasExecRel hRel hTarget hFull
  | jump =>
      exact EvmYul_step_jump_preserves_gasExecRel hRel hTarget hFull
  | jumpi =>
      exact EvmYul_step_jumpi_preserves_gasExecRel hRel hTarget hFull
  | jumpdest =>
      exact EvmYul_step_jumpdest_preserves_gasExecRel hRel hTarget hFull
  | prim op =>
      change op.step target = .ok targetPost at hTarget
      change EvmYul.step op.toEVM none full = .ok fullPost at hFull
      cases hStep : op.continuingStep? with
      | none =>
          exact
            EvmYul_step_noncontinuing_prim_preserves_gasExecRel
              hStep (by simpa [targetInstrUsesCallCreate] using hNoCallCreate)
              hRel hTarget hFull
      | some step =>
          have hTargetRun : step.run target = .ok targetPost := by
            rw [PrimOp.step_eq_continuingStep_run hStep] at hTarget
            exact hTarget
          exact
            EvmYul_step_continuing_prim_preserves_gasExecRel hStep hRel
              hTargetRun hFull

theorem EVM_step_targetInstr_preserves_gasExecRel
    {fuel gasCost : Nat} {instr : TargetInstr}
    {full target fullPost targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost)
    (hFull :
      EvmYul.EVM.step fuel.succ gasCost (some (instr.op, instr.arg)) full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  rw [EVM_step_targetInstr_eq_of_no_call_create
    (fuel := fuel) (gasCost := gasCost) (state := full)
    (instr := instr) hNoCallCreate] at hFull
  exact
    EvmYul_step_targetInstr_preserves_gasExecRel hNoCallCreate
      (hRel.charge_left (cost := gasCost)) hTarget hFull

theorem EVM_step_targetInstr_preserves_gasExecRel_of_ok
    {fuel gasCost : Nat} {instr : TargetInstr}
    {full target fullPost targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost)
    (hFull :
      EvmYul.EVM.step fuel gasCost (some (instr.op, instr.arg)) full =
        .ok fullPost) :
    GasExecRel fullPost targetPost := by
  cases fuel with
  | zero =>
      simp [EvmYul.EVM.step] at hFull
  | succ fuel =>
      exact
        EVM_step_targetInstr_preserves_gasExecRel
          (fuel := fuel) (gasCost := gasCost) hNoCallCreate hRel hTarget
          hFull

set_option maxHeartbeats 2000000 in
theorem EvmYul_step_control_targetInstr_exists_gasExecRel
    {instr : TargetInstr} {value : Word}
    {full target targetPost : EVMState}
    (hControl :
      instr = .push32 value ∨ instr = .jump ∨ instr = .jumpi ∨
        instr = .jumpdest)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.step instr.op instr.arg full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  rcases hControl with hPush | hJump | hJumpi | hJumpdest
  · subst instr
    rw [hRel]
    simp [Target.stepInstr] at hTarget
    cases hTarget
    refine ⟨_, rfl, ?_⟩
    simp [GasExecRel, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · subst instr
    rw [hRel]
    cases hPop : target.stack.pop with
    | none =>
        simp [Target.stepInstr, hPop] at hTarget
    | some popped =>
        rcases popped with ⟨stack, dest⟩
        simp [Target.stepInstr, hPop] at hTarget
        cases hTarget
        have hStack : target.stack = dest :: stack :=
          stack_eq_cons_of_pop hPop
        let fullState : EVMState :=
          { target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength }
        refine ⟨{ fullState with pc := dest, stack := stack }, ?_, ?_⟩
        · simpa [TargetInstr.op, TargetInstr.arg, fullState] using
            EvmYul_step_jump_of_stack
              fullState stack dest (by simpa [fullState] using hStack)
        · simp [GasExecRel, fullState]
  · subst instr
    rw [hRel]
    cases hPop : target.stack.pop2 with
    | none =>
        simp [Target.stepInstr, hPop] at hTarget
    | some popped =>
        rcases popped with ⟨stack, dest, cond⟩
        simp [Target.stepInstr, hPop] at hTarget
        cases hTarget
        have hStack : target.stack = dest :: cond :: stack :=
          stack_eq_cons_cons_of_pop2 hPop
        let fullState : EVMState :=
          { target with
            gasAvailable := full.gasAvailable,
            execLength := full.execLength }
        refine
          ⟨{ fullState with
              pc :=
                if cond != EvmYul.UInt256.ofNat 0 then
                  dest
                else
                  fullState.pc + EvmYul.UInt256.ofNat 1,
              stack := stack },
            ?_, ?_⟩
        · simpa [TargetInstr.op, TargetInstr.arg, fullState] using
            EvmYul_step_jumpi_of_stack
              fullState stack dest cond (by simpa [fullState] using hStack)
        · simp [GasExecRel, fullState]
  · subst instr
    rw [hRel]
    simp [Target.stepInstr] at hTarget
    cases hTarget
    let fullState : EVMState :=
      { target with
        gasAvailable := full.gasAvailable,
        execLength := full.execLength }
    refine ⟨EvmYul.EVM.State.incrPC fullState, ?_, ?_⟩
    · simpa [TargetInstr.op, TargetInstr.arg, fullState] using
        EvmYul_step_jumpdest_eq fullState
    · simp [GasExecRel, EvmYul.EVM.State.incrPC, fullState]

theorem EvmYul_step_targetInstr_exists_gasExecRel
    {instr : TargetInstr}
    {full target targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.step instr.op instr.arg full = .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  cases instr with
  | push32 value =>
      exact
        EvmYul_step_control_targetInstr_exists_gasExecRel
          (value := value) (hControl := Or.inl rfl) hRel hTarget
  | jump =>
      exact
        EvmYul_step_control_targetInstr_exists_gasExecRel
          (value := EvmYul.UInt256.ofNat 0)
          (hControl := Or.inr (Or.inl rfl)) hRel hTarget
  | jumpi =>
      exact
        EvmYul_step_control_targetInstr_exists_gasExecRel
          (value := EvmYul.UInt256.ofNat 0)
          (hControl := Or.inr (Or.inr (Or.inl rfl))) hRel hTarget
  | jumpdest =>
      exact
        EvmYul_step_control_targetInstr_exists_gasExecRel
          (value := EvmYul.UInt256.ofNat 0)
          (hControl := Or.inr (Or.inr (Or.inr rfl))) hRel hTarget
  | prim op =>
      change op.step target = .ok targetPost at hTarget
      change
        ∃ fullPost,
          EvmYul.step op.toEVM none full = .ok fullPost ∧
            GasExecRel fullPost targetPost
      cases hStep : op.continuingStep? with
      | none =>
          exact
            EvmYul_step_noncontinuing_prim_exists_gasExecRel
              hStep (by simpa [targetInstrUsesCallCreate] using hNoCallCreate)
              hRel hTarget
      | some step =>
          have hTargetRun : step.run target = .ok targetPost := by
            rw [PrimOp.step_eq_continuingStep_run hStep] at hTarget
            exact hTarget
          exact
            EvmYul_step_continuing_prim_exists_gasExecRel hStep hRel
              hTargetRun

theorem EVM_step_targetInstr_exists_gasExecRel
    {fuel gasCost : Nat} {instr : TargetInstr}
    {full target targetPost : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hTarget : Target.stepInstr instr target = .ok targetPost) :
    ∃ fullPost,
      EvmYul.EVM.step fuel.succ gasCost (some (instr.op, instr.arg)) full =
        .ok fullPost ∧
        GasExecRel fullPost targetPost := by
  obtain ⟨fullPost, hRun, hRelPost⟩ :=
    EvmYul_step_targetInstr_exists_gasExecRel hNoCallCreate
      (hRel.charge_left (cost := gasCost)) hTarget
  refine ⟨fullPost, ?_, hRelPost⟩
  rw [EVM_step_targetInstr_eq_of_no_call_create
    (fuel := fuel) (gasCost := gasCost) (state := full)
    (instr := instr) hNoCallCreate]
  exact hRun

theorem Target.stepInstrResult_running_stepInstr
    {instr : TargetInstr} {state mid : EVMState}
    (hRun : Target.stepInstrResult instr state = .ok (.running mid)) :
    Target.stepInstr instr state = .ok mid ∧ instr.haltKind? = none := by
  unfold Target.stepInstrResult at hRun
  cases hStep : Target.stepInstr instr state with
  | error err =>
      rw [hStep] at hRun
      cases hRun
  | ok state' =>
      rw [hStep] at hRun
      cases hKind : instr.haltKind? with
      | none =>
          rw [hKind] at hRun
          cases hRun
          exact ⟨rfl, rfl⟩
      | some kind =>
          rw [hKind] at hRun
          cases hRun

theorem Target.stepInstrResult_halted_stepInstr
    {instr : TargetInstr} {state : EVMState} {halt : Halt}
    (hRun : Target.stepInstrResult instr state = .ok (.halted halt)) :
    Target.stepInstr instr state = .ok halt.state ∧
      instr.haltKind? = some halt.kind ∧
        halt.output = halt.kind.output halt.state := by
  unfold Target.stepInstrResult at hRun
  cases hStep : Target.stepInstr instr state with
  | error err =>
      rw [hStep] at hRun
      cases hRun
  | ok state' =>
      rw [hStep] at hRun
      cases hKind : instr.haltKind? with
      | none =>
          rw [hKind] at hRun
          cases hRun
      | some kind =>
          rw [hKind] at hRun
          cases hRun
          exact ⟨rfl, rfl, rfl⟩

theorem Target.runListResult_cons_ok_cases
    {instr : TargetInstr} {rest : List TargetInstr}
    {state : EVMState} {result : StepResult}
    (hRun :
      Target.runListResult (instr :: rest) state = .ok result) :
    (∃ mid,
      Target.stepInstrResult instr state = .ok (.running mid) ∧
        Target.runListResult rest mid = .ok result) ∨
      (∃ halt,
        Target.stepInstrResult instr state = .ok (.halted halt) ∧
          result = .halted halt) := by
  unfold Target.runListResult at hRun
  cases hStep : Target.stepInstrResult instr state with
  | error err =>
      rw [hStep] at hRun
      cases hRun
  | ok stepResult =>
      rw [hStep] at hRun
      cases stepResult with
      | running mid =>
          exact Or.inl ⟨mid, rfl, hRun⟩
      | halted halt =>
          cases hRun
          exact Or.inr ⟨halt, rfl, rfl⟩

theorem HaltKind.output_eq_of_gasExecRel
    (kind : HaltKind) {full target : EVMState}
    (hRel : GasExecRel full target) :
  kind.output full = kind.output target := by
  rw [hRel]
  cases kind <;> simp [HaltKind.output]

theorem memoryExpansionCost_eq_of_gasExecRel {full target : EVMState}
    (hRel : GasExecRel full target) (op : EVMOp) :
    EvmYul.EVM.memoryExpansionCost full op =
      EvmYul.EVM.memoryExpansionCost target op := by
  rw [hRel]
  cases target
  rfl

set_option maxHeartbeats 2000000 in
theorem C'_eq_of_gasExecRel_of_targetInstr_no_call_create
    {full target : EVMState} {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target) :
    EvmYul.EVM.C' full instr.op =
      EvmYul.EVM.C' target instr.op := by
  rw [hRel]
  cases target
  cases instr with
  | push32 value =>
      simp [TargetInstr.op, EvmYul.EVM.C']
  | jump =>
      simp [TargetInstr.op, EvmYul.EVM.C']
  | jumpi =>
      simp [TargetInstr.op, EvmYul.EVM.C']
  | jumpdest =>
      simp [TargetInstr.op, EvmYul.EVM.C']
  | prim op =>
      cases op <;>
        simp [targetInstrUsesCallCreate, PrimOp.isCallCreate,
          TargetInstr.op, PrimOp.toEVM, EvmYul.EVM.C',
          EvmYul.EVM.Csstore, EvmYul.EVM.Cselfdestruct] at hNoCallCreate ⊢

def jumpTargetAllowed (target? : Option Word)
    (validJumps : Array Word) : Prop :=
  match target? with
  | some target => validJumps.contains target = true
  | none => False

theorem emitFrom_labelPcFrom_jumpdest_mem
    {full suffix : Program} {base pc : Nat} {label : Label}
    {code : List LocatedTarget}
    (hEmit : emitFrom? full suffix base = some code)
    (hLabel : Program.labelPcFrom suffix base label = some pc) :
    ({ pc := pc, instr := TargetInstr.jumpdest } : LocatedTarget) ∈
      code := by
  induction suffix generalizing base code with
  | nil =>
      simp [Program.labelPcFrom] at hLabel
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
              subst code
              cases head with
              | label name =>
                  by_cases hEq : name = label
                  · unfold Program.labelPcFrom at hLabel
                    simp [hEq] at hLabel
                    subst pc
                    simp [emitInstr?] at hHere
                    subst here
                    simp
                  · unfold Program.labelPcFrom at hLabel
                    simp [hEq] at hLabel
                    exact List.mem_append_right here (ih hThere hLabel)
              | prim op =>
                  unfold Program.labelPcFrom at hLabel
                  exact List.mem_append_right here (ih hThere hLabel)
              | push value =>
                  unfold Program.labelPcFrom at hLabel
                  exact List.mem_append_right here (ih hThere hLabel)
              | jump target =>
                  unfold Program.labelPcFrom at hLabel
                  exact List.mem_append_right here (ih hThere hLabel)
              | jumpi target =>
                  unfold Program.labelPcFrom at hLabel
                  exact List.mem_append_right here (ih hThere hLabel)

theorem emit_labelPc_jumpdest_mem
    {program : Program} {code : List LocatedTarget} {label : Label}
    {pc : Nat}
    (hEmit : emit? program = some code)
    (hLabel : Program.labelPc program label = some pc) :
    ({ pc := pc, instr := TargetInstr.jumpdest } : LocatedTarget) ∈
      code := by
  exact
    emitFrom_labelPcFrom_jumpdest_mem
      (full := program) (suffix := program) (base := 0)
      (code := code) hEmit (by simpa [Program.labelPc] using hLabel)

theorem assemble_labelPc_jumpdest_mem
    {program : Program} {target : TargetProgram} {label : Label}
    {pc : Nat}
    (hAsm : assemble? program = some target)
    (hLabel : Program.labelPc program label = some pc) :
    ({ pc := pc, instr := TargetInstr.jumpdest } : LocatedTarget) ∈
      target.code := by
  obtain ⟨code, hEmit, hTargetCode⟩ :=
    Preservation.assemble_emits_code hAsm
  rw [hTargetCode]
  exact emit_labelPc_jumpdest_mem hEmit hLabel

theorem jumpTargetAllowed_of_jumpdestCorrect_mem
    {target : TargetProgram} {pc : Nat}
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hMem :
      ({ pc := pc, instr := TargetInstr.jumpdest } : LocatedTarget) ∈
        target.code) :
    jumpTargetAllowed (some (EvmYul.UInt256.ofNat pc)) (validJumps target) := by
  simpa [jumpTargetAllowed, validJumps, Bytecode.jumpdestListed,
    Bytecode.jumpdestListed?] using
      hJumpdest.jumpdests
        ({ pc := pc, instr := TargetInstr.jumpdest } : LocatedTarget)
        hMem rfl

theorem jumpTargetAllowed_of_assemble_labelPc
    {program : Program} {target : TargetProgram} {label : Label}
    {pc : Nat}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hLabel : Program.labelPc program label = some pc) :
    jumpTargetAllowed (some (EvmYul.UInt256.ofNat pc)) (validJumps target) :=
  jumpTargetAllowed_of_jumpdestCorrect_mem hJumpdest
    (assemble_labelPc_jumpdest_mem hAsm hLabel)


/--
The non-gas exceptional-halting checks performed by `EVM.X` before it calls
`EVM.step`. These are not made true by giving the machine more gas; they must
come from bytecode/path safety, stack bounds, static-mode compatibility, and
the no-CALL/CREATE fragment boundary.
-/
def XNonGasChecksPass (validJumps : Array Word) (state : EVMState)
    (op : EVMOp) : Prop :=
  EvmYul.EVM.δ op ≠ none ∧
    state.stack.length ≥ (EvmYul.EVM.δ op).getD 0 ∧
      (op = EvmYul.Operation.JUMP →
        jumpTargetAllowed state.stack[0]? validJumps) ∧
        (op = EvmYul.Operation.JUMPI →
          state.stack[1]? ≠ some ⟨0⟩ →
            jumpTargetAllowed state.stack[0]? validJumps) ∧
          (op = EvmYul.Operation.RETURNDATACOPY →
            (state.stack.getD 1 ⟨0⟩).toNat +
                (state.stack.getD 2 ⟨0⟩).toNat ≤
              state.returnData.size) ∧
            state.stack.length - (EvmYul.EVM.δ op).getD 0 +
                (EvmYul.EVM.α op).getD 0 ≤ 1024 ∧
              (state.executionEnv.perm = false →
                ¬ staticWriteSensitive op state.stack) ∧
                (op.isCreate = true →
                  state.stack.getD 2 ⟨0⟩ ≤ ⟨49152⟩)

def XNonGasCoreChecksPass (validJumps : Array Word) (state : EVMState)
    (op : EVMOp) : Prop :=
  EvmYul.EVM.δ op ≠ none ∧
    state.stack.length ≥ (EvmYul.EVM.δ op).getD 0 ∧
      (op = EvmYul.Operation.JUMP →
        jumpTargetAllowed state.stack[0]? validJumps) ∧
        (op = EvmYul.Operation.JUMPI →
          state.stack[1]? ≠ some ⟨0⟩ →
            jumpTargetAllowed state.stack[0]? validJumps) ∧
          state.stack.length - (EvmYul.EVM.δ op).getD 0 +
              (EvmYul.EVM.α op).getD 0 ≤ 1024 ∧
            (state.executionEnv.perm = false →
              ¬ staticWriteSensitive op state.stack)

def XCoreStackAndJumpInputsReady (validJumps : Array Word)
    (state : EVMState) (op : EVMOp) : Prop :=
  EvmYul.EVM.δ op ≠ none ∧
    state.stack.length ≥ (EvmYul.EVM.δ op).getD 0 ∧
      (op = EvmYul.Operation.JUMP →
        jumpTargetAllowed state.stack[0]? validJumps) ∧
        (op = EvmYul.Operation.JUMPI →
          state.stack[1]? ≠ some ⟨0⟩ →
            jumpTargetAllowed state.stack[0]? validJumps)

theorem XCoreStackAndJumpInputsReady.of_prim_continuing_run
    {validJumps : Array Word} {state : EVMState}
    {op : PrimOp} {step : PrimStep} {evm' : EVMState}
    (hStep : op.continuingStep? = some step)
    (hRun : step.run state = .ok evm') :
    XCoreStackAndJumpInputsReady validJumps state
      (TargetInstr.prim op).op := by
  have hArity := PrimStep.run_inputArity_le hRun
  have hDeltaAlpha := PrimOp.continuingStep?_delta_alpha hStep
  have hNotInvalid : op ≠ .invalid := by
    intro hInvalid
    subst op
    simp [PrimOp.continuingStep?] at hStep
    subst step
    simp [PrimStep.run] at hRun
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases op <;>
      simp [PrimOp.continuingStep?, TargetInstr.op, PrimOp.toEVM,
        EvmYul.EVM.δ] at hStep ⊢
    · exact hNotInvalid rfl
  · simpa [TargetInstr.op, hDeltaAlpha.1] using hArity
  · intro hJump
    cases op <;>
      simp [TargetInstr.op, PrimOp.toEVM] at hStep hJump
  · intro hJumpi _hCond
    cases op <;>
      simp [TargetInstr.op, PrimOp.toEVM] at hStep hJumpi

theorem XCoreStackAndJumpInputsReady.of_prim_continuing_stepInstrResult
    {validJumps : Array Word} {state : EVMState}
    {op : PrimOp} {step : PrimStep} {result : StepResult}
    (hStep : op.continuingStep? = some step)
    (hRun :
      Target.stepInstrResult (TargetInstr.prim op) state = .ok result) :
    XCoreStackAndJumpInputsReady validJumps state
      (TargetInstr.prim op).op := by
  cases result with
  | running mid =>
      have hStepRun :=
        (Target.stepInstrResult_running_stepInstr hRun).1
      simp [Target.stepInstr,
        PrimOp.step_eq_continuingStep_run hStep] at hStepRun
      exact
        XCoreStackAndJumpInputsReady.of_prim_continuing_run
          hStep hStepRun
  | halted halt =>
      have hStepRun :=
        (Target.stepInstrResult_halted_stepInstr hRun).1
      simp [Target.stepInstr,
        PrimOp.step_eq_continuingStep_run hStep] at hStepRun
      exact
        XCoreStackAndJumpInputsReady.of_prim_continuing_run
          hStep hStepRun

theorem XCoreStackAndJumpInputsReady.of_prim_stepInstrResult_no_call_create
    {validJumps : Array Word} {state : EVMState}
    {op : PrimOp} {result : StepResult}
    (hNoCallCreate : op.isCallCreate = false)
    (hRun :
      Target.stepInstrResult (TargetInstr.prim op) state = .ok result) :
    XCoreStackAndJumpInputsReady validJumps state
      (TargetInstr.prim op).op := by
  cases hStep : op.continuingStep? with
  | some step =>
      exact
        XCoreStackAndJumpInputsReady.of_prim_continuing_stepInstrResult
          hStep hRun
  | none =>
      obtain ⟨post, hStepInstr⟩ : ∃ post,
          Target.stepInstr (TargetInstr.prim op) state = .ok post := by
        cases result with
        | running mid =>
            exact ⟨mid, (Target.stepInstrResult_running_stepInstr hRun).1⟩
        | halted halt =>
            exact
              ⟨halt.state,
                (Target.stepInstrResult_halted_stepInstr hRun).1⟩
      have hOpStep : op.step state = .ok post := by
        simpa [Target.stepInstr] using hStepInstr
      rw [PrimOp.step_eq_evm_step_of_not_continuing
        hStep hNoCallCreate] at hOpStep
      refine ⟨?_, ?_, ?_, ?_⟩
      · cases op <;>
          simp [PrimOp.continuingStep?, PrimOp.isCallCreate, TargetInstr.op,
            PrimOp.toEVM, EvmYul.EVM.δ] at hStep hNoCallCreate ⊢
      · cases op <;>
          simp [PrimOp.continuingStep?, PrimOp.isCallCreate, TargetInstr.op,
            PrimOp.toEVM, EvmYul.EVM.δ] at hStep hNoCallCreate ⊢
        · change
            (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run
                state = .ok post at hOpStep
          have hArity := PrimStep.run_inputArity_le hOpStep
          simpa [PrimStep.inputArity] using hArity
        · change
            (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run
                state = .ok post at hOpStep
          have hArity := PrimStep.run_inputArity_le hOpStep
          simpa [PrimStep.inputArity] using hArity
        · change EvmYul.step (τ := .EVM)
            EvmYul.Operation.SELFDESTRUCT none state = .ok post at hOpStep
          cases hPop : state.stack.pop with
          | none =>
              rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop]
                at hOpStep
              cases hOpStep
          | some popped =>
              rcases popped with ⟨stack, recipient⟩
              have hLen := PrimStep.Stack.length_of_pop_some hPop
              omega
      · intro hJump
        cases op <;>
          simp [PrimOp.continuingStep?, PrimOp.isCallCreate,
            TargetInstr.op, PrimOp.toEVM] at hStep hNoCallCreate hJump
      · intro hJumpi _hCond
        cases op <;>
          simp [PrimOp.continuingStep?, PrimOp.isCallCreate,
            TargetInstr.op, PrimOp.toEVM] at hStep hNoCallCreate hJumpi

theorem XCoreStackAndJumpInputsReady.of_prim_continuing_runListResult
    {validJumps : Array Word} {state : EVMState}
    {op : PrimOp} {step : PrimStep} {result : StepResult}
    (hStep : op.continuingStep? = some step)
    (hRun :
      Target.runListResult [TargetInstr.prim op] state = .ok result) :
    XCoreStackAndJumpInputsReady validJumps state
      (TargetInstr.prim op).op := by
  rcases Target.runListResult_cons_ok_cases hRun with
    ⟨mid, hStepResult, _hRest⟩ | ⟨halt, hStepResult, _hResult⟩
  · exact
      XCoreStackAndJumpInputsReady.of_prim_continuing_stepInstrResult
        hStep hStepResult
  · exact
      XCoreStackAndJumpInputsReady.of_prim_continuing_stepInstrResult
        hStep hStepResult

theorem XCoreStackAndJumpInputsReady.of_prim_runListResult_no_call_create
    {validJumps : Array Word} {state : EVMState}
    {op : PrimOp} {result : StepResult}
    (hNoCallCreate : op.isCallCreate = false)
    (hRun :
      Target.runListResult [TargetInstr.prim op] state = .ok result) :
    XCoreStackAndJumpInputsReady validJumps state
      (TargetInstr.prim op).op := by
  rcases Target.runListResult_cons_ok_cases hRun with
    ⟨mid, hStepResult, _hRest⟩ | ⟨halt, hStepResult, _hResult⟩
  · exact
      XCoreStackAndJumpInputsReady.of_prim_stepInstrResult_no_call_create
        hNoCallCreate hStepResult
  · exact
      XCoreStackAndJumpInputsReady.of_prim_stepInstrResult_no_call_create
        hNoCallCreate hStepResult

theorem EVM_alpha_getD_le_17 (op : EVMOp) :
    (EvmYul.EVM.α op).getD 0 ≤ 17 := by
  cases op with
  | StopArith op => cases op <;> simp [EvmYul.EVM.α]
  | CompBit op => cases op <;> simp [EvmYul.EVM.α]
  | Keccak op =>
      cases op
      simp [EvmYul.EVM.α]
  | Env op => cases op <;> simp [EvmYul.EVM.α]
  | Block op => cases op <;> simp [EvmYul.EVM.α]
  | StackMemFlow op => cases op <;> simp [EvmYul.EVM.α]
  | Push n => simp [EvmYul.EVM.α]
  | Dup op => cases op <;> simp [EvmYul.EVM.α]
  | Exchange op => cases op <;> simp [EvmYul.EVM.α]
  | Log op => cases op <;> simp [EvmYul.EVM.α]
  | System op => cases op <;> simp [EvmYul.EVM.α]

theorem XNonGasCoreChecksPass.of_inputs_overflow_static
    {validJumps : Array Word} {state : EVMState} {op : EVMOp}
    (hInputs : XCoreStackAndJumpInputsReady validJumps state op)
    (hOverflow :
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
          (EvmYul.EVM.α op).getD 0 ≤ 1024)
    (hStatic :
      state.executionEnv.perm = false →
        ¬ staticWriteSensitive op state.stack) :
    XNonGasCoreChecksPass validJumps state op := by
  rcases hInputs with ⟨hDelta, hStack, hJump, hJumpi⟩
  exact ⟨hDelta, hStack, hJump, hJumpi, hOverflow, hStatic⟩

theorem XNonGasCoreChecksPass.to_inputs_overflow_static
    {validJumps : Array Word} {state : EVMState} {op : EVMOp}
    (hCore : XNonGasCoreChecksPass validJumps state op) :
    XCoreStackAndJumpInputsReady validJumps state op ∧
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
          (EvmYul.EVM.α op).getD 0 ≤ 1024 ∧
        (state.executionEnv.perm = false →
          ¬ staticWriteSensitive op state.stack) := by
  rcases hCore with
    ⟨hDelta, hStack, hJump, hJumpi, hOverflow, hStatic⟩
  exact ⟨⟨hDelta, hStack, hJump, hJumpi⟩, hOverflow, hStatic⟩

theorem Target.stepInstrResult_running_stack_le_of_core_no_call_create
    {validJumps : Array Word} {instr : TargetInstr}
    {state post : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hCore : XNonGasCoreChecksPass validJumps state instr.op)
    (hRun : Target.stepInstrResult instr state = .ok (.running post)) :
    post.stack.length ≤ 1024 := by
  rcases XNonGasCoreChecksPass.to_inputs_overflow_static hCore with
    ⟨hInputs, hOverflow, _hStatic⟩
  rcases hInputs with ⟨_hDelta, hStack, _hJump, _hJumpi⟩
  have hStepAndKind := Target.stepInstrResult_running_stepInstr hRun
  rcases hStepAndKind with ⟨hStepInstr, hKind⟩
  cases instr with
  | push32 value =>
      simp [Target.stepInstr, TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
        EvmYul.Stack.push] at hStepInstr hOverflow ⊢
      cases hStepInstr
      simpa [EvmYul.Stack.push] using hOverflow
  | jump =>
      simp [Target.stepInstr, TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α]
        at hStepInstr hOverflow
      cases hPop : state.stack.pop with
      | none => simp [hPop] at hStepInstr
      | some popped =>
          rcases popped with ⟨rest, dest⟩
          simp [hPop] at hStepInstr
          cases hStepInstr
          have hLen := PrimStep.Stack.length_of_pop_some hPop
          simp
          omega
  | jumpi =>
      simp [Target.stepInstr, TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α]
        at hStepInstr hOverflow
      cases hPop : state.stack.pop2 with
      | none => simp [hPop] at hStepInstr
      | some popped =>
          rcases popped with ⟨rest, dest, cond⟩
          simp [hPop] at hStepInstr
          cases hStepInstr
          have hLen := PrimStep.Stack.length_of_pop2_some hPop
          simp
          omega
  | jumpdest =>
      simp [Target.stepInstr, TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α,
        EvmYul.EVM.State.incrPC] at hStepInstr hOverflow ⊢
      cases hStepInstr
      exact hOverflow
  | prim op =>
      simp [Target.stepInstr] at hStepInstr
      cases hCont : op.continuingStep? with
      | none =>
          rw [PrimOp.step_eq_evm_step_of_not_continuing
            hCont hNoCallCreate] at hStepInstr
          cases op <;>
            simp [PrimOp.continuingStep?, PrimOp.isCallCreate,
              targetInstrUsesCallCreate, TargetInstr.haltKind?,
              PrimOp.haltKind?] at hCont hNoCallCreate hKind
          case pc =>
            simp [TargetInstr.op, PrimOp.toEVM, EvmYul.EVM.δ,
              EvmYul.EVM.α] at hOverflow
            have hPcStep :
                EvmYul.step PrimOp.pc.toEVM none state =
                  .ok (state.replaceStackAndIncrPC
                    (state.stack.push state.pc)) := rfl
            rw [hPcStep] at hStepInstr
            cases hStepInstr
            simpa [EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
              Nat.add_comm] using Nat.succ_le_succ hOverflow
      | some step =>
          rw [PrimOp.step_eq_continuingStep_run hCont] at hStepInstr
          have hArity := PrimOp.continuingStep?_delta_alpha hCont
          have hStackStep :
              PrimStep.inputArity step ≤ state.stack.length := by
            simpa [TargetInstr.op, hArity.1] using hStack
          have hBoundStep :
              state.stack.length - PrimStep.inputArity step +
                  PrimStep.outputArity step ≤ 1024 := by
            simpa [TargetInstr.op, hArity.1, hArity.2] using hOverflow
          exact
            PrimStep.run_stack_le_of_arity_bound hStackStep hBoundStep
              (fun n hEq => by
                subst step
                exact PrimOp.continuingStep?_swap_pos hCont)
              hStepInstr

theorem XNonGasCoreChecksPass.of_inputs_bounded_stack
    {validJumps : Array Word} {state : EVMState} {op : EVMOp}
    (hInputs : XCoreStackAndJumpInputsReady validJumps state op)
    (hStackBound : state.stack.length ≤ 16)
    (hStatic :
      state.executionEnv.perm = false →
        ¬ staticWriteSensitive op state.stack) :
    XNonGasCoreChecksPass validJumps state op := by
  rcases hInputs with ⟨hDelta, hStack, hJump, hJumpi⟩
  refine ⟨hDelta, hStack, hJump, hJumpi, ?_, hStatic⟩
  have hAlpha := EVM_alpha_getD_le_17 op
  omega

theorem XNonGasCoreChecksPass.of_inputs_bounded_stack_writable
    {validJumps : Array Word} {state : EVMState} {op : EVMOp}
    (hInputs : XCoreStackAndJumpInputsReady validJumps state op)
    (hStackBound : state.stack.length ≤ 16)
    (hWritable : state.executionEnv.perm = true) :
    XNonGasCoreChecksPass validJumps state op :=
  XNonGasCoreChecksPass.of_inputs_bounded_stack hInputs hStackBound (by
    intro hStatic
    rw [hWritable] at hStatic
    cases hStatic)

theorem XNonGasChecksPass.intro' {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hDelta : EvmYul.EVM.δ op ≠ none)
    (hStack :
      state.stack.length ≥ (EvmYul.EVM.δ op).getD 0)
    (hJump :
      op = EvmYul.Operation.JUMP →
        jumpTargetAllowed state.stack[0]? validJumps)
    (hJumpi :
      op = EvmYul.Operation.JUMPI →
        state.stack[1]? ≠ some ⟨0⟩ →
          jumpTargetAllowed state.stack[0]? validJumps)
    (hReturnData :
      op = EvmYul.Operation.RETURNDATACOPY →
        (state.stack.getD 1 ⟨0⟩).toNat +
            (state.stack.getD 2 ⟨0⟩).toNat ≤
          state.returnData.size)
    (hOverflow :
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
          (EvmYul.EVM.α op).getD 0 ≤ 1024)
    (hStatic :
      state.executionEnv.perm = false →
        ¬ staticWriteSensitive op state.stack)
    (hCreate :
      op.isCreate = true →
        state.stack.getD 2 ⟨0⟩ ≤ ⟨49152⟩) :
    XNonGasChecksPass validJumps state op :=
  ⟨hDelta, hStack, hJump, hJumpi, hReturnData, hOverflow, hStatic, hCreate⟩

def XReturnDataCopyBoundsPass (state : EVMState) (op : EVMOp) : Prop :=
  op = EvmYul.Operation.RETURNDATACOPY →
    (state.stack.getD 1 ⟨0⟩).toNat +
        (state.stack.getD 2 ⟨0⟩).toNat ≤
      state.returnData.size

theorem XReturnDataCopyBoundsPass.of_no_returnDataCopy
    {state : EVMState} {op : EVMOp}
    (hNoReturnDataCopy : op ≠ EvmYul.Operation.RETURNDATACOPY) :
    XReturnDataCopyBoundsPass state op := by
  intro hOp
  exact False.elim (hNoReturnDataCopy hOp)

theorem XReturnDataCopyBoundsPass_iff_of_gasExecRel
    {full target : EVMState} {op : EVMOp}
    (hRel : GasExecRel full target) :
    XReturnDataCopyBoundsPass full op ↔
      XReturnDataCopyBoundsPass target op := by
  rw [hRel]
  cases target
  rfl

theorem XReturnDataCopyBoundsPass.of_stepInstrResult_ok
    {instr : TargetInstr} {target : EVMState} {result : StepResult}
    (hStep : Target.stepInstrResult instr target = .ok result) :
    XReturnDataCopyBoundsPass target instr.op := by
  intro hOp
  cases instr with
  | push32 value =>
      simp [TargetInstr.op] at hOp
  | jump =>
      simp [TargetInstr.op] at hOp
  | jumpi =>
      simp [TargetInstr.op] at hOp
  | jumpdest =>
      simp [TargetInstr.op] at hOp
  | prim op =>
      cases op <;> simp [TargetInstr.op, PrimOp.toEVM] at hOp
      case returndatacopy =>
        clear hOp
        rw [Target.stepInstrResult, Target.stepInstr] at hStep
        cases hPop : target.stack.pop3 with
        | none =>
            simp [PrimOp.step, PrimOp.continuingStep?, PrimStep.run,
              hPop] at hStep
            cases hStep
        | some popped =>
            rcases popped with ⟨stack, memStart, dataStart, size⟩
            by_cases hBounds :
                target.returnData.size < dataStart.toNat + size.toNat
            · simp [PrimOp.step, PrimOp.continuingStep?, PrimStep.run,
                hPop, hBounds] at hStep
              cases hStep
            · have hLe :
                  dataStart.toNat + size.toNat ≤ target.returnData.size :=
                Nat.le_of_not_gt hBounds
              have hStack :
                  target.stack = memStart :: dataStart :: size :: stack :=
                stack_eq_cons_cons_cons_of_pop3 hPop
              simpa [XReturnDataCopyBoundsPass, hStack] using hLe

theorem XNonGasChecksPass.of_core_returnDataCopyBounds_no_create
    {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hCore : XNonGasCoreChecksPass validJumps state op)
    (hReturnDataCopyBounds : XReturnDataCopyBoundsPass state op)
    (hNoCreate : op.isCreate = false) :
    XNonGasChecksPass validJumps state op := by
  rcases hCore with
    ⟨hDelta, hStack, hJump, hJumpi, hOverflow, hStatic⟩
  refine
    XNonGasChecksPass.intro' hDelta hStack hJump hJumpi
      hReturnDataCopyBounds hOverflow hStatic ?_
  intro hCreate
  rw [hNoCreate] at hCreate
  cases hCreate

theorem XNonGasChecksPass.of_core_no_returnDataCopy_no_create
    {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hCore : XNonGasCoreChecksPass validJumps state op)
    (hNoReturnDataCopy : op ≠ EvmYul.Operation.RETURNDATACOPY)
    (hNoCreate : op.isCreate = false) :
    XNonGasChecksPass validJumps state op := by
  rcases hCore with
    ⟨hDelta, hStack, hJump, hJumpi, hOverflow, hStatic⟩
  refine
    XNonGasChecksPass.intro' hDelta hStack hJump hJumpi ?_
      hOverflow hStatic ?_
  · intro hOp
    exact
      XReturnDataCopyBoundsPass.of_no_returnDataCopy
        hNoReturnDataCopy hOp
  · intro hCreate
    rw [hNoCreate] at hCreate
    cases hCreate

theorem XNonGasChecksPass.of_no_returnDataCopy_no_create
    {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hDelta : EvmYul.EVM.δ op ≠ none)
    (hStack :
      state.stack.length ≥ (EvmYul.EVM.δ op).getD 0)
    (hJump :
      op = EvmYul.Operation.JUMP →
        jumpTargetAllowed state.stack[0]? validJumps)
    (hJumpi :
      op = EvmYul.Operation.JUMPI →
        state.stack[1]? ≠ some ⟨0⟩ →
          jumpTargetAllowed state.stack[0]? validJumps)
    (hNoReturnDataCopy : op ≠ EvmYul.Operation.RETURNDATACOPY)
    (hOverflow :
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
          (EvmYul.EVM.α op).getD 0 ≤ 1024)
    (hStatic :
      state.executionEnv.perm = false →
        ¬ staticWriteSensitive op state.stack)
    (hNoCreate : op.isCreate = false) :
    XNonGasChecksPass validJumps state op := by
  refine
    XNonGasChecksPass.intro' hDelta hStack hJump hJumpi ?_
      hOverflow hStatic ?_
  · intro hOp
    exact False.elim (hNoReturnDataCopy hOp)
  · intro hCreate
    rw [hNoCreate] at hCreate
    cases hCreate

theorem XNonGasChecksPass.of_no_returnDataCopy_no_create_writable
    {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hDelta : EvmYul.EVM.δ op ≠ none)
    (hStack :
      state.stack.length ≥ (EvmYul.EVM.δ op).getD 0)
    (hJump :
      op = EvmYul.Operation.JUMP →
        jumpTargetAllowed state.stack[0]? validJumps)
    (hJumpi :
      op = EvmYul.Operation.JUMPI →
        state.stack[1]? ≠ some ⟨0⟩ →
          jumpTargetAllowed state.stack[0]? validJumps)
    (hNoReturnDataCopy : op ≠ EvmYul.Operation.RETURNDATACOPY)
    (hOverflow :
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
          (EvmYul.EVM.α op).getD 0 ≤ 1024)
    (hWritable : state.executionEnv.perm = true)
    (hNoCreate : op.isCreate = false) :
    XNonGasChecksPass validJumps state op :=
  XNonGasChecksPass.of_no_returnDataCopy_no_create
    hDelta hStack hJump hJumpi hNoReturnDataCopy hOverflow
    (by
      intro hStatic
      rw [hWritable] at hStatic
      cases hStatic)
    hNoCreate

theorem XNonGasChecksPass_iff_of_gasExecRel {validJumps : Array Word}
    {full target : EVMState} {op : EVMOp}
    (hRel : GasExecRel full target) :
    XNonGasChecksPass validJumps full op ↔
      XNonGasChecksPass validJumps target op := by
  rw [hRel]
  cases target
  rfl

theorem XNonGasCoreChecksPass_iff_of_gasExecRel {validJumps : Array Word}
    {full target : EVMState} {op : EVMOp}
    (hRel : GasExecRel full target) :
    XNonGasCoreChecksPass validJumps full op ↔
      XNonGasCoreChecksPass validJumps target op := by
  rw [hRel]
  cases target
  rfl

/--
The gas-only checks performed by `EVM.X` before it calls `EVM.step`, expressed
against the state after the memory-expansion charge has been subtracted.
-/
def XGasChecksPassAt (state : EVMState) (op : EVMOp) : Prop :=
  EvmYul.EVM.memoryExpansionCost state op ≤ state.gasAvailable.toNat ∧
    EvmYul.EVM.C' (memoryGasState state op) op ≤
      (memoryGasState state op).gasAvailable.toNat ∧
      (op = EvmYul.Operation.SSTORE →
        GasConstants.Gcallstipend <
          (memoryGasState state op).gasAvailable.toNat)

def sstoreStipendExtra (op : EVMOp) : Nat :=
  if op = EvmYul.Operation.SSTORE then GasConstants.Gcallstipend + 1 else 0

def XGasRequiredAt (state : EVMState) (op : EVMOp) : Nat :=
  EvmYul.EVM.memoryExpansionCost state op +
    EvmYul.EVM.C' (memoryGasState state op) op +
      sstoreStipendExtra op

def xBodyState (state : EVMState) (op : EVMOp) : EVMState :=
  { memoryGasState state op with
    gasAvailable :=
      (memoryGasState state op).gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.C' (memoryGasState state op) op),
    execLength := (memoryGasState state op).execLength + 1 }

theorem XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
    {full target : EVMState} {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target) :
    XGasRequiredAt full instr.op =
      XGasRequiredAt target instr.op := by
  unfold XGasRequiredAt
  rw [memoryExpansionCost_eq_of_gasExecRel hRel instr.op]
  rw [C'_eq_of_gasExecRel_of_targetInstr_no_call_create
    hNoCallCreate (hRel.memoryGasState_both (op := instr.op))]

theorem memoryGasState_gasAvailable_toNat
    {state : EVMState} {op : EVMOp}
    (hMem :
      EvmYul.EVM.memoryExpansionCost state op ≤ state.gasAvailable.toNat) :
    (memoryGasState state op).gasAvailable.toNat =
      state.gasAvailable.toNat -
        EvmYul.EVM.memoryExpansionCost state op := by
  have hMemLt :
      EvmYul.EVM.memoryExpansionCost state op < EvmYul.UInt256.size :=
    lt_of_le_of_lt hMem state.gasAvailable.val.2
  have hMemNat :
      (EvmYul.UInt256.ofNat
        (EvmYul.EVM.memoryExpansionCost state op)).toNat =
          EvmYul.EVM.memoryExpansionCost state op :=
    Bytecode.uint256_ofNat_toNat_of_lt_size hMemLt
  have hSub :=
    uint256_sub_toNat_of_le
      (left := state.gasAvailable)
      (right :=
        EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op))
      (by simpa [hMemNat] using hMem)
  simpa [memoryGasState, hMemNat] using hSub

theorem xBodyState_gasAvailable_toNat_of_required
    {state : EVMState} {op : EVMOp} {restBudget : Nat}
    (hRequired :
      XGasRequiredAt state op + restBudget ≤ state.gasAvailable.toNat) :
    restBudget ≤ (xBodyState state op).gasAvailable.toNat := by
  have hMem :
      EvmYul.EVM.memoryExpansionCost state op ≤
        state.gasAvailable.toNat := by
    unfold XGasRequiredAt at hRequired
    omega
  have hMemGas :
      (memoryGasState state op).gasAvailable.toNat =
        state.gasAvailable.toNat -
          EvmYul.EVM.memoryExpansionCost state op :=
    memoryGasState_gasAvailable_toNat (state := state) (op := op) hMem
  have hCostLe :
      EvmYul.EVM.C' (memoryGasState state op) op ≤
        (memoryGasState state op).gasAvailable.toNat := by
    rw [hMemGas]
    unfold XGasRequiredAt at hRequired
    omega
  have hCostLt :
      EvmYul.EVM.C' (memoryGasState state op) op < EvmYul.UInt256.size :=
    lt_of_le_of_lt hCostLe (memoryGasState state op).gasAvailable.val.2
  have hCostNat :
      (EvmYul.UInt256.ofNat
        (EvmYul.EVM.C' (memoryGasState state op) op)).toNat =
          EvmYul.EVM.C' (memoryGasState state op) op :=
    Bytecode.uint256_ofNat_toNat_of_lt_size hCostLt
  have hSub :
      ((memoryGasState state op).gasAvailable -
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.C' (memoryGasState state op) op)).toNat =
        (memoryGasState state op).gasAvailable.toNat -
          EvmYul.EVM.C' (memoryGasState state op) op := by
    simpa [hCostNat] using
      uint256_sub_toNat_of_le
        (left := (memoryGasState state op).gasAvailable)
        (right :=
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.C' (memoryGasState state op) op))
        (by simpa [hCostNat] using hCostLe)
  have hRest :
      restBudget ≤
        (memoryGasState state op).gasAvailable.toNat -
          EvmYul.EVM.C' (memoryGasState state op) op := by
    rw [hMemGas]
    unfold XGasRequiredAt at hRequired
    omega
  change
    restBudget ≤
      ((memoryGasState state op).gasAvailable -
        EvmYul.UInt256.ofNat
          (EvmYul.EVM.C' (memoryGasState state op) op)).toNat
  rw [hSub]
  exact hRest

theorem EVM_step_targetInstr_eq_xBodyState {fuel : Nat}
    {state : EVMState} {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false) :
    EvmYul.EVM.step fuel.succ
        (EvmYul.EVM.C' (memoryGasState state instr.op) instr.op)
        (some (instr.op, instr.arg)) (memoryGasState state instr.op) =
      EvmYul.step instr.op instr.arg (xBodyState state instr.op) := by
  simpa [xBodyState] using
    EVM_step_targetInstr_eq_of_no_call_create
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState state instr.op) instr.op)
      (state := memoryGasState state instr.op)
      (instr := instr) hNoCallCreate

theorem XGasChecksPassAt.of_required_le
    {state : EVMState} {op : EVMOp}
    (hRequired :
      XGasRequiredAt state op ≤ state.gasAvailable.toNat) :
    XGasChecksPassAt state op := by
  have hMem :
      EvmYul.EVM.memoryExpansionCost state op ≤ state.gasAvailable.toNat := by
    unfold XGasRequiredAt at hRequired
    omega
  have hGasAfter :=
    memoryGasState_gasAvailable_toNat (state := state) (op := op) hMem
  refine ⟨hMem, ?_, ?_⟩
  · rw [hGasAfter]
    unfold XGasRequiredAt at hRequired
    omega
  · intro hSstore
    rw [hGasAfter]
    subst op
    simp [XGasRequiredAt, sstoreStipendExtra] at hRequired
    omega

def XStepChecksPass (validJumps : Array Word) (state : EVMState)
    (op : EVMOp) : Prop :=
  XNonGasChecksPass validJumps state op ∧ XGasChecksPassAt state op

theorem XNonGasChecksPass_stop {validJumps : Array Word}
    {state : EVMState}
    (hStack : state.stack.length ≤ 1024) :
    XNonGasChecksPass validJumps state EvmYul.Operation.STOP := by
  simp [XNonGasChecksPass, jumpTargetAllowed, staticWriteSensitive,
    EvmYul.EVM.δ, EvmYul.EVM.α, EvmYul.Operation.isCreate, hStack]

theorem XGasRequiredAt_stop_eq_zero (state : EVMState) :
    XGasRequiredAt state EvmYul.Operation.STOP = 0 := by
  simp [XGasRequiredAt, sstoreStipendExtra, memoryGasState,
    EvmYul.EVM.memoryExpansionCost, EvmYul.EVM.memoryExpansionCost.μᵢ']
  cases state
  simp [EvmYul.EVM.C', EvmYul.EVM.InstructionGasGroups.Wcopy,
    EvmYul.EVM.InstructionGasGroups.Wextaccount,
    EvmYul.EVM.InstructionGasGroups.Wzero, GasConstants.Gzero]

theorem XStepChecksPass_stop_of_required_le {validJumps : Array Word}
    {state : EVMState}
    (hStack : state.stack.length ≤ 1024)
    (hRequired :
      XGasRequiredAt state EvmYul.Operation.STOP ≤ state.gasAvailable.toNat) :
    XStepChecksPass validJumps state EvmYul.Operation.STOP :=
  ⟨XNonGasChecksPass_stop hStack, XGasChecksPassAt.of_required_le hRequired⟩

theorem XStepChecksPass_stop {validJumps : Array Word}
    {state : EVMState}
    (hStack : state.stack.length ≤ 1024) :
    XStepChecksPass validJumps state EvmYul.Operation.STOP := by
  refine XStepChecksPass_stop_of_required_le hStack ?_
  rw [XGasRequiredAt_stop_eq_zero]
  exact Nat.zero_le _

theorem XStepChecksPass.of_nonGas_required_le {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hNonGas : XNonGasChecksPass validJumps state op)
    (hRequired : XGasRequiredAt state op ≤ state.gasAvailable.toNat) :
    XStepChecksPass validJumps state op :=
  ⟨hNonGas, XGasChecksPassAt.of_required_le hRequired⟩

structure XStepRawChecksPass (validJumps : Array Word) (state : EVMState)
    (op : EVMOp) : Prop where
  memoryGas : ¬ (state.gasAvailable.toNat < EvmYul.EVM.memoryExpansionCost state op)
  dynamicGas : ¬ ((memoryGasState state op).gasAvailable.toNat <
    EvmYul.EVM.C' (memoryGasState state op) op)
  delta : ¬ (EvmYul.EVM.δ op = none)
  stack : ¬ ((memoryGasState state op).stack.length < (EvmYul.EVM.δ op).getD 0)
  jump : ¬ (op = EvmYul.Operation.JUMP ∧
    EvmYul.EVM.X.notIn (memoryGasState state op).stack[0]? validJumps = true)
  jumpi : ¬ (op = EvmYul.Operation.JUMPI ∧
    (memoryGasState state op).stack[1]? ≠ some (⟨0⟩ : Word) ∧
      EvmYul.EVM.X.notIn (memoryGasState state op).stack[0]? validJumps = true)
  returnData : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
    ((memoryGasState state op).stack.getD 1 (⟨0⟩ : Word)).toNat +
      ((memoryGasState state op).stack.getD 2 (⟨0⟩ : Word)).toNat >
        (memoryGasState state op).returnData.size)
  stackOverflow : ¬ ((memoryGasState state op).stack.length -
      (EvmYul.EVM.δ op).getD 0 + (EvmYul.EVM.α op).getD 0 > 1024)
  staticMode : ¬ ((¬ (memoryGasState state op).executionEnv.perm) ∧
    (op ∈ [EvmYul.Operation.CREATE, EvmYul.Operation.CREATE2,
      EvmYul.Operation.SSTORE, EvmYul.Operation.SELFDESTRUCT,
      EvmYul.Operation.LOG0, EvmYul.Operation.LOG1, EvmYul.Operation.LOG2,
      EvmYul.Operation.LOG3, EvmYul.Operation.LOG4,
      EvmYul.Operation.TSTORE] ∨
      (op = EvmYul.Operation.CALL ∧
        (memoryGasState state op).stack[2]? ≠ some (⟨0⟩ : Word))))
  sstoreStipend : ¬ (op = EvmYul.Operation.SSTORE ∧
    (memoryGasState state op).gasAvailable.toNat ≤ GasConstants.Gcallstipend)
  createSize : ¬ (op.isCreate = true ∧
    (memoryGasState state op).stack.getD 2 (⟨0⟩ : Word) > (⟨49152⟩ : Word))

def XHaltOutput? (op : EVMOp) (state : EVMState) : Option ByteArray :=
  if op ∈ [EvmYul.Operation.RETURN, EvmYul.Operation.REVERT] then
    some state.toMachineState.H_return
  else if op ∈ [EvmYul.Operation.STOP, EvmYul.Operation.SELFDESTRUCT] then
    some ByteArray.empty
  else
    none

def XStepHaltOutput? (op : EVMOp) (state : EVMState) : Option ByteArray :=
  if op = EvmYul.Operation.RETURN ∨ op = EvmYul.Operation.REVERT then
    some state.toMachineState.H_return
  else if op = EvmYul.Operation.STOP ∨ op = EvmYul.Operation.SELFDESTRUCT then
    some ByteArray.empty
  else
    none

theorem XHaltOutput?_eq_XStepHaltOutput?
    (op : EVMOp) (state : EVMState) :
    XHaltOutput? op state = XStepHaltOutput? op state := by
  simp [XHaltOutput?, XStepHaltOutput?]

theorem XHaltOutput?_none_of_targetInstr_haltKind_none
    {instr : TargetInstr} {state : EVMState}
    (hKind : instr.haltKind? = none) :
    XHaltOutput? instr.op state = none := by
  cases instr with
  | push32 value =>
      rfl
  | jump =>
      rfl
  | jumpi =>
      rfl
  | jumpdest =>
      rfl
  | prim op =>
      cases op <;> simp [TargetInstr.haltKind?, PrimOp.haltKind?,
        TargetInstr.op, PrimOp.toEVM, XHaltOutput?] at hKind ⊢

theorem XHaltOutput?_some_of_targetInstr_haltKind_some
    {instr : TargetInstr} {state : EVMState} {kind : HaltKind}
    (hKind : instr.haltKind? = some kind) :
    XHaltOutput? instr.op state = some (kind.output state) := by
  cases instr with
  | push32 value =>
      simp [TargetInstr.haltKind?] at hKind
  | jump =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpi =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpdest =>
      simp [TargetInstr.haltKind?] at hKind
  | prim op =>
      cases op <;> simp [TargetInstr.haltKind?, PrimOp.haltKind?,
        TargetInstr.op, PrimOp.toEVM, XHaltOutput?, HaltKind.output] at hKind ⊢
      all_goals cases hKind
      all_goals rfl

theorem targetInstr_op_ne_revert_of_haltKind_some_ne
    {instr : TargetInstr} {kind : HaltKind}
    (hKind : instr.haltKind? = some kind)
    (hNotRevert : kind ≠ .revert) :
    instr.op ≠ EvmYul.Operation.REVERT := by
  intro hOp
  cases instr with
  | push32 value =>
      simp [TargetInstr.haltKind?] at hKind
  | jump =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpi =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpdest =>
      simp [TargetInstr.haltKind?] at hKind
  | prim op =>
      cases op <;> simp [TargetInstr.haltKind?, PrimOp.haltKind?,
        TargetInstr.op, PrimOp.toEVM] at hKind hOp
      cases hKind
      exact hNotRevert rfl

theorem targetInstr_op_eq_revert_of_haltKind_revert
    {instr : TargetInstr}
    (hKind : instr.haltKind? = some .revert) :
    instr.op = EvmYul.Operation.REVERT := by
  cases instr with
  | push32 value =>
      simp [TargetInstr.haltKind?] at hKind
  | jump =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpi =>
      simp [TargetInstr.haltKind?] at hKind
  | jumpdest =>
      simp [TargetInstr.haltKind?] at hKind
  | prim op =>
      cases op <;> simp [TargetInstr.haltKind?, PrimOp.haltKind?,
        TargetInstr.op, PrimOp.toEVM] at hKind ⊢

theorem XStepRawChecksPass.of_step_checks {validJumps : Array Word}
    {state : EVMState} {op : EVMOp}
    (hChecks : XStepChecksPass validJumps state op) :
    XStepRawChecksPass validJumps state op := by
  rcases hChecks with ⟨hNon, hGas⟩
  rcases hNon with
    ⟨hDelta, hStack, hJump, hJumpi, hReturnData, hOverflow, hStatic, hCreate⟩
  rcases hGas with ⟨hMemoryGas, hDynamicGas, hSstore⟩
  refine
    { memoryGas := ?_
      dynamicGas := ?_
      delta := hDelta
      stack := ?_
      jump := ?_
      jumpi := ?_
      returnData := ?_
      stackOverflow := ?_
      staticMode := ?_
      sstoreStipend := ?_
      createSize := ?_ }
  · omega
  · omega
  · simpa [memoryGasState] using (not_lt_of_ge hStack)
  · intro hBad
    rcases hBad with ⟨hOp, hBad⟩
    have hAllowed := hJump hOp
    unfold jumpTargetAllowed at hAllowed
    subst op
    cases hTarget : state.stack[0]? with
    | none =>
        simp [hTarget] at hAllowed
    | some target =>
        simp [hTarget] at hAllowed
        simp [memoryGasState, EvmYul.EVM.X.notIn, EvmYul.EVM.X.belongs,
          hTarget, hAllowed] at hBad
  · intro hBad
    rcases hBad with ⟨hOp, hCond, hBad⟩
    have hCond' : state.stack[1]? ≠ some (⟨0⟩ : Word) := by
      simpa [memoryGasState] using hCond
    have hAllowed := hJumpi hOp hCond'
    unfold jumpTargetAllowed at hAllowed
    subst op
    cases hTarget : state.stack[0]? with
    | none =>
        simp [hTarget] at hAllowed
    | some target =>
        simp [hTarget] at hAllowed
        simp [memoryGasState, EvmYul.EVM.X.notIn, EvmYul.EVM.X.belongs,
          hTarget, hAllowed] at hBad
  · intro hBad
    exact (not_lt_of_ge (hReturnData hBad.1)) (by
      simpa [memoryGasState] using hBad.2)
  · simpa [memoryGasState] using (not_lt_of_ge hOverflow)
  · intro hBad
    rcases hBad with ⟨hNoPerm, hWrite⟩
    have hPermFalse : state.executionEnv.perm = false := by
      simpa using hNoPerm
    exact (hStatic hPermFalse) (by
      simpa [memoryGasState, staticWriteSensitive, or_assoc] using hWrite)
  · intro hBad
    exact (not_le_of_gt (hSstore hBad.1)) hBad.2
  · intro hBad
    have hCreateGet :
        state.stack[2]?.getD (⟨0⟩ : Word) ≤ (⟨49152⟩ : Word) := by
      simpa using hCreate hBad.1
    have hTooLarge0 := hBad.2
    simp [memoryGasState] at hTooLarge0
    have hTooLarge :
        (⟨49152⟩ : Word).val <
          (state.stack[2]?.getD (⟨0⟩ : Word)).val := by
      change (⟨49152⟩ : Word).val <
        (state.stack[2]?.getD (⟨0⟩ : Word)).val at hTooLarge0
      exact hTooLarge0
    have hCreateGet0 := hCreateGet
    have hCreateVal :
        (state.stack[2]?.getD (⟨0⟩ : Word)).val ≤
          (⟨49152⟩ : Word).val := by
      change (state.stack[2]?.getD (⟨0⟩ : Word)).val ≤
        (⟨49152⟩ : Word).val at hCreateGet0
      exact hCreateGet0
    exact (not_lt_of_ge hCreateVal) hTooLarge

set_option linter.unusedSimpArgs false in
theorem X_step_expand_of_raw_checks_of_getD {fuel : Nat}
    {validJumps : Array Word}
    {state : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    (hInstr :
      (EvmYul.EVM.decode state.executionEnv.code state.pc).getD
        (EvmYul.Operation.STOP, none) = (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op) :
    EvmYul.EVM.X fuel.succ validJumps state =
      (do
        let evmState' ←
          EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
            (some (op, arg)) (memoryGasState state op)
        match XStepHaltOutput? op evmState' with
        | none => EvmYul.EVM.X fuel validJumps evmState'
        | some output =>
            if op = EvmYul.Operation.REVERT then
              .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
            else
              .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) := by
  have hDynamic : ¬ ((state.gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op)).toNat <
      EvmYul.EVM.C'
        { state with
          gasAvailable :=
            state.gasAvailable -
              EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }
        op) := by
    simpa [memoryGasState] using hChecks.dynamicGas
  have hStack : ¬ (state.stack.length < (EvmYul.EVM.δ op).getD 0) := by
    simpa [memoryGasState] using hChecks.stack
  have hJump : ¬ (op = EvmYul.Operation.JUMP ∧
      EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [memoryGasState] using hChecks.jump
  have hJumpi : ¬ (op = EvmYul.Operation.JUMPI ∧
      state.stack[1]? ≠ some (⟨0⟩ : Word) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [memoryGasState] using hChecks.jumpi
  have hReturnData : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
      state.returnData.size <
        (state.stack.getD 1 (⟨0⟩ : Word)).toNat +
          (state.stack.getD 2 (⟨0⟩ : Word)).toNat) := by
    simpa [memoryGasState, Nat.lt_iff_add_one_le] using hChecks.returnData
  have hStackOverflow : ¬ (1024 <
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
        (EvmYul.EVM.α op).getD 0) := by
    simpa [memoryGasState] using hChecks.stackOverflow
  have hStatic : ¬ (state.executionEnv.perm = false ∧
      ((op = EvmYul.Operation.CREATE ∨
          op = EvmYul.Operation.CREATE2 ∨
            op = EvmYul.Operation.SSTORE ∨
              op = EvmYul.Operation.SELFDESTRUCT ∨
                op = EvmYul.Operation.LOG0 ∨
                  op = EvmYul.Operation.LOG1 ∨
                    op = EvmYul.Operation.LOG2 ∨
                      op = EvmYul.Operation.LOG3 ∨
                        op = EvmYul.Operation.LOG4 ∨
                          op = EvmYul.Operation.TSTORE) ∨
        op = EvmYul.Operation.CALL ∧
          state.stack[2]? ≠ some (⟨0⟩ : Word))) := by
    simpa [memoryGasState] using hChecks.staticMode
  have hSstore : ¬ (op = EvmYul.Operation.SSTORE ∧
      (state.gasAvailable -
          EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op)).toNat ≤
        GasConstants.Gcallstipend) := by
    simpa [memoryGasState] using hChecks.sstoreStipend
  have hCreate : ¬ (op.isCreate = true ∧
      (⟨49152⟩ : Word) <
        state.stack.getD 2 (⟨0⟩ : Word)) := by
    simpa [memoryGasState] using hChecks.createSize
  have hReturnData' : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
      state.returnData.size <
        (state.stack[1]?.getD (⟨0⟩ : Word)).toNat +
          (state.stack[2]?.getD (⟨0⟩ : Word)).toNat) := by
    simpa using hReturnData
  have hStatic' : ¬ (state.executionEnv.perm = false ∧
      ((op = EvmYul.Operation.CREATE ∨
          op = EvmYul.Operation.CREATE2 ∨
            op = EvmYul.Operation.SSTORE ∨
              op = EvmYul.Operation.SELFDESTRUCT ∨
                op = EvmYul.Operation.LOG0 ∨
                  op = EvmYul.Operation.LOG1 ∨
                    op = EvmYul.Operation.LOG2 ∨
                      op = EvmYul.Operation.LOG3 ∨
                        op = EvmYul.Operation.LOG4 ∨
                          op = EvmYul.Operation.TSTORE) ∨
        op = EvmYul.Operation.CALL ∧
          ¬ state.stack[2]? = some (⟨0⟩ : Word))) := by
    simpa using hStatic
  have hCreate' : ¬ (op.isCreate = true ∧
      (⟨49152⟩ : Word) < state.stack[2]?.getD (⟨0⟩ : Word)) := by
    simpa using hCreate
  simp [EvmYul.EVM.X, hInstr, hChecks.memoryGas, hDynamic,
    hChecks.delta, hStack, hJump, hStackOverflow, hSstore]
  rw [if_neg hJumpi]
  rw [if_neg hReturnData']
  rw [if_neg hStatic']
  rw [if_neg hCreate']
  change
    (match
      pure
        ({ state with
          gasAvailable :=
            state.gasAvailable -
              EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) },
          EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }
            op) with
    | Except.error e => Except.error e
    | Except.ok (evmState, cost₂) => do
      let evmState' ← EvmYul.EVM.step fuel cost₂ (some (op, arg)) evmState
      match XStepHaltOutput? op evmState' with
      | none => EvmYul.EVM.X fuel validJumps evmState'
      | some output =>
          if op = EvmYul.Operation.REVERT then
            .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
          else
            .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) =
      (do
        let evmState' ←
          EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              { state with
                gasAvailable :=
                  state.gasAvailable -
                    EvmYul.UInt256.ofNat
                      (EvmYul.EVM.memoryExpansionCost state op) }
              op)
            (some (op, arg))
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state op) }
        match XStepHaltOutput? op evmState' with
        | none => EvmYul.EVM.X fuel validJumps evmState'
        | some output =>
            if op = EvmYul.Operation.REVERT then
              .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
            else
              .ok (EvmYul.EVM.ExecutionResult.success evmState' output))
  rfl

theorem X_step_expand_of_raw_checks {fuel : Nat} {validJumps : Array Word}
    {state : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op) :
    EvmYul.EVM.X fuel.succ validJumps state =
      (do
        let evmState' ←
          EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
            (some (op, arg)) (memoryGasState state op)
        match XStepHaltOutput? op evmState' with
        | none => EvmYul.EVM.X fuel validJumps evmState'
        | some output =>
            if op = EvmYul.Operation.REVERT then
              .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
            else
              .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) := by
  exact
    X_step_expand_of_raw_checks_of_getD
      (by simp [hDecode]) hChecks

theorem X_step_expand_default_stop_of_raw_checks {fuel : Nat}
    {validJumps : Array Word} {state : EVMState}
    (hDecodeNone : EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hChecks :
      XStepRawChecksPass validJumps state EvmYul.Operation.STOP) :
    EvmYul.EVM.X fuel.succ validJumps state =
      (do
        let evmState' ←
          EvmYul.EVM.step fuel
            (EvmYul.EVM.C'
              (memoryGasState state EvmYul.Operation.STOP)
              EvmYul.Operation.STOP)
            (some (EvmYul.Operation.STOP, none))
            (memoryGasState state EvmYul.Operation.STOP)
        match XStepHaltOutput? EvmYul.Operation.STOP evmState' with
        | none => EvmYul.EVM.X fuel validJumps evmState'
        | some output =>
            if (EvmYul.Operation.STOP : EVMOp) =
                (EvmYul.Operation.REVERT : EVMOp) then
              .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
            else
              .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) := by
  exact
    X_step_expand_of_raw_checks_of_getD
      (by simp [hDecodeNone]) hChecks

theorem X_step_running_of_raw_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hNoHalt : XHaltOutput? op post = none) :
    EvmYul.EVM.X fuel.succ validJumps state =
      EvmYul.EVM.X fuel validJumps post := by
  have hDynamic : ¬ ((state.gasAvailable -
        EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op)).toNat <
      EvmYul.EVM.C'
        { state with
          gasAvailable :=
            state.gasAvailable -
              EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }
        op) := by
    simpa [memoryGasState] using hChecks.dynamicGas
  have hStack : ¬ (state.stack.length < (EvmYul.EVM.δ op).getD 0) := by
    simpa [memoryGasState] using hChecks.stack
  have hJump : ¬ (op = EvmYul.Operation.JUMP ∧
      EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [memoryGasState] using hChecks.jump
  have hJumpi : ¬ (op = EvmYul.Operation.JUMPI ∧
      state.stack[1]? ≠ some (⟨0⟩ : Word) ∧
        EvmYul.EVM.X.notIn state.stack[0]? validJumps = true) := by
    simpa [memoryGasState] using hChecks.jumpi
  have hReturnData : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
      state.returnData.size <
        (state.stack.getD 1 (⟨0⟩ : Word)).toNat +
          (state.stack.getD 2 (⟨0⟩ : Word)).toNat) := by
    simpa [memoryGasState, Nat.lt_iff_add_one_le] using hChecks.returnData
  have hStackOverflow : ¬ (1024 <
      state.stack.length - (EvmYul.EVM.δ op).getD 0 +
        (EvmYul.EVM.α op).getD 0) := by
    simpa [memoryGasState] using hChecks.stackOverflow
  have hStatic : ¬ (state.executionEnv.perm = false ∧
      ((op = EvmYul.Operation.CREATE ∨
          op = EvmYul.Operation.CREATE2 ∨
            op = EvmYul.Operation.SSTORE ∨
              op = EvmYul.Operation.SELFDESTRUCT ∨
                op = EvmYul.Operation.LOG0 ∨
                  op = EvmYul.Operation.LOG1 ∨
                    op = EvmYul.Operation.LOG2 ∨
                      op = EvmYul.Operation.LOG3 ∨
                        op = EvmYul.Operation.LOG4 ∨
                          op = EvmYul.Operation.TSTORE) ∨
        op = EvmYul.Operation.CALL ∧
          state.stack[2]? ≠ some (⟨0⟩ : Word))) := by
    simpa [memoryGasState] using hChecks.staticMode
  have hSstore : ¬ (op = EvmYul.Operation.SSTORE ∧
      (state.gasAvailable -
          EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op)).toNat ≤
        GasConstants.Gcallstipend) := by
    simpa [memoryGasState] using hChecks.sstoreStipend
  have hCreate : ¬ (op.isCreate = true ∧
      (⟨49152⟩ : Word) <
        state.stack.getD 2 (⟨0⟩ : Word)) := by
    simpa [memoryGasState] using hChecks.createSize
  have hReturnData' : ¬ (op = EvmYul.Operation.RETURNDATACOPY ∧
      state.returnData.size <
        (state.stack[1]?.getD (⟨0⟩ : Word)).toNat +
          (state.stack[2]?.getD (⟨0⟩ : Word)).toNat) := by
    simpa using hReturnData
  have hStatic' : ¬ (state.executionEnv.perm = false ∧
      ((op = EvmYul.Operation.CREATE ∨
          op = EvmYul.Operation.CREATE2 ∨
            op = EvmYul.Operation.SSTORE ∨
              op = EvmYul.Operation.SELFDESTRUCT ∨
                op = EvmYul.Operation.LOG0 ∨
                  op = EvmYul.Operation.LOG1 ∨
                    op = EvmYul.Operation.LOG2 ∨
                      op = EvmYul.Operation.LOG3 ∨
                        op = EvmYul.Operation.LOG4 ∨
                          op = EvmYul.Operation.TSTORE) ∨
        op = EvmYul.Operation.CALL ∧
          ¬ state.stack[2]? = some (⟨0⟩ : Word))) := by
    simpa using hStatic
  have hCreate' : ¬ (op.isCreate = true ∧
      (⟨49152⟩ : Word) < state.stack[2]?.getD (⟨0⟩ : Word)) := by
    simpa using hCreate
  have hStep' :
      EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state op) }
            op)
          (some (op, arg))
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) } =
        .ok post := by
    simpa [memoryGasState] using hStep
  simp [EvmYul.EVM.X, hDecode, hChecks.memoryGas, hDynamic,
    hChecks.delta, hStack, hJump, hStackOverflow, hSstore] at hNoHalt ⊢
  rw [if_neg hJumpi]
  rw [if_neg hReturnData']
  rw [if_neg hStatic']
  rw [if_neg hCreate']
  change
    (do
      let evmState' ←
        EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            { state with
              gasAvailable :=
                state.gasAvailable -
                  EvmYul.UInt256.ofNat
                    (EvmYul.EVM.memoryExpansionCost state op) }
            op)
          (some (op, arg))
          { state with
            gasAvailable :=
              state.gasAvailable -
                EvmYul.UInt256.ofNat (EvmYul.EVM.memoryExpansionCost state op) }
      match
        if op = EvmYul.Operation.RETURN ∨ op = EvmYul.Operation.REVERT then
          some evmState'.H_return
        else if op = EvmYul.Operation.STOP ∨
            op = EvmYul.Operation.SELFDESTRUCT then
          some ByteArray.empty
        else
          none
      with
      | none => EvmYul.EVM.X fuel validJumps evmState'
      | some output =>
          if op = EvmYul.Operation.REVERT then
            .ok (EvmYul.EVM.ExecutionResult.revert evmState'.gasAvailable output)
          else
            .ok (EvmYul.EVM.ExecutionResult.success evmState' output)) =
      EvmYul.EVM.X fuel validJumps post
  rw [hStep']
  simp [XHaltOutput?] at hNoHalt
  change
    (match
        if op = EvmYul.Operation.RETURN ∨ op = EvmYul.Operation.REVERT then
          some post.H_return
        else if op = EvmYul.Operation.STOP ∨
            op = EvmYul.Operation.SELFDESTRUCT then
          some ByteArray.empty
        else
          none
      with
      | none => EvmYul.EVM.X fuel validJumps post
      | some output =>
          if op = EvmYul.Operation.REVERT then
            .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
          else
            .ok (EvmYul.EVM.ExecutionResult.success post output)) =
      EvmYul.EVM.X fuel validJumps post
  rw [hNoHalt]

theorem X_step_running_of_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hNoHalt : XHaltOutput? op post = none) :
    EvmYul.EVM.X fuel.succ validJumps state =
      EvmYul.EVM.X fuel validJumps post :=
  X_step_running_of_raw_checks hDecode
    (XStepRawChecksPass.of_step_checks hChecks) hStep hNoHalt

theorem X_step_success_of_raw_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hHalt : XHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.success post output) := by
  rw [X_step_expand_of_raw_checks hDecode hChecks, hStep]
  have hHalt' : XStepHaltOutput? op post = some output := by
    simpa [XHaltOutput?_eq_XStepHaltOutput?] using hHalt
  change
    (match XStepHaltOutput? op post with
    | none => EvmYul.EVM.X fuel validJumps post
    | some output =>
        if op = EvmYul.Operation.REVERT then
          .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
        else
          .ok (EvmYul.EVM.ExecutionResult.success post output)) =
      .ok (EvmYul.EVM.ExecutionResult.success post output)
  rw [hHalt']
  simp [hNotRevert]

theorem X_step_success_of_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hHalt : XHaltOutput? op post = some output)
    (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.success post output) :=
  X_step_success_of_raw_checks hDecode
    (XStepRawChecksPass.of_step_checks hChecks) hStep hHalt hNotRevert

theorem X_step_revert_of_raw_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepRawChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hHalt : XHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output) := by
  rw [X_step_expand_of_raw_checks hDecode hChecks, hStep]
  have hHalt' : XStepHaltOutput? op post = some output := by
    simpa [XHaltOutput?_eq_XStepHaltOutput?] using hHalt
  change
    (match XStepHaltOutput? op post with
    | none => EvmYul.EVM.X fuel validJumps post
    | some output =>
        if op = EvmYul.Operation.REVERT then
          .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
        else
          .ok (EvmYul.EVM.ExecutionResult.success post output)) =
      .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
  rw [hHalt']
  simp [hRevert]

theorem X_step_revert_of_checks {fuel : Nat} {validJumps : Array Word}
    {state post : EVMState} {op : EVMOp} {arg : Option (Word × Nat)}
    {output : ByteArray}
    (hDecode : EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
    (hChecks : XStepChecksPass validJumps state op)
    (hStep : EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
      (some (op, arg)) (memoryGasState state op) = .ok post)
    (hHalt : XHaltOutput? op post = some output)
    (hRevert : op = EvmYul.Operation.REVERT) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output) :=
  X_step_revert_of_raw_checks hDecode
    (XStepRawChecksPass.of_step_checks hChecks) hStep hHalt hRevert

theorem X_step_fallthrough_stop_success_of_raw_checks {fuel : Nat}
    {validJumps : Array Word} {state post : EVMState}
    {output : ByteArray}
    (hDecodeNone : EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hChecks :
      XStepRawChecksPass validJumps state EvmYul.Operation.STOP)
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C'
          (memoryGasState state EvmYul.Operation.STOP)
          EvmYul.Operation.STOP)
        (some (EvmYul.Operation.STOP, none))
        (memoryGasState state EvmYul.Operation.STOP) = .ok post)
    (hHalt : XHaltOutput? EvmYul.Operation.STOP post = some output) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.success post output) := by
  rw [X_step_expand_default_stop_of_raw_checks hDecodeNone hChecks, hStep]
  have hHalt' :
      XStepHaltOutput? EvmYul.Operation.STOP post = some output := by
    simpa [XHaltOutput?_eq_XStepHaltOutput?] using hHalt
  dsimp
  change
    (match XStepHaltOutput? EvmYul.Operation.STOP post with
    | none => EvmYul.EVM.X fuel validJumps post
    | some output =>
        .ok (EvmYul.EVM.ExecutionResult.success post output)) =
      .ok (EvmYul.EVM.ExecutionResult.success post output)
  rw [hHalt']

theorem X_step_fallthrough_stop_success_of_checks {fuel : Nat}
    {validJumps : Array Word} {state post : EVMState}
    {output : ByteArray}
    (hDecodeNone : EvmYul.EVM.decode state.executionEnv.code state.pc = none)
    (hChecks :
      XStepChecksPass validJumps state EvmYul.Operation.STOP)
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C'
          (memoryGasState state EvmYul.Operation.STOP)
          EvmYul.Operation.STOP)
        (some (EvmYul.Operation.STOP, none))
        (memoryGasState state EvmYul.Operation.STOP) = .ok post)
    (hHalt : XHaltOutput? EvmYul.Operation.STOP post = some output) :
    EvmYul.EVM.X fuel.succ validJumps state =
      .ok (EvmYul.EVM.ExecutionResult.success post output) :=
  X_step_fallthrough_stop_success_of_raw_checks hDecodeNone
    (XStepRawChecksPass.of_step_checks hChecks) hStep hHalt

inductive XStepTrace (validJumps : Array Word) :
    Nat → EVMState → EvmYul.EVM.ExecutionResult EVMState → Prop where
  | success {fuel : Nat} {state post : EVMState} {op : EVMOp}
      {arg : Option (Word × Nat)} {output : ByteArray}
      (hDecode :
        EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
      (hChecks : XStepChecksPass validJumps state op)
      (hStep :
        EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
          (some (op, arg)) (memoryGasState state op) = .ok post)
      (hHalt : XHaltOutput? op post = some output)
      (hNotRevert : op ≠ EvmYul.Operation.REVERT) :
      XStepTrace validJumps fuel.succ state
        (EvmYul.EVM.ExecutionResult.success post output)
  | revert {fuel : Nat} {state post : EVMState} {op : EVMOp}
      {arg : Option (Word × Nat)} {output : ByteArray}
      (hDecode :
        EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
      (hChecks : XStepChecksPass validJumps state op)
      (hStep :
        EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
          (some (op, arg)) (memoryGasState state op) = .ok post)
      (hHalt : XHaltOutput? op post = some output)
      (hRevert : op = EvmYul.Operation.REVERT) :
      XStepTrace validJumps fuel.succ state
        (EvmYul.EVM.ExecutionResult.revert post.gasAvailable output)
  | running {fuel : Nat} {state post : EVMState} {op : EVMOp}
      {arg : Option (Word × Nat)}
      {result : EvmYul.EVM.ExecutionResult EVMState}
      (hDecode :
        EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
      (hChecks : XStepChecksPass validJumps state op)
      (hStep :
        EvmYul.EVM.step fuel (EvmYul.EVM.C' (memoryGasState state op) op)
          (some (op, arg)) (memoryGasState state op) = .ok post)
      (hNoHalt : XHaltOutput? op post = none)
      (hRest : XStepTrace validJumps fuel post result) :
      XStepTrace validJumps fuel.succ state result
  | fallthroughStop {fuel : Nat} {state post : EVMState}
      {output : ByteArray}
      (hDecodeNone :
        EvmYul.EVM.decode state.executionEnv.code state.pc = none)
      (hChecks : XStepChecksPass validJumps state EvmYul.Operation.STOP)
      (hStep :
        EvmYul.EVM.step fuel
          (EvmYul.EVM.C'
            (memoryGasState state EvmYul.Operation.STOP)
            EvmYul.Operation.STOP)
          (some (EvmYul.Operation.STOP, none))
          (memoryGasState state EvmYul.Operation.STOP) = .ok post)
      (hHalt : XHaltOutput? EvmYul.Operation.STOP post = some output) :
      XStepTrace validJumps fuel.succ state
        (EvmYul.EVM.ExecutionResult.success post output)

namespace XStepTrace

theorem run {validJumps : Array Word} {fuel : Nat} {state : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hTrace : XStepTrace validJumps fuel state result) :
    EvmYul.EVM.X fuel validJumps state = .ok result := by
  induction hTrace with
  | success hDecode hChecks hStep hHalt hNotRevert =>
      exact X_step_success_of_checks hDecode hChecks hStep hHalt hNotRevert
  | revert hDecode hChecks hStep hHalt hRevert =>
      exact X_step_revert_of_checks hDecode hChecks hStep hHalt hRevert
  | running hDecode hChecks hStep hNoHalt _ ih =>
      rw [X_step_running_of_checks hDecode hChecks hStep hNoHalt]
      exact ih
  | fallthroughStop hDecodeNone hChecks hStep hHalt =>
      exact X_step_fallthrough_stop_success_of_checks
        hDecodeNone hChecks hStep hHalt

inductive XPrefixTrace (validJumps : Array Word) :
    Nat → EVMState → EVMState → Prop where
  | done (state : EVMState) :
      XPrefixTrace validJumps 0 state state
  | running {fuel : Nat} {state post final : EVMState} {op : EVMOp}
      {arg : Option (Word × Nat)}
      (hDecode :
        EvmYul.EVM.decode state.executionEnv.code state.pc = some (op, arg))
      (hChecks : XStepChecksPass validJumps state op)
      (hStep :
        ∀ tailFuel : Nat,
          EvmYul.EVM.step tailFuel.succ
            (EvmYul.EVM.C' (memoryGasState state op) op)
            (some (op, arg)) (memoryGasState state op) = .ok post)
      (hNoHalt : XHaltOutput? op post = none)
      (hRest : XPrefixTrace validJumps fuel post final) :
      XPrefixTrace validJumps fuel.succ state final

theorem XPrefixTrace.then_stepTrace {validJumps : Array Word}
    {prefixFuel restFuel : Nat} {state mid : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hPrefix : XPrefixTrace validJumps prefixFuel state mid)
    (hRest : XStepTrace validJumps restFuel.succ mid result) :
    ∃ fuel : Nat,
      XStepTrace validJumps fuel.succ state result := by
  induction hPrefix generalizing restFuel result with
  | done state =>
      exact ⟨restFuel, hRest⟩
  | running hDecode hChecks hStep hNoHalt _ ih =>
      obtain ⟨fuel, hTrace⟩ := ih hRest
      exact
        ⟨fuel.succ,
          XStepTrace.running hDecode hChecks (hStep fuel) hNoHalt
            hTrace⟩

theorem targetInstr_running
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full fullPost target targetPost : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.running targetPost))
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
        (some (instr.op, instr.arg)) (memoryGasState full instr.op) =
          .ok fullPost)
    (hNoHalt : XHaltOutput? instr.op fullPost = none)
    (hRest : XStepTrace validJumps fuel fullPost result) :
    GasExecRel fullPost targetPost ∧
      XStepTrace validJumps fuel.succ full result := by
  obtain ⟨hTargetStep, hKind⟩ :=
    Target.stepInstrResult_running_stepInstr hTarget
  have hRelPost :
      GasExecRel fullPost targetPost :=
    EVM_step_targetInstr_preserves_gasExecRel_of_ok
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep hStep
  exact
    ⟨hRelPost,
      XStepTrace.running hDecode hChecks hStep hNoHalt hRest⟩

theorem targetInstr_success
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full fullPost target : EVMState} {halt : Halt}
    {output : ByteArray}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
        (some (instr.op, instr.arg)) (memoryGasState full instr.op) =
          .ok fullPost)
    (hHalt : XHaltOutput? instr.op fullPost = some output)
    (hNotRevert : instr.op ≠ EvmYul.Operation.REVERT) :
    GasExecRel fullPost halt.state ∧
      XStepTrace validJumps fuel.succ full
        (.success fullPost output) := by
  obtain ⟨hTargetStep, _hKind, _hOutputKind⟩ :=
    Target.stepInstrResult_halted_stepInstr hTarget
  have hRelPost :
      GasExecRel fullPost halt.state :=
    EVM_step_targetInstr_preserves_gasExecRel_of_ok
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep hStep
  exact
    ⟨hRelPost,
      XStepTrace.success hDecode hChecks hStep hHalt hNotRevert⟩

theorem targetInstr_revert
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full fullPost target : EVMState} {halt : Halt}
    {output : ByteArray}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hStep :
      EvmYul.EVM.step fuel
        (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
        (some (instr.op, instr.arg)) (memoryGasState full instr.op) =
          .ok fullPost)
    (hHalt : XHaltOutput? instr.op fullPost = some output)
    (hRevert : instr.op = EvmYul.Operation.REVERT) :
    GasExecRel fullPost halt.state ∧
      XStepTrace validJumps fuel.succ full
        (.revert fullPost.gasAvailable output) := by
  obtain ⟨hTargetStep, _hKind, _hOutputKind⟩ :=
    Target.stepInstrResult_halted_stepInstr hTarget
  have hRelPost :
      GasExecRel fullPost halt.state :=
    EVM_step_targetInstr_preserves_gasExecRel_of_ok
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep hStep
  exact
    ⟨hRelPost,
      XStepTrace.revert hDecode hChecks hStep hHalt hRevert⟩

theorem targetInstr_running_exists
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target targetPost : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.running targetPost))
    (hRest :
      ∀ fullPost,
        GasExecRel fullPost targetPost →
          XStepTrace validJumps fuel.succ fullPost result) :
    ∃ fullPost,
      GasExecRel fullPost targetPost ∧
        XStepTrace validJumps fuel.succ.succ full result := by
  obtain ⟨hTargetStep, hKind⟩ :=
    Target.stepInstrResult_running_stepInstr hTarget
  obtain ⟨fullPost, hStep, hRelPost⟩ :=
    EVM_step_targetInstr_exists_gasExecRel
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep
  have hNoHalt : XHaltOutput? instr.op fullPost = none :=
    XHaltOutput?_none_of_targetInstr_haltKind_none hKind
  exact
    ⟨fullPost, hRelPost,
      XStepTrace.running hDecode hChecks hStep hNoHalt
        (hRest fullPost hRelPost)⟩

theorem targetInstr_success_exists
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hNotRevert : halt.kind ≠ .revert) :
    ∃ fullPost,
      GasExecRel fullPost halt.state ∧
        XStepTrace validJumps fuel.succ.succ full
          (.success fullPost halt.output) := by
  obtain ⟨hTargetStep, hKind, hOutput⟩ :=
    Target.stepInstrResult_halted_stepInstr hTarget
  obtain ⟨fullPost, hStep, hRelPost⟩ :=
    EVM_step_targetInstr_exists_gasExecRel
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep
  have hHalt : XHaltOutput? instr.op fullPost = some halt.output := by
    have hHaltFull :=
      XHaltOutput?_some_of_targetInstr_haltKind_some
        (instr := instr) (state := fullPost) hKind
    rw [HaltKind.output_eq_of_gasExecRel halt.kind hRelPost, ← hOutput] at hHaltFull
    exact hHaltFull
  have hNotRevertOp : instr.op ≠ EvmYul.Operation.REVERT :=
    targetInstr_op_ne_revert_of_haltKind_some_ne hKind hNotRevert
  exact
    ⟨fullPost, hRelPost,
      XStepTrace.success hDecode hChecks hStep hHalt hNotRevertOp⟩

theorem targetInstr_revert_exists
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hRevert : halt.kind = .revert) :
    ∃ fullPost,
      GasExecRel fullPost halt.state ∧
        XStepTrace validJumps fuel.succ.succ full
          (.revert fullPost.gasAvailable halt.output) := by
  obtain ⟨hTargetStep, hKind, hOutput⟩ :=
    Target.stepInstrResult_halted_stepInstr hTarget
  obtain ⟨fullPost, hStep, hRelPost⟩ :=
    EVM_step_targetInstr_exists_gasExecRel
      (fuel := fuel)
      (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
      hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
      hTargetStep
  have hHalt : XHaltOutput? instr.op fullPost = some halt.output := by
    have hHaltFull :=
      XHaltOutput?_some_of_targetInstr_haltKind_some
        (instr := instr) (state := fullPost) hKind
    rw [HaltKind.output_eq_of_gasExecRel halt.kind hRelPost, ← hOutput] at hHaltFull
    exact hHaltFull
  have hRevertOp : instr.op = EvmYul.Operation.REVERT := by
    exact targetInstr_op_eq_revert_of_haltKind_revert (by simpa [hRevert] using hKind)
  exact
    ⟨fullPost, hRelPost,
      XStepTrace.revert hDecode hChecks hStep hHalt hRevertOp⟩

end XStepTrace

/--
Successful `X` results preserve the same non-gas final state as the gasless
source run.  Revert needs a separate output/projection theorem because
EVMYulLean's `ExecutionResult.revert` does not carry the final `EVM.State`.
-/
def XSuccessErasesTo (sourceFinal : EVMState) :
    EvmYul.EVM.ExecutionResult EVMState → Prop
  | .success evmFinal _output => eraseGas evmFinal = eraseGas sourceFinal
  | .revert _gas _output => False

def XRunsSuccessfullyAbove (target : TargetProgram) (initial sourceFinal : EVMState)
    (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      gas < EvmYul.UInt256.size →
        ∃ result,
          EvmYul.EVM.X evmFuel (validJumps target)
              (installCodeAndGas target gas initial) =
            .ok result ∧
            XSuccessErasesTo sourceFinal result

/--
Result-level agreement for the gas-aware `X` runner.

The running case compares gas-erased states and requires the eventual EVM
success output to be empty, matching ordinary non-terminal completion as seen by
message-call return data. Terminal success compares both the gas-erased halted
state and output. Revert in EVMYulLean does not carry the final state, so the
result-level contract compares the revert output and halt kind only.
-/
def XResultAgrees (targetResult : StepResult) :
    EvmYul.EVM.ExecutionResult EVMState → Prop
  | .success evmFinal output =>
      match targetResult with
      | .running state =>
          eraseGas evmFinal = eraseGas state ∧ output = ByteArray.empty
      | .halted halt =>
          halt.kind ≠ .revert ∧
            eraseGas evmFinal = eraseGas halt.state ∧
              output = halt.output
  | .revert _gas output =>
      match targetResult with
      | .running _ => False
      | .halted halt => halt.kind = .revert ∧ output = halt.output

/--
Final committed-result observation for gas-aware execution.

Successful execution observes the persistent/shared EVM state and return
output. Reverts reset state, so the committed observation records only their
caller-visible output bytes. Remaining gas is still deliberately outside this
observation: low-gas safety is about final effects, not refund exactness.
-/
inductive XCommittedObservation where
  | committed (state : EvmYul.State .EVM) (output : ByteArray)
  | reverted (output : ByteArray)

def XTargetCommittedObservation : StepResult → XCommittedObservation
  | .running state => .committed state.toState ByteArray.empty
  | .halted halt =>
      match halt.kind with
      | .revert => .reverted halt.output
      | .stop => .committed halt.state.toState halt.output
      | .return => .committed halt.state.toState halt.output
      | .selfdestruct => .committed halt.state.toState halt.output

def XResultCommittedObservation :
    EvmYul.EVM.ExecutionResult EVMState → XCommittedObservation
  | .success state output => .committed state.toState output
  | .revert _gas output => .reverted output

def XRunOutcomeFails :
    Except EVMException (EvmYul.EVM.ExecutionResult EVMState) → Prop
  | .error EvmYul.EVM.ExecutionException.OutOfGass => True
  | _ => False

def XRunOutcomeCommitsTo
    (outcome : Except EVMException (EvmYul.EVM.ExecutionResult EVMState))
    (observation : XCommittedObservation) : Prop :=
  match outcome with
  | .ok (.success state output) =>
      observation = .committed state.toState output
  | .ok (.revert _gas output) =>
      observation = .reverted output
  | _ => False

namespace XRunOutcomeCommitsTo

theorem ok_result_observation
    {result : EvmYul.EVM.ExecutionResult EVMState}
    {observation : XCommittedObservation}
    (hCommit : XRunOutcomeCommitsTo (.ok result) observation) :
    observation = XResultCommittedObservation result := by
  cases result with
  | success state output =>
      simpa [XRunOutcomeCommitsTo, XResultCommittedObservation] using hCommit
  | revert gas output =>
      simpa [XRunOutcomeCommitsTo, XResultCommittedObservation] using hCommit

end XRunOutcomeCommitsTo

def XRunOutcomeSafelyMatches (targetResult : StepResult)
    (outcome : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)) :
    Prop :=
  (∃ result,
      outcome = .ok result ∧
        XResultCommittedObservation result =
          XTargetCommittedObservation targetResult) ∨
    XRunOutcomeFails outcome

namespace XRunOutcomeCommitsTo

theorem outcomeSafelyMatches
    {targetResult : StepResult}
    {outcome : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {observation : XCommittedObservation}
    (hCommit : XRunOutcomeCommitsTo outcome observation)
    (hObservation :
      observation = XTargetCommittedObservation targetResult) :
    XRunOutcomeSafelyMatches targetResult outcome := by
  cases outcome with
  | ok result =>
      cases result with
      | success state output =>
          refine Or.inl ⟨.success state output, rfl, ?_⟩
          simpa [XRunOutcomeCommitsTo, XResultCommittedObservation]
            using hCommit.symm.trans hObservation
      | revert gas output =>
          refine Or.inl ⟨.revert gas output, rfl, ?_⟩
          simpa [XRunOutcomeCommitsTo, XResultCommittedObservation]
            using hCommit.symm.trans hObservation
  | error err =>
      simp [XRunOutcomeCommitsTo] at hCommit

end XRunOutcomeCommitsTo

def XRunOutcomesSafeEquivalent
    (left right :
      Except EVMException (EvmYul.EVM.ExecutionResult EVMState)) : Prop :=
  (∃ observation,
      XRunOutcomeCommitsTo left observation ∧
        XRunOutcomeCommitsTo right observation) ∨
    XRunOutcomeFails left ∨
      XRunOutcomeFails right

/--
Directional committed-observation tracking.

`candidate` is safe relative to `reference` when the candidate either fails
(including out-of-gas) or, if it commits, commits to the same observation as the
reference.  Unlike `XRunOutcomesSafeEquivalent`, failure of the reference alone
does not make an arbitrary candidate safe. This is the useful low-gas proof
shape: the low-gas run may fail, but any low-gas commit must track the
high-gas/reference commit.
-/
def XRunOutcomeSafelyTracks
    (candidate reference :
      Except EVMException (EvmYul.EVM.ExecutionResult EVMState)) : Prop :=
  (∃ observation,
      XRunOutcomeCommitsTo candidate observation ∧
        XRunOutcomeCommitsTo reference observation) ∨
    XRunOutcomeFails candidate

namespace XRunOutcomeSafelyTracks

theorem of_candidate_fails
    {candidate reference :
      Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    (hFails : XRunOutcomeFails candidate) :
    XRunOutcomeSafelyTracks candidate reference :=
  Or.inr hFails

theorem ok_refl (result : EvmYul.EVM.ExecutionResult EVMState) :
    XRunOutcomeSafelyTracks (.ok result) (.ok result) := by
  cases result with
  | success state output =>
      exact
        Or.inl
          ⟨.committed state.toState output,
            by simp [XRunOutcomeCommitsTo],
            by simp [XRunOutcomeCommitsTo]⟩
  | revert gas output =>
      exact
        Or.inl
          ⟨.reverted output,
            by simp [XRunOutcomeCommitsTo],
            by simp [XRunOutcomeCommitsTo]⟩

theorem retarget_ok
    {candidate : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {left right : EvmYul.EVM.ExecutionResult EVMState}
    (hTracks : XRunOutcomeSafelyTracks candidate (.ok left))
    (hObservation :
      XResultCommittedObservation left =
        XResultCommittedObservation right) :
    XRunOutcomeSafelyTracks candidate (.ok right) := by
  rcases hTracks with hCommit | hFails
  · rcases hCommit with ⟨observation, hCandidate, hLeft⟩
    cases left with
    | success leftState leftOutput =>
        cases right with
        | success rightState rightOutput =>
            exact
              Or.inl
                ⟨observation, hCandidate, by
                  simp [XRunOutcomeCommitsTo,
                    XResultCommittedObservation] at hLeft hObservation ⊢
                  rcases hObservation with ⟨hState, hOutput⟩
                  rw [← hState, ← hOutput]
                  exact hLeft⟩
        | revert gas output =>
            cases hObservation
    | revert gas output =>
        cases right with
        | success rightState rightOutput =>
            cases hObservation
        | revert rightGas rightOutput =>
            exact
              Or.inl
                ⟨observation, hCandidate, by
                  simpa [XRunOutcomeCommitsTo, XResultCommittedObservation]
                    using hLeft.trans hObservation⟩
  · exact Or.inr hFails

theorem outcomeSafelyMatches_of_result
    {targetResult : StepResult}
    {candidate : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {reference : EvmYul.EVM.ExecutionResult EVMState}
    (hTracks : XRunOutcomeSafelyTracks candidate (.ok reference))
    (hReference :
      XResultCommittedObservation reference =
        XTargetCommittedObservation targetResult) :
    XRunOutcomeSafelyMatches targetResult candidate := by
  rcases hTracks with hCommit | hFails
  · rcases hCommit with ⟨observation, hCandidate, hReferenceCommit⟩
    exact
      XRunOutcomeCommitsTo.outcomeSafelyMatches hCandidate
        ((XRunOutcomeCommitsTo.ok_result_observation hReferenceCommit).trans
          hReference)
  · exact Or.inr hFails

end XRunOutcomeSafelyTracks

theorem eraseGas_toState (state : EVMState) :
    (eraseGas state).toState = state.toState := by
  rfl

theorem XResultAgrees.committedObservation
    {targetResult : StepResult}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hAgree : XResultAgrees targetResult result) :
    XResultCommittedObservation result =
      XTargetCommittedObservation targetResult := by
  cases result with
  | success evmFinal output =>
      cases targetResult with
      | running state =>
          rcases hAgree with ⟨hState, hOutput⟩
          cases hOutput
          have hToState :
              evmFinal.toState = state.toState := by
            calc
              evmFinal.toState = (eraseGas evmFinal).toState := by
                rw [eraseGas_toState]
              _ = (eraseGas state).toState := by
                rw [hState]
              _ = state.toState := eraseGas_toState state
          simp [XResultCommittedObservation, XTargetCommittedObservation,
            hToState]
      | halted halt =>
          rcases hAgree with ⟨hKind, hState, hOutput⟩
          cases hOutput
          rcases halt with ⟨kind, state, haltOutput⟩
          have hToState :
              evmFinal.toState = state.toState := by
            calc
              evmFinal.toState = (eraseGas evmFinal).toState := by
                rw [eraseGas_toState]
              _ = (eraseGas state).toState := by
                rw [hState]
              _ = state.toState := eraseGas_toState state
          cases kind <;>
            simp [XResultCommittedObservation, XTargetCommittedObservation,
              hToState] at hKind ⊢
  | revert gas output =>
      cases targetResult with
      | running state =>
          cases hAgree
      | halted halt =>
          rcases hAgree with ⟨hKind, hOutput⟩
          rcases halt with ⟨kind, state, haltOutput⟩
          cases kind <;>
            simp [XResultCommittedObservation, XTargetCommittedObservation]
              at hKind hOutput ⊢
          exact hOutput

theorem XResultAgrees.outcomeSafelyMatches
    {targetResult : StepResult}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    (hAgree : XResultAgrees targetResult result) :
    XRunOutcomeSafelyMatches targetResult (.ok result) :=
  Or.inl ⟨result, rfl, hAgree.committedObservation⟩

theorem XResultAgrees_running_success_of_gasExecRel
    {full target : EVMState}
    (hRel : GasExecRel full target) :
    XResultAgrees (.running target)
      (.success full ByteArray.empty) := by
  exact ⟨hRel.eraseGas_eq, rfl⟩

theorem XResultAgrees_halted_success_of_gasExecRel
    {full : EVMState} {halt : Halt} {output : ByteArray}
    (hKind : halt.kind ≠ .revert)
    (hRel : GasExecRel full halt.state)
    (hOutput : output = halt.output) :
    XResultAgrees (.halted halt) (.success full output) := by
  exact ⟨hKind, hRel.eraseGas_eq, hOutput⟩

theorem XResultAgrees_halted_revert
    {halt : Halt} {gas : Word} {output : ByteArray}
    (hKind : halt.kind = .revert)
    (hOutput : output = halt.output) :
    XResultAgrees (.halted halt) (.revert gas output) := by
  exact ⟨hKind, hOutput⟩

namespace XStepTrace

theorem targetInstr_running_exists_agrees
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target targetPost : EVMState}
    {result : EvmYul.EVM.ExecutionResult EVMState}
    {targetResult : StepResult}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.running targetPost))
    (hRest :
      ∀ fullPost,
        GasExecRel fullPost targetPost →
          XStepTrace validJumps fuel.succ fullPost result)
    (hAgree :
      ∀ fullPost,
        GasExecRel fullPost targetPost →
          XResultAgrees targetResult result) :
    ∃ fullPost,
      GasExecRel fullPost targetPost ∧
        XStepTrace validJumps fuel.succ.succ full result ∧
          XResultAgrees targetResult result := by
  obtain ⟨fullPost, hRelPost, hTrace⟩ :=
    targetInstr_running_exists
      (fuel := fuel)
      (instr := instr)
      (full := full)
      (target := target)
      (targetPost := targetPost)
      (result := result)
      hNoCallCreate hRel hDecode hChecks hTarget hRest
  exact ⟨fullPost, hRelPost, hTrace, hAgree fullPost hRelPost⟩

theorem targetInstr_success_exists_agrees
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hNotRevert : halt.kind ≠ .revert) :
    ∃ fullPost,
      GasExecRel fullPost halt.state ∧
        XStepTrace validJumps fuel.succ.succ full
          (.success fullPost halt.output) ∧
          XResultAgrees (.halted halt) (.success fullPost halt.output) := by
  obtain ⟨fullPost, hRelPost, hTrace⟩ :=
    targetInstr_success_exists
      (fuel := fuel)
      (instr := instr)
      (full := full)
      (target := target)
      (halt := halt)
      hNoCallCreate hRel hDecode hChecks hTarget hNotRevert
  exact
    ⟨fullPost, hRelPost, hTrace,
      XResultAgrees_halted_success_of_gasExecRel
        hNotRevert hRelPost rfl⟩

theorem targetInstr_revert_exists_agrees
    {validJumps : Array Word} {fuel : Nat}
    {instr : TargetInstr}
    {full target : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hTarget :
      Target.stepInstrResult instr target = .ok (.halted halt))
    (hRevert : halt.kind = .revert) :
    ∃ fullPost,
      GasExecRel fullPost halt.state ∧
        XStepTrace validJumps fuel.succ.succ full
          (.revert fullPost.gasAvailable halt.output) ∧
          XResultAgrees (.halted halt)
            (.revert fullPost.gasAvailable halt.output) := by
  obtain ⟨fullPost, hRelPost, hTrace⟩ :=
    targetInstr_revert_exists
      (fuel := fuel)
      (instr := instr)
      (full := full)
      (target := target)
      (halt := halt)
      hNoCallCreate hRel hDecode hChecks hTarget hRevert
  exact
    ⟨fullPost, hRelPost, hTrace,
      XResultAgrees_halted_revert hRevert rfl⟩

theorem runListResult_cons_exists_agrees
    {validJumps : Array Word}
    {instr : TargetInstr} {rest : List TargetInstr}
    {full target : EVMState} {targetResult : StepResult}
    (hRun :
      Target.runListResult (instr :: rest) target = .ok targetResult)
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hRel : GasExecRel full target)
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hChecks : XStepChecksPass validJumps full instr.op)
    (hContinue :
      ∀ targetPost,
        Target.stepInstrResult instr target = .ok (.running targetPost) →
          Target.runListResult rest targetPost = .ok targetResult →
            ∃ fuel : Nat,
              ∀ fullPost,
                GasExecRel fullPost targetPost →
                  ∃ evmResult,
                    XStepTrace validJumps fuel.succ fullPost evmResult ∧
                      XResultAgrees targetResult evmResult) :
    ∃ fuel : Nat, ∃ evmResult,
      XStepTrace validJumps fuel.succ full evmResult ∧
        XResultAgrees targetResult evmResult := by
  rcases Target.runListResult_cons_ok_cases hRun with
    ⟨targetPost, hStepResult, hRunRest⟩ | ⟨halt, hStepResult, hResult⟩
  · obtain ⟨hTargetStep, hKind⟩ :=
      Target.stepInstrResult_running_stepInstr hStepResult
    obtain ⟨fuelRest, hContinueAtFuel⟩ :=
      hContinue targetPost hStepResult hRunRest
    obtain ⟨fullPost, hStep, hRelPost⟩ :=
      EVM_step_targetInstr_exists_gasExecRel
        (fuel := fuelRest)
        (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
        hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
        hTargetStep
    obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
      hContinueAtFuel fullPost hRelPost
    have hNoHalt : XHaltOutput? instr.op fullPost = none :=
      XHaltOutput?_none_of_targetInstr_haltKind_none hKind
    exact
      ⟨fuelRest.succ, evmResult,
        XStepTrace.running hDecode hChecks hStep hNoHalt hRestTrace,
        hAgree⟩
  · subst targetResult
    by_cases hRevert : halt.kind = .revert
    · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
        targetInstr_revert_exists_agrees
          (fuel := 0)
          (instr := instr)
          (full := full)
          (target := target)
          (halt := halt)
          hNoCallCreate hRel hDecode hChecks hStepResult hRevert
      exact ⟨1, .revert fullPost.gasAvailable halt.output, hTrace, hAgree⟩
    · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
        targetInstr_success_exists_agrees
          (fuel := 0)
          (instr := instr)
          (full := full)
          (target := target)
          (halt := halt)
          hNoCallCreate hRel hDecode hChecks hStepResult hRevert
      exact ⟨1, .success fullPost halt.output, hTrace, hAgree⟩

def XRunListSuffixReady (validJumps : Array Word)
    (code : List TargetInstr) : Prop :=
  ∀ {instr : TargetInstr} {rest : List TargetInstr}
      {targetState : EVMState} {blockResult : StepResult},
    (∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) →
      Target.runListResult (instr :: rest) targetState = .ok blockResult →
        ∀ {fullState : EVMState},
          GasExecRel fullState targetState →
            EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
                some (instr.op, instr.arg) ∧
              XNonGasChecksPass validJumps fullState instr.op ∧
                XGasRequiredAt fullState instr.op ≤
                  fullState.gasAvailable.toNat ∧
                  targetInstrUsesCallCreate instr = false

def XRunListSuffixNonGasReady (validJumps : Array Word)
    (code : List TargetInstr) : Prop :=
  ∀ {instr : TargetInstr} {rest : List TargetInstr}
      {targetState : EVMState} {blockResult : StepResult},
    (∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) →
      Target.runListResult (instr :: rest) targetState = .ok blockResult →
        ∀ {fullState : EVMState},
          GasExecRel fullState targetState →
            EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
                some (instr.op, instr.arg) ∧
              XNonGasChecksPass validJumps fullState instr.op ∧
                targetInstrUsesCallCreate instr = false

def XRunListSuffixCoreNonGasReady (validJumps : Array Word)
    (code : List TargetInstr) : Prop :=
  ∀ {instr : TargetInstr} {rest : List TargetInstr}
      {targetState : EVMState} {blockResult : StepResult},
    (∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) →
      Target.runListResult (instr :: rest) targetState = .ok blockResult →
        ∀ {fullState : EVMState},
          GasExecRel fullState targetState →
            XNonGasCoreChecksPass validJumps fullState instr.op

def XRunListSuffixCoreInputsReady (validJumps : Array Word)
    (code : List TargetInstr) : Prop :=
  ∀ {instr : TargetInstr} {rest : List TargetInstr}
      {targetState : EVMState} {blockResult : StepResult},
      (∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) →
      Target.runListResult (instr :: rest) targetState = .ok blockResult →
        ∀ {fullState : EVMState},
          GasExecRel fullState targetState →
            XCoreStackAndJumpInputsReady validJumps fullState instr.op ∧
              fullState.stack.length -
                    (EvmYul.EVM.δ instr.op).getD 0 +
                  (EvmYul.EVM.α instr.op).getD 0 ≤ 1024 ∧
                (fullState.executionEnv.perm = false →
                  ¬ staticWriteSensitive instr.op fullState.stack)

theorem XRunListSuffixCoreNonGasReady.of_inputs
    {validJumps : Array Word} {code : List TargetInstr}
    (hInputs : XRunListSuffixCoreInputsReady validJumps code) :
    XRunListSuffixCoreNonGasReady validJumps code := by
  intro instr rest targetState blockResult hSuffix hRun fullState hRel
  rcases hInputs hSuffix hRun hRel with
    ⟨hStepInputs, hOverflow, hStatic⟩
  exact
    XNonGasCoreChecksPass.of_inputs_overflow_static
      hStepInputs hOverflow hStatic

def XRunListSuffixGasReady (code : List TargetInstr) : Prop :=
  ∀ {instr : TargetInstr} {rest : List TargetInstr}
      {targetState : EVMState} {blockResult : StepResult},
    (∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) →
      Target.runListResult (instr :: rest) targetState = .ok blockResult →
        ∀ {fullState : EVMState},
          GasExecRel fullState targetState →
            XGasRequiredAt fullState instr.op ≤
              fullState.gasAvailable.toNat

def PrimStepPreservesCode : PrimStep → Prop
  | .unaryState f =>
      ∀ state arg, (f state arg).1.executionEnv.code =
        state.executionEnv.code
  | .binaryState f =>
      ∀ state left right, (f state left right).executionEnv.code =
        state.executionEnv.code
  | .ternaryCopy f =>
      ∀ shared a b c, (f shared a b c).executionEnv.code =
        shared.executionEnv.code
  | .quaternaryCopy f =>
      ∀ shared a b c d, (f shared a b c d).executionEnv.code =
        shared.executionEnv.code
  | _ => True

theorem State_sstore_preserves_code
    (state : EvmYul.State EvmYul.OperationType.EVM) (left right : Word) :
    (EvmYul.State.sstore state left right).executionEnv.code =
      state.executionEnv.code := by
  simp [EvmYul.State.sstore, EvmYul.State.setAccount,
    EvmYul.State.addAccessedStorageKey, EvmYul.State.lookupAccount]
  cases hAcc :
      Batteries.RBMap.find? state.accountMap state.executionEnv.codeOwner <;>
    rfl

theorem State_tstore_preserves_code
    (state : EvmYul.State EvmYul.OperationType.EVM) (left right : Word) :
    (EvmYul.State.tstore state left right).executionEnv.code =
      state.executionEnv.code := by
  simp [EvmYul.State.tstore, EvmYul.State.updateAccount,
    EvmYul.State.lookupAccount]
  cases hAcc :
      Batteries.RBMap.find? state.accountMap state.executionEnv.codeOwner <;>
    rfl

theorem PrimStepPreservesCode.of_continuingStep
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    PrimStepPreservesCode step := by
  cases op <;> simp [PrimOp.continuingStep?] at hStep <;>
    subst step <;>
    simp [PrimStepPreservesCode, State_sstore_preserves_code,
      State_tstore_preserves_code, EvmYul.State.balance,
      EvmYul.State.sload, EvmYul.State.tload, EvmYul.State.extCodeSize,
      EvmYul.State.extCodeHash, EvmYul.State.addAccessedAccount,
      EvmYul.State.addAccessedStorageKey, EvmYul.State.lookupAccount,
      EvmYul.SharedState.calldatacopy, EvmYul.SharedState.codeCopy,
      EvmYul.SharedState.extCodeCopy'] <;>
    intros <;>
    repeat split <;>
    simp

theorem PrimStep.run_preserves_code
    {step : PrimStep} {state post : EVMState}
    (hPreserve : PrimStepPreservesCode step)
    (hRun : step.run state = .ok post) :
    post.executionEnv.code = state.executionEnv.code := by
  cases step with
  | bin f =>
      cases hPop : state.stack.pop2 with
      | none => simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | un f =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | tri f =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | executionEnv f =>
      simp [PrimStep.run, EvmYul.EVM.executionEnvOp, Id.run] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | unaryExecutionEnv f =>
      cases hPop : state.stack.pop with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | machineState f =>
      simp [PrimStep.run, EvmYul.EVM.machineStateOp, Id.run] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | binaryMachineState f =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | binaryMachineStateWithResult f =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | ternaryMachineState f =>
      cases hPop : state.stack.pop3 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | state f =>
      simp [PrimStep.run, EvmYul.EVM.stateOp, Id.run] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | unaryState f =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hRun
          cases hRun
          simp [PrimStepPreservesCode] at hPreserve
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, hPreserve]
  | binaryState f =>
      cases hPop : state.stack.pop2 with
      | none => simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hRun
          cases hRun
          simp [PrimStepPreservesCode] at hPreserve
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, hPreserve]
  | ternaryCopy f =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hRun
          cases hRun
          simp [PrimStepPreservesCode] at hPreserve
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, hPreserve]
  | quaternaryCopy f =>
      cases hPop : state.stack.pop4 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d⟩
          simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hRun
          cases hRun
          simp [PrimStepPreservesCode] at hPreserve
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, hPreserve]
  | pop =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | mload =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, offset⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | returndatacopy =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, hPop] at hRun
          by_cases hBounds : state.returnData.size < b.toNat + c.toNat
          · simp [hBounds] at hRun
          · simp [hBounds] at hRun
            cases hRun
            simp [EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | dup n =>
      by_cases hLen : n ≤ state.stack.length
      · simp [PrimStep.run, EvmYul.dup, hLen] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · simp [PrimStep.run, EvmYul.dup, hLen] at hRun
  | swap n =>
      by_cases hLen : n + 1 ≤ state.stack.length
      · simp [PrimStep.run, EvmYul.swap, hLen] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · simp [PrimStep.run, EvmYul.swap, hLen] at hRun
  | log0 =>
      cases hPop : state.stack.pop2 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log1 =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log2 =>
      cases hPop : state.stack.pop4 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log3 =>
      cases hPop : state.stack.pop5 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d, e⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log4 =>
      cases hPop : state.stack.pop6 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d, e, f⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | invalid =>
      simp [PrimStep.run] at hRun

theorem PrimOp.step_preserves_code_of_no_call_create
    {op : PrimOp} {state post : EVMState}
    (hNoCallCreate : op.isCallCreate = false)
    (hRun : op.step state = .ok post) :
    post.executionEnv.code = state.executionEnv.code := by
  unfold PrimOp.step at hRun
  cases hStep : op.continuingStep? with
  | some step =>
      simp [hStep] at hRun
      exact
        PrimStep.run_preserves_code
          (PrimStepPreservesCode.of_continuingStep hStep) hRun
  | none =>
      simp [hStep] at hRun
      cases op <;>
        simp [PrimOp.continuingStep?, PrimOp.isCallCreate, PrimOp.toEVM] at hStep hNoCallCreate hRun
      · have hStop :
            EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none state =
              .ok
                { state with
                  toMachineState :=
                    (state.toMachineState.setReturnData
                      ByteArray.empty).setHReturn ByteArray.empty } := by
          rfl
        rw [hStop] at hRun
        cases hRun
        simp [EvmYul.MachineState.setReturnData,
          EvmYul.MachineState.setHReturn]
      · have hPc :
            EvmYul.step (τ := .EVM) EvmYul.Operation.PC none state =
              .ok
                (EvmYul.EVM.State.replaceStackAndIncrPC state
                  (state.stack.push state.pc)) := by
          rfl
        rw [hPc] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · change
          (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run
              state =
            .ok post at hRun
        exact
          PrimStep.run_preserves_code
            (step := PrimStep.binaryMachineState EvmYul.MachineState.evmReturn)
            trivial hRun
      · change
          (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run
              state =
            .ok post at hRun
        exact
          PrimStep.run_preserves_code
            (step := PrimStep.binaryMachineState EvmYul.MachineState.evmRevert)
            trivial hRun
      · cases hPop : state.stack.pop with
        | none =>
            rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop]
              at hRun
            cases hRun
        | some popped =>
            rcases popped with ⟨stack, recipient⟩
            have hStack : state.stack = recipient :: stack :=
              stack_eq_cons_of_pop hPop
            rw [EvmYul.EVM.step_selfdestruct_of_stack
              state recipient stack hStack] at hRun
            cases hRun
            simp [EvmYul.EVM.selfdestructState,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC,
              EvmYul.MachineState.setHReturn]

def PrimStepPreservesPerm : PrimStep → Prop
  | .unaryState f =>
      ∀ state arg, (f state arg).1.executionEnv.perm =
        state.executionEnv.perm
  | .binaryState f =>
      ∀ state left right, (f state left right).executionEnv.perm =
        state.executionEnv.perm
  | .ternaryCopy f =>
      ∀ shared a b c, (f shared a b c).executionEnv.perm =
        shared.executionEnv.perm
  | .quaternaryCopy f =>
      ∀ shared a b c d, (f shared a b c d).executionEnv.perm =
        shared.executionEnv.perm
  | _ => True

theorem State_sstore_preserves_perm
    (state : EvmYul.State EvmYul.OperationType.EVM) (left right : Word) :
    (EvmYul.State.sstore state left right).executionEnv.perm =
      state.executionEnv.perm := by
  simp [EvmYul.State.sstore, EvmYul.State.setAccount,
    EvmYul.State.addAccessedStorageKey, EvmYul.State.lookupAccount]
  cases hAcc :
      Batteries.RBMap.find? state.accountMap state.executionEnv.codeOwner <;>
    rfl

theorem State_tstore_preserves_perm
    (state : EvmYul.State EvmYul.OperationType.EVM) (left right : Word) :
    (EvmYul.State.tstore state left right).executionEnv.perm =
      state.executionEnv.perm := by
  simp [EvmYul.State.tstore, EvmYul.State.updateAccount,
    EvmYul.State.lookupAccount]
  cases hAcc :
      Batteries.RBMap.find? state.accountMap state.executionEnv.codeOwner <;>
    rfl

theorem PrimStepPreservesPerm.of_continuingStep
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    PrimStepPreservesPerm step := by
  cases op <;> simp [PrimOp.continuingStep?] at hStep <;>
    subst step <;>
    simp [PrimStepPreservesPerm, State_sstore_preserves_perm,
      State_tstore_preserves_perm, EvmYul.State.balance,
      EvmYul.State.sload, EvmYul.State.tload, EvmYul.State.extCodeSize,
      EvmYul.State.extCodeHash, EvmYul.State.addAccessedAccount,
      EvmYul.State.addAccessedStorageKey, EvmYul.State.lookupAccount,
      EvmYul.SharedState.calldatacopy, EvmYul.SharedState.codeCopy,
      EvmYul.SharedState.extCodeCopy'] <;>
    intros <;>
    repeat split <;>
    simp

theorem PrimStep.run_preserves_perm
    {step : PrimStep} {state post : EVMState}
    (hPreserve : PrimStepPreservesPerm step)
    (hRun : step.run state = .ok post) :
    post.executionEnv.perm = state.executionEnv.perm := by
  cases step with
  | bin f =>
      cases hPop : state.stack.pop2 with
      | none => simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | un f =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | tri f =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | executionEnv f =>
      simp [PrimStep.run, EvmYul.EVM.executionEnvOp] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | unaryExecutionEnv f =>
      cases hPop : state.stack.pop with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | machineState f =>
      simp [PrimStep.run, EvmYul.EVM.machineStateOp] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | binaryMachineState f =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | binaryMachineStateWithResult f =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | ternaryMachineState f =>
      cases hPop : state.stack.pop3 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | state f =>
      simp [PrimStep.run, EvmYul.EVM.stateOp] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | unaryState f =>
      cases hPop : state.stack.pop with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hRun
          cases hRun
          simpa [PrimStepPreservesPerm,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hPreserve state.toState value
  | binaryState f =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hRun
          cases hRun
          simpa [PrimStepPreservesPerm,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hPreserve state.toState left right
  | ternaryCopy f =>
      cases hPop : state.stack.pop3 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hRun
          cases hRun
          simpa [PrimStepPreservesPerm,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using
            hPreserve state.toSharedState a b c
  | quaternaryCopy f =>
      cases hPop : state.stack.pop4 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d⟩
          simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hRun
          cases hRun
          simpa [PrimStepPreservesPerm,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using
            hPreserve state.toSharedState a b c d
  | pop =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | mload =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, offset⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | returndatacopy =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, hPop] at hRun
          by_cases hBounds : state.returnData.size < b.toNat + c.toNat
          · simp [hBounds] at hRun
          · simp [hBounds] at hRun
            cases hRun
            simp [EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
  | dup n =>
      by_cases hLen : n ≤ state.stack.length
      · simp [PrimStep.run, EvmYul.dup, hLen] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · simp [PrimStep.run, EvmYul.dup, hLen] at hRun
  | swap n =>
      by_cases hLen : n + 1 ≤ state.stack.length
      · simp [PrimStep.run, EvmYul.swap, hLen] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · simp [PrimStep.run, EvmYul.swap, hLen] at hRun
  | log0 =>
      cases hPop : state.stack.pop2 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log1 =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log2 =>
      cases hPop : state.stack.pop4 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log3 =>
      cases hPop : state.stack.pop5 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d, e⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | log4 =>
      cases hPop : state.stack.pop6 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d, e, f⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.SharedState.logOp,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | invalid =>
      simp [PrimStep.run] at hRun

theorem PrimOp.step_preserves_perm_of_no_call_create
    {op : PrimOp} {state post : EVMState}
    (hNoCallCreate : op.isCallCreate = false)
    (hRun : op.step state = .ok post) :
    post.executionEnv.perm = state.executionEnv.perm := by
  unfold PrimOp.step at hRun
  cases hStep : op.continuingStep? with
  | some step =>
      simp [hStep] at hRun
      exact
        PrimStep.run_preserves_perm
          (PrimStepPreservesPerm.of_continuingStep hStep) hRun
  | none =>
      simp [hStep] at hRun
      cases op <;>
        simp [PrimOp.continuingStep?, PrimOp.isCallCreate, PrimOp.toEVM] at hStep hNoCallCreate hRun
      · have hStop :
            EvmYul.step (τ := .EVM) EvmYul.Operation.STOP none state =
              .ok
                { state with
                  toMachineState :=
                    (state.toMachineState.setReturnData
                      ByteArray.empty).setHReturn ByteArray.empty } := by
          rfl
        rw [hStop] at hRun
        cases hRun
        simp [EvmYul.MachineState.setReturnData,
          EvmYul.MachineState.setHReturn]
      · have hPc :
            EvmYul.step (τ := .EVM) EvmYul.Operation.PC none state =
              .ok
                (EvmYul.EVM.State.replaceStackAndIncrPC state
                  (state.stack.push state.pc)) := by
          rfl
        rw [hPc] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · change
          (PrimStep.binaryMachineState EvmYul.MachineState.evmReturn).run
              state =
            .ok post at hRun
        exact
          PrimStep.run_preserves_perm
            (step :=
              PrimStep.binaryMachineState EvmYul.MachineState.evmReturn)
            trivial hRun
      · change
          (PrimStep.binaryMachineState EvmYul.MachineState.evmRevert).run
              state =
            .ok post at hRun
        exact
          PrimStep.run_preserves_perm
            (step :=
              PrimStep.binaryMachineState EvmYul.MachineState.evmRevert)
            trivial hRun
      · cases hPop : state.stack.pop with
        | none =>
            rw [EvmYul_step_selfdestruct_stackUnderflow_of_pop_none hPop]
              at hRun
            cases hRun
        | some popped =>
            rcases popped with ⟨stack, recipient⟩
            have hStack : state.stack = recipient :: stack :=
              stack_eq_cons_of_pop hPop
            rw [EvmYul.EVM.step_selfdestruct_of_stack
              state recipient stack hStack] at hRun
            cases hRun
            simp [EvmYul.EVM.selfdestructState,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC,
              EvmYul.MachineState.setHReturn]

theorem Target.stepInstr_preserves_code_of_no_call_create
    {instr : TargetInstr} {state post : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hStep : Target.stepInstr instr state = .ok post) :
    post.executionEnv.code = state.executionEnv.code := by
  cases instr with
  | push32 value =>
      simp [Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | jump =>
      cases hPop : state.stack.pop with
      | none =>
          simp [Target.stepInstr, hPop] at hStep
      | some popped =>
          rcases popped with ⟨stack, dest⟩
          simp [Target.stepInstr, hPop] at hStep
          cases hStep
          rfl
  | jumpi =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [Target.stepInstr, hPop] at hStep
      | some popped =>
          rcases popped with ⟨stack, dest, cond⟩
          simp [Target.stepInstr, hPop] at hStep
          cases hStep
          rfl
  | jumpdest =>
      simp [Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.incrPC]
  | prim op =>
      change op.step state = .ok post at hStep
      exact
        PrimOp.step_preserves_code_of_no_call_create
          (by simpa [targetInstrUsesCallCreate] using hNoCallCreate)
          hStep

theorem Target.stepInstr_preserves_perm_of_no_call_create
    {instr : TargetInstr} {state post : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hStep : Target.stepInstr instr state = .ok post) :
    post.executionEnv.perm = state.executionEnv.perm := by
  cases instr with
  | push32 value =>
      simp [Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | jump =>
      cases hPop : state.stack.pop with
      | none =>
          simp [Target.stepInstr, hPop] at hStep
      | some popped =>
          rcases popped with ⟨stack, dest⟩
          simp [Target.stepInstr, hPop] at hStep
          cases hStep
          rfl
  | jumpi =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [Target.stepInstr, hPop] at hStep
      | some popped =>
          rcases popped with ⟨stack, dest, cond⟩
          simp [Target.stepInstr, hPop] at hStep
          cases hStep
          rfl
  | jumpdest =>
      simp [Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.incrPC]
  | prim op =>
      change op.step state = .ok post at hStep
      exact
        PrimOp.step_preserves_perm_of_no_call_create
          (by simpa [targetInstrUsesCallCreate] using hNoCallCreate)
          hStep

theorem Target.stepInstrResult_running_preserves_code_of_no_call_create
    {instr : TargetInstr} {state post : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hStepResult :
      Target.stepInstrResult instr state = .ok (.running post)) :
    post.executionEnv.code = state.executionEnv.code := by
  exact
    Target.stepInstr_preserves_code_of_no_call_create hNoCallCreate
      (Target.stepInstrResult_running_stepInstr hStepResult).1

theorem Target.stepInstrResult_halted_preserves_code_of_no_call_create
    {instr : TargetInstr} {state : EVMState} {halt : Halt}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hStepResult :
      Target.stepInstrResult instr state = .ok (.halted halt)) :
    halt.state.executionEnv.code = state.executionEnv.code := by
  exact
    Target.stepInstr_preserves_code_of_no_call_create hNoCallCreate
      (Target.stepInstrResult_halted_stepInstr hStepResult).1

theorem Target.stepInstrResult_running_preserves_perm_of_no_call_create
    {instr : TargetInstr} {state post : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hStepResult :
      Target.stepInstrResult instr state = .ok (.running post)) :
    post.executionEnv.perm = state.executionEnv.perm := by
  exact
    Target.stepInstr_preserves_perm_of_no_call_create hNoCallCreate
      (Target.stepInstrResult_running_stepInstr hStepResult).1

theorem Target.runListResult_running_preserves_perm_of_no_call_create :
    ∀ {code : List TargetInstr} {state post : EVMState},
      Target.runListResult code state = .ok (.running post) →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      post.executionEnv.perm = state.executionEnv.perm := by
  intro code
  induction code with
  | nil =>
      intro state post hRun _hNoCall
      simp [Target.runListResult] at hRun
      cases hRun
      rfl
  | cons instr rest ih =>
      intro state post hRun hNoCall
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCall instr (by simp)
      rcases Target.runListResult_cons_ok_cases hRun with
        ⟨mid, hStepResult, hRunRest⟩ | ⟨halt, _hStepResult, hResult⟩
      · have hMidPerm :
            mid.executionEnv.perm = state.executionEnv.perm :=
          Target.stepInstrResult_running_preserves_perm_of_no_call_create
            hNoCallInstr hStepResult
        have hNoCallRest :
            ∀ instr' ∈ rest, targetInstrUsesCallCreate instr' = false := by
          intro instr' hMem
          exact hNoCall instr' (by simp [hMem])
        exact (ih hRunRest hNoCallRest).trans hMidPerm
      · cases hResult

theorem Target.runListResult_preserves_code_of_no_call_create :
    ∀ {code : List TargetInstr} {state : EVMState} {result : StepResult},
      Target.runListResult code state = .ok result →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      match result with
      | .running post =>
          post.executionEnv.code = state.executionEnv.code
      | .halted halt =>
          halt.state.executionEnv.code = state.executionEnv.code := by
  intro code
  induction code with
  | nil =>
      intro state result hRun _hNoCall
      simp [Target.runListResult] at hRun
      cases hRun
      rfl
  | cons instr rest ih =>
      intro state result hRun hNoCall
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCall instr (by simp)
      rcases Target.runListResult_cons_ok_cases hRun with
        ⟨post, hStepResult, hRunRest⟩ | ⟨halt, hStepResult, hResult⟩
      · have hHeadCode :
            post.executionEnv.code = state.executionEnv.code :=
          Target.stepInstrResult_running_preserves_code_of_no_call_create
            hNoCallInstr hStepResult
        have hNoCallRest :
            ∀ instr' ∈ rest, targetInstrUsesCallCreate instr' = false := by
          intro instr' hMem
          exact hNoCall instr' (by simp [hMem])
        have hTailCode :=
          ih hRunRest hNoCallRest
        cases result with
        | running final =>
            exact hTailCode.trans hHeadCode
        | halted halt =>
            exact hTailCode.trans hHeadCode
      · subst result
        exact
          Target.stepInstrResult_halted_preserves_code_of_no_call_create
            hNoCallInstr hStepResult

def TargetInstrBodyPreservesGas (instr : TargetInstr) : Prop :=
  ∀ {state post : EVMState},
    EvmYul.step instr.op instr.arg state = .ok post →
      post.gasAvailable = state.gasAvailable

theorem TargetInstrBodyPreservesGas.of_no_call_create
    {instr : TargetInstr}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false) :
    TargetInstrBodyPreservesGas instr := by
  intro state post hRun
  cases instr with
  | push32 value =>
      change
        Except.ok (EvmYul.EVM.State.replaceStackAndIncrPC state
          (state.stack.push value) (pcΔ := 33)) = .ok post at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | jump =>
      simp only [TargetInstr.op, TargetInstr.arg] at hRun
      cases hPop : state.stack.pop with
      | none =>
          cases state with
          | mk shared pc stack execLength =>
              cases stack with
              | nil =>
                  change
                    (Except.error EvmYul.EVM.ExecutionException.StackUnderflow :
                      Except EvmYul.EVM.ExecutionException EVMState) =
                      .ok post at hRun
                  cases hRun
              | cons hd tl =>
                  simp [EvmYul.Stack.pop] at hPop
      | some popped =>
          rcases popped with ⟨stack, dest⟩
          have hStack : state.stack = dest :: stack :=
            stack_eq_cons_of_pop hPop
          rw [EvmYul_step_jump_of_stack state stack dest hStack] at hRun
          cases hRun
          rfl
  | jumpi =>
      simp only [TargetInstr.op, TargetInstr.arg] at hRun
      cases hPop : state.stack.pop2 with
      | none =>
          cases state with
          | mk shared pc stack execLength =>
              cases stack with
              | nil =>
                  change
                    (Except.error EvmYul.EVM.ExecutionException.StackUnderflow :
                      Except EvmYul.EVM.ExecutionException EVMState) =
                      .ok post at hRun
                  cases hRun
              | cons first rest =>
                  cases rest with
                  | nil =>
                      change
                        (Except.error
                            EvmYul.EVM.ExecutionException.StackUnderflow :
                          Except EvmYul.EVM.ExecutionException EVMState) =
                          .ok post at hRun
                      cases hRun
                  | cons second rest =>
                      simp [EvmYul.Stack.pop2] at hPop
      | some popped =>
          rcases popped with ⟨stack, dest, cond⟩
          have hStack : state.stack = dest :: cond :: stack :=
            stack_eq_cons_cons_of_pop2 hPop
          rw [EvmYul_step_jumpi_of_stack state stack dest cond hStack]
            at hRun
          cases hRun
          rfl
  | jumpdest =>
      simp only [TargetInstr.op, TargetInstr.arg] at hRun
      rw [EvmYul_step_jumpdest_eq state] at hRun
      cases hRun
      simp [EvmYul.EVM.State.incrPC]
  | prim op =>
      change EvmYul.step op.toEVM none state = .ok post at hRun
      cases hStep : op.continuingStep? with
      | none =>
          exact EvmYul_step_noncontinuing_prim_gasAvailable_eq hStep
            (by simpa [targetInstrUsesCallCreate] using hNoCallCreate) hRun
      | some step =>
          exact EvmYul_step_continuing_prim_gasAvailable_eq hStep hRun

def XRunListBodyPreservesGas : List TargetInstr → Prop
  | [] => True
  | instr :: rest =>
      TargetInstrBodyPreservesGas instr ∧
        XRunListBodyPreservesGas rest

theorem XRunListBodyPreservesGas.of_all_no_call_create :
    ∀ {code : List TargetInstr},
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      XRunListBodyPreservesGas code := by
  intro code
  induction code with
  | nil =>
      intro _hAll
      trivial
  | cons instr rest ih =>
      intro hAll
      exact
        ⟨TargetInstrBodyPreservesGas.of_no_call_create
            (hAll instr (by simp)),
          ih (by
            intro instr' hMem
            exact hAll instr' (by simp [hMem]))⟩

def XRunListGasBudget : List TargetInstr → EVMState → Nat
  | [], _target => 0
  | instr :: rest, target =>
      XGasRequiredAt target instr.op +
        match Target.stepInstrResult instr target with
        | .ok (.running targetPost) =>
            XRunListGasBudget rest targetPost
        | .ok (.halted _halt) | .error _ =>
            0

theorem XRunListSuffixReady.of_parts {validJumps : Array Word}
    {code : List TargetInstr}
    (hNonGas : XRunListSuffixNonGasReady validJumps code)
    (hGas : XRunListSuffixGasReady code) :
    XRunListSuffixReady validJumps code := by
  intro instr rest targetState blockResult hSuffix hRun fullState hRel
  obtain ⟨hDecode, hChecks, hNoCallCreate⟩ :=
    hNonGas hSuffix hRun hRel
  exact ⟨hDecode, hChecks, hGas hSuffix hRun hRel, hNoCallCreate⟩

theorem XRunListSuffixReady.nonGas {validJumps : Array Word}
    {code : List TargetInstr}
    (hReady : XRunListSuffixReady validJumps code) :
    XRunListSuffixNonGasReady validJumps code := by
  intro instr rest targetState blockResult hSuffix hRun fullState hRel
  obtain ⟨hDecode, hChecks, _hGas, hNoCallCreate⟩ :=
    hReady hSuffix hRun hRel
  exact ⟨hDecode, hChecks, hNoCallCreate⟩

theorem XRunListSuffixReady.gas {validJumps : Array Word}
    {code : List TargetInstr}
    (hReady : XRunListSuffixReady validJumps code) :
    XRunListSuffixGasReady code := by
  intro instr rest targetState blockResult hSuffix hRun fullState hRel
  exact (hReady hSuffix hRun hRel).2.2.1

def XRunListPathReady (validJumps : Array Word) :
    List TargetInstr → EVMState → EVMState → StepResult → Prop
  | [], target, full, result =>
      result = .running target ∧ GasExecRel full target
  | instr :: rest, target, full, result =>
      GasExecRel full target ∧
        EvmYul.EVM.decode full.executionEnv.code full.pc =
          some (instr.op, instr.arg) ∧
        XNonGasChecksPass validJumps full instr.op ∧
        XGasRequiredAt full instr.op ≤ full.gasAvailable.toNat ∧
        targetInstrUsesCallCreate instr = false ∧
        match Target.stepInstrResult instr target with
        | .ok (.running targetPost) =>
            ∀ {stepFuel : Nat} {fullPost : EVMState},
              EvmYul.EVM.step stepFuel.succ
                  (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  (some (instr.op, instr.arg))
                  (memoryGasState full instr.op) =
                .ok fullPost →
              XRunListPathReady validJumps rest targetPost fullPost result
        | .ok (.halted halt) =>
            result = .halted halt
        | .error _ =>
            False

def XRunListPathDecodeReady :
    List TargetInstr → EVMState → EVMState → StepResult → Prop
  | [], _target, _full, _result => True
  | instr :: rest, target, full, result =>
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg) ∧
        match Target.stepInstrResult instr target with
        | .ok (.running targetPost) =>
            ∀ {stepFuel : Nat} {fullPost : EVMState},
              EvmYul.EVM.step stepFuel.succ
                  (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  (some (instr.op, instr.arg))
                  (memoryGasState full instr.op) =
                .ok fullPost →
              XRunListPathDecodeReady rest targetPost fullPost result
        | .ok (.halted _halt) =>
            True
        | .error _ =>
            False

def XRunListPathChecksReady (validJumps : Array Word) :
    List TargetInstr → EVMState → EVMState → StepResult → Prop
  | [], target, full, result =>
      result = .running target ∧ GasExecRel full target
  | instr :: rest, target, full, result =>
      GasExecRel full target ∧
        XNonGasChecksPass validJumps full instr.op ∧
        targetInstrUsesCallCreate instr = false ∧
        match Target.stepInstrResult instr target with
        | .ok (.running targetPost) =>
            ∀ {stepFuel : Nat} {fullPost : EVMState},
              EvmYul.EVM.step stepFuel.succ
                  (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  (some (instr.op, instr.arg))
                  (memoryGasState full instr.op) =
                .ok fullPost →
              XRunListPathChecksReady validJumps rest targetPost fullPost result
        | .ok (.halted halt) =>
            result = .halted halt
        | .error _ =>
            False

def XRunListPathCoreChecksReady (validJumps : Array Word) :
    List TargetInstr → EVMState → EVMState → StepResult → Prop
  | [], target, full, result =>
      result = .running target ∧ GasExecRel full target
  | instr :: rest, target, full, result =>
      GasExecRel full target ∧
        XNonGasCoreChecksPass validJumps full instr.op ∧
        match Target.stepInstrResult instr target with
        | .ok (.running targetPost) =>
            ∀ {stepFuel : Nat} {fullPost : EVMState},
              EvmYul.EVM.step stepFuel.succ
                  (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  (some (instr.op, instr.arg))
                  (memoryGasState full instr.op) =
                .ok fullPost →
              XRunListPathCoreChecksReady validJumps rest targetPost
                fullPost result
        | .ok (.halted halt) =>
            result = .halted halt
        | .error _ =>
            False

def XRunListPathReturnDataCopyBoundsReady :
    List TargetInstr → EVMState → EVMState → StepResult → Prop
  | [], target, full, result =>
      result = .running target ∧ GasExecRel full target
  | instr :: rest, target, full, result =>
      GasExecRel full target ∧
        XReturnDataCopyBoundsPass full instr.op ∧
        match Target.stepInstrResult instr target with
        | .ok (.running targetPost) =>
            ∀ {stepFuel : Nat} {fullPost : EVMState},
              EvmYul.EVM.step stepFuel.succ
                  (EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  (some (instr.op, instr.arg))
                  (memoryGasState full instr.op) =
                .ok fullPost →
              XRunListPathReturnDataCopyBoundsReady rest targetPost
                fullPost result
        | .ok (.halted halt) =>
            result = .halted halt
        | .error _ =>
            False

theorem XRunListPathReturnDataCopyBoundsReady.of_run_noReturnDataCopy_noCallCreate :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      (∀ instr ∈ code, targetInstrNoReturnDataCopy instr = true) →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      GasExecRel full target →
      XRunListPathReturnDataCopyBoundsReady code target full
        targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hNoReturnDataCopy _hNoCallCreate
        hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hNoReturnDataCopy hNoCallCreate
        hRel
      have hNoReturnInstr :
          instr.op ≠ EvmYul.Operation.RETURNDATACOPY :=
        targetInstr_op_ne_returnDataCopy_of_noReturnDataCopy
          (hNoReturnDataCopy instr (by simp))
      have hReturnDataCopyBounds :
          XReturnDataCopyBoundsPass full instr.op :=
        XReturnDataCopyBoundsPass.of_no_returnDataCopy hNoReturnInstr
      have hNoCallInstr :
          targetInstrUsesCallCreate instr = false :=
        hNoCallCreate instr (by simp)
      simp [XRunListPathReturnDataCopyBoundsReady, hRel,
        hReturnDataCopyBounds]
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          change False
          rw [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok targetResult at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [Target.runListResult, hStepResult] at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallInstr (hRel.memoryGasState_left (op := instr.op))
                  (Target.stepInstrResult_running_stepInstr
                    hStepResult).1 hStep
              have hNoReturnRest :
                  ∀ instr' ∈ rest,
                    targetInstrNoReturnDataCopy instr' = true := by
                intro instr' hMemRest
                exact hNoReturnDataCopy instr' (by simp [hMemRest])
              have hNoCallRest :
                  ∀ instr' ∈ rest,
                    targetInstrUsesCallCreate instr' = false := by
                intro instr' hMemRest
                exact hNoCallCreate instr' (by simp [hMemRest])
              exact ih hRun hNoReturnRest hNoCallRest hRelPost

theorem XRunListPathReturnDataCopyBoundsReady.of_run_noCallCreate :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      GasExecRel full target →
      XRunListPathReturnDataCopyBoundsReady code target full
        targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hNoCallCreate hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hNoCallCreate hRel
      have hNoCallInstr :
          targetInstrUsesCallCreate instr = false :=
        hNoCallCreate instr (by simp)
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          rw [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok targetResult at hRun
          cases hRun
      | ok stepResult =>
          have hReturnDataCopyBounds :
              XReturnDataCopyBoundsPass full instr.op :=
            (XReturnDataCopyBoundsPass_iff_of_gasExecRel hRel).2
              (XReturnDataCopyBoundsPass.of_stepInstrResult_ok
                hStepResult)
          cases stepResult with
          | halted halt =>
              simp [XRunListPathReturnDataCopyBoundsReady, hRel,
                hReturnDataCopyBounds, hStepResult]
              simp [Target.runListResult, hStepResult] at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [XRunListPathReturnDataCopyBoundsReady, hRel,
                hReturnDataCopyBounds, hStepResult]
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallInstr (hRel.memoryGasState_left (op := instr.op))
                  (Target.stepInstrResult_running_stepInstr
                    hStepResult).1 hStep
              have hNoCallRest :
                  ∀ instr' ∈ rest,
                    targetInstrUsesCallCreate instr' = false := by
                intro instr' hMemRest
                exact hNoCallCreate instr' (by simp [hMemRest])
              exact ih hRun hNoCallRest hRelPost

/--
Gasless target execution with the non-gas `EVM.X` core checks made explicit.

This is the thin intermediate layer between `Target.runListResult` and the
gas-aware replay proof: it follows the same target instructions, but records
the stack/jump/static checks that `EVM.X` performs before delegating to
`EVM.step`.
-/
inductive CoreRunListResult (validJumps : Array Word) :
    List TargetInstr → EVMState → StepResult → Prop where
  | nil (state : EVMState) :
      CoreRunListResult validJumps [] state (.running state)
  | stepRunning {instr : TargetInstr} {rest : List TargetInstr}
      {state mid : EVMState} {result : StepResult}
      (hCore : XNonGasCoreChecksPass validJumps state instr.op)
      (hStep :
        Target.stepInstrResult instr state = .ok (.running mid))
      (hRest : CoreRunListResult validJumps rest mid result) :
      CoreRunListResult validJumps (instr :: rest) state result
  | stepHalted {instr : TargetInstr} {rest : List TargetInstr}
      {state : EVMState} {halt : Halt}
      (hCore : XNonGasCoreChecksPass validJumps state instr.op)
      (hStep :
        Target.stepInstrResult instr state = .ok (.halted halt)) :
      CoreRunListResult validJumps (instr :: rest) state (.halted halt)

theorem CoreRunListResult.to_runListResult {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {state : EVMState} {result : StepResult},
      CoreRunListResult validJumps code state result →
        Target.runListResult code state = .ok result := by
  intro code state result hCore
  induction hCore with
  | nil state =>
      rfl
  | stepRunning hCoreStep hStep hRest ih =>
      rw [Target.runListResult, hStep]
      simpa using ih
  | stepHalted hCoreStep hStep =>
      rw [Target.runListResult, hStep]
      rfl

theorem CoreRunListResult.head_core
    {validJumps : Array Word} {instr : TargetInstr}
    {rest : List TargetInstr} {state : EVMState} {result : StepResult}
    (hCore :
      CoreRunListResult validJumps (instr :: rest) state result) :
    XNonGasCoreChecksPass validJumps state instr.op := by
  cases hCore with
  | stepRunning hCoreStep _hStep _hRest =>
      exact hCoreStep
  | stepHalted hCoreStep _hStep =>
      exact hCoreStep

theorem CoreRunListResult.running_stack_le_of_initial
    {validJumps : Array Word} {code : List TargetInstr}
    {state post : EVMState}
    (hCore : CoreRunListResult validJumps code state (.running post))
    (hInitial : state.stack.length ≤ 1024)
    (hNoCallCreate :
      ∀ instr ∈ code, targetInstrUsesCallCreate instr = false) :
    post.stack.length ≤ 1024 := by
  induction code generalizing state post with
  | nil =>
      cases hCore
      exact hInitial
  | cons instr rest ih =>
      cases hCore with
      | stepRunning hCoreStep hStep hRest =>
          have hNoInstr :
              targetInstrUsesCallCreate instr = false :=
            hNoCallCreate instr (by simp)
          have hMid :=
            Target.stepInstrResult_running_stack_le_of_core_no_call_create
              hNoInstr hCoreStep hStep
          have hNoRest :
              ∀ instr' ∈ rest, targetInstrUsesCallCreate instr' = false := by
            intro instr' hMem
            exact hNoCallCreate instr' (by simp [hMem])
          exact ih hRest hMid hNoRest

theorem CoreRunListResult.singleton_of_core
    {validJumps : Array Word} {instr : TargetInstr}
    {state : EVMState} {result : StepResult}
    (hCore : XNonGasCoreChecksPass validJumps state instr.op)
    (hRun : Target.runListResult [instr] state = .ok result) :
    CoreRunListResult validJumps [instr] state result := by
  rcases Target.runListResult_cons_ok_cases hRun with
    ⟨mid, hStep, hRest⟩ | ⟨halt, hStep, hResult⟩
  · simp [Target.runListResult] at hRest
    subst result
    exact
      CoreRunListResult.stepRunning hCore hStep
        (CoreRunListResult.nil (validJumps := validJumps) mid)
  · subst result
    exact CoreRunListResult.stepHalted hCore hStep

theorem XCoreStackAndJumpInputsReady.push32
    {validJumps : Array Word} {state : EVMState} {value : Word} :
    XCoreStackAndJumpInputsReady validJumps state
      (TargetInstr.push32 value).op := by
  simp [XCoreStackAndJumpInputsReady, TargetInstr.op, EvmYul.EVM.δ]

theorem XNonGasCoreChecksPass.push32_of_stack
    {validJumps : Array Word} {state : EVMState} {value : Word}
    (hStack : state.stack.length + 1 ≤ 1024) :
    XNonGasCoreChecksPass validJumps state (TargetInstr.push32 value).op := by
  exact
    XNonGasCoreChecksPass.of_inputs_overflow_static
      (XCoreStackAndJumpInputsReady.push32
        (validJumps := validJumps) (state := state) (value := value))
      (by
        simpa [TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α] using hStack)
      (by
        intro _hStatic hWrite
        simp [staticWriteSensitive, TargetInstr.op] at hWrite)

theorem XNonGasCoreChecksPass.jumpdest_of_stack
    {validJumps : Array Word} {state : EVMState}
    (hStack : state.stack.length ≤ 1024) :
    XNonGasCoreChecksPass validJumps state TargetInstr.jumpdest.op := by
  refine
    XNonGasCoreChecksPass.of_inputs_overflow_static ?_ ?_ ?_
  · simp [XCoreStackAndJumpInputsReady, TargetInstr.op, EvmYul.EVM.δ]
  · simpa [TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α] using hStack
  · intro _hStatic hWrite
    simp [staticWriteSensitive, TargetInstr.op] at hWrite

theorem CoreRunListResult.jumpdest_of_stack
    {validJumps : Array Word} {state : EVMState} {result : StepResult}
    (hStack : state.stack.length ≤ 1024)
    (hRun :
      Target.runListResult [TargetInstr.jumpdest] state = .ok result) :
    CoreRunListResult validJumps [TargetInstr.jumpdest] state result :=
  CoreRunListResult.singleton_of_core
    (XNonGasCoreChecksPass.jumpdest_of_stack
      (validJumps := validJumps) (state := state) hStack)
    hRun

theorem CoreRunListResult.push32_of_stack
    {validJumps : Array Word} {state : EVMState} {value : Word}
    {result : StepResult}
    (hStack : state.stack.length + 1 ≤ 1024)
    (hRun :
      Target.runListResult [TargetInstr.push32 value] state = .ok result) :
    CoreRunListResult validJumps [TargetInstr.push32 value] state result :=
  CoreRunListResult.singleton_of_core
    (XNonGasCoreChecksPass.push32_of_stack
      (validJumps := validJumps) (state := state) (value := value) hStack)
    hRun

theorem XNonGasCoreChecksPass.jump_after_push32_of_allowed
    {validJumps : Array Word} {state : EVMState} {value : Word}
    (hAllowed : jumpTargetAllowed (some value) validJumps)
    (hStack : state.stack.length + 1 ≤ 1024) :
    XNonGasCoreChecksPass validJumps
      (EvmYul.EVM.State.replaceStackAndIncrPC state
        (state.stack.push value) (pcΔ := 33))
      TargetInstr.jump.op := by
  refine
    XNonGasCoreChecksPass.of_inputs_overflow_static ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [TargetInstr.op, EvmYul.EVM.δ]
    · simp [TargetInstr.op, EvmYul.EVM.δ, EvmYul.Stack.push,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
    · intro _hOp
      simpa [jumpTargetAllowed, EvmYul.Stack.push,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] using hAllowed
    · intro hOp
      simp [TargetInstr.op] at hOp
  · simp [TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α,
      EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
    omega
  · intro _hStatic hWrite
    simp [staticWriteSensitive, TargetInstr.op] at hWrite

theorem XNonGasCoreChecksPass.jumpi_after_push32_of_allowed
    {validJumps : Array Word} {state : EVMState} {value : Word}
    (hStackNonempty : 1 ≤ state.stack.length)
    (hAllowed :
      state.stack[0]? ≠ some ⟨0⟩ →
        jumpTargetAllowed (some value) validJumps)
    (hStack : state.stack.length + 1 ≤ 1024) :
    XNonGasCoreChecksPass validJumps
      (EvmYul.EVM.State.replaceStackAndIncrPC state
        (state.stack.push value) (pcΔ := 33))
      TargetInstr.jumpi.op := by
  refine
    XNonGasCoreChecksPass.of_inputs_overflow_static ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [TargetInstr.op, EvmYul.EVM.δ]
    · simp [TargetInstr.op, EvmYul.EVM.δ, EvmYul.Stack.push,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
      omega
    · intro hOp
      simp [TargetInstr.op] at hOp
    · intro _hOp hCond
      exact hAllowed (by
        simpa [EvmYul.Stack.push,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC] using hCond)
  · simp [TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α,
      EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
    omega
  · intro _hStatic hWrite
    simp [staticWriteSensitive, TargetInstr.op] at hWrite

theorem CoreRunListResult.push32_jump_of_allowed
    {validJumps : Array Word} {state : EVMState} {value : Word}
    {result : StepResult}
    (hAllowed : jumpTargetAllowed (some value) validJumps)
    (hStack : state.stack.length + 1 ≤ 1024)
    (hRun :
      Target.runListResult [TargetInstr.push32 value, TargetInstr.jump]
        state = .ok result) :
    CoreRunListResult validJumps
      [TargetInstr.push32 value, TargetInstr.jump] state result := by
  let mid :=
    EvmYul.EVM.State.replaceStackAndIncrPC state
      (state.stack.push value) (pcΔ := 33)
  have hPushStep :
      Target.stepInstrResult (TargetInstr.push32 value) state =
        .ok (.running mid) := by
    rfl
  have hRunRest :
      Target.runListResult [TargetInstr.jump] mid = .ok result := by
    simpa [mid, Target.runListResult, Target.stepInstrResult,
      Target.stepInstr] using hRun
  exact
    CoreRunListResult.stepRunning
      (XNonGasCoreChecksPass.push32_of_stack
        (validJumps := validJumps) (state := state) (value := value)
        hStack)
      hPushStep
      (CoreRunListResult.singleton_of_core
        (XNonGasCoreChecksPass.jump_after_push32_of_allowed
          (validJumps := validJumps) (state := state) (value := value)
          hAllowed hStack)
        hRunRest)

theorem CoreRunListResult.push32_jumpi_of_allowed
    {validJumps : Array Word} {state : EVMState} {value : Word}
    {result : StepResult}
    (hStackNonempty : 1 ≤ state.stack.length)
    (hAllowed :
      state.stack[0]? ≠ some ⟨0⟩ →
        jumpTargetAllowed (some value) validJumps)
    (hStack : state.stack.length + 1 ≤ 1024)
    (hRun :
      Target.runListResult [TargetInstr.push32 value, TargetInstr.jumpi]
        state = .ok result) :
    CoreRunListResult validJumps
      [TargetInstr.push32 value, TargetInstr.jumpi] state result := by
  let mid :=
    EvmYul.EVM.State.replaceStackAndIncrPC state
      (state.stack.push value) (pcΔ := 33)
  have hPushStep :
      Target.stepInstrResult (TargetInstr.push32 value) state =
        .ok (.running mid) := by
    rfl
  have hRunRest :
      Target.runListResult [TargetInstr.jumpi] mid = .ok result := by
    simpa [mid, Target.runListResult, Target.stepInstrResult,
      Target.stepInstr] using hRun
  exact
    CoreRunListResult.stepRunning
      (XNonGasCoreChecksPass.push32_of_stack
        (validJumps := validJumps) (state := state) (value := value)
        hStack)
      hPushStep
      (CoreRunListResult.singleton_of_core
        (XNonGasCoreChecksPass.jumpi_after_push32_of_allowed
          (validJumps := validJumps) (state := state) (value := value)
          hStackNonempty hAllowed hStack)
        hRunRest)

theorem CoreRunListResult.push32_jump_of_labelPc
    {program : Program} {target : TargetProgram} {label : Label}
    {dest : Nat} {state : EVMState} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hDest : Program.labelPc program label = some dest)
    (hStack : state.stack.length + 1 ≤ 1024)
    (hRun :
      Target.runListResult
          [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
          , TargetInstr.jump ]
        state = .ok result) :
    CoreRunListResult (validJumps target)
      [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
      , TargetInstr.jump ]
      state result :=
  CoreRunListResult.push32_jump_of_allowed
    (validJumps := validJumps target) (state := state)
    (value := EvmYul.UInt256.ofNat dest)
    (jumpTargetAllowed_of_assemble_labelPc hAsm hJumpdest hDest)
    hStack hRun

theorem CoreRunListResult.push32_jumpi_of_labelPc
    {program : Program} {target : TargetProgram} {label : Label}
    {dest : Nat} {state : EVMState} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hDest : Program.labelPc program label = some dest)
    (hStackNonempty : 1 ≤ state.stack.length)
    (hStack : state.stack.length + 1 ≤ 1024)
    (hRun :
      Target.runListResult
          [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
          , TargetInstr.jumpi ]
        state = .ok result) :
    CoreRunListResult (validJumps target)
      [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
      , TargetInstr.jumpi ]
      state result :=
  CoreRunListResult.push32_jumpi_of_allowed
    (validJumps := validJumps target) (state := state)
    (value := EvmYul.UInt256.ofNat dest)
    hStackNonempty
    (fun _hCond =>
      jumpTargetAllowed_of_assemble_labelPc hAsm hJumpdest hDest)
    hStack hRun

theorem CoreRunListResult.of_emitInstr_jump
    {program : Program} {target : TargetProgram} {pc : Nat}
    {label : Label} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hEmit : emitInstr? program pc (.jump label) = some emitted)
    (hStack : state.stack.length + 1 ≤ 1024)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    CoreRunListResult (validJumps target)
      (emitted.map LocatedTarget.instr) state result := by
  cases hDest : Program.labelPc program label with
  | none =>
      simp [emitInstr?, hDest] at hEmit
  | some dest =>
      simp [emitInstr?, hDest] at hEmit
      subst emitted
      exact
        CoreRunListResult.push32_jump_of_labelPc
          (program := program) (target := target) (label := label)
          (dest := dest) hAsm hJumpdest hDest hStack
          (by simpa using hRun)

theorem CoreRunListResult.of_emitInstr_jumpi
    {program : Program} {target : TargetProgram} {pc : Nat}
    {label : Label} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hEmit : emitInstr? program pc (.jumpi label) = some emitted)
    (hStackNonempty : 1 ≤ state.stack.length)
    (hStack : state.stack.length + 1 ≤ 1024)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    CoreRunListResult (validJumps target)
      (emitted.map LocatedTarget.instr) state result := by
  cases hDest : Program.labelPc program label with
  | none =>
      simp [emitInstr?, hDest] at hEmit
  | some dest =>
      simp [emitInstr?, hDest] at hEmit
      subst emitted
      exact
        CoreRunListResult.push32_jumpi_of_labelPc
          (program := program) (target := target) (label := label)
          (dest := dest) hAsm hJumpdest hDest hStackNonempty hStack
          (by simpa using hRun)

theorem CoreRunListResult.of_emitInstr_label
    {validJumps : Array Word} {program : Program} {pc : Nat}
    {label : Label} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc (.label label) = some emitted)
    (hStack : state.stack.length ≤ 1024)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    CoreRunListResult validJumps
      (emitted.map LocatedTarget.instr) state result := by
  simp [emitInstr?] at hEmit
  subst emitted
  exact
    CoreRunListResult.jumpdest_of_stack
      (validJumps := validJumps) hStack (by simpa using hRun)

theorem CoreRunListResult.of_emitInstr_push
    {validJumps : Array Word} {program : Program} {pc : Nat}
    {value : Word} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc (.push value) = some emitted)
    (hStack : state.stack.length + 1 ≤ 1024)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    CoreRunListResult validJumps
      (emitted.map LocatedTarget.instr) state result := by
  simp [emitInstr?] at hEmit
  subst emitted
  exact
    CoreRunListResult.push32_of_stack
      (validJumps := validJumps) hStack (by simpa using hRun)

def InstrControlCoreStackReady (instr : Instr) (state : EVMState) : Prop :=
  match instr with
  | .label _ => state.stack.length ≤ 1024
  | .push _ | .jump _ => state.stack.length + 1 ≤ 1024
  | .jumpi _ => 1 ≤ state.stack.length ∧ state.stack.length + 1 ≤ 1024
  | .prim _ => False

def InstrCoreBlockReady (target : TargetProgram) (instr : Instr)
    (state : EVMState) : Prop :=
  match instr with
  | .prim op =>
      XNonGasCoreChecksPass (validJumps target) state
        (TargetInstr.prim op).op
  | _ => InstrControlCoreStackReady instr state

def InstrCoreBlockInputsReady (target : TargetProgram) (instr : Instr)
    (state : EVMState) : Prop :=
  match instr with
  | .prim op =>
      let evmOp := (TargetInstr.prim op).op
      XCoreStackAndJumpInputsReady (validJumps target) state evmOp ∧
        state.stack.length - (EvmYul.EVM.δ evmOp).getD 0 +
            (EvmYul.EVM.α evmOp).getD 0 ≤ 1024 ∧
          (state.executionEnv.perm = false →
            ¬ staticWriteSensitive evmOp state.stack)
  | _ => InstrControlCoreStackReady instr state

def InstrControlCoreInputsReady (instr : Instr) (state : EVMState) : Prop :=
  match instr with
  | .prim _ => True
  | _ => InstrControlCoreStackReady instr state

def InstrControlStackRoomReady (instr : Instr) (state : EVMState) : Prop :=
  match instr with
  | .label _ => state.stack.length ≤ 1024
  | .push _ | .jump _ | .jumpi _ => state.stack.length + 1 ≤ 1024
  | .prim _ => True

def InstrPrimitiveStackJumpInputsReady
    (target : TargetProgram) (instr : Instr) (state : EVMState) : Prop :=
  match instr with
  | .prim op =>
      XCoreStackAndJumpInputsReady (validJumps target) state
        (TargetInstr.prim op).op
  | _ => True

def InstrPrimitiveOverflowInputsReady
    (_target : TargetProgram) (instr : Instr) (state : EVMState) : Prop :=
  match instr with
  | .prim op =>
      let evmOp := (TargetInstr.prim op).op
      state.stack.length - (EvmYul.EVM.δ evmOp).getD 0 +
          (EvmYul.EVM.α evmOp).getD 0 ≤ 1024
  | _ => True

def InstrPrimitiveStaticInputsReady
    (_target : TargetProgram) (instr : Instr) (state : EVMState) : Prop :=
  match instr with
  | .prim op =>
      let evmOp := (TargetInstr.prim op).op
      state.executionEnv.perm = false →
        ¬ staticWriteSensitive evmOp state.stack
  | _ => True

theorem InstrPrimitiveStaticInputsReady.of_perm_true
    {target : TargetProgram} {instr : Instr} {state : EVMState}
    (hPerm : state.executionEnv.perm = true) :
    InstrPrimitiveStaticInputsReady target instr state := by
  cases instr with
  | label label =>
      simp [InstrPrimitiveStaticInputsReady]
  | prim op =>
      intro hStatic
      rw [hPerm] at hStatic
      cases hStatic
  | push value =>
      simp [InstrPrimitiveStaticInputsReady]
  | jump targetLabel =>
      simp [InstrPrimitiveStaticInputsReady]
  | jumpi targetLabel =>
      simp [InstrPrimitiveStaticInputsReady]

theorem InstrPrimitiveStackJumpInputsReady.of_prim_continuing_run
    {program : Program} {target : TargetProgram} {pc : Nat}
    {op : PrimOp} {step : PrimStep} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc (.prim op) = some emitted)
    (hStep : op.continuingStep? = some step)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    InstrPrimitiveStackJumpInputsReady target (.prim op) state := by
  simp [emitInstr?] at hEmit
  subst emitted
  simpa [InstrPrimitiveStackJumpInputsReady] using
    XCoreStackAndJumpInputsReady.of_prim_continuing_runListResult
      (validJumps := validJumps target) hStep (by simpa using hRun)

theorem InstrPrimitiveStackJumpInputsReady.of_prim_run_no_call_create
    {program : Program} {target : TargetProgram} {pc : Nat}
    {op : PrimOp} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc (.prim op) = some emitted)
    (hNoCallCreate : op.isCallCreate = false)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    InstrPrimitiveStackJumpInputsReady target (.prim op) state := by
  simp [emitInstr?] at hEmit
  subst emitted
  simpa [InstrPrimitiveStackJumpInputsReady] using
    XCoreStackAndJumpInputsReady.of_prim_runListResult_no_call_create
      (validJumps := validJumps target) hNoCallCreate (by simpa using hRun)

def InstrCoreResidualInputsReady (target : TargetProgram) (instr : Instr)
    (state : EVMState) : Prop :=
  match instr with
  | .prim op =>
      InstrPrimitiveOverflowInputsReady target (.prim op) state ∧
        InstrPrimitiveStaticInputsReady target (.prim op) state
  | _ => InstrControlStackRoomReady instr state

theorem InstrPrimitiveOverflowInputsReady.of_stack_bound16
    {target : TargetProgram} {instr : Instr} {state : EVMState}
    (hStack : state.stack.length ≤ 16) :
    InstrPrimitiveOverflowInputsReady target instr state := by
  cases instr with
  | label label =>
      simp [InstrPrimitiveOverflowInputsReady]
  | prim op =>
      simp [InstrPrimitiveOverflowInputsReady]
      have hAlpha :=
        EVM_alpha_getD_le_17 (TargetInstr.prim op).op
      have hSub :
          state.stack.length -
              (EvmYul.EVM.δ (TargetInstr.prim op).op).getD 0 ≤
            state.stack.length := Nat.sub_le _ _
      omega
  | push value =>
      simp [InstrPrimitiveOverflowInputsReady]
  | jump targetLabel =>
      simp [InstrPrimitiveOverflowInputsReady]
  | jumpi targetLabel =>
      simp [InstrPrimitiveOverflowInputsReady]

theorem InstrPrimitiveOverflowInputsReady.of_stack_headroom17
    {target : TargetProgram} {instr : Instr} {state : EVMState}
    (hStack : state.stack.length + 17 ≤ 1024) :
    InstrPrimitiveOverflowInputsReady target instr state := by
  cases instr with
  | label label =>
      simp [InstrPrimitiveOverflowInputsReady]
  | prim op =>
      simp [InstrPrimitiveOverflowInputsReady]
      have hAlpha :=
        EVM_alpha_getD_le_17 (TargetInstr.prim op).op
      have hSub :
          state.stack.length -
              (EvmYul.EVM.δ (TargetInstr.prim op).op).getD 0 ≤
            state.stack.length := Nat.sub_le _ _
      omega
  | push value =>
      simp [InstrPrimitiveOverflowInputsReady]
  | jump targetLabel =>
      simp [InstrPrimitiveOverflowInputsReady]
  | jumpi targetLabel =>
      simp [InstrPrimitiveOverflowInputsReady]

theorem InstrCoreResidualInputsReady.of_stack_bound16_static
    {target : TargetProgram} {instr : Instr} {state : EVMState}
    (hStack : state.stack.length ≤ 16)
    (hStatic : InstrPrimitiveStaticInputsReady target instr state) :
    InstrCoreResidualInputsReady target instr state := by
  cases instr with
  | label label =>
      simp [InstrCoreResidualInputsReady, InstrControlStackRoomReady]
      omega
  | prim op =>
      exact
        ⟨InstrPrimitiveOverflowInputsReady.of_stack_bound16
            (target := target) (instr := .prim op) hStack,
          hStatic⟩
  | push value =>
      simp [InstrCoreResidualInputsReady, InstrControlStackRoomReady]
      omega
  | jump targetLabel =>
      simp [InstrCoreResidualInputsReady, InstrControlStackRoomReady]
      omega
  | jumpi targetLabel =>
      simp [InstrCoreResidualInputsReady, InstrControlStackRoomReady]
      omega

theorem InstrCoreResidualInputsReady.of_stack_headroom17_static
    {target : TargetProgram} {instr : Instr} {state : EVMState}
    (hStack : state.stack.length + 17 ≤ 1024)
    (hStatic : InstrPrimitiveStaticInputsReady target instr state) :
    InstrCoreResidualInputsReady target instr state := by
  cases instr with
  | label label =>
      simp [InstrCoreResidualInputsReady, InstrControlStackRoomReady]
      omega
  | prim op =>
      exact
        ⟨InstrPrimitiveOverflowInputsReady.of_stack_headroom17
            (target := target) (instr := .prim op) hStack,
          hStatic⟩
  | push value =>
      simp [InstrCoreResidualInputsReady, InstrControlStackRoomReady]
      omega
  | jump targetLabel =>
      simp [InstrCoreResidualInputsReady, InstrControlStackRoomReady]
      omega
  | jumpi targetLabel =>
      simp [InstrCoreResidualInputsReady, InstrControlStackRoomReady]
      omega

theorem InstrControlCoreInputsReady.of_stack_room_run
    {program : Program} {pc : Nat}
    {instr : Instr} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc instr = some emitted)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result)
    (hRoom : InstrControlStackRoomReady instr state) :
    InstrControlCoreInputsReady instr state := by
  cases instr with
  | label label =>
      simpa [InstrControlCoreInputsReady, InstrControlCoreStackReady,
        InstrControlStackRoomReady] using hRoom
  | prim op =>
      simp [InstrControlCoreInputsReady]
  | push value =>
      simpa [InstrControlCoreInputsReady, InstrControlCoreStackReady,
        InstrControlStackRoomReady] using hRoom
  | jump label =>
      simpa [InstrControlCoreInputsReady, InstrControlCoreStackReady,
        InstrControlStackRoomReady] using hRoom
  | jumpi label =>
      cases hDest : Program.labelPc program label with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          have hNonempty : 1 ≤ state.stack.length := by
            cases hStackEq : state.stack with
            | nil =>
                have hRunErr :
                    Target.runListResult
                        [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
                        , TargetInstr.jumpi ] state =
                      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
                  rw [Preservation.run_push_jumpi_result dest state]
                  simp [hStackEq, EvmYul.Stack.pop]
                have hRunPlain :
                    Target.runListResult
                        [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
                        , TargetInstr.jumpi ] state =
                      .ok result := by
                  simpa using hRun
                rw [hRunErr] at hRunPlain
                cases hRunPlain
            | cons head tail =>
                simp
          have hStackRoom : state.stack.length + 1 ≤ 1024 := by
            simpa [InstrControlStackRoomReady] using hRoom
          exact ⟨hNonempty, hStackRoom⟩

theorem InstrCoreBlockInputsReady.of_residual_no_call_create
    {program : Program} {target : TargetProgram} {pc : Nat}
    {instr : Instr} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc instr = some emitted)
    (hNoCallCreate : Instr.usesCallCreate instr = false)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result)
    (hResidual : InstrCoreResidualInputsReady target instr state) :
    InstrCoreBlockInputsReady target instr state := by
  cases instr with
  | label label =>
      simpa [InstrCoreBlockInputsReady] using
        InstrControlCoreInputsReady.of_stack_room_run hEmit hRun hResidual
  | prim op =>
      have hNoPrim : op.isCallCreate = false := by
        simpa [Instr.usesCallCreate] using hNoCallCreate
      exact
        ⟨by
          simpa [InstrPrimitiveStackJumpInputsReady] using
            InstrPrimitiveStackJumpInputsReady.of_prim_run_no_call_create
              hEmit hNoPrim hRun,
         by
          simpa [InstrCoreResidualInputsReady] using hResidual.1,
         by
          simpa [InstrCoreResidualInputsReady] using hResidual.2⟩
  | push value =>
      simpa [InstrCoreBlockInputsReady] using
        InstrControlCoreInputsReady.of_stack_room_run hEmit hRun hResidual
  | jump targetLabel =>
      simpa [InstrCoreBlockInputsReady] using
        InstrControlCoreInputsReady.of_stack_room_run hEmit hRun hResidual
  | jumpi targetLabel =>
      simpa [InstrCoreBlockInputsReady] using
        InstrControlCoreInputsReady.of_stack_room_run hEmit hRun hResidual

def XBlockInstrCoreResidualResources
    (program : Program) (target : TargetProgram) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          InstrCoreResidualInputsReady target instr blockState

structure XBlockInstrCoreInputResources
    (program : Program) (target : TargetProgram) : Prop where
  controlStack :
    ∀ {pc : Nat} {instr : Instr}
        {emitted before after : List LocatedTarget}
        {blockState : EVMState} {blockResult : StepResult},
      Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
        emitInstr? program pc instr = some emitted →
          target.code = before ++ emitted ++ after →
            Target.runListResult (emitted.map LocatedTarget.instr) blockState =
              .ok blockResult →
            InstrControlCoreInputsReady instr blockState
  primitiveStackJump :
    ∀ {pc : Nat} {instr : Instr}
        {emitted before after : List LocatedTarget}
        {blockState : EVMState} {blockResult : StepResult},
      Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
        emitInstr? program pc instr = some emitted →
          target.code = before ++ emitted ++ after →
            Target.runListResult (emitted.map LocatedTarget.instr) blockState =
              .ok blockResult →
            InstrPrimitiveStackJumpInputsReady target instr blockState
  primitiveOverflow :
    ∀ {pc : Nat} {instr : Instr}
        {emitted before after : List LocatedTarget}
        {blockState : EVMState} {blockResult : StepResult},
      Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
        emitInstr? program pc instr = some emitted →
          target.code = before ++ emitted ++ after →
            Target.runListResult (emitted.map LocatedTarget.instr) blockState =
              .ok blockResult →
            InstrPrimitiveOverflowInputsReady target instr blockState
  primitiveStatic :
    ∀ {pc : Nat} {instr : Instr}
        {emitted before after : List LocatedTarget}
        {blockState : EVMState} {blockResult : StepResult},
      Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
        emitInstr? program pc instr = some emitted →
          target.code = before ++ emitted ++ after →
            Target.runListResult (emitted.map LocatedTarget.instr) blockState =
              .ok blockResult →
            InstrPrimitiveStaticInputsReady target instr blockState

def InstrPrimitiveCoreReady (target : TargetProgram) (instr : Instr)
    (state : EVMState) : Prop :=
  match instr with
  | .prim op =>
      XNonGasCoreChecksPass (validJumps target) state
        (TargetInstr.prim op).op
  | _ => True

theorem InstrPrimitiveCoreReady.of_prim_continuing_resources
    {program : Program} {target : TargetProgram} {pc : Nat}
    {op : PrimOp} {step : PrimStep} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc (.prim op) = some emitted)
    (hStep : op.continuingStep? = some step)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result)
    (hOverflow :
      InstrPrimitiveOverflowInputsReady target (.prim op) state)
    (hStatic :
      InstrPrimitiveStaticInputsReady target (.prim op) state) :
    InstrPrimitiveCoreReady target (.prim op) state := by
  have hInputs :
      InstrPrimitiveStackJumpInputsReady target (.prim op) state :=
    InstrPrimitiveStackJumpInputsReady.of_prim_continuing_run
      hEmit hStep hRun
  exact
    XNonGasCoreChecksPass.of_inputs_overflow_static
      (by simpa [InstrPrimitiveStackJumpInputsReady] using hInputs)
      (by simpa [InstrPrimitiveOverflowInputsReady] using hOverflow)
      (by simpa [InstrPrimitiveStaticInputsReady] using hStatic)

theorem InstrPrimitiveCoreReady.of_prim_resources_no_call_create
    {program : Program} {target : TargetProgram} {pc : Nat}
    {op : PrimOp} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc (.prim op) = some emitted)
    (hNoCallCreate : op.isCallCreate = false)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result)
    (hOverflow :
      InstrPrimitiveOverflowInputsReady target (.prim op) state)
    (hStatic :
      InstrPrimitiveStaticInputsReady target (.prim op) state) :
    InstrPrimitiveCoreReady target (.prim op) state := by
  have hInputs :
      InstrPrimitiveStackJumpInputsReady target (.prim op) state :=
    InstrPrimitiveStackJumpInputsReady.of_prim_run_no_call_create
      hEmit hNoCallCreate hRun
  exact
    XNonGasCoreChecksPass.of_inputs_overflow_static
      (by simpa [InstrPrimitiveStackJumpInputsReady] using hInputs)
      (by simpa [InstrPrimitiveOverflowInputsReady] using hOverflow)
      (by simpa [InstrPrimitiveStaticInputsReady] using hStatic)

def XBlockInstrCoreReady (program : Program) (target : TargetProgram) :
    Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          InstrCoreBlockReady target instr blockState

def XBlockInstrCoreInputsReady
    (program : Program) (target : TargetProgram) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          InstrCoreBlockInputsReady target instr blockState

theorem XBlockInstrCoreInputsReady.of_residual_resources
    {program : Program} {target : TargetProgram}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hResidual : XBlockInstrCoreResidualResources program target) :
    XBlockInstrCoreInputsReady program target := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact
    InstrCoreBlockInputsReady.of_residual_no_call_create
      hEmit
      (instr_usesCallCreate_false_of_instrAtPc hNoCallCreate hAt)
      hRun
      (hResidual hAt hEmit hTargetBlock hRun)

inductive InstrCoreBlockTraceReadyFor
    {program : Program} (target : TargetProgram) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel state
          targetResult → Prop where
  | done (state : EVMState) :
      InstrCoreBlockTraceReadyFor target
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hReady : InstrCoreBlockReady target instr state)
      (hRestReady : InstrCoreBlockTraceReadyFor target hRest) :
      InstrCoreBlockTraceReadyFor target
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) {state : EVMState} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hReady : InstrCoreBlockReady target instr state) :
      InstrCoreBlockTraceReadyFor target
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

inductive InstrCoreBlockTraceInputsReadyFor
    {program : Program} (target : TargetProgram) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel state
          targetResult → Prop where
  | done {state : EVMState} :
      InstrCoreBlockTraceInputsReadyFor target
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hInputs : InstrCoreBlockInputsReady target instr state)
      (hRestReady : InstrCoreBlockTraceInputsReadyFor target hRest) :
      InstrCoreBlockTraceInputsReadyFor target
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) {state : EVMState} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hInputs : InstrCoreBlockInputsReady target instr state) :
      InstrCoreBlockTraceInputsReadyFor target
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

inductive InstrCoreBlockTraceResidualReadyFor
    {program : Program} (target : TargetProgram) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel state
          targetResult → Prop where
  | done {state : EVMState} :
      InstrCoreBlockTraceResidualReadyFor target
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hResidual : InstrCoreResidualInputsReady target instr state)
      (hRestReady : InstrCoreBlockTraceResidualReadyFor target hRest) :
      InstrCoreBlockTraceResidualReadyFor target
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) {state : EVMState} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hResidual : InstrCoreResidualInputsReady target instr state) :
      InstrCoreBlockTraceResidualReadyFor target
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

inductive InstrCoreBlockTraceStackStaticReadyFor
    {program : Program} (target : TargetProgram) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel state
          targetResult → Prop where
  | done {state : EVMState} :
      InstrCoreBlockTraceStackStaticReadyFor target
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hStack : state.stack.length ≤ 16)
      (hStatic : InstrPrimitiveStaticInputsReady target instr state)
      (hRestReady : InstrCoreBlockTraceStackStaticReadyFor target hRest) :
      InstrCoreBlockTraceStackStaticReadyFor target
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) {state : EVMState} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hStack : state.stack.length ≤ 16)
      (hStatic : InstrPrimitiveStaticInputsReady target instr state) :
      InstrCoreBlockTraceStackStaticReadyFor target
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

inductive InstrCoreBlockTraceHeadroomStaticReadyFor
    {program : Program} (target : TargetProgram) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel state
          targetResult → Prop where
  | done {state : EVMState} :
      InstrCoreBlockTraceHeadroomStaticReadyFor target
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hHeadroom : state.stack.length + 17 ≤ 1024)
      (hStatic : InstrPrimitiveStaticInputsReady target instr state)
      (hRestReady : InstrCoreBlockTraceHeadroomStaticReadyFor target hRest) :
      InstrCoreBlockTraceHeadroomStaticReadyFor target
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) {state : EVMState} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hHeadroom : state.stack.length + 17 ≤ 1024)
      (hStatic : InstrPrimitiveStaticInputsReady target instr state) :
      InstrCoreBlockTraceHeadroomStaticReadyFor target
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

inductive InstrCoreBlockTraceHeadroomReadyFor
    {program : Program} (target : TargetProgram) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel
          state targetResult → Prop where
  | done {state : EVMState} :
      InstrCoreBlockTraceHeadroomReadyFor target
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning {fuel : Nat} {state mid : EVMState}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hHeadroom : state.stack.length + 17 ≤ 1024)
      (hRestReady : InstrCoreBlockTraceHeadroomReadyFor target hRest) :
      InstrCoreBlockTraceHeadroomReadyFor target
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) {state : EVMState} {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hHeadroom : state.stack.length + 17 ≤ 1024) :
      InstrCoreBlockTraceHeadroomReadyFor target
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

theorem InstrCoreBlockTraceResidualReadyFor.of_stack_static_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hReady : InstrCoreBlockTraceStackStaticReadyFor target hTrace) :
    InstrCoreBlockTraceResidualReadyFor target hTrace := by
  induction hReady with
  | done =>
      exact InstrCoreBlockTraceResidualReadyFor.done (target := target)
  | stepRunning hAt hEmit hTargetBlock hRun hRest hStack hStatic _ ih =>
      exact InstrCoreBlockTraceResidualReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (InstrCoreResidualInputsReady.of_stack_bound16_static
          hStack hStatic)
        ih
  | stepHalted fuel hAt hEmit hTargetBlock hRun hStack hStatic =>
      exact InstrCoreBlockTraceResidualReadyFor.stepHalted
        (target := target)
        fuel
        hAt hEmit hTargetBlock hRun
        (InstrCoreResidualInputsReady.of_stack_bound16_static
          hStack hStatic)

theorem InstrCoreBlockTraceHeadroomStaticReadyFor.of_stack_static_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hReady : InstrCoreBlockTraceStackStaticReadyFor target hTrace) :
    InstrCoreBlockTraceHeadroomStaticReadyFor target hTrace := by
  induction hReady with
  | done =>
      exact InstrCoreBlockTraceHeadroomStaticReadyFor.done (target := target)
  | stepRunning hAt hEmit hTargetBlock hRun hRest hStack hStatic _ ih =>
      exact InstrCoreBlockTraceHeadroomStaticReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (by omega)
        hStatic
        ih
  | stepHalted fuel hAt hEmit hTargetBlock hRun hStack hStatic =>
      exact InstrCoreBlockTraceHeadroomStaticReadyFor.stepHalted
        (target := target)
        fuel hAt hEmit hTargetBlock hRun
        (by omega)
        hStatic

theorem InstrCoreBlockTraceHeadroomStaticReadyFor.of_headroom_perm_true
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hReady : InstrCoreBlockTraceHeadroomReadyFor target hTrace)
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hPerm : state.executionEnv.perm = true) :
    InstrCoreBlockTraceHeadroomStaticReadyFor target hTrace := by
  induction hReady with
  | done =>
      exact InstrCoreBlockTraceHeadroomStaticReadyFor.done (target := target)
  | stepRunning hAt hEmit hTargetBlock hRun hRest hHeadroom _ ih =>
      rename_i state0 mid0 _result _pc _instr emitted _before _after _hRestReady
      have hNoCallBlock :
          ∀ targetInstr ∈ emitted.map LocatedTarget.instr,
            targetInstrUsesCallCreate targetInstr = false := by
        intro targetInstr hMem
        rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
        subst targetInstr
        exact
          targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
            hNoCallCreate hAt hEmit hLocatedMem
      have hMidPermEq :
          mid0.executionEnv.perm = state0.executionEnv.perm :=
        Target.runListResult_running_preserves_perm_of_no_call_create
          hRun hNoCallBlock
      have hMidPerm : mid0.executionEnv.perm = true := by
        rw [hMidPermEq, hPerm]
      exact InstrCoreBlockTraceHeadroomStaticReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        hHeadroom
        (InstrPrimitiveStaticInputsReady.of_perm_true hPerm)
        (ih hMidPerm)
  | stepHalted fuel hAt hEmit hTargetBlock hRun hHeadroom =>
      exact InstrCoreBlockTraceHeadroomStaticReadyFor.stepHalted
        (target := target)
        fuel hAt hEmit hTargetBlock hRun
        hHeadroom
        (InstrPrimitiveStaticInputsReady.of_perm_true hPerm)

theorem InstrCoreBlockTraceResidualReadyFor.of_headroom_static_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hReady : InstrCoreBlockTraceHeadroomStaticReadyFor target hTrace) :
    InstrCoreBlockTraceResidualReadyFor target hTrace := by
  induction hReady with
  | done =>
      exact InstrCoreBlockTraceResidualReadyFor.done (target := target)
  | stepRunning hAt hEmit hTargetBlock hRun hRest hHeadroom hStatic _ ih =>
      exact InstrCoreBlockTraceResidualReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (InstrCoreResidualInputsReady.of_stack_headroom17_static
          hHeadroom hStatic)
        ih
  | stepHalted fuel hAt hEmit hTargetBlock hRun hHeadroom hStatic =>
      exact InstrCoreBlockTraceResidualReadyFor.stepHalted
        (target := target)
        fuel
        hAt hEmit hTargetBlock hRun
        (InstrCoreResidualInputsReady.of_stack_headroom17_static
          hHeadroom hStatic)

theorem InstrCoreBlockReady.of_inputs_ready
    {target : TargetProgram} {instr : Instr} {state : EVMState}
    (hInputs : InstrCoreBlockInputsReady target instr state) :
    InstrCoreBlockReady target instr state := by
  cases instr with
  | label label =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using hInputs
  | prim op =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using
        XNonGasCoreChecksPass.of_inputs_overflow_static
          hInputs.1 hInputs.2.1 hInputs.2.2
  | push value =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using hInputs
  | jump targetLabel =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using hInputs
  | jumpi targetLabel =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using hInputs

theorem InstrCoreBlockInputsReady.of_ready
    {target : TargetProgram} {instr : Instr} {state : EVMState}
    (hReady : InstrCoreBlockReady target instr state) :
    InstrCoreBlockInputsReady target instr state := by
  cases instr with
  | label label =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using hReady
  | prim op =>
      rcases hReady with
        ⟨hDelta, hStack, hJump, hJumpi, hOverflow, hStatic⟩
      exact
        ⟨⟨hDelta, hStack, hJump, hJumpi⟩, hOverflow, hStatic⟩
  | push value =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using hReady
  | jump targetLabel =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using hReady
  | jumpi targetLabel =>
      simpa [InstrCoreBlockInputsReady, InstrCoreBlockReady] using hReady

theorem instrCoreBlockInputsReady_iff_ready
    {target : TargetProgram} {instr : Instr} {state : EVMState} :
    InstrCoreBlockInputsReady target instr state ↔
      InstrCoreBlockReady target instr state :=
  ⟨InstrCoreBlockReady.of_inputs_ready,
    InstrCoreBlockInputsReady.of_ready⟩

theorem InstrCoreResidualInputsReady.of_inputs_ready
    {target : TargetProgram} {instr : Instr} {state : EVMState}
    (hInputs : InstrCoreBlockInputsReady target instr state) :
    InstrCoreResidualInputsReady target instr state := by
  cases instr with
  | label label =>
      simpa [InstrCoreResidualInputsReady, InstrControlStackRoomReady,
        InstrCoreBlockInputsReady, InstrControlCoreStackReady] using hInputs
  | prim op =>
      exact
        ⟨by
          simpa [InstrPrimitiveOverflowInputsReady,
            InstrCoreBlockInputsReady] using hInputs.2.1,
         by
          simpa [InstrPrimitiveStaticInputsReady,
            InstrCoreBlockInputsReady] using hInputs.2.2⟩
  | push value =>
      simpa [InstrCoreResidualInputsReady, InstrControlStackRoomReady,
        InstrCoreBlockInputsReady, InstrControlCoreStackReady] using hInputs
  | jump targetLabel =>
      simpa [InstrCoreResidualInputsReady, InstrControlStackRoomReady,
        InstrCoreBlockInputsReady, InstrControlCoreStackReady] using hInputs
  | jumpi targetLabel =>
      exact hInputs.2

theorem XBlockInstrCoreReady.of_inputs
    {program : Program} {target : TargetProgram}
    (hInputs : XBlockInstrCoreInputsReady program target) :
    XBlockInstrCoreReady program target := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact
    InstrCoreBlockReady.of_inputs_ready
      (hInputs hAt hEmit hTargetBlock hRun)

theorem XBlockInstrCoreInputsReady.of_ready
    {program : Program} {target : TargetProgram}
    (hReady : XBlockInstrCoreReady program target) :
    XBlockInstrCoreInputsReady program target := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact
    InstrCoreBlockInputsReady.of_ready
      (hReady hAt hEmit hTargetBlock hRun)

theorem XBlockInstrCoreInputsReady.of_resources
    {program : Program} {target : TargetProgram}
    (hResources : XBlockInstrCoreInputResources program target) :
    XBlockInstrCoreInputsReady program target := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  cases instr with
  | label label =>
      simpa [InstrCoreBlockInputsReady, InstrControlCoreInputsReady] using
        hResources.controlStack hAt hEmit hTargetBlock hRun
  | prim op =>
      exact
        ⟨by
          simpa [InstrPrimitiveStackJumpInputsReady] using
            hResources.primitiveStackJump hAt hEmit hTargetBlock hRun,
         by
          simpa [InstrPrimitiveOverflowInputsReady] using
            hResources.primitiveOverflow hAt hEmit hTargetBlock hRun,
         by
          simpa [InstrPrimitiveStaticInputsReady] using
            hResources.primitiveStatic hAt hEmit hTargetBlock hRun⟩
  | push value =>
      simpa [InstrCoreBlockInputsReady, InstrControlCoreInputsReady] using
        hResources.controlStack hAt hEmit hTargetBlock hRun
  | jump targetLabel =>
      simpa [InstrCoreBlockInputsReady, InstrControlCoreInputsReady] using
        hResources.controlStack hAt hEmit hTargetBlock hRun
  | jumpi targetLabel =>
      simpa [InstrCoreBlockInputsReady, InstrControlCoreInputsReady] using
        hResources.controlStack hAt hEmit hTargetBlock hRun

theorem XBlockInstrCoreInputResources.of_inputs_ready
    {program : Program} {target : TargetProgram}
    (hInputs : XBlockInstrCoreInputsReady program target) :
    XBlockInstrCoreInputResources program target where
  controlStack := by
    intro pc instr emitted before after blockState blockResult
      hAt hEmit hTargetBlock hRun
    have hBlock := hInputs hAt hEmit hTargetBlock hRun
    cases instr with
    | label label =>
        simpa [InstrControlCoreInputsReady, InstrCoreBlockInputsReady]
          using hBlock
    | prim op =>
        simp [InstrControlCoreInputsReady]
    | push value =>
        simpa [InstrControlCoreInputsReady, InstrCoreBlockInputsReady]
          using hBlock
    | jump targetLabel =>
        simpa [InstrControlCoreInputsReady, InstrCoreBlockInputsReady]
          using hBlock
    | jumpi targetLabel =>
        simpa [InstrControlCoreInputsReady, InstrCoreBlockInputsReady]
          using hBlock
  primitiveStackJump := by
    intro pc instr emitted before after blockState blockResult
      hAt hEmit hTargetBlock hRun
    have hBlock := hInputs hAt hEmit hTargetBlock hRun
    cases instr with
    | label label =>
        simp [InstrPrimitiveStackJumpInputsReady]
    | prim op =>
        simpa [InstrPrimitiveStackJumpInputsReady,
          InstrCoreBlockInputsReady] using hBlock.1
    | push value =>
        simp [InstrPrimitiveStackJumpInputsReady]
    | jump targetLabel =>
        simp [InstrPrimitiveStackJumpInputsReady]
    | jumpi targetLabel =>
        simp [InstrPrimitiveStackJumpInputsReady]
  primitiveOverflow := by
    intro pc instr emitted before after blockState blockResult
      hAt hEmit hTargetBlock hRun
    have hBlock := hInputs hAt hEmit hTargetBlock hRun
    cases instr with
    | label label =>
        simp [InstrPrimitiveOverflowInputsReady]
    | prim op =>
        simpa [InstrPrimitiveOverflowInputsReady,
          InstrCoreBlockInputsReady] using hBlock.2.1
    | push value =>
        simp [InstrPrimitiveOverflowInputsReady]
    | jump targetLabel =>
        simp [InstrPrimitiveOverflowInputsReady]
    | jumpi targetLabel =>
        simp [InstrPrimitiveOverflowInputsReady]
  primitiveStatic := by
    intro pc instr emitted before after blockState blockResult
      hAt hEmit hTargetBlock hRun
    have hBlock := hInputs hAt hEmit hTargetBlock hRun
    cases instr with
    | label label =>
        simp [InstrPrimitiveStaticInputsReady]
    | prim op =>
        simpa [InstrPrimitiveStaticInputsReady,
          InstrCoreBlockInputsReady] using hBlock.2.2
    | push value =>
        simp [InstrPrimitiveStaticInputsReady]
    | jump targetLabel =>
        simp [InstrPrimitiveStaticInputsReady]
    | jumpi targetLabel =>
        simp [InstrPrimitiveStaticInputsReady]

theorem XBlockInstrCoreInputResources.push_stack_room
    {program : Program} {target : TargetProgram}
    {pc : Nat} {value : Word}
    {emitted before after : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hResources : XBlockInstrCoreInputResources program target)
    (hAt :
      Program.instrAtPc program state.pc.toNat = some (pc, .push value))
    (hEmit : emitInstr? program pc (.push value) = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    state.stack.length + 1 ≤ 1024 := by
  have hReady : InstrControlCoreInputsReady (.push value) state :=
    hResources.controlStack hAt hEmit hTargetBlock hRun
  simpa [InstrControlCoreInputsReady,
    InstrControlCoreStackReady] using hReady

theorem XBlockInstrCoreInputResources.not_push_full_stack
    {program : Program} {target : TargetProgram}
    {pc : Nat} {value : Word}
    {emitted before after : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hResources : XBlockInstrCoreInputResources program target)
    (hAt :
      Program.instrAtPc program state.pc.toNat = some (pc, .push value))
    (hEmit : emitInstr? program pc (.push value) = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result)
    (hFull : state.stack.length = 1024) :
    False := by
  have hRoom :=
    hResources.push_stack_room hAt hEmit hTargetBlock hRun
  omega

theorem Target.runListResult_push32_full_stack_succeeds_without_headroom
    (state : EVMState) (value : Word)
    (hFull : state.stack.length = 1024) :
    Target.runListResult [TargetInstr.push32 value] state =
        .ok (.running
          (state.replaceStackAndIncrPC (state.stack.push value) (pcΔ := 33))) ∧
      ¬ (state.stack.length + 1 ≤ 1024) ∧
        ¬ (state.stack.length + 17 ≤ 1024) := by
  constructor
  · simp [Target.runListResult, Target.stepInstrResult, Target.stepInstr,
      TargetInstr.haltKind?, Bind.bind, Except.bind]
  · constructor <;> omega

theorem InstrPrimitiveStaticInputsReady.not_sstore_static
    {target : TargetProgram} {state : EVMState}
    (hStatic : state.executionEnv.perm = false) :
    ¬ InstrPrimitiveStaticInputsReady target (.prim .sstore) state := by
  intro hReady
  exact
    (hReady hStatic)
      (by
        simp [staticWriteSensitive, TargetInstr.op, PrimOp.toEVM])

theorem Target.runListResult_sstore_static_succeeds
    {state : EVMState} {slot value : Word}
    {rest : EvmYul.Stack Word}
    (hStack : state.stack = slot :: value :: rest) :
    ∃ post,
      Target.runListResult [TargetInstr.prim .sstore] state =
        .ok (.running post) := by
  refine
    ⟨({ state with
          toState := EvmYul.State.sstore state.toState slot value } :
        EVMState).replaceStackAndIncrPC rest, ?_⟩
  simp [Target.runListResult, Target.stepInstrResult, Target.stepInstr,
    TargetInstr.haltKind?, PrimOp.haltKind?,
    PrimOp.step, PrimOp.continuingStep?, PrimStep.run,
    EvmYul.EVM.binaryStateOp, hStack, EvmYul.Stack.pop2,
    Bind.bind, Except.bind]
  rfl

theorem InstrCoreBlockInputsReady.of_emitInstr_coreRun
    {program : Program} {target : TargetProgram} {pc : Nat}
    {instr : Instr} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc instr = some emitted)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result)
    (hCore :
      CoreRunListResult (validJumps target)
        (emitted.map LocatedTarget.instr) state result) :
    InstrCoreBlockInputsReady target instr state := by
  cases instr with
  | label label =>
      simp [emitInstr?] at hEmit
      subst emitted
      have hHeadCore := CoreRunListResult.head_core hCore
      have hOverflow :=
        (XNonGasCoreChecksPass.to_inputs_overflow_static hHeadCore).2.1
      simpa [InstrCoreBlockInputsReady, InstrControlCoreStackReady,
        TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α] using hOverflow
  | prim op =>
      simp [emitInstr?] at hEmit
      subst emitted
      have hHeadCore := CoreRunListResult.head_core hCore
      simpa [InstrCoreBlockInputsReady] using
        XNonGasCoreChecksPass.to_inputs_overflow_static hHeadCore
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      have hHeadCore := CoreRunListResult.head_core hCore
      have hOverflow :=
        (XNonGasCoreChecksPass.to_inputs_overflow_static hHeadCore).2.1
      simpa [InstrCoreBlockInputsReady, InstrControlCoreStackReady,
        TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α] using hOverflow
  | jump label =>
      cases hDest : Program.labelPc program label with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          have hHeadCore := CoreRunListResult.head_core hCore
          have hOverflow :=
            (XNonGasCoreChecksPass.to_inputs_overflow_static hHeadCore).2.1
          simpa [InstrCoreBlockInputsReady, InstrControlCoreStackReady,
            TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α] using hOverflow
  | jumpi label =>
      cases hDest : Program.labelPc program label with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          have hHeadCore := CoreRunListResult.head_core hCore
          have hOverflow :=
            (XNonGasCoreChecksPass.to_inputs_overflow_static hHeadCore).2.1
          have hStackBound : state.stack.length + 1 ≤ 1024 := by
            simpa [TargetInstr.op, EvmYul.EVM.δ, EvmYul.EVM.α]
              using hOverflow
          have hNonempty : 1 ≤ state.stack.length := by
            cases hStackEq : state.stack with
            | nil =>
                have hRunErr :
                    Target.runListResult
                        [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
                        , TargetInstr.jumpi ] state =
                      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
                  rw [Preservation.run_push_jumpi_result dest state]
                  simp [hStackEq, EvmYul.Stack.pop]
                have hRunPlain :
                    Target.runListResult
                        [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
                        , TargetInstr.jumpi ] state =
                      .ok result := by
                  simpa using hRun
                rw [hRunErr] at hRunPlain
                cases hRunPlain
            | cons head tail =>
                simp
          exact ⟨hNonempty, hStackBound⟩

theorem InstrCoreBlockReady.of_stack_bound16_and_primitive
    {program : Program} {target : TargetProgram} {pc : Nat}
    {instr : Instr} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hEmit : emitInstr? program pc instr = some emitted)
    (hStack : state.stack.length ≤ 16)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result)
    (hPrimitive : InstrPrimitiveCoreReady target instr state) :
    InstrCoreBlockReady target instr state := by
  cases instr with
  | label label =>
      simpa [InstrCoreBlockReady, InstrControlCoreStackReady] using
        (show state.stack.length ≤ 1024 by omega)
  | prim op =>
      simpa [InstrCoreBlockReady, InstrPrimitiveCoreReady] using hPrimitive
  | push value =>
      simpa [InstrCoreBlockReady, InstrControlCoreStackReady] using
        (show state.stack.length + 1 ≤ 1024 by omega)
  | jump label =>
      simpa [InstrCoreBlockReady, InstrControlCoreStackReady] using
        (show state.stack.length + 1 ≤ 1024 by omega)
  | jumpi label =>
      cases hDest : Program.labelPc program label with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          have hNonempty : 1 ≤ state.stack.length := by
            cases hStackEq : state.stack with
            | nil =>
                have hRunErr :
                    Target.runListResult
                        [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
                        , TargetInstr.jumpi ] state =
                      .error EvmYul.EVM.ExecutionException.StackUnderflow := by
                  rw [Preservation.run_push_jumpi_result dest state]
                  simp [hStackEq, EvmYul.Stack.pop]
                have hRunPlain :
                    Target.runListResult
                        [ TargetInstr.push32 (EvmYul.UInt256.ofNat dest)
                        , TargetInstr.jumpi ] state =
                      .ok result := by
                  simpa using hRun
                rw [hRunErr] at hRunPlain
                cases hRunPlain
            | cons head tail =>
                simp
          simp [InstrCoreBlockReady, InstrControlCoreStackReady,
            hNonempty]
          omega

theorem InstrCoreBlockTraceReadyFor.of_inputs_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hInputs : InstrCoreBlockTraceInputsReadyFor target hTrace) :
    InstrCoreBlockTraceReadyFor target hTrace := by
  induction hInputs with
  | done =>
      rename_i state
      exact InstrCoreBlockTraceReadyFor.done (target := target) state
  | stepRunning hAt hEmit hTargetBlock hRun hRest
      hInputs _ ih =>
      exact InstrCoreBlockTraceReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (InstrCoreBlockReady.of_inputs_ready hInputs)
        ih
  | stepHalted fuel hAt hEmit hTargetBlock hRun hInputs =>
      exact InstrCoreBlockTraceReadyFor.stepHalted
        (target := target)
        fuel
        hAt hEmit hTargetBlock hRun
        (InstrCoreBlockReady.of_inputs_ready hInputs)

theorem InstrCoreBlockTraceInputsReadyFor.of_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hReady : InstrCoreBlockTraceReadyFor target hTrace) :
    InstrCoreBlockTraceInputsReadyFor target hTrace := by
  induction hReady with
  | done =>
      rename_i state
      exact InstrCoreBlockTraceInputsReadyFor.done (target := target)
  | stepRunning hAt hEmit hTargetBlock hRun hRest
      hBlockReady _ ih =>
      exact InstrCoreBlockTraceInputsReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (InstrCoreBlockInputsReady.of_ready hBlockReady)
        ih
  | stepHalted fuel hAt hEmit hTargetBlock hRun hBlockReady =>
      exact InstrCoreBlockTraceInputsReadyFor.stepHalted
        (target := target)
        fuel
        hAt hEmit hTargetBlock hRun
        (InstrCoreBlockInputsReady.of_ready hBlockReady)

theorem InstrCoreBlockTraceInputsReadyFor.of_residual_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hResidual : InstrCoreBlockTraceResidualReadyFor target hTrace) :
    InstrCoreBlockTraceInputsReadyFor target hTrace := by
  induction hResidual with
  | done =>
      exact InstrCoreBlockTraceInputsReadyFor.done (target := target)
  | stepRunning hAt hEmit hTargetBlock hRun hRest
      hBlockResidual _ ih =>
      exact InstrCoreBlockTraceInputsReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (InstrCoreBlockInputsReady.of_residual_no_call_create
          hEmit
          (instr_usesCallCreate_false_of_instrAtPc hNoCallCreate hAt)
          hRun hBlockResidual)
        ih
  | stepHalted fuel hAt hEmit hTargetBlock hRun hBlockResidual =>
      exact InstrCoreBlockTraceInputsReadyFor.stepHalted
        (target := target)
        fuel
        hAt hEmit hTargetBlock hRun
        (InstrCoreBlockInputsReady.of_residual_no_call_create
          hEmit
          (instr_usesCallCreate_false_of_instrAtPc hNoCallCreate hAt)
          hRun hBlockResidual)

theorem instrCoreBlockTraceInputsReadyFor_iff_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult} :
    InstrCoreBlockTraceInputsReadyFor target hTrace ↔
      InstrCoreBlockTraceReadyFor target hTrace :=
  ⟨InstrCoreBlockTraceReadyFor.of_inputs_ready,
    InstrCoreBlockTraceInputsReadyFor.of_ready⟩

theorem InstrCoreBlockTraceInputsReadyFor.of_block_instr_inputs_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hInputs : XBlockInstrCoreInputsReady program target) :
    InstrCoreBlockTraceInputsReadyFor target hTrace := by
  induction hTrace with
  | done state =>
      exact InstrCoreBlockTraceInputsReadyFor.done (target := target)
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      exact InstrCoreBlockTraceInputsReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (hInputs hAt hEmit hTargetBlock hRun)
        ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state halt pc instr emitted before after
      exact InstrCoreBlockTraceInputsReadyFor.stepHalted
        (target := target)
        fuel
        hAt hEmit hTargetBlock hRun
        (hInputs hAt hEmit hTargetBlock hRun)

theorem CoreRunListResult.of_emitInstr_control
    {program : Program} {target : TargetProgram} {pc : Nat}
    {instr : Instr} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hEmit : emitInstr? program pc instr = some emitted)
    (hReady : InstrControlCoreStackReady instr state)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    CoreRunListResult (validJumps target)
      (emitted.map LocatedTarget.instr) state result := by
  cases instr with
  | label label =>
      exact
        CoreRunListResult.of_emitInstr_label
          (validJumps := validJumps target) hEmit hReady hRun
  | prim op =>
      cases hReady
  | push value =>
      exact
        CoreRunListResult.of_emitInstr_push
          (validJumps := validJumps target) hEmit hReady hRun
  | jump label =>
      exact
        CoreRunListResult.of_emitInstr_jump
          (program := program) (target := target)
          (pc := pc) (label := label) hAsm hJumpdest hEmit hReady hRun
  | jumpi label =>
      exact
        CoreRunListResult.of_emitInstr_jumpi
          (program := program) (target := target)
          (pc := pc) (label := label) hAsm hJumpdest hEmit
          hReady.1 hReady.2 hRun

theorem CoreRunListResult.of_emitInstr_coreBlockReady
    {program : Program} {target : TargetProgram} {pc : Nat}
    {instr : Instr} {emitted : List LocatedTarget}
    {state : EVMState} {result : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hEmit : emitInstr? program pc instr = some emitted)
    (hReady : InstrCoreBlockReady target instr state)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) state =
        .ok result) :
    CoreRunListResult (validJumps target)
      (emitted.map LocatedTarget.instr) state result := by
  cases instr with
  | label label =>
      exact
        CoreRunListResult.of_emitInstr_control
          (program := program) (target := target) (pc := pc)
          (instr := .label label) hAsm hJumpdest hEmit hReady hRun
  | prim op =>
      simp [emitInstr?] at hEmit
      subst emitted
      exact
        CoreRunListResult.singleton_of_core hReady (by simpa using hRun)
  | push value =>
      exact
        CoreRunListResult.of_emitInstr_control
          (program := program) (target := target) (pc := pc)
          (instr := .push value) hAsm hJumpdest hEmit hReady hRun
  | jump label =>
      exact
        CoreRunListResult.of_emitInstr_control
          (program := program) (target := target) (pc := pc)
          (instr := .jump label) hAsm hJumpdest hEmit hReady hRun
  | jumpi label =>
      exact
        CoreRunListResult.of_emitInstr_control
          (program := program) (target := target) (pc := pc)
          (instr := .jumpi label) hAsm hJumpdest hEmit hReady hRun

theorem CoreRunListResult.of_suffix_core {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {state : EVMState} {result : StepResult},
      Target.runListResult code state = .ok result →
      XRunListSuffixCoreNonGasReady validJumps code →
        CoreRunListResult validJumps code state result := by
  intro code
  induction code with
  | nil =>
      intro state result hRun _hCore
      simp [Target.runListResult] at hRun
      subst result
      exact CoreRunListResult.nil (validJumps := validJumps) state
  | cons instr rest ih =>
      intro state result hRun hCore
      have hCoreStep :
          XNonGasCoreChecksPass validJumps state instr.op :=
        hCore
          (instr := instr) (rest := rest)
          (targetState := state) (blockResult := result)
          ⟨[], by simp⟩ hRun (GasExecRel.refl state)
      rcases Target.runListResult_cons_ok_cases hRun with
        ⟨mid, hStep, hRunRest⟩ | ⟨halt, hStep, hResult⟩
      · have hCoreRest :
            XRunListSuffixCoreNonGasReady validJumps rest := by
          intro instr' rest' targetState blockResult hSuffix hRunSuffix
          intro fullState hRelState
          rcases hSuffix with ⟨pre, hPrefix⟩
          exact
            hCore
              (instr := instr') (rest := rest')
              (targetState := targetState)
              (blockResult := blockResult)
              ⟨instr :: pre, by simp [hPrefix]⟩
              hRunSuffix hRelState
        exact CoreRunListResult.stepRunning hCoreStep hStep
          (ih hRunRest hCoreRest)
      · subst result
        exact CoreRunListResult.stepHalted hCoreStep hStep

theorem CoreRunListResult.to_path_core_checks
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      CoreRunListResult validJumps code target targetResult →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      GasExecRel full target →
      XRunListPathCoreChecksReady validJumps code target full
        targetResult := by
  intro code target full targetResult hCore
  induction hCore generalizing full with
  | nil state =>
      intro _hNoCall hRel
      exact ⟨rfl, hRel⟩
  | stepRunning hCoreStep hStep hRest ih =>
      rename_i instr rest state mid result
      intro hNoCall hRel
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCall instr (by simp)
      have hNoCallRest :
          ∀ instr' ∈ rest, targetInstrUsesCallCreate instr' = false := by
        intro instr' hMemRest
        exact hNoCall instr' (by simp [hMemRest])
      have hCoreFull :
          XNonGasCoreChecksPass validJumps full instr.op :=
        (XNonGasCoreChecksPass_iff_of_gasExecRel hRel).2 hCoreStep
      simp [XRunListPathCoreChecksReady, hRel, hCoreFull, hStep]
      intro stepFuel fullPost hStepFull
      have hTargetStep :
          Target.stepInstr instr state = .ok mid :=
        (Target.stepInstrResult_running_stepInstr hStep).1
      have hRelPost : GasExecRel fullPost mid :=
        EVM_step_targetInstr_preserves_gasExecRel_of_ok
          (fuel := stepFuel.succ)
          (gasCost :=
            EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
          hNoCallInstr (hRel.memoryGasState_left (op := instr.op))
          hTargetStep hStepFull
      exact ih hNoCallRest hRelPost
  | stepHalted hCoreStep hStep =>
      rename_i instr rest state halt
      intro _hNoCall hRel
      have hCoreFull :
          XNonGasCoreChecksPass validJumps full instr.op :=
        (XNonGasCoreChecksPass_iff_of_gasExecRel hRel).2 hCoreStep
      simp [XRunListPathCoreChecksReady, hRel, hCoreFull, hStep]

theorem XRunListPathChecksReady.of_path_core_noReturnDataCopy_noCallCreate
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      XRunListPathCoreChecksReady validJumps code target full targetResult →
      (∀ instr ∈ code, targetInstrNoReturnDataCopy instr = true) →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      XRunListPathChecksReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hCore _hNoReturnDataCopy _hNoCallCreate
      simpa [XRunListPathCoreChecksReady, XRunListPathChecksReady] using hCore
  | cons instr rest ih =>
      intro target full targetResult hCore hNoReturnDataCopy hNoCallCreate
      have hMem : instr ∈ instr :: rest := by simp
      have hNoReturnOp :
          instr.op ≠ EvmYul.Operation.RETURNDATACOPY :=
        targetInstr_op_ne_returnDataCopy_of_noReturnDataCopy
          (hNoReturnDataCopy instr hMem)
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCallCreate instr hMem
      have hNoCreate : instr.op.isCreate = false :=
        targetInstr_op_isCreate_false_of_usesCallCreate_false hNoCallInstr
      have hNoReturnRest :
          ∀ instr' ∈ rest, targetInstrNoReturnDataCopy instr' = true := by
        intro instr' hMemRest
        exact hNoReturnDataCopy instr' (by simp [hMemRest])
      have hNoCallRest :
          ∀ instr' ∈ rest, targetInstrUsesCallCreate instr' = false := by
        intro instr' hMemRest
        exact hNoCallCreate instr' (by simp [hMemRest])
      simp [XRunListPathCoreChecksReady] at hCore
      rcases hCore with ⟨hRel, hCoreStep, hTail⟩
      have hNonGasStep :
          XNonGasChecksPass validJumps full instr.op :=
        XNonGasChecksPass.of_core_no_returnDataCopy_no_create
          hCoreStep hNoReturnOp hNoCreate
      simp [XRunListPathChecksReady, hRel, hNonGasStep, hNoCallInstr]
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hTail
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hTail
              exact hTail
          | running targetPost =>
              simp [hStepResult] at hTail
              intro stepFuel fullPost hStep
              exact ih (hTail hStep) hNoReturnRest hNoCallRest

theorem XRunListPathChecksReady.of_path_core_returnDataCopyBounds_noCallCreate
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      XRunListPathCoreChecksReady validJumps code target full targetResult →
      XRunListPathReturnDataCopyBoundsReady code target full targetResult →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      XRunListPathChecksReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hCore _hReturnDataCopyBounds
        _hNoCallCreate
      simpa [XRunListPathCoreChecksReady, XRunListPathChecksReady] using hCore
  | cons instr rest ih =>
      intro target full targetResult hCore hReturnDataCopyBounds hNoCallCreate
      have hMem : instr ∈ instr :: rest := by simp
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCallCreate instr hMem
      have hNoCreate : instr.op.isCreate = false :=
        targetInstr_op_isCreate_false_of_usesCallCreate_false hNoCallInstr
      have hNoCallRest :
          ∀ instr' ∈ rest, targetInstrUsesCallCreate instr' = false := by
        intro instr' hMemRest
        exact hNoCallCreate instr' (by simp [hMemRest])
      simp [XRunListPathCoreChecksReady] at hCore
      rcases hCore with ⟨hRel, hCoreStep, hTailCore⟩
      simp [XRunListPathReturnDataCopyBoundsReady] at hReturnDataCopyBounds
      rcases hReturnDataCopyBounds with
        ⟨_hRelBounds, hReturnDataCopyStep, hTailBounds⟩
      have hNonGasStep :
          XNonGasChecksPass validJumps full instr.op :=
        XNonGasChecksPass.of_core_returnDataCopyBounds_no_create
          hCoreStep hReturnDataCopyStep hNoCreate
      simp [XRunListPathChecksReady, hRel, hNonGasStep, hNoCallInstr]
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hTailCore
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hTailCore hTailBounds
              exact hTailCore
          | running targetPost =>
              simp [hStepResult] at hTailCore hTailBounds
              intro stepFuel fullPost hStep
              exact
                ih (hTailCore hStep) (hTailBounds hStep) hNoCallRest

theorem XRunListPathCoreChecksReady.of_suffix_core_noCallCreate
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixCoreNonGasReady validJumps code →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      GasExecRel full target →
      XRunListPathCoreChecksReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hCore _hNoCallCreate hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hCore hNoCallCreate hRel
      have hCoreStep :
          XNonGasCoreChecksPass validJumps full instr.op :=
        hCore
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := targetResult)
          ⟨[], by simp⟩ hRun hRel
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCallCreate instr (by simp)
      simp [XRunListPathCoreChecksReady, hRel, hCoreStep]
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          change False
          rw [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok targetResult at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              change targetResult = .halted halt
              rw [Target.runListResult, hStepResult] at hRun
              change
                (Except.ok (.halted halt) : Except EVMException StepResult) =
                  .ok targetResult at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (fuel := stepFuel.succ)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallInstr (hRel.memoryGasState_left (op := instr.op))
                  (Target.stepInstrResult_running_stepInstr
                    hStepResult).1 hStep
              have hCoreRest :
                  XRunListSuffixCoreNonGasReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                intro fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hCore
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              have hNoCallRest :
                  ∀ instr' ∈ rest,
                    targetInstrUsesCallCreate instr' = false := by
                intro instr' hMemRest
                exact hNoCallCreate instr' (by simp [hMemRest])
              exact ih hRun hCoreRest hNoCallRest hRelPost

theorem XRunListPathDecodeReady.singleton_of_decode
    {instr : TargetInstr} {target full : EVMState} {result : StepResult}
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some (instr.op, instr.arg))
    (hRun : Target.runListResult [instr] target = .ok result) :
    XRunListPathDecodeReady [instr] target full result := by
  simp [XRunListPathDecodeReady, hDecode]
  cases hStepResult : Target.stepInstrResult instr target with
  | error err =>
      simp [Target.runListResult, hStepResult] at hRun
      cases hRun
  | ok stepResult =>
      cases stepResult <;> simp

theorem XRunListPathDecodeReady.push32_pair
    {value : Word} {next : TargetInstr}
    {target full : EVMState} {result : StepResult}
    (hDecode :
      EvmYul.EVM.decode full.executionEnv.code full.pc =
        some ((TargetInstr.push32 value).op, (TargetInstr.push32 value).arg))
    (hDecodeNext :
      ∀ {stepFuel : Nat} {fullPost : EVMState},
        EvmYul.EVM.step stepFuel.succ
            (EvmYul.EVM.C' (memoryGasState full (TargetInstr.push32 value).op)
              (TargetInstr.push32 value).op)
            (some ((TargetInstr.push32 value).op,
              (TargetInstr.push32 value).arg))
            (memoryGasState full (TargetInstr.push32 value).op) =
          .ok fullPost →
        EvmYul.EVM.decode fullPost.executionEnv.code fullPost.pc =
          some (next.op, next.arg))
    (hRun :
      Target.runListResult [TargetInstr.push32 value, next] target =
        .ok result) :
    XRunListPathDecodeReady [TargetInstr.push32 value, next] target full
      result := by
  let targetPost :=
    EvmYul.EVM.State.replaceStackAndIncrPC target
      (target.stack.push value) (pcΔ := 33)
  have hRunRest :
      Target.runListResult [next] targetPost = .ok result := by
    simpa [targetPost, Target.runListResult, Target.stepInstrResult,
      Target.stepInstr] using hRun
  change
    EvmYul.EVM.decode full.executionEnv.code full.pc =
        some ((TargetInstr.push32 value).op, (TargetInstr.push32 value).arg) ∧
      (∀ {stepFuel : Nat} {fullPost : EVMState},
        EvmYul.EVM.step stepFuel.succ
            (EvmYul.EVM.C'
              (memoryGasState full (TargetInstr.push32 value).op)
              (TargetInstr.push32 value).op)
            (some ((TargetInstr.push32 value).op,
              (TargetInstr.push32 value).arg))
            (memoryGasState full (TargetInstr.push32 value).op) =
          .ok fullPost →
        XRunListPathDecodeReady [next] targetPost fullPost result)
  refine ⟨hDecode, ?_⟩
  intro stepFuel fullPost hStep
  exact
    XRunListPathDecodeReady.singleton_of_decode
      (hDecodeNext hStep) hRunRest

theorem XRunListPathDecodeReady.of_emitInstr
    {program : Program} {target : TargetProgram}
    {targetState fullState : EVMState}
    {pc : Nat} {instr : Instr}
    {emitted before after : List LocatedTarget} {blockResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hAt : Program.instrAtPc program targetState.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) targetState =
        .ok blockResult)
    (hRel : GasExecRel fullState targetState)
    (hCode : fullState.executionEnv.code = Bytecode.encodeTarget target) :
    XRunListPathDecodeReady (emitted.map LocatedTarget.instr) targetState
      fullState blockResult := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      subst emitted
      have hDecode :
          EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
            some (TargetInstr.jumpdest.op, TargetInstr.jumpdest.arg) :=
        decode_of_gasExecRel_instrAt_mem_emitted_of_safety
          (located := { pc := pc, instr := TargetInstr.jumpdest })
          hEncoding hSafety hAt hTargetBlock (by simp) rfl hRel hCode
      exact XRunListPathDecodeReady.singleton_of_decode hDecode (by simpa using hRun)
  | prim op =>
      simp [emitInstr?] at hEmit
      subst emitted
      have hDecode :
          EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
            some ((TargetInstr.prim op).op, (TargetInstr.prim op).arg) :=
        decode_of_gasExecRel_instrAt_mem_emitted_of_safety
          (located := { pc := pc, instr := TargetInstr.prim op })
          hEncoding hSafety hAt hTargetBlock (by simp) rfl hRel hCode
      exact XRunListPathDecodeReady.singleton_of_decode hDecode (by simpa using hRun)
  | push value =>
      simp [emitInstr?] at hEmit
      subst emitted
      have hDecode :
          EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
            some ((TargetInstr.push32 value).op,
              (TargetInstr.push32 value).arg) :=
        decode_of_gasExecRel_instrAt_mem_emitted_of_safety
          (located := { pc := pc, instr := TargetInstr.push32 value })
          hEncoding hSafety hAt hTargetBlock (by simp) rfl hRel hCode
      exact XRunListPathDecodeReady.singleton_of_decode hDecode (by simpa using hRun)
  | jump label =>
      cases hDest : Program.labelPc program label with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          have hEmitPair :
              emitInstr? program pc (Instr.jump label) =
                some
                  [ { pc := pc,
                      instr := TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest) },
                    { pc := pc + Instr.push32Size,
                      instr := TargetInstr.jump } ] := by
            simp [emitInstr?, hDest]
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          have hHeadDecode :
              EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
                some
                  ((TargetInstr.push32 (EvmYul.UInt256.ofNat dest)).op,
                    (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)).arg) :=
            decode_of_gasExecRel_instrAt_mem_emitted_of_safety
              (located :=
                { pc := pc,
                  instr := TargetInstr.push32
                    (EvmYul.UInt256.ofNat dest) })
              hEncoding hSafety hAt hTargetBlock (by simp) rfl hRel hCode
          have hNextDecode :
              ∀ {stepFuel : Nat} {fullPost : EVMState},
                EvmYul.EVM.step stepFuel.succ
                    (EvmYul.EVM.C'
                      (memoryGasState fullState
                        (TargetInstr.push32
                          (EvmYul.UInt256.ofNat dest)).op)
                      (TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest)).op)
                    (some
                      ((TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest)).op,
                        (TargetInstr.push32
                          (EvmYul.UInt256.ofNat dest)).arg))
                    (memoryGasState fullState
                      (TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest)).op) =
                  .ok fullPost →
                EvmYul.EVM.decode fullPost.executionEnv.code fullPost.pc =
                  some (TargetInstr.jump.op, TargetInstr.jump.arg) := by
            intro stepFuel fullPost hStep
            exact
              decode_jump_after_push32_step_of_emitInstr
                hEncoding hSafety hAt hDest hEmitPair hTargetBlock hRel
                hCode hStep
          exact
            XRunListPathDecodeReady.push32_pair hHeadDecode hNextDecode
              (by simpa using hRun)
  | jumpi label =>
      cases hDest : Program.labelPc program label with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          have hEmitPair :
              emitInstr? program pc (Instr.jumpi label) =
                some
                  [ { pc := pc,
                      instr := TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest) },
                    { pc := pc + Instr.push32Size,
                      instr := TargetInstr.jumpi } ] := by
            simp [emitInstr?, hDest]
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          have hHeadDecode :
              EvmYul.EVM.decode fullState.executionEnv.code fullState.pc =
                some
                  ((TargetInstr.push32 (EvmYul.UInt256.ofNat dest)).op,
                    (TargetInstr.push32 (EvmYul.UInt256.ofNat dest)).arg) :=
            decode_of_gasExecRel_instrAt_mem_emitted_of_safety
              (located :=
                { pc := pc,
                  instr := TargetInstr.push32
                    (EvmYul.UInt256.ofNat dest) })
              hEncoding hSafety hAt hTargetBlock (by simp) rfl hRel hCode
          have hNextDecode :
              ∀ {stepFuel : Nat} {fullPost : EVMState},
                EvmYul.EVM.step stepFuel.succ
                    (EvmYul.EVM.C'
                      (memoryGasState fullState
                        (TargetInstr.push32
                          (EvmYul.UInt256.ofNat dest)).op)
                      (TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest)).op)
                    (some
                      ((TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest)).op,
                        (TargetInstr.push32
                          (EvmYul.UInt256.ofNat dest)).arg))
                    (memoryGasState fullState
                      (TargetInstr.push32
                        (EvmYul.UInt256.ofNat dest)).op) =
                  .ok fullPost →
                EvmYul.EVM.decode fullPost.executionEnv.code fullPost.pc =
                  some (TargetInstr.jumpi.op, TargetInstr.jumpi.arg) := by
            intro stepFuel fullPost hStep
            exact
              decode_jumpi_after_push32_step_of_emitInstr
                hEncoding hSafety hAt hDest hEmitPair hTargetBlock hRel
                hCode hStep
          exact
            XRunListPathDecodeReady.push32_pair hHeadDecode hNextDecode
              (by simpa using hRun)

theorem XRunListPathReady.of_decode_checks_and_budget
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListPathDecodeReady code target full targetResult →
      XRunListPathChecksReady validJumps code target full targetResult →
      XRunListBodyPreservesGas code →
      XRunListGasBudget code target ≤ full.gasAvailable.toNat →
      XRunListPathReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hDecode hChecks _hBody _hBudget
      simpa [Target.runListResult] using hChecks
  | cons instr rest ih =>
      intro target full targetResult hRun hDecodeReady hChecksReady hBody
        hBudget
      rcases hBody with ⟨hBodyInstr, hBodyRest⟩
      rcases hDecodeReady with ⟨hDecode, hDecodeRest⟩
      rcases hChecksReady with
        ⟨hRel, hNonGasStep, hNoCallCreate, hChecksRest⟩
      have hReqBudget :
          XGasRequiredAt target instr.op ≤
            XRunListGasBudget (instr :: rest) target := by
        simp [XRunListGasBudget]
      have hRequired :
          XGasRequiredAt full instr.op ≤ full.gasAvailable.toNat := by
        rw [XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
          hNoCallCreate hRel]
        exact le_trans hReqBudget hBudget
      simp only [XRunListPathReady]
      refine
        ⟨hRel, hDecode, hNonGasStep, hRequired, hNoCallCreate, ?_⟩
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hChecksRest
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hChecksRest
              exact hChecksRest
          | running targetPost =>
              simp [hStepResult] at hDecodeRest hChecksRest
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              have hBudgetRun :
                  XRunListGasBudget (instr :: rest) target =
                    XGasRequiredAt target instr.op +
                      XRunListGasBudget rest targetPost := by
                simp [XRunListGasBudget, hStepResult]
              have hBudgetStep :
                  XGasRequiredAt full instr.op +
                      XRunListGasBudget rest targetPost ≤
                    full.gasAvailable.toNat := by
                rw [hBudgetRun] at hBudget
                rw [←
                  XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
                    hNoCallCreate hRel] at hBudget
                exact hBudget
              have hStepBody :
                  EvmYul.step instr.op instr.arg
                      (xBodyState full instr.op) =
                    .ok fullPost := by
                rw [← EVM_step_targetInstr_eq_xBodyState
                  (fuel := stepFuel) (state := full) (instr := instr)
                  hNoCallCreate]
                exact hStep
              have hRestBudgetBody :
                  XRunListGasBudget rest targetPost ≤
                    (xBodyState full instr.op).gasAvailable.toNat :=
                xBodyState_gasAvailable_toNat_of_required hBudgetStep
              have hRestBudget :
                  XRunListGasBudget rest targetPost ≤
                    fullPost.gasAvailable.toNat := by
                rw [hBodyInstr hStepBody]
                exact hRestBudgetBody
              exact
                ih hRun (hDecodeRest hStep) (hChecksRest hStep) hBodyRest
                  hRestBudget

theorem XRunListPathReady.of_emitInstr_checks_and_budget
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word}
    {blockState fullState : EVMState}
    {pc : Nat} {instr : Instr}
    {emitted before after : List LocatedTarget} {blockResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hAt : Program.instrAtPc program blockState.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) blockState =
        .ok blockResult)
    (hRel : GasExecRel fullState blockState)
    (hCode : fullState.executionEnv.code = Bytecode.encodeTarget target)
    (hChecks :
      XRunListPathChecksReady validJumps (emitted.map LocatedTarget.instr)
        blockState fullState blockResult)
    (hNoCallCreate :
      ∀ targetInstr ∈ emitted.map LocatedTarget.instr,
        targetInstrUsesCallCreate targetInstr = false)
    (hBudget :
      XRunListGasBudget (emitted.map LocatedTarget.instr) blockState ≤
        fullState.gasAvailable.toNat) :
    XRunListPathReady validJumps (emitted.map LocatedTarget.instr)
      blockState fullState blockResult := by
  have hDecode :
      XRunListPathDecodeReady (emitted.map LocatedTarget.instr)
        blockState fullState blockResult :=
    XRunListPathDecodeReady.of_emitInstr hEncoding hSafety hAt hEmit
      hTargetBlock hRun hRel hCode
  exact
    XRunListPathReady.of_decode_checks_and_budget
      (validJumps := validJumps)
      hRun hDecode hChecks
      (XRunListBodyPreservesGas.of_all_no_call_create hNoCallCreate)
      hBudget

theorem XRunListPathChecksReady.of_suffix_nonGas
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixNonGasReady validJumps code →
      GasExecRel full target →
      XRunListPathChecksReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hNonGas hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hNonGas hRel
      obtain ⟨_hDecode, hNonGasStep, hNoCallCreate⟩ :=
        hNonGas
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := targetResult)
          ⟨[], by simp⟩ hRun hRel
      simp [XRunListPathChecksReady, hRel, hNonGasStep, hNoCallCreate]
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [Target.runListResult, hStepResult] at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [Target.runListResult, hStepResult] at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (fuel := stepFuel.succ)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
                  (Target.stepInstrResult_running_stepInstr
                    hStepResult).1 hStep
              have hNonGasRest :
                  XRunListSuffixNonGasReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                intro fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hNonGas
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              exact ih hRun hNonGasRest hRelPost

theorem XRunListPathChecksReady.of_suffix_core_noReturnDataCopy_noCallCreate
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixCoreNonGasReady validJumps code →
      (∀ instr ∈ code, targetInstrNoReturnDataCopy instr = true) →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      GasExecRel full target →
      XRunListPathChecksReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hCore _hNoReturnDataCopy
        _hNoCallCreate hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hCore hNoReturnDataCopy
        hNoCallCreate hRel
      have hCoreStep :
          XNonGasCoreChecksPass validJumps full instr.op :=
        hCore
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := targetResult)
          ⟨[], by simp⟩ hRun hRel
      have hMem : instr ∈ instr :: rest := by simp
      have hNoReturnOp :
          instr.op ≠ EvmYul.Operation.RETURNDATACOPY :=
        targetInstr_op_ne_returnDataCopy_of_noReturnDataCopy
          (hNoReturnDataCopy instr hMem)
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCallCreate instr hMem
      have hNoCreate : instr.op.isCreate = false :=
        targetInstr_op_isCreate_false_of_usesCallCreate_false hNoCallInstr
      have hNonGasStep :
          XNonGasChecksPass validJumps full instr.op :=
        XNonGasChecksPass.of_core_no_returnDataCopy_no_create
          hCoreStep hNoReturnOp hNoCreate
      simp [XRunListPathChecksReady, hRel, hNonGasStep, hNoCallInstr]
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [Target.runListResult, hStepResult] at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [Target.runListResult, hStepResult] at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (fuel := stepFuel.succ)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallInstr (hRel.memoryGasState_left (op := instr.op))
                  (Target.stepInstrResult_running_stepInstr
                    hStepResult).1 hStep
              have hCoreRest :
                  XRunListSuffixCoreNonGasReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                intro fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hCore
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              have hNoReturnRest :
                  ∀ instr' ∈ rest,
                    targetInstrNoReturnDataCopy instr' = true := by
                intro instr' hMemRest
                exact hNoReturnDataCopy instr' (by simp [hMemRest])
              have hNoCallRest :
                  ∀ instr' ∈ rest,
                    targetInstrUsesCallCreate instr' = false := by
                intro instr' hMemRest
                exact hNoCallCreate instr' (by simp [hMemRest])
              exact
                ih hRun hCoreRest hNoReturnRest hNoCallRest hRelPost

theorem XRunListPathChecksReady.of_suffix_core_returnDataCopyBounds_noCallCreate
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixCoreNonGasReady validJumps code →
      XRunListPathReturnDataCopyBoundsReady code target full targetResult →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      GasExecRel full target →
      XRunListPathChecksReady validJumps code target full targetResult := by
  intro code target full targetResult hRun hCore hReturnDataCopyBounds
    hNoCallCreate hRel
  exact
    XRunListPathChecksReady.of_path_core_returnDataCopyBounds_noCallCreate
      (XRunListPathCoreChecksReady.of_suffix_core_noCallCreate
        hRun hCore hNoCallCreate hRel)
      hReturnDataCopyBounds
      hNoCallCreate

theorem XRunListPathReady.of_suffix_ready {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixReady validJumps code →
      GasExecRel full target →
      XRunListPathReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hReady hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hReady hRel
      obtain ⟨hDecode, hNonGas, hGas, hNoCallCreate⟩ :=
        hReady
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := targetResult)
          ⟨[], by simp⟩ hRun hRel
      simp [XRunListPathReady, hRel, hDecode, hNonGas, hGas,
        hNoCallCreate]
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok targetResult at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [Target.runListResult, hStepResult] at hRun
              change
                (Except.ok (StepResult.halted halt) :
                    Except EVMException StepResult) =
                  .ok targetResult at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (fuel := stepFuel.succ)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
                  (Target.stepInstrResult_running_stepInstr
                    hStepResult).1 hStep
              have hReadyRest :
                  XRunListSuffixReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                intro fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hReady
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              exact ih hRun hReadyRest hRelPost

theorem XRunListPathReady.of_nonGas_and_budget {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixNonGasReady validJumps code →
      XRunListBodyPreservesGas code →
      XRunListGasBudget code target ≤ full.gasAvailable.toNat →
      GasExecRel full target →
      XRunListPathReady validJumps code target full targetResult := by
  intro code
  induction code with
  | nil =>
      intro target full targetResult hRun _hNonGas _hBody _hBudget hRel
      simp [Target.runListResult] at hRun
      subst targetResult
      exact ⟨rfl, hRel⟩
  | cons instr rest ih =>
      intro target full targetResult hRun hNonGas hBody hBudget hRel
      rcases hBody with ⟨hBodyInstr, hBodyRest⟩
      obtain ⟨hDecode, hNonGasStep, hNoCallCreate⟩ :=
        hNonGas
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := targetResult)
          ⟨[], by simp⟩ hRun hRel
      have hReqBudget :
          XGasRequiredAt target instr.op ≤
            XRunListGasBudget (instr :: rest) target := by
        simp [XRunListGasBudget]
      have hRequired :
          XGasRequiredAt full instr.op ≤ full.gasAvailable.toNat := by
        rw [XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
          hNoCallCreate hRel]
        exact le_trans hReqBudget hBudget
      simp only [XRunListPathReady]
      refine
        ⟨hRel, hDecode, hNonGasStep, hRequired, hNoCallCreate, ?_⟩
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok targetResult at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [Target.runListResult, hStepResult] at hRun
              cases hRun
              rfl
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              intro stepFuel fullPost hStep
              obtain ⟨hTargetStep, _hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              have hRelPost :
                  GasExecRel fullPost targetPost :=
                EVM_step_targetInstr_preserves_gasExecRel_of_ok
                  (fuel := stepFuel.succ)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
                  hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep hStep
              have hStepBody :
                  EvmYul.step instr.op instr.arg
                      (xBodyState full instr.op) =
                    .ok fullPost := by
                rw [← EVM_step_targetInstr_eq_xBodyState
                  (fuel := stepFuel) (state := full) (instr := instr)
                  hNoCallCreate]
                exact hStep
              have hBudgetStep :
                  XGasRequiredAt full instr.op +
                      XRunListGasBudget rest targetPost ≤
                    full.gasAvailable.toNat := by
                have hBudgetRun :
                    XRunListGasBudget (instr :: rest) target =
                      XGasRequiredAt target instr.op +
                        XRunListGasBudget rest targetPost := by
                  simp [XRunListGasBudget, hStepResult]
                rw [hBudgetRun] at hBudget
                rw [←
                  XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
                    hNoCallCreate hRel] at hBudget
                exact hBudget
              have hRestBudgetBody :
                  XRunListGasBudget rest targetPost ≤
                    (xBodyState full instr.op).gasAvailable.toNat :=
                xBodyState_gasAvailable_toNat_of_required hBudgetStep
              have hRestBudget :
                  XRunListGasBudget rest targetPost ≤
                    fullPost.gasAvailable.toNat := by
                rw [hBodyInstr hStepBody]
                exact hRestBudgetBody
              have hNonGasRest :
                  XRunListSuffixNonGasReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                  fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hNonGas
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              exact
                ih hRun hNonGasRest hBodyRest hRestBudget hRelPost

theorem XRunListPathReady.of_nonGas_no_call_create_and_budget
    {validJumps : Array Word}
    {code : List TargetInstr} {target full : EVMState}
    {targetResult : StepResult}
    (hRun : Target.runListResult code target = .ok targetResult)
    (hNonGas : XRunListSuffixNonGasReady validJumps code)
    (hNoCallCreate :
      ∀ instr ∈ code, targetInstrUsesCallCreate instr = false)
    (hBudget : XRunListGasBudget code target ≤ full.gasAvailable.toNat)
    (hRel : GasExecRel full target) :
    XRunListPathReady validJumps code target full targetResult := by
  exact XRunListPathReady.of_nonGas_and_budget hRun hNonGas
    (XRunListBodyPreservesGas.of_all_no_call_create hNoCallCreate)
    hBudget hRel

theorem XRunListPathReady.running_prefix_of_nonGas_no_call_create_and_budget
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full targetFinal : EVMState}
      {restBudget : Nat},
      Target.runListResult code target = .ok (.running targetFinal) →
      XRunListSuffixNonGasReady validJumps code →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      XRunListGasBudget code target + restBudget ≤
        full.gasAvailable.toNat →
      GasExecRel full target →
      ∃ prefixFuel fullFinal,
        GasExecRel fullFinal targetFinal ∧
          XPrefixTrace validJumps prefixFuel full fullFinal ∧
          restBudget ≤ fullFinal.gasAvailable.toNat := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal restBudget hRun _hNonGas _hNoCall
        hBudget hRel
      simp [Target.runListResult] at hRun
      subst targetFinal
      simp [XRunListGasBudget] at hBudget
      exact ⟨0, full, hRel, XPrefixTrace.done full, by simpa using hBudget⟩
  | cons instr rest ih =>
      intro target full targetFinal restBudget hRun hNonGas hNoCall hBudget
        hRel
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCall instr (by simp)
      obtain ⟨hDecode, hNonGasStep, _hNoCallFromReady⟩ :=
        hNonGas
          (instr := instr) (rest := rest)
          (targetState := target) (blockResult := .running targetFinal)
          ⟨[], by simp⟩ hRun hRel
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          rw [Target.runListResult, hStepResult] at hRun
          change
            (Except.error err : Except EVMException StepResult) =
              .ok (.running targetFinal) at hRun
          cases hRun
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              rw [Target.runListResult, hStepResult] at hRun
              change
                (Except.ok (StepResult.halted halt) :
                    Except EVMException StepResult) =
                  .ok (.running targetFinal) at hRun
              cases hRun
          | running targetPost =>
              simp [Target.runListResult, hStepResult] at hRun
              have hBudgetRun :
                  XRunListGasBudget (instr :: rest) target =
                    XGasRequiredAt target instr.op +
                      XRunListGasBudget rest targetPost := by
                simp [XRunListGasBudget, hStepResult]
              have hBudgetStep :
                  XGasRequiredAt full instr.op +
                      (XRunListGasBudget rest targetPost + restBudget) ≤
                    full.gasAvailable.toNat := by
                rw [hBudgetRun] at hBudget
                rw [←
                  XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
                    hNoCallInstr hRel] at hBudget
                omega
              have hRequired :
                  XGasRequiredAt full instr.op ≤ full.gasAvailable.toNat := by
                omega
              have hChecks :
                  XStepChecksPass validJumps full instr.op :=
                XStepChecksPass.of_nonGas_required_le hNonGasStep hRequired
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallInstr
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              have hStepBody :
                  EvmYul.step instr.op instr.arg
                      (xBodyState full instr.op) =
                    .ok fullPost := by
                rw [← EVM_step_targetInstr_eq_xBodyState
                  (fuel := 0) (state := full) (instr := instr)
                  hNoCallInstr]
                exact hStep
              have hRestBudgetBody :
                  XRunListGasBudget rest targetPost + restBudget ≤
                    (xBodyState full instr.op).gasAvailable.toNat :=
                xBodyState_gasAvailable_toNat_of_required hBudgetStep
              have hRestBudget :
                  XRunListGasBudget rest targetPost + restBudget ≤
                    fullPost.gasAvailable.toNat := by
                rw [TargetInstrBodyPreservesGas.of_no_call_create
                  hNoCallInstr hStepBody]
                exact hRestBudgetBody
              have hNonGasRest :
                  XRunListSuffixNonGasReady validJumps rest := by
                intro instr' rest' targetState blockResult hSuffix hRunSuffix
                  fullState hRelState
                rcases hSuffix with ⟨pre, hPrefix⟩
                exact
                  hNonGas
                    (instr := instr') (rest := rest')
                    (targetState := targetState)
                    (blockResult := blockResult)
                    ⟨instr :: pre, by simp [hPrefix]⟩
                    hRunSuffix hRelState
              have hNoCallRest :
                  ∀ instr' ∈ rest,
                    targetInstrUsesCallCreate instr' = false := by
                intro instr' hMem
                exact hNoCall instr' (by simp [hMem])
              obtain
                ⟨fuelTail, fullFinal, hRelFinal, hPrefixTail,
                  hRestFinal⟩ :=
                ih hRun hNonGasRest hNoCallRest hRestBudget hRelPost
              have hStepAll :
                  ∀ tailFuel : Nat,
                    EvmYul.EVM.step tailFuel.succ
                        (EvmYul.EVM.C' (memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (memoryGasState full instr.op) =
                      .ok fullPost := by
                intro tailFuel
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallInstr]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallInstr] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelTail.succ, fullFinal, hRelFinal,
                  XPrefixTrace.running hDecode hChecks hStepAll hNoHalt
                    hPrefixTail,
                  hRestFinal⟩

theorem XRunListPathReady.running_prefix {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full targetFinal : EVMState},
      XRunListPathReady validJumps code target full (.running targetFinal) →
      ∃ fuel fullFinal,
        GasExecRel fullFinal targetFinal ∧
          XPrefixTrace validJumps fuel full fullFinal := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal hReady
      rcases hReady with ⟨hResult, hRel⟩
      cases hResult
      exact ⟨0, full, hRel, XPrefixTrace.done full⟩
  | cons instr rest ih =>
      intro target full targetFinal hReady
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          XStepChecksPass validJumps full instr.op :=
        XStepChecksPass.of_nonGas_required_le hNonGas hGas
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hStepReady
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨fuelTail, fullFinal, hRelFinal, hPrefixTail⟩ :=
                ih (hStepReady hStep)
              have hStepAll :
                  ∀ tailFuel : Nat,
                    EvmYul.EVM.step tailFuel.succ
                        (EvmYul.EVM.C' (memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (memoryGasState full instr.op) =
                      .ok fullPost := by
                intro tailFuel
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelTail.succ, fullFinal, hRelFinal,
                  XPrefixTrace.running hDecode hChecks hStepAll hNoHalt
                    hPrefixTail⟩

theorem XRunListPathReady.running_prefix_with_budget
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full targetFinal : EVMState}
      {restBudget : Nat},
      XRunListPathReady validJumps code target full (.running targetFinal) →
      XRunListGasBudget code target + restBudget ≤
        full.gasAvailable.toNat →
      ∃ prefixFuel fullFinal,
        GasExecRel fullFinal targetFinal ∧
          XPrefixTrace validJumps prefixFuel full fullFinal ∧
          restBudget ≤ fullFinal.gasAvailable.toNat := by
  intro code
  induction code with
  | nil =>
      intro target full targetFinal restBudget hReady hBudget
      rcases hReady with ⟨hResult, hRel⟩
      cases hResult
      simp [XRunListGasBudget] at hBudget
      exact ⟨0, full, hRel, XPrefixTrace.done full, by simpa using hBudget⟩
  | cons instr rest ih =>
      intro target full targetFinal restBudget hReady hBudget
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | halted halt =>
              simp [hStepResult] at hStepReady
          | running targetPost =>
              simp [hStepResult] at hStepReady
              have hBudgetRun :
                  XRunListGasBudget (instr :: rest) target =
                    XGasRequiredAt target instr.op +
                      XRunListGasBudget rest targetPost := by
                simp [XRunListGasBudget, hStepResult]
              have hBudgetStep :
                  XGasRequiredAt full instr.op +
                      (XRunListGasBudget rest targetPost + restBudget) ≤
                    full.gasAvailable.toNat := by
                rw [hBudgetRun] at hBudget
                rw [←
                  XGasRequiredAt_eq_of_gasExecRel_of_targetInstr_no_call_create
                    hNoCallCreate hRel] at hBudget
                omega
              have hChecks :
                  XStepChecksPass validJumps full instr.op :=
                XStepChecksPass.of_nonGas_required_le hNonGas hGas
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              have hStepBody :
                  EvmYul.step instr.op instr.arg
                      (xBodyState full instr.op) =
                    .ok fullPost := by
                rw [← EVM_step_targetInstr_eq_xBodyState
                  (fuel := 0) (state := full) (instr := instr)
                  hNoCallCreate]
                exact hStep
              have hRestBudgetBody :
                  XRunListGasBudget rest targetPost + restBudget ≤
                    (xBodyState full instr.op).gasAvailable.toNat :=
                xBodyState_gasAvailable_toNat_of_required hBudgetStep
              have hRestBudget :
                  XRunListGasBudget rest targetPost + restBudget ≤
                    fullPost.gasAvailable.toNat := by
                rw [TargetInstrBodyPreservesGas.of_no_call_create
                  hNoCallCreate hStepBody]
                exact hRestBudgetBody
              obtain
                ⟨fuelTail, fullFinal, hRelFinal, hPrefixTail,
                  hRestFinal⟩ :=
                ih (hStepReady hStep) hRestBudget
              have hStepAll :
                  ∀ tailFuel : Nat,
                    EvmYul.EVM.step tailFuel.succ
                        (EvmYul.EVM.C' (memoryGasState full instr.op)
                          instr.op)
                        (some (instr.op, instr.arg))
                        (memoryGasState full instr.op) =
                      .ok fullPost := by
                intro tailFuel
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := tailFuel)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelTail.succ, fullFinal, hRelFinal,
                  XPrefixTrace.running hDecode hChecks hStepAll hNoHalt
                    hPrefixTail,
                  hRestFinal⟩

theorem runListResult_with_continuation_exists_agrees_of_path_ready
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {blockResult finalResult : StepResult},
      XRunListPathReady validJumps code target full blockResult →
      (∀ halt, blockResult = .halted halt → finalResult = .halted halt) →
      (∀ targetFinal,
        blockResult = .running targetFinal →
          ∃ fuel : Nat,
            ∀ fullFinal,
              GasExecRel fullFinal targetFinal →
                ∃ evmResult,
                  XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                    XResultAgrees finalResult evmResult) →
      ∃ fuel : Nat, ∃ evmResult,
        XStepTrace validJumps fuel.succ full evmResult ∧
          XResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target full blockResult finalResult hReady _hHalted hContinue
      rcases hReady with ⟨hResult, hRel⟩
      subst blockResult
      obtain ⟨fuel, hReplay⟩ := hContinue target rfl
      obtain ⟨evmResult, hTrace, hAgree⟩ := hReplay full hRel
      exact ⟨fuel, evmResult, hTrace, hAgree⟩
  | cons instr rest ih =>
      intro target full blockResult finalResult hReady hHalted hContinue
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          XStepChecksPass validJumps full instr.op :=
        XStepChecksPass.of_nonGas_required_le hNonGas hGas
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨fuelRest, evmResult, hRestTrace, hAgree⟩ :=
                ih (hStepReady hStep) hHalted hContinue
              have hStepFuel :
                  EvmYul.EVM.step fuelRest.succ
                      (EvmYul.EVM.C' (memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := fuelRest)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelRest.succ, evmResult,
                  XStepTrace.running hDecode hChecks hStepFuel hNoHalt
                    hRestTrace,
                  hAgree⟩
          | halted halt =>
              simp [hStepResult] at hStepReady
              subst blockResult
              have hFinal : finalResult = .halted halt :=
                hHalted halt rfl
              subst finalResult
              by_cases hRevert : halt.kind = .revert
              · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
                  targetInstr_revert_exists_agrees
                    (fuel := 0)
                    (instr := instr)
                    (full := full)
                    (target := target)
                    (halt := halt)
                    hNoCallCreate hRel hDecode hChecks hStepResult hRevert
                exact
                  ⟨1, .revert fullPost.gasAvailable halt.output, hTrace,
                    hAgree⟩
              · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
                  targetInstr_success_exists_agrees
                    (fuel := 0)
                    (instr := instr)
                    (full := full)
                    (target := target)
                    (halt := halt)
                    hNoCallCreate hRel hDecode hChecks hStepResult hRevert
                exact
                  ⟨1, .success fullPost halt.output, hTrace, hAgree⟩

theorem runListResult_with_path_continuation_exists_agrees_of_path_ready
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target full : EVMState}
      {blockResult finalResult : StepResult},
      XRunListPathReady validJumps code target full blockResult →
      (∀ halt, blockResult = .halted halt → finalResult = .halted halt) →
      (∀ targetFinal fullFinal,
        blockResult = .running targetFinal →
          GasExecRel fullFinal targetFinal →
            ∃ fuel : Nat, ∃ evmResult,
              XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                XResultAgrees finalResult evmResult) →
      ∃ fuel : Nat, ∃ evmResult,
        XStepTrace validJumps fuel.succ full evmResult ∧
          XResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target full blockResult finalResult hReady _hHalted hContinue
      rcases hReady with ⟨hResult, hRel⟩
      subst blockResult
      exact hContinue target full rfl hRel
  | cons instr rest ih =>
      intro target full blockResult finalResult hReady hHalted hContinue
      rcases hReady with
        ⟨hRel, hDecode, hNonGas, hGas, hNoCallCreate, hStepReady⟩
      have hChecks :
          XStepChecksPass validJumps full instr.op :=
        XStepChecksPass.of_nonGas_required_le hNonGas hGas
      cases hStepResult : Target.stepInstrResult instr target with
      | error err =>
          simp [hStepResult] at hStepReady
      | ok stepResult =>
          cases stepResult with
          | running targetPost =>
              simp [hStepResult] at hStepReady
              obtain ⟨hTargetStep, hKind⟩ :=
                Target.stepInstrResult_running_stepInstr hStepResult
              obtain ⟨fullPost, hStep, hRelPost⟩ :=
                EVM_step_targetInstr_exists_gasExecRel
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  hNoCallCreate
                  (hRel.memoryGasState_left (op := instr.op))
                  hTargetStep
              obtain ⟨fuelRest, evmResult, hRestTrace, hAgree⟩ :=
                ih (hStepReady hStep) hHalted hContinue
              have hStepFuel :
                  EvmYul.EVM.step fuelRest.succ
                      (EvmYul.EVM.C' (memoryGasState full instr.op)
                        instr.op)
                      (some (instr.op, instr.arg))
                      (memoryGasState full instr.op) =
                    .ok fullPost := by
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := fuelRest)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate]
                rw [EVM_step_targetInstr_eq_of_no_call_create
                  (fuel := 0)
                  (gasCost :=
                    EvmYul.EVM.C' (memoryGasState full instr.op)
                      instr.op)
                  (state := memoryGasState full instr.op)
                  (instr := instr) hNoCallCreate] at hStep
                exact hStep
              have hNoHalt : XHaltOutput? instr.op fullPost = none :=
                XHaltOutput?_none_of_targetInstr_haltKind_none hKind
              exact
                ⟨fuelRest.succ, evmResult,
                  XStepTrace.running hDecode hChecks hStepFuel hNoHalt
                    hRestTrace,
                  hAgree⟩
          | halted halt =>
              simp [hStepResult] at hStepReady
              subst blockResult
              have hFinal : finalResult = .halted halt :=
                hHalted halt rfl
              subst finalResult
              by_cases hRevert : halt.kind = .revert
              · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
                  targetInstr_revert_exists_agrees
                    (fuel := 0)
                    (instr := instr)
                    (full := full)
                    (target := target)
                    (halt := halt)
                    hNoCallCreate hRel hDecode hChecks hStepResult hRevert
                exact
                  ⟨1, .revert fullPost.gasAvailable halt.output, hTrace,
                    hAgree⟩
              · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
                  targetInstr_success_exists_agrees
                    (fuel := 0)
                    (instr := instr)
                    (full := full)
                    (target := target)
                    (halt := halt)
                    hNoCallCreate hRel hDecode hChecks hStepResult hRevert
                exact
                  ⟨1, .success fullPost halt.output, hTrace, hAgree⟩

theorem runListResult_exists_agrees_of_instr_ready
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target : EVMState}
      {targetResult : StepResult},
      Target.runListResult code target = .ok targetResult →
      XRunListSuffixReady validJumps code →
      (∀ targetFinal,
        targetResult = .running targetFinal →
          ∃ fuel : Nat,
            ∀ fullFinal,
              GasExecRel fullFinal targetFinal →
                ∃ evmResult,
                  XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                    XResultAgrees targetResult evmResult) →
      ∃ fuel : Nat,
        ∀ full,
          GasExecRel full target →
            ∃ evmResult,
              XStepTrace validJumps fuel.succ full evmResult ∧
                XResultAgrees targetResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target targetResult hRun _hReady hContinue
      simp [Target.runListResult] at hRun
      subst targetResult
      exact hContinue target rfl
  | cons instr rest ih =>
      intro target targetResult hRun hReady hContinue
      rcases Target.runListResult_cons_ok_cases hRun with
        ⟨targetPost, hStepResult, hRunRest⟩ | ⟨halt, hStepResult, hResult⟩
      · have hReadyRest :
            XRunListSuffixReady validJumps rest := by
          intro instr' rest' targetState blockResult hSuffix hRunSuffix
          intro fullState hRel
          rcases hSuffix with ⟨pre, hPrefix⟩
          exact
            hReady
              (instr := instr') (rest := rest')
              (targetState := targetState) (blockResult := blockResult)
              ⟨instr :: pre, by simp [hPrefix]⟩ hRunSuffix hRel
        obtain ⟨fuelRest, hRestAll⟩ :=
          ih hRunRest hReadyRest hContinue
        refine ⟨fuelRest.succ, ?_⟩
        intro full hRel
        obtain ⟨hDecode, hNonGas, hRequired, hNoCallCreate⟩ :=
          hReady
            (instr := instr) (rest := rest)
            (targetState := target) (blockResult := targetResult)
            ⟨[], by simp⟩ hRun hRel
        have hChecks :
            XStepChecksPass validJumps full instr.op :=
          XStepChecksPass.of_nonGas_required_le hNonGas hRequired
        obtain ⟨hTargetStep, hKind⟩ :=
          Target.stepInstrResult_running_stepInstr hStepResult
        obtain ⟨fullPost, hStep, hRelPost⟩ :=
          EVM_step_targetInstr_exists_gasExecRel
            (fuel := fuelRest)
            (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
            hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
            hTargetStep
        obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
          hRestAll fullPost hRelPost
        have hNoHalt : XHaltOutput? instr.op fullPost = none :=
          XHaltOutput?_none_of_targetInstr_haltKind_none hKind
        exact
          ⟨evmResult,
            XStepTrace.running hDecode hChecks hStep hNoHalt hRestTrace,
            hAgree⟩
      · subst targetResult
        refine ⟨1, ?_⟩
        intro full hRel
        obtain ⟨hDecode, hNonGas, hRequired, hNoCallCreate⟩ :=
          hReady
            (instr := instr) (rest := rest)
            (targetState := target) (blockResult := .halted halt)
            ⟨[], by simp⟩ (by simpa using hRun) hRel
        have hChecks :
            XStepChecksPass validJumps full instr.op :=
          XStepChecksPass.of_nonGas_required_le hNonGas hRequired
        by_cases hRevert : halt.kind = .revert
        · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
            targetInstr_revert_exists_agrees
              (fuel := 0)
              (instr := instr)
              (full := full)
              (target := target)
              (halt := halt)
              hNoCallCreate hRel hDecode hChecks hStepResult hRevert
          exact
            ⟨.revert fullPost.gasAvailable halt.output, hTrace, hAgree⟩
        · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
            targetInstr_success_exists_agrees
              (fuel := 0)
              (instr := instr)
              (full := full)
              (target := target)
              (halt := halt)
              hNoCallCreate hRel hDecode hChecks hStepResult hRevert
          exact ⟨.success fullPost halt.output, hTrace, hAgree⟩

theorem runListResult_with_continuation_exists_agrees_of_instr_ready
    {validJumps : Array Word} :
    ∀ {code : List TargetInstr} {target : EVMState}
      {blockResult finalResult : StepResult},
      Target.runListResult code target = .ok blockResult →
      XRunListSuffixReady validJumps code →
      (∀ halt, blockResult = .halted halt → finalResult = .halted halt) →
      (∀ targetFinal,
        blockResult = .running targetFinal →
          ∃ fuel : Nat,
            ∀ fullFinal,
              GasExecRel fullFinal targetFinal →
                ∃ evmResult,
                  XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                    XResultAgrees finalResult evmResult) →
      ∃ fuel : Nat,
        ∀ full,
          GasExecRel full target →
            ∃ evmResult,
              XStepTrace validJumps fuel.succ full evmResult ∧
                XResultAgrees finalResult evmResult := by
  intro code
  induction code with
  | nil =>
      intro target blockResult finalResult hRun _hReady _hHalted hContinue
      simp [Target.runListResult] at hRun
      subst blockResult
      exact hContinue target rfl
  | cons instr rest ih =>
      intro target blockResult finalResult hRun hReady hHalted hContinue
      rcases Target.runListResult_cons_ok_cases hRun with
        ⟨targetPost, hStepResult, hRunRest⟩ | ⟨halt, hStepResult, hBlockResult⟩
      · have hReadyRest :
            XRunListSuffixReady validJumps rest := by
          intro instr' rest' targetState blockResult' hSuffix hRunSuffix
          intro fullState hRel
          rcases hSuffix with ⟨pre, hPrefix⟩
          exact
            hReady
              (instr := instr') (rest := rest')
              (targetState := targetState) (blockResult := blockResult')
              ⟨instr :: pre, by simp [hPrefix]⟩ hRunSuffix hRel
        obtain ⟨fuelRest, hRestAll⟩ :=
          ih hRunRest hReadyRest hHalted hContinue
        refine ⟨fuelRest.succ, ?_⟩
        intro full hRel
        obtain ⟨hDecode, hNonGas, hRequired, hNoCallCreate⟩ :=
          hReady
            (instr := instr) (rest := rest)
            (targetState := target) (blockResult := blockResult)
            ⟨[], by simp⟩ hRun hRel
        have hChecks :
            XStepChecksPass validJumps full instr.op :=
          XStepChecksPass.of_nonGas_required_le hNonGas hRequired
        obtain ⟨hTargetStep, hKind⟩ :=
          Target.stepInstrResult_running_stepInstr hStepResult
        obtain ⟨fullPost, hStep, hRelPost⟩ :=
          EVM_step_targetInstr_exists_gasExecRel
            (fuel := fuelRest)
            (gasCost := EvmYul.EVM.C' (memoryGasState full instr.op) instr.op)
            hNoCallCreate (hRel.memoryGasState_left (op := instr.op))
            hTargetStep
        obtain ⟨evmResult, hRestTrace, hAgree⟩ :=
          hRestAll fullPost hRelPost
        have hNoHalt : XHaltOutput? instr.op fullPost = none :=
          XHaltOutput?_none_of_targetInstr_haltKind_none hKind
        exact
          ⟨evmResult,
            XStepTrace.running hDecode hChecks hStep hNoHalt hRestTrace,
            hAgree⟩
      · subst blockResult
        have hFinal : finalResult = .halted halt :=
          hHalted halt rfl
        subst finalResult
        refine ⟨1, ?_⟩
        intro full hRel
        obtain ⟨hDecode, hNonGas, hRequired, hNoCallCreate⟩ :=
          hReady
            (instr := instr) (rest := rest)
            (targetState := target) (blockResult := .halted halt)
            ⟨[], by simp⟩ (by simpa using hRun) hRel
        have hChecks :
            XStepChecksPass validJumps full instr.op :=
          XStepChecksPass.of_nonGas_required_le hNonGas hRequired
        by_cases hRevert : halt.kind = .revert
        · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
            targetInstr_revert_exists_agrees
              (fuel := 0)
              (instr := instr)
              (full := full)
              (target := target)
              (halt := halt)
              hNoCallCreate hRel hDecode hChecks hStepResult hRevert
          exact
            ⟨.revert fullPost.gasAvailable halt.output, hTrace, hAgree⟩
        · obtain ⟨fullPost, _hRelPost, hTrace, hAgree⟩ :=
            targetInstr_success_exists_agrees
              (fuel := 0)
              (instr := instr)
              (full := full)
              (target := target)
              (halt := halt)
              hNoCallCreate hRel hDecode hChecks hStepResult hRevert
          exact ⟨.success fullPost halt.output, hTrace, hAgree⟩

def XBlockReplayReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          XRunListSuffixReady validJumps (emitted.map LocatedTarget.instr)

def XBlockReplayNonGasReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          XRunListSuffixNonGasReady validJumps
            (emitted.map LocatedTarget.instr)

def XBlockReplayCoreNonGasReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          XRunListSuffixCoreNonGasReady validJumps
            (emitted.map LocatedTarget.instr)

def XBlockReplayCoreInputsReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          XRunListSuffixCoreInputsReady validJumps
            (emitted.map LocatedTarget.instr)

theorem XBlockReplayCoreNonGasReady.of_inputs
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word}
    (hInputs : XBlockReplayCoreInputsReady program target validJumps) :
    XBlockReplayCoreNonGasReady program target validJumps := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact
    XRunListSuffixCoreNonGasReady.of_inputs
      (hInputs hAt hEmit hTargetBlock hRun)

def XBlockPathChecksReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState fullState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          GasExecRel fullState blockState →
            XRunListPathChecksReady validJumps
              (emitted.map LocatedTarget.instr) blockState fullState
              blockResult

def XBlockPathCoreChecksReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState fullState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          GasExecRel fullState blockState →
            XRunListPathCoreChecksReady validJumps
              (emitted.map LocatedTarget.instr) blockState fullState
              blockResult

def XBlockPathReturnDataCopyBoundsReady
    (program : Program) (target : TargetProgram) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState fullState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          GasExecRel fullState blockState →
            XRunListPathReturnDataCopyBoundsReady
              (emitted.map LocatedTarget.instr) blockState fullState
              blockResult

def XBlockReplayGasReady
    (program : Program) (target : TargetProgram) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          XRunListSuffixGasReady (emitted.map LocatedTarget.instr)

def XBlockReplayNoCallCreate
    (program : Program) (target : TargetProgram) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          ∀ targetInstr ∈ emitted.map LocatedTarget.instr,
            targetInstrUsesCallCreate targetInstr = false

theorem XBlockReplayNoCallCreate.of_program_no_call_create
    {program : Program} {target : TargetProgram}
    (hNoCallCreate : Program.usesCallCreate program = false) :
    XBlockReplayNoCallCreate program target := by
  intro pc instr emitted before after blockState blockResult hAt hEmit
    _hTargetBlock _hRun targetInstr hMem
  rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
  subst targetInstr
  exact targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
    hNoCallCreate hAt hEmit hLocatedMem

def XBlockReplayNoReturnDataCopy
    (program : Program) (target : TargetProgram) : Prop :=
  ∀ {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      {blockState : EVMState} {blockResult : StepResult},
    Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
      emitInstr? program pc instr = some emitted →
        target.code = before ++ emitted ++ after →
          Target.runListResult (emitted.map LocatedTarget.instr) blockState =
            .ok blockResult →
          ∀ targetInstr ∈ emitted.map LocatedTarget.instr,
            targetInstrNoReturnDataCopy targetInstr = true

theorem XBlockReplayNoReturnDataCopy.of_target_noReturnDataCopy
    {program : Program} {target : TargetProgram}
    (hNoReturnDataCopy : targetProgramNoReturnDataCopy target) :
    XBlockReplayNoReturnDataCopy program target := by
  intro pc instr emitted before after blockState blockResult _hAt _hEmit
    hTargetBlock _hRun targetInstr hMem
  rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
  subst targetInstr
  exact hNoReturnDataCopy (by
    rw [hTargetBlock]
    exact List.mem_append_left after
      (List.mem_append_right before hLocatedMem))

theorem targetInstr_mem_of_suffix {code : List TargetInstr}
    {instr : TargetInstr} {rest : List TargetInstr}
    (hSuffix : ∃ pre : List TargetInstr, code = pre ++ (instr :: rest)) :
    instr ∈ code := by
  rcases hSuffix with ⟨pre, hCode⟩
  rw [hCode]
  exact List.mem_append_right pre (by simp)

theorem XBlockReplayNoReturnDataCopy.op_ne_returnDataCopy_of_suffix
    {program : Program} {target : TargetProgram}
    (hNoReturnDataCopy : XBlockReplayNoReturnDataCopy program target)
    {pc : Nat} {instr : Instr}
    {emitted before after : List LocatedTarget}
    {blockState : EVMState} {blockResult : StepResult}
    {targetInstr : TargetInstr} {rest : List TargetInstr}
    (hAt : Program.instrAtPc program blockState.pc.toNat = some (pc, instr))
    (hEmit : emitInstr? program pc instr = some emitted)
    (hTargetBlock : target.code = before ++ emitted ++ after)
    (hRun :
      Target.runListResult (emitted.map LocatedTarget.instr) blockState =
        .ok blockResult)
    (hSuffix :
      ∃ pre : List TargetInstr,
        emitted.map LocatedTarget.instr = pre ++ (targetInstr :: rest)) :
    targetInstr.op ≠ EvmYul.Operation.RETURNDATACOPY :=
  targetInstr_op_ne_returnDataCopy_of_noReturnDataCopy
    (hNoReturnDataCopy hAt hEmit hTargetBlock hRun targetInstr
      (targetInstr_mem_of_suffix hSuffix))

theorem XBlockPathReturnDataCopyBoundsReady.of_noReturnDataCopy_noCallCreate
    {program : Program} {target : TargetProgram}
    (hNoReturnDataCopy : XBlockReplayNoReturnDataCopy program target)
    (hNoCallCreate : XBlockReplayNoCallCreate program target) :
    XBlockPathReturnDataCopyBoundsReady program target := by
  intro pc instr emitted before after blockState fullState blockResult hAt
    hEmit hTargetBlock hRun hRel
  exact
    XRunListPathReturnDataCopyBoundsReady.of_run_noReturnDataCopy_noCallCreate
      hRun
      (fun targetInstr hMem =>
        hNoReturnDataCopy hAt hEmit hTargetBlock hRun targetInstr hMem)
      (fun targetInstr hMem =>
        hNoCallCreate hAt hEmit hTargetBlock hRun targetInstr hMem)
      hRel

theorem XBlockPathReturnDataCopyBoundsReady.of_run_noCallCreate
    {program : Program} {target : TargetProgram}
    (hNoCallCreate : XBlockReplayNoCallCreate program target) :
    XBlockPathReturnDataCopyBoundsReady program target := by
  intro pc instr emitted before after blockState fullState blockResult hAt
    hEmit hTargetBlock hRun hRel
  exact
    XRunListPathReturnDataCopyBoundsReady.of_run_noCallCreate
      hRun
      (fun targetInstr hMem =>
        hNoCallCreate hAt hEmit hTargetBlock hRun targetInstr hMem)
      hRel

theorem XBlockPathChecksReady.of_core_noReturnDataCopy_noCallCreate
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word}
    (hCore : XBlockReplayCoreNonGasReady program target validJumps)
    (hNoReturnDataCopy : XBlockReplayNoReturnDataCopy program target)
    (hNoCallCreate : XBlockReplayNoCallCreate program target) :
    XBlockPathChecksReady program target validJumps := by
  intro pc instr emitted before after blockState fullState blockResult hAt hEmit
    hTargetBlock hRun hRel
  exact
    XRunListPathChecksReady.of_suffix_core_noReturnDataCopy_noCallCreate
      hRun
      (hCore hAt hEmit hTargetBlock hRun)
      (fun targetInstr hMem =>
        hNoReturnDataCopy hAt hEmit hTargetBlock hRun targetInstr hMem)
      (fun targetInstr hMem =>
        hNoCallCreate hAt hEmit hTargetBlock hRun targetInstr hMem)
      hRel

theorem XBlockPathChecksReady.of_core_returnDataCopyBounds_noCallCreate
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word}
    (hCore : XBlockReplayCoreNonGasReady program target validJumps)
    (hReturnDataCopyBounds :
      XBlockPathReturnDataCopyBoundsReady program target)
    (hNoCallCreate : XBlockReplayNoCallCreate program target) :
    XBlockPathChecksReady program target validJumps := by
  intro pc instr emitted before after blockState fullState blockResult hAt hEmit
    hTargetBlock hRun hRel
  exact
    XRunListPathChecksReady.of_suffix_core_returnDataCopyBounds_noCallCreate
      hRun
      (hCore hAt hEmit hTargetBlock hRun)
      (hReturnDataCopyBounds hAt hEmit hTargetBlock hRun hRel)
      (fun targetInstr hMem =>
        hNoCallCreate hAt hEmit hTargetBlock hRun targetInstr hMem)
      hRel

theorem XBlockPathCoreChecksReady.of_core_noCallCreate
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word}
    (hCore : XBlockReplayCoreNonGasReady program target validJumps)
    (hNoCallCreate : XBlockReplayNoCallCreate program target) :
    XBlockPathCoreChecksReady program target validJumps := by
  intro pc instr emitted before after blockState fullState blockResult hAt hEmit
    hTargetBlock hRun hRel
  exact
    XRunListPathCoreChecksReady.of_suffix_core_noCallCreate
      hRun
      (hCore hAt hEmit hTargetBlock hRun)
      (fun targetInstr hMem =>
        hNoCallCreate hAt hEmit hTargetBlock hRun targetInstr hMem)
      hRel

def XBlockTraceGasBudget (program : Program) :
    Nat → EVMState → StepResult → Nat
  | 0, _state, _result => 0
  | fuel + 1, state, result =>
      match Program.instrAtPc program state.pc.toNat with
      | none => 0
      | some (pc, instr) =>
          match emitInstr? program pc instr with
          | none => 0
          | some emitted =>
              let code := emitted.map LocatedTarget.instr
              match Target.runListResult code state with
              | .ok (.running mid) =>
                  XRunListGasBudget code state +
                    XBlockTraceGasBudget program fuel mid result
              | .ok (.halted _halt) =>
                  XRunListGasBudget code state
              | .error _ => 0

/--
The concrete gas bridge only needs the finite gas budget computed from the
gasless block trace to fit in a `UInt256`.  This is a resource bound, not a
semantic replay witness.
-/
def XTraceGasBudgetFits (program : Program) (targetFuel : Nat)
    (state : EVMState) (targetResult : StepResult) : Prop :=
  XBlockTraceGasBudget program targetFuel state targetResult <
    EvmYul.UInt256.size

theorem XBlockReplayReady.of_parts {program : Program}
    {target : TargetProgram} {validJumps : Array Word}
    (hNonGas : XBlockReplayNonGasReady program target validJumps)
    (hGas : XBlockReplayGasReady program target) :
    XBlockReplayReady program target validJumps := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact
    XRunListSuffixReady.of_parts
      (hNonGas hAt hEmit hTargetBlock hRun)
      (hGas hAt hEmit hTargetBlock hRun)

theorem XBlockPathChecksReady.of_replay_nonGas {program : Program}
    {target : TargetProgram} {validJumps : Array Word}
    (hNonGas : XBlockReplayNonGasReady program target validJumps) :
    XBlockPathChecksReady program target validJumps := by
  intro pc instr emitted before after blockState fullState blockResult
    hAt hEmit hTargetBlock hRun hRel
  exact
    XRunListPathChecksReady.of_suffix_nonGas hRun
      (hNonGas hAt hEmit hTargetBlock hRun) hRel

theorem XBlockReplayReady.nonGas {program : Program}
    {target : TargetProgram} {validJumps : Array Word}
    (hReady : XBlockReplayReady program target validJumps) :
    XBlockReplayNonGasReady program target validJumps := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact XRunListSuffixReady.nonGas
    (hReady hAt hEmit hTargetBlock hRun)

theorem XBlockReplayReady.gas {program : Program}
    {target : TargetProgram} {validJumps : Array Word}
    (hReady : XBlockReplayReady program target validJumps) :
    XBlockReplayGasReady program target := by
  intro pc instr emitted before after blockState blockResult
    hAt hEmit hTargetBlock hRun
  exact XRunListSuffixReady.gas
    (hReady hAt hEmit hTargetBlock hRun)

def XTraceDoneContinuation
    (validJumps : Array Word) (result : StepResult) : Prop :=
  ∀ finalState,
    result = .running finalState →
      ∃ fuel : Nat,
        ∀ fullFinal,
          GasExecRel fullFinal finalState →
            ∃ evmResult,
            XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                XResultAgrees result evmResult

/--
If the gasless target trace has already halted, there is no fuel-exhausted
target continuation for the gas-aware bridge to replay.
-/
theorem XTraceDoneContinuation.halted {validJumps : Array Word}
    {halt : Halt} :
    XTraceDoneContinuation validJumps (.halted halt) := by
  intro finalState hResult
  cases hResult

/--
Honest finalization condition for a gasless trace that stops with a running
state because the source-level execution has completed.

`EVM.X` observes a running state only by taking one more fallthrough `STOP`
step.  That step is gas-free in EVMYulLean, but it can still update the
machine's return-data fields, so higher layers must prove the STOP result is
the same observation they intend to expose for the gasless running state.
-/
def XFallthroughStopContinuationReady (target : EVMState) : Prop :=
  ∀ full : EVMState,
    GasExecRel full target →
      EvmYul.EVM.decode full.executionEnv.code full.pc = none ∧
        full.stack.length ≤ 1024 ∧
          ∃ post : EVMState,
            EvmYul.EVM.step 1
                (EvmYul.EVM.C'
                  (memoryGasState full EvmYul.Operation.STOP)
                  EvmYul.Operation.STOP)
                (some (EvmYul.Operation.STOP, none))
                (memoryGasState full EvmYul.Operation.STOP) =
              .ok post ∧
            XHaltOutput? EvmYul.Operation.STOP post =
              some ByteArray.empty ∧
            XResultAgrees (.running target)
              (EvmYul.EVM.ExecutionResult.success post ByteArray.empty)

def XFallthroughStopCleanReady (target : EVMState) : Prop :=
  (∀ full : EVMState,
      GasExecRel full target →
        EvmYul.EVM.decode full.executionEnv.code full.pc = none) ∧
    target.stack.length ≤ 1024 ∧
      (target.toMachineState.setReturnData ByteArray.empty).setHReturn
          ByteArray.empty =
        target.toMachineState

def ReturnBuffersClean (state : EVMState) : Prop :=
  (state.toMachineState.setReturnData ByteArray.empty).setHReturn
      ByteArray.empty =
    state.toMachineState

theorem returnBuffersClean_iff (state : EVMState) :
    ReturnBuffersClean state ↔
      state.returnData = ByteArray.empty ∧
        state.H_return = ByteArray.empty := by
  cases state with
  | mk shared pc stack execLength =>
      cases shared
      rename_i toState toMachineState
      constructor
      · intro h
        constructor
        · exact
            (congrArg EvmYul.MachineState.returnData h).symm
        · exact
            (congrArg EvmYul.MachineState.H_return h).symm
      · intro h
        rcases h with ⟨hReturnData, hHReturn⟩
        cases toMachineState
        simp [ReturnBuffersClean, EvmYul.MachineState.setReturnData,
          EvmYul.MachineState.setHReturn] at hReturnData hHReturn ⊢
        exact ⟨hReturnData.symm, hHReturn.symm⟩

theorem ReturnBuffersClean.of_return_buffers_eq
    {state post : EVMState}
    (hClean : ReturnBuffersClean state)
    (hReturnData : post.returnData = state.returnData)
    (hHReturn : post.H_return = state.H_return) :
    ReturnBuffersClean post := by
  rw [returnBuffersClean_iff] at hClean ⊢
  exact ⟨hReturnData.trans hClean.1, hHReturn.trans hClean.2⟩

def MachineReturnBuffersPreserved
    (before after : EvmYul.MachineState) : Prop :=
  after.returnData = before.returnData ∧
    after.H_return = before.H_return

def SharedReturnBuffersPreserved
    {τ : EvmYul.OperationType}
    (before after : EvmYul.SharedState τ) : Prop :=
  after.returnData = before.returnData ∧
    after.H_return = before.H_return

def PrimStepPreservesReturnBuffers : PrimStep → Prop
  | .binaryMachineState f =>
      ∀ machine a b, MachineReturnBuffersPreserved machine (f machine a b)
  | .binaryMachineStateWithResult f =>
      ∀ machine a b,
        MachineReturnBuffersPreserved machine (f machine a b).2
  | .ternaryMachineState f =>
      ∀ machine a b c,
        MachineReturnBuffersPreserved machine (f machine a b c)
  | .ternaryCopy f =>
      ∀ shared a b c, SharedReturnBuffersPreserved shared (f shared a b c)
  | .quaternaryCopy f =>
      ∀ shared a b c d,
        SharedReturnBuffersPreserved shared (f shared a b c d)
  | .mload =>
      ∀ machine offset,
        MachineReturnBuffersPreserved machine
          (EvmYul.MachineState.mload machine offset).2
  | .returndatacopy =>
      ∀ machine a b c,
        MachineReturnBuffersPreserved machine
          (EvmYul.MachineState.returndatacopy machine a b c)
  | .log0 =>
      ∀ (shared : EvmYul.SharedState .EVM) a b,
        SharedReturnBuffersPreserved shared
          (EvmYul.SharedState.logOp a b #[] shared)
  | .log1 =>
      ∀ (shared : EvmYul.SharedState .EVM) a b c,
        SharedReturnBuffersPreserved shared
          (EvmYul.SharedState.logOp a b #[c] shared)
  | .log2 =>
      ∀ (shared : EvmYul.SharedState .EVM) a b c d,
        SharedReturnBuffersPreserved shared
          (EvmYul.SharedState.logOp a b #[c, d] shared)
  | .log3 =>
      ∀ (shared : EvmYul.SharedState .EVM) a b c d e,
        SharedReturnBuffersPreserved shared
          (EvmYul.SharedState.logOp a b #[c, d, e] shared)
  | .log4 =>
      ∀ (shared : EvmYul.SharedState .EVM) a b c d e f,
        SharedReturnBuffersPreserved shared
          (EvmYul.SharedState.logOp a b #[c, d, e, f] shared)
  | _ => True

theorem PrimStepPreservesReturnBuffers.of_continuingStep
    {op : PrimOp} {step : PrimStep}
    (hStep : op.continuingStep? = some step) :
    PrimStepPreservesReturnBuffers step := by
  cases op <;> simp [PrimOp.continuingStep?] at hStep <;>
    subst step
  all_goals
    first
    | trivial
    | simp [PrimStepPreservesReturnBuffers, MachineReturnBuffersPreserved,
        SharedReturnBuffersPreserved, EvmYul.MachineState.mload,
        EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
        EvmYul.MachineState.mstore8, EvmYul.MachineState.mcopy,
        EvmYul.MachineState.keccak256,
        EvmYul.MachineState.returndatacopy, EvmYul.writeBytes,
        EvmYul.SharedState.calldatacopy, EvmYul.SharedState.codeCopy,
        EvmYul.SharedState.extCodeCopy', EvmYul.SharedState.logOp]

theorem PrimStep.run_preserves_return_buffers
    {step : PrimStep} {state post : EVMState}
    (hPreserve : PrimStepPreservesReturnBuffers step)
    (hRun : step.run state = .ok post) :
    post.returnData = state.returnData ∧
      post.H_return = state.H_return := by
  cases step with
  | bin f =>
      cases hPop : state.stack.pop2 with
      | none => simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.execBinOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | un f =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.execUnOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | tri f =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.execTriOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | executionEnv f =>
      simp [PrimStep.run, EvmYul.EVM.executionEnvOp, Id.run] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | unaryExecutionEnv f =>
      cases hPop : state.stack.pop with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.unaryExecutionEnvOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | machineState f =>
      simp [PrimStep.run, EvmYul.EVM.machineStateOp, Id.run] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | binaryMachineState f =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toMachineState left right
          simpa [PrimStepPreservesReturnBuffers, MachineReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | binaryMachineStateWithResult f =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryMachineStateOp', hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toMachineState left right
          simpa [PrimStepPreservesReturnBuffers, MachineReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | ternaryMachineState f =>
      cases hPop : state.stack.pop3 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.ternaryMachineStateOp, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toMachineState a b c
          simpa [PrimStepPreservesReturnBuffers, MachineReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | state f =>
      simp [PrimStep.run, EvmYul.EVM.stateOp, Id.run] at hRun
      cases hRun
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | unaryState f =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, EvmYul.EVM.unaryStateOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | binaryState f =>
      cases hPop : state.stack.pop2 with
      | none => simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, left, right⟩
          simp [PrimStep.run, EvmYul.EVM.binaryStateOp, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | ternaryCopy f =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toSharedState a b c
          simpa [PrimStepPreservesReturnBuffers, SharedReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | quaternaryCopy f =>
      cases hPop : state.stack.pop4 with
      | none =>
          simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d⟩
          simp [PrimStep.run, EvmYul.EVM.quaternaryCopyOp, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toSharedState a b c d
          simpa [PrimStepPreservesReturnBuffers, SharedReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | pop =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          simp [EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
  | mload =>
      cases hPop : state.stack.pop with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, offset⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toMachineState offset
          simpa [PrimStepPreservesReturnBuffers, MachineReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | returndatacopy =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, hPop] at hRun
          by_cases hBounds : state.returnData.size < b.toNat + c.toNat
          · simp [hBounds] at hRun
          · simp [hBounds] at hRun
            cases hRun
            have hBuffers := hPreserve state.toMachineState a b c
            simpa [PrimStepPreservesReturnBuffers, MachineReturnBuffersPreserved,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC] using hBuffers
  | dup n =>
      by_cases hLen : n ≤ state.stack.length
      · simp [PrimStep.run, EvmYul.dup, hLen] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · simp [PrimStep.run, EvmYul.dup, hLen] at hRun
  | swap n =>
      by_cases hLen : n + 1 ≤ state.stack.length
      · simp [PrimStep.run, EvmYul.swap, hLen] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · simp [PrimStep.run, EvmYul.swap, hLen] at hRun
  | log0 =>
      cases hPop : state.stack.pop2 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toSharedState a b
          simpa [PrimStepPreservesReturnBuffers, SharedReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | log1 =>
      cases hPop : state.stack.pop3 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toSharedState a b c
          simpa [PrimStepPreservesReturnBuffers, SharedReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | log2 =>
      cases hPop : state.stack.pop4 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toSharedState a b c d
          simpa [PrimStepPreservesReturnBuffers, SharedReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | log3 =>
      cases hPop : state.stack.pop5 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d, e⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toSharedState a b c d e
          simpa [PrimStepPreservesReturnBuffers, SharedReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | log4 =>
      cases hPop : state.stack.pop6 with
      | none => simp [PrimStep.run, hPop] at hRun
      | some popped =>
          rcases popped with ⟨stack, a, b, c, d, e, f⟩
          simp [PrimStep.run, hPop] at hRun
          cases hRun
          have hBuffers := hPreserve state.toSharedState a b c d e f
          simpa [PrimStepPreservesReturnBuffers, SharedReturnBuffersPreserved,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] using hBuffers
  | invalid =>
      simp [PrimStep.run] at hRun

theorem PrimOp.step_preserves_return_buffers_of_no_call_create_nonhalting
    {op : PrimOp} {state post : EVMState}
    (hNoCallCreate : op.isCallCreate = false)
    (hNoHalt : op.haltKind? = none)
    (hRun : op.step state = .ok post) :
    post.returnData = state.returnData ∧
      post.H_return = state.H_return := by
  unfold PrimOp.step at hRun
  cases hStep : op.continuingStep? with
  | some step =>
      simp [hStep] at hRun
      exact
        PrimStep.run_preserves_return_buffers
          (PrimStepPreservesReturnBuffers.of_continuingStep hStep) hRun
  | none =>
      simp [hStep] at hRun
      cases op <;>
        simp [PrimOp.continuingStep?, PrimOp.haltKind?,
          PrimOp.isCallCreate, PrimOp.toEVM] at hStep hNoCallCreate hNoHalt hRun
      · have hPc :
            EvmYul.step (τ := .EVM) EvmYul.Operation.PC none state =
              .ok
                (EvmYul.EVM.State.replaceStackAndIncrPC state
                  (state.stack.push state.pc)) := by
          rfl
        rw [hPc] at hRun
        cases hRun
        simp [EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]

theorem Target.stepInstrResult_running_preserves_return_buffers_of_no_call_create
    {instr : TargetInstr} {state post : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hStepResult :
      Target.stepInstrResult instr state = .ok (.running post)) :
    post.returnData = state.returnData ∧
      post.H_return = state.H_return := by
  obtain ⟨hStep, hNoHalt⟩ :=
    Target.stepInstrResult_running_stepInstr hStepResult
  cases instr with
  | push32 value =>
      simp [Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  | jump =>
      cases hPop : state.stack.pop with
      | none =>
          simp [Target.stepInstr, hPop] at hStep
      | some popped =>
          rcases popped with ⟨stack, dest⟩
          simp [Target.stepInstr, hPop] at hStep
          cases hStep
          constructor <;> rfl
  | jumpi =>
      cases hPop : state.stack.pop2 with
      | none =>
          simp [Target.stepInstr, hPop] at hStep
      | some popped =>
          rcases popped with ⟨stack, dest, cond⟩
          simp [Target.stepInstr, hPop] at hStep
          cases hStep
          constructor <;> rfl
  | jumpdest =>
      simp [Target.stepInstr] at hStep
      cases hStep
      simp [EvmYul.EVM.State.incrPC]
  | prim op =>
      exact
        PrimOp.step_preserves_return_buffers_of_no_call_create_nonhalting
          (by simpa [targetInstrUsesCallCreate] using hNoCallCreate)
          (by simpa [TargetInstr.haltKind?] using hNoHalt)
          (by simpa [Target.stepInstr] using hStep)

theorem Target.stepInstrResult_running_preserves_returnBuffersClean_of_no_call_create
    {instr : TargetInstr} {state post : EVMState}
    (hNoCallCreate : targetInstrUsesCallCreate instr = false)
    (hStepResult :
      Target.stepInstrResult instr state = .ok (.running post))
    (hClean : ReturnBuffersClean state) :
    ReturnBuffersClean post := by
  obtain ⟨hReturnData, hHReturn⟩ :=
    Target.stepInstrResult_running_preserves_return_buffers_of_no_call_create
      hNoCallCreate hStepResult
  exact
    ReturnBuffersClean.of_return_buffers_eq hClean hReturnData hHReturn

theorem Target.runListResult_running_preserves_returnBuffersClean_of_no_call_create :
    ∀ {code : List TargetInstr} {state post : EVMState},
      Target.runListResult code state = .ok (.running post) →
      (∀ instr ∈ code, targetInstrUsesCallCreate instr = false) →
      ReturnBuffersClean state →
      ReturnBuffersClean post := by
  intro code
  induction code with
  | nil =>
      intro state post hRun _hNoCall hClean
      simp [Target.runListResult] at hRun
      cases hRun
      exact hClean
  | cons instr rest ih =>
      intro state post hRun hNoCall hClean
      have hNoCallInstr : targetInstrUsesCallCreate instr = false :=
        hNoCall instr (by simp)
      rcases Target.runListResult_cons_ok_cases hRun with
        ⟨mid, hStepResult, hRunRest⟩ | ⟨halt, _hStepResult, hResult⟩
      · have hMidClean :
            ReturnBuffersClean mid :=
          Target.stepInstrResult_running_preserves_returnBuffersClean_of_no_call_create
            hNoCallInstr hStepResult hClean
        have hNoCallRest :
            ∀ instr' ∈ rest, targetInstrUsesCallCreate instr' = false := by
          intro instr' hMem
          exact hNoCall instr' (by simp [hMem])
        exact ih hRunRest hNoCallRest hMidClean
      · cases hResult

def XFallthroughStopObservationReady (target : EVMState) : Prop :=
  (∀ full : EVMState,
      GasExecRel full target →
        EvmYul.EVM.decode full.executionEnv.code full.pc = none) ∧
    ReturnBuffersClean target

theorem decode_none_of_gasExecRel_pc_at_code_end
    {targetProgram : TargetProgram} {full target : EVMState}
    (hRel : GasExecRel full target)
    (hCode :
      target.executionEnv.code = Bytecode.encodeTarget targetProgram)
    (hPc :
      target.pc.toNat = Bytecode.codeByteLength targetProgram.code) :
    EvmYul.EVM.decode full.executionEnv.code full.pc = none := by
  rw [hRel]
  unfold EvmYul.EVM.decode
  simp [hCode, hPc, Bytecode.encodeTarget_get?_codeByteLength]

theorem XFallthroughStopObservationReady.of_pc_code_cleanReturn
    {targetProgram : TargetProgram} {target : EVMState}
    (hCode :
      target.executionEnv.code = Bytecode.encodeTarget targetProgram)
    (hPc :
      target.pc.toNat = Bytecode.codeByteLength targetProgram.code)
    (hCleanReturn :
      (target.toMachineState.setReturnData ByteArray.empty).setHReturn
          ByteArray.empty =
        target.toMachineState) :
    XFallthroughStopObservationReady target := by
  refine ⟨?_, hCleanReturn⟩
  intro full hRel
  exact decode_none_of_gasExecRel_pc_at_code_end hRel hCode hPc

theorem XFallthroughStopCleanReady.of_observation_stack
    {target : EVMState}
    (hObservation : XFallthroughStopObservationReady target)
    (hStack : target.stack.length ≤ 1024) :
    XFallthroughStopCleanReady target :=
  ⟨hObservation.1, hStack, hObservation.2⟩

structure XBlockTraceFinalizationReady
    (validJumps : Array Word) (program : Program) (target : TargetProgram)
    (initial : EVMState) : Prop where
  cleanRunning :
    ∀ {targetFuel targetState},
      Preservation.BlockTraceResult program target targetFuel initial
        (.running targetState) →
        XFallthroughStopCleanReady targetState

def XTraceFinalizationReadyFor
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {targetOutcome : StepResult}
    (_hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome) : Prop :=
  match targetOutcome with
  | .running targetState => XFallthroughStopCleanReady targetState
  | .halted _ => True

def XTraceFinalizationObservationReadyFor
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {targetOutcome : StepResult}
    (_hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome) : Prop :=
  match targetOutcome with
  | .running targetState => XFallthroughStopObservationReady targetState
  | .halted _ => True

def XTraceFallthroughPcFor
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {targetOutcome : StepResult}
    (_hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome) : Prop :=
  match targetOutcome with
  | .running targetState =>
      targetState.pc.toNat = Bytecode.codeByteLength target.code
  | .halted _ => True

def XTraceFallthroughPcAndReturnCleanFor
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {targetOutcome : StepResult}
    (_hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome) : Prop :=
  match targetOutcome with
  | .running targetState =>
      targetState.pc.toNat = Bytecode.codeByteLength target.code ∧
        ReturnBuffersClean targetState
  | .halted _ => True

theorem blockTraceResult_running_preserves_code_of_no_call_create
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial final : EVMState}
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        (.running final))
    (hNoCallCreate : Program.usesCallCreate program = false) :
    final.executionEnv.code = initial.executionEnv.code := by
  induction targetFuel generalizing initial final with
  | zero =>
      cases hTrace
      rfl
  | succ fuel ih =>
      cases hTrace with
      | stepRunning hAt hEmit hTargetBlock hRun hRest =>
          rename_i mid pc instr emitted before after
          have hBlockCode :
              mid.executionEnv.code = initial.executionEnv.code := by
            refine
              Target.runListResult_preserves_code_of_no_call_create hRun ?_
            intro targetInstr hMem
            rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
            subst targetInstr
            exact targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
              hNoCallCreate hAt hEmit hLocatedMem
          have hRestCode :
              final.executionEnv.code = mid.executionEnv.code :=
            ih hRest
          exact hRestCode.trans hBlockCode

theorem blockTraceResult_running_preserves_returnBuffersClean_of_no_call_create
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial final : EVMState}
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        (.running final))
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hInitialClean : ReturnBuffersClean initial) :
    ReturnBuffersClean final := by
  induction targetFuel generalizing initial final with
  | zero =>
      cases hTrace
      exact hInitialClean
  | succ fuel ih =>
      cases hTrace with
      | stepRunning hAt hEmit hTargetBlock hRun hRest =>
          rename_i mid pc instr emitted before after
          have hBlockClean :
              ReturnBuffersClean mid := by
            refine
              Target.runListResult_running_preserves_returnBuffersClean_of_no_call_create
                hRun ?_ hInitialClean
            intro targetInstr hMem
            rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
            subst targetInstr
            exact targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
              hNoCallCreate hAt hEmit hLocatedMem
          exact ih hRest hBlockClean

theorem XTraceFallthroughPcAndReturnCleanFor.of_pc_initialClean
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {targetOutcome : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hInitialClean : ReturnBuffersClean initial)
    (hPc : XTraceFallthroughPcFor hTrace) :
    XTraceFallthroughPcAndReturnCleanFor hTrace := by
  cases targetOutcome with
  | halted halt =>
      trivial
  | running final =>
      exact
        ⟨hPc,
          blockTraceResult_running_preserves_returnBuffersClean_of_no_call_create
            hTrace hNoCallCreate hInitialClean⟩

theorem XTraceFinalizationObservationReadyFor.of_fallthrough_pc_cleanReturn
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState}
    {targetOutcome : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome}
    (hInitialCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hFallthrough :
      XTraceFallthroughPcAndReturnCleanFor hTrace) :
    XTraceFinalizationObservationReadyFor hTrace := by
  cases targetOutcome with
  | halted halt =>
      trivial
  | running final =>
      have hFinalCode :
          final.executionEnv.code = Bytecode.encodeTarget target :=
        (blockTraceResult_running_preserves_code_of_no_call_create
          hTrace hNoCallCreate).trans hInitialCode
      exact
        XFallthroughStopObservationReady.of_pc_code_cleanReturn
          hFinalCode hFallthrough.1 hFallthrough.2

theorem XFallthroughStopContinuationReady.of_clean_stop_fallthrough
    {target : EVMState}
    (hDecodeNone :
      ∀ full : EVMState,
        GasExecRel full target →
          EvmYul.EVM.decode full.executionEnv.code full.pc = none)
    (hStack : target.stack.length ≤ 1024)
    (hCleanReturn :
      (target.toMachineState.setReturnData ByteArray.empty).setHReturn
          ByteArray.empty =
        target.toMachineState) :
    XFallthroughStopContinuationReady target := by
  intro full hRel
  refine ⟨hDecodeNone full hRel, ?_, ?_⟩
  · rw [hRel.stack_eq]
    exact hStack
  · let fullStop := memoryGasState full EvmYul.Operation.STOP
    let chargedStop : EVMState :=
      { fullStop with
        execLength := fullStop.execLength + 1,
        gasAvailable :=
          fullStop.gasAvailable -
            EvmYul.UInt256.ofNat
              (EvmYul.EVM.C' fullStop EvmYul.Operation.STOP) }
    let post : EVMState :=
      { chargedStop with
        toMachineState :=
          (chargedStop.toMachineState.setReturnData ByteArray.empty).setHReturn
            ByteArray.empty }
    refine ⟨post, ?_, ?_, ?_⟩
    · rfl
    · simp [XHaltOutput?]
    · apply XResultAgrees_running_success_of_gasExecRel
      have hTargetReturnData : target.returnData = ByteArray.empty := by
        symm
        simpa [EvmYul.MachineState.setReturnData,
          EvmYul.MachineState.setHReturn] using
          congrArg EvmYul.MachineState.returnData hCleanReturn
      have hTargetHReturn : target.H_return = ByteArray.empty := by
        symm
        simpa [EvmYul.MachineState.setReturnData,
          EvmYul.MachineState.setHReturn] using
          congrArg EvmYul.MachineState.H_return hCleanReturn
      dsimp [GasExecRel, post, chargedStop, fullStop, memoryGasState]
      rw [hRel]
      simp [EvmYul.MachineState.setReturnData,
        EvmYul.MachineState.setHReturn,
        hTargetReturnData, hTargetHReturn]

theorem XFallthroughStopContinuationReady.of_clean
    {target : EVMState}
    (hReady : XFallthroughStopCleanReady target) :
    XFallthroughStopContinuationReady target :=
  XFallthroughStopContinuationReady.of_clean_stop_fallthrough
    hReady.1 hReady.2.1 hReady.2.2

theorem XTraceDoneContinuation.running_of_fallthrough_stop
    {validJumps : Array Word} {target : EVMState}
    (hReady : XFallthroughStopContinuationReady target) :
    XTraceDoneContinuation validJumps (.running target) := by
  intro finalState hResult
  cases hResult
  refine ⟨1, ?_⟩
  intro fullFinal hRel
  obtain ⟨hDecodeNone, hStack, post, hStep, hHalt, hAgree⟩ :=
    hReady fullFinal hRel
  exact
    ⟨EvmYul.EVM.ExecutionResult.success post ByteArray.empty,
      XStepTrace.fallthroughStop hDecodeNone
        (XStepChecksPass_stop hStack) hStep hHalt,
      hAgree⟩

def XTracePathDoneContinuation
    (validJumps : Array Word) (result : StepResult) : Prop :=
  ∀ finalState fullFinal,
    result = .running finalState →
      GasExecRel fullFinal finalState →
        ∃ fuel : Nat, ∃ evmResult,
          XStepTrace validJumps fuel.succ fullFinal evmResult ∧
            XResultAgrees result evmResult

theorem XTraceDoneContinuation.to_path {validJumps : Array Word}
    {result : StepResult}
    (hDone : XTraceDoneContinuation validJumps result) :
    XTracePathDoneContinuation validJumps result := by
  intro finalState fullFinal hResult hRel
  obtain ⟨fuel, hAll⟩ := hDone finalState hResult
  obtain ⟨evmResult, hTrace, hAgree⟩ := hAll fullFinal hRel
  exact ⟨fuel, evmResult, hTrace, hAgree⟩

theorem XBlockTraceFinalizationReady.to_done_continuation
    {validJumps : Array Word} {program : Program} {target : TargetProgram}
    {initial : EVMState}
    (hReady :
      XBlockTraceFinalizationReady validJumps program target initial) :
    ∀ {targetFuel targetOutcome},
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome →
      XTraceDoneContinuation validJumps targetOutcome := by
  intro targetFuel targetOutcome hTrace
  cases targetOutcome with
  | running targetState =>
      exact
        XTraceDoneContinuation.running_of_fallthrough_stop
          (XFallthroughStopContinuationReady.of_clean
            (hReady.cleanRunning hTrace))
  | halted halt =>
      exact XTraceDoneContinuation.halted

theorem XTraceFinalizationReadyFor.to_done_continuation
    {validJumps : Array Word} {program : Program}
    {target : TargetProgram} {targetFuel : Nat}
    {initial : EVMState} {targetOutcome : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome}
    (hReady : XTraceFinalizationReadyFor hTrace) :
    XTraceDoneContinuation validJumps targetOutcome := by
  cases targetOutcome with
  | running targetState =>
      exact
        XTraceDoneContinuation.running_of_fallthrough_stop
          (XFallthroughStopContinuationReady.of_clean hReady)
  | halted halt =>
      exact XTraceDoneContinuation.halted

theorem XBlockTraceFinalizationReady.initial_clean
    {validJumps : Array Word} {program : Program}
    {target : TargetProgram} {initial : EVMState}
    (hReady :
      XBlockTraceFinalizationReady validJumps program target initial) :
    XFallthroughStopCleanReady initial :=
  hReady.cleanRunning
    (Preservation.BlockTraceResult.done (program := program)
      (target := target) initial)

theorem XTraceFinalizationReadyFor.all_initial_clean
    {program : Program} {target : TargetProgram} {initial : EVMState}
    (hReady :
      ∀ {targetFuel : Nat} {targetOutcome : StepResult},
        (hTrace :
          Preservation.BlockTraceResult program target targetFuel initial
            targetOutcome) →
        XTraceFinalizationReadyFor hTrace) :
    XFallthroughStopCleanReady initial :=
  hReady
    (Preservation.BlockTraceResult.done (program := program)
      (target := target) initial)

theorem XBlockTraceFinalizationReady.of_clean_running
    {validJumps : Array Word} {program : Program} {target : TargetProgram}
    {initial : EVMState}
    (hClean :
      ∀ {targetFuel targetState},
        Preservation.BlockTraceResult program target targetFuel initial
          (.running targetState) →
          XFallthroughStopCleanReady targetState) :
    XBlockTraceFinalizationReady validJumps program target initial where
  cleanRunning := hClean

/--
Trace-local core non-gas `EVM.X` path safety for a particular gasless block
trace.

This is intentionally weaker than `XBlockReplayCoreNonGasReady`: it follows
only the concrete states reached by the gasless trace, so emitted two-instruction
blocks such as `push32 label; jump` can prove jump safety after the push has
actually executed.
-/
inductive XBlockTraceCoreChecksReadyFor
    {program : Program} {target : TargetProgram}
    (validJumps : Array Word) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel state
          targetResult → Prop where
  | done (state : EVMState) :
      XBlockTraceCoreChecksReadyFor validJumps
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning (fuel : Nat) (state mid : EVMState)
      (result : StepResult)
      (pc : Nat) (instr : Instr)
      (emitted before after : List LocatedTarget)
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hChecks :
      (∀ {fullState : EVMState},
        GasExecRel fullState state →
          XRunListPathCoreChecksReady validJumps
            (emitted.map LocatedTarget.instr) state fullState
            (.running mid)))
      (hRestChecks :
        XBlockTraceCoreChecksReadyFor validJumps hRest) :
      XBlockTraceCoreChecksReadyFor validJumps
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) (state : EVMState) (halt : Halt)
      (pc : Nat) (instr : Instr)
      (emitted before after : List LocatedTarget)
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hChecks :
      ∀ {fullState : EVMState},
        GasExecRel fullState state →
          XRunListPathCoreChecksReady validJumps
            (emitted.map LocatedTarget.instr) state fullState
            (.halted halt)) :
      XBlockTraceCoreChecksReadyFor validJumps
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

/--
The actual gasless block trace, checked through the intermediate core-safe
target layer. Unlike `XBlockTraceCoreChecksReadyFor`, this predicate talks in
terms of a target execution relation (`CoreRunListResult`) rather than the
gas-aware path predicate consumed by `EVM.X`.
-/
inductive CoreBlockTraceResultFor
    {program : Program} {target : TargetProgram}
    (validJumps : Array Word) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel state
          targetResult → Prop where
  | done (state : EVMState) :
      CoreBlockTraceResultFor validJumps
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning (fuel : Nat) (state mid : EVMState)
      (result : StepResult)
      (pc : Nat) (instr : Instr)
      (emitted before after : List LocatedTarget)
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hCoreRun :
        CoreRunListResult validJumps (emitted.map LocatedTarget.instr)
          state (.running mid))
      (hRestCore :
        CoreBlockTraceResultFor validJumps hRest) :
      CoreBlockTraceResultFor validJumps
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) (state : EVMState) (halt : Halt)
      (pc : Nat) (instr : Instr)
      (emitted before after : List LocatedTarget)
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hCoreRun :
        CoreRunListResult validJumps (emitted.map LocatedTarget.instr)
          state (.halted halt)) :
      CoreBlockTraceResultFor validJumps
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

theorem CoreBlockTraceResultFor.running_stack_le_of_initial
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {initial final : EVMState}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        (.running final)}
    (hCore : CoreBlockTraceResultFor validJumps hTrace)
    (hInitial : initial.stack.length ≤ 1024)
    (hNoCallCreate : Program.usesCallCreate program = false) :
    final.stack.length ≤ 1024 := by
  induction targetFuel generalizing initial final with
  | zero =>
      cases hCore with
      | done state =>
          exact hInitial
  | succ fuel ih =>
      cases hCore with
      | stepRunning fuel state mid result pc instr emitted before after
          hAt hEmit hTargetBlock hRun hRest hCoreRun hRestCore =>
          have hMid := by
            refine
              CoreRunListResult.running_stack_le_of_initial
                hCoreRun hInitial ?_
            intro targetInstr hMem
            rcases List.mem_map.mp hMem with ⟨located, hLocatedMem, hEq⟩
            subst targetInstr
            exact targetInstr_usesCallCreate_false_of_program_noCall_emit_mem
              hNoCallCreate hAt hEmit hLocatedMem
          exact ih (hTrace := hRest) hRestCore hMid

theorem XTraceFinalizationReadyFor.of_observation_core
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {initial : EVMState} {targetOutcome : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetOutcome}
    (hCore : CoreBlockTraceResultFor validJumps hTrace)
    (hInitial : initial.stack.length ≤ 1024)
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hObservation : XTraceFinalizationObservationReadyFor hTrace) :
    XTraceFinalizationReadyFor hTrace := by
  cases targetOutcome with
  | halted halt =>
      trivial
  | running final =>
      exact
        XFallthroughStopCleanReady.of_observation_stack hObservation
          (CoreBlockTraceResultFor.running_stack_le_of_initial
            hCore hInitial hNoCallCreate)

theorem CoreBlockTraceResultFor.of_block_replay_core
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {state : EVMState} {targetResult : StepResult}
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hCore : XBlockReplayCoreNonGasReady program target validJumps) :
    CoreBlockTraceResultFor validJumps hTrace := by
  induction hTrace with
  | done state =>
      exact CoreBlockTraceResultFor.done
        (validJumps := validJumps) state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid result pc instr emitted before after
      exact CoreBlockTraceResultFor.stepRunning
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (mid := mid)
        (result := result)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (hRest := hRest)
        (CoreRunListResult.of_suffix_core hRun
          (hCore hAt hEmit hTargetBlock hRun))
        ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state halt pc instr emitted before after
      exact CoreBlockTraceResultFor.stepHalted
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (halt := halt)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (CoreRunListResult.of_suffix_core hRun
          (hCore hAt hEmit hTargetBlock hRun))

theorem CoreBlockTraceResultFor.of_block_replay_core_inputs
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {state : EVMState} {targetResult : StepResult}
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hInputs : XBlockReplayCoreInputsReady program target validJumps) :
    CoreBlockTraceResultFor validJumps hTrace :=
  CoreBlockTraceResultFor.of_block_replay_core hTrace
    (XBlockReplayCoreNonGasReady.of_inputs hInputs)

theorem CoreBlockTraceResultFor.of_instr_core_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hReady :
      ∀ {pc : Nat} {instr : Instr}
        {emitted before after : List LocatedTarget}
        {blockState : EVMState} {blockResult : StepResult},
        Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
          emitInstr? program pc instr = some emitted →
            target.code = before ++ emitted ++ after →
              Target.runListResult (emitted.map LocatedTarget.instr)
                  blockState =
                .ok blockResult →
                InstrCoreBlockReady target instr blockState) :
    CoreBlockTraceResultFor (validJumps target) hTrace := by
  induction hTrace with
  | done state =>
      exact CoreBlockTraceResultFor.done
        (validJumps := validJumps target) state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid result pc instr emitted before after
      exact CoreBlockTraceResultFor.stepRunning
        (validJumps := validJumps target)
        (fuel := fuel)
        (state := state)
        (mid := mid)
        (result := result)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (hRest := hRest)
        (CoreRunListResult.of_emitInstr_coreBlockReady
          hAsm hJumpdest hEmit
          (hReady hAt hEmit hTargetBlock hRun) hRun)
        ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state halt pc instr emitted before after
      exact CoreBlockTraceResultFor.stepHalted
        (validJumps := validJumps target)
        (fuel := fuel)
        (state := state)
        (halt := halt)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (CoreRunListResult.of_emitInstr_coreBlockReady
          hAsm hJumpdest hEmit
          (hReady hAt hEmit hTargetBlock hRun) hRun)

theorem CoreBlockTraceResultFor.of_trace_instr_core_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hReady : InstrCoreBlockTraceReadyFor target hTrace) :
    CoreBlockTraceResultFor (validJumps target) hTrace := by
  induction hReady with
  | done state =>
      exact CoreBlockTraceResultFor.done
        (validJumps := validJumps target) state
  | stepRunning hAt hEmit hTargetBlock hRun hRest
      hBlockReady hRestReady ih =>
      exact CoreBlockTraceResultFor.stepRunning
        (validJumps := validJumps target)
        _ _ _ _ _ _ _ _ _
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (hRest := hRest)
        (CoreRunListResult.of_emitInstr_coreBlockReady
          hAsm hJumpdest hEmit hBlockReady hRun)
        ih
  | stepHalted fuel hAt hEmit hTargetBlock hRun hBlockReady =>
      exact CoreBlockTraceResultFor.stepHalted
        (validJumps := validJumps target)
        fuel _ _ _ _ _ _ _
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (CoreRunListResult.of_emitInstr_coreBlockReady
          hAsm hJumpdest hEmit hBlockReady hRun)

theorem CoreBlockTraceResultFor.of_block_instr_core_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hReady : XBlockInstrCoreReady program target) :
    CoreBlockTraceResultFor (validJumps target) hTrace :=
  CoreBlockTraceResultFor.of_instr_core_ready
    hAsm hJumpdest hTrace
    (fun hAt hEmit hTargetBlock hRun =>
      hReady hAt hEmit hTargetBlock hRun)

theorem CoreBlockTraceResultFor.of_block_instr_core_residual_resources
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hResidual : XBlockInstrCoreResidualResources program target) :
    CoreBlockTraceResultFor (validJumps target) hTrace :=
  CoreBlockTraceResultFor.of_block_instr_core_ready hAsm hJumpdest hTrace
    (XBlockInstrCoreReady.of_inputs
      (XBlockInstrCoreInputsReady.of_residual_resources
        hNoCallCreate hResidual))

theorem CoreBlockTraceResultFor.of_trace_instr_core_residual_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    (hAsm : assemble? program = some target)
    (hJumpdest : Bytecode.JumpdestCorrect target)
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hNoCallCreate : Program.usesCallCreate program = false)
    (hResidual : InstrCoreBlockTraceResidualReadyFor target hTrace) :
    CoreBlockTraceResultFor (validJumps target) hTrace :=
  CoreBlockTraceResultFor.of_trace_instr_core_ready hAsm hJumpdest
    (InstrCoreBlockTraceReadyFor.of_inputs_ready
      (InstrCoreBlockTraceInputsReadyFor.of_residual_ready
        hNoCallCreate hResidual))

theorem CoreBlockTraceResultFor.to_trace_inputs_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hCore : CoreBlockTraceResultFor (validJumps target) hTrace) :
    InstrCoreBlockTraceInputsReadyFor target hTrace := by
  induction hCore with
  | done state =>
      exact InstrCoreBlockTraceInputsReadyFor.done (target := target)
  | stepRunning fuel state mid result pc instr emitted before after
      hAt hEmit hTargetBlock hRun hRest hCoreRun _hRestCore ih =>
      exact InstrCoreBlockTraceInputsReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (InstrCoreBlockInputsReady.of_emitInstr_coreRun hEmit hRun hCoreRun)
        ih
  | stepHalted fuel state halt pc instr emitted before after
      hAt hEmit hTargetBlock hRun hCoreRun =>
      exact InstrCoreBlockTraceInputsReadyFor.stepHalted
        (target := target)
        fuel
        hAt hEmit hTargetBlock hRun
        (InstrCoreBlockInputsReady.of_emitInstr_coreRun hEmit hRun hCoreRun)

theorem InstrCoreBlockTraceResidualReadyFor.of_inputs_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hReady : InstrCoreBlockTraceInputsReadyFor target hTrace) :
    InstrCoreBlockTraceResidualReadyFor target hTrace := by
  induction hReady with
  | done =>
      exact InstrCoreBlockTraceResidualReadyFor.done (target := target)
  | stepRunning hAt hEmit hTargetBlock hRun hRest hInputs _ ih =>
      exact InstrCoreBlockTraceResidualReadyFor.stepRunning
        (target := target)
        hAt hEmit hTargetBlock hRun hRest
        (InstrCoreResidualInputsReady.of_inputs_ready hInputs)
        ih
  | stepHalted fuel hAt hEmit hTargetBlock hRun hInputs =>
      exact InstrCoreBlockTraceResidualReadyFor.stepHalted
        (target := target)
        fuel
        hAt hEmit hTargetBlock hRun
        (InstrCoreResidualInputsReady.of_inputs_ready hInputs)

theorem InstrCoreBlockTraceResidualReadyFor.of_core_trace
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hCore : CoreBlockTraceResultFor (validJumps target) hTrace) :
    InstrCoreBlockTraceResidualReadyFor target hTrace :=
  InstrCoreBlockTraceResidualReadyFor.of_inputs_ready
    (CoreBlockTraceResultFor.to_trace_inputs_ready hCore)

theorem CoreBlockTraceResultFor.to_trace_core_checks
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hCore : CoreBlockTraceResultFor validJumps hTrace)
    (hNoCallCreate : XBlockReplayNoCallCreate program target) :
    XBlockTraceCoreChecksReadyFor validJumps hTrace := by
  induction hCore with
  | done state =>
      exact XBlockTraceCoreChecksReadyFor.done
        (validJumps := validJumps) state
  | stepRunning fuel state mid result pc instr emitted before after
      hAt hEmit hTargetBlock hRun hRest hCoreRun _hRestCore ih =>
      exact XBlockTraceCoreChecksReadyFor.stepRunning
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (mid := mid)
        (result := result)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (hRest := hRest)
        (fun hRel =>
          CoreRunListResult.to_path_core_checks hCoreRun
            (fun targetInstr hMem =>
              hNoCallCreate hAt hEmit hTargetBlock hRun
                targetInstr hMem)
            hRel)
        ih
  | stepHalted fuel state halt pc instr emitted before after
      hAt hEmit hTargetBlock hRun hCoreRun =>
      exact XBlockTraceCoreChecksReadyFor.stepHalted
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (halt := halt)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (fun hRel =>
          CoreRunListResult.to_path_core_checks hCoreRun
            (fun targetInstr hMem =>
              hNoCallCreate hAt hEmit hTargetBlock hRun
                targetInstr hMem)
            hRel)

theorem XBlockTraceCoreChecksReadyFor.of_block_path_core_checks
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {state : EVMState} {targetResult : StepResult}
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hChecks : XBlockPathCoreChecksReady program target validJumps) :
    XBlockTraceCoreChecksReadyFor validJumps hTrace := by
  induction hTrace with
  | done state =>
      exact XBlockTraceCoreChecksReadyFor.done
        (validJumps := validJumps) state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid result pc instr emitted before after
      exact XBlockTraceCoreChecksReadyFor.stepRunning
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (mid := mid)
        (result := result)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (hRest := hRest)
        (fun hRel => hChecks hAt hEmit hTargetBlock hRun hRel)
        ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state halt pc instr emitted before after
      exact XBlockTraceCoreChecksReadyFor.stepHalted
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (halt := halt)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (fun hRel => hChecks hAt hEmit hTargetBlock hRun hRel)

/--
Trace-local non-gas `EVM.X` path safety for a particular gasless block trace.

This is the small intermediate layer between the gasless target trace and the
gas-aware runner.  It deliberately follows one concrete `BlockTraceResult`
rather than asking for a global replay assumption over every possible target
state.  The remaining obligation for higher compiler layers is to construct
this predicate for the trace they produce, using source/runtime safety facts
such as return-data-copy bounds and static-mode write exclusion.
-/
inductive XBlockTraceChecksReadyFor
    {program : Program} {target : TargetProgram}
    (validJumps : Array Word) :
    {targetFuel : Nat} → {state : EVMState} →
      {targetResult : StepResult} →
        Preservation.BlockTraceResult program target targetFuel state
          targetResult → Prop where
  | done (state : EVMState) :
      XBlockTraceChecksReadyFor validJumps
        (Preservation.BlockTraceResult.done (program := program)
          (target := target) state)
  | stepRunning (fuel : Nat) (state mid : EVMState)
      (result : StepResult)
      (pc : Nat) (instr : Instr)
      (emitted before after : List LocatedTarget)
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hRest :
        Preservation.BlockTraceResult program target fuel mid result)
      (hChecks :
      (∀ {fullState : EVMState},
        GasExecRel fullState state →
          XRunListPathChecksReady validJumps
            (emitted.map LocatedTarget.instr) state fullState
            (.running mid)))
      (hRestChecks :
        XBlockTraceChecksReadyFor validJumps hRest) :
      XBlockTraceChecksReadyFor validJumps
        (Preservation.BlockTraceResult.stepRunning hAt hEmit
          hTargetBlock hRun hRest)
  | stepHalted (fuel : Nat) (state : EVMState) (halt : Halt)
      (pc : Nat) (instr : Instr)
      (emitted before after : List LocatedTarget)
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hChecks :
      ∀ {fullState : EVMState},
        GasExecRel fullState state →
          XRunListPathChecksReady validJumps
            (emitted.map LocatedTarget.instr) state fullState
            (.halted halt)) :
      XBlockTraceChecksReadyFor validJumps
        (Preservation.BlockTraceResult.stepHalted hAt hEmit
          hTargetBlock hRun)

theorem XBlockTraceChecksReadyFor.of_trace_core_noReturnDataCopy_noCallCreate
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {state : EVMState} {targetResult : StepResult}
    {hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult}
    (hCore : XBlockTraceCoreChecksReadyFor validJumps hTrace)
    (hNoReturnDataCopy : XBlockReplayNoReturnDataCopy program target)
    (hNoCallCreate : XBlockReplayNoCallCreate program target) :
    XBlockTraceChecksReadyFor validJumps hTrace := by
  induction hCore with
  | done state =>
      exact XBlockTraceChecksReadyFor.done (validJumps := validJumps) state
  | stepRunning fuel state mid result pc instr emitted before after
      hAt hEmit hTargetBlock hRun hRest hChecks _hRestChecks ih =>
      exact XBlockTraceChecksReadyFor.stepRunning
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (mid := mid)
        (result := result)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (hRest := hRest)
        (fun hRel =>
          XRunListPathChecksReady.of_path_core_noReturnDataCopy_noCallCreate
            (hChecks hRel)
            (fun targetInstr hMem =>
              hNoReturnDataCopy hAt hEmit hTargetBlock hRun
                targetInstr hMem)
            (fun targetInstr hMem =>
              hNoCallCreate hAt hEmit hTargetBlock hRun
                targetInstr hMem))
        ih
  | stepHalted fuel state halt pc instr emitted before after
      hAt hEmit hTargetBlock hRun hChecks =>
      exact XBlockTraceChecksReadyFor.stepHalted
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (halt := halt)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (fun hRel =>
          XRunListPathChecksReady.of_path_core_noReturnDataCopy_noCallCreate
            (hChecks hRel)
            (fun targetInstr hMem =>
              hNoReturnDataCopy hAt hEmit hTargetBlock hRun
                targetInstr hMem)
            (fun targetInstr hMem =>
              hNoCallCreate hAt hEmit hTargetBlock hRun
                targetInstr hMem))

theorem XBlockTraceChecksReadyFor.of_block_path_checks
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {state : EVMState} {targetResult : StepResult}
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hChecks : XBlockPathChecksReady program target validJumps) :
    XBlockTraceChecksReadyFor validJumps hTrace := by
  induction hTrace with
  | done state =>
      exact XBlockTraceChecksReadyFor.done (validJumps := validJumps) state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid result pc instr emitted before after
      exact XBlockTraceChecksReadyFor.stepRunning
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (mid := mid)
        (result := result)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (hRest := hRest)
        (fun hRel => hChecks hAt hEmit hTargetBlock hRun hRel)
        ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state halt pc instr emitted before after
      exact XBlockTraceChecksReadyFor.stepHalted
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (halt := halt)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (fun hRel => hChecks hAt hEmit hTargetBlock hRun hRel)

theorem XBlockTraceChecksReadyFor.of_block_replay_nonGas
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {targetFuel : Nat}
    {state : EVMState} {targetResult : StepResult}
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel state
        targetResult)
    (hNonGas : XBlockReplayNonGasReady program target validJumps) :
    XBlockTraceChecksReadyFor validJumps hTrace := by
  induction hTrace with
  | done state =>
      exact XBlockTraceChecksReadyFor.done (validJumps := validJumps) state
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      rename_i fuel state mid result pc instr emitted before after
      exact XBlockTraceChecksReadyFor.stepRunning
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (mid := mid)
        (result := result)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (hRest := hRest)
        (fun hRel =>
          XRunListPathChecksReady.of_suffix_nonGas hRun
            (hNonGas hAt hEmit hTargetBlock hRun) hRel)
        ih
  | stepHalted hAt hEmit hTargetBlock hRun =>
      rename_i fuel state halt pc instr emitted before after
      exact XBlockTraceChecksReadyFor.stepHalted
        (validJumps := validJumps)
        (fuel := fuel)
        (state := state)
        (halt := halt)
        (pc := pc)
        (instr := instr)
        (emitted := emitted)
        (before := before)
        (after := after)
        (hAt := hAt)
        (hEmit := hEmit)
        (hTargetBlock := hTargetBlock)
        (hRun := hRun)
        (fun hRel =>
          XRunListPathChecksReady.of_suffix_nonGas hRun
            (hNonGas hAt hEmit hTargetBlock hRun) hRel)

inductive XBlockTracePathReady
    (program : Program) (target : TargetProgram)
    (validJumps : Array Word) :
    Nat → EVMState → EVMState → StepResult → Prop where
  | done {state full : EVMState}
      (hRel : GasExecRel full state) :
      XBlockTracePathReady program target validJumps 0 state full
        (.running state)
  | stepRunning {fuel : Nat} {state full mid : EVMState}
      {result : StepResult}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.running mid))
      (hBlockPath :
        XRunListPathReady validJumps (emitted.map LocatedTarget.instr)
          state full (.running mid))
      (hRest :
        ∀ {prefixFuel : Nat} {fullMid : EVMState},
          XPrefixTrace validJumps prefixFuel full fullMid →
            GasExecRel fullMid mid →
              XBlockTracePathReady program target validJumps fuel mid
                fullMid result) :
      XBlockTracePathReady program target validJumps fuel.succ state full
        result
  | stepHalted {fuel : Nat} {state full : EVMState}
      {halt : Halt}
      {pc : Nat} {instr : Instr}
      {emitted before after : List LocatedTarget}
      (hAt : Program.instrAtPc program state.pc.toNat = some (pc, instr))
      (hEmit : emitInstr? program pc instr = some emitted)
      (hTargetBlock : target.code = before ++ emitted ++ after)
      (hRun :
        Target.runListResult (emitted.map LocatedTarget.instr) state =
          .ok (.halted halt))
      (hBlockPath :
        XRunListPathReady validJumps (emitted.map LocatedTarget.instr)
          state full (.halted halt)) :
      XBlockTracePathReady program target validJumps fuel.succ state full
        (.halted halt)

theorem XBlockTracePathReady.exists_agrees
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} {fuel : Nat}
    {state full : EVMState} {result : StepResult}
    (hReady :
      XBlockTracePathReady program target validJumps fuel state full result)
    (hDoneContinue : XTracePathDoneContinuation validJumps result) :
    ∃ fuel : Nat, ∃ evmResult,
      XStepTrace validJumps fuel.succ full evmResult ∧
        XResultAgrees result evmResult := by
  induction hReady with
  | done hRel =>
      exact hDoneContinue _ _ rfl hRel
  | stepRunning hAt hEmit hTargetBlock hRun hBlockPath hRest ih =>
      obtain ⟨prefixFuel, fullMid, hRelMid, hPrefix⟩ :=
        XRunListPathReady.running_prefix hBlockPath
      obtain ⟨restFuel, evmResult, hRestTrace, hAgree⟩ :=
        ih hPrefix hRelMid hDoneContinue
      obtain ⟨fuel, hTrace⟩ :=
        XPrefixTrace.then_stepTrace hPrefix hRestTrace
      exact ⟨fuel, evmResult, hTrace, hAgree⟩
  | stepHalted hAt hEmit hTargetBlock hRun hBlockPath =>
      refine
        runListResult_with_path_continuation_exists_agrees_of_path_ready
          hBlockPath ?_ ?_
      · intro halt hEq
        cases hEq
        rfl
      · intro targetFinal fullFinal hImpossible _hRel
        cases hImpossible

theorem blockTraceResult_exists_agrees_of_nonGas_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} :
    ∀ {targetFuel : Nat} {state full : EVMState}
      {targetResult : StepResult},
      Preservation.BlockTraceResult program target targetFuel state
        targetResult →
      XBlockReplayNonGasReady program target validJumps →
      XBlockReplayNoCallCreate program target →
      XBlockTraceGasBudget program targetFuel state targetResult ≤
        full.gasAvailable.toNat →
      GasExecRel full state →
      XTracePathDoneContinuation validJumps targetResult →
      ∃ fuel : Nat, ∃ evmResult,
        XStepTrace validJumps fuel.succ full evmResult ∧
          XResultAgrees targetResult evmResult := by
  intro targetFuel state full targetResult hTrace
  induction hTrace generalizing full with
  | done state =>
      intro _hNonGas _hNoCall _hBudget hRel hDoneContinue
      exact hDoneContinue state full rfl hRel
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      intro hNonGas hNoCall hBudget hRel hDoneContinue
      rename_i fuel state mid result pc instr emitted before after
      let code := emitted.map LocatedTarget.instr
      have hNonGasCode : XRunListSuffixNonGasReady validJumps code := by
        dsimp [code]
        exact hNonGas hAt hEmit hTargetBlock hRun
      have hNoCallCode :
          ∀ targetInstr ∈ code,
            targetInstrUsesCallCreate targetInstr = false := by
        dsimp [code]
        exact hNoCall hAt hEmit hTargetBlock hRun
      have hBudgetBlock :
          XRunListGasBudget code state +
              XBlockTraceGasBudget program fuel mid result ≤
            full.gasAvailable.toNat := by
        simpa [XBlockTraceGasBudget, hAt, hEmit, hRun, code,
          Nat.add_comm] using hBudget
      obtain ⟨prefixFuel, fullMid, hRelMid, hPrefix, hRestBudget⟩ :=
        XRunListPathReady.running_prefix_of_nonGas_no_call_create_and_budget
          (validJumps := validJumps)
          (code := code)
          (target := state)
          (full := full)
          (targetFinal := mid)
          (restBudget := XBlockTraceGasBudget program fuel mid result)
          (by simpa [code] using hRun)
          hNonGasCode
          hNoCallCode
          hBudgetBlock hRel
      obtain ⟨restFuel, evmResult, hRestTrace, hAgree⟩ :=
        ih hNonGas hNoCall hRestBudget hRelMid hDoneContinue
      obtain ⟨fuelAll, hTraceAll⟩ :=
        XPrefixTrace.then_stepTrace hPrefix hRestTrace
      exact ⟨fuelAll, evmResult, hTraceAll, hAgree⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      intro hNonGas hNoCall hBudget hRel _hDoneContinue
      rename_i fuel state halt pc instr emitted before after
      let code := emitted.map LocatedTarget.instr
      have hNonGasCode : XRunListSuffixNonGasReady validJumps code := by
        dsimp [code]
        exact hNonGas hAt hEmit hTargetBlock hRun
      have hNoCallCode :
          ∀ targetInstr ∈ code,
            targetInstrUsesCallCreate targetInstr = false := by
        dsimp [code]
        exact hNoCall hAt hEmit hTargetBlock hRun
      have hBudgetBlock :
          XRunListGasBudget code state ≤ full.gasAvailable.toNat := by
        simpa [XBlockTraceGasBudget, hAt, hEmit, hRun, code,
          Nat.add_comm] using hBudget
      have hBlockPath :
          XRunListPathReady validJumps code state full (.halted halt) :=
        XRunListPathReady.of_nonGas_no_call_create_and_budget
          (validJumps := validJumps)
          (code := code)
          (target := state)
          (full := full)
          (targetResult := .halted halt)
          (by simpa [code] using hRun)
          hNonGasCode
          hNoCallCode
          hBudgetBlock hRel
      refine
        runListResult_with_path_continuation_exists_agrees_of_path_ready
          hBlockPath ?_ ?_
      · intro halt' hEq
        cases hEq
        rfl
      · intro targetFinal fullFinal hImpossible _hRelFinal
        cases hImpossible

theorem blockTraceResult_exists_agrees_of_path_checks_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} :
    ∀ {targetFuel : Nat} {state full : EVMState}
      {targetResult : StepResult},
      Preservation.BlockTraceResult program target targetFuel state
        targetResult →
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) →
      Bytecode.DecodeSafety target →
      XBlockPathChecksReady program target validJumps →
      XBlockReplayNoCallCreate program target →
      XBlockTraceGasBudget program targetFuel state targetResult ≤
        full.gasAvailable.toNat →
      GasExecRel full state →
      full.executionEnv.code = Bytecode.encodeTarget target →
      XTracePathDoneContinuation validJumps targetResult →
      ∃ fuel : Nat, ∃ evmResult,
        XStepTrace validJumps fuel.succ full evmResult ∧
          XResultAgrees targetResult evmResult := by
  intro targetFuel state full targetResult hTrace
  induction hTrace generalizing full with
  | done state =>
      intro _hEncoding _hSafety _hChecks _hNoCall _hBudget hRel _hCode
        hDoneContinue
      exact hDoneContinue state full rfl hRel
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      intro hEncoding hSafety hChecks hNoCall hBudget hRel hCode
        hDoneContinue
      rename_i fuel state mid result pc instr emitted before after
      let code := emitted.map LocatedTarget.instr
      have hChecksCode :
          XRunListPathChecksReady validJumps code state full (.running mid) := by
        dsimp [code]
        exact hChecks hAt hEmit hTargetBlock hRun hRel
      have hNoCallCode :
          ∀ targetInstr ∈ code,
            targetInstrUsesCallCreate targetInstr = false := by
        dsimp [code]
        exact hNoCall hAt hEmit hTargetBlock hRun
      have hBudgetBlockRest :
          XRunListGasBudget code state +
              XBlockTraceGasBudget program fuel mid result ≤
            full.gasAvailable.toNat := by
        simpa [XBlockTraceGasBudget, hAt, hEmit, hRun, code,
          Nat.add_comm] using hBudget
      have hBudgetBlock :
          XRunListGasBudget code state ≤ full.gasAvailable.toNat := by
        omega
      have hBlockPath :
          XRunListPathReady validJumps code state full (.running mid) :=
        XRunListPathReady.of_emitInstr_checks_and_budget
          (program := program)
          (target := target)
          (validJumps := validJumps)
          (blockState := state)
          (fullState := full)
          hEncoding hSafety hAt hEmit hTargetBlock
          (by simpa [code] using hRun)
          hRel hCode hChecksCode hNoCallCode hBudgetBlock
      obtain ⟨prefixFuel, fullMid, hRelMid, hPrefix, hRestBudget⟩ :=
        XRunListPathReady.running_prefix_with_budget
          (validJumps := validJumps)
          (code := code)
          (target := state)
          (full := full)
          (targetFinal := mid)
          (restBudget := XBlockTraceGasBudget program fuel mid result)
          hBlockPath hBudgetBlockRest
      have hStateCode :
          state.executionEnv.code = Bytecode.encodeTarget target :=
        (GasExecRel.code_eq hRel).symm.trans hCode
      have hMidCode :
          mid.executionEnv.code = Bytecode.encodeTarget target := by
        have hMidStateCode :
            mid.executionEnv.code = state.executionEnv.code :=
          Target.runListResult_preserves_code_of_no_call_create
            (code := code)
            (state := state)
            (result := .running mid)
            (by simpa [code] using hRun)
            hNoCallCode
        exact hMidStateCode.trans hStateCode
      have hFullMidCode :
          fullMid.executionEnv.code = Bytecode.encodeTarget target :=
        (GasExecRel.code_eq hRelMid).trans hMidCode
      obtain ⟨restFuel, evmResult, hRestTrace, hAgree⟩ :=
        ih hEncoding hSafety hChecks hNoCall hRestBudget hRelMid
          hFullMidCode hDoneContinue
      obtain ⟨fuelAll, hTraceAll⟩ :=
        XPrefixTrace.then_stepTrace hPrefix hRestTrace
      exact ⟨fuelAll, evmResult, hTraceAll, hAgree⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      intro hEncoding hSafety hChecks hNoCall hBudget hRel hCode
        _hDoneContinue
      rename_i fuel state halt pc instr emitted before after
      let code := emitted.map LocatedTarget.instr
      have hChecksCode :
          XRunListPathChecksReady validJumps code state full (.halted halt) := by
        dsimp [code]
        exact hChecks hAt hEmit hTargetBlock hRun hRel
      have hNoCallCode :
          ∀ targetInstr ∈ code,
            targetInstrUsesCallCreate targetInstr = false := by
        dsimp [code]
        exact hNoCall hAt hEmit hTargetBlock hRun
      have hBudgetBlock :
          XRunListGasBudget code state ≤ full.gasAvailable.toNat := by
        simpa [XBlockTraceGasBudget, hAt, hEmit, hRun, code,
          Nat.add_comm] using hBudget
      have hBlockPath :
          XRunListPathReady validJumps code state full (.halted halt) :=
        XRunListPathReady.of_emitInstr_checks_and_budget
          (program := program)
          (target := target)
          (validJumps := validJumps)
          (blockState := state)
          (fullState := full)
          hEncoding hSafety hAt hEmit hTargetBlock
          (by simpa [code] using hRun)
          hRel hCode hChecksCode hNoCallCode hBudgetBlock
      refine
        runListResult_with_path_continuation_exists_agrees_of_path_ready
          hBlockPath ?_ ?_
      · intro halt' hEq
        cases hEq
        rfl
      · intro targetFinal fullFinal hImpossible _hRelFinal
        cases hImpossible

theorem blockTraceResult_exists_agrees_of_trace_checks_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} :
    ∀ {targetFuel : Nat} {state full : EVMState}
      {targetResult : StepResult}
      (hTrace :
        Preservation.BlockTraceResult program target targetFuel state
          targetResult),
      XBlockTraceChecksReadyFor validJumps hTrace →
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) →
      Bytecode.DecodeSafety target →
      XBlockReplayNoCallCreate program target →
      XBlockTraceGasBudget program targetFuel state targetResult ≤
        full.gasAvailable.toNat →
      GasExecRel full state →
      full.executionEnv.code = Bytecode.encodeTarget target →
      XTracePathDoneContinuation validJumps targetResult →
      ∃ fuel : Nat, ∃ evmResult,
          XStepTrace validJumps fuel.succ full evmResult ∧
          XResultAgrees targetResult evmResult := by
  intro targetFuel state full targetResult hTrace hTraceChecks
  induction hTraceChecks generalizing full with
  | done state =>
      intro _hEncoding _hSafety _hNoCall _hBudget hRel _hCode
        hDoneContinue
      exact hDoneContinue state full rfl hRel
  | stepRunning fuel state mid result pc instr emitted before after hAt hEmit
      hTargetBlock hRun hRest hChecksCodeFor hRestChecks ih =>
      intro hEncoding hSafety hNoCall hBudget hRel hCode
        hDoneContinue
      let code := emitted.map LocatedTarget.instr
      have hChecksCode :
          XRunListPathChecksReady validJumps code state full
            (.running mid) := by
        dsimp [code]
        exact hChecksCodeFor hRel
      have hNoCallCode :
          ∀ targetInstr ∈ code,
            targetInstrUsesCallCreate targetInstr = false := by
        dsimp [code]
        exact hNoCall hAt hEmit hTargetBlock hRun
      have hBudgetBlockRest :
          XRunListGasBudget code state +
              XBlockTraceGasBudget program fuel mid result ≤
            full.gasAvailable.toNat := by
        simpa [XBlockTraceGasBudget, hAt, hEmit, hRun, code,
          Nat.add_comm] using hBudget
      have hBudgetBlock :
          XRunListGasBudget code state ≤ full.gasAvailable.toNat := by
        omega
      have hBlockPath :
          XRunListPathReady validJumps code state full (.running mid) :=
        XRunListPathReady.of_emitInstr_checks_and_budget
          (program := program)
          (target := target)
          (validJumps := validJumps)
          (blockState := state)
          (fullState := full)
          hEncoding hSafety hAt hEmit hTargetBlock
          (by simpa [code] using hRun)
          hRel hCode hChecksCode hNoCallCode hBudgetBlock
      obtain ⟨prefixFuel, fullMid, hRelMid, hPrefix, hRestBudget⟩ :=
        XRunListPathReady.running_prefix_with_budget
          (validJumps := validJumps)
          (code := code)
          (target := state)
          (full := full)
          (targetFinal := mid)
          (restBudget := XBlockTraceGasBudget program fuel mid result)
          hBlockPath hBudgetBlockRest
      have hStateCode :
          state.executionEnv.code = Bytecode.encodeTarget target :=
        (GasExecRel.code_eq hRel).symm.trans hCode
      have hMidCode :
          mid.executionEnv.code = Bytecode.encodeTarget target := by
        have hMidStateCode :
            mid.executionEnv.code = state.executionEnv.code :=
          Target.runListResult_preserves_code_of_no_call_create
            (code := code)
            (state := state)
            (result := .running mid)
            (by simpa [code] using hRun)
            hNoCallCode
        exact hMidStateCode.trans hStateCode
      have hFullMidCode :
          fullMid.executionEnv.code = Bytecode.encodeTarget target :=
        (GasExecRel.code_eq hRelMid).trans hMidCode
      obtain ⟨restFuel, evmResult, hRestTrace, hAgree⟩ :=
        ih hEncoding hSafety hNoCall hRestBudget hRelMid
          hFullMidCode hDoneContinue
      obtain ⟨fuelAll, hTraceAll⟩ :=
        XPrefixTrace.then_stepTrace hPrefix hRestTrace
      exact ⟨fuelAll, evmResult, hTraceAll, hAgree⟩
  | stepHalted fuel state halt pc instr emitted before after hAt hEmit
      hTargetBlock hRun hChecksCodeFor =>
      intro hEncoding hSafety hNoCall hBudget hRel hCode
        _hDoneContinue
      let code := emitted.map LocatedTarget.instr
      have hChecksCode :
          XRunListPathChecksReady validJumps code state full
            (.halted halt) := by
        dsimp [code]
        exact hChecksCodeFor hRel
      have hNoCallCode :
          ∀ targetInstr ∈ code,
            targetInstrUsesCallCreate targetInstr = false := by
        dsimp [code]
        exact hNoCall hAt hEmit hTargetBlock hRun
      have hBudgetBlock :
          XRunListGasBudget code state ≤ full.gasAvailable.toNat := by
        simpa [XBlockTraceGasBudget, hAt, hEmit, hRun, code,
          Nat.add_comm] using hBudget
      have hBlockPath :
          XRunListPathReady validJumps code state full (.halted halt) :=
        XRunListPathReady.of_emitInstr_checks_and_budget
          (program := program)
          (target := target)
          (validJumps := validJumps)
          (blockState := state)
          (fullState := full)
          hEncoding hSafety hAt hEmit hTargetBlock
          (by simpa [code] using hRun)
          hRel hCode hChecksCode hNoCallCode hBudgetBlock
      refine
        runListResult_with_path_continuation_exists_agrees_of_path_ready
          hBlockPath ?_ ?_
      · intro halt' hEq
        cases hEq
        rfl
      · intro targetFinal fullFinal hImpossible _hRelFinal
        cases hImpossible

theorem blockTraceResult_stepTrace_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hTraceChecks :
      XBlockTraceChecksReadyFor (validJumps target) hTrace)
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult)
    {gas : Nat}
    (hGasAtLeast :
      XBlockTraceGasBudget program targetFuel initial targetResult ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    ∃ evmFuel evmResult,
      XStepTrace (validJumps target) evmFuel
          (installCodeAndGas target gas initial) evmResult ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gas initial) =
          .ok evmResult ∧
        XResultAgrees targetResult evmResult := by
  let gasBound := XBlockTraceGasBudget program targetFuel initial targetResult
  have hBudget :
      gasBound ≤
        (installCodeAndGas target gas initial).gasAvailable.toNat := by
    rw [installCodeAndGas_gasAvailable_toNat hGasFits]
    exact hGasAtLeast
  have hInstalledCode :
      (installCodeAndGas target gas initial).executionEnv.code =
        Bytecode.encodeTarget target := by
    simp [installCodeAndGas]
  obtain ⟨fuel, evmResult, hTraceX, hAgree⟩ :=
    blockTraceResult_exists_agrees_of_trace_checks_no_call_create_and_budget
      (program := program)
      (target := target)
      (validJumps := validJumps target)
      hTrace hTraceChecks hEncoding hSafety hNoCallCreate hBudget
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
      hInstalledCode
      hDoneContinue
  exact ⟨fuel.succ, evmResult, hTraceX, hTraceX.run, hAgree⟩

theorem blockTraceResult_runs_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hTraceChecks :
      XBlockTraceChecksReadyFor (validJumps target) hTrace)
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult)
    {gas : Nat}
    (hGasAtLeast :
      XBlockTraceGasBudget program targetFuel initial targetResult ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    ∃ evmFuel evmResult,
      EvmYul.EVM.X evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok evmResult ∧
      XResultAgrees targetResult evmResult := by
  obtain ⟨evmFuel, evmResult, _hTraceX, hRun, hAgree⟩ :=
    blockTraceResult_stepTrace_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget
      (program := program)
      (target := target)
      (initial := initial)
      (targetFuel := targetFuel)
      (targetResult := targetResult)
      hEncoding hSafety hCode hTrace hTraceChecks hNoCallCreate
      hDoneContinue hGasAtLeast hGasFits
  exact ⟨evmFuel, evmResult, hRun, hAgree⟩

theorem blockTraceResult_runs_at_or_above_computed_gas_of_nonGas_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hNonGas :
      XBlockReplayNonGasReady program target (validJumps target))
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult)
    {gas : Nat}
    (hGasAtLeast :
      XBlockTraceGasBudget program targetFuel initial targetResult ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    ∃ evmFuel evmResult,
      EvmYul.EVM.X evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok evmResult ∧
      XResultAgrees targetResult evmResult := by
  let gasBound := XBlockTraceGasBudget program targetFuel initial targetResult
  have hBudget :
      gasBound ≤
        (installCodeAndGas target gas initial).gasAvailable.toNat := by
    rw [installCodeAndGas_gasAvailable_toNat hGasFits]
    exact hGasAtLeast
  obtain ⟨fuel, evmResult, hTraceX, hAgree⟩ :=
    blockTraceResult_exists_agrees_of_nonGas_no_call_create_and_budget
      (program := program)
      (target := target)
      (validJumps := validJumps target)
      hTrace hNonGas hNoCallCreate hBudget
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
      hDoneContinue
  exact ⟨fuel.succ, evmResult, hTraceX.run, hAgree⟩

theorem blockTraceResult_runs_at_or_above_computed_gas_of_core_noReturnDataCopy_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hCore :
      XBlockReplayCoreNonGasReady program target (validJumps target))
    (hNoReturnDataCopy : XBlockReplayNoReturnDataCopy program target)
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult)
    {gas : Nat}
    (hGasAtLeast :
      XBlockTraceGasBudget program targetFuel initial targetResult ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    ∃ evmFuel evmResult,
      EvmYul.EVM.X evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok evmResult ∧
      XResultAgrees targetResult evmResult :=
  blockTraceResult_runs_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget
    hEncoding hSafety hCode hTrace
    (XBlockTraceChecksReadyFor.of_block_path_checks hTrace
      (XBlockPathChecksReady.of_core_noReturnDataCopy_noCallCreate
        hCore hNoReturnDataCopy hNoCallCreate))
    hNoCallCreate hDoneContinue hGasAtLeast hGasFits

theorem blockTraceResult_runs_at_or_above_computed_gas_of_core_returnDataCopyBounds_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hCore :
      XBlockReplayCoreNonGasReady program target (validJumps target))
    (hReturnDataCopyBounds :
      XBlockPathReturnDataCopyBoundsReady program target)
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult)
    {gas : Nat}
    (hGasAtLeast :
      XBlockTraceGasBudget program targetFuel initial targetResult ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    ∃ evmFuel evmResult,
      EvmYul.EVM.X evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok evmResult ∧
      XResultAgrees targetResult evmResult :=
  blockTraceResult_runs_at_or_above_computed_gas_of_trace_checks_no_call_create_and_budget
    hEncoding hSafety hCode hTrace
    (XBlockTraceChecksReadyFor.of_block_path_checks hTrace
      (XBlockPathChecksReady.of_core_returnDataCopyBounds_noCallCreate
        hCore hReturnDataCopyBounds hNoCallCreate))
    hNoCallCreate hDoneContinue hGasAtLeast hGasFits

theorem blockTraceResult_concrete_gas_of_nonGas_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hGasBoundFits :
      XTraceGasBudgetFits program targetFuel initial targetResult)
    (hNonGas :
      XBlockReplayNonGasReady program target (validJumps target))
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult) :
    ∃ evmFuel gasValue evmResult,
      gasValue < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gasValue initial) =
          .ok evmResult ∧
        XResultAgrees targetResult evmResult := by
  let gasBound := XBlockTraceGasBudget program targetFuel initial targetResult
  have hBudget :
      gasBound ≤
        (installCodeAndGas target gasBound initial).gasAvailable.toNat := by
    rw [installCodeAndGas_gasAvailable_toNat hGasBoundFits]
  obtain ⟨fuel, evmResult, hTraceX, hAgree⟩ :=
    blockTraceResult_exists_agrees_of_nonGas_no_call_create_and_budget
      (program := program)
      (target := target)
      (validJumps := validJumps target)
      hTrace hNonGas hNoCallCreate hBudget
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
      hDoneContinue
  exact ⟨fuel.succ, gasBound, evmResult, hGasBoundFits, hTraceX.run, hAgree⟩

theorem blockTraceResult_concrete_gas_of_path_checks_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hGasBoundFits :
      XTraceGasBudgetFits program targetFuel initial targetResult)
    (hChecks :
      XBlockPathChecksReady program target (validJumps target))
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult) :
    ∃ evmFuel gasValue evmResult,
      gasValue < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gasValue initial) =
          .ok evmResult ∧
        XResultAgrees targetResult evmResult := by
  let gasBound := XBlockTraceGasBudget program targetFuel initial targetResult
  have hBudget :
      gasBound ≤
        (installCodeAndGas target gasBound initial).gasAvailable.toNat := by
    rw [installCodeAndGas_gasAvailable_toNat hGasBoundFits]
  have hInstalledCode :
      (installCodeAndGas target gasBound initial).executionEnv.code =
        Bytecode.encodeTarget target := by
    simp [installCodeAndGas]
  have hTraceChecks :
      XBlockTraceChecksReadyFor (validJumps target) hTrace :=
    XBlockTraceChecksReadyFor.of_block_path_checks hTrace hChecks
  obtain ⟨fuel, evmResult, hTraceX, hAgree⟩ :=
    blockTraceResult_exists_agrees_of_trace_checks_no_call_create_and_budget
      (program := program)
      (target := target)
      (validJumps := validJumps target)
      hTrace hTraceChecks hEncoding hSafety hNoCallCreate hBudget
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
      hInstalledCode
      hDoneContinue
  exact ⟨fuel.succ, gasBound, evmResult, hGasBoundFits, hTraceX.run, hAgree⟩

/--
Concrete-gas bridge specialized to the finite budget computed from the gasless
block trace.  This is the witness used by the public compiler theorem: the
chosen installed gas is exactly `XBlockTraceGasBudget`.
-/
theorem blockTraceResult_computed_gas_of_path_checks_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hGasBoundFits :
      XTraceGasBudgetFits program targetFuel initial targetResult)
    (hChecks :
      XBlockPathChecksReady program target (validJumps target))
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult) :
    ∃ evmFuel evmResult,
      XBlockTraceGasBudget program targetFuel initial targetResult <
        EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target
              (XBlockTraceGasBudget program targetFuel initial targetResult)
              initial) =
          .ok evmResult ∧
        XResultAgrees targetResult evmResult := by
  let gasBound := XBlockTraceGasBudget program targetFuel initial targetResult
  have hBudget :
      gasBound ≤
        (installCodeAndGas target gasBound initial).gasAvailable.toNat := by
    rw [installCodeAndGas_gasAvailable_toNat hGasBoundFits]
  have hInstalledCode :
      (installCodeAndGas target gasBound initial).executionEnv.code =
        Bytecode.encodeTarget target := by
    simp [installCodeAndGas]
  have hTraceChecks :
      XBlockTraceChecksReadyFor (validJumps target) hTrace :=
    XBlockTraceChecksReadyFor.of_block_path_checks hTrace hChecks
  obtain ⟨fuel, evmResult, hTraceX, hAgree⟩ :=
    blockTraceResult_exists_agrees_of_trace_checks_no_call_create_and_budget
      (program := program)
      (target := target)
      (validJumps := validJumps target)
      hTrace hTraceChecks hEncoding hSafety hNoCallCreate hBudget
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
      hInstalledCode
      hDoneContinue
  exact ⟨fuel.succ, evmResult, hGasBoundFits, hTraceX.run, hAgree⟩

/--
Sufficient-gas version of the computed-budget bridge.  The finite budget
computed from the gasless block trace is a lower bound: any installed UInt256
gas value above it makes the gas-aware `X` run follow the same checked path and
produce an agreeing result.
-/
theorem blockTraceResult_runs_at_or_above_computed_gas_of_path_checks_no_call_create_and_budget
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    (hEncoding :
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target))
    (hSafety : Bytecode.DecodeSafety target)
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hChecks :
      XBlockPathChecksReady program target (validJumps target))
    (hNoCallCreate : XBlockReplayNoCallCreate program target)
    (hDoneContinue :
      XTracePathDoneContinuation (validJumps target) targetResult)
    {gas : Nat}
    (hGasAtLeast :
      XBlockTraceGasBudget program targetFuel initial targetResult ≤ gas)
    (hGasFits : gas < EvmYul.UInt256.size) :
    ∃ evmFuel evmResult,
      EvmYul.EVM.X evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok evmResult ∧
      XResultAgrees targetResult evmResult := by
  let gasBound := XBlockTraceGasBudget program targetFuel initial targetResult
  have hBudget :
      gasBound ≤
        (installCodeAndGas target gas initial).gasAvailable.toNat := by
    rw [installCodeAndGas_gasAvailable_toNat hGasFits]
    exact hGasAtLeast
  have hInstalledCode :
      (installCodeAndGas target gas initial).executionEnv.code =
        Bytecode.encodeTarget target := by
    simp [installCodeAndGas]
  have hTraceChecks :
      XBlockTraceChecksReadyFor (validJumps target) hTrace :=
    XBlockTraceChecksReadyFor.of_block_path_checks hTrace hChecks
  obtain ⟨fuel, evmResult, hTraceX, hAgree⟩ :=
    blockTraceResult_exists_agrees_of_trace_checks_no_call_create_and_budget
      (program := program)
      (target := target)
      (validJumps := validJumps target)
      hTrace hTraceChecks hEncoding hSafety hNoCallCreate hBudget
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
      hInstalledCode
      hDoneContinue
  exact ⟨fuel.succ, evmResult, hTraceX.run, hAgree⟩

theorem blockTraceResult_with_continuation_exists_agrees_of_block_ready
    {program : Program} {target : TargetProgram}
    {validJumps : Array Word} :
    ∀ {targetFuel : Nat} {state : EVMState} {result : StepResult},
      Preservation.BlockTraceResult program target targetFuel state result →
      (∀ {pc : Nat} {instr : Instr}
          {emitted before after : List LocatedTarget}
          {blockState : EVMState} {blockResult : StepResult},
        Program.instrAtPc program blockState.pc.toNat = some (pc, instr) →
          emitInstr? program pc instr = some emitted →
            target.code = before ++ emitted ++ after →
              Target.runListResult (emitted.map LocatedTarget.instr)
                  blockState =
                .ok blockResult →
              XRunListSuffixReady validJumps
                (emitted.map LocatedTarget.instr)) →
      (∀ finalState,
        result = .running finalState →
          ∃ fuel : Nat,
            ∀ fullFinal,
              GasExecRel fullFinal finalState →
                ∃ evmResult,
                  XStepTrace validJumps fuel.succ fullFinal evmResult ∧
                    XResultAgrees result evmResult) →
      ∃ fuel : Nat,
        ∀ full,
          GasExecRel full state →
            ∃ evmResult,
              XStepTrace validJumps fuel.succ full evmResult ∧
                XResultAgrees result evmResult := by
  intro targetFuel state result hTrace
  induction hTrace with
  | done state =>
      intro _hBlockReady hDoneContinue
      exact hDoneContinue state rfl
  | stepRunning hAt hEmit hTargetBlock hRun hRest ih =>
      intro hBlockReady hDoneContinue
      obtain ⟨fuelRest, hRestAll⟩ :=
        ih hBlockReady hDoneContinue
      refine
        runListResult_with_continuation_exists_agrees_of_instr_ready
          (validJumps := validJumps)
          hRun
          ?_
          ?_
          ?_
      · exact hBlockReady hAt hEmit hTargetBlock hRun
      · intro halt hImpossible
        cases hImpossible
      · intro targetFinal hRunning
        cases hRunning
        exact ⟨fuelRest, hRestAll⟩
  | stepHalted hAt hEmit hTargetBlock hRun =>
      intro hBlockReady _hDoneContinue
      refine
        runListResult_with_continuation_exists_agrees_of_instr_ready
          (validJumps := validJumps)
          hRun
          ?_
          ?_
          ?_
      · exact hBlockReady hAt hEmit hTargetBlock hRun
      · intro halt hEq
        cases hEq
        rfl
      · intro targetFinal hImpossible
        cases hImpossible

theorem blockTraceResult_concrete_gas_of_replay_ready
    {program : Program} {target : TargetProgram}
    {targetFuel : Nat} {initial : EVMState} {targetResult : StepResult}
    {gas : Nat}
    (hCode : initial.executionEnv.code = Bytecode.encodeTarget target)
    (hTrace :
      Preservation.BlockTraceResult program target targetFuel initial
        targetResult)
    (hGasFits : gas < EvmYul.UInt256.size)
    (hBlockReady :
      XBlockReplayReady program target (validJumps target))
    (hDoneContinue :
      XTraceDoneContinuation (validJumps target) targetResult) :
    ∃ evmFuel gasValue evmResult,
      gasValue < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gasValue initial) =
          .ok evmResult ∧
        XResultAgrees targetResult evmResult := by
  obtain ⟨fuel, hReplay⟩ :=
    blockTraceResult_with_continuation_exists_agrees_of_block_ready
      (validJumps := validJumps target)
      hTrace hBlockReady hDoneContinue
  obtain ⟨evmResult, hTraceX, hAgree⟩ :=
    hReplay (installCodeAndGas target gas initial)
      (GasExecRel.installCodeAndGas_of_code_eq hCode)
  exact ⟨fuel.succ, gas, evmResult, hGasFits, hTraceX.run, hAgree⟩

end XStepTrace

def XRunsResultSuccessfullyAbove (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) (evmFuel gasBound : Nat) : Prop :=
  ∀ gas,
    gasBound ≤ gas →
      gas < EvmYul.UInt256.size →
        ∃ result,
          EvmYul.EVM.X evmFuel (validJumps target)
              (installCodeAndGas target gas initial) =
            .ok result ∧
            XResultAgrees targetResult result

/--
The gas-analysis evidence needed to move from the gasless block trace to
EVMYulLean's gas-aware `X` runner.

This is intentionally an assumption interface, not a trusted constant.  A later
proof can replace a caller-provided value of this structure with a computed
bound derived from the finite block trace and EVMYulLean's gas cost functions.
-/
structure SufficientGasForX
    (target : TargetProgram) (initial sourceFinal : EVMState) where
  evmFuel : Nat
  gasBound : Nat
  gasBoundFits : gasBound < EvmYul.UInt256.size
  runsAboveBound : XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound

/--
Alias used at theorem boundaries: these are the explicit gas-aware preconditions
not yet derived from the gasless block trace.
-/
abbrev XPreconditionAssumptions :=
  SufficientGasForX

/--
Result-level gas-analysis evidence for the theorem path whose source
semantics can halt.  This is the explicit gas/resource boundary for connecting
the gasless result trace to EVMYulLean's gas-aware `X` runner.
-/
structure SufficientGasForXResult
    (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) where
  evmFuel : Nat
  gasBound : Nat
  gasBoundFits : gasBound < EvmYul.UInt256.size
  runsAboveBound :
    XRunsResultSuccessfullyAbove target initial targetResult evmFuel gasBound

abbrev XResultPreconditionAssumptions :=
  SufficientGasForXResult

def ConcreteGasForXResult
    (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) : Prop :=
  ∃ evmFuel gas result,
    gas < EvmYul.UInt256.size ∧
      EvmYul.EVM.X evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok result ∧
      XResultAgrees targetResult result

abbrev XResultConcreteWitness :=
  ConcreteGasForXResult

structure XConcretePathForResult
    (target : TargetProgram) (initial : EVMState)
    (targetResult : StepResult) where
  evmFuel : Nat
  gas : Nat
  result : EvmYul.EVM.ExecutionResult EVMState
  gasFits : gas < EvmYul.UInt256.size
  path :
    XStepTrace (validJumps target) evmFuel
      (installCodeAndGas target gas initial) result
  agrees : XResultAgrees targetResult result

theorem XConcretePathForResult.toConcrete {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    (hPath : XConcretePathForResult target initial targetResult) :
    ConcreteGasForXResult target initial targetResult := by
  exact
    ⟨hPath.evmFuel, hPath.gas, hPath.result, hPath.gasFits,
      hPath.path.run, hPath.agrees⟩

theorem SufficientGasForX.runsAtGasBound {target : TargetProgram}
    {initial sourceFinal : EVMState}
    (hGasForX : SufficientGasForX target initial sourceFinal) :
    ∃ result,
      EvmYul.EVM.X hGasForX.evmFuel (validJumps target)
          (installCodeAndGas target hGasForX.gasBound initial) =
        .ok result ∧
      XSuccessErasesTo sourceFinal result :=
  hGasForX.runsAboveBound hGasForX.gasBound (Nat.le_refl _)
    hGasForX.gasBoundFits

theorem SufficientGasForX.exists_concrete_gas {target : TargetProgram}
    {initial sourceFinal : EVMState}
    (hGasForX : SufficientGasForX target initial sourceFinal) :
    ∃ evmFuel gas result,
      gas < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gas initial) =
          .ok result ∧
        XSuccessErasesTo sourceFinal result := by
  obtain ⟨result, hRun, hAgrees⟩ := hGasForX.runsAtGasBound
  exact
    ⟨hGasForX.evmFuel, hGasForX.gasBound, result,
      hGasForX.gasBoundFits, hRun, hAgrees⟩

theorem SufficientGasForXResult.runsAtGasBound {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    (hGasForX : SufficientGasForXResult target initial targetResult) :
    ∃ result,
      EvmYul.EVM.X hGasForX.evmFuel (validJumps target)
          (installCodeAndGas target hGasForX.gasBound initial) =
        .ok result ∧
      XResultAgrees targetResult result :=
  hGasForX.runsAboveBound hGasForX.gasBound (Nat.le_refl _)
    hGasForX.gasBoundFits

theorem SufficientGasForXResult.exists_concrete_gas {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    (hGasForX : SufficientGasForXResult target initial targetResult) :
    ∃ evmFuel gas result,
      gas < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gas initial) =
          .ok result ∧
        XResultAgrees targetResult result := by
  obtain ⟨result, hRun, hAgrees⟩ := hGasForX.runsAtGasBound
  exact
    ⟨hGasForX.evmFuel, hGasForX.gasBound, result,
      hGasForX.gasBoundFits, hRun, hAgrees⟩

theorem SufficientGasForXResult.toConcrete {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    (hGasForX : SufficientGasForXResult target initial targetResult) :
    ConcreteGasForXResult target initial targetResult :=
  hGasForX.exists_concrete_gas

theorem SufficientGasForXResult.runsAtInstalledGas {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult} {gas : Nat}
    (hGasForX :
      SufficientGasForXResult target (installCodeAndGas target gas initial)
        targetResult)
    (hGas : hGasForX.gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    ∃ result,
      EvmYul.EVM.X hGasForX.evmFuel (validJumps target)
          (installCodeAndGas target gas initial) =
        .ok result ∧
      XResultAgrees targetResult result := by
  simpa [installCodeAndGas_idempotent] using
    hGasForX.runsAboveBound gas hGas hUInt256

theorem XRunsSuccessfullyAbove.not_out_of_gas {target : TargetProgram}
    {initial sourceFinal : EVMState} {evmFuel gasBound gas : Nat}
    (hRuns : XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound)
    (hGas : gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    EvmYul.EVM.X evmFuel (validJumps target)
        (installCodeAndGas target gas initial) ≠
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨result, hRun, _hProject⟩ := hRuns gas hGas hUInt256
  rw [hRun]
  intro hImpossible
  cases hImpossible

theorem XRunsResultSuccessfullyAbove.not_out_of_gas {target : TargetProgram}
    {initial : EVMState} {targetResult : StepResult}
    {evmFuel gasBound gas : Nat}
    (hRuns :
      XRunsResultSuccessfullyAbove target initial targetResult evmFuel
        gasBound)
    (hGas : gasBound ≤ gas)
    (hUInt256 : gas < EvmYul.UInt256.size) :
    EvmYul.EVM.X evmFuel (validJumps target)
        (installCodeAndGas target gas initial) ≠
      .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨result, hRun, _hProject⟩ := hRuns gas hGas hUInt256
  rw [hRun]
  intro hImpossible
  cases hImpossible

/--
Reusable package produced by the gas-aware bridge theorem.

Higher compiler layers should depend on this structure rather than destructing
large conjunctions: it names the bytecode facts, runtime-boundary facts,
gasless block trace, and sufficient-gas `X` behavior that the bridge provides.
-/
structure XBridgeEvidence
    (program : Program) (target : TargetProgram) (fuel : Nat)
    (initial sourceFinal : EVMState) : Prop where
  accepted : Accepted program
  compileBytes_eq : Bytecode.compileBytes? program = some (Bytecode.encodeTarget target)
  encodingCorrect : Bytecode.EncodingCorrect target (Bytecode.encodeTarget target)
  outOfGasPolicy : OutOfGasPolicyAssumption program initial
  currentContractProjection : CurrentContractProjectionAssumption program initial
  blockTrace : (
    ∃ targetFinal,
      Preservation.BlockTrace program target fuel initial targetFinal ∧
        eraseGas targetFinal = eraseGas sourceFinal)
  sufficientGas : (
    ∃ evmFuel gasBound,
      gasBound < EvmYul.UInt256.size ∧
        XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound)

namespace XBridgeEvidence

theorem exists_sufficient_gas {program : Program} {target : TargetProgram}
    {fuel : Nat} {initial sourceFinal : EVMState}
    (evidence : XBridgeEvidence program target fuel initial sourceFinal) :
    ∃ evmFuel gasBound,
      gasBound < EvmYul.UInt256.size ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
            ∃ result,
              EvmYul.EVM.X evmFuel (validJumps target)
                  (installCodeAndGas target gas initial) =
                .ok result ∧
                XSuccessErasesTo sourceFinal result :=
  evidence.sufficientGas

theorem exists_concrete_gas {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (evidence : XBridgeEvidence program target fuel initial sourceFinal) :
    ∃ evmFuel gas result,
      gas < EvmYul.UInt256.size ∧
        EvmYul.EVM.X evmFuel (validJumps target)
            (installCodeAndGas target gas initial) =
          .ok result ∧
        XSuccessErasesTo sourceFinal result := by
  obtain ⟨evmFuel, gasBound, hFits, hRuns⟩ := evidence.sufficientGas
  obtain ⟨result, hRun, hAgrees⟩ := hRuns gasBound (Nat.le_refl _) hFits
  exact ⟨evmFuel, gasBound, result, hFits, hRun, hAgrees⟩

theorem not_out_of_gas_above_bound {program : Program} {target : TargetProgram}
    {fuel : Nat} {initial sourceFinal : EVMState}
    (evidence : XBridgeEvidence program target fuel initial sourceFinal) :
    ∃ evmFuel gasBound,
      gasBound < EvmYul.UInt256.size ∧
      ∀ gas,
        gasBound ≤ gas →
        gas < EvmYul.UInt256.size →
            EvmYul.EVM.X evmFuel (validJumps target)
                (installCodeAndGas target gas initial) ≠
              .error EvmYul.EVM.ExecutionException.OutOfGass := by
  obtain ⟨evmFuel, gasBound, hFits, hRuns⟩ := evidence.sufficientGas
  exact
    ⟨evmFuel, gasBound, hFits, fun gas hGas hUInt256 =>
      hRuns.not_out_of_gas hGas hUInt256⟩

end XBridgeEvidence

/--
Primary gas-aware bridge theorem.

This theorem packages the existing compiler-correctness theorem together with
the explicit `XPreconditionAssumptions` evidence into a single named
artifact for higher compiler layers.
-/
theorem compile_whole_program_X_bridge {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    XBridgeEvidence program target fuel initial sourceFinal := by
    have hSound := compile_whole_program_sound hCompile hRuntime hRun
    rcases hSound with
      ⟨hAccepted, hBytes, hEncoding, hOutOfGas, hProjection,
        targetFinal, hTrace, hErase⟩
    exact
      { accepted := hAccepted
        compileBytes_eq := hBytes
        encodingCorrect := hEncoding
        outOfGasPolicy := hOutOfGas
        currentContractProjection := hProjection
        blockTrace := ⟨targetFinal, hTrace, hErase⟩
        sufficientGas :=
          ⟨hPreconditions.evmFuel, hPreconditions.gasBound,
            hPreconditions.gasBoundFits,
            hPreconditions.runsAboveBound⟩ }

/--
Gas-aware whole-program bridge to EVMYulLean `X`.

The compiler proof supplies the accepted-program, bytecode, and gas-erased
block-trace facts.  `SufficientGasForX` supplies the remaining gas-aware runner
analysis: an EVM fuel amount and a gas bound such that every larger UInt256 gas
input makes `X` return successfully and project to the same non-gas result.
-/
theorem compile_whole_program_X_sufficient_gas {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hSufficientGas : SufficientGasForX target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ targetFinal evmFuel gasBound,
          Preservation.BlockTrace program target fuel initial targetFinal ∧
            eraseGas targetFinal = eraseGas sourceFinal ∧
              gasBound < EvmYul.UInt256.size ∧
              XRunsSuccessfullyAbove target initial sourceFinal evmFuel gasBound ∧
                ∀ gas,
                  gasBound ≤ gas →
                  gas < EvmYul.UInt256.size →
                      EvmYul.EVM.X evmFuel (validJumps target)
                          (installCodeAndGas target gas initial) ≠
                        .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let cert :=
    compile_whole_program_X_bridge hCompile hRuntime hRun hSufficientGas
  obtain ⟨targetFinal, hTrace, hErase⟩ := cert.blockTrace
  obtain ⟨evmFuel, gasBound, hFits, hRuns⟩ := cert.sufficientGas
  refine
    ⟨cert.accepted, cert.encodingCorrect, targetFinal, evmFuel,
      gasBound, hTrace, hErase, hFits, hRuns, ?_⟩
  intro gas hGas hUInt256
  exact hRuns.not_out_of_gas hGas hUInt256

/--
Direct existential sufficient-gas statement for EVMYulLean `X`.

Under the bytecode/runtime assumptions and the explicit gas-aware `X`
preconditions, successful source execution implies that there is an EVM fuel
and gas bound such that every larger UInt256 gas input makes `X` return
successfully and preserve the gas-erased final state.
-/
theorem compile_whole_program_X_exists_sufficient_gas {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ evmFuel gasBound,
          gasBound < EvmYul.UInt256.size ∧
          ∀ gas,
            gasBound ≤ gas →
              gas < EvmYul.UInt256.size →
                ∃ result,
                  EvmYul.EVM.X evmFuel (validJumps target)
                      (installCodeAndGas target gas initial) =
                    .ok result ∧
                    XSuccessErasesTo sourceFinal result := by
  let cert := compile_whole_program_X_bridge hCompile hRuntime hRun hPreconditions
  obtain ⟨evmFuel, gasBound, hFits, hRuns⟩ := cert.exists_sufficient_gas
  exact ⟨cert.accepted, cert.encodingCorrect, evmFuel, gasBound, hFits, hRuns⟩

/--
No-out-of-gas corollary for callers that only need the gas safety part of the
`X` bridge.  The stronger theorem above additionally returns a successful
`ExecutionResult` with the gas-erased projection.
-/
theorem compile_whole_program_X_no_out_of_gas_above_bound {program : Program}
    {target : TargetProgram} {fuel : Nat} {initial sourceFinal : EVMState}
    (hCompile : compile? program = some target)
    (hRuntime : RuntimeAssumptions program target initial)
    (hRun : Source.runN program fuel initial = .ok sourceFinal)
    (hPreconditions : XPreconditionAssumptions target initial sourceFinal) :
    Accepted program ∧
      Bytecode.EncodingCorrect target (Bytecode.encodeTarget target) ∧
        ∃ evmFuel gasBound,
          gasBound < EvmYul.UInt256.size ∧
          ∀ gas,
            gasBound ≤ gas →
              gas < EvmYul.UInt256.size →
                EvmYul.EVM.X evmFuel (validJumps target)
                    (installCodeAndGas target gas initial) ≠
                  .error EvmYul.EVM.ExecutionException.OutOfGass := by
  let cert := compile_whole_program_X_bridge hCompile hRuntime hRun hPreconditions
  obtain ⟨evmFuel, gasBound, hFits, hNoOutOfGas⟩ :=
    cert.not_out_of_gas_above_bound
  exact
    ⟨cert.accepted, cert.encodingCorrect, evmFuel, gasBound, hFits,
      hNoOutOfGas⟩

end GasAware

end Assembly
end EvmCompiler
