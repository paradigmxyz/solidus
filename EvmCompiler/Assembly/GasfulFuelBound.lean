import EvmCompiler.Assembly.GasfulBridge

/-!
# Gas-derived structural fuel bounds for the charged interpreter

The gasful `EvmYul.EVM.X` interpreter threads a structural `fuel` argument
through every function of its mutual block (`X`, `step`, `call`, `Θ`, `Ξ`,
`Lambda`).  This module proves that the structural fuel demand of a charged
run is bounded by its available gas: every continuing instruction charges at
least one unit of gas, every CALL-family child frame starts with at least 100
less gas than its parent, and every CREATE-family child frame starts with at
least 32000 less.  Consequently, running `X` at any fuel of at least
`gasAvailable + 6` can never report `OutOfFuel`, which removes the
per-execution `hNoFuelStop` hypothesis from the gasful endpoints.
-/

namespace EvmCompiler
namespace Assembly
namespace GasfulFuelBound

open EvmYul (UInt256)

/-! ## `UInt256` arithmetic facts -/

theorem uint256_toNat_lt (a : EvmYul.UInt256) :
    a.toNat < EvmYul.UInt256.size :=
  a.val.isLt

theorem uint256_toNat_ofNat_le (n : Nat) :
    (EvmYul.UInt256.ofNat n).toNat ≤ n := by
  simp only [EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, Id.run, Fin.ofNat]
  exact Nat.mod_le _ _

theorem uint256_toNat_ofNat_of_lt {n : Nat}
    (h : n < EvmYul.UInt256.size) :
    (EvmYul.UInt256.ofNat n).toNat = n := by
  simp only [EvmYul.UInt256.ofNat, EvmYul.UInt256.toNat, Id.run, Fin.ofNat]
  exact Nat.mod_eq_of_lt h

theorem uint256_toNat_add_le (a b : EvmYul.UInt256) :
    (a + b).toNat ≤ a.toNat + b.toNat := by
  show (EvmYul.UInt256.add a b).toNat ≤ a.toNat + b.toNat
  simp only [EvmYul.UInt256.add, EvmYul.UInt256.toNat, Fin.add_def]
  exact Nat.mod_le _ _

theorem uint256_toNat_sub_of_le {a b : EvmYul.UInt256}
    (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  show (EvmYul.UInt256.sub a b).toNat = a.toNat - b.toNat
  simp only [EvmYul.UInt256.sub, EvmYul.UInt256.toNat, Fin.sub_def]
  have ha := a.val.isLt
  have hb := b.val.isLt
  have hEq :
      b.val.val + (a.val.val - b.val.val) = a.val.val := by
    simp only [EvmYul.UInt256.toNat] at h
    omega
  simp only [EvmYul.UInt256.toNat] at h ⊢
  rw [show EvmYul.UInt256.size - b.val.val + a.val.val =
      (a.val.val - b.val.val) + EvmYul.UInt256.size by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem uint256_toNat_sub_le (a b : EvmYul.UInt256) :
    b.toNat ≤ a.toNat → (a - b).toNat ≤ a.toNat := by
  intro h
  rw [uint256_toNat_sub_of_le h]
  exact Nat.sub_le _ _

/-- Charging a nat-cost that fits inside the available gas subtracts exactly. -/
theorem uint256_toNat_sub_ofNat_of_le {a : EvmYul.UInt256} {n : Nat}
    (h : n ≤ a.toNat) :
    (a - EvmYul.UInt256.ofNat n).toNat = a.toNat - n := by
  have hLt : n < EvmYul.UInt256.size :=
    Nat.lt_of_le_of_lt h (uint256_toNat_lt a)
  have hOf : (EvmYul.UInt256.ofNat n).toNat = n :=
    uint256_toNat_ofNat_of_lt hLt
  rw [uint256_toNat_sub_of_le (by rw [hOf]; exact h), hOf]

/-! ## Positivity of the dynamic instruction charge

Outside the zero-cost terminal group `Wzero = {STOP, RETURN, REVERT}`, every
instruction accepted by the stack-arity table `δ` charges at least one unit
of gas. -/

section CPrimePositivity

open GasConstants EvmYul.EVM.InstructionGasGroups

theorem one_le_Caccess (a : EvmYul.AccountAddress) (A : EvmYul.Substate) :
    1 ≤ EvmYul.EVM.Caccess a A := by
  unfold EvmYul.EVM.Caccess
  split <;> decide

theorem one_le_Cextra {τ : EvmYul.OperationType}
    (t r : EvmYul.AccountAddress) (val : EvmYul.UInt256)
    (σ : EvmYul.AccountMap τ) (A : EvmYul.Substate) :
    1 ≤ EvmYul.EVM.Cextra t r val σ A := by
  have h := one_le_Caccess t A
  simp only [EvmYul.EVM.Cextra]
  omega

theorem one_le_Ccall {τ : EvmYul.OperationType}
    (t r : EvmYul.AccountAddress) (val g : EvmYul.UInt256)
    (σ : EvmYul.AccountMap τ) (μ : EvmYul.MachineState)
    (A : EvmYul.Substate) :
    1 ≤ EvmYul.EVM.Ccall t r val g σ μ A := by
  unfold EvmYul.EVM.Ccall
  have h := one_le_Cextra t r val σ A
  omega

theorem one_le_Csload (μₛ : EvmYul.Stack EvmYul.UInt256)
    (A : EvmYul.Substate) (I : EvmYul.ExecutionEnv .EVM) :
    1 ≤ EvmYul.EVM.Csload μₛ A I := by
  unfold EvmYul.EVM.Csload
  split <;> decide

set_option linter.unusedSimpArgs false in
theorem one_le_Csstore (s : EvmYul.EVM.State) :
    1 ≤ EvmYul.EVM.Csstore s := by
  unfold EvmYul.EVM.Csstore
  repeat' split
  all_goals simp only [letFun]
  all_goals repeat' split
  all_goals simp [Gwarmaccess, Gcoldsload, Gsset, Gsreset]

set_option linter.unusedSimpArgs false in
theorem one_le_Cselfdestruct (s : EvmYul.EVM.State) :
    1 ≤ EvmYul.EVM.Cselfdestruct s := by
  unfold EvmYul.EVM.Cselfdestruct
  repeat' split
  all_goals simp only [letFun]
  all_goals repeat' split
  all_goals simp [Gselfdestruct, Gcoldaccountaccess, Gnewaccount]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 3200000 in
/-- Every continuing instruction charges at least one unit of gas: the only
zero-cost table entries are the `Wzero` terminals, and the only opcode
rejected by `δ` is `INVALID`. -/
theorem one_le_C'
    (s : EvmYul.EVM.State) (w : EvmYul.Operation .EVM)
    (hδ : EvmYul.EVM.δ w ≠ none)
    (hzero : w ∉ Wzero) :
    1 ≤ EvmYul.EVM.C' s w := by
  have hCsstore := one_le_Csstore s
  have hCselfdestruct := one_le_Cselfdestruct s
  cases w <;> rename_i p <;> cases p <;>
    first
      | (exact (hzero (by decide)).elim)
      | (exact (hδ (by decide)).elim)
      | (simpa [EvmYul.EVM.C'] using hCsstore)
      | (simpa [EvmYul.EVM.C'] using hCselfdestruct)
      | (simp [EvmYul.EVM.C', EvmYul.EVM.Ctstore, EvmYul.EVM.Ctload,
          EvmYul.EVM.Csload, EvmYul.EVM.Caccess, EvmYul.EVM.Ccall,
          EvmYul.EVM.Cextra, EvmYul.EVM.Cxfer, EvmYul.EVM.Cnew,
          EvmYul.EVM.CdelegatedCodeAccess,
          Wcopy, Wextaccount, Wzero, Wbase, Wverylow,
          Wverylow.pushInstrsWithoutZero, Wverylow.dupInstrs,
          Wverylow.swapInstrs, Wlow, Wmid, Whigh,
          Gjumpdest, Gbase, Gverylow, Glow, Gmid, Ghigh, Gexp, Gexpbyte,
          Glog, Glogdata, Glogtopic, Gkeccak256, Gkeccak256word,
          Gblockhash, HASH_OPCODE_GAS, Gcreate, Gwarmaccess,
          Gcoldaccountaccess, Gcoldsload, Gcopy] <;>
        (repeat' split) <;> omega)

end CPrimePositivity

/-! ## CALL-family gas headroom

The gas made available to a CALL-family child frame (`Ccallgas`) is at least
`Gwarmaccess = 100` below the parent's dynamic charge for the instruction
(`Ccall`): the stipend granted for value-bearing calls is strictly smaller
than the `Gcallvalue` component of `Cextra` that such calls are charged. -/

section CallGasHeadroom

open GasConstants

theorem gwarm_le_Caccess (a : EvmYul.AccountAddress) (A : EvmYul.Substate) :
    Gwarmaccess ≤ EvmYul.EVM.Caccess a A := by
  unfold EvmYul.EVM.Caccess
  split <;> decide

theorem uint256_bne_zero_of_ne {val : EvmYul.UInt256}
    (hne : ¬ val = ⟨0⟩) : (val != ⟨0⟩) = true := by
  cases val with
  | mk v =>
      have hv : v ≠ 0 := fun hz => hne (by cases hz; rfl)
      simpa [bne, EvmYul.instBEqUInt256, EvmYul.instBEqUInt256.beq] using hv

theorem ccallgas_add_gwarm_le_ccall {τ : EvmYul.OperationType}
    (t r : EvmYul.AccountAddress) (val g : EvmYul.UInt256)
    (σ : EvmYul.AccountMap τ) (μ : EvmYul.MachineState)
    (A : EvmYul.Substate) :
    EvmYul.EVM.Ccallgas t r val g σ μ A + Gwarmaccess ≤
      EvmYul.EVM.Ccall t r val g σ μ A := by
  have hAccess := gwarm_le_Caccess t A
  unfold EvmYul.EVM.Ccallgas EvmYul.EVM.Ccall
  simp only [EvmYul.EVM.Cextra]
  split
  · simp only [Gwarmaccess] at *
    omega
  · rename_i hne
    have hxfer : EvmYul.EVM.Cxfer val = Gcallvalue := by
      unfold EvmYul.EVM.Cxfer
      rw [uint256_bne_zero_of_ne (fun h => hne h)]
      simp
    rw [hxfer]
    simp only [Gwarmaccess, Gcallvalue, Gcallstipend] at *
    omega

theorem cgascap_le_ccall {τ : EvmYul.OperationType}
    (t r : EvmYul.AccountAddress) (val g : EvmYul.UInt256)
    (σ : EvmYul.AccountMap τ) (μ : EvmYul.MachineState)
    (A : EvmYul.Substate) :
    EvmYul.EVM.Cgascap t r val g σ μ A ≤
      EvmYul.EVM.Ccall t r val g σ μ A := by
  unfold EvmYul.EVM.Ccall
  exact Nat.le_add_right _ _

end CallGasHeadroom

/-! ## The shared (pure) instruction step

`EvmYul.step` — the fuel-free shared interpreter used by `EVM.step` for every
instruction outside the CALL/CREATE families — never changes `gasAvailable`
on success and never reports `OutOfFuel`. -/

section PureStep

/-- Facts needed about one pure-step result: success preserves the frame's
available gas, and the result is never structural fuel exhaustion. -/
def PureStepProps
    (result : Except EvmYul.EVM.ExecutionException EvmYul.EVM.State)
    (s : EvmYul.EVM.State) : Prop :=
  (∀ s', result = .ok s' → s'.gasAvailable = s.gasAvailable) ∧
    result ≠ .error .OutOfFuel

theorem pureStepProps_execUnOp (f : EvmYul.Primop.Unary)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.execUnOp f s) s := by
  unfold EvmYul.EVM.execUnOp
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_execBinOp (f : EvmYul.Primop.Binary)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.execBinOp f s) s := by
  unfold EvmYul.EVM.execBinOp
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_execTriOp (f : EvmYul.Primop.Ternary)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.execTriOp f s) s := by
  unfold EvmYul.EVM.execTriOp
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_execQuadOp (f : EvmYul.Primop.Quaternary)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.execQuadOp f s) s := by
  unfold EvmYul.EVM.execQuadOp
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_executionEnvOp
    (op : EvmYul.ExecutionEnv .EVM → EvmYul.UInt256)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.executionEnvOp op s) s := by
  exact ⟨fun s' h => by cases h; rfl, fun h => by cases h⟩

theorem pureStepProps_unaryExecutionEnvOp
    (op : EvmYul.ExecutionEnv .EVM → EvmYul.UInt256 → EvmYul.UInt256)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.unaryExecutionEnvOp op s) s := by
  unfold EvmYul.EVM.unaryExecutionEnvOp
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_machineStateOp
    (op : EvmYul.MachineState → EvmYul.UInt256)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.machineStateOp op s) s := by
  exact ⟨fun s' h => by cases h; rfl, fun h => by cases h⟩

theorem pureStepProps_stateOp
    (op : EvmYul.State .EVM → EvmYul.UInt256)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.stateOp op s) s := by
  exact ⟨fun s' h => by cases h; rfl, fun h => by cases h⟩

theorem pureStepProps_unaryStateOp
    (op : EvmYul.State .EVM → EvmYul.UInt256 →
      EvmYul.State .EVM × EvmYul.UInt256)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.unaryStateOp op s) s := by
  unfold EvmYul.EVM.unaryStateOp
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_binaryStateOp
    (op : EvmYul.State .EVM → EvmYul.UInt256 → EvmYul.UInt256 →
      EvmYul.State .EVM)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.binaryStateOp op s) s := by
  unfold EvmYul.EVM.binaryStateOp
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_binaryMachineStateOp
    (op : EvmYul.MachineState → EvmYul.UInt256 → EvmYul.UInt256 →
      EvmYul.MachineState)
    (hop : ∀ m a b, (op m a b).gasAvailable = m.gasAvailable)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.binaryMachineStateOp op s) s := by
  unfold EvmYul.EVM.binaryMachineStateOp
  constructor
  · intro s' h
    split at h
    · cases h
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hop]
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_binaryMachineStateOp'
    (op : EvmYul.MachineState → EvmYul.UInt256 → EvmYul.UInt256 →
      EvmYul.UInt256 × EvmYul.MachineState)
    (hop : ∀ m a b, (op m a b).2.gasAvailable = m.gasAvailable)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.binaryMachineStateOp' op s) s := by
  unfold EvmYul.EVM.binaryMachineStateOp'
  constructor
  · intro s' h
    split at h
    · cases h
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hop]
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_ternaryMachineStateOp
    (op : EvmYul.MachineState → EvmYul.UInt256 → EvmYul.UInt256 →
      EvmYul.UInt256 → EvmYul.MachineState)
    (hop : ∀ m a b c, (op m a b c).gasAvailable = m.gasAvailable)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.ternaryMachineStateOp op s) s := by
  unfold EvmYul.EVM.ternaryMachineStateOp
  constructor
  · intro s' h
    split at h
    · cases h
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hop]
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_ternaryCopyOp
    (op : EvmYul.SharedState .EVM → EvmYul.UInt256 → EvmYul.UInt256 →
      EvmYul.UInt256 → EvmYul.SharedState .EVM)
    (hop : ∀ st a b c, (op st a b c).gasAvailable = st.gasAvailable)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.ternaryCopyOp op s) s := by
  unfold EvmYul.EVM.ternaryCopyOp
  constructor
  · intro s' h
    split at h
    · cases h
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hop]
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_quaternaryCopyOp
    (op : EvmYul.SharedState .EVM → EvmYul.UInt256 → EvmYul.UInt256 →
      EvmYul.UInt256 → EvmYul.UInt256 → EvmYul.SharedState .EVM)
    (hop : ∀ st a b c d, (op st a b c d).gasAvailable = st.gasAvailable)
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.quaternaryCopyOp op s) s := by
  unfold EvmYul.EVM.quaternaryCopyOp
  constructor
  · intro s' h
    split at h
    · cases h
      simp [EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC, hop]
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

set_option linter.unusedSimpArgs false in
theorem pureStepProps_dup (n : Nat) (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.dup n s) s := by
  unfold EvmYul.dup
  constructor
  · intro s' h
    simp only [letFun] at h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    simp only [letFun] at h
    split at h
    · cases h
    · injection h with h; cases h

set_option linter.unusedSimpArgs false in
theorem pureStepProps_swap (n : Nat) (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.swap n s) s := by
  unfold EvmYul.swap
  constructor
  · intro s' h
    simp only [letFun] at h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    simp only [letFun] at h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_log0Op (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.log0Op s) s := by
  unfold EvmYul.EVM.log0Op
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_log1Op (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.log1Op s) s := by
  unfold EvmYul.EVM.log1Op
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_log2Op (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.log2Op s) s := by
  unfold EvmYul.EVM.log2Op
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_log3Op (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.log3Op s) s := by
  unfold EvmYul.EVM.log3Op
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_log4Op (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.EVM.log4Op s) s := by
  unfold EvmYul.EVM.log4Op
  constructor
  · intro s' h
    split at h
    · cases h; rfl
    · cases h
  · intro h
    split at h
    · cases h
    · injection h with h; cases h

theorem pureStepProps_of_ok {s X : EvmYul.EVM.State}
    (hgas : X.gasAvailable = s.gasAvailable) :
    PureStepProps (.ok X) s := by
  refine ⟨fun s' h => ?_, fun h => ?_⟩
  · cases h
    exact hgas
  · cases h

theorem pureStepProps_of_error {e : EvmYul.EVM.ExecutionException}
    (s : EvmYul.EVM.State) (he : e ≠ .OutOfFuel) :
    PureStepProps (.error e) s := by
  refine ⟨fun s' h => ?_, fun h => ?_⟩
  · cases h
  · injection h with h
    exact he h

theorem pureStepProps_stop (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .STOP arg s) s :=
  pureStepProps_of_ok rfl

theorem pureStepProps_invalid (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .INVALID arg s) s :=
  pureStepProps_of_error _ (fun h => by cases h)

theorem pureStepProps_pop (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .POP arg s) s := by
  show PureStepProps
    (match s.stack.pop with
      | some ⟨rest, _⟩ => .ok <| s.replaceStackAndIncrPC rest
      | _ => .error .StackUnderflow) s
  cases s.stack.pop with
  | none => exact pureStepProps_of_error _ (fun h => by cases h)
  | some popped => exact pureStepProps_of_ok rfl

theorem pureStepProps_mload (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .MLOAD arg s) s := by
  show PureStepProps
    (match s.stack.pop with
      | some ⟨rest, μ₀⟩ => Id.run do
          let (v, mState') := s.toMachineState.mload μ₀
          let s' := { s with toMachineState := mState' }
          .ok <| s'.replaceStackAndIncrPC (rest.push v)
      | _ => .error .StackUnderflow) s
  cases s.stack.pop with
  | none => exact pureStepProps_of_error _ (fun h => by cases h)
  | some popped => exact pureStepProps_of_ok rfl

theorem pureStepProps_returndatacopy (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .RETURNDATACOPY arg s) s := by
  show PureStepProps
    (match s.stack.pop3 with
      | some ⟨rest, μ₀, μ₁, μ₂⟩ => do
          if s.returnData.size < μ₁.toNat + μ₂.toNat then
            .error .InvalidMemoryAccess
          let mState' := s.toMachineState.returndatacopy μ₀ μ₁ μ₂
          let s' := { s with toMachineState := mState' }
          .ok <| s'.replaceStackAndIncrPC rest
      | _ => .error .StackUnderflow) s
  cases s.stack.pop3 with
  | none => exact pureStepProps_of_error _ (fun h => by cases h)
  | some popped =>
      obtain ⟨rest, μ₀, μ₁, μ₂⟩ := popped
      show PureStepProps
        (if s.returnData.size < μ₁.toNat + μ₂.toNat then
          Except.error .InvalidMemoryAccess
        else
          .ok
            ((({ s with
              toMachineState :=
                s.toMachineState.returndatacopy μ₀ μ₁ μ₂ } :
              EvmYul.EVM.State)).replaceStackAndIncrPC rest)) s
      by_cases hSize : s.returnData.size < μ₁.toNat + μ₂.toNat
      · rw [if_pos hSize]
        exact pureStepProps_of_error _ (fun h => by cases h)
      · rw [if_neg hSize]
        exact pureStepProps_of_ok rfl

theorem pureStepProps_selfdestruct (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .SELFDESTRUCT arg s) s := by
  show PureStepProps
    (match s.stack.pop with
      | some ⟨tail, recipient⟩ =>
          .ok <| EvmYul.EVM.selfdestructState s recipient tail
      | _ => .error .StackUnderflow) s
  cases s.stack.pop with
  | none => exact pureStepProps_of_error _ (fun h => by cases h)
  | some popped => exact pureStepProps_of_ok rfl

theorem pureStepProps_jump (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .JUMP arg s) s := by
  show PureStepProps
    (match s.stack.pop with
      | some ⟨rest, μ₀⟩ => .ok { s with pc := μ₀, stack := rest }
      | _ => .error .StackUnderflow) s
  cases s.stack.pop with
  | none => exact pureStepProps_of_error _ (fun h => by cases h)
  | some popped => exact pureStepProps_of_ok rfl

theorem pureStepProps_jumpi (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .JUMPI arg s) s := by
  show PureStepProps
    (match s.stack.pop2 with
      | some ⟨rest, μ₀, μ₁⟩ =>
          .ok { s with
            pc := if μ₁ != ⟨0⟩ then μ₀ else s.pc + ⟨1⟩, stack := rest }
      | _ => .error .StackUnderflow) s
  cases s.stack.pop2 with
  | none => exact pureStepProps_of_error _ (fun h => by cases h)
  | some popped => exact pureStepProps_of_ok rfl

theorem pureStepProps_pc (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .PC arg s) s :=
  pureStepProps_of_ok rfl

theorem pureStepProps_jumpdest (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) .JUMPDEST arg s) s :=
  pureStepProps_of_ok rfl

theorem pureStepProps_push0 (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps (EvmYul.step (τ := .EVM) (.Push .PUSH0) arg s) s :=
  pureStepProps_of_ok rfl

theorem pureStepProps_pushArg (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) :
    PureStepProps
      (match arg with
        | some (v, width) =>
            .ok <| s.replaceStackAndIncrPC (s.stack.push v)
              (pcΔ := width.succ)
        | _ => .error .StackUnderflow) s := by
  cases arg with
  | none => exact pureStepProps_of_error _ (fun h => by cases h)
  | some vw => exact pureStepProps_of_ok rfl

/-- The six external-frame opcodes handled directly by the charged `EVM.step`
before it delegates to the shared pure interpreter. -/
def externalOps : List (EvmYul.Operation .EVM) :=
  [.CREATE, .CREATE2, .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL]

/-- The shared pure step preserves `gasAvailable` on success and never
reports structural fuel exhaustion, for every instruction outside the
CALL/CREATE families. -/
theorem evmyulStep_props
    (w : EvmYul.Operation .EVM) (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State)
    (hw : w ∉ externalOps) :
    PureStepProps (EvmYul.step (τ := .EVM) w arg s) s := by
  cases w with
  | StopArith p =>
      cases p with
      | STOP => exact pureStepProps_stop arg s
      | ADD => exact pureStepProps_execBinOp EvmYul.UInt256.add s
      | MUL => exact pureStepProps_execBinOp EvmYul.UInt256.mul s
      | SUB => exact pureStepProps_execBinOp EvmYul.UInt256.sub s
      | DIV => exact pureStepProps_execBinOp EvmYul.UInt256.div s
      | SDIV => exact pureStepProps_execBinOp EvmYul.UInt256.sdiv s
      | MOD => exact pureStepProps_execBinOp EvmYul.UInt256.mod s
      | SMOD => exact pureStepProps_execBinOp EvmYul.UInt256.smod s
      | ADDMOD => exact pureStepProps_execTriOp EvmYul.UInt256.addMod s
      | MULMOD => exact pureStepProps_execTriOp EvmYul.UInt256.mulMod s
      | EXP => exact pureStepProps_execBinOp EvmYul.UInt256.exp s
      | SIGNEXTEND =>
          exact pureStepProps_execBinOp EvmYul.UInt256.signextend s
  | CompBit p =>
      cases p with
      | LT => exact pureStepProps_execBinOp EvmYul.UInt256.lt s
      | GT => exact pureStepProps_execBinOp EvmYul.UInt256.gt s
      | SLT => exact pureStepProps_execBinOp EvmYul.UInt256.slt s
      | SGT => exact pureStepProps_execBinOp EvmYul.UInt256.sgt s
      | EQ => exact pureStepProps_execBinOp EvmYul.UInt256.eq s
      | ISZERO => exact pureStepProps_execUnOp EvmYul.UInt256.isZero s
      | AND => exact pureStepProps_execBinOp EvmYul.UInt256.land s
      | OR => exact pureStepProps_execBinOp EvmYul.UInt256.lor s
      | XOR => exact pureStepProps_execBinOp EvmYul.UInt256.xor s
      | NOT => exact pureStepProps_execUnOp EvmYul.UInt256.lnot s
      | BYTE => exact pureStepProps_execBinOp EvmYul.UInt256.byteAt s
      | SHL =>
          exact pureStepProps_execBinOp (flip EvmYul.UInt256.shiftLeft) s
      | SHR =>
          exact pureStepProps_execBinOp (flip EvmYul.UInt256.shiftRight) s
      | SAR => exact pureStepProps_execBinOp EvmYul.UInt256.sar s
      | CLZ => exact pureStepProps_execUnOp EvmYul.UInt256.clz s
  | Keccak p =>
      cases p with
      | KECCAK256 =>
          exact pureStepProps_binaryMachineStateOp'
            EvmYul.MachineState.keccak256 (fun _ _ _ => rfl) s
  | Env p =>
      cases p with
      | ADDRESS =>
          exact pureStepProps_executionEnvOp
            (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.codeOwner) s
      | BALANCE => exact pureStepProps_unaryStateOp EvmYul.State.balance s
      | ORIGIN =>
          exact pureStepProps_executionEnvOp
            (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.sender) s
      | CALLER =>
          exact pureStepProps_executionEnvOp
            (.ofNat ∘ Fin.val ∘ EvmYul.ExecutionEnv.source) s
      | CALLVALUE =>
          exact pureStepProps_executionEnvOp EvmYul.ExecutionEnv.weiValue s
      | CALLDATALOAD =>
          exact pureStepProps_unaryStateOp
            (fun st v => (st, EvmYul.State.calldataload st v)) s
      | CALLDATASIZE =>
          exact pureStepProps_executionEnvOp
            (.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.calldata) s
      | CALLDATACOPY =>
          exact pureStepProps_ternaryCopyOp
            EvmYul.SharedState.calldatacopy (fun _ _ _ _ => rfl) s
      | GASPRICE =>
          exact pureStepProps_executionEnvOp
            (.ofNat ∘ EvmYul.ExecutionEnv.gasPrice) s
      | CODESIZE =>
          exact pureStepProps_executionEnvOp
            (.ofNat ∘ ByteArray.size ∘ EvmYul.ExecutionEnv.code) s
      | CODECOPY =>
          exact pureStepProps_ternaryCopyOp
            EvmYul.SharedState.codeCopy (fun _ _ _ _ => rfl) s
      | EXTCODESIZE =>
          exact pureStepProps_unaryStateOp EvmYul.State.extCodeSize s
      | EXTCODECOPY =>
          exact pureStepProps_quaternaryCopyOp
            EvmYul.SharedState.extCodeCopy' (fun _ _ _ _ _ => rfl) s
      | RETURNDATASIZE =>
          exact pureStepProps_machineStateOp
            EvmYul.MachineState.returndatasize s
      | RETURNDATACOPY => exact pureStepProps_returndatacopy arg s
      | EXTCODEHASH =>
          exact pureStepProps_unaryStateOp EvmYul.State.extCodeHash s
  | Block p =>
      cases p with
      | BLOCKHASH =>
          exact pureStepProps_unaryStateOp
            (fun st v => (st, EvmYul.State.blockHash st v)) s
      | COINBASE =>
          exact pureStepProps_stateOp
            (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase) s
      | TIMESTAMP => exact pureStepProps_stateOp EvmYul.State.timeStamp s
      | NUMBER => exact pureStepProps_stateOp EvmYul.State.number s
      | PREVRANDAO =>
          exact pureStepProps_executionEnvOp EvmYul.prevRandao s
      | GASLIMIT => exact pureStepProps_stateOp EvmYul.State.gasLimit s
      | CHAINID => exact pureStepProps_stateOp EvmYul.State.chainId s
      | SELFBALANCE =>
          exact pureStepProps_stateOp EvmYul.State.selfbalance s
      | BASEFEE => exact pureStepProps_executionEnvOp EvmYul.basefee s
      | BLOBHASH =>
          exact pureStepProps_unaryExecutionEnvOp EvmYul.blobhash s
      | BLOBBASEFEE =>
          exact pureStepProps_executionEnvOp
            EvmYul.ExecutionEnv.getBlobGasprice s
  | StackMemFlow p =>
      cases p with
      | POP => exact pureStepProps_pop arg s
      | MLOAD => exact pureStepProps_mload arg s
      | MSTORE =>
          exact pureStepProps_binaryMachineStateOp
            EvmYul.MachineState.mstore (fun _ _ _ => rfl) s
      | SLOAD => exact pureStepProps_unaryStateOp EvmYul.State.sload s
      | SSTORE => exact pureStepProps_binaryStateOp EvmYul.State.sstore s
      | MSTORE8 =>
          exact pureStepProps_binaryMachineStateOp
            EvmYul.MachineState.mstore8 (fun _ _ _ => rfl) s
      | JUMP => exact pureStepProps_jump arg s
      | JUMPI => exact pureStepProps_jumpi arg s
      | PC => exact pureStepProps_pc arg s
      | MSIZE =>
          exact pureStepProps_machineStateOp EvmYul.MachineState.msize s
      | GAS => exact pureStepProps_machineStateOp EvmYul.MachineState.gas s
      | JUMPDEST => exact pureStepProps_jumpdest arg s
      | TLOAD => exact pureStepProps_unaryStateOp EvmYul.State.tload s
      | TSTORE => exact pureStepProps_binaryStateOp EvmYul.State.tstore s
      | MCOPY =>
          exact pureStepProps_ternaryMachineStateOp
            EvmYul.MachineState.mcopy (fun _ _ _ _ => rfl) s
  | Push p =>
      cases p with
      | PUSH0 => exact pureStepProps_push0 arg s
      | PUSH1 => exact pureStepProps_pushArg arg s
      | PUSH2 => exact pureStepProps_pushArg arg s
      | PUSH3 => exact pureStepProps_pushArg arg s
      | PUSH4 => exact pureStepProps_pushArg arg s
      | PUSH5 => exact pureStepProps_pushArg arg s
      | PUSH6 => exact pureStepProps_pushArg arg s
      | PUSH7 => exact pureStepProps_pushArg arg s
      | PUSH8 => exact pureStepProps_pushArg arg s
      | PUSH9 => exact pureStepProps_pushArg arg s
      | PUSH10 => exact pureStepProps_pushArg arg s
      | PUSH11 => exact pureStepProps_pushArg arg s
      | PUSH12 => exact pureStepProps_pushArg arg s
      | PUSH13 => exact pureStepProps_pushArg arg s
      | PUSH14 => exact pureStepProps_pushArg arg s
      | PUSH15 => exact pureStepProps_pushArg arg s
      | PUSH16 => exact pureStepProps_pushArg arg s
      | PUSH17 => exact pureStepProps_pushArg arg s
      | PUSH18 => exact pureStepProps_pushArg arg s
      | PUSH19 => exact pureStepProps_pushArg arg s
      | PUSH20 => exact pureStepProps_pushArg arg s
      | PUSH21 => exact pureStepProps_pushArg arg s
      | PUSH22 => exact pureStepProps_pushArg arg s
      | PUSH23 => exact pureStepProps_pushArg arg s
      | PUSH24 => exact pureStepProps_pushArg arg s
      | PUSH25 => exact pureStepProps_pushArg arg s
      | PUSH26 => exact pureStepProps_pushArg arg s
      | PUSH27 => exact pureStepProps_pushArg arg s
      | PUSH28 => exact pureStepProps_pushArg arg s
      | PUSH29 => exact pureStepProps_pushArg arg s
      | PUSH30 => exact pureStepProps_pushArg arg s
      | PUSH31 => exact pureStepProps_pushArg arg s
      | PUSH32 => exact pureStepProps_pushArg arg s
  | Dup p =>
      cases p with
      | DUP1 => exact pureStepProps_dup 1 s
      | DUP2 => exact pureStepProps_dup 2 s
      | DUP3 => exact pureStepProps_dup 3 s
      | DUP4 => exact pureStepProps_dup 4 s
      | DUP5 => exact pureStepProps_dup 5 s
      | DUP6 => exact pureStepProps_dup 6 s
      | DUP7 => exact pureStepProps_dup 7 s
      | DUP8 => exact pureStepProps_dup 8 s
      | DUP9 => exact pureStepProps_dup 9 s
      | DUP10 => exact pureStepProps_dup 10 s
      | DUP11 => exact pureStepProps_dup 11 s
      | DUP12 => exact pureStepProps_dup 12 s
      | DUP13 => exact pureStepProps_dup 13 s
      | DUP14 => exact pureStepProps_dup 14 s
      | DUP15 => exact pureStepProps_dup 15 s
      | DUP16 => exact pureStepProps_dup 16 s
  | Exchange p =>
      cases p with
      | SWAP1 => exact pureStepProps_swap 1 s
      | SWAP2 => exact pureStepProps_swap 2 s
      | SWAP3 => exact pureStepProps_swap 3 s
      | SWAP4 => exact pureStepProps_swap 4 s
      | SWAP5 => exact pureStepProps_swap 5 s
      | SWAP6 => exact pureStepProps_swap 6 s
      | SWAP7 => exact pureStepProps_swap 7 s
      | SWAP8 => exact pureStepProps_swap 8 s
      | SWAP9 => exact pureStepProps_swap 9 s
      | SWAP10 => exact pureStepProps_swap 10 s
      | SWAP11 => exact pureStepProps_swap 11 s
      | SWAP12 => exact pureStepProps_swap 12 s
      | SWAP13 => exact pureStepProps_swap 13 s
      | SWAP14 => exact pureStepProps_swap 14 s
      | SWAP15 => exact pureStepProps_swap 15 s
      | SWAP16 => exact pureStepProps_swap 16 s
  | Log p =>
      cases p with
      | LOG0 => exact pureStepProps_log0Op s
      | LOG1 => exact pureStepProps_log1Op s
      | LOG2 => exact pureStepProps_log2Op s
      | LOG3 => exact pureStepProps_log3Op s
      | LOG4 => exact pureStepProps_log4Op s
  | System p =>
      cases p with
      | CREATE => exact (hw (by decide)).elim
      | CALL => exact (hw (by decide)).elim
      | CALLCODE => exact (hw (by decide)).elim
      | RETURN =>
          exact pureStepProps_binaryMachineStateOp
            EvmYul.MachineState.evmReturn (fun _ _ _ => rfl) s
      | DELEGATECALL => exact (hw (by decide)).elim
      | CREATE2 => exact (hw (by decide)).elim
      | STATICCALL => exact (hw (by decide)).elim
      | REVERT =>
          exact pureStepProps_binaryMachineStateOp
            EvmYul.MachineState.evmRevert (fun _ _ _ => rfl) s
      | INVALID => exact pureStepProps_invalid arg s
      | SELFDESTRUCT => exact pureStepProps_selfdestruct arg s

end PureStep

/-! ## Precompiled contracts never mint gas -/

section Precompiles

theorem uint256_zero_toNat :
    ({ val := 0 } : EvmYul.UInt256).toNat = 0 := by
  simp [EvmYul.UInt256.toNat]

theorem sub_ofNat_toNat_le {g : EvmYul.UInt256} (n : Nat)
    (h : ¬ g.toNat < n) :
    (g - EvmYul.UInt256.ofNat n).toNat ≤ g.toNat := by
  rw [uint256_toNat_sub_ofNat_of_le (Nat.le_of_not_lt h)]
  omega

set_option maxHeartbeats 1600000 in
/-- Every precompiled contract returns at most the gas it was given. -/
theorem runPrecompiledContract_gas_le {τ : EvmYul.OperationType}
    (p : EvmYul.PrecompiledContract) (σ : EvmYul.AccountMap τ)
    (g : EvmYul.UInt256) (A : EvmYul.Substate)
    (I : EvmYul.ExecutionEnv τ) :
    (_root_.runPrecompiledContract p σ g A I).2.2.1.toNat ≤ g.toNat := by
  cases p <;>
    simp only [_root_.runPrecompiledContract, Ξ_ECREC, Ξ_SHA256, Ξ_RIP160,
      Ξ_ID, Ξ_EXPMOD, Ξ_BN_ADD, Ξ_BN_MUL, Ξ_SNARKV, Ξ_BLAKE2_F,
      Ξ_PointEval] <;>
    (repeat' split) <;>
    first
      | exact sub_ofNat_toNat_le _ (by assumption)
      | simp [uint256_zero_toNat]
      | (show ({ val := 0 } : EvmYul.UInt256).toNat ≤ g.toNat;
          simp [uint256_zero_toNat])

end Precompiles

/-! ## The master fuel-bound induction

One property bundle per function of the `EvmYul.EVM` mutual block.  The
`OutOfFuel`-freedom side of each bundle carries the fuel threshold; the
gas-monotonicity side (needed to thread the induction through CALL/CREATE
returns and the `X` recursion) is unconditional in the fuel. -/

section Master

open EvmYul.EVM.InstructionGasGroups

/-- Fuel/gas bundle for the frame interpreter `EVM.X`. -/
def XProps (n : Nat) : Prop :=
  ∀ (vj : Array EvmYul.UInt256) (s : EvmYul.EVM.State),
    (s.gasAvailable.toNat + 6 ≤ n →
      EvmYul.EVM.X n vj s ≠ .error .OutOfFuel) ∧
    (∀ s' o, EvmYul.EVM.X n vj s = .ok (.success s' o) →
      s'.gasAvailable.toNat ≤ s.gasAvailable.toNat) ∧
    (∀ g o, EvmYul.EVM.X n vj s = .ok (.revert g o) →
      g.toNat ≤ s.gasAvailable.toNat)

/-- Fuel/gas bundle for the charged instruction step `EVM.step`, invoked the
way `EVM.X` invokes it: with the dynamic charge `C'` for the decoded
instruction, which the `Z` prechecks have verified to be affordable. -/
def StepFProps (n : Nat) : Prop :=
  ∀ (w : EvmYul.Operation .EVM) (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State),
    EvmYul.EVM.δ w ≠ none →
    EvmYul.EVM.C' s w ≤ s.gasAvailable.toNat →
    (s.gasAvailable.toNat + 5 ≤ n →
      EvmYul.EVM.step n (EvmYul.EVM.C' s w) (some (w, arg)) s ≠
        .error .OutOfFuel) ∧
    (∀ s',
      EvmYul.EVM.step n (EvmYul.EVM.C' s w) (some (w, arg)) s = .ok s' →
      s'.gasAvailable.toNat ≤ s.gasAvailable.toNat ∧
        (w ∉ Wzero →
          s'.gasAvailable.toNat + 1 ≤ s.gasAvailable.toNat))

/-- Fuel/gas bundle for the CALL-family helper `EVM.call`. -/
def CallProps (n : Nat) : Prop :=
  ∀ (gasCost : Nat) (bvh : List ByteArray)
    (gasP source recipient t value value' inO inS outO outS :
      EvmYul.UInt256)
    (perm : Bool) (s : EvmYul.EVM.State),
    (EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 t)
        (EvmYul.AccountAddress.ofUInt256 recipient) value gasP
        s.accountMap s.toMachineState s.substate + 9 ≤ n →
      EvmYul.EVM.call n gasCost bvh gasP source recipient t value value'
        inO inS outO outS perm s ≠ .error .OutOfFuel) ∧
    (∀ x s',
      EvmYul.EVM.call n gasCost bvh gasP source recipient t value value'
        inO inS outO outS perm s = .ok (x, s') →
      gasCost ≤ s.gasAvailable.toNat →
      EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 t)
        (EvmYul.AccountAddress.ofUInt256 recipient) value gasP
        s.accountMap s.toMachineState s.substate + 100 ≤ gasCost →
      s'.gasAvailable.toNat + 100 ≤ s.gasAvailable.toNat)

/-- Fuel/gas bundle for the message-call boundary `EVM.Θ`. -/
def ThetaProps (n : Nat) : Prop :=
  ∀ (bvh : List ByteArray)
    (cA : Batteries.RBSet EvmYul.AccountAddress compare)
    (gbh : EvmYul.BlockHeader) (blocks : EvmYul.ProcessedBlocks)
    (σ σ₀ : EvmYul.AccountMap .EVM)
    (cctx : EvmYul.EVM.ChildFrameChainContext) (A : EvmYul.Substate)
    (sA oA rA : EvmYul.AccountAddress) (c : EvmYul.ToExecute .EVM)
    (g p v v' : EvmYul.UInt256) (d : ByteArray) (e : Nat)
    (H : EvmYul.BlockHeader) (wperm : Bool),
    (g.toNat + 8 ≤ n →
      EvmYul.EVM.Θ n bvh cA gbh blocks σ σ₀ cctx A sA oA rA c g p v v'
        d e H wperm ≠ .error .OutOfFuel) ∧
    (∀ res,
      EvmYul.EVM.Θ n bvh cA gbh blocks σ σ₀ cctx A sA oA rA c g p v v'
        d e H wperm = .ok res →
      res.2.2.1.toNat ≤ g.toNat)

/-- Fuel/gas bundle for the code-execution boundary `EVM.Ξ`. -/
def XiProps (n : Nat) : Prop :=
  ∀ (cA : Batteries.RBSet EvmYul.AccountAddress compare)
    (gbh : EvmYul.BlockHeader) (blocks : EvmYul.ProcessedBlocks)
    (σ σ₀ : EvmYul.AccountMap .EVM)
    (cctx : EvmYul.EVM.ChildFrameChainContext)
    (g : EvmYul.UInt256) (A : EvmYul.Substate)
    (I : EvmYul.ExecutionEnv .EVM),
    (g.toNat + 7 ≤ n →
      EvmYul.EVM.Ξ n cA gbh blocks σ σ₀ cctx g A I ≠
        .error .OutOfFuel) ∧
    (∀ out o,
      EvmYul.EVM.Ξ n cA gbh blocks σ σ₀ cctx g A I =
        .ok (.success out o) →
      out.2.2.1.toNat ≤ g.toNat) ∧
    (∀ g' o,
      EvmYul.EVM.Ξ n cA gbh blocks σ σ₀ cctx g A I =
        .ok (.revert g' o) →
      g'.toNat ≤ g.toNat)

/-- Fuel/gas bundle for the contract-creation boundary `EVM.Lambda`. -/
def LambdaProps (n : Nat) : Prop :=
  ∀ (bvh : List ByteArray)
    (cA : Batteries.RBSet EvmYul.AccountAddress compare)
    (gbh : EvmYul.BlockHeader) (blocks : EvmYul.ProcessedBlocks)
    (σ σ₀ : EvmYul.AccountMap .EVM)
    (cctx : EvmYul.EVM.ChildFrameChainContext) (A : EvmYul.Substate)
    (sA oA : EvmYul.AccountAddress)
    (g p v : EvmYul.UInt256) (i : ByteArray) (e : EvmYul.UInt256)
    (ζ : Option ByteArray) (H : EvmYul.BlockHeader) (wperm : Bool),
    (g.toNat + 8 ≤ n →
      EvmYul.EVM.Lambda n bvh cA gbh blocks σ σ₀ cctx A sA oA g p v i e
        ζ H wperm ≠ .error .OutOfFuel) ∧
    (∀ res,
      EvmYul.EVM.Lambda n bvh cA gbh blocks σ σ₀ cctx A sA oA g p v i e
        ζ H wperm = .ok res →
      res.2.2.2.1.toNat ≤ g.toNat)

theorem xProps_zero : XProps 0 := by
  intro vj s
  refine ⟨fun h => by omega, fun s' o h => ?_, fun g o h => ?_⟩ <;>
    simp [EvmYul.EVM.X] at h

theorem stepFProps_zero : StepFProps 0 := by
  intro w arg s _ _
  refine ⟨fun h => by omega, fun s' h => ?_⟩
  simp [EvmYul.EVM.step] at h

theorem callProps_zero : CallProps 0 := by
  intro gasCost bvh gasP source recipient t value value' inO inS outO outS
    perm s
  refine ⟨fun h hcall => ?_, fun x s' h => ?_⟩
  · exact absurd h (by omega)
  · simp [EvmYul.EVM.call] at h

theorem thetaProps_zero : ThetaProps 0 := by
  intro bvh cA gbh blocks σ σ₀ cctx A sA oA rA c g p v v' d e H wperm
  refine ⟨fun h => by omega, fun res h => ?_⟩
  simp [EvmYul.EVM.Θ] at h

theorem xiProps_zero : XiProps 0 := by
  intro cA gbh blocks σ σ₀ cctx g A I
  refine ⟨fun h => by omega, fun out o h => ?_, fun g' o h => ?_⟩ <;>
    simp [EvmYul.EVM.Ξ] at h

theorem lambdaProps_zero : LambdaProps 0 := by
  intro bvh cA gbh blocks σ σ₀ cctx A sA oA g p v i e ζ H wperm
  refine ⟨fun h => by omega, fun res h => ?_⟩
  simp [EvmYul.EVM.Lambda] at h

/-! ### The `Ξ` layer -/

theorem xi_eq_of_x_success
    {f : Nat}
    {cA : Batteries.RBSet EvmYul.AccountAddress compare}
    {gbh : EvmYul.BlockHeader} {blocks : EvmYul.ProcessedBlocks}
    {σ σ₀ : EvmYul.AccountMap .EVM}
    {cctx : EvmYul.EVM.ChildFrameChainContext}
    {g : EvmYul.UInt256} {A : EvmYul.Substate}
    {I : EvmYul.ExecutionEnv .EVM}
    {e : EvmYul.EVM.State} {o : ByteArray}
    (hX :
      EvmYul.EVM.X f (EvmYul.EVM.D_J I.code ⟨0⟩)
        (GasfulBridge.xiEntryState cA gbh blocks σ σ₀ cctx g A I) =
        .ok (.success e o)) :
    EvmYul.EVM.Ξ (f + 1) cA gbh blocks σ σ₀ cctx g A I =
      .ok (.success (e.createdAccounts, e.accountMap, e.gasAvailable,
        e.substate) o) := by
  simp only [EvmYul.EVM.Ξ, GasfulBridge.xiEntryState] at hX ⊢
  rw [hX]
  rfl

theorem xi_eq_of_x_revert
    {f : Nat}
    {cA : Batteries.RBSet EvmYul.AccountAddress compare}
    {gbh : EvmYul.BlockHeader} {blocks : EvmYul.ProcessedBlocks}
    {σ σ₀ : EvmYul.AccountMap .EVM}
    {cctx : EvmYul.EVM.ChildFrameChainContext}
    {g : EvmYul.UInt256} {A : EvmYul.Substate}
    {I : EvmYul.ExecutionEnv .EVM}
    {g' : EvmYul.UInt256} {o : ByteArray}
    (hX :
      EvmYul.EVM.X f (EvmYul.EVM.D_J I.code ⟨0⟩)
        (GasfulBridge.xiEntryState cA gbh blocks σ σ₀ cctx g A I) =
        .ok (.revert g' o)) :
    EvmYul.EVM.Ξ (f + 1) cA gbh blocks σ σ₀ cctx g A I =
      .ok (.revert g' o) := by
  simp only [EvmYul.EVM.Ξ, GasfulBridge.xiEntryState] at hX ⊢
  rw [hX]
  rfl

theorem xiEntryState_gasAvailable
    (cA : Batteries.RBSet EvmYul.AccountAddress compare)
    (gbh : EvmYul.BlockHeader) (blocks : EvmYul.ProcessedBlocks)
    (σ σ₀ : EvmYul.AccountMap .EVM)
    (cctx : EvmYul.EVM.ChildFrameChainContext)
    (g : EvmYul.UInt256) (A : EvmYul.Substate)
    (I : EvmYul.ExecutionEnv .EVM) :
    (GasfulBridge.xiEntryState cA gbh blocks σ σ₀ cctx g A I).gasAvailable =
      g := rfl

theorem xiProps_succ (f : Nat) (hX : XProps f) : XiProps (f + 1) := by
  intro cA gbh blocks σ σ₀ cctx g A I
  obtain ⟨hne, hsucc, hrev⟩ :=
    hX (EvmYul.EVM.D_J I.code ⟨0⟩)
      (GasfulBridge.xiEntryState cA gbh blocks σ σ₀ cctx g A I)
  refine ⟨?_, ?_, ?_⟩
  · intro hle h
    cases hXr : EvmYul.EVM.X f (EvmYul.EVM.D_J I.code ⟨0⟩)
        (GasfulBridge.xiEntryState cA gbh blocks σ σ₀ cctx g A I) with
    | error e =>
        rw [GasfulBridge.xi_error_of_x_entry_error hXr] at h
        injection h with h
        subst h
        refine hne ?_ hXr
        rw [xiEntryState_gasAvailable]
        omega
    | ok result =>
        cases result with
        | success e o => rw [xi_eq_of_x_success hXr] at h; cases h
        | revert g' o => rw [xi_eq_of_x_revert hXr] at h; cases h
  · intro out o h
    cases hXr : EvmYul.EVM.X f (EvmYul.EVM.D_J I.code ⟨0⟩)
        (GasfulBridge.xiEntryState cA gbh blocks σ σ₀ cctx g A I) with
    | error e =>
        rw [GasfulBridge.xi_error_of_x_entry_error hXr] at h
        cases h
    | ok result =>
        cases result with
        | success e o' =>
            rw [xi_eq_of_x_success hXr] at h
            cases h
            simpa [xiEntryState_gasAvailable] using hsucc _ _ hXr
        | revert g' o' =>
            rw [xi_eq_of_x_revert hXr] at h
            cases h
  · intro g' o h
    cases hXr : EvmYul.EVM.X f (EvmYul.EVM.D_J I.code ⟨0⟩)
        (GasfulBridge.xiEntryState cA gbh blocks σ σ₀ cctx g A I) with
    | error e =>
        rw [GasfulBridge.xi_error_of_x_entry_error hXr] at h
        cases h
    | ok result =>
        cases result with
        | success e o' =>
            rw [xi_eq_of_x_success hXr] at h
            cases h
        | revert g'' o' =>
            rw [xi_eq_of_x_revert hXr] at h
            cases h
            simpa [xiEntryState_gasAvailable] using hrev _ _ hXr

/-! ### The `Θ` layer -/

theorem execException_eq_outOfFuel_of_beq
    {e : EvmYul.EVM.ExecutionException}
    (h : (e == EvmYul.EVM.ExecutionException.OutOfFuel) = true) :
    e = .OutOfFuel := by
  cases e <;> first
    | rfl
    | exact absurd h (by decide)

theorem theta_outOfFuel_of_xi_outOfFuel
    {f : Nat} {bvh : List ByteArray}
    {cA : Batteries.RBSet EvmYul.AccountAddress compare}
    {gbh : EvmYul.BlockHeader} {blocks : EvmYul.ProcessedBlocks}
    {σ σ₀ : EvmYul.AccountMap .EVM}
    {cctx : EvmYul.EVM.ChildFrameChainContext} {A : EvmYul.Substate}
    {sA oA rA : EvmYul.AccountAddress} {code : ByteArray}
    {g p v v' : EvmYul.UInt256} {d : ByteArray} {e : Nat}
    {H : EvmYul.BlockHeader} {wperm : Bool}
    (hXi :
      EvmYul.EVM.Ξ f cA gbh blocks
        (EvmYul.EVM.thetaCallTransfer σ sA rA v) σ₀ cctx g A
        (EvmYul.EVM.thetaCallExecutionEnv bvh sA oA rA
          (EvmYul.ToExecute.Code code) p v' d e H wperm) =
        .error .OutOfFuel) :
    EvmYul.EVM.Θ (f + 1) bvh cA gbh blocks σ σ₀ cctx A sA oA rA
      (EvmYul.ToExecute.Code code) g p v v' d e H wperm =
      .error .OutOfFuel := by
  simp [EvmYul.EVM.Θ, hXi]
  rfl

theorem theta_eq_of_xi_success
    {f : Nat} {bvh : List ByteArray}
    {cA cA' : Batteries.RBSet EvmYul.AccountAddress compare}
    {gbh : EvmYul.BlockHeader} {blocks : EvmYul.ProcessedBlocks}
    {σ σ₀ σ'' : EvmYul.AccountMap .EVM}
    {cctx : EvmYul.EVM.ChildFrameChainContext} {A A'' : EvmYul.Substate}
    {sA oA rA : EvmYul.AccountAddress} {code : ByteArray}
    {g g' p v v' : EvmYul.UInt256} {d o : ByteArray} {e : Nat}
    {H : EvmYul.BlockHeader} {wperm : Bool}
    (hXi :
      EvmYul.EVM.Ξ f cA gbh blocks
        (EvmYul.EVM.thetaCallTransfer σ sA rA v) σ₀ cctx g A
        (EvmYul.EVM.thetaCallExecutionEnv bvh sA oA rA
          (EvmYul.ToExecute.Code code) p v' d e H wperm) =
        .ok (.success (cA', σ'', g', A'') o)) :
    EvmYul.EVM.Θ (f + 1) bvh cA gbh blocks σ σ₀ cctx A sA oA rA
      (EvmYul.ToExecute.Code code) g p v v' d e H wperm =
      .ok (cA', if σ''.isEmpty then σ else σ'', g',
        if σ''.isEmpty then A else A'', true, o) := by
  simp [EvmYul.EVM.Θ, hXi]

theorem theta_eq_of_xi_revert
    {f : Nat} {bvh : List ByteArray}
    {cA : Batteries.RBSet EvmYul.AccountAddress compare}
    {gbh : EvmYul.BlockHeader} {blocks : EvmYul.ProcessedBlocks}
    {σ σ₀ : EvmYul.AccountMap .EVM}
    {cctx : EvmYul.EVM.ChildFrameChainContext} {A : EvmYul.Substate}
    {sA oA rA : EvmYul.AccountAddress} {code : ByteArray}
    {g g' p v v' : EvmYul.UInt256} {d o : ByteArray} {e : Nat}
    {H : EvmYul.BlockHeader} {wperm : Bool}
    (hXi :
      EvmYul.EVM.Ξ f cA gbh blocks
        (EvmYul.EVM.thetaCallTransfer σ sA rA v) σ₀ cctx g A
        (EvmYul.EVM.thetaCallExecutionEnv bvh sA oA rA
          (EvmYul.ToExecute.Code code) p v' d e H wperm) =
        .ok (.revert g' o)) :
    EvmYul.EVM.Θ (f + 1) bvh cA gbh blocks σ σ₀ cctx A sA oA rA
      (EvmYul.ToExecute.Code code) g p v v' d e H wperm =
      .ok (cA, if σ.isEmpty then σ else σ, g',
        if σ.isEmpty then A else A, false, o) := by
  simp [EvmYul.EVM.Θ, hXi]

theorem thetaProps_succ (f : Nat) (hxi : XiProps f) : ThetaProps (f + 1) := by
  intro bvh cA gbh blocks σ σ₀ cctx A sA oA rA c g p v v' d e H wperm
  cases c with
  | Precompiled pc =>
      rcases hP : _root_.runPrecompiledContract pc
          (EvmYul.EVM.thetaCallTransfer σ sA rA v) g A
          (EvmYul.EVM.thetaCallExecutionEnv bvh sA oA rA
            (EvmYul.ToExecute.Precompiled pc) p v' d e H wperm)
        with ⟨z, σr, gr, Ar, outr⟩
      have hgr : gr.toNat ≤ g.toNat := by
        have hle := runPrecompiledContract_gas_le pc
          (EvmYul.EVM.thetaCallTransfer σ sA rA v) g A
          (EvmYul.EVM.thetaCallExecutionEnv bvh sA oA rA
            (EvmYul.ToExecute.Precompiled pc) p v' d e H wperm)
        rw [hP] at hle
        simpa using hle
      have hres :
          EvmYul.EVM.Θ (f + 1) bvh cA gbh blocks σ σ₀ cctx A sA oA rA
            (EvmYul.ToExecute.Precompiled pc) g p v v' d e H wperm =
            .ok (cA, if σr.isEmpty then σ else σr, gr,
              if σr.isEmpty then A else Ar, z, outr) := by
        simp [EvmYul.EVM.Θ, hP]
      refine ⟨fun hle h => ?_, fun res h => ?_⟩
      · rw [hres] at h
        cases h
      · rw [hres] at h
        cases h
        simpa using hgr
  | Code code =>
      obtain ⟨hXine, hXisucc, hXirev⟩ :=
        hxi cA gbh blocks (EvmYul.EVM.thetaCallTransfer σ sA rA v) σ₀ cctx
          g A
          (EvmYul.EVM.thetaCallExecutionEnv bvh sA oA rA
            (EvmYul.ToExecute.Code code) p v' d e H wperm)
      refine ⟨fun hle h => ?_, fun res h => ?_⟩
      · cases hXi : EvmYul.EVM.Ξ f cA gbh blocks
            (EvmYul.EVM.thetaCallTransfer σ sA rA v) σ₀ cctx g A
            (EvmYul.EVM.thetaCallExecutionEnv bvh sA oA rA
              (EvmYul.ToExecute.Code code) p v' d e H wperm) with
        | error err =>
            by_cases he : err = .OutOfFuel
            · subst he
              exact hXine (by omega) hXi
            · rw [GasfulBridge.theta_rollback_of_xi_error he hXi] at h
              cases h
        | ok result =>
            cases result with
            | success out o =>
                obtain ⟨cA', σ'', g', A''⟩ := out
                rw [theta_eq_of_xi_success hXi] at h
                cases h
            | revert g' o =>
                rw [theta_eq_of_xi_revert hXi] at h
                cases h
      · cases hXi : EvmYul.EVM.Ξ f cA gbh blocks
            (EvmYul.EVM.thetaCallTransfer σ sA rA v) σ₀ cctx g A
            (EvmYul.EVM.thetaCallExecutionEnv bvh sA oA rA
              (EvmYul.ToExecute.Code code) p v' d e H wperm) with
        | error err =>
            by_cases he : err = .OutOfFuel
            · subst he
              rw [theta_outOfFuel_of_xi_outOfFuel hXi] at h
              cases h
            · rw [GasfulBridge.theta_rollback_of_xi_error he hXi] at h
              cases h
              simp [uint256_zero_toNat]
        | ok result =>
            cases result with
            | success out o =>
                obtain ⟨cA', σ'', g', A''⟩ := out
                rw [theta_eq_of_xi_success hXi] at h
                cases h
                simpa using hXisucc _ _ hXi
            | revert g' o =>
                rw [theta_eq_of_xi_revert hXi] at h
                cases h
                simpa using hXirev _ _ hXi

/-! ### The `Lambda` layer -/

/-- The contract-creation boundary after its account prelude: exactly the
code `EVM.Lambda` runs from its inner `Ξ` call onward, with the prelude
values abstracted. -/
def lambdaTail (f : Nat)
    (cA' : Batteries.RBSet EvmYul.AccountAddress compare)
    (gbh : EvmYul.BlockHeader) (blocks : EvmYul.ProcessedBlocks)
    (σ σStar σ₀ : EvmYul.AccountMap .EVM)
    (cctx : EvmYul.EVM.ChildFrameChainContext)
    (g : EvmYul.UInt256) (AStar : EvmYul.Substate)
    (exEnv : EvmYul.ExecutionEnv .EVM) (a : EvmYul.AccountAddress) :
    Except EvmYul.EVM.ExecutionException
      (EvmYul.AccountAddress ×
        Batteries.RBSet EvmYul.AccountAddress compare ×
        EvmYul.AccountMap .EVM × EvmYul.UInt256 × EvmYul.Substate ×
        Bool × ByteArray) :=
  match EvmYul.EVM.Ξ f cA' gbh blocks σStar σ₀ cctx g AStar exEnv with
    | .error e => do
      if e == .OutOfFuel then throw .OutOfFuel
      .ok (a, cA', σ, ⟨0⟩, AStar, false, .empty)
    | .ok (.revert g' o) =>
      .ok (a, cA', σ, g', AStar, false, o)
    | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar)
        returnedData) =>
      let c := GasConstants.Gcodedeposit * returnedData.size
      let F : Bool := Id.run do
        let F₀ : Bool :=
          match σ.find? a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
          | .none => false
        let F₂ : Bool := gStarStar.toNat < c
        let MAX_CODE_SIZE := 24576
        let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
        let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
        pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)
      let σ' : EvmYul.AccountMap .EVM :=
        if F then σ else
          let newAccount' := σStarStar.findD a default
          σStarStar.insert a {newAccount' with code := returnedData}
      let g' := if F then 0 else gStarStar.toNat - c
      let A' := if F then AStar else AStarStar
      let z := not F
      .ok (a, createdAccounts', σ', .ofNat g', A', z, .empty)

set_option linter.unusedSimpArgs false in
theorem lambdaTailProps (f : Nat) (hxi : XiProps f)
    (cA' : Batteries.RBSet EvmYul.AccountAddress compare)
    (gbh : EvmYul.BlockHeader) (blocks : EvmYul.ProcessedBlocks)
    (σ σStar σ₀ : EvmYul.AccountMap .EVM)
    (cctx : EvmYul.EVM.ChildFrameChainContext)
    (g : EvmYul.UInt256) (AStar : EvmYul.Substate)
    (exEnv : EvmYul.ExecutionEnv .EVM) (a : EvmYul.AccountAddress) :
    (g.toNat + 7 ≤ f →
      lambdaTail f cA' gbh blocks σ σStar σ₀ cctx g AStar exEnv a ≠
        .error .OutOfFuel) ∧
    (∀ res,
      lambdaTail f cA' gbh blocks σ σStar σ₀ cctx g AStar exEnv a =
        .ok res →
      res.2.2.2.1.toNat ≤ g.toNat) := by
  obtain ⟨hne, hsucc, hrev⟩ :=
    hxi cA' gbh blocks σStar σ₀ cctx g AStar exEnv
  constructor
  · intro hle h
    unfold lambdaTail at h
    split at h
    · rename_i e heq
      by_cases he : e = .OutOfFuel
      · exact hne hle (he ▸ heq)
      · have hbeq :
            (e == EvmYul.EVM.ExecutionException.OutOfFuel) = false := by
          cases e <;> first
            | (exact absurd rfl he)
            | rfl
        simp only [letFun] at h
        rw [if_neg (by simp [hbeq])] at h
        cases h
    · cases h
    · cases h
  · intro res h
    unfold lambdaTail at h
    split at h
    · rename_i e heq
      by_cases he : e = .OutOfFuel
      · subst he
        simp only [letFun] at h
        rw [if_pos (by rfl)] at h
        cases h
      · have hbeq :
            (e == EvmYul.EVM.ExecutionException.OutOfFuel) = false := by
          cases e <;> first
            | (exact absurd rfl he)
            | rfl
        simp only [letFun] at h
        rw [if_neg (by simp [hbeq])] at h
        cases h
        simp [uint256_zero_toNat]
    · rename_i g' o heq
      cases h
      exact hrev _ _ heq
    · rename_i cA'' σSS gSS ASS ret heq
      have hSS : gSS.toNat ≤ g.toNat := by
        simpa using hsucc (cA'', σSS, gSS, ASS) ret heq
      simp only [letFun] at h
      cases h
      refine Nat.le_trans (uint256_toNat_ofNat_le _) ?_
      (repeat' split) <;> omega

theorem lambdaProps_succ (f : Nat) (hxi : XiProps f) :
    LambdaProps (f + 1) := by
  intro bvh cA gbh blocks σ σ₀ cctx A sA oA g p v i e ζ H wperm
  cases hLA : EvmYul.EVM.Lambda.L_A sA
      ((σ.find? sA |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩) ζ i with
  | none =>
      refine ⟨fun hle h => ?_, fun res h => ?_⟩ <;>
        simp only [EvmYul.EVM.Lambda, hLA] at h
      · injection h with h
        cases h
      · cases h
  | some lA =>
      refine ⟨fun hle h => ?_, fun res h => ?_⟩
      · simp only [EvmYul.EVM.Lambda, hLA] at h
        refine (lambdaTailProps f hxi _ _ _ _ _ _ _ _ _ _ _).1 ?_ h
        omega
      · simp only [EvmYul.EVM.Lambda, hLA] at h
        exact (lambdaTailProps f hxi _ _ _ _ _ _ _ _ _ _ _).2 res h

/-! ### The `call` layer -/

theorem except_bind_error_of_total
    {ε α β : Type} {x : Except ε α} {k : α → Except ε β}
    (hk : ∀ b, ∃ c, k b = .ok c) {e : ε}
    (h : (x >>= k) = .error e) : x = .error e := by
  cases x with
  | error e' =>
      injection h with h
      rw [h]
  | ok b =>
      obtain ⟨c, hc⟩ := hk b
      rw [show ((Except.ok b : Except ε α) >>= k) = k b from rfl, hc] at h
      cases h

theorem except_bind_ok
    {ε α β : Type} {x : Except ε α} {k : α → Except ε β} {c : β}
    (h : (x >>= k) = .ok c) : ∃ b, x = .ok b ∧ k b = .ok c := by
  cases x with
  | error e' => cases h
  | ok b => exact ⟨b, rfl, h⟩

theorem callProps_succ (f : Nat) (htheta : ThetaProps f) :
    CallProps (f + 1) := by
  intro gasCost bvh gasP source recipient t value value' inO inS outO outS
    perm s
  have hOf := uint256_toNat_ofNat_le
    (EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 t)
      (EvmYul.AccountAddress.ofUInt256 recipient) value gasP
      s.accountMap s.toMachineState s.substate)
  constructor
  · intro hle h
    simp only [EvmYul.EVM.call] at h
    split at h
    · have hΘ := except_bind_error_of_total (fun b => ⟨_, rfl⟩) h
      exact (htheta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1
        (by omega) hΘ
    · cases h
  · intro x s' h hcost hcg
    simp only [EvmYul.EVM.call] at h
    split at h
    · obtain ⟨rΘ, hΘ, hk⟩ := except_bind_ok h
      have hΘgas :=
        (htheta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 rΘ hΘ
      cases hk
      have hadd : ((s.gasAvailable - EvmYul.UInt256.ofNat gasCost) +
            rΘ.2.2.1).toNat ≤
          (s.gasAvailable - EvmYul.UInt256.ofNat gasCost).toNat +
            rΘ.2.2.1.toNat :=
        uint256_toNat_add_le _ _
      rw [uint256_toNat_sub_ofNat_of_le hcost] at hadd
      show ((s.gasAvailable - EvmYul.UInt256.ofNat gasCost) +
          rΘ.2.2.1).toNat + 100 ≤ s.gasAvailable.toNat
      omega
    · cases h
      have hadd : ((s.gasAvailable - EvmYul.UInt256.ofNat gasCost) +
            EvmYul.UInt256.ofNat
              (EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 t)
                (EvmYul.AccountAddress.ofUInt256 recipient) value gasP
                s.accountMap s.toMachineState s.substate)).toNat ≤
          (s.gasAvailable - EvmYul.UInt256.ofNat gasCost).toNat +
            (EvmYul.UInt256.ofNat
              (EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 t)
                (EvmYul.AccountAddress.ofUInt256 recipient) value gasP
                s.accountMap s.toMachineState s.substate)).toNat :=
        uint256_toNat_add_le _ _
      rw [uint256_toNat_sub_ofNat_of_le hcost] at hadd
      show ((s.gasAvailable - EvmYul.UInt256.ofNat gasCost) +
          EvmYul.UInt256.ofNat
            (EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 t)
              (EvmYul.AccountAddress.ofUInt256 recipient) value gasP
              s.accountMap s.toMachineState s.substate)).toNat + 100 ≤
        s.gasAvailable.toNat
      omega

/-! ### The `step` layer -/

set_option maxHeartbeats 3200000 in
/-- Outside the CALL/CREATE families, the charged `EVM.step` at positive fuel
is the shared pure step on the charged frame. -/
theorem evmStep_eq_pureStep (f gasCost : Nat)
    (w : EvmYul.Operation .EVM) (arg : Option (EvmYul.UInt256 × Nat))
    (s : EvmYul.EVM.State) (hw : w ∉ externalOps) :
    EvmYul.EVM.step (f + 1) gasCost (some (w, arg)) s =
      EvmYul.step (τ := .EVM) w arg
        { s with
            execLength := s.execLength + 1,
            gasAvailable := s.gasAvailable - EvmYul.UInt256.ofNat gasCost } := by
  cases w <;> rename_i p <;> cases p <;>
    first
      | exact (hw (by decide)).elim
      | rfl

theorem accountAddress_ofUInt256_ofNat (a : EvmYul.AccountAddress) :
    EvmYul.AccountAddress.ofUInt256 (EvmYul.UInt256.ofNat ↑a) = a := by
  have hlt : (a : Nat) < EvmYul.UInt256.size :=
    Nat.lt_trans a.isLt (by norm_num [EvmYul.AccountAddress.size,
      EvmYul.UInt256.size])
  apply Fin.ext
  show (EvmYul.UInt256.ofNat ↑a).val.val % EvmYul.AccountAddress.size %
      EvmYul.AccountAddress.size = _
  have hofNat : (EvmYul.UInt256.ofNat ↑a).val.val = (a : Nat) :=
    uint256_toNat_ofNat_of_lt hlt
  rw [hofNat, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt a.isLt]

theorem stack_shape_of_pop7 {st : EvmYul.Stack EvmYul.UInt256}
    {rest : EvmYul.Stack EvmYul.UInt256}
    {μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : EvmYul.UInt256}
    (h : st.pop7 = some (rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆)) :
    st = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: rest := by
  unfold EvmYul.Stack.pop7 at h
  split at h
  · cases h
    rfl
  · cases h

theorem stack_shape_of_pop6 {st : EvmYul.Stack EvmYul.UInt256}
    {rest : EvmYul.Stack EvmYul.UInt256}
    {μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ : EvmYul.UInt256}
    (h : st.pop6 = some (rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅)) :
    st = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: rest := by
  unfold EvmYul.Stack.pop6 at h
  split at h
  · cases h
    rfl
  · cases h

theorem evmStep_call_none (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    (hPop : s.stack.pop7 = none) :
    EvmYul.EVM.step (f + 1) gasCost (some (.CALL, arg)) s =
      .error .StackUnderflow := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_call_some (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    {rest : EvmYul.Stack EvmYul.UInt256}
    {μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : EvmYul.UInt256}
    (hPop : s.stack.pop7 = some (rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆)) :
    EvmYul.EVM.step (f + 1) gasCost (some (.CALL, arg)) s =
      (EvmYul.EVM.call f gasCost s.executionEnv.blobVersionedHashes μ₀
        (.ofNat ↑s.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
        s.executionEnv.perm
        { s with execLength := s.execLength + 1 }) >>= fun r =>
        .ok (r.2.replaceStackAndIncrPC (rest.push r.1)) := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_callcode_none (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    (hPop : s.stack.pop7 = none) :
    EvmYul.EVM.step (f + 1) gasCost (some (.CALLCODE, arg)) s =
      .error .StackUnderflow := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_callcode_some (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    {rest : EvmYul.Stack EvmYul.UInt256}
    {μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : EvmYul.UInt256}
    (hPop : s.stack.pop7 = some (rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆)) :
    EvmYul.EVM.step (f + 1) gasCost (some (.CALLCODE, arg)) s =
      (EvmYul.EVM.call f gasCost s.executionEnv.blobVersionedHashes μ₀
        (.ofNat ↑s.executionEnv.codeOwner)
        (.ofNat ↑s.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆
        s.executionEnv.perm
        { s with execLength := s.execLength + 1 }) >>= fun r =>
        .ok (r.2.replaceStackAndIncrPC (rest.push r.1)) := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_delegatecall_none (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    (hPop : s.stack.pop6 = none) :
    EvmYul.EVM.step (f + 1) gasCost (some (.DELEGATECALL, arg)) s =
      .error .StackUnderflow := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_delegatecall_some (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    {rest : EvmYul.Stack EvmYul.UInt256}
    {μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ : EvmYul.UInt256}
    (hPop : s.stack.pop6 = some (rest, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆)) :
    EvmYul.EVM.step (f + 1) gasCost (some (.DELEGATECALL, arg)) s =
      (EvmYul.EVM.call f gasCost s.executionEnv.blobVersionedHashes μ₀
        (.ofNat ↑s.executionEnv.source)
        (.ofNat ↑s.executionEnv.codeOwner) μ₁ ⟨0⟩
        s.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆
        s.executionEnv.perm
        { s with execLength := s.execLength + 1 }) >>= fun r =>
        .ok (r.2.replaceStackAndIncrPC (rest.push r.1)) := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_staticcall_none (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    (hPop : s.stack.pop6 = none) :
    EvmYul.EVM.step (f + 1) gasCost (some (.STATICCALL, arg)) s =
      .error .StackUnderflow := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_staticcall_some (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    {rest : EvmYul.Stack EvmYul.UInt256}
    {μ₀ μ₁ μ₃ μ₄ μ₅ μ₆ : EvmYul.UInt256}
    (hPop : s.stack.pop6 = some (rest, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆)) :
    EvmYul.EVM.step (f + 1) gasCost (some (.STATICCALL, arg)) s =
      (EvmYul.EVM.call f gasCost s.executionEnv.blobVersionedHashes μ₀
        (.ofNat ↑s.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆
        false
        { s with execLength := s.execLength + 1 }) >>= fun r =>
        .ok (r.2.replaceStackAndIncrPC (rest.push r.1)) := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem L_le (n : Nat) : EvmYul.EVM.L n ≤ n := by
  unfold EvmYul.EVM.L
  omega

theorem create_gas_bound {gAvail : EvmYul.UInt256} {cost : Nat}
    {g' : EvmYul.UInt256}
    (hcost' : cost ≤ gAvail.toNat) (hpos : 1 ≤ cost)
    (hg' : g'.toNat ≤
      EvmYul.EVM.L ((gAvail - EvmYul.UInt256.ofNat cost).toNat)) :
    (EvmYul.UInt256.ofNat
        ((gAvail - EvmYul.UInt256.ofNat cost).toNat -
          EvmYul.EVM.L ((gAvail - EvmYul.UInt256.ofNat cost).toNat) +
          g'.toNat)).toNat + 1 ≤ gAvail.toNat := by
  have h1 := uint256_toNat_ofNat_le
    ((gAvail - EvmYul.UInt256.ofNat cost).toNat -
      EvmYul.EVM.L ((gAvail - EvmYul.UInt256.ofNat cost).toNat) +
      g'.toNat)
  have h2 := uint256_toNat_sub_ofNat_of_le hcost'
  have h3 := L_le ((gAvail - EvmYul.UInt256.ofNat cost).toNat)
  omega

section CPrimeCallShapes

open GasConstants

theorem cprime_call_shape (s : EvmYul.EVM.State)
    {μ₀ μ₁ μ₂ : EvmYul.UInt256} {tail : EvmYul.Stack EvmYul.UInt256}
    (hstack : s.stack = μ₀ :: μ₁ :: μ₂ :: tail) :
    EvmYul.EVM.C' s .CALL =
      EvmYul.EVM.Ccall (EvmYul.AccountAddress.ofUInt256 μ₁)
        (EvmYul.AccountAddress.ofUInt256 μ₁) μ₂ μ₀
        s.accountMap s.toMachineState s.substate := by
  simp only [EvmYul.EVM.C', hstack]
  simp

theorem cprime_callcode_shape (s : EvmYul.EVM.State)
    {μ₀ μ₁ μ₂ : EvmYul.UInt256} {tail : EvmYul.Stack EvmYul.UInt256}
    (hstack : s.stack = μ₀ :: μ₁ :: μ₂ :: tail) :
    EvmYul.EVM.C' s .CALLCODE =
      EvmYul.EVM.Ccall (EvmYul.AccountAddress.ofUInt256 μ₁)
        s.executionEnv.codeOwner μ₂ μ₀
        s.accountMap s.toMachineState s.substate := by
  simp only [EvmYul.EVM.C', hstack]
  simp

theorem cprime_delegatecall_shape (s : EvmYul.EVM.State)
    {μ₀ μ₁ : EvmYul.UInt256} {tail : EvmYul.Stack EvmYul.UInt256}
    (hstack : s.stack = μ₀ :: μ₁ :: tail) :
    EvmYul.EVM.C' s .DELEGATECALL =
      EvmYul.EVM.Ccall (EvmYul.AccountAddress.ofUInt256 μ₁)
        s.executionEnv.codeOwner ⟨0⟩ μ₀
        s.accountMap s.toMachineState s.substate := by
  simp only [EvmYul.EVM.C', hstack]
  simp

theorem cprime_staticcall_shape (s : EvmYul.EVM.State)
    {μ₀ μ₁ : EvmYul.UInt256} {tail : EvmYul.Stack EvmYul.UInt256}
    (hstack : s.stack = μ₀ :: μ₁ :: tail) :
    EvmYul.EVM.C' s .STATICCALL =
      EvmYul.EVM.Ccall (EvmYul.AccountAddress.ofUInt256 μ₁)
        (EvmYul.AccountAddress.ofUInt256 μ₁) ⟨0⟩ μ₀
        s.accountMap s.toMachineState s.substate := by
  simp only [EvmYul.EVM.C', hstack]
  simp

theorem hcg_call (s : EvmYul.EVM.State)
    {μ₀ μ₁ μ₂ : EvmYul.UInt256} {tail : EvmYul.Stack EvmYul.UInt256}
    (hstack : s.stack = μ₀ :: μ₁ :: μ₂ :: tail) :
    EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 μ₁)
        (EvmYul.AccountAddress.ofUInt256 μ₁) μ₂ μ₀
        s.accountMap s.toMachineState s.substate + 100 ≤
      EvmYul.EVM.C' s .CALL := by
  rw [cprime_call_shape s hstack]
  have h := ccallgas_add_gwarm_le_ccall
    (EvmYul.AccountAddress.ofUInt256 μ₁)
    (EvmYul.AccountAddress.ofUInt256 μ₁) μ₂ μ₀
    s.accountMap s.toMachineState s.substate
  simpa [Gwarmaccess] using h

theorem hcg_callcode (s : EvmYul.EVM.State)
    {μ₀ μ₁ μ₂ : EvmYul.UInt256} {tail : EvmYul.Stack EvmYul.UInt256}
    (hstack : s.stack = μ₀ :: μ₁ :: μ₂ :: tail) :
    EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 μ₁)
        (EvmYul.AccountAddress.ofUInt256
          (EvmYul.UInt256.ofNat ↑s.executionEnv.codeOwner)) μ₂ μ₀
        s.accountMap s.toMachineState s.substate + 100 ≤
      EvmYul.EVM.C' s .CALLCODE := by
  rw [cprime_callcode_shape s hstack, accountAddress_ofUInt256_ofNat]
  have h := ccallgas_add_gwarm_le_ccall
    (EvmYul.AccountAddress.ofUInt256 μ₁)
    s.executionEnv.codeOwner μ₂ μ₀
    s.accountMap s.toMachineState s.substate
  simpa [Gwarmaccess] using h

theorem hcg_delegatecall (s : EvmYul.EVM.State)
    {μ₀ μ₁ : EvmYul.UInt256} {tail : EvmYul.Stack EvmYul.UInt256}
    (hstack : s.stack = μ₀ :: μ₁ :: tail) :
    EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 μ₁)
        (EvmYul.AccountAddress.ofUInt256
          (EvmYul.UInt256.ofNat ↑s.executionEnv.codeOwner)) ⟨0⟩ μ₀
        s.accountMap s.toMachineState s.substate + 100 ≤
      EvmYul.EVM.C' s .DELEGATECALL := by
  rw [cprime_delegatecall_shape s hstack, accountAddress_ofUInt256_ofNat]
  have h := ccallgas_add_gwarm_le_ccall
    (EvmYul.AccountAddress.ofUInt256 μ₁)
    s.executionEnv.codeOwner ⟨0⟩ μ₀
    s.accountMap s.toMachineState s.substate
  simpa [Gwarmaccess] using h

theorem hcg_staticcall (s : EvmYul.EVM.State)
    {μ₀ μ₁ : EvmYul.UInt256} {tail : EvmYul.Stack EvmYul.UInt256}
    (hstack : s.stack = μ₀ :: μ₁ :: tail) :
    EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 μ₁)
        (EvmYul.AccountAddress.ofUInt256 μ₁) ⟨0⟩ μ₀
        s.accountMap s.toMachineState s.substate + 100 ≤
      EvmYul.EVM.C' s .STATICCALL := by
  rw [cprime_staticcall_shape s hstack]
  have h := ccallgas_add_gwarm_le_ccall
    (EvmYul.AccountAddress.ofUInt256 μ₁)
    (EvmYul.AccountAddress.ofUInt256 μ₁) ⟨0⟩ μ₀
    s.accountMap s.toMachineState s.substate
  simpa [Gwarmaccess] using h

end CPrimeCallShapes

/-- The CREATE/CREATE2 instruction body after the operand pop, with the
prelude values abstracted; exactly the code `EVM.step` runs for the
CREATE-family, so that the charged-state result can be analyzed with
ordinary case splits. -/
def createCore (fInner : Nat) (evmState₀ : EvmYul.EVM.State)
    (gasCost : Nat) (stack : EvmYul.Stack EvmYul.UInt256)
    (μ₀ μ₁ μ₂ : EvmYul.UInt256) (ζ : Option ByteArray) :
    Except EvmYul.EVM.ExecutionException EvmYul.EVM.State := do
  let evmState :=
    { evmState₀ with
        gasAvailable := evmState₀.gasAvailable - EvmYul.UInt256.ofNat gasCost }
  let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
  let I := evmState.executionEnv
  let Iₐ := evmState.executionEnv.codeOwner
  let Iₒ := evmState.executionEnv.sender
  let Iₑ := evmState.executionEnv.depth
  let σ := evmState.accountMap
  let σ_Iₐ : EvmYul.Account .EVM := σ.find? Iₐ |>.getD default
  let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
  let (a, evmState', g', z, o)
        : (EvmYul.AccountAddress × EvmYul.EVM.State × EvmYul.UInt256 ×
            Bool × ByteArray)
    :=
    if σ_Iₐ.nonce.toNat ≥ 2^64-1 then
      (default, evmState, .ofNat (EvmYul.EVM.L evmState.gasAvailable.toNat),
        False, .empty) else
    if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧
        i.size ≤ 49152 then
      let Λ :=
        EvmYul.EVM.Lambda fInner
          evmState.executionEnv.blobVersionedHashes
          evmState.createdAccounts
          evmState.genesisBlockHeader
          evmState.blocks
          σStar
          evmState.σ₀
          { totalGasUsedInBlock := evmState.totalGasUsedInBlock
            transactionReceipts := evmState.transactionReceipts }
          evmState.toState.substate
          Iₐ
          Iₒ
          (.ofNat <| EvmYul.EVM.L evmState.gasAvailable.toNat)
          (.ofNat I.gasPrice)
          μ₀
          i
          (.ofNat <| Iₑ + 1)
          ζ
          I.header
          I.perm
      match Λ with
        | .ok (a, cA, σ', g', A', z, o) =>
          ( a
          , { evmState with
                accountMap := σ'
                substate := A'
                createdAccounts := cA
            }
          , g'
          , z
          , o
          )
        | _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)
    else
      (0, evmState, .ofNat (EvmYul.EVM.L evmState.gasAvailable.toNat),
        False, .empty)
  let x : EvmYul.UInt256 :=
    let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
      if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩
      else .ofNat a
  let newReturnData : ByteArray := if z then .empty else o
  if (evmState.gasAvailable + g').toNat <
      EvmYul.EVM.L (evmState.gasAvailable.toNat) then
    .error .OutOfGass
  let evmState' :=
    { evmState' with
        activeWords :=
          .ofNat <| EvmYul.MachineState.M evmState.activeWords.toNat
            μ₁.toNat μ₂.toNat
        returnData := newReturnData
        H_return := ByteArray.empty
        gasAvailable :=
          .ofNat <| evmState.gasAvailable.toNat -
            EvmYul.EVM.L (evmState.gasAvailable.toNat) + g'.toNat
    }
  .ok <| evmState'.replaceStackAndIncrPC (stack.push x)

set_option linter.unusedSimpArgs false in
theorem createCore_props (fInner : Nat) (hlam : LambdaProps fInner)
    (evmState₀ : EvmYul.EVM.State) (gasCost : Nat)
    (stack : EvmYul.Stack EvmYul.UInt256)
    (μ₀ μ₁ μ₂ : EvmYul.UInt256) (ζ : Option ByteArray)
    (hcost' : gasCost ≤ evmState₀.gasAvailable.toNat)
    (hpos : 1 ≤ gasCost) :
    (createCore fInner evmState₀ gasCost stack μ₀ μ₁ μ₂ ζ ≠
      .error .OutOfFuel) ∧
    (∀ s', createCore fInner evmState₀ gasCost stack μ₀ μ₁ μ₂ ζ = .ok s' →
      s'.gasAvailable.toNat + 1 ≤ evmState₀.gasAvailable.toNat) := by
  constructor
  · intro h
    unfold createCore at h
    simp only [letFun] at h
    repeat' split at h
    all_goals first
      | (injection h with h; cases h)
      | cases h
  · intro s' h
    unfold createCore at h
    simp only [letFun] at h
    repeat' split at h
    all_goals cases h
    all_goals refine create_gas_bound hcost' hpos ?_
    all_goals first
      | exact uint256_toNat_ofNat_le _
      | (simp [uint256_zero_toNat]; done)
      | (refine Nat.le_trans ?_ (uint256_toNat_ofNat_le _)
         simpa using
           ((hlam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 _ (by assumption)))

theorem evmStep_create_none (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    (hPop : s.stack.pop3 = none) :
    EvmYul.EVM.step (f + 1) gasCost (some (.CREATE, arg)) s =
      .error .StackUnderflow := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_create_some (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    {rest : EvmYul.Stack EvmYul.UInt256} {μ₀ μ₁ μ₂ : EvmYul.UInt256}
    (hPop : s.stack.pop3 = some (rest, μ₀, μ₁, μ₂)) :
    EvmYul.EVM.step (f + 1) gasCost (some (.CREATE, arg)) s =
      createCore f { s with execLength := s.execLength + 1 } gasCost rest
        μ₀ μ₁ μ₂ none := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_create2_none (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    (hPop : s.stack.pop4 = none) :
    EvmYul.EVM.step (f + 1) gasCost (some (.CREATE2, arg)) s =
      .error .StackUnderflow := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

theorem evmStep_create2_some (f gasCost : Nat)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    {rest : EvmYul.Stack EvmYul.UInt256} {μ₀ μ₁ μ₂ μ₃ : EvmYul.UInt256}
    (hPop : s.stack.pop4 = some (rest, μ₀, μ₁, μ₂, μ₃)) :
    EvmYul.EVM.step (f + 1) gasCost (some (.CREATE2, arg)) s =
      createCore f { s with execLength := s.execLength + 1 } gasCost rest
        μ₀ μ₁ μ₂ (some (EvmYul.UInt256.toByteArray μ₃)) := by
  simp only [EvmYul.EVM.step, hPop]
  rfl

set_option maxHeartbeats 3200000 in
theorem stepFProps_succ (f : Nat) (hcall : CallProps f)
    (hlam : LambdaProps f) : StepFProps (f + 1) := by
  intro w arg s hδ hcost
  by_cases hw : w ∈ externalOps
  case neg =>
    obtain ⟨hgasPres, hne⟩ := evmyulStep_props w arg
      { s with
          execLength := s.execLength + 1,
          gasAvailable :=
            s.gasAvailable - EvmYul.UInt256.ofNat (EvmYul.EVM.C' s w) } hw
    constructor
    · intro _ h
      rw [evmStep_eq_pureStep f _ w arg s hw] at h
      exact hne h
    · intro s' h
      rw [evmStep_eq_pureStep f _ w arg s hw] at h
      have hg := hgasPres s' h
      have hgn : s'.gasAvailable.toNat =
          s.gasAvailable.toNat - EvmYul.EVM.C' s w := by
        rw [hg]
        exact uint256_toNat_sub_ofNat_of_le hcost
      refine ⟨by omega, fun hzero => ?_⟩
      have hpos := one_le_C' s w hδ hzero
      omega
  case pos =>
    simp only [externalOps, List.mem_cons, List.not_mem_nil, or_false]
      at hw
    have hbump :
        ({ s with execLength := s.execLength + 1 } :
          EvmYul.EVM.State).gasAvailable = s.gasAvailable := rfl
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · -- CREATE
      have hpos : 1 ≤ EvmYul.EVM.C' s .CREATE :=
        one_le_C' s _ hδ (by decide)
      have hkey : ∀ s',
          EvmYul.EVM.step (f + 1) (EvmYul.EVM.C' s (.CREATE))
            (some (.CREATE, arg)) s = .ok s' →
          s'.gasAvailable.toNat + 1 ≤ s.gasAvailable.toNat := by
        intro s' h
        cases hPop : s.stack.pop3 with
        | none =>
            rw [evmStep_create_none f _ arg s hPop] at h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₂⟩ := r
            rw [evmStep_create_some f _ arg s hPop] at h
            exact (createCore_props f hlam
              { s with execLength := s.execLength + 1 }
              (EvmYul.EVM.C' s (.CREATE)) rest μ₀ μ₁ μ₂ none
              hcost hpos).2 s' h
      constructor
      · intro _ h
        cases hPop : s.stack.pop3 with
        | none =>
            rw [evmStep_create_none f _ arg s hPop] at h
            injection h with h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₂⟩ := r
            rw [evmStep_create_some f _ arg s hPop] at h
            exact (createCore_props f hlam
              { s with execLength := s.execLength + 1 }
              (EvmYul.EVM.C' s (.CREATE)) rest μ₀ μ₁ μ₂ none
              hcost hpos).1 h
      · intro s' h
        exact ⟨by have := hkey s' h; omega, fun _ => hkey s' h⟩
    · -- CREATE2
      have hpos : 1 ≤ EvmYul.EVM.C' s .CREATE2 :=
        one_le_C' s _ hδ (by decide)
      have hkey : ∀ s',
          EvmYul.EVM.step (f + 1) (EvmYul.EVM.C' s (.CREATE2))
            (some (.CREATE2, arg)) s = .ok s' →
          s'.gasAvailable.toNat + 1 ≤ s.gasAvailable.toNat := by
        intro s' h
        cases hPop : s.stack.pop4 with
        | none =>
            rw [evmStep_create2_none f _ arg s hPop] at h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₂, μ₃⟩ := r
            rw [evmStep_create2_some f _ arg s hPop] at h
            exact (createCore_props f hlam
              { s with execLength := s.execLength + 1 }
              (EvmYul.EVM.C' s (.CREATE2)) rest μ₀ μ₁ μ₂
              (some (EvmYul.UInt256.toByteArray μ₃))
              hcost hpos).2 s' h
      constructor
      · intro _ h
        cases hPop : s.stack.pop4 with
        | none =>
            rw [evmStep_create2_none f _ arg s hPop] at h
            injection h with h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₂, μ₃⟩ := r
            rw [evmStep_create2_some f _ arg s hPop] at h
            exact (createCore_props f hlam
              { s with execLength := s.execLength + 1 }
              (EvmYul.EVM.C' s (.CREATE2)) rest μ₀ μ₁ μ₂
              (some (EvmYul.UInt256.toByteArray μ₃))
              hcost hpos).1 h
      · intro s' h
        exact ⟨by have := hkey s' h; omega, fun _ => hkey s' h⟩
    · -- CALL
      constructor
      · intro hfuel h
        cases hPop : s.stack.pop7 with
        | none =>
            rw [evmStep_call_none f _ arg s hPop] at h
            injection h with h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := r
            rw [evmStep_call_some f _ arg s hPop] at h
            have hstack := stack_shape_of_pop7 hPop
            have hcg := hcg_call s hstack
            have hCallErr := except_bind_error_of_total
              (fun b => ⟨_, rfl⟩) h
            refine (hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 ?_ hCallErr
            show EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 μ₁)
              (EvmYul.AccountAddress.ofUInt256 μ₁) μ₂ μ₀
              s.accountMap s.toMachineState s.substate + 9 ≤ f
            omega
      · intro s' h
        cases hPop : s.stack.pop7 with
        | none =>
            rw [evmStep_call_none f _ arg s hPop] at h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := r
            rw [evmStep_call_some f _ arg s hPop] at h
            have hstack := stack_shape_of_pop7 hPop
            have hcg := hcg_call s hstack
            obtain ⟨rc, hCall, hk⟩ := except_bind_ok h
            obtain ⟨xc, stc⟩ := rc
            cases hk
            have hres0 :=
              (hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 xc stc hCall
                (by exact hcost) (by exact hcg)
            have hres : stc.gasAvailable.toNat + 100 ≤
                s.gasAvailable.toNat := hres0
            constructor
            · show stc.gasAvailable.toNat ≤ s.gasAvailable.toNat
              omega
            · intro _
              show stc.gasAvailable.toNat + 1 ≤ s.gasAvailable.toNat
              omega
    · -- CALLCODE
      constructor
      · intro hfuel h
        cases hPop : s.stack.pop7 with
        | none =>
            rw [evmStep_callcode_none f _ arg s hPop] at h
            injection h with h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := r
            rw [evmStep_callcode_some f _ arg s hPop] at h
            have hstack := stack_shape_of_pop7 hPop
            have hcg := hcg_callcode s hstack
            have hCallErr := except_bind_error_of_total
              (fun b => ⟨_, rfl⟩) h
            refine (hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 ?_ hCallErr
            show EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 μ₁)
              (EvmYul.AccountAddress.ofUInt256
                (EvmYul.UInt256.ofNat ↑s.executionEnv.codeOwner)) μ₂ μ₀
              s.accountMap s.toMachineState s.substate + 9 ≤ f
            omega
      · intro s' h
        cases hPop : s.stack.pop7 with
        | none =>
            rw [evmStep_callcode_none f _ arg s hPop] at h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆⟩ := r
            rw [evmStep_callcode_some f _ arg s hPop] at h
            have hstack := stack_shape_of_pop7 hPop
            have hcg := hcg_callcode s hstack
            obtain ⟨rc, hCall, hk⟩ := except_bind_ok h
            obtain ⟨xc, stc⟩ := rc
            cases hk
            have hres0 :=
              (hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 xc stc hCall
                (by exact hcost) (by exact hcg)
            have hres : stc.gasAvailable.toNat + 100 ≤
                s.gasAvailable.toNat := hres0
            constructor
            · show stc.gasAvailable.toNat ≤ s.gasAvailable.toNat
              omega
            · intro _
              show stc.gasAvailable.toNat + 1 ≤ s.gasAvailable.toNat
              omega
    · -- DELEGATECALL
      constructor
      · intro hfuel h
        cases hPop : s.stack.pop6 with
        | none =>
            rw [evmStep_delegatecall_none f _ arg s hPop] at h
            injection h with h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩ := r
            rw [evmStep_delegatecall_some f _ arg s hPop] at h
            have hstack : s.stack = μ₀ :: μ₁ :: μ₃ :: μ₄ :: μ₅ :: μ₆ ::
                rest := stack_shape_of_pop6 hPop
            have hcg := hcg_delegatecall s
              (by rw [hstack] :
                s.stack = μ₀ :: μ₁ :: (μ₃ :: μ₄ :: μ₅ :: μ₆ :: rest))
            have hCallErr := except_bind_error_of_total
              (fun b => ⟨_, rfl⟩) h
            refine (hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 ?_ hCallErr
            show EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 μ₁)
              (EvmYul.AccountAddress.ofUInt256
                (EvmYul.UInt256.ofNat ↑s.executionEnv.codeOwner)) ⟨0⟩ μ₀
              s.accountMap s.toMachineState s.substate + 9 ≤ f
            omega
      · intro s' h
        cases hPop : s.stack.pop6 with
        | none =>
            rw [evmStep_delegatecall_none f _ arg s hPop] at h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩ := r
            rw [evmStep_delegatecall_some f _ arg s hPop] at h
            have hstack : s.stack = μ₀ :: μ₁ :: μ₃ :: μ₄ :: μ₅ :: μ₆ ::
                rest := stack_shape_of_pop6 hPop
            have hcg := hcg_delegatecall s
              (by rw [hstack] :
                s.stack = μ₀ :: μ₁ :: (μ₃ :: μ₄ :: μ₅ :: μ₆ :: rest))
            obtain ⟨rc, hCall, hk⟩ := except_bind_ok h
            obtain ⟨xc, stc⟩ := rc
            cases hk
            have hres0 :=
              (hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 xc stc hCall
                (by exact hcost) (by exact hcg)
            have hres : stc.gasAvailable.toNat + 100 ≤
                s.gasAvailable.toNat := hres0
            constructor
            · show stc.gasAvailable.toNat ≤ s.gasAvailable.toNat
              omega
            · intro _
              show stc.gasAvailable.toNat + 1 ≤ s.gasAvailable.toNat
              omega
    · -- STATICCALL
      constructor
      · intro hfuel h
        cases hPop : s.stack.pop6 with
        | none =>
            rw [evmStep_staticcall_none f _ arg s hPop] at h
            injection h with h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩ := r
            rw [evmStep_staticcall_some f _ arg s hPop] at h
            have hstack : s.stack = μ₀ :: μ₁ :: μ₃ :: μ₄ :: μ₅ :: μ₆ ::
                rest := stack_shape_of_pop6 hPop
            have hcg := hcg_staticcall s
              (by rw [hstack] :
                s.stack = μ₀ :: μ₁ :: (μ₃ :: μ₄ :: μ₅ :: μ₆ :: rest))
            have hCallErr := except_bind_error_of_total
              (fun b => ⟨_, rfl⟩) h
            refine (hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 ?_ hCallErr
            show EvmYul.EVM.Ccallgas (EvmYul.AccountAddress.ofUInt256 μ₁)
              (EvmYul.AccountAddress.ofUInt256 μ₁) ⟨0⟩ μ₀
              s.accountMap s.toMachineState s.substate + 9 ≤ f
            omega
      · intro s' h
        cases hPop : s.stack.pop6 with
        | none =>
            rw [evmStep_staticcall_none f _ arg s hPop] at h
            cases h
        | some r =>
            obtain ⟨rest, μ₀, μ₁, μ₃, μ₄, μ₅, μ₆⟩ := r
            rw [evmStep_staticcall_some f _ arg s hPop] at h
            have hstack : s.stack = μ₀ :: μ₁ :: μ₃ :: μ₄ :: μ₅ :: μ₆ ::
                rest := stack_shape_of_pop6 hPop
            have hcg := hcg_staticcall s
              (by rw [hstack] :
                s.stack = μ₀ :: μ₁ :: (μ₃ :: μ₄ :: μ₅ :: μ₆ :: rest))
            obtain ⟨rc, hCall, hk⟩ := except_bind_ok h
            obtain ⟨xc, stc⟩ := rc
            cases hk
            have hres0 :=
              (hcall _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 xc stc hCall
                (by exact hcost) (by exact hcg)
            have hres : stc.gasAvailable.toNat + 100 ≤
                s.gasAvailable.toNat := hres0
            constructor
            · show stc.gasAvailable.toNat ≤ s.gasAvailable.toNat
              omega
            · intro _
              show stc.gasAvailable.toNat + 1 ≤ s.gasAvailable.toNat
              omega

/-! ### The `X` layer -/

theorem eq_create_of_isCreate {w : EvmYul.Operation .EVM}
    (h : EvmYul.Operation.isCreate w = true) :
    w = .CREATE ∨ w = .CREATE2 := by
  unfold EvmYul.Operation.isCreate at h
  split at h
  · exact Or.inl rfl
  · exact Or.inr rfl
  · cases h

theorem not_wzero_of_haltOutput_none {s₃ : EvmYul.EVM.State}
    {w : EvmYul.Operation .EVM}
    (h : GasfulBridge.haltOutputAt s₃ w = none) : w ∉ Wzero := by
  intro hmem
  simp only [Wzero, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;>
    simp [GasfulBridge.haltOutputAt] at h

/-- The checked-precheck cascade: `EVM.X` at positive fuel either raises one
of the checked non-fuel exceptions, or every precheck passes. -/
theorem x_prechecks_cases (f : Nat) (vj : Array EvmYul.UInt256)
    (s : EvmYul.EVM.State) :
    (∃ err, err ≠ EvmYul.EVM.ExecutionException.OutOfFuel ∧
      EvmYul.EVM.X (f + 1) vj s = .error err) ∨
    (GasfulBridge.XSstoreStipendChecksPass vj s ∧
      ¬ (EvmYul.Operation.isCreate (GasfulBridge.decodedOperationAt s) =
          true ∧
        (EvmYul.UInt256.ofNat 49152) <
          s.stack[2]?.getD (EvmYul.UInt256.ofNat 0))) := by
  by_cases hMem :
      s.gasAvailable.toNat < GasfulBridge.memoryExpansionCostAt s
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_outOfGas_before_memory_charge hMem⟩
  by_cases hDyn :
      (GasfulBridge.afterMemoryChargeAt s).gasAvailable.toNat <
        GasfulBridge.dynamicGasCostAt s
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_outOfGas_before_dynamic_charge hMem hDyn⟩
  have hGasPass : GasfulBridge.XGasChecksPass s := ⟨hMem, hDyn⟩
  by_cases hInv :
      EvmYul.EVM.δ (GasfulBridge.decodedOperationAt s) = none
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_invalid_instruction_after_gas_checks hGasPass hInv⟩
  by_cases hLen :
      s.stack.length <
        (EvmYul.EVM.δ (GasfulBridge.decodedOperationAt s)).getD 0
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_stack_underflow_after_gas_opcode_check hGasPass hInv
        hLen⟩
  have hStackPass : GasfulBridge.XOpcodeStackChecksPass s :=
    ⟨hGasPass, hInv, hLen⟩
  by_cases hBJ : GasfulBridge.badJumpAt vj s
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_bad_jump_destination_after_stack_check hStackPass hBJ⟩
  by_cases hBJi : GasfulBridge.badJumpiAt vj s
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_bad_jumpi_destination_after_stack_check hStackPass
        hBJi⟩
  have hJumpPass : GasfulBridge.XJumpChecksPass vj s :=
    ⟨hStackPass, hBJ, hBJi⟩
  by_cases hRDC : GasfulBridge.invalidReturnDataCopyAt s
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_invalid_returndatacopy_after_jump_checks hJumpPass
        hRDC⟩
  have hMemPass : GasfulBridge.XMemoryAccessChecksPass vj s :=
    ⟨hJumpPass, hRDC⟩
  by_cases hOvf : GasfulBridge.stackOverflowAt s
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_stack_overflow_after_memory_access_checks hMemPass
        hOvf⟩
  have hLimitPass : GasfulBridge.XStackLimitChecksPass vj s :=
    ⟨hMemPass, hOvf⟩
  by_cases hStatic : GasfulBridge.staticModeViolationAt s
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_static_mode_violation_after_stack_limit_checks
        hLimitPass hStatic⟩
  have hStaticPass : GasfulBridge.XStaticChecksPass vj s :=
    ⟨hLimitPass, hStatic⟩
  by_cases hSstore : GasfulBridge.sstoreStipendOutOfGasAt s
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_sstore_stipend_outOfGas_after_static_check
        hStaticPass hSstore⟩
  have hPassAll : GasfulBridge.XSstoreStipendChecksPass vj s :=
    ⟨hStaticPass, hSstore⟩
  by_cases hBig :
      EvmYul.Operation.isCreate (GasfulBridge.decodedOperationAt s) =
          true ∧
        (EvmYul.UInt256.ofNat 49152) <
          s.stack[2]?.getD (EvmYul.UInt256.ofNat 0)
  · exact .inl ⟨_, (fun hh => by cases hh),
      GasfulBridge.x_create_initcode_outOfGas_after_sstore_check hPassAll
        (eq_create_of_isCreate hBig.1) hBig.2⟩
  · exact .inr ⟨hPassAll, hBig⟩

set_option maxHeartbeats 3200000 in
theorem xProps_succ (f : Nat) (hstep : StepFProps f) (hX : XProps f) :
    XProps (f + 1) := by
  intro vj s
  rcases x_prechecks_cases f vj s with ⟨err, hErrNe, hErrEq⟩ |
    ⟨hPass, hCreateOk⟩
  · refine ⟨fun hle h => ?_, fun s' o h => ?_, fun g o h => ?_⟩ <;>
      rw [hErrEq] at h
    · injection h with h
      exact hErrNe h
    · cases h
    · cases h
  · -- every precheck passes
    have hδ' : EvmYul.EVM.δ (GasfulBridge.decodedOperationAt s) ≠ none :=
      hPass.static.stackLimit.memoryAccess.jumps.stack.opcodeValid
    have hMem :
        ¬ s.gasAvailable.toNat < GasfulBridge.memoryExpansionCostAt s :=
      hPass.static.stackLimit.memoryAccess.jumps.stack.gas.memoryGas
    have hDyn :
        ¬ (GasfulBridge.afterMemoryChargeAt s).gasAvailable.toNat <
          GasfulBridge.dynamicGasCostAt s :=
      hPass.static.stackLimit.memoryAccess.jumps.stack.gas.dynamicGas
    have hs2eq : (GasfulBridge.afterMemoryChargeAt s).gasAvailable.toNat =
        s.gasAvailable.toNat - GasfulBridge.memoryExpansionCostAt s := by
      show (s.gasAvailable -
          EvmYul.UInt256.ofNat
            (GasfulBridge.memoryExpansionCostAt s)).toNat = _
      exact uint256_toNat_sub_ofNat_of_le (Nat.le_of_not_lt hMem)
    have hstepFacts :=
      hstep (GasfulBridge.decodedOperationAt s)
        ((EvmYul.EVM.decode s.executionEnv.code s.pc).getD
          (.STOP, none)).2
        (GasfulBridge.afterMemoryChargeAt s) hδ' (Nat.le_of_not_lt hDyn)
    have hXeq := GasfulBridge.x_after_prechecks_of_step_result
      (fuel := f) (validJumps := vj) (state := s) hPass hCreateOk rfl
    cases hres : EvmYul.EVM.step f (GasfulBridge.dynamicGasCostAt s)
        (some ((EvmYul.EVM.decode s.executionEnv.code s.pc).getD
          (.STOP, none)))
        (GasfulBridge.afterMemoryChargeAt s) with
    | error errS =>
        rw [hres] at hXeq
        simp only [GasfulBridge.xPostStepExceptResult] at hXeq
        refine ⟨fun hle h => ?_, fun s' o h => ?_, fun g o h => ?_⟩ <;>
          rw [hXeq] at h
        · injection h with h
          subst h
          exact hstepFacts.1 (by omega) hres
        · cases h
        · cases h
    | ok s₃ =>
        rw [hres] at hXeq
        simp only [GasfulBridge.xPostStepExceptResult] at hXeq
        have hgb := hstepFacts.2 s₃ hres
        cases hHalt : GasfulBridge.haltOutputAt s₃
            (GasfulBridge.decodedOperationAt s) with
        | none =>
            have hzero := not_wzero_of_haltOutput_none hHalt
            have hlt : s₃.gasAvailable.toNat + 1 ≤
                (GasfulBridge.afterMemoryChargeAt s).gasAvailable.toNat :=
              hgb.2 hzero
            have hXeq2 : EvmYul.EVM.X (f + 1) vj s =
                EvmYul.EVM.X f vj s₃ := by
              rw [hXeq]
              simp only [GasfulBridge.xPostStepResult, hHalt]
            obtain ⟨hXne, hXsucc, hXrev⟩ := hX vj s₃
            refine ⟨fun hle h => ?_, fun s' o h => ?_, fun g o h => ?_⟩ <;>
              rw [hXeq2] at h
            · exact hXne (by omega) h
            · have := hXsucc s' o h
              omega
            · have := hXrev g o h
              omega
        | some output =>
            have hle3 : s₃.gasAvailable.toNat ≤
                (GasfulBridge.afterMemoryChargeAt s).gasAvailable.toNat :=
              hgb.1
            have hXeq2 : EvmYul.EVM.X (f + 1) vj s =
                if GasfulBridge.decodedOperationAt s ==
                    EvmYul.Operation.REVERT then
                  Except.ok (.revert s₃.gasAvailable output)
                else
                  Except.ok (.success s₃ output) := by
              rw [hXeq]
              simp only [GasfulBridge.xPostStepResult, hHalt]
            by_cases hRev :
                (GasfulBridge.decodedOperationAt s ==
                  EvmYul.Operation.REVERT) = true
            · rw [if_pos hRev] at hXeq2
              refine ⟨fun hle h => ?_, fun s' o h => ?_,
                fun g o h => ?_⟩ <;> rw [hXeq2] at h
              · cases h
              · cases h
              · cases h
                omega
            · rw [if_neg hRev] at hXeq2
              refine ⟨fun hle h => ?_, fun s' o h => ?_,
                fun g o h => ?_⟩ <;> rw [hXeq2] at h
              · cases h
              · cases h
                omega
              · cases h

/-! ### The master induction and the gas-derived fuel bound -/

theorem master (n : Nat) :
    XProps n ∧ StepFProps n ∧ CallProps n ∧ ThetaProps n ∧ XiProps n ∧
      LambdaProps n := by
  induction n with
  | zero =>
      exact ⟨xProps_zero, stepFProps_zero, callProps_zero,
        thetaProps_zero, xiProps_zero, lambdaProps_zero⟩
  | succ f ih =>
      obtain ⟨hx, hstep, hcall, htheta, hxi, hlam⟩ := ih
      exact ⟨xProps_succ f hstep hx, stepFProps_succ f hcall hlam,
        callProps_succ f htheta, thetaProps_succ f hxi,
        xiProps_succ f hx, lambdaProps_succ f hxi⟩

end Master

/-- **Gas bounds structural fuel.** Running the charged frame interpreter
`EvmYul.EVM.X` at any structural fuel of at least `gasAvailable + 6` can
never report `OutOfFuel`: every continuing instruction charges at least one
unit of gas, CALL-family child frames enter with at least 100 less gas than
their parent, and CREATE-family child frames with at least 32000 less, so
the gas-derived fuel outlasts the whole recursion. -/
theorem x_ne_outOfFuel_of_gas_lt_fuel
    (fuel : Nat) (validJumps : Array EvmYul.UInt256)
    (s : EvmYul.EVM.State)
    (hfuel : s.gasAvailable.toNat + 6 ≤ fuel) :
    EvmYul.EVM.X fuel validJumps s ≠
      .error EvmYul.EVM.ExecutionException.OutOfFuel :=
  (((master fuel).1) validJumps s).1 hfuel

/-- The companion bounds for the other five functions of the charged
interpreter's mutual block. -/
theorem step_ne_outOfFuel_of_gas_lt_fuel
    (fuel : Nat) (w : EvmYul.Operation .EVM)
    (arg : Option (EvmYul.UInt256 × Nat)) (s : EvmYul.EVM.State)
    (hδ : EvmYul.EVM.δ w ≠ none)
    (hcost : EvmYul.EVM.C' s w ≤ s.gasAvailable.toNat)
    (hfuel : s.gasAvailable.toNat + 5 ≤ fuel) :
    EvmYul.EVM.step fuel (EvmYul.EVM.C' s w) (some (w, arg)) s ≠
      .error EvmYul.EVM.ExecutionException.OutOfFuel :=
  ((master fuel).2.1 w arg s hδ hcost).1 hfuel

theorem theta_ne_outOfFuel_of_gas_lt_fuel
    (fuel : Nat) (bvh : List ByteArray)
    (cA : Batteries.RBSet EvmYul.AccountAddress compare)
    (gbh : EvmYul.BlockHeader) (blocks : EvmYul.ProcessedBlocks)
    (σ σ₀ : EvmYul.AccountMap .EVM)
    (cctx : EvmYul.EVM.ChildFrameChainContext) (A : EvmYul.Substate)
    (sA oA rA : EvmYul.AccountAddress) (c : EvmYul.ToExecute .EVM)
    (g p v v' : EvmYul.UInt256) (d : ByteArray) (e : Nat)
    (H : EvmYul.BlockHeader) (wperm : Bool)
    (hfuel : g.toNat + 8 ≤ fuel) :
    EvmYul.EVM.Θ fuel bvh cA gbh blocks σ σ₀ cctx A sA oA rA c g p v v'
      d e H wperm ≠ .error EvmYul.EVM.ExecutionException.OutOfFuel :=
  ((master fuel).2.2.2.1 bvh cA gbh blocks σ σ₀ cctx A sA oA rA c g p v
    v' d e H wperm).1 hfuel

theorem xi_ne_outOfFuel_of_gas_lt_fuel
    (fuel : Nat)
    (cA : Batteries.RBSet EvmYul.AccountAddress compare)
    (gbh : EvmYul.BlockHeader) (blocks : EvmYul.ProcessedBlocks)
    (σ σ₀ : EvmYul.AccountMap .EVM)
    (cctx : EvmYul.EVM.ChildFrameChainContext)
    (g : EvmYul.UInt256) (A : EvmYul.Substate)
    (I : EvmYul.ExecutionEnv .EVM)
    (hfuel : g.toNat + 7 ≤ fuel) :
    EvmYul.EVM.Ξ fuel cA gbh blocks σ σ₀ cctx g A I ≠
      .error EvmYul.EVM.ExecutionException.OutOfFuel :=
  ((master fuel).2.2.2.2.1 cA gbh blocks σ σ₀ cctx g A I).1 hfuel

/-! ## Fuel monotonicity of decided open runs

An open raw-bytecode run that has decided (halted or raised an error) at
fuel `B` decides identically, over the same transcript, at any fuel
`N ≥ B`. Only still-`running` results are fuel-sensitive. -/

section RunnerFuelMono

theorem executes_openRunNResult_of_le
    {bytes : ByteArray} {B N : Nat} {s : EVMState}
    {t : Simulation.Interaction.Transcript}
    {d : Except EVMException StepResult}
    (hBN : B ≤ N)
    (hDecided : ∀ st, d ≠ .ok (.running st))
    (hExec : Simulation.Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes B s) t d) :
    Simulation.Interaction.Executes
      (Compact.InteractionSemantics.openRunNResult bytes N s) t d := by
  induction B generalizing N s t d with
  | zero =>
      have hzero :
          Compact.InteractionSemantics.openRunNResult bytes 0 s =
            .done (.ok (.running s)) := rfl
      rw [hzero] at hExec
      cases hExec
      exact absurd rfl (hDecided s)
  | succ b ih =>
      cases N with
      | zero => omega
      | succ n =>
          have hEq :
              Compact.InteractionSemantics.openRunNResult bytes (b + 1)
                  s =
                Simulation.Interaction.bind
                  (Compact.InteractionSemantics.openStepResult bytes s)
                  (fun result =>
                    match result with
                    | .running state' =>
                        Compact.InteractionSemantics.openRunNResult bytes
                          b state'
                    | .halted halt => .done (.ok (.halted halt))) := rfl
          have hEqN :
              Compact.InteractionSemantics.openRunNResult bytes (n + 1)
                  s =
                Simulation.Interaction.bind
                  (Compact.InteractionSemantics.openStepResult bytes s)
                  (fun result =>
                    match result with
                    | .running state' =>
                        Compact.InteractionSemantics.openRunNResult bytes
                          n state'
                    | .halted halt => .done (.ok (.halted halt))) := rfl
          rw [hEq] at hExec
          rw [hEqN]
          rcases Simulation.Interaction.Executes.bind_cases hExec with
            ⟨err, hd, hFirst⟩ |
            ⟨value, t1, t2, hT, hFirst, hRest⟩
          · subst hd
            exact Simulation.Interaction.Executes.bind_error hFirst
          · subst hT
            cases value with
            | running s' =>
                exact Simulation.Interaction.Executes.bind_ok hFirst
                  (ih (by omega) hDecided hRest)
            | halted halt =>
                cases hRest
                exact Simulation.Interaction.Executes.bind_ok hFirst
                  (.done _)

end RunnerFuelMono

end GasfulFuelBound
end Assembly
end EvmCompiler
