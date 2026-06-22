import EvmCompiler.Assembly.Assembler
import EvmYul.EVM.State

namespace EvmCompiler
namespace Assembly

namespace PrimOp

/--
Primitive operations whose non-gas behavior is supplied by the shared
EVM/Yul semantics imported from EVMYulLean.

The first assembly source semantics deliberately has no continuing `GAS`
primitive or exact gas accounting, and raw EVM jumps are represented by labeled
control-flow instructions. Account/code reads, logs, storage, memory, and terminal
`SELFDESTRUCT` reuse shared EVMYulLean state transformers in the gasless source
step relation.  `CALL`/`CREATE` are admitted at the syntax/encoding level; the
deployed open-world request/response behavior is handled by the higher Yul
open-boundary theorem, not by an extra assembly-layer oracle.
-/
def accepted (_op : PrimOp) : Bool :=
  true

/--
Operations whose result can depend on context outside the current stack/control
state. This classifier is documentation only.  It includes the call/create
family because those opcodes have an additional gas-aware runner bridge
obligation beyond the ordinary gasless source step relation.
-/
def usesOutsideContext : PrimOp → Bool
  | .address | .balance | .origin | .caller | .callvalue | .calldataload
  | .calldatasize | .calldatacopy | .codesize | .codecopy | .gasprice
  | .extcodesize | .extcodecopy | .returndatasize | .returndatacopy
  | .extcodehash
  | .blockhash | .coinbase | .timestamp | .number | .prevrandao | .gaslimit
  | .chainid | .selfbalance | .basefee | .blobhash | .blobbasefee
  | .sload | .sstore | .tload | .tstore | .gas | .log0 | .log1 | .log2 | .log3
  | .log4 | .create | .call | .callcode | .return | .delegatecall | .create2
  | .staticcall | .revert | .selfdestruct =>
      true
  | _ =>
      false

end PrimOp

namespace Instr

def accepted : Instr → Bool
  | .prim op => op.accepted
  | .label _ | .push _ | .pushLabel _ | .jump _ | .jumpi _ => true
  | .jumpDynamic => false

end Instr

namespace Program

def labelsRev : Program → List Label → List Label
  | [], acc => acc
  | .label name :: rest, acc => labelsRev rest (name :: acc)
  | _ :: rest, acc => labelsRev rest acc

def labelsFast (program : Program) : List Label :=
  (labelsRev program []).reverse

@[implemented_by labelsFast]
def labels : Program → List Label
  | [] => []
  | .label name :: rest => name :: labels rest
  | _ :: rest => labels rest

theorem labelsRev_eq (program : Program) (acc : List Label) :
    labelsRev program acc = program.labels.reverse ++ acc := by
  induction program generalizing acc with
  | nil => simp [labelsRev, labels]
  | cons instr rest ih =>
      cases instr <;>
        simp [labelsRev, labels, ih, List.reverse_cons,
          List.append_assoc]

theorem labelsFast_eq_labels (program : Program) :
    labelsFast program = program.labels := by
  simp [labelsFast, labelsRev_eq]

theorem labels_append (left right : Program) :
    labels (left ++ right) = labels left ++ labels right := by
  induction left with
  | nil =>
      simp [labels]
  | cons instr rest ih =>
      cases instr <;> simp [labels, ih]

def noDuplicates {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && noDuplicates xs

theorem noDuplicates_eq_true_iff_nodup
    {α : Type} [BEq α] [LawfulBEq α] (values : List α) :
    noDuplicates values = true ↔ values.Nodup := by
  induction values with
  | nil =>
      simp [noDuplicates]
  | cons value rest ih =>
      simp [noDuplicates, ih, List.contains_iff_mem]

def labelsUnique (program : Program) : Bool :=
  LabelList.unique? program.labels

def instructionsAccepted (program : Program) : Bool :=
  program.all Instr.accepted

theorem instr_ne_jumpDynamic_of_instructionsAccepted
    {program : Program} {instr : Instr}
    (hAccepted : instructionsAccepted program = true)
    (hMem : instr ∈ program) : instr ≠ .jumpDynamic := by
  have hInstr := (List.all_eq_true.mp hAccepted) instr hMem
  intro hEq
  subst instr
  simp [Instr.accepted] at hInstr

/--
The independent accepted-input checker for the labeled assembly IR.

This checker is intentionally separate from assembler success.  It rejects
duplicate labels, verifies that every jump target resolves, and keeps the
primitive-operation boundary centralized.
-/
def accepted (program : Program) : Bool :=
  instructionsAccepted program && labelsUnique program && allTargetsResolve program

theorem labels_nodup_of_accepted {program : Program}
    (hAccepted : program.accepted = true) :
    program.labels.Nodup := by
  have hUnique : program.labelsUnique = true := by
    simp only [accepted, Bool.and_eq_true] at hAccepted
    exact hAccepted.1.2
  exact (LabelList.unique?_eq_true_iff program.labels).mp hUnique

theorem target_resolves_of_accepted {program : Program}
    {instr : Instr} {target : Label}
    (hAccepted : program.accepted = true)
    (hInstr : instr ∈ program)
    (hTarget : target ∈ instr.targets) :
    ∃ pc, program.labelPc target = some pc := by
  have hAllTargets : program.allTargetsResolve = true := by
    simp only [accepted, Bool.and_eq_true] at hAccepted
    exact hAccepted.2
  have hInstrTargets :
      instr.targets.all
        (fun label => (program.labelPc label).isSome) = true :=
    (List.all_eq_true.mp hAllTargets) instr hInstr
  have hSome : (program.labelPc target).isSome = true :=
    (List.all_eq_true.mp hInstrTargets) target hTarget
  cases hPc : program.labelPc target with
  | none =>
      simp [hPc] at hSome
  | some pc =>
      exact ⟨pc, rfl⟩

theorem labelPcFrom_none_of_not_mem_labels
    (program : Program) (base : Nat) {target : Label}
    (hNotMem : target ∉ labels program) :
    labelPcFrom program base target = none := by
  induction program generalizing base with
  | nil =>
      rfl
  | cons instr rest ih =>
      cases instr with
      | label name =>
          simp [labels] at hNotMem
          have hNameNe : name ≠ target := by
            intro hEq
            exact hNotMem.left hEq.symm
          unfold labelPcFrom
          simp [hNameNe, ih (base + Instr.byteSize (.label name)) hNotMem.right]
      | prim op =>
          unfold labelPcFrom
          exact ih (base + Instr.byteSize (.prim op)) hNotMem
      | push value =>
          unfold labelPcFrom
          exact ih (base + Instr.byteSize (.push value)) hNotMem
      | pushLabel label =>
          unfold labelPcFrom
          exact ih (base + Instr.byteSize (.pushLabel label)) hNotMem
      | jump target' =>
          unfold labelPcFrom
          exact ih (base + Instr.byteSize (.jump target')) hNotMem
      | jumpi target' =>
          unfold labelPcFrom
          exact ih (base + Instr.byteSize (.jumpi target')) hNotMem
      | jumpDynamic =>
          unfold labelPcFrom
          exact ih (base + Instr.byteSize .jumpDynamic) hNotMem

theorem labelPc_none_of_not_mem_labels
    (program : Program) {target : Label}
    (hNotMem : target ∉ labels program) :
    labelPc program target = none := by
  exact labelPcFrom_none_of_not_mem_labels program 0 hNotMem

theorem mem_labels_of_label_mem
    {program : Program} {target : Label}
    (hMem : Instr.label target ∈ program) :
    target ∈ labels program := by
  induction program with
  | nil =>
      simp at hMem
  | cons instr rest ih =>
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl hEq =>
          subst instr
          simp [labels]
      | inr hRest =>
          cases instr <;> simp [labels, ih hRest]

theorem labelPcFrom_exists_of_mem_labels
    (program : Program) (base : Nat) {target : Label}
    (hMem : target ∈ labels program) :
    ∃ pc, labelPcFrom program base target = some pc := by
  induction program generalizing base with
  | nil =>
      simp [labels] at hMem
  | cons instr rest ih =>
      cases instr with
      | label name =>
          simp only [labels, List.mem_cons] at hMem
          by_cases hName : name = target
          · subst name
            exact ⟨base, by simp [labelPcFrom]⟩
          · have hRest : target ∈ labels rest := by
              exact hMem.resolve_left (Ne.symm hName)
            simpa [labelPcFrom, hName] using
              ih (base + Instr.byteSize (.label name)) hRest
      | prim op =>
          exact ih (base + Instr.byteSize (.prim op)) hMem
      | push value =>
          exact ih (base + Instr.byteSize (.push value)) hMem
      | pushLabel label =>
          exact ih (base + Instr.byteSize (.pushLabel label)) hMem
      | jump jumpTarget =>
          exact ih (base + Instr.byteSize (.jump jumpTarget)) hMem
      | jumpi jumpTarget =>
          exact ih (base + Instr.byteSize (.jumpi jumpTarget)) hMem
      | jumpDynamic =>
          exact ih (base + Instr.byteSize .jumpDynamic) hMem

theorem labelPc_exists_of_mem_labels
    (program : Program) {target : Label}
    (hMem : target ∈ labels program) :
    ∃ pc, labelPc program target = some pc := by
  simpa [labelPc] using
    labelPcFrom_exists_of_mem_labels program 0 hMem

theorem labelPcFrom_append_label_eq
    (pre suffix : Program) (base : Nat) {target : Label}
    (hNotMem : target ∉ labels pre) :
    labelPcFrom (pre ++ .label target :: suffix) base target =
      some (base + byteLength pre) := by
  induction pre generalizing base with
  | nil =>
      simp [labelPcFrom]
  | cons instr rest ih =>
      cases instr with
      | label name =>
          simp [labels] at hNotMem
          have hNameNe : name ≠ target := by
            intro hEq
            exact hNotMem.left hEq.symm
          unfold labelPcFrom
          simp [hNameNe]
          rw [ih (base := base + Instr.byteSize (.label name)) hNotMem.right]
          simp [Nat.add_assoc]
      | prim op =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize (.prim op)) target =
              some (base + byteLength (.prim op :: rest))
          rw [ih (base := base + Instr.byteSize (.prim op)) hNotMem]
          simp [byteLength_cons, Nat.add_assoc]
      | push value =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize (.push value)) target =
              some (base + byteLength (.push value :: rest))
          rw [ih (base := base + Instr.byteSize (.push value)) hNotMem]
          simp [byteLength_cons, Nat.add_assoc]
      | pushLabel label =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize (.pushLabel label)) target =
              some (base + byteLength (.pushLabel label :: rest))
          rw [ih (base := base + Instr.byteSize (.pushLabel label)) hNotMem]
          simp [byteLength_cons, Nat.add_assoc]
      | jump target' =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize (.jump target')) target =
              some (base + byteLength (.jump target' :: rest))
          rw [ih (base := base + Instr.byteSize (.jump target')) hNotMem]
          simp [byteLength_cons, Nat.add_assoc]
      | jumpi target' =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize (.jumpi target')) target =
              some (base + byteLength (.jumpi target' :: rest))
          rw [ih (base := base + Instr.byteSize (.jumpi target')) hNotMem]
          simp [byteLength_cons, Nat.add_assoc]
      | jumpDynamic =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize .jumpDynamic) target =
              some (base + byteLength (.jumpDynamic :: rest))
          rw [ih (base := base + Instr.byteSize .jumpDynamic) hNotMem]
          simp [byteLength_cons, Nat.add_assoc]

theorem labelPc_append_label_eq
    (pre suffix : Program) {target : Label}
    (hNotMem : target ∉ labels pre) :
    labelPc (pre ++ .label target :: suffix) target =
      some (byteLength pre) := by
  simpa [labelPc] using
    labelPcFrom_append_label_eq pre suffix 0 hNotMem

theorem labelPc_append_label_eq_of_labels_nodup
    (pre suffix : Program) {target : Label}
    (hNodup : (labels (pre ++ .label target :: suffix)).Nodup) :
    labelPc (pre ++ .label target :: suffix) target =
      some pre.byteLength := by
  have hLabels :
      labels (pre ++ .label target :: suffix) =
        labels pre ++ target :: labels suffix := by
    simp [labels_append, labels]
  have hNodupLocal :
      (labels pre ++ target :: labels suffix).Nodup := by
    simpa [hLabels] using hNodup
  have hNotMem : target ∉ labels pre := by
    rw [List.nodup_append] at hNodupLocal
    intro hMem
    exact hNodupLocal.2.2 target hMem target (by simp) rfl
  exact labelPc_append_label_eq pre suffix hNotMem

end Program

/--
Named boundary for the AST-level verified compiler path.

Future source languages should target `Program` values and prove they satisfy
this predicate independently of the assembler returning `some`.
-/
structure Accepted (program : Program) : Prop where
  checked : Program.accepted program = true

/--
The trusted Lean compiler entry point for this layer: accepted labeled assembly
AST to resolved EVM assembly.
-/
def compile? (program : Program) : Option TargetProgram :=
  if Program.accepted program then
    assemble? program
  else
    none

def compileExecutable? (program : Program) : Option TargetProgram :=
  if Program.accepted program then
    assembleExecutable? program
  else
    none

theorem compileExecutable?_eq_compile? (program : Program) :
    compileExecutable? program = compile? program := by
  simp [compileExecutable?, compile?, assembleExecutable?_eq_assemble? program]

/--
Out-of-gas policy boundary for the full EVM runner.

The checked gasless theorem proves preservation for successful source runs.
When related to gas-aware EVM execution, out-of-gas is an additional behavior:
it can interrupt the deployed bytecode before the gasless run finishes unless a
sufficient-gas premise is provided by a later theorem.
-/
structure OutOfGasPolicyAssumption
    (_program : Program) (_initial : EvmYul.EVM.State) : Prop where
  outOfGasMayInterruptFullEVMExecution : True

/--
Projection boundary for observations of full EVM state.

The current theorem compares EVM states after erasing gas accounting fields.
External-facing state remains part of the compared EVM state; it is not
projected away by this assembly layer.
-/
structure CurrentContractProjectionAssumption
    (_program : Program) (_initial : EvmYul.EVM.State) : Prop where
  compareOnlyGasErasedExecutionState : True

namespace OutOfGasPolicyAssumption

def trivial {program : Program} {initial : EvmYul.EVM.State} :
    OutOfGasPolicyAssumption program initial where
  outOfGasMayInterruptFullEVMExecution := True.intro

end OutOfGasPolicyAssumption

namespace CurrentContractProjectionAssumption

def trivial {program : Program} {initial : EvmYul.EVM.State} :
    CurrentContractProjectionAssumption program initial where
  compareOnlyGasErasedExecutionState := True.intro

end CurrentContractProjectionAssumption

/--
The extra assumptions needed when moving from the gasless AST theorem to a
gas-aware EVM execution theorem.

No field is a new trusted constant: each later theorem must either require this
structure as a hypothesis or prove the relevant field for a concrete execution.
Keeping the fields here makes the trust boundary for gas and out-of-gas
behavior visible to later compiler layers.
-/
structure EVMExecutionAssumptions (program : Program) (initial : EvmYul.EVM.State) : Prop where
  accepted : Accepted program
  outOfGasPolicy : OutOfGasPolicyAssumption program initial
  currentContractProjection : CurrentContractProjectionAssumption program initial

namespace EVMExecutionAssumptions

def noExtraAssumptions {program : Program} {initial : EvmYul.EVM.State}
    (accepted : Accepted program) : EVMExecutionAssumptions program initial where
  accepted := accepted
  outOfGasPolicy := OutOfGasPolicyAssumption.trivial
  currentContractProjection := CurrentContractProjectionAssumption.trivial

end EVMExecutionAssumptions

end Assembly
end EvmCompiler
