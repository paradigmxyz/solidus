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
  | .label _ | .push _ | .jump _ | .jumpi _ => true

end Instr

namespace Program

def labels : Program → List Label
  | [] => []
  | .label name :: rest => name :: labels rest
  | _ :: rest => labels rest

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

def labelsUnique (program : Program) : Bool :=
  noDuplicates program.labels

def instructionsAccepted (program : Program) : Bool :=
  program.all Instr.accepted

/--
The independent accepted-input checker for the labeled assembly IR.

This checker is intentionally separate from assembler success.  It rejects
duplicate labels, verifies that every jump target resolves, and keeps the
primitive-operation boundary centralized.
-/
def accepted (program : Program) : Bool :=
  instructionsAccepted program && labelsUnique program && allTargetsResolve program

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
      | jump target' =>
          unfold labelPcFrom
          exact ih (base + Instr.byteSize (.jump target')) hNotMem
      | jumpi target' =>
          unfold labelPcFrom
          exact ih (base + Instr.byteSize (.jumpi target')) hNotMem

theorem labelPc_none_of_not_mem_labels
    (program : Program) {target : Label}
    (hNotMem : target ∉ labels program) :
    labelPc program target = none := by
  exact labelPcFrom_none_of_not_mem_labels program 0 hNotMem

theorem labelPcFrom_append_label_eq
    (pre suffix : Program) (base : Nat) {target : Label}
    (hNotMem : target ∉ labels pre) :
    labelPcFrom (pre ++ .label target :: suffix) base target =
      some (base + byteLength pre) := by
  induction pre generalizing base with
  | nil =>
      simp [labelPcFrom, byteLength]
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
          simp [byteLength, Nat.add_assoc]
      | push value =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize (.push value)) target =
              some (base + byteLength (.push value :: rest))
          rw [ih (base := base + Instr.byteSize (.push value)) hNotMem]
          simp [byteLength, Nat.add_assoc]
      | jump target' =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize (.jump target')) target =
              some (base + byteLength (.jump target' :: rest))
          rw [ih (base := base + Instr.byteSize (.jump target')) hNotMem]
          simp [byteLength, Nat.add_assoc]
      | jumpi target' =>
          unfold labelPcFrom
          change
            labelPcFrom (rest ++ Instr.label target :: suffix)
              (base + Instr.byteSize (.jumpi target')) target =
              some (base + byteLength (.jumpi target' :: rest))
          rw [ih (base := base + Instr.byteSize (.jumpi target')) hNotMem]
          simp [byteLength, Nat.add_assoc]

theorem labelPc_append_label_eq
    (pre suffix : Program) {target : Label}
    (hNotMem : target ∉ labels pre) :
    labelPc (pre ++ .label target :: suffix) target =
      some (byteLength pre) := by
  simpa [labelPc] using
    labelPcFrom_append_label_eq pre suffix 0 hNotMem

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
