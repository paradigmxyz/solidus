import EvmCompiler.Assembly.Syntax
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

namespace EvmCompiler
namespace Assembly

inductive TargetInstr where
  | push32 (value : Word)
  | jump
  | jumpi
  | jumpdest
  | prim (op : PrimOp)
  deriving DecidableEq, Repr

structure LocatedTarget where
  pc : Nat
  instr : TargetInstr
  deriving DecidableEq, Repr

structure TargetProgram where
  code : List LocatedTarget
  deriving DecidableEq, Repr

namespace TargetInstr

def op : TargetInstr → EVMOp
  | .push32 _ => EvmYul.Operation.PUSH32
  | .jump => EvmYul.Operation.JUMP
  | .jumpi => EvmYul.Operation.JUMPI
  | .jumpdest => EvmYul.Operation.JUMPDEST
  | .prim op => op.toEVM

def arg : TargetInstr → Option (Word × Nat)
  | .push32 value => some (value, 32)
  | .jump | .jumpi | .jumpdest | .prim _ => none

/-- Decode the exact instruction forms emitted by the verified assembler. -/
def ofDecoded? (op : EVMOp) (arg : Option (Word × Nat)) :
    Option TargetInstr :=
  match op, arg with
  | .PUSH32, some (value, 32) => some (.push32 value)
  | .JUMP, none => some .jump
  | .JUMPI, none => some .jumpi
  | .JUMPDEST, none => some .jumpdest
  | op, none => (PrimOp.ofEVM? op).map .prim
  | _, _ => none

@[simp] theorem ofDecoded?_op_arg (instr : TargetInstr) :
    ofDecoded? instr.op instr.arg = some instr := by
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
      cases op <;> rfl

@[simp] theorem ofDecoded?_call :
    ofDecoded? EvmYul.Operation.CALL none = some (.prim .call) := rfl

@[simp] theorem ofDecoded?_callcode :
    ofDecoded? EvmYul.Operation.CALLCODE none =
      some (.prim .callcode) := rfl

@[simp] theorem ofDecoded?_delegatecall :
    ofDecoded? EvmYul.Operation.DELEGATECALL none =
      some (.prim .delegatecall) := rfl

@[simp] theorem ofDecoded?_staticcall :
    ofDecoded? EvmYul.Operation.STATICCALL none =
      some (.prim .staticcall) := rfl

@[simp] theorem ofDecoded?_create :
    ofDecoded? EvmYul.Operation.CREATE none = some (.prim .create) := rfl

@[simp] theorem ofDecoded?_create2 :
    ofDecoded? EvmYul.Operation.CREATE2 none = some (.prim .create2) := rfl

end TargetInstr

namespace LabelList

def uniqueFrom? (seen : Std.HashSet Label) : List Label → Bool
  | [] => true
  | label :: rest =>
      if seen.contains label then false
      else uniqueFrom? (seen.insert label) rest

def unique? (labels : List Label) : Bool :=
  uniqueFrom? {} labels

theorem uniqueFrom?_eq_true_iff
    (seen : Std.HashSet Label) (labels : List Label) :
    uniqueFrom? seen labels = true ↔
      labels.Nodup ∧ ∀ label ∈ labels, label ∉ seen := by
  induction labels generalizing seen with
  | nil => simp [uniqueFrom?]
  | cons label rest ih =>
      by_cases hMem : label ∈ seen
      · have hContains : seen.contains label = true :=
          Std.HashSet.mem_iff_contains.mp hMem
        simp [uniqueFrom?, hContains, hMem]
      · have hContains : seen.contains label = false :=
          Std.HashSet.contains_eq_false_iff_not_mem.mpr hMem
        rw [uniqueFrom?, if_neg (by simpa using hContains), ih]
        simp only [List.nodup_cons, List.mem_cons, forall_eq_or_imp,
          Std.HashSet.mem_insert]
        constructor
        · rintro ⟨hRestNodup, hFresh⟩
          refine ⟨⟨?_, hRestNodup⟩, hMem, ?_⟩
          · intro hLabelRest
            exact (hFresh label hLabelRest) (Or.inl (by simp))
          intro candidate hCandidate
          have hNotInserted := hFresh candidate hCandidate
          intro hCandidateMem
          exact hNotInserted (Or.inr hCandidateMem)
        · rintro ⟨⟨hNotRest, hRestNodup⟩, _hHeadFresh, hRestFresh⟩
          refine ⟨hRestNodup, ?_⟩
          intro candidate hCandidate
          intro hInserted
          rcases hInserted with hEq | hSeen
          · apply hNotRest
            have hLabelEq : label = candidate := by simpa using hEq
            simpa [hLabelEq] using hCandidate
          · exact hRestFresh candidate hCandidate hSeen

@[simp] theorem unique?_eq_true_iff (labels : List Label) :
    unique? labels = true ↔ labels.Nodup := by
  rw [unique?, uniqueFrom?_eq_true_iff]
  simp

end LabelList

namespace Program

def labelPcFrom : Program → Nat → Label → Option Nat
  | [], _, _ => none
  | instr :: rest, pc, target =>
      match instr with
      | .label name =>
          if name = target then
            some pc
          else
            labelPcFrom rest (pc + instr.byteSize) target
      | _ =>
          labelPcFrom rest (pc + instr.byteSize) target

def labelPc (program : Program) (target : Label) : Option Nat :=
  labelPcFrom program 0 target

abbrev LabelTable := List (Label × Nat)

def labelTableFromRev : Program → Nat → LabelTable → LabelTable
  | [], _pc, acc => acc
  | instr :: rest, pc, acc =>
      match instr with
      | .label name =>
          labelTableFromRev rest (pc + instr.byteSize) ((name, pc) :: acc)
      | _ => labelTableFromRev rest (pc + instr.byteSize) acc

def labelTableFromFast (program : Program) (pc : Nat) : LabelTable :=
  (labelTableFromRev program pc []).reverse

@[implemented_by labelTableFromFast]
def labelTableFrom : Program → Nat → LabelTable
  | [], _ => []
  | instr :: rest, pc =>
      match instr with
      | .label name =>
          (name, pc) :: labelTableFrom rest (pc + instr.byteSize)
      | _ => labelTableFrom rest (pc + instr.byteSize)

def labelTable (program : Program) : LabelTable :=
  labelTableFrom program 0

def lookupLabel? (table : LabelTable) (target : Label) : Option Nat :=
  (table.find? fun entry => entry.1 == target).map Prod.snd

abbrev LabelIndex := Std.HashMap Label Nat

def buildLabelIndexFrom : Program → Nat → LabelIndex → LabelIndex
  | [], _pc, index => index
  | instr :: rest, pc, index =>
      let index :=
        match instr with
        | .label name => index.insertIfNew name pc
        | _ => index
      buildLabelIndexFrom rest (pc + instr.byteSize) index

def buildLabelIndex (program : Program) : LabelIndex :=
  buildLabelIndexFrom program 0 {}

theorem buildLabelIndexFrom_get?
    (program : Program) (pc : Nat) (index : LabelIndex) (target : Label) :
    (buildLabelIndexFrom program pc index).get? target =
      match index.get? target with
      | some existing => some existing
      | none => labelPcFrom program pc target := by
  induction program generalizing pc index with
  | nil =>
      cases hExisting : index.get? target <;>
        simp only [buildLabelIndexFrom, labelPcFrom, hExisting]
  | cons instr rest ih =>
      cases instr with
      | label name =>
          rw [buildLabelIndexFrom, ih]
          by_cases hName : name = target
          · subst name
            cases hExisting : index.get? target with
            | none =>
                have hExisting' : index[target]? = none := by
                  simpa only [Std.HashMap.get?_eq_getElem?] using hExisting
                have hNotMem : target ∉ index := by
                  intro hMem
                  have hSome :=
                    (Std.HashMap.mem_iff_isSome_getElem?).mp hMem
                  rw [hExisting'] at hSome
                  simp at hSome
                simp only [Std.HashMap.get?_eq_getElem?,
                  Std.HashMap.getElem?_insertIfNew]
                simp [hExisting', hNotMem, labelPcFrom]
            | some existing =>
                have hExisting' : index[target]? = some existing := by
                  simpa only [Std.HashMap.get?_eq_getElem?] using hExisting
                obtain ⟨hMem, _hGet⟩ :=
                  Std.HashMap.getElem?_eq_some_iff.mp hExisting'
                simp only [Std.HashMap.get?_eq_getElem?,
                  Std.HashMap.getElem?_insertIfNew]
                simp only [beq_self_eq_true, true_and, hMem,
                  not_true_eq_false, if_false, hExisting']
          · have hBeq : (name == target) = false := by
              simpa using hName
            simp only [Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insertIfNew]
            simp [hBeq, hName, labelPcFrom]
      | prim op | push op | jump op | jumpi op =>
          simpa [buildLabelIndexFrom, labelPcFrom] using
            ih (pc := pc + Instr.byteSize _) (index := index)

theorem buildLabelIndex_get? (program : Program) (target : Label) :
    program.buildLabelIndex.get? target = program.labelPc target := by
  simpa [buildLabelIndex, labelPc] using
    buildLabelIndexFrom_get? program 0 ({} : LabelIndex) target

theorem labelTableFromRev_eq
    (program : Program) (pc : Nat) (acc : LabelTable) :
    labelTableFromRev program pc acc =
      (labelTableFrom program pc).reverse ++ acc := by
  induction program generalizing pc acc with
  | nil => simp [labelTableFromRev, labelTableFrom]
  | cons instr rest ih =>
      cases instr <;>
        simp [labelTableFromRev, labelTableFrom, ih,
          List.reverse_cons, List.append_assoc]

theorem labelTableFromFast_eq
    (program : Program) (pc : Nat) :
    labelTableFromFast program pc = labelTableFrom program pc := by
  simp [labelTableFromFast, labelTableFromRev_eq]

theorem lookupLabel?_labelTableFrom_eq_labelPcFrom
    (program : Program) (pc : Nat) (target : Label) :
    lookupLabel? (labelTableFrom program pc) target =
      labelPcFrom program pc target := by
  induction program generalizing pc with
  | nil => simp [labelTableFrom, lookupLabel?, labelPcFrom]
  | cons instr rest ih =>
      cases instr with
      | label name =>
          by_cases hName : name = target
          · subst name
            simp [labelTableFrom, lookupLabel?, labelPcFrom]
          · simp [labelTableFrom, lookupLabel?, labelPcFrom, hName]
            change
              lookupLabel?
                  (labelTableFrom rest
                    (pc + Instr.byteSize (.label name))) target =
                labelPcFrom rest
                  (pc + Instr.byteSize (.label name)) target
            exact ih (pc := pc + Instr.byteSize (.label name))
      | prim op =>
          change
            lookupLabel?
                (labelTableFrom rest (pc + Instr.byteSize (.prim op))) target =
              labelPcFrom rest (pc + Instr.byteSize (.prim op)) target
          exact ih (pc := pc + Instr.byteSize (.prim op))
      | push value =>
          change
            lookupLabel?
                (labelTableFrom rest (pc + Instr.byteSize (.push value))) target =
              labelPcFrom rest (pc + Instr.byteSize (.push value)) target
          exact ih (pc := pc + Instr.byteSize (.push value))
      | jump jumpTarget =>
          change
            lookupLabel?
                (labelTableFrom rest
                  (pc + Instr.byteSize (.jump jumpTarget))) target =
              labelPcFrom rest
                (pc + Instr.byteSize (.jump jumpTarget)) target
          exact ih (pc := pc + Instr.byteSize (.jump jumpTarget))
      | jumpi jumpTarget =>
          change
            lookupLabel?
                (labelTableFrom rest
                  (pc + Instr.byteSize (.jumpi jumpTarget))) target =
              labelPcFrom rest
                (pc + Instr.byteSize (.jumpi jumpTarget)) target
          exact ih (pc := pc + Instr.byteSize (.jumpi jumpTarget))

theorem lookupLabel?_labelTable_eq_labelPc
    (program : Program) (target : Label) :
    lookupLabel? program.labelTable target = program.labelPc target := by
  exact lookupLabel?_labelTableFrom_eq_labelPcFrom program 0 target

def instrAtPcFrom : Program → Nat → Nat → Option (Nat × Instr)
  | [], _, _ => none
  | instr :: rest, pc, query =>
      if query = pc then
        some (pc, instr)
      else
        instrAtPcFrom rest (pc + instr.byteSize) query

def instrAtPc (program : Program) (pc : Nat) : Option (Nat × Instr) :=
  instrAtPcFrom program 0 pc

theorem instrAtPcFrom_at_head (instr : Instr) (rest : Program) (base : Nat) :
    instrAtPcFrom (instr :: rest) base base = some (base, instr) := by
  simp [instrAtPcFrom]

theorem instrAtPcFrom_pc_eq {suffix : Program} {base query pc : Nat}
    {instr : Instr}
    (hAt : instrAtPcFrom suffix base query = some (pc, instr)) :
    pc = query := by
  induction suffix generalizing base with
  | nil =>
      simp [instrAtPcFrom] at hAt
  | cons head rest ih =>
      unfold instrAtPcFrom at hAt
      by_cases hQuery : query = base
      · simp [hQuery] at hAt
        have hPair : (base, head) = (pc, instr) := by
          simpa using hAt
        cases hPair
        exact hQuery.symm
      · simp [hQuery] at hAt
        exact ih hAt

theorem instrAtPcFrom_base_le_query {suffix : Program} {base query pc : Nat}
    {instr : Instr}
    (hAt : instrAtPcFrom suffix base query = some (pc, instr)) :
    base ≤ query := by
  induction suffix generalizing base with
  | nil =>
      simp [instrAtPcFrom] at hAt
  | cons head rest ih =>
      unfold instrAtPcFrom at hAt
      by_cases hQuery : query = base
      · exact Nat.le_of_eq hQuery.symm
      · simp [hQuery] at hAt
        exact
          Nat.le_trans
            (Nat.le_add_right base head.byteSize)
            (ih hAt)

theorem instrAtPcFrom_end_le_base_byteLength
    {suffix : Program} {base query pc : Nat} {instr : Instr}
    (hAt : instrAtPcFrom suffix base query = some (pc, instr)) :
    pc + instr.byteSize ≤ base + byteLength suffix := by
  induction suffix generalizing base with
  | nil =>
      simp [instrAtPcFrom] at hAt
  | cons head rest ih =>
      unfold instrAtPcFrom at hAt
      by_cases hQuery : query = base
      · simp [hQuery] at hAt
        have hPair : (base, head) = (pc, instr) := by
          simpa using hAt
        cases hPair
        simpa [byteLength_cons, Nat.add_assoc] using
          Nat.le_add_right (base + head.byteSize) (byteLength rest)
      · simp [hQuery] at hAt
        have hTail :
            pc + instr.byteSize ≤
              (base + head.byteSize) + byteLength rest :=
          ih (base := base + head.byteSize) hAt
        simpa [byteLength_cons, Nat.add_assoc] using hTail

theorem instrAtPc_pc_eq {program : Program} {query pc : Nat}
    {instr : Instr}
    (hAt : instrAtPc program query = some (pc, instr)) :
    pc = query :=
  instrAtPcFrom_pc_eq hAt

theorem instrAtPc_end_le_byteLength {program : Program}
    {query pc : Nat} {instr : Instr}
    (hAt : instrAtPc program query = some (pc, instr)) :
    pc + instr.byteSize ≤ byteLength program := by
  simpa [instrAtPc] using
    instrAtPcFrom_end_le_base_byteLength (base := 0) hAt

theorem instrAtPcFrom_next_or_end
    {suffix : Program} {base query pc : Nat} {instr : Instr}
    (hAt : instrAtPcFrom suffix base query = some (pc, instr)) :
    pc + instr.byteSize = base + byteLength suffix ∨
      ∃ nextPc nextInstr,
        instrAtPcFrom suffix base (pc + instr.byteSize) =
          some (nextPc, nextInstr) := by
  induction suffix generalizing base with
  | nil =>
      simp [instrAtPcFrom] at hAt
  | cons head rest ih =>
      unfold instrAtPcFrom at hAt
      by_cases hQuery : query = base
      · simp [hQuery] at hAt
        rcases hAt with ⟨rfl, rfl⟩
        cases rest with
        | nil =>
            left
            simp [byteLength_cons]
        | cons next tail =>
            right
            refine ⟨base + head.byteSize, next, ?_⟩
            have hNe : base + head.byteSize ≠ base := by
              have hPos := Instr.byteSize_pos head
              omega
            unfold instrAtPcFrom
            rw [if_neg hNe]
            exact
              instrAtPcFrom_at_head next tail
                (base + head.byteSize)
      · simp [hQuery] at hAt
        rcases ih (base := base + head.byteSize) hAt with
          hEnd | ⟨nextPc, nextInstr, hNext⟩
        · left
          simpa [byteLength_cons, Nat.add_assoc] using hEnd
        · right
          refine ⟨nextPc, nextInstr, ?_⟩
          have hBaseLeQuery :
              base + head.byteSize ≤ query :=
            instrAtPcFrom_base_le_query
              (suffix := rest) (base := base + head.byteSize)
              (query := query) (pc := pc) (instr := instr) hAt
          have hPc : pc = query :=
            instrAtPcFrom_pc_eq hAt
          have hBaseLe : base + head.byteSize ≤ pc := by
            omega
          have hNe : pc + instr.byteSize ≠ base := by
            have hHeadPos := Instr.byteSize_pos head
            have hInstrPos := Instr.byteSize_pos instr
            omega
          simpa [instrAtPcFrom, hNe] using hNext

theorem instrAtPc_next_or_end
    {program : Program} {query pc : Nat} {instr : Instr}
    (hAt : instrAtPc program query = some (pc, instr)) :
    pc + instr.byteSize = byteLength program ∨
      ∃ nextPc nextInstr,
        instrAtPc program (pc + instr.byteSize) =
          some (nextPc, nextInstr) := by
  simpa [instrAtPc] using
    instrAtPcFrom_next_or_end (base := 0) hAt

theorem instrAtPcFrom_of_labelPcFrom
    {suffix : Program} {base pc : Nat} {target : Label}
    (hLabel : labelPcFrom suffix base target = some pc) :
    instrAtPcFrom suffix base pc = some (pc, .label target) := by
  induction suffix generalizing base with
  | nil =>
      simp [labelPcFrom] at hLabel
  | cons head rest ih =>
      cases head with
      | label name =>
          by_cases hName : name = target
          · subst name
            simp [labelPcFrom] at hLabel
            subst pc
            exact instrAtPcFrom_at_head (.label target) rest base
          · simp [labelPcFrom, hName] at hLabel
            have hAt :=
              ih (base := base + Instr.byteSize (.label name)) hLabel
            have hBaseLe :
                base + Instr.byteSize (.label name) ≤ pc :=
              instrAtPcFrom_base_le_query hAt
            have hNe : pc ≠ base := by
              have hPos := Instr.byteSize_pos (.label name)
              omega
            simpa [instrAtPcFrom, hNe] using hAt
      | prim op =>
          change
            labelPcFrom rest (base + Instr.byteSize (.prim op)) target =
              some pc at hLabel
          have hAt :=
            ih (base := base + Instr.byteSize (.prim op)) hLabel
          have hBaseLe :
              base + Instr.byteSize (.prim op) ≤ pc :=
            instrAtPcFrom_base_le_query hAt
          have hNe : pc ≠ base := by
            have hPos := Instr.byteSize_pos (.prim op)
            omega
          simpa [instrAtPcFrom, hNe] using hAt
      | push value =>
          change
            labelPcFrom rest (base + Instr.byteSize (.push value)) target =
              some pc at hLabel
          have hAt :=
            ih (base := base + Instr.byteSize (.push value)) hLabel
          have hBaseLe :
              base + Instr.byteSize (.push value) ≤ pc :=
            instrAtPcFrom_base_le_query hAt
          have hNe : pc ≠ base := by
            have hPos := Instr.byteSize_pos (.push value)
            omega
          simpa [instrAtPcFrom, hNe] using hAt
      | jump jumpTarget =>
          change
            labelPcFrom rest
                (base + Instr.byteSize (.jump jumpTarget)) target =
              some pc at hLabel
          have hAt :=
            ih (base := base + Instr.byteSize (.jump jumpTarget)) hLabel
          have hBaseLe :
              base + Instr.byteSize (.jump jumpTarget) ≤ pc :=
            instrAtPcFrom_base_le_query hAt
          have hNe : pc ≠ base := by
            have hPos := Instr.byteSize_pos (.jump jumpTarget)
            omega
          simpa [instrAtPcFrom, hNe] using hAt
      | jumpi jumpTarget =>
          change
            labelPcFrom rest
                (base + Instr.byteSize (.jumpi jumpTarget)) target =
              some pc at hLabel
          have hAt :=
            ih (base := base + Instr.byteSize (.jumpi jumpTarget)) hLabel
          have hBaseLe :
              base + Instr.byteSize (.jumpi jumpTarget) ≤ pc :=
            instrAtPcFrom_base_le_query hAt
          have hNe : pc ≠ base := by
            have hPos := Instr.byteSize_pos (.jumpi jumpTarget)
            omega
          simpa [instrAtPcFrom, hNe] using hAt

theorem instrAtPc_of_labelPc
    {program : Program} {pc : Nat} {target : Label}
    (hLabel : labelPc program target = some pc) :
    instrAtPc program pc = some (pc, .label target) := by
  exact instrAtPcFrom_of_labelPcFrom hLabel

theorem labelPc_lt_byteLength
    {program : Program} {pc : Nat} {target : Label}
    (hLabel : labelPc program target = some pc) :
    pc < program.byteLength := by
  have hAt := instrAtPc_of_labelPc hLabel
  have hEnd := instrAtPc_end_le_byteLength hAt
  have hPositive := Instr.byteSize_pos (.label target)
  omega

theorem toNat_ofNat_labelPc
    {program : Program} {pc : Nat} {target : Label}
    (hFits : program.PCFits)
    (hLabel : labelPc program target = some pc) :
    (EvmYul.UInt256.ofNat pc).toNat = pc := by
  have hProgramLt : program.byteLength < EvmYul.UInt256.size := by
    have hWordLt : program.pcAfter.toNat < EvmYul.UInt256.size :=
      program.pcAfter.val.isLt
    rw [hFits] at hWordLt
    exact hWordLt
  exact
    EvmYul.UInt256.toNat_ofNat_of_lt
      (Nat.lt_trans (labelPc_lt_byteLength hLabel) hProgramLt)

theorem instrAtPcFrom_append_boundary
    (pre suffix : Program) (base : Nat) :
    instrAtPcFrom (pre ++ suffix) base (base + byteLength pre) =
      instrAtPcFrom suffix (base + byteLength pre)
        (base + byteLength pre) := by
  induction pre generalizing base with
  | nil =>
      simp
  | cons instr rest ih =>
      unfold instrAtPcFrom
      have hByteNe : instr.byteSize ≠ 0 :=
        Nat.ne_of_gt (Instr.byteSize_pos instr)
      simp [byteLength_cons, hByteNe]
      rw [← Nat.add_assoc]
      cases suffix with
      | nil =>
          simpa [instrAtPcFrom] using ih (base := base + instr.byteSize)
      | cons next suffixTail =>
          simpa [instrAtPcFrom] using ih (base := base + instr.byteSize)

theorem instrAtPcFrom_append_boundary_cons
    (pre suffix : Program) (instr : Instr) (base : Nat) :
    instrAtPcFrom (pre ++ instr :: suffix) base (base + byteLength pre) =
      some (base + byteLength pre, instr) := by
  rw [instrAtPcFrom_append_boundary]
  exact instrAtPcFrom_at_head instr suffix (base + byteLength pre)

def allTargetsResolveFast (program : Program) : Bool :=
  let index := program.buildLabelIndex
  program.all fun instr =>
    instr.targets.all fun target =>
      (index.get? target).isSome

@[implemented_by allTargetsResolveFast]
def allTargetsResolve (program : Program) : Bool :=
  program.all fun instr =>
    instr.targets.all fun target =>
      (labelPc program target).isSome

theorem allTargetsResolveFast_eq_allTargetsResolve (program : Program) :
    allTargetsResolveFast program = allTargetsResolve program := by
  simp only [allTargetsResolveFast, allTargetsResolve,
    buildLabelIndex_get?]

end Program

def emitInstr? (program : Program) (pc : Nat) : Instr → Option (List LocatedTarget)
  | .label _ =>
      some [{ pc := pc, instr := TargetInstr.jumpdest }]
  | .prim op =>
      some [{ pc := pc, instr := TargetInstr.prim op }]
  | .push value =>
      some [{ pc := pc, instr := TargetInstr.push32 value }]
  | .jump target => do
      let dest ← Program.labelPc program target
      some
        [ { pc := pc, instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) }
        , { pc := pc + Instr.push32Size, instr := TargetInstr.jump }
        ]
  | .jumpi target => do
      let dest ← Program.labelPc program target
      some
        [ { pc := pc, instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) }
        , { pc := pc + Instr.push32Size, instr := TargetInstr.jumpi }
        ]

def emitInstrWithTable? (table : Program.LabelTable) (pc : Nat) :
    Instr → Option (List LocatedTarget)
  | .label _ =>
      some [{ pc := pc, instr := TargetInstr.jumpdest }]
  | .prim op =>
      some [{ pc := pc, instr := TargetInstr.prim op }]
  | .push value =>
      some [{ pc := pc, instr := TargetInstr.push32 value }]
  | .jump target => do
      let dest ← Program.lookupLabel? table target
      some
        [ { pc := pc, instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) }
        , { pc := pc + Instr.push32Size, instr := TargetInstr.jump }
        ]
  | .jumpi target => do
      let dest ← Program.lookupLabel? table target
      some
        [ { pc := pc, instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) }
        , { pc := pc + Instr.push32Size, instr := TargetInstr.jumpi }
        ]

def emitInstrWithIndex? (index : Program.LabelIndex) (pc : Nat) :
    Instr → Option (List LocatedTarget)
  | .label _ =>
      some [{ pc := pc, instr := TargetInstr.jumpdest }]
  | .prim op =>
      some [{ pc := pc, instr := TargetInstr.prim op }]
  | .push value =>
      some [{ pc := pc, instr := TargetInstr.push32 value }]
  | .jump target => do
      let dest ← index.get? target
      some
        [ { pc := pc, instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) }
        , { pc := pc + Instr.push32Size, instr := TargetInstr.jump }
        ]
  | .jumpi target => do
      let dest ← index.get? target
      some
        [ { pc := pc, instr := TargetInstr.push32 (EvmYul.UInt256.ofNat dest) }
        , { pc := pc + Instr.push32Size, instr := TargetInstr.jumpi }
        ]

theorem emitInstrWithTable?_eq_emitInstr?
    (program : Program) (pc : Nat) (instr : Instr) :
    emitInstrWithTable? program.labelTable pc instr =
      emitInstr? program pc instr := by
  cases instr <;>
    simp [emitInstrWithTable?, emitInstr?,
      Program.lookupLabel?_labelTable_eq_labelPc]

theorem emitInstrWithIndex?_eq_emitInstr?
    (program : Program) (pc : Nat) (instr : Instr) :
    emitInstrWithIndex? program.buildLabelIndex pc instr =
      emitInstr? program pc instr := by
  cases instr <;>
    simp [emitInstrWithIndex?, emitInstr?,
      ← Std.HashMap.get?_eq_getElem?, Program.buildLabelIndex_get?]

/-- Every symbolic Assembly instruction expands to at most two target
instructions. -/
theorem emitInstr?_length_le_two
    {program : Program} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget}
    (hEmit : emitInstr? program pc instr = some emitted) :
    emitted.length <= 2 := by
  cases instr with
  | label name | prim name | push name =>
      simp [emitInstr?] at hEmit
      subst emitted
      simp
  | jump target | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none => simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          subst emitted
          simp

theorem emitInstr?_first {program : Program} {pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget}
    (hEmit : emitInstr? program pc instr = some emitted) :
    ∃ targetInstr rest,
      emitted = { pc := pc, instr := targetInstr } :: rest := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      cases hEmit
      exact ⟨TargetInstr.jumpdest, [], rfl⟩
  | prim op =>
      simp [emitInstr?] at hEmit
      cases hEmit
      exact ⟨TargetInstr.prim op, [], rfl⟩
  | push value =>
      simp [emitInstr?] at hEmit
      cases hEmit
      exact ⟨TargetInstr.push32 value, [], rfl⟩
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          cases hEmit
          exact
            ⟨TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
              [{ pc := pc + Instr.push32Size, instr := TargetInstr.jump }],
              rfl⟩
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          cases hEmit
          exact
            ⟨TargetInstr.push32 (EvmYul.UInt256.ofNat dest),
              [{ pc := pc + Instr.push32Size, instr := TargetInstr.jumpi }],
              rfl⟩

theorem emitInstr?_find?_none_of_byteSize_le {program : Program}
    {pc query : Nat} {instr : Instr} {emitted : List LocatedTarget}
    (hEmit : emitInstr? program pc instr = some emitted)
    (hLe : pc + instr.byteSize ≤ query) :
    emitted.find? (fun located => located.pc == query) = none := by
  cases instr with
  | label name =>
      simp [emitInstr?] at hEmit
      cases hEmit
      have hNe : pc ≠ query := by
        exact Nat.ne_of_lt
          (Nat.lt_of_lt_of_le (by simp [Instr.byteSize]) hLe)
      simp [hNe]
  | prim op =>
      simp [emitInstr?] at hEmit
      cases hEmit
      have hNe : pc ≠ query := by
        exact Nat.ne_of_lt
          (Nat.lt_of_lt_of_le (by simp [Instr.byteSize]) hLe)
      simp [hNe]
  | push value =>
      simp [emitInstr?] at hEmit
      cases hEmit
      have hNe : pc ≠ query := by
        have hLe' : pc + Instr.push32Size ≤ query := by
          simpa [Instr.byteSize] using hLe
        have hPos : 0 < Instr.push32Size := by
          decide
        exact Nat.ne_of_lt
          (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hPos pc) hLe')
      simp [hNe]
  | jump target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          cases hEmit
          have hNeHead : pc ≠ query := by
            exact Nat.ne_of_lt
              (Nat.lt_of_lt_of_le (by simp [Instr.byteSize, Instr.jumpSize]) hLe)
          have hNeJump : pc + Instr.push32Size ≠ query := by
            exact Nat.ne_of_lt
              (Nat.lt_of_lt_of_le
                (by simp [Instr.byteSize, Instr.jumpSize, Instr.push32Size])
                hLe)
          simp [hNeHead, hNeJump]
  | jumpi target =>
      cases hDest : Program.labelPc program target with
      | none =>
          simp [emitInstr?, hDest] at hEmit
      | some dest =>
          simp [emitInstr?, hDest] at hEmit
          cases hEmit
          have hNeHead : pc ≠ query := by
            exact Nat.ne_of_lt
              (Nat.lt_of_lt_of_le (by simp [Instr.byteSize, Instr.jumpSize]) hLe)
          have hNeJump : pc + Instr.push32Size ≠ query := by
            exact Nat.ne_of_lt
              (Nat.lt_of_lt_of_le
                (by simp [Instr.byteSize, Instr.jumpSize, Instr.push32Size])
                hLe)
          simp [hNeHead, hNeJump]

def emitFrom? (program : Program) : Program → Nat → Option (List LocatedTarget)
  | [], _ => some []
  | instr :: rest, pc => do
      let here ← emitInstr? program pc instr
      let there ← emitFrom? program rest (pc + instr.byteSize)
      some (here ++ there)

def emit? (program : Program) : Option (List LocatedTarget) :=
  emitFrom? program program 0

def assemble? (program : Program) : Option TargetProgram := do
  let code ← emit? program
  some { code := code }

def emitFromRev? (program : Program) :
    Program → Nat → List LocatedTarget → Option (List LocatedTarget)
  | [], _, acc => some acc.reverse
  | instr :: rest, pc, acc => do
      let here ← emitInstr? program pc instr
      emitFromRev? program rest (pc + instr.byteSize)
        (here.reverse ++ acc)

def emitFromTableRev? (table : Program.LabelTable) :
    Program → Nat → List LocatedTarget → Option (List LocatedTarget)
  | [], _, acc => some acc.reverse
  | instr :: rest, pc, acc => do
      let here ← emitInstrWithTable? table pc instr
      emitFromTableRev? table rest (pc + instr.byteSize)
        (here.reverse ++ acc)

def emitFromIndexRev? (index : Program.LabelIndex) :
    Program → Nat → List LocatedTarget → Option (List LocatedTarget)
  | [], _, acc => some acc.reverse
  | instr :: rest, pc, acc => do
      let here ← emitInstrWithIndex? index pc instr
      emitFromIndexRev? index rest (pc + instr.byteSize)
        (here.reverse ++ acc)

def emitExecutable? (program : Program) : Option (List LocatedTarget) :=
  emitFromIndexRev? program.buildLabelIndex program 0 []

def assembleExecutable? (program : Program) : Option TargetProgram := do
  let code ← emitExecutable? program
  some { code := code }

theorem emitFromRev?_eq_emitFrom?_append (program : Program) :
    ∀ rest pc acc,
      emitFromRev? program rest pc acc =
        match emitFrom? program rest pc with
        | some code => some (acc.reverse ++ code)
        | none => none
  | [], _pc, acc => by
      simp [emitFromRev?, emitFrom?]
  | instr :: rest, pc, acc => by
      simp [emitFromRev?, emitFrom?]
      cases hHere : emitInstr? program pc instr with
      | none =>
          simp [hHere]
      | some here =>
          simp [hHere]
          rw [emitFromRev?_eq_emitFrom?_append program rest
            (pc + instr.byteSize) (here.reverse ++ acc)]
          cases hRest : emitFrom? program rest (pc + instr.byteSize) with
          | none =>
              simp [hRest]
          | some there =>
              simp [hRest, List.reverse_append, List.append_assoc]

theorem emitFromTableRev?_eq_emitFromRev? (program : Program) :
    ∀ rest pc acc,
      emitFromTableRev? program.labelTable rest pc acc =
        emitFromRev? program rest pc acc
  | [], _pc, acc => by
      simp [emitFromTableRev?, emitFromRev?]
  | instr :: rest, pc, acc => by
      simp [emitFromTableRev?, emitFromRev?,
        emitInstrWithTable?_eq_emitInstr? program pc instr]
      cases hHere : emitInstr? program pc instr with
      | none => simp [hHere]
      | some here =>
          simp [hHere]
          exact
            emitFromTableRev?_eq_emitFromRev? program rest
              (pc + instr.byteSize) (here.reverse ++ acc)

theorem emitFromIndexRev?_eq_emitFromRev? (program : Program) :
    ∀ rest pc acc,
      emitFromIndexRev? program.buildLabelIndex rest pc acc =
        emitFromRev? program rest pc acc
  | [], _pc, acc => by
      simp [emitFromIndexRev?, emitFromRev?]
  | instr :: rest, pc, acc => by
      simp [emitFromIndexRev?, emitFromRev?,
        emitInstrWithIndex?_eq_emitInstr? program pc instr]
      cases hHere : emitInstr? program pc instr with
      | none => simp [hHere]
      | some here =>
          simp [hHere]
          exact
            emitFromIndexRev?_eq_emitFromRev? program rest
              (pc + instr.byteSize) (here.reverse ++ acc)

theorem emitExecutable?_eq_emit? (program : Program) :
    emitExecutable? program = emit? program := by
  rw [emitExecutable?, emitFromIndexRev?_eq_emitFromRev?]
  simp [emit?,
    emitFromRev?_eq_emitFrom?_append program program 0 []]
  cases emitFrom? program program 0 <;> rfl

theorem assembleExecutable?_eq_assemble? (program : Program) :
    assembleExecutable? program = assemble? program := by
  simp [assembleExecutable?, assemble?, emitExecutable?_eq_emit? program]

namespace TargetProgram

def fetch (target : TargetProgram) (pc : Nat) : Option TargetInstr :=
  match target.code.find? (fun located => located.pc == pc) with
  | some located => some located.instr
  | none => none

theorem fetch_cons_same (pc : Nat) (instr : TargetInstr)
    (rest : List LocatedTarget) :
    fetch { code := { pc := pc, instr := instr } :: rest } pc =
      some instr := by
  simp [fetch]

theorem fetch_append_of_fetch_left {left right : List LocatedTarget}
    {pc : Nat} {instr : TargetInstr}
    (hFetch : fetch { code := left } pc = some instr) :
    fetch { code := left ++ right } pc = some instr := by
  induction left with
  | nil =>
      simp [fetch] at hFetch
  | cons head tail ih =>
      unfold fetch at hFetch ⊢
      by_cases hEq : head.pc == pc
      · simp [hEq] at hFetch ⊢
        exact hFetch
      · simp [hEq] at hFetch ⊢
        simpa [fetch] using ih hFetch

theorem exists_located_of_fetch {target : TargetProgram}
    {pc : Nat} {instr : TargetInstr}
    (hFetch : fetch target pc = some instr) :
    ∃ located,
      located ∈ target.code ∧
        located.pc = pc ∧
          located.instr = instr := by
  unfold fetch at hFetch
  cases hFind :
      target.code.find? (fun located => located.pc == pc) with
  | none =>
      simp [hFind] at hFetch
  | some located =>
      have hMem : located ∈ target.code :=
        List.mem_of_find?_eq_some hFind
      have hPc : located.pc = pc := by
        have hFound := List.find?_some hFind
        simpa using hFound
      simp [hFind] at hFetch
      subst instr
      exact ⟨located, hMem, hPc, rfl⟩

end TargetProgram

theorem emitFrom?_fetch_some_of_instrAtPcFrom {full suffix : Program}
    {base query pc : Nat} {instr : Instr} {code : List LocatedTarget}
    (hEmit : emitFrom? full suffix base = some code)
    (hAt : Program.instrAtPcFrom suffix base query = some (pc, instr)) :
    ∃ targetInstr,
      TargetProgram.fetch { code := code } query = some targetInstr := by
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
                subst query
                rcases emitInstr?_first hHere with
                  ⟨targetInstr, restEmitted, hFirst⟩
                cases hFirst
                exact ⟨targetInstr, by simp [TargetProgram.fetch]⟩
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                have hLe :
                    base + head.byteSize ≤ query :=
                  Program.instrAtPcFrom_base_le_query hAt
                have hHereNone :
                    here.find? (fun located => located.pc == query) = none :=
                  emitInstr?_find?_none_of_byteSize_le hHere hLe
                rcases ih hThere hAt with ⟨targetInstr, hFetch⟩
                exact ⟨targetInstr, by
                  simpa [TargetProgram.fetch, hHereNone] using hFetch⟩

theorem emitFrom?_fetch_first_of_instrAtPcFrom {full suffix : Program}
    {base query pc : Nat} {instr : Instr}
    {code emitted : List LocatedTarget}
    (hEmitFrom : emitFrom? full suffix base = some code)
    (hAt : Program.instrAtPcFrom suffix base query = some (pc, instr))
    (hEmitInstr : emitInstr? full pc instr = some emitted) :
    ∃ targetInstr rest,
      emitted = { pc := query, instr := targetInstr } :: rest ∧
        TargetProgram.fetch { code := code } query = some targetInstr := by
  induction suffix generalizing base code emitted with
  | nil =>
      simp [Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      unfold emitFrom? at hEmitFrom
      cases hHere : emitInstr? full base head with
      | none =>
          simp [hHere] at hEmitFrom
      | some here =>
          cases hThere : emitFrom? full rest (base + head.byteSize) with
          | none =>
              simp [hHere, hThere] at hEmitFrom
          | some there =>
              simp [hHere, hThere] at hEmitFrom
              cases hEmitFrom
              by_cases hQuery : query = base
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                have hPair : (base, head) = (pc, instr) := by
                  simpa using hAt
                cases hPair
                subst query
                have hEmittedEq : emitted = here := by
                  rw [hHere] at hEmitInstr
                  cases hEmitInstr
                  rfl
                subst emitted
                rcases emitInstr?_first hHere with
                  ⟨targetInstr, restEmitted, hFirst⟩
                cases hFirst
                exact
                  ⟨targetInstr, restEmitted, rfl,
                    by simp [TargetProgram.fetch]⟩
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                have hLe :
                    base + head.byteSize ≤ query :=
                  Program.instrAtPcFrom_base_le_query hAt
                have hHereNone :
                    here.find? (fun located => located.pc == query) = none :=
                  emitInstr?_find?_none_of_byteSize_le hHere hLe
                rcases ih hThere hAt hEmitInstr with
                  ⟨targetInstr, restEmitted, hFirst, hFetch⟩
                exact
                  ⟨targetInstr, restEmitted, hFirst,
                    by simpa [TargetProgram.fetch, hHereNone] using hFetch⟩

theorem assemble?_fetch_first_of_instrAtPc {program : Program}
    {target : TargetProgram} {query pc : Nat} {instr : Instr}
    {emitted : List LocatedTarget}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program query = some (pc, instr))
    (hEmitInstr : emitInstr? program pc instr = some emitted) :
    ∃ targetInstr rest,
      emitted = { pc := query, instr := targetInstr } :: rest ∧
        TargetProgram.fetch target query = some targetInstr := by
  unfold assemble? at hAsm
  cases hEmit : emit? program with
  | none =>
      simp [hEmit] at hAsm
  | some code =>
      simp [hEmit] at hAsm
      cases hAsm
      have hEmitFrom : emitFrom? program program 0 = some code := by
        simpa [emit?] using hEmit
      exact
        emitFrom?_fetch_first_of_instrAtPcFrom
          (full := program) (suffix := program) (base := 0)
          (query := query) (pc := pc) (instr := instr)
          (code := code) (emitted := emitted)
          hEmitFrom hAt hEmitInstr

theorem emitFrom?_fetch_of_instrAtPcFrom_emitted_fetch
    {full suffix : Program}
    {base query pc blockPc : Nat} {instr : Instr}
    {code emitted : List LocatedTarget} {targetInstr : TargetInstr}
    (hEmitFrom : emitFrom? full suffix base = some code)
    (hAt : Program.instrAtPcFrom suffix base query = some (pc, instr))
    (hEmitInstr : emitInstr? full pc instr = some emitted)
    (hLower : query ≤ blockPc)
    (hBlockFetch :
      TargetProgram.fetch { code := emitted } blockPc = some targetInstr) :
    TargetProgram.fetch { code := code } blockPc = some targetInstr := by
  induction suffix generalizing base code emitted blockPc targetInstr with
  | nil =>
      simp [Program.instrAtPcFrom] at hAt
  | cons head rest ih =>
      unfold emitFrom? at hEmitFrom
      cases hHere : emitInstr? full base head with
      | none =>
          simp [hHere] at hEmitFrom
      | some here =>
          cases hThere : emitFrom? full rest (base + head.byteSize) with
          | none =>
              simp [hHere, hThere] at hEmitFrom
          | some there =>
              simp [hHere, hThere] at hEmitFrom
              cases hEmitFrom
              by_cases hQuery : query = base
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                have hPair : (base, head) = (pc, instr) := by
                  simpa using hAt
                cases hPair
                have hEmittedEq : emitted = here := by
                  rw [hHere] at hEmitInstr
                  cases hEmitInstr
                  rfl
                subst emitted
                exact
                  TargetProgram.fetch_append_of_fetch_left
                    (right := there) hBlockFetch
              · unfold Program.instrAtPcFrom at hAt
                simp [hQuery] at hAt
                have hLeQuery :
                    base + head.byteSize ≤ query :=
                  Program.instrAtPcFrom_base_le_query hAt
                have hLeBlock : base + head.byteSize ≤ blockPc :=
                  Nat.le_trans hLeQuery hLower
                have hHereNone :
                    here.find? (fun located => located.pc == blockPc) = none :=
                  emitInstr?_find?_none_of_byteSize_le hHere hLeBlock
                have hTailFetch :=
                  ih hThere hAt hEmitInstr hLower hBlockFetch
                simpa [TargetProgram.fetch, hHereNone] using hTailFetch

theorem assemble?_fetch_of_instrAtPc_emitted_fetch {program : Program}
    {target : TargetProgram} {query pc blockPc : Nat} {instr : Instr}
    {emitted : List LocatedTarget} {targetInstr : TargetInstr}
    (hAsm : assemble? program = some target)
    (hAt : Program.instrAtPc program query = some (pc, instr))
    (hEmitInstr : emitInstr? program pc instr = some emitted)
    (hLower : query ≤ blockPc)
    (hBlockFetch :
      TargetProgram.fetch { code := emitted } blockPc = some targetInstr) :
    TargetProgram.fetch target blockPc = some targetInstr := by
  unfold assemble? at hAsm
  cases hEmit : emit? program with
  | none =>
      simp [hEmit] at hAsm
  | some code =>
      simp [hEmit] at hAsm
      cases hAsm
      have hEmitFrom : emitFrom? program program 0 = some code := by
        simpa [emit?] using hEmit
      exact
        emitFrom?_fetch_of_instrAtPcFrom_emitted_fetch
          (full := program) (suffix := program) (base := 0)
          (query := query) (pc := pc) (blockPc := blockPc)
          (instr := instr) (code := code) (emitted := emitted)
          (targetInstr := targetInstr)
          hEmitFrom hAt hEmitInstr hLower hBlockFetch

theorem emitInstr?_fetch_jump_second {program : Program}
    {pc : Nat} {target : Label} {emitted : List LocatedTarget}
    (hEmit : emitInstr? program pc (.jump target) = some emitted) :
    TargetProgram.fetch { code := emitted } (pc + Instr.push32Size) =
      some TargetInstr.jump := by
  cases hDest : Program.labelPc program target with
  | none =>
      simp [emitInstr?, hDest] at hEmit
  | some dest =>
      simp [emitInstr?, hDest] at hEmit
      cases hEmit
      have hNe : pc ≠ pc + Instr.push32Size := by
        exact Nat.ne_of_lt
          (Nat.add_lt_add_left (by decide : 0 < Instr.push32Size) pc)
      simp [TargetProgram.fetch, beq_false_of_ne hNe]

theorem emitInstr?_fetch_jumpi_second {program : Program}
    {pc : Nat} {target : Label} {emitted : List LocatedTarget}
    (hEmit : emitInstr? program pc (.jumpi target) = some emitted) :
    TargetProgram.fetch { code := emitted } (pc + Instr.push32Size) =
      some TargetInstr.jumpi := by
  cases hDest : Program.labelPc program target with
  | none =>
      simp [emitInstr?, hDest] at hEmit
  | some dest =>
      simp [emitInstr?, hDest] at hEmit
      cases hEmit
      have hNe : pc ≠ pc + Instr.push32Size := by
        exact Nat.ne_of_lt
          (Nat.add_lt_add_left (by decide : 0 < Instr.push32Size) pc)
      simp [TargetProgram.fetch, beq_false_of_ne hNe]

theorem assemble?_fetch_jump_second_of_instrAtPc {program : Program}
    {targetProgram : TargetProgram} {query pc : Nat} {target : Label}
    {emitted : List LocatedTarget}
    (hAsm : assemble? program = some targetProgram)
    (hAt : Program.instrAtPc program query = some (pc, .jump target))
    (hEmitInstr : emitInstr? program pc (.jump target) = some emitted) :
    TargetProgram.fetch targetProgram (query + Instr.push32Size) =
      some TargetInstr.jump := by
  have hPc : pc = query := Program.instrAtPc_pc_eq hAt
  subst pc
  exact
    assemble?_fetch_of_instrAtPc_emitted_fetch
      (program := program) (target := targetProgram)
      (query := query) (pc := query)
      (blockPc := query + Instr.push32Size)
      (instr := .jump target) (emitted := emitted)
      (targetInstr := TargetInstr.jump)
      hAsm hAt hEmitInstr
      (Nat.le_add_right query Instr.push32Size)
      (emitInstr?_fetch_jump_second hEmitInstr)

theorem assemble?_fetch_jumpi_second_of_instrAtPc {program : Program}
    {targetProgram : TargetProgram} {query pc : Nat} {target : Label}
    {emitted : List LocatedTarget}
    (hAsm : assemble? program = some targetProgram)
    (hAt : Program.instrAtPc program query = some (pc, .jumpi target))
    (hEmitInstr : emitInstr? program pc (.jumpi target) = some emitted) :
    TargetProgram.fetch targetProgram (query + Instr.push32Size) =
      some TargetInstr.jumpi := by
  have hPc : pc = query := Program.instrAtPc_pc_eq hAt
  subst pc
  exact
    assemble?_fetch_of_instrAtPc_emitted_fetch
      (program := program) (target := targetProgram)
      (query := query) (pc := query)
      (blockPc := query + Instr.push32Size)
      (instr := .jumpi target) (emitted := emitted)
      (targetInstr := TargetInstr.jumpi)
      hAsm hAt hEmitInstr
      (Nat.le_add_right query Instr.push32Size)
      (emitInstr?_fetch_jumpi_second hEmitInstr)

end Assembly
end EvmCompiler
