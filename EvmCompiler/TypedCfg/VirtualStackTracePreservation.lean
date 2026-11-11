import EvmCompiler.TypedCfg.VirtualStackCanon
import EvmCompiler.TypedCfg.InteractionSemantics
import EvmCompiler.TypedCfg.ShuffleCanonChainRuntime
import EvmCompiler.Assembly.InteractionPreservation
import Mathlib.Data.Nat.Bitwise

/-!
# Semantic kernel for virtual-stack trace certificates

`VirtualStack.certify?` checks source and candidate bodies with an independent
symbolic interpreter.  This file gives that check its runtime meaning.  The
central relation says that two concrete EVM stacks realise two symbolic atom
layouts under one valuation and one common opaque suffix.

This is deliberately an orphan proof leaf until the trace-soundness theorem is
complete.  Importing it cannot change compiler output.
-/

namespace EvmCompiler
namespace TypedCfg
namespace VirtualStack

open Assembly (EVMState SameRuntimeData eraseRuntimeControl)

abbrev Valuation := Atom → Word
abbrev ValueTable := List Word

theorem traceOperands_eq_rel
    {op : Assembly.PrimOp} {left right : List Atom}
    (hEq : traceOperands op left = traceOperands op right) :
    if traceCommutative? op then left.Perm right else left = right := by
  unfold traceOperands at hEq
  split at hEq
  · rename_i hComm
    simp only [hComm, if_true]
    exact
      (List.mergeSort_perm left _).symm.trans
        (hEq ▸ List.mergeSort_perm right _)
  · rename_i hComm
    simpa [hComm] using hEq

theorem perm_pair_iff {α : Type} {a₁ b₁ a₂ b₂ : α} :
    [a₁, b₁].Perm [a₂, b₂] ↔
      (a₁ = a₂ ∧ b₁ = b₂) ∨
        (a₁ = b₂ ∧ b₁ = a₂) := by
  constructor
  · intro hPerm
    simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.cons_zero, Multiset.cons_eq_cons,
      Multiset.singleton_inj, ne_eq,
      Multiset.singleton_eq_cons_iff, exists_eq_right_right,
      and_true] at hPerm
    rcases hPerm with hSame | ⟨_hNe, hLeft, hRight⟩
    · exact Or.inl hSame
    · exact Or.inr ⟨hRight.symm, hLeft⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .refl _
    · exact .swap _ _ _

theorem uint256_add_comm (left right : Word) :
    EvmYul.UInt256.add left right =
      EvmYul.UInt256.add right left := by
  unfold EvmYul.UInt256.add
  congr 1
  exact add_comm _ _

theorem uint256_land_comm (left right : Word) :
    EvmYul.UInt256.land left right =
      EvmYul.UInt256.land right left := by
  unfold EvmYul.UInt256.land
  congr 1
  apply Fin.ext
  change Nat.land left.1.val right.1.val % EvmYul.UInt256.size =
    Nat.land right.1.val left.1.val % EvmYul.UInt256.size
  exact congrArg (fun value => value % EvmYul.UInt256.size)
    (Nat.land_comm _ _)

theorem uint256_lor_comm (left right : Word) :
    EvmYul.UInt256.lor left right =
      EvmYul.UInt256.lor right left := by
  unfold EvmYul.UInt256.lor
  congr 1
  apply Fin.ext
  change Nat.lor left.1.val right.1.val % EvmYul.UInt256.size =
    Nat.lor right.1.val left.1.val % EvmYul.UInt256.size
  exact congrArg (fun value => value % EvmYul.UInt256.size)
    (Nat.lor_comm _ _)

theorem uint256_mul_comm (left right : Word) :
    EvmYul.UInt256.mul left right = EvmYul.UInt256.mul right left := by
  unfold EvmYul.UInt256.mul
  congr 1
  exact mul_comm _ _

theorem uint256_xor_comm (left right : Word) :
    EvmYul.UInt256.xor left right = EvmYul.UInt256.xor right left := by
  unfold EvmYul.UInt256.xor
  congr 1
  apply Fin.ext
  change Nat.xor left.1.val right.1.val % EvmYul.UInt256.size =
    Nat.xor right.1.val left.1.val % EvmYul.UInt256.size
  exact congrArg (fun value => value % EvmYul.UInt256.size) (Nat.xor_comm _ _)

theorem uint256_eq_comm (left right : Word) :
    EvmYul.UInt256.eq left right = EvmYul.UInt256.eq right left := by
  simp only [EvmYul.UInt256.eq, eq_comm]

def lookupAtom (values : ValueTable) (atom : Atom) : Word :=
  values[atom]!

/--
Two runtime states realise possibly different virtual layouts.  All named
values use one valuation, both stacks retain the same opaque caller suffix,
and all shared EVM data agrees.  Program counters and execution-length
counters are intentionally ignored.
-/
def AtomStateRel (sourceAtoms targetAtoms : List Atom)
    (source target : EVMState) : Prop :=
  ∃ valuation : Valuation, ∃ hidden : EvmYul.Stack Word,
    source.stack = sourceAtoms.map valuation ++ hidden ∧
      target.stack = targetAtoms.map valuation ++ hidden ∧
        source.toSharedState = target.toSharedState

/--
Index-based form of `AtomStateRel`.  The trace interpreter allocates atoms in
strictly increasing order, so successful primitive outputs extend this table
without changing any existing atom value.
-/
def TableStateRel (values : ValueTable) (hidden : EvmYul.Stack Word)
    (sourceAtoms targetAtoms : List Atom)
    (source target : EVMState) : Prop :=
  source.stack = sourceAtoms.map (lookupAtom values) ++ hidden ∧
    target.stack = targetAtoms.map (lookupAtom values) ++ hidden ∧
      source.toSharedState = target.toSharedState

def StateRealizes (values : ValueTable) (hidden : EvmYul.Stack Word)
    (atoms : List Atom) (state : EVMState) : Prop :=
  state.stack = atoms.map (lookupAtom values) ++ hidden

theorem sameRuntimeData_of_shared_stack
    {source target : EVMState}
    (hShared : source.toSharedState = target.toSharedState)
    (hStack : source.stack = target.stack) :
    SameRuntimeData source target := by
  cases source
  cases target
  simp_all [SameRuntimeData, eraseRuntimeControl]

theorem range_map_stack_getElem_take (stack : EvmYul.Stack Word)
    (count : Nat) (hCount : count ≤ stack.length) :
    (List.range count).map (fun index => stack[index]!) =
      stack.take count := by
  apply List.ext_getElem
  · simp [hCount]
  · intro index hLeft hRight
    rw [List.getElem_map, List.getElem_range]
    rw [List.getElem_take]
    rw [getElem!_pos stack index (by
      have hIndex : index < count := by
        simpa [List.length_take, Nat.min_eq_left hCount] using hRight
      omega)]

theorem AtomStateRel.range_of_sameRuntimeData
    (count : Nat) {source target : EVMState}
    (hCount : count ≤ source.stack.length)
    (hRel : SameRuntimeData source target) :
    AtomStateRel (List.range count) (List.range count) source target := by
  let valuation : Valuation := fun index => source.stack[index]!
  refine ⟨valuation, source.stack.drop count, ?_, ?_, ?_⟩
  · rw [range_map_stack_getElem_take source.stack count hCount,
      List.take_append_drop]
  · rw [← SameRuntimeData.stack_eq hRel]
    rw [range_map_stack_getElem_take source.stack count hCount,
      List.take_append_drop]
  · exact SameRuntimeData.shared_eq hRel

theorem TableStateRel.range_of_sameRuntimeData
    (count : Nat) {source target : EVMState}
    (hCount : count ≤ source.stack.length)
    (hRel : SameRuntimeData source target) :
    ∃ values : ValueTable, ∃ hidden : EvmYul.Stack Word,
      values.length = count ∧
        TableStateRel values hidden
          (List.range count) (List.range count) source target := by
  let values := source.stack.take count
  let hidden := source.stack.drop count
  have hValuesLength : values.length = count := by
    simp [values, hCount]
  refine ⟨values, hidden, hValuesLength, ?_, ?_, ?_⟩
  · change
      source.stack =
        (List.range count).map (fun index => values[index]!) ++ hidden
    rw [range_map_stack_getElem_take values count (by
      simpa [hValuesLength])]
    simp only [values, hidden, List.take_take, Nat.min_self,
      List.take_append_drop]
  · rw [← SameRuntimeData.stack_eq hRel]
    change
      source.stack =
        (List.range count).map (fun index => values[index]!) ++ hidden
    rw [range_map_stack_getElem_take values count (by
      simpa [hValuesLength])]
    simp only [values, hidden, List.take_take, Nat.min_self,
      List.take_append_drop]
  · exact SameRuntimeData.shared_eq hRel

theorem AtomStateRel.resync
    {atoms : List Atom} {source target : EVMState}
    (hRel : AtomStateRel atoms atoms source target) :
    SameRuntimeData source target := by
  rcases hRel with ⟨valuation, hidden, hSource, hTarget, hShared⟩
  apply sameRuntimeData_of_shared_stack hShared
  rw [hSource, hTarget]

theorem TableStateRel.toAtomStateRel
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {sourceAtoms targetAtoms : List Atom}
    {source target : EVMState}
    (hRel :
      TableStateRel values hidden sourceAtoms targetAtoms source target) :
    AtomStateRel sourceAtoms targetAtoms source target := by
  exact ⟨lookupAtom values, hidden, hRel⟩

theorem TableStateRel.sourceRealizes
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {sourceAtoms targetAtoms : List Atom}
    {source target : EVMState}
    (hRel :
      TableStateRel values hidden sourceAtoms targetAtoms source target) :
    StateRealizes values hidden sourceAtoms source :=
  hRel.1

theorem TableStateRel.targetRealizes
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {sourceAtoms targetAtoms : List Atom}
    {source target : EVMState}
    (hRel :
      TableStateRel values hidden sourceAtoms targetAtoms source target) :
    StateRealizes values hidden targetAtoms target :=
  hRel.2.1

theorem TableStateRel.resync
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {atoms : List Atom} {source target : EVMState}
    (hRel : TableStateRel values hidden atoms atoms source target) :
    SameRuntimeData source target :=
  hRel.toAtomStateRel.resync

theorem TableStateRel.symm
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {sourceAtoms targetAtoms : List Atom}
    {source target : EVMState}
    (hRel :
      TableStateRel values hidden sourceAtoms targetAtoms source target) :
    TableStateRel values hidden targetAtoms sourceAtoms target source :=
  ⟨hRel.2.1, hRel.1, hRel.2.2.symm⟩

theorem lookupAtom_append_of_lt
    (values outputs : ValueTable) {atom : Atom}
    (hAtom : atom < values.length) :
    lookupAtom (values ++ outputs) atom = lookupAtom values atom := by
  have hAppend : atom < (values ++ outputs).length := by
    simpa only [List.length_append] using
      Nat.lt_of_lt_of_le hAtom
        (Nat.le_add_right values.length outputs.length)
  unfold lookupAtom
  rw [getElem!_pos (values ++ outputs) atom hAppend,
    List.getElem_append_left hAtom,
    getElem!_pos values atom hAtom]

theorem map_lookupAtom_append_of_below
    (atoms : List Atom) (values outputs : ValueTable)
    (hBelow : ∀ atom ∈ atoms, atom < values.length) :
    atoms.map (lookupAtom (values ++ outputs)) =
      atoms.map (lookupAtom values) := by
  apply List.map_congr_left
  intro atom hAtom
  exact lookupAtom_append_of_lt values outputs (hBelow atom hAtom)

theorem atomRangeFrom_map_lookupAtom_append
    (values outputs : ValueTable) :
    (atomRangeFrom values.length outputs.length).map
        (lookupAtom (values ++ outputs)) =
      outputs := by
  induction outputs generalizing values with
  | nil => simp [atomRangeFrom]
  | cons output rest ih =>
      have hHead :
          lookupAtom (values ++ output :: rest) values.length = output := by
        unfold lookupAtom
        rw [getElem!_pos (values ++ output :: rest) values.length (by simp),
          List.getElem_append_right (Nat.le_refl _)]
        simp
      simp only [List.length_cons, atomRangeFrom, List.map_cons]
      rw [hHead]
      have hTail := ih (values := values ++ [output])
      simpa [List.append_assoc] using hTail

def AtomsBelow (limit : Nat) (atoms : List Atom) : Prop :=
  ∀ atom ∈ atoms, atom < limit

theorem atomsBelow_range (count : Nat) :
    AtomsBelow count (List.range count) := by
  intro atom hAtom
  simpa using (List.mem_range.mp hAtom)

theorem atomRangeFrom_eq_range' (start count : Nat) :
    atomRangeFrom start count = List.range' start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp [atomRangeFrom, List.range', ih]

theorem atomsBelow_atomRangeFrom (start count : Nat) :
    AtomsBelow (start + count) (atomRangeFrom start count) := by
  unfold AtomsBelow
  induction count generalizing start with
  | zero =>
      intro atom hAtom
      simp [atomRangeFrom] at hAtom
  | succ count ih =>
      intro atom hAtom
      simp only [atomRangeFrom, List.mem_cons] at hAtom
      rcases hAtom with rfl | hAtom
      · exact Nat.lt_add_of_pos_right (Nat.succ_pos count)
      · have hTail := ih (start + 1) atom hAtom
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem AtomsBelow.mono {left right : Nat} {atoms : List Atom}
    (hBelow : AtomsBelow left atoms) (hLe : left ≤ right) :
    AtomsBelow right atoms := by
  intro atom hAtom
  exact Nat.lt_of_lt_of_le (hBelow atom hAtom) hLe

theorem AtomsBelow.applySwap {limit depth : Nat} {atoms : List Atom}
    (hBelow : AtomsBelow limit atoms) :
    AtomsBelow limit (applySwap depth atoms) := by
  intro atom hAtom
  apply hBelow atom
  exact
    (ShuffleCanon.applySwap_perm (depth + 1) atoms).mem_iff.mp hAtom

theorem sourceSwap?_atomsBelow
    {depth limit : Nat} {before after : List Atom}
    (hRun : sourceSwap? depth before = some after)
    (hBelow : AtomsBelow limit before) :
    AtomsBelow limit after := by
  unfold sourceSwap? at hRun
  split at hRun
  · cases hRun
    exact hBelow.applySwap
  · contradiction

theorem sourceDup?_atomsBelow
    {depth limit : Nat} {before after : List Atom}
    (hRun : sourceDup? depth before = some after)
    (hBelow : AtomsBelow limit before) :
    AtomsBelow limit after := by
  unfold sourceDup? at hRun
  split at hRun
  · rename_i hDepth
    simp only [Option.bind_eq_bind] at hRun
    cases hGet : before[depth]? with
    | none => simp [hGet] at hRun
    | some atom =>
        have hAtomMem : atom ∈ before := by
          rw [List.mem_iff_getElem]
          obtain ⟨hIndex, hEq⟩ :=
            List.getElem?_eq_some_iff.mp hGet
          exact ⟨depth, hIndex, hEq⟩
        have hAtomBelow : atom < limit :=
          hBelow atom hAtomMem
        simp [hGet] at hRun
        subst after
        intro value hValue
        simp only [List.mem_cons] at hValue
        rcases hValue with rfl | hValue
        · exact hAtomBelow
        · exact hBelow value hValue
  · simp at hRun

theorem traceStep_atomsBelow
    {instr : Instr} {before after : TraceState}
    (hRun : traceStep instr before = some after)
    (hBelow : AtomsBelow before.nextAtom before.stack) :
    AtomsBelow after.nextAtom after.stack := by
  cases instr with
  | push value =>
      simp only [traceStep] at hRun
      cases hRun
      unfold AtomsBelow at hBelow ⊢
      intro atom hAtom
      simp only [List.mem_cons] at hAtom
      rcases hAtom with rfl | hAtom
      · exact Nat.lt_succ_self before.nextAtom
      · exact
          Nat.lt_trans (hBelow atom hAtom)
            (Nat.lt_succ_self before.nextAtom)
  | returnToken value =>
      simp only [traceStep] at hRun
      cases hRun
      unfold AtomsBelow at hBelow ⊢
      intro atom hAtom
      simp only [List.mem_cons] at hAtom
      rcases hAtom with rfl | hAtom
      · exact Nat.lt_succ_self before.nextAtom
      · exact
          Nat.lt_trans (hBelow atom hAtom)
            (Nat.lt_succ_self before.nextAtom)
  | pop =>
      simp only [traceStep] at hRun
      cases hStack : before.stack with
      | nil => simp [hStack] at hRun
      | cons head tail =>
          simp [hStack] at hRun
          subst after
          unfold AtomsBelow at hBelow ⊢
          intro atom hAtom
          exact hBelow atom (by simp [hStack, hAtom])
  | swap depth =>
      simp only [traceStep] at hRun
      cases hSwap : sourceSwap? depth before.stack with
      | none => simp [hSwap] at hRun
      | some stack =>
          simp [hSwap] at hRun
          subst after
          exact sourceSwap?_atomsBelow hSwap hBelow
  | dup depth =>
      simp only [traceStep] at hRun
      cases hDup : sourceDup? depth before.stack with
      | none => simp [hDup] at hRun
      | some stack =>
          simp [hDup] at hRun
          subst after
          exact sourceDup?_atomsBelow hDup hBelow
  | prim op =>
      unfold traceStep at hRun
      by_cases hAllowed : primAllowed op = true
      · simp only [hAllowed, if_true, pure_bind] at hRun
        cases hArity : op.stackArity? with
        | none => simp [hArity] at hRun
        | some arity =>
            rcases arity with ⟨inputs, outputs⟩
            by_cases hInputs : inputs ≤ before.stack.length
            · simp [hArity, hInputs] at hRun
              subst after
              unfold AtomsBelow at hBelow ⊢
              intro atom hAtom
              rw [List.mem_append] at hAtom
              rcases hAtom with hAtom | hAtom
              · exact atomsBelow_atomRangeFrom _ _ atom hAtom
              · exact
                  Nat.lt_of_lt_of_le
                    (hBelow atom (List.mem_of_mem_drop hAtom))
                    (Nat.le_add_right before.nextAtom outputs)
            · simp [hArity, hInputs] at hRun
      · have hFalse : primAllowed op = false :=
          Bool.eq_false_of_not_eq_true hAllowed
        simp [hFalse] at hRun
  | bindLocals offset names =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      exact hBelow
  | bindScratch baseDepth name slot =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      exact hBelow
  | relabel target =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      exact hBelow
  | unwind target =>
      simp [traceStep] at hRun

theorem traceBody_atomsBelow
    {body : List Instr} {before after : TraceState}
    (hRun : traceBody body before = some after)
    (hBelow : AtomsBelow before.nextAtom before.stack) :
    AtomsBelow after.nextAtom after.stack := by
  induction body generalizing before with
  | nil =>
      simp [traceBody] at hRun
      subst after
      exact hBelow
  | cons instr rest ih =>
      simp only [traceBody] at hRun
      cases hStep : traceStep instr before with
      | none => simp [hStep] at hRun
      | some middle =>
          simp [hStep] at hRun
          exact
            ih hRun (traceStep_atomsBelow hStep hBelow)

theorem traceStep_events_suffix
    {instr : Instr} {before after : TraceState}
    (hRun : traceStep instr before = some after) :
    ∃ suffix, after.events = before.events ++ suffix := by
  cases instr with
  | push value =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      exact ⟨[.push value before.nextAtom], rfl⟩
  | returnToken value =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      exact ⟨[.returnToken value before.nextAtom], rfl⟩
  | prim op =>
      unfold traceStep at hRun
      by_cases hAllowed : primAllowed op = true
      · simp only [hAllowed, if_true, pure_bind] at hRun
        cases hArity : op.stackArity? with
        | none => simp [hArity] at hRun
        | some arity =>
            rcases arity with ⟨inputs, outputs⟩
            by_cases hInputs : inputs ≤ before.stack.length
            · simp [hArity, hInputs] at hRun
              subst after
              exact
                ⟨[.prim op (traceOperands op (before.stack.take inputs))
                    (atomRangeFrom before.nextAtom outputs)], rfl⟩
            · simp [hArity, hInputs] at hRun
      · have hFalse : primAllowed op = false :=
          Bool.eq_false_of_not_eq_true hAllowed
        simp [hFalse] at hRun
  | pop =>
      simp only [traceStep] at hRun
      cases hStack : before.stack with
      | nil => simp [hStack] at hRun
      | cons head tail =>
          simp [hStack] at hRun
          subst after
          exact ⟨[], by simp⟩
  | dup depth =>
      simp only [traceStep] at hRun
      cases hDup : sourceDup? depth before.stack with
      | none => simp [hDup] at hRun
      | some stack =>
          simp [hDup] at hRun
          subst after
          exact ⟨[], by simp⟩
  | swap depth =>
      simp only [traceStep] at hRun
      cases hSwap : sourceSwap? depth before.stack with
      | none => simp [hSwap] at hRun
      | some stack =>
          simp [hSwap] at hRun
          subst after
          exact ⟨[], by simp⟩
  | bindLocals offset names =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      exact ⟨[], by simp⟩
  | bindScratch baseDepth name slot =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      exact ⟨[], by simp⟩
  | relabel output =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      exact ⟨[], by simp⟩
  | unwind output =>
      simp [traceStep] at hRun

theorem traceStep_nextAtom_of_silent
    {instr : Instr} {before after : TraceState}
    (hRun : traceStep instr before = some after)
    (hSilent : after.events = before.events) :
    after.nextAtom = before.nextAtom := by
  cases instr with
  | push value =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      have hLength := congrArg List.length hSilent
      simp at hLength
  | returnToken value =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      have hLength := congrArg List.length hSilent
      simp at hLength
  | prim op =>
      unfold traceStep at hRun
      by_cases hAllowed : primAllowed op = true
      · simp only [hAllowed, if_true, pure_bind] at hRun
        cases hArity : op.stackArity? with
        | none => simp [hArity] at hRun
        | some arity =>
            rcases arity with ⟨inputs, outputs⟩
            by_cases hInputs : inputs ≤ before.stack.length
            · simp [hArity, hInputs] at hRun
              subst after
              have hLength := congrArg List.length hSilent
              simp at hLength
            · simp [hArity, hInputs] at hRun
      · have hFalse : primAllowed op = false :=
          Bool.eq_false_of_not_eq_true hAllowed
        simp [hFalse] at hRun
  | pop =>
      simp only [traceStep] at hRun
      cases hStack : before.stack with
      | nil => simp [hStack] at hRun
      | cons head tail =>
          simp [hStack] at hRun
          subst after
          rfl
  | dup depth =>
      simp only [traceStep] at hRun
      cases hDup : sourceDup? depth before.stack with
      | none => simp [hDup] at hRun
      | some stack =>
          simp [hDup] at hRun
          subst after
          rfl
  | swap depth =>
      simp only [traceStep] at hRun
      cases hSwap : sourceSwap? depth before.stack with
      | none => simp [hSwap] at hRun
      | some stack =>
          simp [hSwap] at hRun
          subst after
          rfl
  | bindLocals offset names =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      rfl
  | bindScratch baseDepth name slot =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      rfl
  | relabel output =>
      simp only [traceStep, Option.some.injEq] at hRun
      subst after
      rfl
  | unwind output =>
      simp [traceStep] at hRun

theorem traceBody_events_suffix
    {body : List Instr} {before after : TraceState}
    (hRun : traceBody body before = some after) :
    ∃ suffix, after.events = before.events ++ suffix := by
  induction body generalizing before with
  | nil =>
      simp [traceBody] at hRun
      subst after
      exact ⟨[], by simp⟩
  | cons instr rest ih =>
      simp only [traceBody] at hRun
      cases hStep : traceStep instr before with
      | none => simp [hStep] at hRun
      | some middle =>
          simp [hStep] at hRun
          obtain ⟨headSuffix, hHead⟩ :=
            traceStep_events_suffix hStep
          obtain ⟨tailSuffix, hTail⟩ := ih hRun
          refine ⟨headSuffix ++ tailSuffix, ?_⟩
          rw [hTail, hHead, List.append_assoc]

inductive TraceEventStep :
    Instr → TraceState → TraceState → Event → Prop where
  | push (before : TraceState) (value : Word) :
      TraceEventStep (.push value) before
        { stack := before.nextAtom :: before.stack
          nextAtom := before.nextAtom + 1
          events :=
            before.events ++ [.push value before.nextAtom] }
        (.push value before.nextAtom)
  | returnToken (before : TraceState) (value : Word) :
      TraceEventStep (.returnToken value) before
        { stack := before.nextAtom :: before.stack
          nextAtom := before.nextAtom + 1
          events :=
            before.events ++ [.returnToken value before.nextAtom] }
        (.returnToken value before.nextAtom)
  | prim (before : TraceState) (op : Assembly.PrimOp)
      (inputCount outputCount : Nat)
      (hAllowed : primAllowed op = true)
      (hArity :
        op.stackArity? = some (inputCount, outputCount))
      (hBound : inputCount ≤ before.stack.length) :
      TraceEventStep (.prim op) before
        { stack :=
            atomRangeFrom before.nextAtom outputCount ++
              before.stack.drop inputCount
          nextAtom := before.nextAtom + outputCount
          events :=
            before.events ++
              [.prim op (traceOperands op (before.stack.take inputCount))
                (atomRangeFrom before.nextAtom outputCount)] }
        (.prim op (traceOperands op (before.stack.take inputCount))
          (atomRangeFrom before.nextAtom outputCount))

theorem traceEventStep_of_loud
    {instr : Instr} {before after : TraceState}
    (hTrace : traceStep instr before = some after)
    (hLoud : after.events ≠ before.events) :
    ∃ event, TraceEventStep instr before after event := by
  cases instr with
  | push value =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      exact ⟨_, .push before value⟩
  | returnToken value =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      exact ⟨_, .returnToken before value⟩
  | prim op =>
      unfold traceStep at hTrace
      by_cases hAllowed : primAllowed op = true
      · simp only [hAllowed, if_true, pure_bind] at hTrace
        cases hArity : op.stackArity? with
        | none => simp [hArity] at hTrace
        | some arity =>
            rcases arity with ⟨inputs, outputs⟩
            by_cases hInputs : inputs ≤ before.stack.length
            · simp [hArity, hInputs] at hTrace
              subst after
              exact
                ⟨_, .prim before op inputs outputs
                  hAllowed hArity hInputs⟩
            · simp [hArity, hInputs] at hTrace
      · have hFalse : primAllowed op = false :=
          Bool.eq_false_of_not_eq_true hAllowed
        simp [hFalse] at hTrace
  | pop =>
      simp only [traceStep] at hTrace
      cases hStack : before.stack with
      | nil => simp [hStack] at hTrace
      | cons head tail =>
          simp [hStack] at hTrace
          subst after
          contradiction
  | dup depth =>
      simp only [traceStep] at hTrace
      cases hDup : sourceDup? depth before.stack with
      | none => simp [hDup] at hTrace
      | some stack =>
          simp [hDup] at hTrace
          subst after
          contradiction
  | swap depth =>
      simp only [traceStep] at hTrace
      cases hSwap : sourceSwap? depth before.stack with
      | none => simp [hSwap] at hTrace
      | some stack =>
          simp [hSwap] at hTrace
          subst after
          contradiction
  | bindLocals offset names =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      contradiction
  | bindScratch baseDepth name slot =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      contradiction
  | relabel output =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      contradiction
  | unwind output =>
      simp [traceStep] at hTrace

theorem TraceEventStep.events_eq
    {instr : Instr} {before after : TraceState} {event : Event}
    (hStep : TraceEventStep instr before after event) :
    after.events = before.events ++ [event] := by
  cases hStep <;> rfl

theorem TraceEventStep.loud
    {instr : Instr} {before after : TraceState} {event : Event}
    (hStep : TraceEventStep instr before after event) :
    after.events ≠ before.events := by
  rw [hStep.events_eq]
  intro hEq
  have hLength := congrArg List.length hEq
  simp at hLength

theorem first_event_eq
    {sourceInstr targetInstr : Instr}
    {sourceBefore targetBefore sourceMiddle targetMiddle
      sourceAfter targetAfter : TraceState}
    {sourceEvent targetEvent : Event}
    {sourceRest targetRest : List Instr}
    (hSourceEvent :
      TraceEventStep sourceInstr sourceBefore sourceMiddle sourceEvent)
    (hTargetEvent :
      TraceEventStep targetInstr targetBefore targetMiddle targetEvent)
    (hSourceRest :
      traceBody sourceRest sourceMiddle = some sourceAfter)
    (hTargetRest :
      traceBody targetRest targetMiddle = some targetAfter)
    (hBeforeEvents :
      sourceBefore.events = targetBefore.events)
    (hAfterEvents :
      sourceAfter.events = targetAfter.events) :
    sourceEvent = targetEvent := by
  obtain ⟨sourceSuffix, hSourceSuffix⟩ :=
    traceBody_events_suffix hSourceRest
  obtain ⟨targetSuffix, hTargetSuffix⟩ :=
    traceBody_events_suffix hTargetRest
  rw [hSourceSuffix, hSourceEvent.events_eq,
    hTargetSuffix, hTargetEvent.events_eq] at hAfterEvents
  rw [hBeforeEvents] at hAfterEvents
  have hAssociated :
      targetBefore.events ++ ([sourceEvent] ++ sourceSuffix) =
        targetBefore.events ++ ([targetEvent] ++ targetSuffix) := by
    simpa [List.append_assoc] using hAfterEvents
  have hTail :
      [sourceEvent] ++ sourceSuffix =
        [targetEvent] ++ targetSuffix :=
    List.append_cancel_left hAssociated
  injection hTail

theorem traceBody_after_event_ne_before
    {instr : Instr} {before middle after : TraceState}
    {event : Event} {rest : List Instr}
    (hEvent : TraceEventStep instr before middle event)
    (hRest : traceBody rest middle = some after) :
    after.events ≠ before.events := by
  obtain ⟨suffix, hSuffix⟩ :=
    traceBody_events_suffix hRest
  rw [hSuffix, hEvent.events_eq]
  intro hEq
  have hLength := congrArg List.length hEq
  simp at hLength

theorem runState_push_realizes
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {atoms : List Atom} {nextAtom : Nat}
    {state : EVMState} {shape : Shape} {value : Word}
    (hNext : nextAtom = values.length)
    (hBelow : AtomsBelow values.length atoms)
    (hReal : StateRealizes values hidden atoms state) :
    ∃ final,
      Instr.runState (.push value) shape state = .ok final ∧
        StateRealizes (values ++ [value]) hidden
          (nextAtom :: atoms) final ∧
        final.toSharedState = state.toSharedState := by
  let final :=
    state.replaceStackAndIncrPC
      (value :: state.stack) (pcΔ := Assembly.pushPcDelta value)
  have hHead :
      lookupAtom (values ++ [value]) values.length = value := by
    have hMap :=
      atomRangeFrom_map_lookupAtom_append values [value]
    simpa [atomRangeFrom] using congrArg List.head? hMap
  have hOld :=
    map_lookupAtom_append_of_below atoms values [value] hBelow
  refine ⟨final, rfl, ?_, ?_⟩
  · unfold StateRealizes
    change value :: state.stack =
      (nextAtom :: atoms).map (lookupAtom (values ++ [value])) ++ hidden
    rw [hReal, List.map_cons, hNext, hHead, hOld]
    simp
  · rfl

theorem runState_returnToken_realizes
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {atoms : List Atom} {nextAtom : Nat}
    {state : EVMState} {shape : Shape} {value : Word}
    (hNext : nextAtom = values.length)
    (hBelow : AtomsBelow values.length atoms)
    (hReal : StateRealizes values hidden atoms state) :
    ∃ final,
      Instr.runState (.returnToken value) shape state = .ok final ∧
        StateRealizes (values ++ [value]) hidden
          (nextAtom :: atoms) final ∧
        final.toSharedState = state.toSharedState := by
  let final :=
    state.replaceStackAndIncrPC
      (value :: state.stack) (pcΔ := 33)
  have hHead :
      lookupAtom (values ++ [value]) values.length = value := by
    have hMap :=
      atomRangeFrom_map_lookupAtom_append values [value]
    simpa [atomRangeFrom] using congrArg List.head? hMap
  have hOld :=
    map_lookupAtom_append_of_below atoms values [value] hBelow
  refine ⟨final, rfl, ?_, ?_⟩
  · unfold StateRealizes
    change value :: state.stack =
      (nextAtom :: atoms).map
          (lookupAtom (values ++ [value])) ++ hidden
    rw [hReal, List.map_cons, hNext, hHead, hOld]
    simp
  · rfl

theorem runState_pop_realizes
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {head : Atom} {tail : List Atom}
    {state : EVMState} {shape : Shape}
    (hReal : StateRealizes values hidden (head :: tail) state) :
    ∃ final,
      Instr.runState .pop shape state = .ok final ∧
        StateRealizes values hidden tail final ∧
        final.toSharedState = state.toSharedState := by
  let final :=
    state.replaceStackAndIncrPC
      (tail.map (lookupAtom values) ++ hidden)
  refine ⟨final, ?_, ?_, ?_⟩
  · unfold StateRealizes at hReal
    simp only [List.map_cons] at hReal
    simp [Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.Stack.pop, hReal, final]
  · rfl
  · rfl

theorem runState_swap_eq_evmSwap
    {depth : Nat} (hDepth : depth < 16)
    (shape : Shape) (state : EVMState) :
    Instr.runState (.swap depth) shape state =
      EvmYul.swap (depth + 1) state := by
  interval_cases depth <;> rfl

theorem runState_dup_eq_evmDup
    {depth : Nat} (hDepth : depth < 16)
    (shape : Shape) (state : EVMState) :
    Instr.runState (.dup depth) shape state =
      EvmYul.dup (depth + 1) state := by
  interval_cases depth <;> rfl

theorem list_eq_take_append_of_getElem?
    {α : Type _} {items : List α} {index : Nat} {item : α}
    (hGet : items[index]? = some item) :
    items =
      items.take index ++ [item] ++ items.drop (index + 1) := by
  obtain ⟨hIndex, hValue⟩ :=
    List.getElem?_eq_some_iff.mp hGet
  calc
    items =
        items.take (index + 1) ++ items.drop (index + 1) :=
      (List.take_append_drop (index + 1) items).symm
    _ =
        (items.take index ++ [items[index]]) ++
          items.drop (index + 1) := by
      rw [← List.take_append_getElem hIndex]
    _ =
        items.take index ++ [item] ++ items.drop (index + 1) := by
      rw [hValue]

theorem runState_dup_realizes
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {before after : List Atom} {depth : Nat}
    {state : EVMState} {shape : Shape}
    (hTrace : sourceDup? depth before = some after)
    (hReal : StateRealizes values hidden before state) :
    ∃ final,
      Instr.runState (.dup depth) shape state = .ok final ∧
        StateRealizes values hidden after final ∧
        final.toSharedState = state.toSharedState := by
  unfold sourceDup? at hTrace
  split at hTrace
  · rename_i hDepth
    cases hGet : before[depth]? with
    | none => simp [hGet] at hTrace
    | some atom =>
        simp [hGet] at hTrace
        subst after
        let front := (before.take depth).map (lookupAtom values)
        let suffix :=
          (before.drop (depth + 1)).map (lookupAtom values) ++ hidden
        have hAtoms :=
          list_eq_take_append_of_getElem? hGet
        have hStack :
            state.stack =
              front ++ [lookupAtom values atom] ++ suffix := by
          unfold StateRealizes at hReal
          rw [hReal, hAtoms]
          simp [front, suffix, List.map_append, List.append_assoc]
        have hFrontLength : front.length = depth := by
          unfold front
          rw [List.length_map, List.length_take]
          obtain ⟨hIndex, _⟩ :=
            List.getElem?_eq_some_iff.mp hGet
          simp [Nat.min_eq_left (Nat.le_of_lt hIndex)]
        have hState :
            ({ state with
                stack := front ++ [lookupAtom values atom] ++ suffix } :
              EVMState) = state := by
          cases state
          simpa using hStack.symm
        have hDup :=
          Assembly.StackShuffle.dup_append_token
            (state := state) (front := front) (suffix := suffix)
            (token := lookupAtom values atom)
        let final :=
          state.replaceStackAndIncrPC
            (lookupAtom values atom :: state.stack)
        refine ⟨final, ?_, ?_, ?_⟩
        · rw [runState_dup_eq_evmDup hDepth]
          rw [← hFrontLength]
          rw [hState] at hDup
          simpa [hStack, final] using hDup
        · unfold StateRealizes
          change lookupAtom values atom :: state.stack =
            (atom :: before).map (lookupAtom values) ++ hidden
          rw [hReal]
          simp
        · rfl
  · simp at hTrace

theorem runState_swap_realizes
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {before after : List Atom} {depth : Nat}
    {state : EVMState} {shape : Shape}
    (hTrace : sourceSwap? depth before = some after)
    (hReal : StateRealizes values hidden before state) :
    ∃ final,
      Instr.runState (.swap depth) shape state = .ok final ∧
        StateRealizes values hidden after final ∧
        final.toSharedState = state.toSharedState := by
  unfold sourceSwap? at hTrace
  split at hTrace
  · rename_i hGuard
    rcases hGuard with ⟨hDepth, hPosition⟩
    cases hTrace
    have hStackLength :
        depth + 1 + 1 ≤ state.stack.length := by
      unfold StateRealizes at hReal
      rw [hReal, List.length_append, List.length_map]
      omega
    have hRun :=
      Peephole.swap_eq_of_depth
        (s := state) (n := depth + 1)
        (Nat.succ_le_succ (Nat.zero_le depth)) hStackLength
    let final :=
      state.replaceStackAndIncrPC
        (ShuffleCanon.applySwap (depth + 1) state.stack)
    refine ⟨final, ?_, ?_, ?_⟩
    · rw [runState_swap_eq_evmSwap hDepth]
      exact hRun
    · unfold StateRealizes
      change ShuffleCanon.applySwap (depth + 1) state.stack =
        (applySwap depth before).map (lookupAtom values) ++ hidden
      rw [hReal,
        ShuffleCanon.applySwap_append_left
          (depth + 1) (before.map (lookupAtom values)) hidden
          (by simpa using hPosition)]
      exact congrArg (· ++ hidden)
        (ShuffleCanon.applySwap_map
          (lookupAtom values) (depth + 1) before)
    · rfl
  · contradiction

/--
Execute one trace-silent instruction on the left side of a layout relation.
The atom table and the right runtime state are unchanged.
-/
theorem runState_silent_left
    {instr : Instr} {before after : TraceState}
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {targetAtoms : List Atom}
    {source target : EVMState} {shape : Shape}
    (hTrace : traceStep instr before = some after)
    (hSilent : after.events = before.events)
    (hRel :
      TableStateRel values hidden before.stack targetAtoms source target) :
    ∃ final,
      Instr.runState instr shape source = .ok final ∧
        TableStateRel values hidden after.stack targetAtoms final target := by
  cases instr with
  | push value =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      have hLength := congrArg List.length hSilent
      simp at hLength
  | returnToken value =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      have hLength := congrArg List.length hSilent
      simp at hLength
  | prim op =>
      unfold traceStep at hTrace
      by_cases hAllowed : primAllowed op = true
      · simp only [hAllowed, if_true, pure_bind] at hTrace
        cases hArity : op.stackArity? with
        | none => simp [hArity] at hTrace
        | some arity =>
            rcases arity with ⟨inputs, outputs⟩
            by_cases hInputs : inputs ≤ before.stack.length
            · simp [hArity, hInputs] at hTrace
              subst after
              have hLength := congrArg List.length hSilent
              simp at hLength
            · simp [hArity, hInputs] at hTrace
      · have hFalse : primAllowed op = false :=
          Bool.eq_false_of_not_eq_true hAllowed
        simp [hFalse] at hTrace
  | pop =>
      simp only [traceStep] at hTrace
      cases hStack : before.stack with
      | nil => simp [hStack] at hTrace
      | cons head tail =>
          simp [hStack] at hTrace
          subst after
          have hSourceRealizes :
              StateRealizes values hidden (head :: tail) source := by
            simpa [hStack] using hRel.sourceRealizes
          obtain ⟨final, hRun, hReal, hShared⟩ :=
            runState_pop_realizes
              (shape := shape) hSourceRealizes
          refine ⟨final, hRun, hReal, hRel.2.1, ?_⟩
          exact hShared.trans hRel.2.2
  | dup depth =>
      simp only [traceStep] at hTrace
      cases hDup : sourceDup? depth before.stack with
      | none => simp [hDup] at hTrace
      | some stack =>
          simp [hDup] at hTrace
          subst after
          obtain ⟨final, hRun, hReal, hShared⟩ :=
            runState_dup_realizes
              (shape := shape) hDup hRel.sourceRealizes
          refine ⟨final, hRun, hReal, hRel.2.1, ?_⟩
          exact hShared.trans hRel.2.2
  | swap depth =>
      simp only [traceStep] at hTrace
      cases hSwap : sourceSwap? depth before.stack with
      | none => simp [hSwap] at hTrace
      | some stack =>
          simp [hSwap] at hTrace
          subst after
          obtain ⟨final, hRun, hReal, hShared⟩ :=
            runState_swap_realizes
              (shape := shape) hSwap hRel.sourceRealizes
          refine ⟨final, hRun, hReal, hRel.2.1, ?_⟩
          exact hShared.trans hRel.2.2
  | bindLocals offset names =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      exact ⟨source, rfl, hRel⟩
  | bindScratch baseDepth name slot =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      exact ⟨source, rfl, hRel⟩
  | relabel output =>
      simp only [traceStep, Option.some.injEq] at hTrace
      subst after
      exact ⟨source, rfl, hRel⟩
  | unwind output =>
      simp [traceStep] at hTrace

theorem runState_silent_right
    {instr : Instr} {before after : TraceState}
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {sourceAtoms : List Atom}
    {source target : EVMState} {shape : Shape}
    (hTrace : traceStep instr before = some after)
    (hSilent : after.events = before.events)
    (hRel :
      TableStateRel values hidden sourceAtoms before.stack source target) :
    ∃ final,
      Instr.runState instr shape target = .ok final ∧
        TableStateRel values hidden sourceAtoms after.stack source final := by
  obtain ⟨final, hRun, hNext⟩ :=
    runState_silent_left hTrace hSilent hRel.symm
  exact ⟨final, hRun, hNext.symm⟩

theorem bodyType?_cons_parts
    {instr : Instr} {rest : List Instr}
    {input output : Shape}
    (hType :
      Block.bodyType? (instr :: rest) input = some output) :
    ∃ middle,
      instr.type? input = some middle ∧
        Block.bodyType? rest middle = some output := by
  rw [Peephole.bodyType?_cons,
    Option.bind_eq_some_iff] at hType
  exact hType

theorem runAt_eq_map_of_type
    {instr : Instr} {input output : Shape} {state : EVMState}
    (hType : instr.type? input = some output) :
    Instr.runAt instr input state =
      (Instr.runState instr input state).map
        (fun final => (final, output)) := by
  unfold Instr.runAt
  simp only [hType, Option.elim_some]
  cases hRun : Instr.runState instr input state <;>
    simp [Except.map]

attribute [local simp] Assembly.PrimStep.idRun_eq

/--
The primitive forms admitted by `primAllowed` have no dynamic failure mode
other than stack underflow.  Permission-sensitive state writes, bounded
return-data copies, logs, and `invalid` are deliberately excluded.
-/
def PrimStepTotal : Assembly.PrimStep → Prop
  | .binaryState _ | .returndatacopy
  | .log0 | .log1 | .log2 | .log3 | .log4 | .invalid => False
  | _ => True

theorem primStep_exists_run_of_total
    {step : Assembly.PrimStep}
    {state : EVMState}
    (hTotal : PrimStepTotal step)
    (hBound :
      Assembly.PrimStep.inputArity step ≤ state.stack.length) :
    ∃ final, step.run state = .ok final := by
  cases step with
  | bin f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop2_of_two_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run, EvmYul.EVM.execBinOp, hPop]
  | un f =>
      obtain ⟨rest, a, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run, EvmYul.EVM.execUnOp, hPop]
  | tri f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop3_of_three_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run, EvmYul.EVM.execTriOp, hPop]
  | executionEnv f =>
      simp [Assembly.PrimStep.run, EvmYul.EVM.executionEnvOp]
  | unaryExecutionEnv f =>
      obtain ⟨rest, a, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run,
        EvmYul.EVM.unaryExecutionEnvOp, hPop]
  | machineState f =>
      simp [Assembly.PrimStep.run, EvmYul.EVM.machineStateOp]
  | binaryMachineState f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop2_of_two_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run,
        EvmYul.EVM.binaryMachineStateOp, hPop]
  | binaryMachineStateWithResult f =>
      obtain ⟨rest, a, b, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop2_of_two_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run,
        EvmYul.EVM.binaryMachineStateOp', hPop]
  | ternaryMachineState f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop3_of_three_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run,
        EvmYul.EVM.ternaryMachineStateOp, hPop]
  | state f =>
      simp [Assembly.PrimStep.run, EvmYul.EVM.stateOp]
  | unaryState f =>
      obtain ⟨rest, a, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run, EvmYul.EVM.unaryStateOp, hPop]
  | binaryState f =>
      contradiction
  | ternaryCopy f =>
      obtain ⟨rest, a, b, c, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop3_of_three_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run, EvmYul.EVM.ternaryCopyOp, hPop]
  | quaternaryCopy f =>
      obtain ⟨rest, a, b, c, d, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop4_of_four_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run,
        EvmYul.EVM.quaternaryCopyOp, hPop]
  | pop =>
      obtain ⟨rest, a, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run, hPop]
  | mload =>
      obtain ⟨rest, a, hPop⟩ :=
        Assembly.PrimStep.Stack.exists_pop_of_one_le
          (by
            simpa [Assembly.PrimStep.inputArity] using hBound)
      simp [Assembly.PrimStep.run, hPop]
  | returndatacopy =>
      contradiction
  | dup n =>
      simp only [Assembly.PrimStep.inputArity] at hBound
      have hTake : (state.stack.take n).length = n := by
        simp [List.length_take, Nat.min_eq_left hBound]
      simp [Assembly.PrimStep.run, EvmYul.dup, hTake]
  | swap n =>
      simp only [Assembly.PrimStep.inputArity] at hBound
      have hTake :
          (state.stack.take (n + 1)).length = n + 1 := by
        simp [List.length_take, Nat.min_eq_left hBound]
      simp [Assembly.PrimStep.run, EvmYul.swap, hTake]
  | log0 =>
      contradiction
  | log1 =>
      contradiction
  | log2 =>
      contradiction
  | log3 =>
      contradiction
  | log4 =>
      contradiction
  | invalid =>
      contradiction

theorem primAllowed_spec {op : Assembly.PrimOp}
    (hAllowed : primAllowed op = true) :
    ∃ step, op.continuingStep? = some step ∧
      op ≠ .gas ∧ op ≠ .msize ∧ PrimStepTotal step := by
  cases op <;>
    simp [primAllowed, Assembly.PrimOp.continuingStep?,
      PrimStepTotal] at hAllowed ⊢

def PrimPostRel (values : ValueTable) (hidden : EvmYul.Stack Word)
    (sourceAtoms targetAtoms : List Atom) (outputCount : Nat)
    (source target : EVMState) : Prop :=
  ∃ outputValues : ValueTable,
    outputValues.length = outputCount ∧
      TableStateRel (values ++ outputValues) hidden
        sourceAtoms targetAtoms source target

/--
Runtime soundness of one certified primitive event.  The two physical stacks
may use different layouts below the common operand prefix.  Executing the same
closed primitive either fails on both sides or extends the common atom table
with one common list of output values.
-/
theorem runState_prim_tableRel
    {op : Assembly.PrimOp} {inputCount outputCount nextAtom : Nat}
    {operands outputAtoms sourceTail targetTail : List Atom}
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {source target : EVMState} {sourceShape targetShape : Shape}
    (hAllowed : primAllowed op = true)
    (hArity : op.stackArity? = some (inputCount, outputCount))
    (hOperandsLength : operands.length = inputCount)
    (hNext : nextAtom = values.length)
    (hOutputAtoms :
      outputAtoms = atomRangeFrom nextAtom outputCount)
    (hSourceBelow :
      AtomsBelow values.length (operands ++ sourceTail))
    (hTargetBelow :
      AtomsBelow values.length (operands ++ targetTail))
    (hRel :
      TableStateRel values hidden
        (operands ++ sourceTail) (operands ++ targetTail)
        source target) :
    Simulation.Interaction.ExceptRel
      (fun sourceError targetError : EVMException =>
        sourceError = targetError)
      (PrimPostRel values hidden
        (outputAtoms ++ sourceTail) (outputAtoms ++ targetTail)
        outputCount)
      (Instr.runState (.prim op) sourceShape source)
      (Instr.runState (.prim op) targetShape target) := by
  obtain ⟨step, hStep, hGas, hMsize, hTotal⟩ :=
    primAllowed_spec hAllowed
  let operandValues := operands.map (lookupAtom values)
  let sourceSuffix :=
    sourceTail.map (lookupAtom values) ++ hidden
  let targetSuffix :=
    targetTail.map (lookupAtom values) ++ hidden
  let sourceIso : EVMState :=
    { source with stack := operandValues }
  let targetIso : EVMState :=
    { target with stack := operandValues }
  have hSourceFrame :
      ({ sourceIso with
          stack := operandValues ++ sourceSuffix } : EVMState) =
        source := by
    unfold sourceIso operandValues sourceSuffix
    cases source
    simp only [TableStateRel, List.map_append] at hRel
    simp_all [List.append_assoc]
  have hTargetFrame :
      ({ targetIso with
          stack := operandValues ++ targetSuffix } : EVMState) =
        target := by
    unfold targetIso operandValues targetSuffix
    cases target
    simp only [TableStateRel, List.map_append] at hRel
    simp_all [List.append_assoc]
  have hIsoRel : SameRuntimeData sourceIso targetIso := by
    apply sameRuntimeData_of_shared_stack
    · exact hRel.2.2
    · rfl
  have hBoundSource : inputCount ≤ sourceIso.stack.length := by
    simp [sourceIso, operandValues, hOperandsLength]
  have hBoundTarget : inputCount ≤ targetIso.stack.length := by
    simp [targetIso, operandValues, hOperandsLength]
  have hInputArity :
      inputCount = Assembly.PrimStep.inputArity step := by
    rcases Assembly.PrimOp.stackArity_values hArity with
      ⟨hDeclared, _⟩
    rcases Assembly.PrimOp.continuingStep?_delta_alpha hStep with
      ⟨hStepInput, _⟩
    exact hDeclared.trans hStepInput
  have hSourceExists :
      ∃ final, step.run sourceIso = .ok final :=
    primStep_exists_run_of_total hTotal
      (by simpa [← hInputArity] using hBoundSource)
  have hCanonCongruence :=
    Assembly.PrimStep.run_map_eraseRuntimeControl
      (step := step) hIsoRel
  cases hSourceCanon : op.step sourceIso with
  | error sourceError =>
      have hSourceStep :
          step.run sourceIso = .error sourceError := by
        simpa [Assembly.PrimOp.step_eq_continuingStep_run hStep] using
          hSourceCanon
      obtain ⟨sourceFinal, hSourceFinal⟩ := hSourceExists
      rw [hSourceStep] at hSourceFinal
      contradiction
  | ok sourceCanonicalFinal =>
      have hSourceStep :
          step.run sourceIso = .ok sourceCanonicalFinal := by
        simpa [Assembly.PrimOp.step_eq_continuingStep_run hStep] using
          hSourceCanon
      rw [hSourceStep] at hCanonCongruence
      cases hTargetStep : step.run targetIso with
      | error targetError =>
          simp [hTargetStep, Except.map] at hCanonCongruence
      | ok targetCanonicalFinal =>
          have hTargetCanon :
              op.step targetIso = .ok targetCanonicalFinal := by
            simpa [Assembly.PrimOp.step_eq_continuingStep_run hStep]
              using hTargetStep
          have hCanonicalRel :
              SameRuntimeData sourceCanonicalFinal targetCanonicalFinal := by
            simpa [hTargetStep, Except.map] using hCanonCongruence
          have hSourceActual :=
            Assembly.PrimOp.step_append_stack_of_stackArity_le
              sourceSuffix hArity hBoundSource hSourceCanon
          have hTargetActual :=
            Assembly.PrimOp.step_append_stack_of_stackArity_le
              targetSuffix hArity hBoundTarget hTargetCanon
          rw [hSourceFrame] at hSourceActual
          rw [hTargetFrame] at hTargetActual
          have hOutputLength :
              sourceCanonicalFinal.stack.length = outputCount := by
            have hLength :=
              Assembly.PrimOp.step_stack_length_of_stackArity
                hArity hSourceCanon
            simpa [sourceIso, operandValues, hOperandsLength] using hLength
          let outputValues : ValueTable :=
            sourceCanonicalFinal.stack
          have hOutputValuesLength :
              outputValues.length = outputCount :=
            hOutputLength
          have hOutputMap :
              outputAtoms.map (lookupAtom (values ++ outputValues)) =
                outputValues := by
            rw [hOutputAtoms, hNext, ← hOutputValuesLength]
            exact atomRangeFrom_map_lookupAtom_append values outputValues
          have hSourceTailBelow :
              AtomsBelow values.length sourceTail := by
            intro atom hAtom
            exact hSourceBelow atom (by simp [hAtom])
          have hTargetTailBelow :
              AtomsBelow values.length targetTail := by
            intro atom hAtom
            exact hTargetBelow atom (by simp [hAtom])
          have hSourceTailMap :=
            map_lookupAtom_append_of_below
              sourceTail values outputValues hSourceTailBelow
          have hTargetTailMap :=
            map_lookupAtom_append_of_below
              targetTail values outputValues hTargetTailBelow
          change
            Simulation.Interaction.ExceptRel
              (fun sourceError targetError : EVMException =>
                sourceError = targetError)
              (PrimPostRel values hidden
                (outputAtoms ++ sourceTail)
                (outputAtoms ++ targetTail) outputCount)
              (op.step source) (op.step target)
          rw [hSourceActual, hTargetActual]
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨outputValues, hOutputLength, ?_⟩
          unfold TableStateRel
          constructor
          · simp only [List.map_append]
            change outputValues ++ sourceSuffix =
              outputAtoms.map (lookupAtom (values ++ outputValues)) ++
                sourceTail.map (lookupAtom (values ++ outputValues)) ++
                  hidden
            rw [hOutputMap, hSourceTailMap]
            simp [sourceSuffix, List.append_assoc]
          constructor
          · simp only [List.map_append]
            change targetCanonicalFinal.stack ++ targetSuffix =
              outputAtoms.map (lookupAtom (values ++ outputValues)) ++
                targetTail.map (lookupAtom (values ++ outputValues)) ++
                  hidden
            rw [← SameRuntimeData.stack_eq hCanonicalRel,
              hOutputMap, hTargetTailMap]
            simp [outputValues, targetSuffix, List.append_assoc]
          · change
              sourceCanonicalFinal.toSharedState =
                targetCanonicalFinal.toSharedState
            exact SameRuntimeData.shared_eq hCanonicalRel

/--
The isolated two-word execution kernel for the only primitives whose trace
operands are canonicalised. Permuting the two inputs changes no observable
runtime data after ADD, AND, or OR.
-/
theorem traceCommutative_step_map_eraseRuntimeControl
    {op : Assembly.PrimOp} {source target : EVMState}
    (hComm : traceCommutative? op = true)
    (hSourceLength : source.stack.length = 2)
    (hTargetLength : target.stack.length = 2)
    (hStackPerm : source.stack.Perm target.stack)
    (hShared : source.toSharedState = target.toSharedState) :
    (op.step source).map eraseRuntimeControl =
      (op.step target).map eraseRuntimeControl := by
  cases hSourceStack : source.stack with
  | nil =>
      simp [hSourceStack] at hSourceLength
  | cons sourceFirst sourceTail =>
      cases hSourceTail : sourceTail with
      | nil =>
          simp [hSourceStack, hSourceTail] at hSourceLength
      | cons sourceSecond sourceRest =>
          have hSourceRest : sourceRest = [] := by
            simpa [hSourceStack, hSourceTail] using hSourceLength
          subst sourceRest
          cases hTargetStack : target.stack with
          | nil =>
              simp [hTargetStack] at hTargetLength
          | cons targetFirst targetTail =>
              cases hTargetTail : targetTail with
              | nil =>
                  simp [hTargetStack, hTargetTail] at hTargetLength
              | cons targetSecond targetRest =>
                  have hTargetRest : targetRest = [] := by
                    simpa [hTargetStack, hTargetTail] using hTargetLength
                  subst targetRest
                  have hPair :
                      (sourceFirst = targetFirst ∧
                          sourceSecond = targetSecond) ∨
                        (sourceFirst = targetSecond ∧
                          sourceSecond = targetFirst) := by
                    apply perm_pair_iff.mp
                    simpa [hSourceStack, hSourceTail,
                      hTargetStack, hTargetTail] using hStackPerm
                  rcases hPair with hSame | hSwap
                  · rcases hSame with ⟨rfl, rfl⟩
                    cases op <;>
                      simp [traceCommutative?] at hComm
                    all_goals
                      simp only [Assembly.PrimOp.step,
                        Assembly.PrimOp.continuingStep?,
                        Assembly.PrimStep.run,
                        EvmYul.EVM.execBinOp,
                        hSourceStack, hSourceTail,
                        hTargetStack, hTargetTail,
                        EvmYul.Stack.pop2]
                      apply congrArg Except.ok
                      apply sameRuntimeData_of_shared_stack
                      · simpa [EvmYul.EVM.State.replaceStackAndIncrPC]
                          using hShared
                      · rfl
                  · rcases hSwap with ⟨rfl, rfl⟩
                    cases op <;>
                      simp [traceCommutative?] at hComm
                    all_goals
                      simp only [Assembly.PrimOp.step,
                        Assembly.PrimOp.continuingStep?,
                        Assembly.PrimStep.run,
                        EvmYul.EVM.execBinOp,
                        hSourceStack, hSourceTail,
                        hTargetStack, hTargetTail,
                        EvmYul.Stack.pop2]
                      apply congrArg Except.ok
                      apply sameRuntimeData_of_shared_stack
                      · simpa [EvmYul.EVM.State.replaceStackAndIncrPC]
                          using hShared
                      · simp [EvmYul.EVM.State.replaceStackAndIncrPC,
                          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
                          uint256_add_comm, uint256_land_comm,
                          uint256_lor_comm, uint256_mul_comm, uint256_xor_comm, uint256_eq_comm]

/--
Runtime soundness for one trace primitive event when its recorded operand list
is canonicalised. Non-commutative operations reduce to
`runState_prim_tableRel`; ADD/AND/OR may use the opposite physical order, whose
isolated executions are related by
`traceCommutative_step_map_eraseRuntimeControl`.
-/
theorem runState_prim_tableRel_traceOperands
    {op : Assembly.PrimOp} {inputCount outputCount nextAtom : Nat}
    {sourceOperands targetOperands outputAtoms sourceTail targetTail :
      List Atom}
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {source target : EVMState} {sourceShape targetShape : Shape}
    (hAllowed : primAllowed op = true)
    (hArity : op.stackArity? = some (inputCount, outputCount))
    (hSourceOperandsLength : sourceOperands.length = inputCount)
    (hTargetOperandsLength : targetOperands.length = inputCount)
    (hTraceOperands :
      traceOperands op sourceOperands =
        traceOperands op targetOperands)
    (hNext : nextAtom = values.length)
    (hOutputAtoms :
      outputAtoms = atomRangeFrom nextAtom outputCount)
    (hSourceBelow :
      AtomsBelow values.length (sourceOperands ++ sourceTail))
    (hTargetBelow :
      AtomsBelow values.length (targetOperands ++ targetTail))
    (hRel :
      TableStateRel values hidden
        (sourceOperands ++ sourceTail)
        (targetOperands ++ targetTail)
        source target) :
    Simulation.Interaction.ExceptRel
      (fun sourceError targetError : EVMException =>
        sourceError = targetError)
      (PrimPostRel values hidden
        (outputAtoms ++ sourceTail) (outputAtoms ++ targetTail)
        outputCount)
      (Instr.runState (.prim op) sourceShape source)
      (Instr.runState (.prim op) targetShape target) := by
  by_cases hComm : traceCommutative? op = true
  · have hDeclared :
        op.stackArity? = some (2, 1) := by
      cases op <;>
        simp [traceCommutative?, Assembly.PrimOp.stackArity?,
          Assembly.PrimOp.toEVM, EvmYul.EVM.δ,
          EvmYul.EVM.α] at hComm ⊢
    have hCounts :
        (inputCount, outputCount) = (2, 1) :=
      Option.some.inj (hArity.symm.trans hDeclared)
    cases hCounts
    have hOperandPerm :
        sourceOperands.Perm targetOperands := by
      simpa [hComm] using traceOperands_eq_rel hTraceOperands
    let sourceOperandValues :=
      sourceOperands.map (lookupAtom values)
    let targetOperandValues :=
      targetOperands.map (lookupAtom values)
    let sourceSuffix :=
      sourceTail.map (lookupAtom values) ++ hidden
    let targetSuffix :=
      targetTail.map (lookupAtom values) ++ hidden
    let sourceIso : EVMState :=
      { source with stack := sourceOperandValues }
    let targetIso : EVMState :=
      { target with stack := targetOperandValues }
    have hSourceFrame :
        ({ sourceIso with
            stack := sourceOperandValues ++ sourceSuffix } : EVMState) =
          source := by
      unfold sourceIso sourceOperandValues sourceSuffix
      cases source
      simp only [TableStateRel, List.map_append] at hRel
      simp_all [List.append_assoc]
    have hTargetFrame :
        ({ targetIso with
            stack := targetOperandValues ++ targetSuffix } : EVMState) =
          target := by
      unfold targetIso targetOperandValues targetSuffix
      cases target
      simp only [TableStateRel, List.map_append] at hRel
      simp_all [List.append_assoc]
    have hSourceLength :
        sourceIso.stack.length = 2 := by
      simp [sourceIso, sourceOperandValues,
        hSourceOperandsLength]
    have hTargetLength :
        targetIso.stack.length = 2 := by
      simp [targetIso, targetOperandValues,
        hTargetOperandsLength]
    have hValuePerm :
        sourceIso.stack.Perm targetIso.stack := by
      simpa [sourceIso, targetIso, sourceOperandValues,
        targetOperandValues] using
          hOperandPerm.map (lookupAtom values)
    have hIsoShared :
        sourceIso.toSharedState = targetIso.toSharedState := by
      exact hRel.2.2
    have hCanonicalCongruence :=
      traceCommutative_step_map_eraseRuntimeControl
        hComm hSourceLength hTargetLength hValuePerm hIsoShared
    obtain ⟨step, hStep, _hGas, _hMsize, hTotal⟩ :=
      primAllowed_spec hAllowed
    have hSourceExists :
        ∃ final, step.run sourceIso = .ok final :=
      primStep_exists_run_of_total hTotal
        (by
          have hStepInput :
              Assembly.PrimStep.inputArity step = 2 :=
            ((Assembly.PrimOp.stackArity_values hArity).1.trans
              (Assembly.PrimOp.continuingStep?_delta_alpha hStep).1).symm
          simpa [hStepInput] using
            (show 2 ≤ sourceIso.stack.length by
              rw [hSourceLength]))
    cases hSourceCanon : op.step sourceIso with
    | error sourceError =>
        have hSourceStep :
            step.run sourceIso = .error sourceError := by
          simpa [Assembly.PrimOp.step_eq_continuingStep_run hStep]
            using hSourceCanon
        obtain ⟨sourceFinal, hSourceFinal⟩ := hSourceExists
        rw [hSourceStep] at hSourceFinal
        contradiction
    | ok sourceCanonicalFinal =>
        rw [hSourceCanon] at hCanonicalCongruence
        cases hTargetCanon : op.step targetIso with
        | error targetError =>
            simp [hTargetCanon, Except.map] at hCanonicalCongruence
        | ok targetCanonicalFinal =>
            have hCanonicalRel :
                SameRuntimeData sourceCanonicalFinal
                  targetCanonicalFinal := by
              simpa [hTargetCanon, Except.map] using
                hCanonicalCongruence
            have hBoundSource : 2 ≤ sourceIso.stack.length := by
              rw [hSourceLength]
            have hBoundTarget : 2 ≤ targetIso.stack.length := by
              rw [hTargetLength]
            have hSourceActual :=
              Assembly.PrimOp.step_append_stack_of_stackArity_le
                sourceSuffix hArity hBoundSource hSourceCanon
            have hTargetActual :=
              Assembly.PrimOp.step_append_stack_of_stackArity_le
                targetSuffix hArity hBoundTarget hTargetCanon
            rw [hSourceFrame] at hSourceActual
            rw [hTargetFrame] at hTargetActual
            have hOutputLength :
                sourceCanonicalFinal.stack.length = 1 := by
              have hLength :=
                Assembly.PrimOp.step_stack_length_of_stackArity
                  hArity hSourceCanon
              simpa [sourceIso, sourceOperandValues,
                hSourceOperandsLength] using hLength
            let outputValues : ValueTable :=
              sourceCanonicalFinal.stack
            have hOutputMap :
                outputAtoms.map
                    (lookupAtom (values ++ outputValues)) =
                  outputValues := by
              rw [hOutputAtoms, hNext, ← hOutputLength]
              exact
                atomRangeFrom_map_lookupAtom_append
                  values outputValues
            have hSourceTailBelow :
                AtomsBelow values.length sourceTail := by
              intro atom hAtom
              exact hSourceBelow atom (by simp [hAtom])
            have hTargetTailBelow :
                AtomsBelow values.length targetTail := by
              intro atom hAtom
              exact hTargetBelow atom (by simp [hAtom])
            have hSourceTailMap :=
              map_lookupAtom_append_of_below
                sourceTail values outputValues hSourceTailBelow
            have hTargetTailMap :=
              map_lookupAtom_append_of_below
                targetTail values outputValues hTargetTailBelow
            change
              Simulation.Interaction.ExceptRel
                (fun sourceError targetError : EVMException =>
                  sourceError = targetError)
                (PrimPostRel values hidden
                  (outputAtoms ++ sourceTail)
                  (outputAtoms ++ targetTail) 1)
                (op.step source) (op.step target)
            rw [hSourceActual, hTargetActual]
            apply Simulation.Interaction.ExceptRel.ok
            refine ⟨outputValues, hOutputLength, ?_⟩
            unfold TableStateRel
            constructor
            · simp only [List.map_append]
              change outputValues ++ sourceSuffix =
                outputAtoms.map
                    (lookupAtom (values ++ outputValues)) ++
                  sourceTail.map
                      (lookupAtom (values ++ outputValues)) ++
                    hidden
              rw [hOutputMap, hSourceTailMap]
              simp [sourceSuffix, List.append_assoc]
            constructor
            · simp only [List.map_append]
              change targetCanonicalFinal.stack ++ targetSuffix =
                outputAtoms.map
                    (lookupAtom (values ++ outputValues)) ++
                  targetTail.map
                      (lookupAtom (values ++ outputValues)) ++
                    hidden
              rw [← SameRuntimeData.stack_eq hCanonicalRel,
                hOutputMap, hTargetTailMap]
              simp [outputValues, targetSuffix,
                List.append_assoc]
            · have hSharedFinal :
                  sourceCanonicalFinal.toSharedState =
                    targetCanonicalFinal.toSharedState :=
                SameRuntimeData.shared_eq hCanonicalRel
              exact hSharedFinal
  · have hOperands :
        sourceOperands = targetOperands := by
      have hRelOperands :=
        traceOperands_eq_rel hTraceOperands
      simpa [Bool.eq_false_of_not_eq_true hComm] using
        hRelOperands
    subst targetOperands
    exact
      runState_prim_tableRel hAllowed hArity
        hSourceOperandsLength hNext hOutputAtoms
        hSourceBelow hTargetBelow hRel

def EventPostRel (hidden : EvmYul.Stack Word)
    (sourceAfter targetAfter : TraceState)
    (source target : EVMState) : Prop :=
  ∃ values : ValueTable,
    values.length = sourceAfter.nextAtom ∧
      sourceAfter.nextAtom = targetAfter.nextAtom ∧
        TableStateRel values hidden
          sourceAfter.stack targetAfter.stack source target

def BodyPostRel (hidden : EvmYul.Stack Word)
    (sourceAfter targetAfter : TraceState)
    (source target : EVMState × Shape) : Prop :=
  EventPostRel hidden sourceAfter targetAfter source.1 target.1

theorem runState_event_pair
    {sourceInstr targetInstr : Instr}
    {sourceBefore targetBefore sourceAfter targetAfter : TraceState}
    {sourceEvent targetEvent : Event}
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {source target : EVMState}
    {sourceShape targetShape : Shape}
    (hSourceEvent :
      TraceEventStep sourceInstr sourceBefore sourceAfter sourceEvent)
    (hTargetEvent :
      TraceEventStep targetInstr targetBefore targetAfter targetEvent)
    (hEventEq : sourceEvent = targetEvent)
    (hSourceNext : sourceBefore.nextAtom = values.length)
    (hTargetNext : targetBefore.nextAtom = values.length)
    (hSourceBelow :
      AtomsBelow values.length sourceBefore.stack)
    (hTargetBelow :
      AtomsBelow values.length targetBefore.stack)
    (hRel :
      TableStateRel values hidden
        sourceBefore.stack targetBefore.stack source target) :
    Simulation.Interaction.ExceptRel
      (fun sourceError targetError : EVMException =>
        sourceError = targetError)
      (EventPostRel hidden sourceAfter targetAfter)
      (Instr.runState sourceInstr sourceShape source)
      (Instr.runState targetInstr targetShape target) := by
  cases hSourceEvent with
  | push sourceBefore value =>
      cases hTargetEvent with
      | push targetBefore targetValue =>
          injection hEventEq with hValue hAtom
          subst targetValue
          obtain ⟨sourceFinal, hSourceRun, hSourceReal, hSourceShared⟩ :=
            runState_push_realizes
              (shape := sourceShape) (value := value)
              hSourceNext hSourceBelow hRel.sourceRealizes
          obtain ⟨targetFinal, hTargetRun, hTargetReal, hTargetShared⟩ :=
            runState_push_realizes
              (shape := targetShape) (value := value)
              hTargetNext hTargetBelow hRel.targetRealizes
          rw [hSourceRun, hTargetRun]
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨values ++ [value], ?_, ?_, ?_⟩
          · simp [← hSourceNext]
          · rw [hSourceNext, hTargetNext]
          · exact
              ⟨hSourceReal, hTargetReal,
                hSourceShared.trans
                  (hRel.2.2.trans hTargetShared.symm)⟩
      | returnToken targetBefore targetValue =>
          contradiction
      | prim targetBefore targetOp targetInput targetOutput
          hTargetAllowed hTargetArity hTargetBound =>
          contradiction
  | returnToken sourceBefore value =>
      cases hTargetEvent with
      | push targetBefore targetValue =>
          contradiction
      | returnToken targetBefore targetValue =>
          injection hEventEq with hValue hAtom
          subst targetValue
          obtain ⟨sourceFinal, hSourceRun, hSourceReal, hSourceShared⟩ :=
            runState_returnToken_realizes
              (shape := sourceShape) (value := value)
              hSourceNext hSourceBelow hRel.sourceRealizes
          obtain ⟨targetFinal, hTargetRun, hTargetReal, hTargetShared⟩ :=
            runState_returnToken_realizes
              (shape := targetShape) (value := value)
              hTargetNext hTargetBelow hRel.targetRealizes
          rw [hSourceRun, hTargetRun]
          apply Simulation.Interaction.ExceptRel.ok
          refine ⟨values ++ [value], ?_, ?_, ?_⟩
          · simp [← hSourceNext]
          · rw [hSourceNext, hTargetNext]
          · exact
              ⟨hSourceReal, hTargetReal,
                hSourceShared.trans
                  (hRel.2.2.trans hTargetShared.symm)⟩
      | prim targetBefore targetOp targetInput targetOutput
          hTargetAllowed hTargetArity hTargetBound =>
          contradiction
  | prim sourceBefore sourceOp sourceInput sourceOutput
      hSourceAllowed hSourceArity hSourceBound =>
      cases hTargetEvent with
      | push targetBefore targetValue =>
          contradiction
      | returnToken targetBefore targetValue =>
          contradiction
      | prim targetBefore targetOp targetInput targetOutput
          hTargetAllowed hTargetArity hTargetBound =>
          injection hEventEq with hOp hOperandsEvent hOutputsEvent
          subst targetOp
          have hCounts :
              (sourceInput, sourceOutput) =
                (targetInput, targetOutput) := by
            exact Option.some.inj
              (hSourceArity.symm.trans hTargetArity)
          cases hCounts
          let sourceOperands := sourceBefore.stack.take sourceInput
          let targetOperands := targetBefore.stack.take sourceInput
          let sourceTail := sourceBefore.stack.drop sourceInput
          let targetTail := targetBefore.stack.drop sourceInput
          have hSourceAtoms :
              sourceBefore.stack = sourceOperands ++ sourceTail := by
            exact (List.take_append_drop _ _).symm
          have hTargetAtoms :
              targetBefore.stack = targetOperands ++ targetTail := by
            exact (List.take_append_drop _ _).symm
          have hSourceOperandsLength :
              sourceOperands.length = sourceInput := by
            unfold sourceOperands
            simp [List.length_take,
              Nat.min_eq_left hSourceBound]
          have hTargetOperandsLength :
              targetOperands.length = sourceInput := by
            unfold targetOperands
            simp [List.length_take,
              Nat.min_eq_left hTargetBound]
          have hRel' :
              TableStateRel values hidden
                (sourceOperands ++ sourceTail)
                (targetOperands ++ targetTail)
                source target := by
            simpa [hSourceAtoms, hTargetAtoms] using hRel
          have hSourceBelow' :
              AtomsBelow values.length
                (sourceOperands ++ sourceTail) := by
            simpa [hSourceAtoms] using hSourceBelow
          have hTargetBelow' :
              AtomsBelow values.length
                (targetOperands ++ targetTail) := by
            simpa [hTargetAtoms] using hTargetBelow
          have hPrim :=
            runState_prim_tableRel_traceOperands
              (sourceShape := sourceShape)
              (targetShape := targetShape)
              hSourceAllowed hSourceArity
              hSourceOperandsLength hTargetOperandsLength
              hOperandsEvent hSourceNext rfl
              hSourceBelow' hTargetBelow' hRel'
          change
            Simulation.Interaction.ExceptRel
              (fun sourceError targetError : EVMException =>
                sourceError = targetError)
              (PrimPostRel values hidden
                (atomRangeFrom sourceBefore.nextAtom sourceOutput ++
                  sourceTail)
                (atomRangeFrom sourceBefore.nextAtom sourceOutput ++
                  targetTail)
                sourceOutput)
              (sourceOp.step source) (sourceOp.step target)
            at hPrim
          change
            Simulation.Interaction.ExceptRel
              (fun sourceError targetError : EVMException =>
                sourceError = targetError)
              (EventPostRel hidden
                { stack :=
                    atomRangeFrom sourceBefore.nextAtom sourceOutput ++
                      sourceTail
                  nextAtom := sourceBefore.nextAtom + sourceOutput
                  events :=
                    sourceBefore.events ++
                        [.prim sourceOp
                          (traceOperands sourceOp sourceOperands)
                        (atomRangeFrom sourceBefore.nextAtom sourceOutput)] }
                { stack :=
                    atomRangeFrom targetBefore.nextAtom sourceOutput ++
                      targetTail
                  nextAtom := targetBefore.nextAtom + sourceOutput
                  events :=
                    targetBefore.events ++
                        [.prim sourceOp
                          (traceOperands sourceOp targetOperands)
                        (atomRangeFrom targetBefore.nextAtom sourceOutput)] })
              (sourceOp.step source) (sourceOp.step target)
          cases hSourceRun : sourceOp.step source with
          | error sourceError =>
              cases hTargetRun : sourceOp.step target with
              | error targetError =>
                  rw [hSourceRun, hTargetRun] at hPrim
                  cases hPrim with
                  | error hError =>
                      exact .error hError
              | ok targetFinal =>
                  rw [hSourceRun, hTargetRun] at hPrim
                  cases hPrim
          | ok sourceFinal =>
              cases hTargetRun : sourceOp.step target with
              | error targetError =>
                  rw [hSourceRun, hTargetRun] at hPrim
                  cases hPrim
              | ok targetFinal =>
                  rw [hSourceRun, hTargetRun] at hPrim
                  cases hPrim with
                  | ok hPost =>
                    apply Simulation.Interaction.ExceptRel.ok
                    rcases hPost with
                      ⟨outputValues, hOutputLength, hTable⟩
                    refine
                      ⟨values ++ outputValues, ?_, ?_, ?_⟩
                    · rw [List.length_append, hOutputLength,
                        ← hSourceNext]
                    · rw [hSourceNext, hTargetNext]
                    · simpa [hSourceNext, hTargetNext] using hTable

theorem runBody_trace_pair_fuel
    (sourceBody targetBody : List Instr) (fuel : Nat)
    {sourceBefore targetBefore sourceAfter targetAfter : TraceState}
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {source target : EVMState}
    {sourceInput targetInput sourceOutput targetOutput : Shape}
    (hSourceTrace :
      traceBody sourceBody sourceBefore = some sourceAfter)
    (hTargetTrace :
      traceBody targetBody targetBefore = some targetAfter)
    (hBeforeEvents :
      sourceBefore.events = targetBefore.events)
    (hAfterEvents :
      sourceAfter.events = targetAfter.events)
    (hSourceNext : sourceBefore.nextAtom = values.length)
    (hTargetNext : targetBefore.nextAtom = values.length)
    (hSourceBelow :
      AtomsBelow values.length sourceBefore.stack)
    (hTargetBelow :
      AtomsBelow values.length targetBefore.stack)
    (hRel :
      TableStateRel values hidden
        sourceBefore.stack targetBefore.stack source target)
    (hSourceType :
      Block.bodyType? sourceBody sourceInput = some sourceOutput)
    (hTargetType :
      Block.bodyType? targetBody targetInput = some targetOutput)
    (hFuel : sourceBody.length + targetBody.length ≤ fuel) :
    Simulation.Interaction.ExceptRel
      (fun sourceError targetError : EVMException =>
        sourceError = targetError)
      (BodyPostRel hidden sourceAfter targetAfter)
      (Block.runBody sourceBody sourceInput source)
      (Block.runBody targetBody targetInput target) := by
  cases sourceBody with
  | nil =>
      simp only [traceBody, Option.some.injEq] at hSourceTrace
      subst sourceAfter
      simp only [Block.bodyType?, Option.some.injEq] at hSourceType
      subst sourceOutput
      cases targetBody with
      | nil =>
          simp only [traceBody, Option.some.injEq] at hTargetTrace
          subst targetAfter
          simp only [Block.bodyType?, Option.some.injEq] at hTargetType
          subst targetOutput
          apply Simulation.Interaction.ExceptRel.ok
          exact
            ⟨values, hSourceNext.symm,
              hSourceNext.trans hTargetNext.symm, hRel⟩
      | cons targetInstr targetRest =>
          simp only [traceBody] at hTargetTrace
          cases hTargetStep :
              traceStep targetInstr targetBefore with
          | none => simp [hTargetStep] at hTargetTrace
          | some targetMiddle =>
              simp [hTargetStep] at hTargetTrace
              obtain ⟨targetMiddleShape, hTargetHeadType,
                  hTargetRestType⟩ :=
                bodyType?_cons_parts hTargetType
              have hTargetSilent :
                  targetMiddle.events = targetBefore.events := by
                by_contra hLoud
                obtain ⟨event, hEvent⟩ :=
                  traceEventStep_of_loud hTargetStep hLoud
                have hFinalNe :=
                  traceBody_after_event_ne_before
                    hEvent hTargetTrace
                apply hFinalNe
                rw [← hAfterEvents, hBeforeEvents]
              obtain ⟨targetMiddleState, hTargetRun, hMiddleRel⟩ :=
                runState_silent_right
                  hTargetStep hTargetSilent hRel
              have hTargetRunAt :
                  Instr.runAt targetInstr targetInput target =
                    .ok (targetMiddleState, targetMiddleShape) := by
                rw [runAt_eq_map_of_type hTargetHeadType,
                  hTargetRun]
                rfl
              have hRecursive :=
                runBody_trace_pair_fuel [] targetRest (fuel - 1)
                  (sourceBefore := sourceBefore)
                  (targetBefore := targetMiddle)
                  (sourceAfter := sourceBefore)
                  (targetAfter := targetAfter)
                  (values := values) (hidden := hidden)
                  (source := source)
                  (target := targetMiddleState)
                  (sourceInput := sourceInput)
                  (targetInput := targetMiddleShape)
                  (sourceOutput := sourceInput)
                  (targetOutput := targetOutput)
                  rfl hTargetTrace
                  (by rw [hTargetSilent, ← hBeforeEvents])
                  hAfterEvents hSourceNext
                  (by
                    rw [traceStep_nextAtom_of_silent
                      hTargetStep hTargetSilent]
                    exact hTargetNext)
                  hSourceBelow
                  (by
                    have hBound :=
                      traceStep_atomsBelow hTargetStep
                        (by simpa [hTargetNext] using hTargetBelow)
                    simpa [traceStep_nextAtom_of_silent
                      hTargetStep hTargetSilent, hTargetNext] using
                        hBound)
                  hMiddleRel rfl hTargetRestType
                  (by
                    simp only [List.length_cons] at hFuel ⊢
                    omega)
              simpa [Block.runBody, hTargetRunAt] using hRecursive
  | cons sourceInstr sourceRest =>
      simp only [traceBody] at hSourceTrace
      cases hSourceStep :
          traceStep sourceInstr sourceBefore with
      | none => simp [hSourceStep] at hSourceTrace
      | some sourceMiddle =>
          simp [hSourceStep] at hSourceTrace
          obtain ⟨sourceMiddleShape, hSourceHeadType,
              hSourceRestType⟩ :=
            bodyType?_cons_parts hSourceType
          by_cases hSourceSilent :
              sourceMiddle.events = sourceBefore.events
          · obtain ⟨sourceMiddleState, hSourceRun, hMiddleRel⟩ :=
              runState_silent_left
                hSourceStep hSourceSilent hRel
            have hSourceRunAt :
                Instr.runAt sourceInstr sourceInput source =
                  .ok (sourceMiddleState, sourceMiddleShape) := by
              rw [runAt_eq_map_of_type hSourceHeadType,
                hSourceRun]
              rfl
            have hRecursive :=
              runBody_trace_pair_fuel sourceRest targetBody (fuel - 1)
                (sourceBefore := sourceMiddle)
                (targetBefore := targetBefore)
                (sourceAfter := sourceAfter)
                (targetAfter := targetAfter)
                (values := values) (hidden := hidden)
                (source := sourceMiddleState) (target := target)
                (sourceInput := sourceMiddleShape)
                (targetInput := targetInput)
                (sourceOutput := sourceOutput)
                (targetOutput := targetOutput)
                hSourceTrace hTargetTrace
                (by rw [hSourceSilent, hBeforeEvents])
                hAfterEvents
                (by
                  rw [traceStep_nextAtom_of_silent
                    hSourceStep hSourceSilent]
                  exact hSourceNext)
                hTargetNext
                (by
                  have hBound :=
                    traceStep_atomsBelow hSourceStep
                      (by simpa [hSourceNext] using hSourceBelow)
                  simpa [traceStep_nextAtom_of_silent
                    hSourceStep hSourceSilent, hSourceNext] using
                      hBound)
                hTargetBelow hMiddleRel
                hSourceRestType hTargetType
                (by
                  simp only [List.length_cons] at hFuel ⊢
                  omega)
            simpa [Block.runBody, hSourceRunAt] using hRecursive
          · obtain ⟨sourceEvent, hSourceEvent⟩ :=
              traceEventStep_of_loud hSourceStep hSourceSilent
            cases targetBody with
            | nil =>
                simp only [traceBody, Option.some.injEq] at hTargetTrace
                subst targetAfter
                exact False.elim
                  ((traceBody_after_event_ne_before
                    hSourceEvent hSourceTrace)
                    (by rw [hAfterEvents, ← hBeforeEvents]))
            | cons targetInstr targetRest =>
                simp only [traceBody] at hTargetTrace
                cases hTargetStep :
                    traceStep targetInstr targetBefore with
                | none => simp [hTargetStep] at hTargetTrace
                | some targetMiddle =>
                    simp [hTargetStep] at hTargetTrace
                    obtain ⟨targetMiddleShape, hTargetHeadType,
                        hTargetRestType⟩ :=
                      bodyType?_cons_parts hTargetType
                    by_cases hTargetSilent :
                        targetMiddle.events = targetBefore.events
                    · obtain ⟨targetMiddleState, hTargetRun,
                          hMiddleRel⟩ :=
                        runState_silent_right
                          hTargetStep hTargetSilent hRel
                      have hTargetRunAt :
                          Instr.runAt targetInstr targetInput target =
                            .ok
                              (targetMiddleState,
                                targetMiddleShape) := by
                        rw [runAt_eq_map_of_type hTargetHeadType,
                          hTargetRun]
                        rfl
                      have hRecursive :=
                        runBody_trace_pair_fuel
                          (sourceInstr :: sourceRest) targetRest (fuel - 1)
                          (sourceBefore := sourceBefore)
                          (targetBefore := targetMiddle)
                          (sourceAfter := sourceAfter)
                          (targetAfter := targetAfter)
                          (values := values) (hidden := hidden)
                          (source := source)
                          (target := targetMiddleState)
                          (sourceInput := sourceInput)
                          (targetInput := targetMiddleShape)
                          (sourceOutput := sourceOutput)
                          (targetOutput := targetOutput)
                          (by
                            simp only [traceBody, hSourceStep]
                            exact hSourceTrace)
                          hTargetTrace
                          (by rw [hTargetSilent, ← hBeforeEvents])
                          hAfterEvents hSourceNext
                          (by
                            rw [traceStep_nextAtom_of_silent
                              hTargetStep hTargetSilent]
                            exact hTargetNext)
                          hSourceBelow
                          (by
                            have hBound :=
                              traceStep_atomsBelow hTargetStep
                                (by
                                  simpa [hTargetNext] using
                                    hTargetBelow)
                            simpa [traceStep_nextAtom_of_silent
                              hTargetStep hTargetSilent,
                              hTargetNext] using hBound)
                          hMiddleRel hSourceType hTargetRestType
                          (by
                            simp only [List.length_cons] at hFuel ⊢
                            omega)
                      simpa [Block.runBody, hTargetRunAt] using
                        hRecursive
                    · obtain ⟨targetEvent, hTargetEvent⟩ :=
                        traceEventStep_of_loud
                          hTargetStep hTargetSilent
                      have hEventEq :
                          sourceEvent = targetEvent :=
                        first_event_eq hSourceEvent hTargetEvent
                          hSourceTrace hTargetTrace
                          hBeforeEvents hAfterEvents
                      have hEventRel :=
                        runState_event_pair
                          (sourceShape := sourceInput)
                          (targetShape := targetInput)
                          hSourceEvent hTargetEvent hEventEq
                          hSourceNext hTargetNext
                          hSourceBelow hTargetBelow hRel
                      cases hSourceRun :
                          Instr.runState sourceInstr sourceInput source with
                      | error sourceError =>
                          cases hTargetRun :
                              Instr.runState targetInstr targetInput target with
                          | error targetError =>
                              rw [hSourceRun, hTargetRun] at hEventRel
                              cases hEventRel with
                              | error hError =>
                                  simpa [Block.runBody,
                                    runAt_eq_map_of_type hSourceHeadType,
                                    runAt_eq_map_of_type hTargetHeadType,
                                    hSourceRun, hTargetRun, Except.map] using
                                      (Simulation.Interaction.ExceptRel.error
                                        (errorRel :=
                                          fun sourceError targetError :
                                              EVMException =>
                                            sourceError = targetError)
                                        (resultRel :=
                                          BodyPostRel hidden
                                            sourceAfter targetAfter)
                                        hError)
                          | ok targetMiddleState =>
                              rw [hSourceRun, hTargetRun] at hEventRel
                              cases hEventRel
                      | ok sourceMiddleState =>
                          cases hTargetRun :
                              Instr.runState targetInstr targetInput target with
                          | error targetError =>
                              rw [hSourceRun, hTargetRun] at hEventRel
                              cases hEventRel
                          | ok targetMiddleState =>
                              rw [hSourceRun, hTargetRun] at hEventRel
                              cases hEventRel with
                              | ok hPost =>
                                  rcases hPost with
                                    ⟨nextValues, hNextLength,
                                      hMiddleNextEq, hMiddleRel⟩
                                  have hSourceRunAt :
                                      Instr.runAt sourceInstr
                                          sourceInput source =
                                        .ok
                                          (sourceMiddleState,
                                            sourceMiddleShape) := by
                                    rw [runAt_eq_map_of_type
                                      hSourceHeadType, hSourceRun]
                                    rfl
                                  have hTargetRunAt :
                                      Instr.runAt targetInstr
                                          targetInput target =
                                        .ok
                                          (targetMiddleState,
                                            targetMiddleShape) := by
                                    rw [runAt_eq_map_of_type
                                      hTargetHeadType, hTargetRun]
                                    rfl
                                  have hRecursive :=
                                    runBody_trace_pair_fuel
                                      sourceRest targetRest (fuel - 1)
                                      (sourceBefore := sourceMiddle)
                                      (targetBefore := targetMiddle)
                                      (sourceAfter := sourceAfter)
                                      (targetAfter := targetAfter)
                                      (values := nextValues)
                                      (hidden := hidden)
                                      (source := sourceMiddleState)
                                      (target := targetMiddleState)
                                      (sourceInput := sourceMiddleShape)
                                      (targetInput := targetMiddleShape)
                                      (sourceOutput := sourceOutput)
                                      (targetOutput := targetOutput)
                                      hSourceTrace hTargetTrace
                                      (by
                                        rw [hSourceEvent.events_eq,
                                          hTargetEvent.events_eq,
                                          hBeforeEvents, hEventEq])
                                      hAfterEvents
                                      hNextLength.symm
                                      (hMiddleNextEq.symm.trans
                                        hNextLength.symm)
                                      (by
                                        have hBound :=
                                          traceStep_atomsBelow hSourceStep
                                            (by
                                              simpa [hSourceNext] using
                                                hSourceBelow)
                                        simpa [hNextLength] using hBound)
                                      (by
                                        have hBound :=
                                          traceStep_atomsBelow hTargetStep
                                            (by
                                              simpa [hTargetNext] using
                                                hTargetBelow)
                                        simpa [hNextLength,
                                          hMiddleNextEq] using hBound)
                                      hMiddleRel
                                      hSourceRestType hTargetRestType
                                      (by
                                        simp only [List.length_cons]
                                          at hFuel ⊢
                                        omega)
                                  simpa [Block.runBody, hSourceRunAt,
                                    hTargetRunAt] using hRecursive
termination_by fuel
decreasing_by
  all_goals
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at hFuel
    omega

theorem openRunState_eq_done_of_traceStep
    {instr : Instr} {before after : TraceState}
    {shape : Shape} {state : EVMState}
    (hTrace : traceStep instr before = some after) :
    InteractionSemantics.Instr.openRunState instr shape state =
      .done (Instr.runState instr shape state) := by
  cases instr with
  | prim op =>
      unfold traceStep at hTrace
      by_cases hAllowed : primAllowed op = true
      · simp only [hAllowed, if_true, pure_bind] at hTrace
        cases hArity : op.stackArity? with
        | none => simp [hArity] at hTrace
        | some arity =>
            rcases arity with ⟨inputs, outputs⟩
            by_cases hInputs : inputs ≤ before.stack.length
            · obtain ⟨step, hStep, hGas, hMsize, _hTotal⟩ :=
                primAllowed_spec hAllowed
              change
                Assembly.InteractionSemantics.PrimOp.openStep op state =
                  .done (op.step state)
              rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
                hStep hGas hMsize]
              rw [Assembly.PrimOp.step_eq_continuingStep_run hStep]
            · simp [hArity, hInputs] at hTrace
      · have hFalse : primAllowed op = false :=
          Bool.eq_false_of_not_eq_true hAllowed
        simp [hFalse] at hTrace
  | push value
  | returnToken value
  | pop
  | dup depth
  | swap depth
  | bindLocals offset names
  | bindScratch baseDepth name slot
  | relabel output
  | unwind output =>
      exact
        InteractionSemantics.Instr.openRunState_eq_done_of_not_prim
          (by intro op hEq; cases hEq)

theorem openRunAt_eq_done_of_traceStep
    {instr : Instr} {before after : TraceState}
    {shape : Shape} {state : EVMState}
    (hTrace : traceStep instr before = some after) :
    InteractionSemantics.Instr.openRunAt instr shape state =
      .done (Instr.runAt instr shape state) := by
  unfold InteractionSemantics.Instr.openRunAt
    Control.Instr.runAt Instr.runAt
  cases hType : instr.type? shape with
  | none => rfl
  | some output =>
      rw [openRunState_eq_done_of_traceStep hTrace]
      cases hRun : instr.runState shape state <;>
        rfl

theorem openRunBody_eq_done_of_traceBody
    {body : List Instr} {before after : TraceState}
    {shape : Shape} {state : EVMState}
    (hTrace : traceBody body before = some after) :
    InteractionSemantics.Block.openRunBody body shape state =
      .done (Block.runBody body shape state) := by
  induction body generalizing before shape state with
  | nil => rfl
  | cons instr rest ih =>
      simp only [traceBody] at hTrace
      cases hStep : traceStep instr before with
      | none => simp [hStep] at hTrace
      | some middle =>
          simp [hStep] at hTrace
          unfold InteractionSemantics.Block.openRunBody
          change
            Simulation.Interaction.bind
                (InteractionSemantics.Instr.openRunAt
                  instr shape state)
                (fun result =>
                  InteractionSemantics.Block.openRunBody
                    rest result.2 result.1) =
              .done (Block.runBody (instr :: rest) shape state)
          rw [openRunAt_eq_done_of_traceStep hStep]
          cases hRun : Instr.runAt instr shape state with
          | error error =>
              simp [Block.runBody, hRun]
          | ok result =>
              rcases result with ⟨middleState, middleShape⟩
              simp only [Simulation.Interaction.bind_done_ok]
              rw [ih hTrace]
              simp [Block.runBody, hRun]

/-- A successful straight-line run carries the output shape computed by the
same typing fold.  The semantic certificate needs this small deterministic
shape fact when it hands control back to a block terminator. -/
theorem runBody_output_of_bodyType :
    ∀ (body : List Instr)
      {input output : Shape} {state final : EVMState}
      {runOutput : Shape},
      Block.bodyType? body input = some output →
      Block.runBody body input state = .ok (final, runOutput) →
      runOutput = output
  | [], input, output, state, final, runOutput, hType, hRun => by
      simp [Block.bodyType?, Block.runBody] at hType hRun
      exact hRun.2.symm.trans hType
  | instr :: rest, input, output, state, final, runOutput,
      hType, hRun => by
      obtain ⟨middle, hHeadType, hRestType⟩ :=
        bodyType?_cons_parts hType
      simp only [Block.runBody] at hRun
      cases hHeadRun : Instr.runAt instr input state with
      | error error =>
          simp [hHeadRun] at hRun
      | ok result =>
          rcases result with ⟨middleState, middleShape⟩
          simp only [hHeadRun, Bind.bind, Except.bind] at hRun
          have hMiddleShape : middleShape = middle := by
            rw [runAt_eq_map_of_type hHeadType] at hHeadRun
            cases hRunState :
                Instr.runState instr input state with
            | error error =>
                simp [hRunState, Except.map] at hHeadRun
            | ok next =>
                simp [hRunState, Except.map] at hHeadRun
                exact hHeadRun.2.symm
          subst middleShape
          exact
            runBody_output_of_bodyType rest hRestType hRun

theorem openRunBody_trace_pair
    (sourceBody targetBody : List Instr)
    {sourceBefore targetBefore sourceAfter targetAfter : TraceState}
    {values : ValueTable} {hidden : EvmYul.Stack Word}
    {source target : EVMState}
    {sourceInput targetInput sourceOutput targetOutput : Shape}
    (hSourceTrace :
      traceBody sourceBody sourceBefore = some sourceAfter)
    (hTargetTrace :
      traceBody targetBody targetBefore = some targetAfter)
    (hBeforeEvents :
      sourceBefore.events = targetBefore.events)
    (hAfterEvents :
      sourceAfter.events = targetAfter.events)
    (hSourceNext : sourceBefore.nextAtom = values.length)
    (hTargetNext : targetBefore.nextAtom = values.length)
    (hSourceBelow :
      AtomsBelow values.length sourceBefore.stack)
    (hTargetBelow :
      AtomsBelow values.length targetBefore.stack)
    (hRel :
      TableStateRel values hidden
        sourceBefore.stack targetBefore.stack source target)
    (hSourceType :
      Block.bodyType? sourceBody sourceInput = some sourceOutput)
    (hTargetType :
      Block.bodyType? targetBody targetInput = some targetOutput) :
    Simulation.Interaction.Rel
      (Simulation.Interaction.ExceptRel
        (fun sourceError targetError : EVMException =>
          sourceError = targetError)
        (fun sourceDone targetDone =>
          BodyPostRel hidden sourceAfter targetAfter
              sourceDone targetDone ∧
            sourceDone.2 = sourceOutput ∧
            targetDone.2 = targetOutput))
      (InteractionSemantics.Block.openRunBody
        sourceBody sourceInput source)
      (InteractionSemantics.Block.openRunBody
        targetBody targetInput target) := by
  rw [openRunBody_eq_done_of_traceBody hSourceTrace,
    openRunBody_eq_done_of_traceBody hTargetTrace]
  apply Simulation.Interaction.Rel.done
  have hPair :=
    runBody_trace_pair_fuel sourceBody targetBody
      (sourceBody.length + targetBody.length)
      hSourceTrace hTargetTrace hBeforeEvents hAfterEvents
      hSourceNext hTargetNext hSourceBelow hTargetBelow hRel
      hSourceType hTargetType (Nat.le_refl _)
  cases hSourceRun :
      Block.runBody sourceBody sourceInput source with
  | error sourceError =>
      cases hTargetRun :
          Block.runBody targetBody targetInput target with
      | error targetError =>
          rw [hSourceRun, hTargetRun] at hPair
          cases hPair with
          | error hError =>
              exact Simulation.Interaction.ExceptRel.error hError
      | ok targetDone =>
          rw [hSourceRun, hTargetRun] at hPair
          cases hPair
  | ok sourceDone =>
      cases hTargetRun :
          Block.runBody targetBody targetInput target with
      | error targetError =>
          rw [hSourceRun, hTargetRun] at hPair
          cases hPair
      | ok targetDone =>
          rw [hSourceRun, hTargetRun] at hPair
          change
            Simulation.Interaction.ExceptRel
              (fun sourceError targetError : EVMException =>
                sourceError = targetError)
              (BodyPostRel hidden sourceAfter targetAfter)
              (.ok sourceDone) (.ok targetDone) at hPair
          rcases sourceDone with ⟨sourceFinal, sourceRunOutput⟩
          rcases targetDone with ⟨targetFinal, targetRunOutput⟩
          cases hPair with
          | ok hPost =>
              apply Simulation.Interaction.ExceptRel.ok
              exact
                ⟨hPost,
                  runBody_output_of_bodyType
                    sourceBody hSourceType hSourceRun,
                  runBody_output_of_bodyType
                    targetBody hTargetType hTargetRun⟩

theorem map_applySwap {α : Type _} (valuation : Atom → α)
    (depth : Nat) (atoms : List Atom) :
    (applySwap depth atoms).map valuation =
      ShuffleCanon.applySwap (depth + 1) (atoms.map valuation) := by
  exact (ShuffleCanon.applySwap_map valuation (depth + 1) atoms).symm

theorem primAllowed_openStep {op : Assembly.PrimOp}
    (hAllowed : primAllowed op = true) (state : EVMState) :
    ∃ step, op.continuingStep? = some step ∧
      Assembly.InteractionSemantics.PrimOp.openStep op state =
        .done (step.run state) := by
  obtain ⟨step, hStep, hGas, hMsize, _hTotal⟩ :=
    primAllowed_spec hAllowed
  exact
    ⟨step, hStep,
      Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
        hStep hGas hMsize⟩

end VirtualStack
end TypedCfg
end EvmCompiler
