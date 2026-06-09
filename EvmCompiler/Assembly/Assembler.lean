import EvmCompiler.Assembly.Syntax

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

end TargetInstr

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
        simpa [byteLength, Nat.add_assoc] using
          Nat.le_add_right (base + head.byteSize) (byteLength rest)
      · simp [hQuery] at hAt
        have hTail :
            pc + instr.byteSize ≤
              (base + head.byteSize) + byteLength rest :=
          ih (base := base + head.byteSize) hAt
        simpa [byteLength, Nat.add_assoc] using hTail

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

theorem instrAtPcFrom_append_boundary
    (pre suffix : Program) (base : Nat) :
    instrAtPcFrom (pre ++ suffix) base (base + byteLength pre) =
      instrAtPcFrom suffix (base + byteLength pre)
        (base + byteLength pre) := by
  induction pre generalizing base with
  | nil =>
      simp [byteLength]
  | cons instr rest ih =>
      unfold instrAtPcFrom
      have hByteNe : instr.byteSize ≠ 0 :=
        Nat.ne_of_gt (Instr.byteSize_pos instr)
      simp [byteLength, hByteNe]
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

def allTargetsResolve (program : Program) : Bool :=
  program.all fun instr =>
    instr.targets.all fun target =>
      (labelPc program target).isSome

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

def emitExecutable? (program : Program) : Option (List LocatedTarget) :=
  emitFromRev? program program 0 []

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

theorem emitExecutable?_eq_emit? (program : Program) :
    emitExecutable? program = emit? program := by
  simp [emitExecutable?, emit?,
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
