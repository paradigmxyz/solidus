import EvmCompiler.Expressions.Compiler
import EvmCompiler.Expressions.EffectSemantics

namespace EvmCompiler
namespace Expressions
namespace TargetFuel

/-
Recursive target-code footprint used to reserve meta-fuel across retained
target nesting. Unlike `List.length`, this sees blocks nested under
conditionals, switches, and loops.
-/
mutual
  def stmtSize : Expressions.Stmt → Nat
    | .code _ => 1
    | .expr _ => 1
    | .if_ _ body => 1 + blockSize body
    | .switch _ cases defaultBody =>
        1 + caseListSize cases + defaultSize defaultBody
    | .for_ init _ post body =>
        1 + blockSize init + blockSize post + blockSize body
    | .brk => 1
    | .cont => 1
    | .leave => 1
    | .call _ => 1
    | .terminal _ => 1

  def blockSize : Expressions.Block → Nat
    | ⟨stmts⟩ => stmtListSize stmts

  def stmtListSize : List Expressions.Stmt → Nat
    | [] => 0
    | stmt :: rest => stmtSize stmt + stmtListSize rest

  def caseListSize : List (Expressions.Word × Expressions.Block) → Nat
    | [] => 0
    | (_, body) :: rest => blockSize body + caseListSize rest

  def defaultSize : Option Expressions.Block → Nat
    | none => 0
    | some body => blockSize body
end

/- Code hidden under retained target control nodes. The ordinary block-length
term in `targetBudget` pays for the current flat list; this measure pays only
for nested blocks. -/
mutual
  def stmtNestedSize : Expressions.Stmt → Nat
    | .code _ => 0
    | .expr _ => 0
    | .if_ _ body => blockSize body
    | .switch _ cases defaultBody =>
        caseListSize cases + defaultSize defaultBody
    | .for_ init _ post body =>
        blockSize init + blockSize post + blockSize body
    | .brk => 0
    | .cont => 0
    | .leave => 0
    | .call _ => 0
    | .terminal _ => 0

  def stmtListNestedSize : List Expressions.Stmt → Nat
    | [] => 0
    | stmt :: rest => stmtNestedSize stmt + stmtListNestedSize rest
end

mutual
  def structuredStmtSize : Structured.Stmt → Nat
    | .code _ => 1
    | .if_ _ body => 1 + structuredBlockSize body
    | .switch _ cases defaultBody =>
        1 + structuredCaseListSize cases +
          structuredDefaultSize defaultBody
    | .for_ init _ post body =>
        1 + structuredBlockSize init + structuredBlockSize post +
          structuredBlockSize body
    | .brk => 1
    | .cont => 1
    | .leave => 1
    | .call _ => 1
    | .terminal _ => 1

  def structuredBlockSize : Structured.Block → Nat
    | ⟨stmts⟩ => structuredStmtListSize stmts

  def structuredStmtListSize : List Structured.Stmt → Nat
    | [] => 0
    | stmt :: rest => structuredStmtSize stmt + structuredStmtListSize rest

  def structuredCaseListSize : List (Structured.Word × Structured.Block) → Nat
    | [] => 0
    | (_, body) :: rest =>
        structuredBlockSize body + structuredCaseListSize rest

  def structuredDefaultSize : Option Structured.Block → Nat
    | none => 0
    | some body => structuredBlockSize body
end

theorem blockSize_toStructured (block : Expressions.Block) :
    structuredBlockSize block.toStructured = blockSize block := by
  exact Expressions.Block.rec
    (motive_1 := fun block =>
      structuredBlockSize block.toStructured = blockSize block)
    (motive_2 := fun stmt =>
      structuredStmtSize stmt.toStructured = stmtSize stmt)
    (motive_3 := fun stmts =>
      structuredStmtListSize
          (Expressions.StmtList.toStructured stmts) =
        stmtListSize stmts)
    (motive_4 := fun cases =>
      structuredCaseListSize
          (Expressions.CaseList.toStructured cases) =
        caseListSize cases)
    (motive_5 := fun defaultBody =>
      structuredDefaultSize
          (Expressions.Default.toStructured defaultBody) =
        defaultSize defaultBody)
    (motive_6 := fun pair =>
      structuredBlockSize pair.2.toStructured = blockSize pair.2)
    (fun _stmts hStmts => hStmts)
    (fun _code => rfl)
    (fun _expr => rfl)
    (fun _cond _body hBody => by
      simp [Expressions.Stmt.toStructured, structuredStmtSize, stmtSize,
        hBody])
    (fun _scrutinee _cases _defaultBody hCases hDefault => by
      simp [Expressions.Stmt.toStructured, structuredStmtSize, stmtSize,
        hCases, hDefault])
    (fun _init _cond _post _body hInit hPost hBody => by
      simp [Expressions.Stmt.toStructured, structuredStmtSize, stmtSize,
        hInit, hPost, hBody])
    (by rfl)
    (by rfl)
    (by rfl)
    (fun _name => rfl)
    (fun _kind => rfl)
    (by rfl)
    (fun _stmt _rest hStmt hRest => by
      simp [Expressions.StmtList.toStructured, structuredStmtListSize,
        stmtListSize, hStmt, hRest])
    (by rfl)
    (fun head _rest hHead hRest => by
      rcases head with ⟨_value, _body⟩
      simp [Expressions.CaseList.toStructured, structuredCaseListSize,
        caseListSize, hHead, hRest])
    (by rfl)
    (fun _body hBody => by
      simp [Expressions.Default.toStructured, structuredDefaultSize,
        defaultSize, hBody])
    (fun _value _body hBody => hBody)
    block

theorem stmtListSize_toStructured (stmts : List Expressions.Stmt) :
    structuredStmtListSize (Expressions.StmtList.toStructured stmts) =
      stmtListSize stmts := by
  have h := blockSize_toStructured ({ stmts := stmts } : Expressions.Block)
  simpa [Expressions.Block.toStructured, structuredBlockSize, blockSize] using h

private theorem stmtList_toStructured_length
    (stmts : List Expressions.Stmt) :
    (Expressions.StmtList.toStructured stmts).length = stmts.length := by
  induction stmts with
  | nil => rfl
  | cons stmt rest ih =>
      simp [Expressions.StmtList.toStructured, ih]

private theorem structured_block_size_le_sum
    {proc : Structured.Proc} {procs : List Structured.Proc}
    (hMem : proc ∈ procs) :
    structuredBlockSize proc.body ≤
      (procs.map fun candidate =>
        structuredBlockSize candidate.body).sum := by
  induction procs with
  | nil => simp at hMem
  | cons head tail ih =>
      simp only [List.mem_cons] at hMem
      simp only [List.map_cons, List.sum_cons]
      cases hMem with
      | inl hHead => subst head; omega
      | inr hTail =>
          have hBound := ih hTail
          omega

theorem structured_block_size_le_program
    {name : Structured.Name} {proc : Structured.Proc}
    {program : Structured.Program}
    (hLookup : Structured.ProcList.lookup? name program.procs = some proc) :
    structuredBlockSize proc.body ≤
      (program.procs.map fun candidate =>
        structuredBlockSize candidate.body).sum := by
  exact structured_block_size_le_sum
    (Structured.ProcList.mem_of_lookup? hLookup)

@[simp] theorem stmtListSize_append
    (left right : List Expressions.Stmt) :
    stmtListSize (left ++ right) =
      stmtListSize left + stmtListSize right := by
  induction left with
  | nil => simp [stmtListSize]
  | cons stmt rest ih => simp [stmtListSize, ih, Nat.add_assoc]

@[simp] theorem stmtListNestedSize_append
    (left right : List Expressions.Stmt) :
    stmtListNestedSize (left ++ right) =
      stmtListNestedSize left + stmtListNestedSize right := by
  induction left with
  | nil => simp [stmtListNestedSize]
  | cons stmt rest ih =>
      simp [stmtListNestedSize, ih, Nat.add_assoc]

theorem stmtSize_eq (stmt : Expressions.Stmt) :
    stmtSize stmt = 1 + stmtNestedSize stmt := by
  cases stmt <;> simp [stmtSize, stmtNestedSize] <;> omega

theorem stmtListSize_eq (stmts : List Expressions.Stmt) :
    stmtListSize stmts = stmts.length + stmtListNestedSize stmts := by
  induction stmts with
  | nil => simp [stmtListSize, stmtListNestedSize]
  | cons stmt rest ih =>
      rw [stmtListSize, List.length_cons, stmtListNestedSize,
        stmtSize_eq, ih]
      omega

theorem nestedSize_le_size (stmts : List Expressions.Stmt) :
    stmtListNestedSize stmts ≤ stmtListSize stmts := by
  rw [stmtListSize_eq]
  omega

theorem stmtSize_pos (stmt : Expressions.Stmt) :
    0 < stmtSize stmt := by
  cases stmt <;> simp [stmtSize]

theorem length_le_stmtListSize (stmts : List Expressions.Stmt) :
    stmts.length ≤ stmtListSize stmts := by
  induction stmts with
  | nil => simp [stmtListSize]
  | cons stmt rest ih =>
      simp only [List.length_cons, stmtListSize]
      have hStmt := stmtSize_pos stmt
      omega

theorem stmtListSize_suffix
    {whole pre suffix : List Expressions.Stmt}
    (hCode : whole = pre ++ suffix) :
    stmtListSize suffix ≤ stmtListSize whole := by
  rw [hCode, stmtListSize_append]
  omega

theorem selected_block_size_le
    {value : Expressions.Word}
    {cases : List (Expressions.Word × Expressions.Block)}
    {defaultBody : Option Expressions.Block}
    {selected : Expressions.Block}
    (hSelect :
      Expressions.EffectSemantics.Switch.select value cases defaultBody =
        some selected) :
    blockSize selected ≤ caseListSize cases + defaultSize defaultBody := by
  induction cases with
  | nil =>
      cases defaultBody with
      | none => simp [Expressions.EffectSemantics.Switch.select] at hSelect
      | some body =>
          simp [Expressions.EffectSemantics.Switch.select] at hSelect
          subst selected
          simp [caseListSize, defaultSize]
  | cons head rest ih =>
      rcases head with ⟨caseValue, caseBody⟩
      simp only [Expressions.EffectSemantics.Switch.select]
        at hSelect
      split at hSelect
      next hEq =>
        cases hSelect
        simp [caseListSize]
        omega
      next hNe =>
        have hTail := ih hSelect
        simp [caseListSize]
        omega

/--
Uniform target meta-fuel reserved for one source recursion level. The two sums
cover every compiler-selected procedure body, including nested target control.
-/
def programStride (program : Expressions.Program) : Nat :=
  8 +
    (program.toStructured.procs.map fun proc => proc.body.stmts.length).sum +
    (program.toStructured.procs.map fun proc =>
      structuredBlockSize proc.body).sum

theorem eight_le_programStride (program : Expressions.Program) :
    8 ≤ programStride program := by
  unfold programStride
  omega

private theorem structured_body_length_le_sum
    {proc : Structured.Proc} {procs : List Structured.Proc}
    (hMem : proc ∈ procs) :
    proc.body.stmts.length ≤
      (procs.map fun candidate => candidate.body.stmts.length).sum := by
  induction procs with
  | nil => simp at hMem
  | cons head tail ih =>
      simp only [List.mem_cons] at hMem
      simp only [List.map_cons, List.sum_cons]
      rcases hMem with rfl | hTail
      · omega
      · have hBound := ih hTail
        omega

theorem proc_body_size_add_length_add_eight_le_programStride
    {program : Expressions.Program} {name : Expressions.Name}
    {proc : Expressions.Proc}
    (hLookup :
      Expressions.EffectSemantics.ProcList.lookup? name program.procs =
        some proc) :
    stmtListSize proc.body.stmts + proc.body.stmts.length + 8 ≤
      programStride program := by
  have hMem : proc ∈ program.procs :=
    Expressions.EffectSemantics.ProcList.mem_of_lookup? hLookup
  have hStructuredMem :
      proc.toStructured ∈ program.toStructured.procs :=
    Expressions.ProcList.mem_toStructured hMem
  have hLength := structured_body_length_le_sum hStructuredMem
  have hSize := structured_block_size_le_sum hStructuredMem
  have hProcBody : proc.toStructured.body = proc.body.toStructured := rfl
  rw [hProcBody] at hLength hSize
  have hBlockStmts :
      proc.body.toStructured.stmts =
        Expressions.StmtList.toStructured proc.body.stmts := by
    cases proc.body
    rfl
  rw [hBlockStmts] at hLength
  have hLengthEq :
      (Expressions.StmtList.toStructured proc.body.stmts).length =
        proc.body.stmts.length :=
    stmtList_toStructured_length proc.body.stmts
  rw [hLengthEq] at hLength
  rw [blockSize_toStructured proc.body] at hSize
  have hBlockSize :
      blockSize proc.body = stmtListSize proc.body.stmts := by
    cases proc.body
    rfl
  rw [hBlockSize] at hSize
  have hStmtSize :
      stmtListSize proc.body.stmts ≤
        (program.toStructured.procs.map fun candidate =>
          structuredBlockSize candidate.body).sum := by
    exact hSize
  unfold programStride
  omega

/--
Structural target budget for a compiled statement list at one source fuel.
`stmtListSize` pays for the current list and every nested target block; the
stride pays for recursive source control and any selected internal callee.
-/
def budget (program : Expressions.Program) (sourceFuel : Nat)
    (stmts : List Expressions.Stmt) : Nat :=
  stmtListSize stmts + programStride program * (sourceFuel + 1)

def Covers (program : Expressions.Program) (sourceFuel targetFuel : Nat)
    (stmts : List Expressions.Stmt) : Prop :=
  budget program sourceFuel stmts ≤ targetFuel

theorem length_lt_budget (program : Expressions.Program)
    (sourceFuel : Nat) (stmts : List Expressions.Stmt) :
    stmts.length < budget program sourceFuel stmts := by
  have hLength := length_le_stmtListSize stmts
  have hStride := eight_le_programStride program
  unfold budget
  nlinarith

@[simp] theorem budget_append (program : Expressions.Program)
    (sourceFuel : Nat) (left right : List Expressions.Stmt) :
    budget program sourceFuel (left ++ right) =
      stmtListSize left + budget program sourceFuel right := by
  simp [budget, stmtListSize_append, Nat.add_assoc]

theorem budget_le_succ_append (program : Expressions.Program)
    (sourceFuel : Nat) (left right : List Expressions.Stmt) :
    budget program sourceFuel left ≤
      budget program (sourceFuel + 1) (left ++ right) := by
  rw [budget_append]
  unfold budget
  have hStride := eight_le_programStride program
  nlinarith

theorem budget_le_append (program : Expressions.Program)
    (sourceFuel : Nat) (left right : List Expressions.Stmt) :
    budget program sourceFuel left ≤
      budget program sourceFuel (left ++ right) := by
  rw [budget_append]
  unfold budget
  omega

theorem budget_tail_add_length_le_succ_append
    (program : Expressions.Program) (sourceFuel : Nat)
    (left right : List Expressions.Stmt) :
    left.length + budget program sourceFuel right ≤
      budget program (sourceFuel + 1) (left ++ right) := by
  rw [budget_append]
  unfold budget
  have hLength := length_le_stmtListSize left
  have hStride := eight_le_programStride program
  nlinarith

theorem budget_tail_le_succ_append_sub_length
    (program : Expressions.Program) (sourceFuel : Nat)
    (left right : List Expressions.Stmt) :
    budget program sourceFuel right ≤
      budget program (sourceFuel + 1) (left ++ right) - left.length := by
  have h := budget_tail_add_length_le_succ_append
    program sourceFuel left right
  omega

theorem budget_tail_add_length_le_append
    (program : Expressions.Program) (sourceFuel : Nat)
    (left right : List Expressions.Stmt) :
    left.length + budget program sourceFuel right ≤
      budget program sourceFuel (left ++ right) := by
  rw [budget_append]
  have hLength := length_le_stmtListSize left
  omega

theorem budget_tail_le_append_sub_length
    (program : Expressions.Program) (sourceFuel : Nat)
    (left right : List Expressions.Stmt) :
    budget program sourceFuel right ≤
      budget program sourceFuel (left ++ right) - left.length := by
  have h := budget_tail_add_length_le_append
    program sourceFuel left right
  omega

theorem budget_if_body_add_two_le
    (program : Expressions.Program) (sourceFuel : Nat)
    (cond : Expressions.Expr 1) (body : Expressions.Block)
    (rest : List Expressions.Stmt) :
    budget program sourceFuel body.stmts + 2 ≤
      budget program (sourceFuel + 1) (.if_ cond body :: rest) := by
  cases body
  unfold budget
  simp only [stmtListSize, stmtSize, blockSize, List.length_cons]
  have hStride := eight_le_programStride program
  nlinarith

theorem budget_switch_selected_add_two_le
    (program : Expressions.Program) (sourceFuel : Nat)
    (scrutinee : Expressions.Expr 1)
    (cases : List (Expressions.Word × Expressions.Block))
    (defaultBody : Option Expressions.Block)
    (rest : List Expressions.Stmt) (value : Expressions.Word)
    (selected : Expressions.Block)
    (hSelect :
      Expressions.EffectSemantics.Switch.select value cases defaultBody =
        some selected) :
    budget program sourceFuel selected.stmts + 2 ≤
      budget program (sourceFuel + 1)
        (.switch scrutinee cases defaultBody :: rest) := by
  have hSelected := selected_block_size_le hSelect
  have hStride := eight_le_programStride program
  rcases selected with ⟨selectedStmts⟩
  unfold budget
  simp only [stmtListSize, stmtSize, blockSize] at hSelected ⊢
  nlinarith

theorem budget_for_init_add_two_le
    (program : Expressions.Program) (sourceFuel : Nat)
    (init : Expressions.Block) (cond : Expressions.Expr 1)
    (post body : Expressions.Block) (rest : List Expressions.Stmt) :
    budget program sourceFuel init.stmts + 2 ≤
      budget program (sourceFuel + 1)
        (.for_ init cond post body :: rest) := by
  have hStride := eight_le_programStride program
  rcases init with ⟨initStmts⟩
  rcases post with ⟨postStmts⟩
  rcases body with ⟨bodyStmts⟩
  unfold budget
  simp only [stmtListSize, stmtSize, blockSize]
  nlinarith

theorem budget_for_loop_add_two_le
    (program : Expressions.Program) (sourceFuel : Nat)
    (init : Expressions.Block) (cond : Expressions.Expr 1)
    (post body : Expressions.Block) (rest : List Expressions.Stmt) :
    budget program sourceFuel [.for_ init cond post body] + 2 ≤
      budget program (sourceFuel + 1)
        (.for_ init cond post body :: rest) := by
  have hStride := eight_le_programStride program
  unfold budget
  simp only [stmtListSize, stmtSize, blockSize]
  nlinarith

theorem budget_for_post_add_one_le
    (program : Expressions.Program) (sourceFuel : Nat)
    (init : Expressions.Block) (cond : Expressions.Expr 1)
    (post body : Expressions.Block) :
    budget program sourceFuel post.stmts + 1 ≤
      budget program (sourceFuel + 1) [.for_ init cond post body] := by
  have hStride := eight_le_programStride program
  rcases init with ⟨initStmts⟩
  rcases post with ⟨postStmts⟩
  rcases body with ⟨bodyStmts⟩
  unfold budget
  simp only [stmtListSize, stmtSize, blockSize]
  nlinarith

theorem budget_for_body_add_one_le
    (program : Expressions.Program) (sourceFuel : Nat)
    (init : Expressions.Block) (cond : Expressions.Expr 1)
    (post body : Expressions.Block) :
    budget program sourceFuel body.stmts + 1 ≤
      budget program (sourceFuel + 1) [.for_ init cond post body] := by
  have hStride := eight_le_programStride program
  rcases init with ⟨initStmts⟩
  rcases post with ⟨postStmts⟩
  rcases body with ⟨bodyStmts⟩
  unfold budget
  simp only [stmtListSize, stmtSize, blockSize]
  nlinarith

theorem budget_for_loop_add_one_le
    (program : Expressions.Program) (sourceFuel : Nat)
    (init : Expressions.Block) (cond : Expressions.Expr 1)
    (post body : Expressions.Block) :
    budget program sourceFuel [.for_ init cond post body] + 1 ≤
      budget program (sourceFuel + 1) [.for_ init cond post body] := by
  have hStride := eight_le_programStride program
  unfold budget
  nlinarith

namespace Covers

theorem weaken_source {program : Expressions.Program}
    {smaller larger targetFuel : Nat} {stmts : List Expressions.Stmt}
    (h : TargetFuel.Covers program larger targetFuel stmts)
    (hLe : smaller ≤ larger) :
    TargetFuel.Covers program smaller targetFuel stmts := by
  unfold TargetFuel.Covers TargetFuel.budget at h ⊢
  have hStride := eight_le_programStride program
  nlinarith

theorem proc_body_after_three {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {callerCode : List Expressions.Stmt}
    {name : Expressions.Name} {proc : Expressions.Proc}
    (hCaller :
      TargetFuel.Covers program (sourceFuel + 1) targetFuel callerCode)
    (hLookup :
      Expressions.EffectSemantics.ProcList.lookup? name program.procs =
        some proc) :
    TargetFuel.Covers program sourceFuel (targetFuel - 3)
      proc.body.stmts := by
  have hProc :=
    proc_body_size_add_length_add_eight_le_programStride hLookup
  have hCallerSize := length_le_stmtListSize callerCode
  unfold TargetFuel.Covers TargetFuel.budget at hCaller ⊢
  have hStride := eight_le_programStride program
  have hBound :
      stmtListSize proc.body.stmts +
          programStride program * (sourceFuel + 1) + 3 ≤
        stmtListSize callerCode +
          programStride program * (sourceFuel + 1 + 1) := by
    nlinarith
  omega

theorem weaken_target {program : Expressions.Program}
    {sourceFuel smaller larger : Nat} {stmts : List Expressions.Stmt}
    (h : TargetFuel.Covers program sourceFuel smaller stmts)
    (hLe : smaller ≤ larger) :
    TargetFuel.Covers program sourceFuel larger stmts :=
  le_trans h hLe

theorem head_after_one_append {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {left right : List Expressions.Stmt}
    (hRight : right ≠ [])
    (h : TargetFuel.Covers program sourceFuel targetFuel (left ++ right)) :
    TargetFuel.Covers program sourceFuel (targetFuel - 1) left := by
  have hRightLength : 1 ≤ right.length :=
    Nat.one_le_iff_ne_zero.mpr fun hZero =>
      hRight (List.length_eq_zero_iff.mp hZero)
  have hRightSize : right.length ≤ stmtListSize right :=
    length_le_stmtListSize right
  unfold TargetFuel.Covers at h ⊢
  rw [budget_append] at h
  unfold budget at h ⊢
  omega

theorem length_lt {program : Expressions.Program} {sourceFuel targetFuel : Nat}
    {stmts : List Expressions.Stmt}
    (h : TargetFuel.Covers program sourceFuel targetFuel stmts) :
    stmts.length < targetFuel := by
  exact lt_of_lt_of_le (length_lt_budget program sourceFuel stmts) h

theorem head_of_succ_append {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {left right : List Expressions.Stmt}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      (left ++ right)) :
    TargetFuel.Covers program sourceFuel targetFuel left := by
  exact le_trans (budget_le_succ_append program sourceFuel left right) h

theorem head_of_append {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {left right : List Expressions.Stmt}
    (h : TargetFuel.Covers program sourceFuel targetFuel (left ++ right)) :
    TargetFuel.Covers program sourceFuel targetFuel left := by
  exact le_trans (budget_le_append program sourceFuel left right) h

theorem tail_after_succ_append {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {left right : List Expressions.Stmt}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      (left ++ right)) :
    TargetFuel.Covers program sourceFuel (targetFuel - left.length) right := by
  exact le_trans
    (budget_tail_le_succ_append_sub_length program sourceFuel left right)
    (Nat.sub_le_sub_right h left.length)

theorem tail_after_append {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {left right : List Expressions.Stmt}
    (h : TargetFuel.Covers program sourceFuel targetFuel (left ++ right)) :
    TargetFuel.Covers program sourceFuel (targetFuel - left.length) right := by
  exact le_trans
    (budget_tail_le_append_sub_length program sourceFuel left right)
    (Nat.sub_le_sub_right h left.length)

theorem if_body_after_two {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {cond : Expressions.Expr 1}
    {body : Expressions.Block} {rest : List Expressions.Stmt}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      (.if_ cond body :: rest)) :
    TargetFuel.Covers program sourceFuel (targetFuel - 2) body.stmts := by
  have hBody := le_trans
    (budget_if_body_add_two_le program sourceFuel cond body rest) h
  exact Nat.le_sub_of_add_le hBody

theorem switch_selected_after_two {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {scrutinee : Expressions.Expr 1}
    {cases : List (Expressions.Word × Expressions.Block)}
    {defaultBody : Option Expressions.Block}
    {rest : List Expressions.Stmt} {value : Expressions.Word}
    {selected : Expressions.Block}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      (.switch scrutinee cases defaultBody :: rest))
    (hSelect :
      Expressions.EffectSemantics.Switch.select value cases defaultBody =
        some selected) :
    TargetFuel.Covers program sourceFuel (targetFuel - 2) selected.stmts := by
  have hBody := le_trans
    (budget_switch_selected_add_two_le program sourceFuel scrutinee cases
      defaultBody rest value selected hSelect) h
  exact Nat.le_sub_of_add_le hBody

theorem for_init_after_two {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {init : Expressions.Block}
    {cond : Expressions.Expr 1} {post body : Expressions.Block}
    {rest : List Expressions.Stmt}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      (.for_ init cond post body :: rest)) :
    TargetFuel.Covers program sourceFuel (targetFuel - 2) init.stmts := by
  have hInit := le_trans
    (budget_for_init_add_two_le program sourceFuel init cond post body rest) h
  exact Nat.le_sub_of_add_le hInit

theorem for_loop_after_two {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {init : Expressions.Block}
    {cond : Expressions.Expr 1} {post body : Expressions.Block}
    {rest : List Expressions.Stmt}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      (.for_ init cond post body :: rest)) :
    TargetFuel.Covers program sourceFuel (targetFuel - 2)
      [.for_ init cond post body] := by
  have hLoop := le_trans
    (budget_for_loop_add_two_le program sourceFuel init cond post body rest) h
  exact Nat.le_sub_of_add_le hLoop

theorem for_post_after_one {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {init : Expressions.Block}
    {cond : Expressions.Expr 1} {post body : Expressions.Block}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      [.for_ init cond post body]) :
    TargetFuel.Covers program sourceFuel (targetFuel - 1) post.stmts := by
  have hPost := le_trans
    (budget_for_post_add_one_le program sourceFuel init cond post body) h
  exact Nat.le_sub_of_add_le hPost

theorem for_body_after_one {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {init : Expressions.Block}
    {cond : Expressions.Expr 1} {post body : Expressions.Block}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      [.for_ init cond post body]) :
    TargetFuel.Covers program sourceFuel (targetFuel - 1) body.stmts := by
  have hBody := le_trans
    (budget_for_body_add_one_le program sourceFuel init cond post body) h
  exact Nat.le_sub_of_add_le hBody

theorem for_loop_after_one {program : Expressions.Program}
    {sourceFuel targetFuel : Nat} {init : Expressions.Block}
    {cond : Expressions.Expr 1} {post body : Expressions.Block}
    (h : TargetFuel.Covers program (sourceFuel + 1) targetFuel
      [.for_ init cond post body]) :
    TargetFuel.Covers program sourceFuel (targetFuel - 1)
      [.for_ init cond post body] := by
  have hLoop := le_trans
    (budget_for_loop_add_one_le program sourceFuel init cond post body) h
  exact Nat.le_sub_of_add_le hLoop

end Covers

end TargetFuel
end Expressions
end EvmCompiler
