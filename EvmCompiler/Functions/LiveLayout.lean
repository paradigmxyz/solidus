import EvmCompiler.Functions.Compiler
import EvmCompiler.Functions.Semantics
import EvmCompiler.Locals.SourceLowering

namespace EvmCompiler
namespace Functions

/-!
Executable liveness and layout-window helpers for the top-16 stack-access
problem.

This module does not widen compiler acceptance by itself.  It provides checked
ingredients for the later live-layout allocator: source-shaped live-name
summaries, exact target-layout access checks, and the first dead-prefix trimming
operation that can be implemented by ordinary `POP`s.
-/

namespace LiveLayout

namespace NameSet

def insert (name : Name) (names : List Name) : List Name :=
  if name ∈ names then names else name :: names

def remove (name : Name) (names : List Name) : List Name :=
  names.filter fun other => other ≠ name

def union : List Name → List Name → List Name
  | [], right => right
  | name :: rest, right => insert name (union rest right)

def unions : List (List Name) → List Name
  | [] => []
  | names :: rest => union names (unions rest)

def allIn? (haystack needles : List Name) : Bool :=
  needles.all fun name => decide (name ∈ haystack)

@[simp] theorem mem_insert {needle name : Name} {names : List Name} :
    needle ∈ insert name names ↔ needle = name ∨ needle ∈ names := by
  unfold insert
  by_cases hName : name ∈ names
  · simp [hName]
    intro hEq
    cases hEq
    exact hName
  · simp [hName]

@[simp] theorem mem_remove {needle name : Name} {names : List Name} :
    needle ∈ remove name names ↔ needle ∈ names ∧ needle ≠ name := by
  simp [remove]

@[simp] theorem mem_union {needle : Name} :
    ∀ {left right : List Name},
      needle ∈ union left right ↔ needle ∈ left ∨ needle ∈ right
  | [], right => by
      simp [union]
  | name :: rest, right => by
      simp [union, mem_union (left := rest) (right := right), or_assoc]

@[simp] theorem mem_unions {needle : Name} :
    ∀ {sets : List (List Name)},
      needle ∈ unions sets ↔ ∃ names, names ∈ sets ∧ needle ∈ names
  | [] => by
      simp [unions]
  | names :: rest => by
      simp [unions, mem_unions (sets := rest)]

theorem allIn?_sound {haystack needles : List Name}
    (hCheck : allIn? haystack needles = true) :
    ∀ {name : Name}, name ∈ needles → name ∈ haystack := by
  intro name hName
  have hEach :=
    List.all_eq_true.mp hCheck name hName
  exact of_decide_eq_true hEach

theorem allIn?_complete {haystack needles : List Name}
    (hAll : ∀ {name : Name}, name ∈ needles → name ∈ haystack) :
    allIn? haystack needles = true := by
  unfold allIn?
  apply List.all_eq_true.mpr
  intro name hName
  exact decide_eq_true (hAll hName)

end NameSet

namespace Reads

mutual
  def expr {results : Nat} : Expr results → List Name
    | .lit _value => []
    | .var name => [name]
    | .code _code => []
    | .prim _op args => exprSeq args

  def exprSeq {results : Nat} : Locals.ExprSeq results → List Name
    | .nil => []
    | .cons head tail => NameSet.union (expr head) (exprSeq tail)
end

def exprList : List (Expr 1) → List Name
  | [] => []
  | e :: rest => NameSet.union (expr e) (exprList rest)

mutual
  def block : Block → List Name
    | ⟨stmts⟩ => stmtList stmts

  def stmt : Stmt → List Name
    | .expr e => expr e
    | .let_ _name value => expr value
    | .assign name value => NameSet.insert name (expr value)
    | .block body => block body
    | .if_ cond body => NameSet.union (expr cond) (block body)
    | .switch scrutinee cases defaultBody =>
        NameSet.union (expr scrutinee)
          (NameSet.union (caseList cases) (default defaultBody))
    | .for_ init cond post body =>
        NameSet.unions [block init, expr cond, block post, block body]
    | .brk => []
    | .cont => []
    | .leave => []
    | .call targets _functionName args =>
        NameSet.union targets (exprList args)
    | .terminal _kind => []
    | .terminalArgs _kind args => exprSeq args

  def stmtList : List Stmt → List Name
    | [] => []
    | s :: rest => NameSet.union (stmt s) (stmtList rest)

  def caseList : List (Word × Block) → List Name
    | [] => []
    | (_value, body) :: rest =>
        NameSet.union (block body) (caseList rest)

  def default : Option Block → List Name
    | none => []
    | some body => block body
end

end Reads

structure Ctx where
  returns : List Name := []
  breakLive : List Name := []
  continueLive : List Name := []
  protectedSuffixDepth : Nat := 0

namespace Ctx

def withLoop (ctx : Ctx) (breakLive continueLive : List Name) : Ctx :=
  { ctx with breakLive := breakLive, continueLive := continueLive }

def withProtectedSuffixDepth (ctx : Ctx) (depth : Nat) : Ctx :=
  { ctx with protectedSuffixDepth := max ctx.protectedSuffixDepth depth }

def withProtectedLayout (ctx : Ctx) (layout : List Name) : Ctx :=
  ctx.withProtectedSuffixDepth layout.length

def protectedDepth (ctx : Ctx) : Nat :=
  max ctx.protectedSuffixDepth (max ctx.breakLive.length ctx.continueLive.length)

end Ctx

mutual
  def Block.liveBefore (ctx : Ctx) (after : List Name) :
      Block → List Name
    | ⟨stmts⟩ => StmtList.liveBefore ctx after stmts

  def Stmt.liveBefore (ctx : Ctx) (after : List Name) :
      Stmt → List Name
    | .expr expr => NameSet.union (Reads.expr expr) after
    | .let_ name value =>
        NameSet.union (Reads.expr value) (NameSet.remove name after)
    | .assign name value =>
        NameSet.insert name (NameSet.union (Reads.expr value) after)
    | .block body => Block.liveBefore ctx after body
    | .if_ cond body =>
        NameSet.unions [Reads.expr cond, after, Block.liveBefore ctx after body]
    | .switch scrutinee cases defaultBody =>
        NameSet.unions
          [ Reads.expr scrutinee
          , after
          , CaseList.liveBefore ctx after cases
          , Default.liveBefore ctx after defaultBody ]
    | .for_ init cond post body =>
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        Block.liveBefore ctx loopLive init
    | .brk => ctx.breakLive
    | .cont => ctx.continueLive
    | .leave => ctx.returns
    | .call targets _functionName args =>
        NameSet.union (Reads.exprList args)
          (NameSet.union targets after)
    | .terminal _kind => []
    | .terminalArgs _kind args => Reads.exprSeq args

  def StmtList.liveBefore (ctx : Ctx) (after : List Name) :
      List Stmt → List Name
    | [] => after
    | stmt :: rest =>
        let restLive := StmtList.liveBefore ctx after rest
        Stmt.liveBefore ctx restLive stmt

  def CaseList.liveBefore (ctx : Ctx) (after : List Name) :
      List (Word × Block) → List Name
    | [] => []
    | (_value, body) :: rest =>
        NameSet.union (Block.liveBefore ctx after body)
          (CaseList.liveBefore ctx after rest)

  def Default.liveBefore (ctx : Ctx) (after : List Name) :
      Option Block → List Name
    | none => []
    | some body => Block.liveBefore ctx after body
end

namespace LiveBefore

theorem block_body_subset_stmt {ctx : Ctx} {after : List Name}
    {body : Block} {name : Name}
    (hMem : name ∈ Block.liveBefore ctx after body) :
    name ∈ Stmt.liveBefore ctx after (.block body) := by
  simpa [Stmt.liveBefore] using hMem

theorem if_body_subset_stmt {ctx : Ctx} {after : List Name}
    {cond : Expr 1} {body : Block} {name : Name}
    (hMem : name ∈ Block.liveBefore ctx after body) :
    name ∈ Stmt.liveBefore ctx after (.if_ cond body) := by
  simp [Stmt.liveBefore, hMem]

theorem caseList_or_default_of_select_some {ctx : Ctx} {after : List Name}
    {scrutinee : Word} {cases : List (Word × Block)}
    {defaultBody : Option Block} {body : Block} {name : Name}
    (hSelect : Switch.select scrutinee cases defaultBody = some body)
    (hMem : name ∈ Block.liveBefore ctx after body) :
    name ∈ CaseList.liveBefore ctx after cases ∨
      name ∈ Default.liveBefore ctx after defaultBody := by
  induction cases with
  | nil =>
      cases defaultBody with
      | none =>
          simp [Switch.select] at hSelect
      | some defaultBlock =>
          simp [Switch.select, Default.liveBefore] at hSelect ⊢
          cases hSelect
          exact Or.inr hMem
  | cons head rest ih =>
      rcases head with ⟨caseValue, caseBody⟩
      by_cases hEq : caseValue = scrutinee
      · simp [Switch.select, hEq] at hSelect
        cases hSelect
        left
        simp [CaseList.liveBefore, hMem]
      · simp [Switch.select, hEq] at hSelect
        rcases ih hSelect with hRest | hDefault
        · left
          simp [CaseList.liveBefore, hRest]
        · right
          exact hDefault

theorem switch_selected_body_subset_stmt {ctx : Ctx} {after : List Name}
    {switchExpr : Expr 1} {scrutinee : Word}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {body : Block} {name : Name}
    (hSelect : Switch.select scrutinee cases defaultBody = some body)
    (hMem : name ∈ Block.liveBefore ctx after body) :
    name ∈ Stmt.liveBefore ctx after (.switch switchExpr cases defaultBody) := by
  rcases caseList_or_default_of_select_some
      (ctx := ctx) (after := after) hSelect hMem with hCases | hDefault
  · simp [Stmt.liveBefore, hCases]
  · simp [Stmt.liveBefore, hDefault]

theorem let_after_of_ne {ctx : Ctx} {after : List Name}
    {declared name : Name} {value : Expr 1}
    (hAfter : name ∈ after)
    (hNe : name ≠ declared) :
    name ∈ Stmt.liveBefore ctx after (.let_ declared value) := by
  simp [Stmt.liveBefore, hAfter, hNe]

theorem let_after_of_scoped_scope {ctx : Ctx} {after env : List Name}
    {declared name : Name} {value : Expr 1}
    (hScoped : Scope.Stmt.Scoped env (.let_ declared value))
    (hScope : name ∈ env)
    (hAfter : name ∈ after) :
    name ∈ Stmt.liveBefore ctx after (.let_ declared value) := by
  have hFresh : declared ∉ env := hScoped.1
  have hNe : name ≠ declared := by
    intro hEq
    subst declared
    exact hFresh hScope
  exact let_after_of_ne (ctx := ctx) (value := value) hAfter hNe

end LiveBefore

namespace FunDef

def entryLive (fn : FunDef) : List Name :=
  Block.liveBefore { returns := fn.returns } fn.returns fn.body

end FunDef

namespace Program

def entryLive (program : Program) : List Name :=
  Block.liveBefore {} [] program.body

end Program

namespace NoInternalCall

/-!
An executable syntactic gate for the live-layout route while ordinary internal
function calls are being handled by the open-CALL proof path.  This predicate is
only about `Functions.Stmt.call`; external CALL-family primitive opcodes are
checked by the existing no-CALL/no-CREATE tower.
-/

mutual
  def Block.check? : Block → Bool
    | ⟨stmts⟩ => StmtList.check? stmts

  def Stmt.check? : Stmt → Bool
    | .block body => Block.check? body
    | .if_ _cond body => Block.check? body
    | .switch _scrutinee cases defaultBody =>
        CaseList.check? cases && Default.check? defaultBody
    | .for_ init _cond post body =>
        Block.check? init && Block.check? post && Block.check? body
    | .call _targets _functionName _args => false
    | _ => true

  def StmtList.check? : List Stmt → Bool
    | [] => true
    | stmt :: rest => Stmt.check? stmt && StmtList.check? rest

  def CaseList.check? : List (Word × Block) → Bool
    | [] => true
    | (_value, body) :: rest =>
        Block.check? body && CaseList.check? rest

  def Default.check? : Option Block → Bool
    | none => true
    | some body => Block.check? body
end

mutual
  def Block.Holds : Block → Prop
    | ⟨stmts⟩ => StmtList.Holds stmts

  def Stmt.Holds : Stmt → Prop
    | .block body => Block.Holds body
    | .if_ _cond body => Block.Holds body
    | .switch _scrutinee cases defaultBody =>
        CaseList.Holds cases ∧ Default.Holds defaultBody
    | .for_ init _cond post body =>
        Block.Holds init ∧ Block.Holds post ∧ Block.Holds body
    | .call _targets _functionName _args => False
    | _ => True

  def StmtList.Holds : List Stmt → Prop
    | [] => True
    | stmt :: rest => Stmt.Holds stmt ∧ StmtList.Holds rest

  def CaseList.Holds : List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        Block.Holds body ∧ CaseList.Holds rest

  def Default.Holds : Option Block → Prop
    | none => True
    | some body => Block.Holds body
end

def FunDef.check? (fn : FunDef) : Bool :=
  Block.check? fn.body

def FunDef.Holds (fn : FunDef) : Prop :=
  Block.Holds fn.body

def FunList.check? : List FunDef → Bool
  | [] => true
  | fn :: rest => FunDef.check? fn && FunList.check? rest

def FunList.Holds : List FunDef → Prop
  | [] => True
  | fn :: rest => FunDef.Holds fn ∧ FunList.Holds rest

def Program.check? (program : Program) : Bool :=
  FunList.check? program.functions && Block.check? program.body

def Program.Holds (program : Program) : Prop :=
  FunList.Holds program.functions ∧ Block.Holds program.body

mutual
  theorem Block.check?_sound {block : Block}
      (hCheck : Block.check? block = true) :
      Block.Holds block := by
    cases block with
    | mk stmts =>
        exact StmtList.check?_sound hCheck

  theorem Stmt.check?_sound {stmt : Stmt}
      (hCheck : Stmt.check? stmt = true) :
      Stmt.Holds stmt := by
    cases stmt with
    | block body =>
        exact Block.check?_sound (by simpa [Stmt.check?] using hCheck)
    | if_ cond body =>
        exact Block.check?_sound (by simpa [Stmt.check?] using hCheck)
    | switch scrutinee cases defaultBody =>
        have hAnd :
            CaseList.check? cases = true ∧
              Default.check? defaultBody = true := by
          simpa [Stmt.check?] using hCheck
        exact ⟨CaseList.check?_sound hAnd.1,
          Default.check?_sound hAnd.2⟩
    | for_ init cond post body =>
        have hParts :
            Block.check? init = true ∧ Block.check? post = true ∧
              Block.check? body = true := by
          simpa [Stmt.check?, Bool.and_assoc] using hCheck
        exact
          ⟨Block.check?_sound hParts.1,
            Block.check?_sound hParts.2.1,
            Block.check?_sound hParts.2.2⟩
    | call targets functionName args =>
        simp [Stmt.check?] at hCheck
    | expr expr =>
        trivial
    | let_ name value =>
        trivial
    | assign name value =>
        trivial
    | brk =>
        trivial
    | cont =>
        trivial
    | leave =>
        trivial
    | terminal kind =>
        trivial
    | terminalArgs kind args =>
        trivial

  theorem StmtList.check?_sound {stmts : List Stmt}
      (hCheck : StmtList.check? stmts = true) :
      StmtList.Holds stmts := by
    cases stmts with
    | nil =>
        trivial
    | cons stmt rest =>
        have hAnd :
            Stmt.check? stmt = true ∧ StmtList.check? rest = true := by
          simpa [StmtList.check?] using hCheck
        exact ⟨Stmt.check?_sound hAnd.1, StmtList.check?_sound hAnd.2⟩

  theorem CaseList.check?_sound {cases : List (Word × Block)}
      (hCheck : CaseList.check? cases = true) :
      CaseList.Holds cases := by
    cases cases with
    | nil =>
        trivial
    | cons head rest =>
        rcases head with ⟨value, body⟩
        have hAnd :
            Block.check? body = true ∧ CaseList.check? rest = true := by
          simpa [CaseList.check?] using hCheck
        exact ⟨Block.check?_sound hAnd.1, CaseList.check?_sound hAnd.2⟩

  theorem Default.check?_sound {defaultBody : Option Block}
      (hCheck : Default.check? defaultBody = true) :
      Default.Holds defaultBody := by
    cases defaultBody with
    | none =>
        trivial
    | some body =>
        exact Block.check?_sound (by simpa [Default.check?] using hCheck)
end

theorem FunDef.check?_sound {fn : FunDef}
    (hCheck : FunDef.check? fn = true) :
    FunDef.Holds fn := by
  exact Block.check?_sound (by simpa [FunDef.check?] using hCheck)

theorem FunList.check?_sound {fns : List FunDef}
    (hCheck : FunList.check? fns = true) :
    FunList.Holds fns := by
  induction fns with
  | nil =>
      trivial
  | cons fn rest ih =>
      have hAnd :
          FunDef.check? fn = true ∧ FunList.check? rest = true := by
        simpa [FunList.check?] using hCheck
      exact ⟨FunDef.check?_sound hAnd.1, ih hAnd.2⟩

theorem Program.check?_sound {program : Program}
    (hCheck : Program.check? program = true) :
    Program.Holds program := by
  have hAnd :
      FunList.check? program.functions = true ∧
        Block.check? program.body = true := by
    simpa [Program.check?] using hCheck
  exact ⟨FunList.check?_sound hAnd.1, Block.check?_sound hAnd.2⟩

theorem Block.holds_stmts {stmts : List Stmt}
    (hHolds : Block.Holds { stmts := stmts }) :
    StmtList.Holds stmts := by
  simpa [Block.Holds] using hHolds

theorem StmtList.holds_cons {stmt : Stmt} {rest : List Stmt}
    (hHolds : StmtList.Holds (stmt :: rest)) :
    Stmt.Holds stmt ∧ StmtList.Holds rest := by
  simpa [StmtList.Holds] using hHolds

theorem Block.holds_cons {stmt : Stmt} {rest : List Stmt}
    (hHolds : Block.Holds { stmts := stmt :: rest }) :
    Stmt.Holds stmt ∧ Block.Holds { stmts := rest } := by
  rcases StmtList.holds_cons (Block.holds_stmts hHolds) with
    ⟨hHead, hTail⟩
  exact ⟨hHead, by simpa [Block.Holds] using hTail⟩

theorem Stmt.holds_block {body : Block}
    (hHolds : Stmt.Holds (.block body)) :
    Block.Holds body := by
  simpa [Stmt.Holds] using hHolds

theorem Stmt.holds_if_body {cond : Expr 1} {body : Block}
    (hHolds : Stmt.Holds (.if_ cond body)) :
    Block.Holds body := by
  simpa [Stmt.Holds] using hHolds

theorem Stmt.holds_switch {scrutinee : Expr 1}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    (hHolds : Stmt.Holds (.switch scrutinee cases defaultBody)) :
    CaseList.Holds cases ∧ Default.Holds defaultBody := by
  simpa [Stmt.Holds] using hHolds

theorem Stmt.holds_for {init : Block} {cond : Expr 1}
    {post body : Block}
    (hHolds : Stmt.Holds (.for_ init cond post body)) :
    Block.Holds init ∧ Block.Holds post ∧ Block.Holds body := by
  simpa [Stmt.Holds] using hHolds

@[simp] theorem call_check?_eq_false {targets : List Name}
    {functionName : Name} {args : List (Expr 1)} :
    Stmt.check? (.call targets functionName args) = false := by
  rfl

end NoInternalCall

namespace Layout

def trimDeadPrefix : List Name → List Name → List Name
  | [], _live => []
  | name :: rest, live =>
      if name ∈ live then
        name :: rest
      else
        trimDeadPrefix rest live

def trimDeadPrefixCount : List Name → List Name → Nat
  | [], _live => 0
  | name :: rest, live =>
      if name ∈ live then
        0
      else
        trimDeadPrefixCount rest live + 1

theorem drop_trimDeadPrefixCount_eq_trimDeadPrefix :
    ∀ (layout live : List Name),
      layout.drop (trimDeadPrefixCount layout live) =
        trimDeadPrefix layout live
  | [], live => by
      simp [trimDeadPrefix, trimDeadPrefixCount]
  | name :: rest, live => by
      by_cases hLive : name ∈ live
      · simp [trimDeadPrefix, trimDeadPrefixCount, hLive]
      · simp [trimDeadPrefix, trimDeadPrefixCount, hLive,
          drop_trimDeadPrefixCount_eq_trimDeadPrefix rest live]

theorem trimDeadPrefix_nodup {layout live : List Name}
    (hNoDup : layout.Nodup) :
    (trimDeadPrefix layout live).Nodup := by
  rw [← drop_trimDeadPrefixCount_eq_trimDeadPrefix layout live]
  exact hNoDup.drop

theorem mem_trimDeadPrefix {needle : Name} :
    ∀ {layout live : List Name},
      needle ∈ trimDeadPrefix layout live → needle ∈ layout
  | [], live, hMem => by
      simpa [trimDeadPrefix] using hMem
  | name :: rest, live, hMem => by
      by_cases hLive : name ∈ live
      · simpa [trimDeadPrefix, hLive] using hMem
      · exact
          List.mem_cons_of_mem name
            (mem_trimDeadPrefix (layout := rest) (live := live)
              (by simpa [trimDeadPrefix, hLive] using hMem))

theorem trimDeadPrefix_eq_self_of_all_mem :
    ∀ {layout live : List Name},
      (∀ {name : Name}, name ∈ layout → name ∈ live) →
        trimDeadPrefix layout live = layout
  | [], live, _hAll => by
      simp [trimDeadPrefix]
  | name :: rest, live, hAll => by
      have hName : name ∈ live := hAll (by simp)
      simp [trimDeadPrefix, hName]

theorem trimDeadPrefixCount_add_length :
    ∀ (layout live : List Name),
      trimDeadPrefixCount layout live +
          (trimDeadPrefix layout live).length =
        layout.length
  | [], live => by
      simp [trimDeadPrefix, trimDeadPrefixCount]
  | name :: rest, live => by
      by_cases hLive : name ∈ live
      · simp [trimDeadPrefix, trimDeadPrefixCount, hLive]
      · have hRest := trimDeadPrefixCount_add_length rest live
        simp [trimDeadPrefix, trimDeadPrefixCount, hLive]
        omega

theorem length_sub_trimDeadPrefix_eq_count (layout live : List Name) :
    layout.length - (trimDeadPrefix layout live).length =
      trimDeadPrefixCount layout live := by
  have hCount := trimDeadPrefixCount_add_length layout live
  omega

def indexFrom? (needle : Name) : List Name → Nat → Option Nat
  | [], _offset => none
  | name :: rest, offset =>
      if name = needle then
        some offset
      else
        indexFrom? needle rest (offset + 1)

def index? (needle : Name) (layout : List Name) : Option Nat :=
  indexFrom? needle layout 0

def promoteAt (idx : Nat) (layout : List Name) : List Name :=
  match layout[idx]? with
  | none => layout
  | some name => name :: layout.take idx ++ layout.drop (idx + 1)

def promoteName? (layout : List Name) (name : Name) :
    Option (List Name × Nat) := do
  let idx ← index? name layout
  if idx ≤ 16 then
    some (promoteAt idx layout, idx)
  else
    none

def promoteNameUnbounded? (layout : List Name) (name : Name) :
    Option (List Name × Nat) := do
  let idx ← index? name layout
  some (promoteAt idx layout, idx)

def accessible? (offset : Nat) (layout : List Name) (name : Name) :
    Bool :=
  match index? name layout with
  | none => false
  | some idx => decide (offset + idx + 1 ≤ 16)

def allAccessible? (offset : Nat) (layout names : List Name) :
    Bool :=
  names.all fun name => accessible? offset layout name

def entryWindowOk? (layout live : List Name) : Bool :=
  allAccessible? 0 (trimDeadPrefix layout live) live

theorem indexFrom?_sound {needle : Name} :
    ∀ {layout : List Name} {base idx : Nat},
      indexFrom? needle layout base = some idx →
        ∃ relIdx,
          layout[relIdx]? = some needle ∧ idx = base + relIdx
  | [], base, idx, hIndex => by
      simp [indexFrom?] at hIndex
  | name :: rest, base, idx, hIndex => by
      unfold indexFrom? at hIndex
      by_cases hName : name = needle
      · simp [hName] at hIndex
        cases hIndex
        exact ⟨0, by simp [hName], by simp⟩
      · simp [hName] at hIndex
        rcases indexFrom?_sound hIndex with ⟨relIdx, hGet, hIdx⟩
        refine ⟨relIdx + 1, ?_, ?_⟩
        · simp [hGet]
        · omega

theorem index?_sound {needle : Name} {layout : List Name} {idx : Nat}
    (hIndex : index? needle layout = some idx) :
    layout[idx]? = some needle := by
  rcases indexFrom?_sound (needle := needle) hIndex with
    ⟨relIdx, hGet, hIdx⟩
  have hIdx' : idx = relIdx := by omega
  simpa [hIdx'] using hGet

theorem indexFrom?_lookupDepthFrom {needle : Name} :
    ∀ {layout : List Name} {base idx : Nat},
      indexFrom? needle layout base = some idx →
        Locals.Layout.lookupDepthFrom needle (base + 1) layout =
          some (idx + 1)
  | [], base, idx, hIndex => by
      simp [indexFrom?] at hIndex
  | name :: rest, base, idx, hIndex => by
      unfold indexFrom? at hIndex
      by_cases hName : name = needle
      · simp [hName] at hIndex
        cases hIndex
        simp [Locals.Layout.lookupDepthFrom, hName]
      · simp [hName] at hIndex
        have hTail :=
          indexFrom?_lookupDepthFrom
            (needle := needle) (layout := rest) (base := base + 1)
            hIndex
        simp [Locals.Layout.lookupDepthFrom, hName]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem index?_lookupDepth? {needle : Name} {layout : List Name}
    {idx : Nat}
    (hIndex : index? needle layout = some idx) :
    Locals.Layout.lookupDepth? needle layout = some (idx + 1) := by
  simpa [index?, Locals.Layout.lookupDepth?, Nat.add_comm] using
    indexFrom?_lookupDepthFrom (needle := needle) hIndex

theorem promoteAt_zero?_of_get {layout : List Name} {idx : Nat}
    {name : Name}
    (hGet : layout[idx]? = some name) :
    (promoteAt idx layout)[0]? = some name := by
  simp [promoteAt, hGet]

theorem promoteAt_length {layout : List Name} {idx : Nat} :
    (promoteAt idx layout).length = layout.length := by
  unfold promoteAt
  cases hGet : layout[idx]? with
  | none =>
      simp
  | some name =>
      rcases List.getElem?_eq_some_iff.mp hGet with ⟨hLt, _hValue⟩
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hLt)]
      omega

theorem mem_of_mem_promoteAt {layout : List Name} {idx : Nat}
    {needle : Name}
    (hMem : needle ∈ promoteAt idx layout) :
    needle ∈ layout := by
  unfold promoteAt at hMem
  cases hGet : layout[idx]? with
  | none =>
      simpa [hGet] using hMem
  | some name =>
      simp [hGet, List.mem_append] at hMem
      rcases hMem with hHead | hTake | hDrop
      · rw [hHead]
        exact List.mem_of_getElem? hGet
      · exact List.mem_of_mem_take hTake
      · exact List.mem_of_mem_drop hDrop

theorem perm_cons_append (name : Name) :
    ∀ (left right : List Name),
      (name :: left ++ right).Perm (left ++ name :: right)
  | [], _right => by
      simp
  | head :: left, right => by
      exact
        (List.Perm.swap head name (left ++ right)).trans
          (List.Perm.cons head (perm_cons_append name left right))

theorem promoteAt_perm {layout : List Name} {idx : Nat} :
    (promoteAt idx layout).Perm layout := by
  unfold promoteAt
  cases hGet : layout[idx]? with
  | none =>
      exact List.Perm.refl layout
  | some name =>
      have hSplit :
          layout = layout.take idx ++ name :: layout.drop (idx + 1) :=
        Locals.StackLowering.list_eq_take_getElem?_drop hGet
      have hTail :
          (layout.take idx ++ name :: layout.drop (idx + 1)).Perm layout := by
        rw [← hSplit]
      exact
        (perm_cons_append name (layout.take idx) (layout.drop (idx + 1))).trans
          hTail

theorem promoteAt_nodup {layout : List Name} {idx : Nat}
    (hNoDup : layout.Nodup) :
    (promoteAt idx layout).Nodup :=
  (List.Perm.nodup_iff promoteAt_perm).mpr hNoDup

theorem drop_promoteAt_suffix_eq {layout : List Name} {idx depth : Nat}
    {name : Name}
    (hGet : layout[idx]? = some name)
    (hIdx : idx < layout.length - depth) :
    (promoteAt idx layout).drop ((promoteAt idx layout).length - depth) =
      layout.drop (layout.length - depth) := by
  let cut := layout.length - depth
  have hIdxCut : idx + 1 ≤ cut := by
    omega
  have hTakeLen : (layout.take idx).length = idx := by
    rcases List.getElem?_eq_some_iff.mp hGet with ⟨hLt, _hValue⟩
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hLt)]
  have hPrefixLen : (name :: layout.take idx).length = idx + 1 := by
    simp [hTakeLen]
  have hPromote :
      promoteAt idx layout = name :: layout.take idx ++ layout.drop (idx + 1) := by
    simp [promoteAt, hGet]
  have hPromoteCut :
      (promoteAt idx layout).length - depth = cut := by
    simp [promoteAt_length, cut]
  calc
    (promoteAt idx layout).drop ((promoteAt idx layout).length - depth)
        = (name :: layout.take idx ++ layout.drop (idx + 1)).drop cut := by
            rw [hPromoteCut, hPromote]
    _ = (layout.drop (idx + 1)).drop (cut - (idx + 1)) := by
            rw [List.drop_append]
            simp [hPrefixLen, hIdxCut]
    _ = layout.drop cut := by
            rw [List.drop_drop]
            congr
            omega

theorem promoteName?_eq_some {layout : List Name} {name : Name}
    {promoted : List Name} {idx : Nat}
    (hPromote : promoteName? layout name = some (promoted, idx)) :
    index? name layout = some idx ∧ idx ≤ 16 ∧
      promoted = promoteAt idx layout ∧
      promoted[0]? = some name ∧ promoted.length = layout.length := by
  unfold promoteName? at hPromote
  cases hIndex : index? name layout with
  | none =>
      simp [hIndex] at hPromote
  | some foundIdx =>
      by_cases hBound : foundIdx ≤ 16
      · simp [hIndex, hBound] at hPromote
        rcases hPromote with ⟨rfl, rfl⟩
        exact
          ⟨rfl, hBound, rfl,
            promoteAt_zero?_of_get (index?_sound hIndex),
            promoteAt_length⟩
      · simp [hIndex, hBound] at hPromote

theorem promoteName?_some_of_index {layout : List Name} {name : Name}
    {idx : Nat}
    (hIndex : index? name layout = some idx)
    (hBound : idx ≤ 16) :
    promoteName? layout name = some (promoteAt idx layout, idx) := by
  simp [promoteName?, hIndex, hBound]

theorem promoteNameUnbounded?_eq_some {layout : List Name} {name : Name}
    {promoted : List Name} {idx : Nat}
    (hPromote :
      promoteNameUnbounded? layout name = some (promoted, idx)) :
    index? name layout = some idx ∧
      promoted = promoteAt idx layout ∧
      promoted[0]? = some name ∧ promoted.length = layout.length := by
  unfold promoteNameUnbounded? at hPromote
  cases hIndex : index? name layout with
  | none =>
      simp [hIndex] at hPromote
  | some foundIdx =>
      simp [hIndex] at hPromote
      rcases hPromote with ⟨rfl, rfl⟩
      exact
        ⟨rfl, rfl, promoteAt_zero?_of_get (index?_sound hIndex),
          promoteAt_length⟩

theorem promoteNameUnbounded?_some_of_index {layout : List Name}
    {name : Name} {idx : Nat}
    (hIndex : index? name layout = some idx) :
    promoteNameUnbounded? layout name = some (promoteAt idx layout, idx) := by
  simp [promoteNameUnbounded?, hIndex]

theorem promoteNameUnbounded?_mem {layout : List Name} {name : Name}
    {promoted : List Name} {idx : Nat}
    (hPromote :
      promoteNameUnbounded? layout name = some (promoted, idx)) :
    ∀ {needle : Name}, needle ∈ promoted → needle ∈ layout := by
  rcases promoteNameUnbounded?_eq_some hPromote with
    ⟨_hIndex, hPromoted, _hTop, _hLength⟩
  intro needle hMem
  rw [hPromoted] at hMem
  exact mem_of_mem_promoteAt hMem

theorem promoteNameUnbounded?_nodup {layout : List Name} {name : Name}
    {promoted : List Name} {idx : Nat}
    (hPromote :
      promoteNameUnbounded? layout name = some (promoted, idx))
    (hNoDup : layout.Nodup) :
    promoted.Nodup := by
  rcases promoteNameUnbounded?_eq_some hPromote with
    ⟨_hIndex, hPromoted, _hTop, _hLength⟩
  rw [hPromoted]
  exact promoteAt_nodup hNoDup

theorem promoteName?_mem {layout : List Name} {name : Name}
    {promoted : List Name} {idx : Nat}
    (hPromote : promoteName? layout name = some (promoted, idx)) :
    ∀ {needle : Name}, needle ∈ promoted → needle ∈ layout := by
  rcases promoteName?_eq_some hPromote with
    ⟨_hIndex, _hBound, hPromoted, _hTop, _hLength⟩
  intro needle hMem
  rw [hPromoted] at hMem
  exact mem_of_mem_promoteAt hMem

theorem promoteName?_nodup {layout : List Name} {name : Name}
    {promoted : List Name} {idx : Nat}
    (hPromote : promoteName? layout name = some (promoted, idx))
    (hNoDup : layout.Nodup) :
    promoted.Nodup := by
  rcases promoteName?_eq_some hPromote with
    ⟨_hIndex, _hBound, hPromoted, _hTop, _hLength⟩
  rw [hPromoted]
  exact promoteAt_nodup hNoDup

theorem accessible?_sound {offset : Nat} {layout : List Name}
    {name : Name}
    (hAccess : accessible? offset layout name = true) :
    ∃ idx, layout[idx]? = some name ∧ offset + idx + 1 ≤ 16 := by
  unfold accessible? at hAccess
  cases hIndex : index? name layout with
  | none =>
      simp [hIndex] at hAccess
  | some idx =>
      simp [hIndex] at hAccess
      exact
        ⟨idx, index?_sound hIndex, by simpa using hAccess⟩

theorem accessible?_complete {offset : Nat} {layout : List Name}
    {name : Name} {idx : Nat}
    (hIndex : index? name layout = some idx)
    (hBound : offset + idx + 1 ≤ 16) :
    accessible? offset layout name = true := by
  simp [accessible?, hIndex, hBound]

theorem accessible?_iff_index {offset : Nat} {layout : List Name}
    {name : Name} :
    accessible? offset layout name = true ↔
      ∃ idx, index? name layout = some idx ∧
        offset + idx + 1 ≤ 16 := by
  constructor
  · intro hAccess
    unfold accessible? at hAccess
    cases hIndex : index? name layout with
    | none =>
        simp [hIndex] at hAccess
    | some idx =>
        simp [hIndex] at hAccess
        exact ⟨idx, rfl, by omega⟩
  · intro hAccess
    rcases hAccess with ⟨idx, hIndex, hBound⟩
    exact accessible?_complete hIndex hBound

theorem allAccessible?_sound {offset : Nat} {layout names : List Name}
    (hCheck : allAccessible? offset layout names = true) :
    ∀ {name : Name}, name ∈ names →
      ∃ idx, layout[idx]? = some name ∧ offset + idx + 1 ≤ 16 := by
  intro name hName
  exact
    accessible?_sound
      ((List.all_eq_true.mp hCheck) name hName)

theorem allAccessible?_complete {offset : Nat} {layout names : List Name}
    (hAll :
      ∀ {name : Name}, name ∈ names →
        ∃ idx, index? name layout = some idx ∧
          offset + idx + 1 ≤ 16) :
    allAccessible? offset layout names = true := by
  unfold allAccessible?
  apply List.all_eq_true.mpr
  intro name hName
  rcases hAll hName with ⟨idx, hIndex, hBound⟩
  exact accessible?_complete hIndex hBound

theorem allAccessible?_iff_index {offset : Nat}
    {layout names : List Name} :
    allAccessible? offset layout names = true ↔
      ∀ {name : Name}, name ∈ names →
        ∃ idx, index? name layout = some idx ∧
          offset + idx + 1 ≤ 16 := by
  constructor
  · intro hCheck name hName
    exact
      accessible?_iff_index.mp
        ((List.all_eq_true.mp hCheck) name hName)
  · exact allAccessible?_complete

theorem entryWindowOk?_sound {layout live : List Name}
    (hCheck : entryWindowOk? layout live = true) :
    ∀ {name : Name}, name ∈ live →
      ∃ idx,
        (trimDeadPrefix layout live)[idx]? = some name ∧ idx + 1 ≤ 16 := by
  intro name hName
  simpa [entryWindowOk?] using
    allAccessible?_sound (offset := 0)
      (layout := trimDeadPrefix layout live) (names := live) hCheck hName

theorem entryWindowOk?_complete {layout live : List Name}
    (hAll :
      ∀ {name : Name}, name ∈ live →
        ∃ idx,
          index? name (trimDeadPrefix layout live) = some idx ∧
            idx + 1 ≤ 16) :
    entryWindowOk? layout live = true := by
  apply
    allAccessible?_complete (offset := 0)
      (layout := trimDeadPrefix layout live) (names := live)
  intro name hName
  rcases hAll hName with ⟨idx, hIndex, hBound⟩
  exact ⟨idx, hIndex, by simpa using hBound⟩

theorem entryWindowOk?_iff_index {layout live : List Name} :
    entryWindowOk? layout live = true ↔
      ∀ {name : Name}, name ∈ live →
        ∃ idx,
          index? name (trimDeadPrefix layout live) = some idx ∧
            idx + 1 ≤ 16 := by
  constructor
  · intro hCheck name hName
    rcases
      allAccessible?_iff_index.mp (by simpa [entryWindowOk?] using hCheck)
        hName with
      ⟨idx, hIndex, hBound⟩
    exact ⟨idx, hIndex, by simpa using hBound⟩
  · exact entryWindowOk?_complete

theorem entryWindowOk?_mem_trimDeadPrefix {layout live : List Name}
    (hCheck : entryWindowOk? layout live = true) :
    ∀ {name : Name}, name ∈ live → name ∈ trimDeadPrefix layout live := by
  intro name hName
  rcases entryWindowOk?_sound hCheck hName with ⟨_idx, hGet, _hTop⟩
  exact List.mem_of_getElem? hGet

theorem entryWindowOk?_allIn_trimDeadPrefix {layout live : List Name}
    (hCheck : entryWindowOk? layout live = true) :
    NameSet.allIn? (trimDeadPrefix layout live) live = true :=
  NameSet.allIn?_complete (entryWindowOk?_mem_trimDeadPrefix hCheck)

end Layout

namespace ExprAccess

mutual
  def expr? {results : Nat} (offset : Nat) (layout : List Name) :
      Expr results → Bool
    | .lit _value => true
    | .var name => Layout.accessible? offset layout name
    | .code _code => false
    | .prim _op args => exprSeq? offset layout args

  def exprSeq? {results : Nat} (offset : Nat) (layout : List Name) :
      Locals.ExprSeq results → Bool
    | .nil => true
    | .cons (left := left) head tail =>
        expr? offset layout head &&
          exprSeq? (offset + left) layout tail
end

mutual
  theorem expr?_sound {results : Nat} {offset : Nat}
      {layout : List Name} :
      ∀ {expr : Expr results},
        expr? offset layout expr = true →
          Locals.SourceLowering.Expr.Accessible layout offset expr := by
    intro expr hCheck
    cases expr with
    | lit value =>
        trivial
    | var name =>
        exact Layout.accessible?_sound hCheck
    | code code =>
        simp [expr?] at hCheck
    | prim op args =>
        exact exprSeq?_sound hCheck

  theorem exprSeq?_sound {results : Nat} {offset : Nat}
      {layout : List Name} :
      ∀ {exprs : Locals.ExprSeq results},
        exprSeq? offset layout exprs = true →
          Locals.SourceLowering.ExprSeq.Accessible layout offset exprs
    | .nil, hCheck => by
        trivial
    | .cons (left := left) head tail, hCheck => by
        have hAnd :
            expr? offset layout head = true ∧
              exprSeq? (offset + left) layout tail = true := by
          simpa [exprSeq?] using hCheck
        exact ⟨expr?_sound hAnd.1, exprSeq?_sound hAnd.2⟩
end

mutual
  theorem expr?_sourceOwned {results : Nat} {offset : Nat}
      {layout : List Name} :
      ∀ {expr : Expr results},
        expr? offset layout expr = true →
          Locals.Source.Expr.SourceOwned expr := by
    intro expr hCheck
    cases expr with
    | lit _value =>
        simp [Locals.Source.Expr.SourceOwned]
    | var _name =>
        simp [Locals.Source.Expr.SourceOwned]
    | code _code =>
        simp [expr?] at hCheck
    | prim _op args =>
        exact exprSeq?_sourceOwned hCheck

  theorem exprSeq?_sourceOwned {results : Nat} {offset : Nat}
      {layout : List Name} :
      ∀ {exprs : Locals.ExprSeq results},
        exprSeq? offset layout exprs = true →
          Locals.Source.ExprSeq.SourceOwned exprs
    | .nil, _hCheck => by
        simp [Locals.Source.ExprSeq.SourceOwned]
    | .cons (left := left) head tail, hCheck => by
        have hAnd :
            expr? offset layout head = true ∧
              exprSeq? (offset + left) layout tail = true := by
          simpa [exprSeq?] using hCheck
        exact ⟨expr?_sourceOwned hAnd.1, exprSeq?_sourceOwned hAnd.2⟩
end

end ExprAccess

namespace NamesAccess

def names? : Nat → List Name → List Name → Bool
  | _offset, _layout, [] => true
  | offset, layout, name :: rest =>
      Layout.accessible? offset layout name &&
        names? (offset + 1) layout rest

def Accessible (layout : List Name) (offset : Nat) :
    List Name → Prop
  | [] => True
  | name :: rest =>
      (∃ idx, layout[idx]? = some name ∧ offset + idx + 1 ≤ 16) ∧
        Accessible layout (offset + 1) rest

theorem names?_sound {layout names : List Name} {offset : Nat}
    (hCheck : names? offset layout names = true) :
    Accessible layout offset names := by
  induction names generalizing offset with
  | nil =>
      trivial
  | cons name rest ih =>
      have hAnd :
          Layout.accessible? offset layout name = true ∧
            names? (offset + 1) layout rest = true := by
        simpa [names?] using hCheck
      exact ⟨Layout.accessible?_sound hAnd.1, ih hAnd.2⟩

theorem get?_sound {layout names : List Name} {offset relIdx : Nat}
    {name : Name}
    (hAccess : Accessible layout offset names)
    (hGet : names[relIdx]? = some name) :
    ∃ idx, layout[idx]? = some name ∧ offset + relIdx + idx + 1 ≤ 16 := by
  induction names generalizing offset relIdx with
  | nil =>
      simp at hGet
  | cons head rest ih =>
      rcases hAccess with ⟨hHead, hTail⟩
      cases relIdx with
      | zero =>
          simp at hGet
          cases hGet
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hHead
      | succ relIdx =>
          simp at hGet
          rcases ih hTail hGet with ⟨idx, hIdx, hBound⟩
          refine ⟨idx, hIdx, ?_⟩
          omega

theorem names?_get?_sound {layout names : List Name} {offset relIdx : Nat}
    {name : Name}
    (hCheck : names? offset layout names = true)
    (hGet : names[relIdx]? = some name) :
    ∃ idx, layout[idx]? = some name ∧ offset + relIdx + idx + 1 ≤ 16 :=
  get?_sound (names?_sound hCheck) hGet

end NamesAccess

namespace StmtAccess

namespace CallArgs

def exprs : (args : List (Expr 1)) → Locals.ExprSeq args.length
  | [] => .nil
  | arg :: rest =>
      by
        simpa [Nat.add_comm] using
          (Locals.ExprSeq.cons (left := 1) (right := rest.length)
            arg (exprs rest))

end CallArgs

def accessible? (returns layout : List Name) :
    Stmt → Bool
  | .expr expr => ExprAccess.expr? 0 layout expr
  | .let_ _name value => ExprAccess.expr? 0 layout value
  | .assign name value =>
      ExprAccess.expr? 0 layout value &&
        Layout.accessible? 1 layout name
  | .block _body => true
  | .if_ cond _body => ExprAccess.expr? 0 layout cond
  | .switch scrutinee _cases _defaultBody =>
      ExprAccess.expr? 0 layout scrutinee
  | .for_ _init _cond _post _body => true
  | .brk => true
  | .cont => true
  | .leave => NamesAccess.names? 0 layout returns
  | .call targets _functionName args =>
      ExprAccess.exprSeq? 0 layout (CallArgs.exprs args) &&
        NamesAccess.names? 0 layout targets
  | .terminal _kind => true
  | .terminalArgs _kind args => ExprAccess.exprSeq? 0 layout args

def Accessible (returns layout : List Name) :
    Stmt → Prop
  | .expr expr =>
      Locals.SourceLowering.Expr.Accessible layout 0 expr
  | .let_ _name value =>
      Locals.SourceLowering.Expr.Accessible layout 0 value
  | .assign name value =>
      Locals.SourceLowering.Expr.Accessible layout 0 value ∧
        ∃ idx, layout[idx]? = some name ∧ idx + 2 ≤ 16
  | .block _body => True
  | .if_ cond _body =>
      Locals.SourceLowering.Expr.Accessible layout 0 cond
  | .switch scrutinee _cases _defaultBody =>
      Locals.SourceLowering.Expr.Accessible layout 0 scrutinee
  | .for_ _init _cond _post _body => True
  | .brk => True
  | .cont => True
  | .leave => NamesAccess.Accessible layout 0 returns
  | .call targets _functionName args =>
      Locals.SourceLowering.ExprSeq.Accessible layout 0
          (CallArgs.exprs args) ∧
        NamesAccess.Accessible layout 0 targets
  | .terminal _kind => True
  | .terminalArgs _kind args =>
      Locals.SourceLowering.ExprSeq.Accessible layout 0 args

theorem accessible?_sound {returns layout : List Name}
    {stmt : Stmt}
    (hCheck : accessible? returns layout stmt = true) :
    Accessible returns layout stmt := by
  cases stmt with
  | expr expr =>
      exact ExprAccess.expr?_sound (by simpa [accessible?] using hCheck)
  | let_ name value =>
      exact ExprAccess.expr?_sound (by simpa [accessible?] using hCheck)
  | assign name value =>
      have hAnd :
          ExprAccess.expr? 0 layout value = true ∧
            Layout.accessible? 1 layout name = true := by
        simpa [accessible?] using hCheck
      exact
        ⟨ExprAccess.expr?_sound hAnd.1,
          by
            rcases Layout.accessible?_sound hAnd.2 with
              ⟨idx, hIdx, hBound⟩
            exact ⟨idx, hIdx, by omega⟩⟩
  | block body =>
      simp [Accessible]
  | if_ cond body =>
      exact ExprAccess.expr?_sound (by simpa [accessible?] using hCheck)
  | switch scrutinee cases defaultBody =>
      exact ExprAccess.expr?_sound (by simpa [accessible?] using hCheck)
  | for_ init cond post body =>
      simp [Accessible]
  | brk =>
      simp [Accessible]
  | cont =>
      simp [Accessible]
  | leave =>
      exact NamesAccess.names?_sound (by simpa [accessible?] using hCheck)
  | call targets functionName args =>
      have hAnd :
          ExprAccess.exprSeq? 0 layout (CallArgs.exprs args) = true ∧
            NamesAccess.names? 0 layout targets = true := by
        simpa [accessible?] using hCheck
      exact
        ⟨ExprAccess.exprSeq?_sound hAnd.1,
          NamesAccess.names?_sound hAnd.2⟩
  | terminal kind =>
      simp [Accessible]
  | terminalArgs kind args =>
      exact ExprAccess.exprSeq?_sound (by simpa [accessible?] using hCheck)

end StmtAccess

namespace Prepare

abbrev NameReq := Nat × Name

namespace NameReq

def accessible? (layout : List Name) (req : NameReq) : Bool :=
  Layout.accessible? req.1 layout req.2

end NameReq

namespace Requirements

mutual
  def expr {results : Nat} (offset : Nat) :
      Expr results → List NameReq
    | .lit _value => []
    | .var name => [(offset, name)]
    | .code _code => []
    | .prim _op args => exprSeq offset args

  def exprSeq {results : Nat} (offset : Nat) :
      Locals.ExprSeq results → List NameReq
    | .nil => []
    | .cons (left := left) head tail =>
        expr offset head ++ exprSeq (offset + left) tail
end

def namesFrom (offset : Nat) : List Name → List NameReq
  | [] => []
  | name :: rest => (offset, name) :: namesFrom (offset + 1) rest

def live (names : List Name) : List NameReq :=
  namesFrom 0 names

def stmt (returns : List Name) : Stmt → List NameReq
  | .expr value => expr 0 value
  | .let_ _name value => expr 0 value
  | .assign name value => expr 0 value ++ [((1 : Nat), name)]
  | .block _body => []
  | .if_ cond _body => expr 0 cond
  | .switch scrutinee _cases _defaultBody => expr 0 scrutinee
  | .for_ _init _cond _post _body => []
  | .brk => []
  | .cont => []
  | .leave => namesFrom 0 returns
  | .call targets _functionName args =>
      exprSeq 0 (StmtAccess.CallArgs.exprs args) ++ namesFrom 0 targets
  | .terminal _kind => []
  | .terminalArgs _kind args => exprSeq 0 args

end Requirements

def allAccessible? (layout : List Name) (reqs : List NameReq) : Bool :=
  reqs.all fun req => NameReq.accessible? layout req

def firstBlocked? (layout : List Name) : List NameReq → Option Name
  | [] => none
  | req :: rest =>
      if NameReq.accessible? layout req then
        firstBlocked? layout rest
      else
        some req.2

def checked? (returns live layout : List Name) (stmt : Stmt) : Bool :=
  Layout.entryWindowOk? layout live &&
    StmtAccess.accessible? returns layout stmt

def requirements (returns live : List Name) (stmt : Stmt) :
    List NameReq :=
  Requirements.stmt returns stmt ++ Requirements.live live

def promoteBlocked? (layout : List Name) (reqs : List NameReq) :
    Option (Locals.Stmt × List Name) := do
  let name ← firstBlocked? layout reqs
  let (promoted, _idx) ← Layout.promoteName? layout name
  some (.promoteName name, promoted)

def promoteBlockedAboveSuffix? (protectedDepth : Nat) (layout : List Name)
    (reqs : List NameReq) : Option (Locals.Stmt × List Name) := do
  let name ← firstBlocked? layout reqs
  let (promoted, idx) ← Layout.promoteName? layout name
  if idx < layout.length - protectedDepth then
    some (.promoteName name, promoted)
  else
    none

theorem promoteBlocked?_eq_some {layout : List Name}
    {reqs : List NameReq} {promoteStmt : Locals.Stmt}
    {promoted : List Name}
    (hPromote :
      promoteBlocked? layout reqs = some (promoteStmt, promoted)) :
    ∃ name idx,
      promoteStmt = .promoteName name ∧
        Layout.promoteName? layout name = some (promoted, idx) := by
  unfold promoteBlocked? at hPromote
  cases hBlocked : firstBlocked? layout reqs with
  | none =>
      simp [hBlocked] at hPromote
  | some name =>
      cases hName : Layout.promoteName? layout name with
      | none =>
          simp [hBlocked, hName] at hPromote
      | some promotedPair =>
          rcases promotedPair with ⟨nextLayout, idx⟩
          simp [hBlocked, hName] at hPromote
          rcases hPromote with ⟨rfl, rfl⟩
          exact ⟨name, idx, rfl, hName⟩

theorem promoteBlockedAboveSuffix?_eq_some {protectedDepth : Nat}
    {layout : List Name} {reqs : List NameReq}
    {promoteStmt : Locals.Stmt} {promoted : List Name}
    (hPromote :
      promoteBlockedAboveSuffix? protectedDepth layout reqs =
        some (promoteStmt, promoted)) :
    ∃ name idx,
      promoteStmt = .promoteName name ∧
        Layout.promoteName? layout name = some (promoted, idx) ∧
        idx < layout.length - protectedDepth := by
  unfold promoteBlockedAboveSuffix? at hPromote
  cases hBlocked : firstBlocked? layout reqs with
  | none =>
      simp [hBlocked] at hPromote
  | some name =>
      cases hName : Layout.promoteName? layout name with
      | none =>
          simp [hBlocked, hName] at hPromote
      | some promotedPair =>
          rcases promotedPair with ⟨nextLayout, idx⟩
          by_cases hIdx : idx < layout.length - protectedDepth
          · simp [hBlocked, hName, hIdx] at hPromote
            rcases hPromote with ⟨rfl, rfl⟩
            exact ⟨name, idx, rfl, hName, hIdx⟩
          · simp [hBlocked, hName, hIdx] at hPromote

def loop (returns live : List Name) (stmt : Stmt)
    (reqs : List NameReq) :
    Nat → List Name → Option (List Locals.Stmt × List Name)
  | 0, layout =>
      if checked? returns live layout stmt then
        some ([], layout)
      else
        none
  | fuel + 1, layout =>
      if checked? returns live layout stmt then
        some ([], layout)
      else do
        let (promoteStmt, promoted) ← promoteBlocked? layout reqs
        let (rest, finalLayout) ← loop returns live stmt reqs fuel promoted
        some (promoteStmt :: rest, finalLayout)

def loopAboveSuffix (protectedDepth : Nat) (returns live : List Name)
    (stmt : Stmt) (reqs : List NameReq) :
    Nat → List Name → Option (List Locals.Stmt × List Name)
  | 0, layout =>
      if checked? returns live layout stmt then
        some ([], layout)
      else
        none
  | fuel + 1, layout =>
      if checked? returns live layout stmt then
        some ([], layout)
      else do
        let (promoteStmt, promoted) ←
          promoteBlockedAboveSuffix? protectedDepth layout reqs
        let (rest, finalLayout) ←
          loopAboveSuffix protectedDepth returns live stmt reqs fuel promoted
        some (promoteStmt :: rest, finalLayout)

def fuelFor (layout : List Name) (reqs : List NameReq) : Nat :=
  layout.length + reqs.length * reqs.length + 1

private def forStmt? (returns layout live : List Name) (stmt : Stmt) :
    Option (List Locals.Stmt × List Name) :=
  if checked? returns live layout stmt then
    some ([], layout)
  else
    none

def forStmtAboveSuffix? (protectedDepth : Nat) (returns layout live : List Name)
    (stmt : Stmt) : Option (List Locals.Stmt × List Name) :=
  loopAboveSuffix protectedDepth returns live stmt
    (requirements returns live stmt)
    (fuelFor layout (requirements returns live stmt)) layout

private theorem forStmt?_eq_some {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare : forStmt? returns layout live stmt = some (prep, finalLayout)) :
    checked? returns live layout stmt = true ∧ prep = [] ∧
      finalLayout = layout := by
  unfold forStmt? at hPrepare
  cases hChecked : checked? returns live layout stmt with
  | false =>
      simp [hChecked] at hPrepare
  | true =>
      simp [hChecked] at hPrepare
      rcases hPrepare with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩

theorem loop_checked {returns live : List Name} {stmt : Stmt}
    {reqs : List NameReq} :
    ∀ {fuel layout prep finalLayout},
      loop returns live stmt reqs fuel layout = some (prep, finalLayout) →
        checked? returns live finalLayout stmt = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hLoop
      unfold loop at hLoop
      cases hChecked : checked? returns live layout stmt with
      | false => simp [hChecked] at hLoop
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, rfl⟩
          exact hChecked
  | succ fuel ih =>
      intro layout prep finalLayout hLoop
      unfold loop at hLoop
      cases hChecked : checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, rfl⟩
          exact hChecked
      | false =>
          simp [hChecked] at hLoop
          cases hPromote : promoteBlocked? layout reqs with
          | none => simp [hPromote] at hLoop
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promoted⟩
              simp [hPromote] at hLoop
              cases hRest :
                  loop returns live stmt reqs fuel promoted with
              | none => simp [hRest] at hLoop
              | some restPair =>
                  rcases restPair with ⟨rest, restLayout⟩
                  simp [hRest] at hLoop
                  rcases hLoop with ⟨rfl, rfl⟩
                  exact ih hRest

theorem loopAboveSuffix_checked {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt}
    {reqs : List NameReq} :
    ∀ {fuel layout prep finalLayout},
      loopAboveSuffix protectedDepth returns live stmt reqs fuel layout =
          some (prep, finalLayout) →
        checked? returns live finalLayout stmt = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hLoop
      unfold loopAboveSuffix at hLoop
      cases hChecked : checked? returns live layout stmt with
      | false => simp [hChecked] at hLoop
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, rfl⟩
          exact hChecked
  | succ fuel ih =>
      intro layout prep finalLayout hLoop
      unfold loopAboveSuffix at hLoop
      cases hChecked : checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, rfl⟩
          exact hChecked
      | false =>
          simp [hChecked] at hLoop
          cases hPromote :
              promoteBlockedAboveSuffix? protectedDepth layout reqs with
          | none => simp [hPromote] at hLoop
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promoted⟩
              simp [hPromote] at hLoop
              cases hRest :
                  loopAboveSuffix protectedDepth returns live stmt reqs fuel
                    promoted with
              | none => simp [hRest] at hLoop
              | some restPair =>
                  rcases restPair with ⟨rest, restLayout⟩
                  simp [hRest] at hLoop
                  rcases hLoop with ⟨rfl, rfl⟩
                  exact ih hRest

theorem loopAboveSuffix_mem {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt}
    {reqs : List NameReq} :
    ∀ {fuel layout prep finalLayout},
      loopAboveSuffix protectedDepth returns live stmt reqs fuel layout =
          some (prep, finalLayout) →
        ∀ {name : Name}, name ∈ finalLayout → name ∈ layout := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hLoop name hMem
      unfold loopAboveSuffix at hLoop
      cases hChecked : checked? returns live layout stmt with
      | false => simp [hChecked] at hLoop
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, rfl⟩
          exact hMem
  | succ fuel ih =>
      intro layout prep finalLayout hLoop name hMem
      unfold loopAboveSuffix at hLoop
      cases hChecked : checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, rfl⟩
          exact hMem
      | false =>
          simp [hChecked] at hLoop
          cases hPromote :
              promoteBlockedAboveSuffix? protectedDepth layout reqs with
          | none => simp [hPromote] at hLoop
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promoted⟩
              simp [hPromote] at hLoop
              cases hRest :
                  loopAboveSuffix protectedDepth returns live stmt reqs fuel
                    promoted with
              | none => simp [hRest] at hLoop
              | some restPair =>
                  rcases restPair with ⟨rest, restLayout⟩
                  simp [hRest] at hLoop
                  rcases hLoop with ⟨rfl, rfl⟩
                  rcases promoteBlockedAboveSuffix?_eq_some hPromote with
                    ⟨_promotedName, _idx, _hStmt, hPromoteLayout, _hIdx⟩
                  exact
                    Layout.promoteName?_mem hPromoteLayout
                      (ih hRest hMem)

theorem loopAboveSuffix_nodup {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt}
    {reqs : List NameReq} :
    ∀ {fuel layout prep finalLayout},
      loopAboveSuffix protectedDepth returns live stmt reqs fuel layout =
          some (prep, finalLayout) →
        layout.Nodup →
          finalLayout.Nodup := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hLoop hNoDup
      unfold loopAboveSuffix at hLoop
      cases hChecked : checked? returns live layout stmt with
      | false => simp [hChecked] at hLoop
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, rfl⟩
          exact hNoDup
  | succ fuel ih =>
      intro layout prep finalLayout hLoop hNoDup
      unfold loopAboveSuffix at hLoop
      cases hChecked : checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, rfl⟩
          exact hNoDup
      | false =>
          simp [hChecked] at hLoop
          cases hPromote :
              promoteBlockedAboveSuffix? protectedDepth layout reqs with
          | none => simp [hPromote] at hLoop
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promoted⟩
              simp [hPromote] at hLoop
              cases hRest :
                  loopAboveSuffix protectedDepth returns live stmt reqs fuel
                    promoted with
              | none => simp [hRest] at hLoop
              | some restPair =>
                  rcases restPair with ⟨rest, restLayout⟩
                  simp [hRest] at hLoop
                  rcases hLoop with ⟨rfl, rfl⟩
                  rcases promoteBlockedAboveSuffix?_eq_some hPromote with
                    ⟨_promotedName, _idx, _hStmt, hPromoteLayout, _hIdx⟩
                  exact
                    ih hRest
                      (Layout.promoteName?_nodup hPromoteLayout hNoDup)

theorem promoteBlocked?_noCallCreate {layout : List Name}
    {reqs : List NameReq} {promoteStmt : Locals.Stmt}
    {promoted : List Name}
    (hPromote :
      promoteBlocked? layout reqs = some (promoteStmt, promoted)) :
    promoteStmt.usesCallCreate = false := by
  rcases promoteBlocked?_eq_some hPromote with
    ⟨name, _idx, hStmt, _hPromoteName⟩
  subst promoteStmt
  rfl

theorem promoteBlockedAboveSuffix?_noCallCreate {protectedDepth : Nat}
    {layout : List Name} {reqs : List NameReq}
    {promoteStmt : Locals.Stmt} {promoted : List Name}
    (hPromote :
      promoteBlockedAboveSuffix? protectedDepth layout reqs =
        some (promoteStmt, promoted)) :
    promoteStmt.usesCallCreate = false := by
  rcases promoteBlockedAboveSuffix?_eq_some hPromote with
    ⟨name, _idx, hStmt, _hPromoteName, _hProtected⟩
  subst promoteStmt
  rfl

theorem loop_noCallCreate {returns live : List Name} {stmt : Stmt}
    {reqs : List NameReq} :
    ∀ {fuel layout prep finalLayout},
      loop returns live stmt reqs fuel layout = some (prep, finalLayout) →
        Locals.StmtList.usesCallCreate prep = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hLoop
      unfold loop at hLoop
      cases hChecked : checked? returns live layout stmt with
      | false => simp [hChecked] at hLoop
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, _rfl⟩
          rfl
  | succ fuel ih =>
      intro layout prep finalLayout hLoop
      unfold loop at hLoop
      cases hChecked : checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, _rfl⟩
          rfl
      | false =>
          simp [hChecked] at hLoop
          cases hPromote : promoteBlocked? layout reqs with
          | none => simp [hPromote] at hLoop
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promoted⟩
              simp [hPromote] at hLoop
              cases hRest :
                  loop returns live stmt reqs fuel promoted with
              | none => simp [hRest] at hLoop
              | some restPair =>
                  rcases restPair with ⟨rest, restLayout⟩
                  simp [hRest] at hLoop
                  rcases hLoop with ⟨rfl, _rfl⟩
                  have hPromoteNo := promoteBlocked?_noCallCreate hPromote
                  have hRestNo := ih hRest
                  simp [Locals.StmtList.usesCallCreate, hPromoteNo, hRestNo]

theorem loopAboveSuffix_noCallCreate {protectedDepth : Nat}
    {returns live : List Name} {stmt : Stmt}
    {reqs : List NameReq} :
    ∀ {fuel layout prep finalLayout},
      loopAboveSuffix protectedDepth returns live stmt reqs fuel layout =
          some (prep, finalLayout) →
        Locals.StmtList.usesCallCreate prep = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro layout prep finalLayout hLoop
      unfold loopAboveSuffix at hLoop
      cases hChecked : checked? returns live layout stmt with
      | false => simp [hChecked] at hLoop
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, _rfl⟩
          rfl
  | succ fuel ih =>
      intro layout prep finalLayout hLoop
      unfold loopAboveSuffix at hLoop
      cases hChecked : checked? returns live layout stmt with
      | true =>
          simp [hChecked] at hLoop
          rcases hLoop with ⟨rfl, _rfl⟩
          rfl
      | false =>
          simp [hChecked] at hLoop
          cases hPromote :
              promoteBlockedAboveSuffix? protectedDepth layout reqs with
          | none => simp [hPromote] at hLoop
          | some promotedPair =>
              rcases promotedPair with ⟨promoteStmt, promoted⟩
              simp [hPromote] at hLoop
              cases hRest :
                  loopAboveSuffix protectedDepth returns live stmt reqs fuel
                    promoted with
              | none => simp [hRest] at hLoop
              | some restPair =>
                  rcases restPair with ⟨rest, restLayout⟩
                  simp [hRest] at hLoop
                  rcases hLoop with ⟨rfl, _rfl⟩
                  have hPromoteNo :=
                    promoteBlockedAboveSuffix?_noCallCreate hPromote
                  have hRestNo := ih hRest
                  simp [Locals.StmtList.usesCallCreate, hPromoteNo, hRestNo]

theorem forStmtAboveSuffix?_noCallCreate {protectedDepth : Nat}
    {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout)) :
    Locals.StmtList.usesCallCreate prep = false := by
  unfold forStmtAboveSuffix? at hPrepare
  exact
    loopAboveSuffix_noCallCreate
      (protectedDepth := protectedDepth) (returns := returns)
      (live := live) (stmt := stmt)
      (reqs := requirements returns live stmt)
      (fuel := fuelFor layout (requirements returns live stmt))
      (layout := layout) hPrepare

private theorem forStmt?_checked {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare : forStmt? returns layout live stmt = some (prep, finalLayout)) :
    Layout.entryWindowOk? finalLayout live = true ∧
      StmtAccess.accessible? returns finalLayout stmt = true := by
  rcases forStmt?_eq_some hPrepare with ⟨hChecked, _hPrep, hFinalLayout⟩
  rw [hFinalLayout]
  cases hEntry : Layout.entryWindowOk? layout live <;>
    simp [checked?, hEntry] at hChecked ⊢
  cases hAccess : StmtAccess.accessible? returns layout stmt <;>
    simp [hAccess] at hChecked ⊢

theorem forStmtAboveSuffix?_checked {protectedDepth : Nat}
    {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout)) :
    Layout.entryWindowOk? finalLayout live = true ∧
      StmtAccess.accessible? returns finalLayout stmt = true := by
  unfold forStmtAboveSuffix? at hPrepare
  have hChecked :
      checked? returns live finalLayout stmt = true :=
    loopAboveSuffix_checked
      (protectedDepth := protectedDepth) (returns := returns)
      (live := live) (stmt := stmt)
      (reqs := requirements returns live stmt)
      (fuel := fuelFor layout (requirements returns live stmt))
      (layout := layout) hPrepare
  cases hEntry : Layout.entryWindowOk? finalLayout live <;>
    simp [checked?, hEntry] at hChecked ⊢
  cases hAccess : StmtAccess.accessible? returns finalLayout stmt <;>
    simp [hAccess] at hChecked ⊢

theorem forStmtAboveSuffix?_mem {protectedDepth : Nat}
    {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout)) :
    ∀ {name : Name}, name ∈ finalLayout → name ∈ layout := by
  unfold forStmtAboveSuffix? at hPrepare
  exact
    loopAboveSuffix_mem
      (protectedDepth := protectedDepth) (returns := returns)
      (live := live) (stmt := stmt)
      (reqs := requirements returns live stmt)
      (fuel := fuelFor layout (requirements returns live stmt))
      (layout := layout) hPrepare

theorem forStmtAboveSuffix?_nodup {protectedDepth : Nat}
    {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout))
    (hNoDup : layout.Nodup) :
    finalLayout.Nodup := by
  unfold forStmtAboveSuffix? at hPrepare
  exact
    loopAboveSuffix_nodup
      (protectedDepth := protectedDepth) (returns := returns)
      (live := live) (stmt := stmt)
      (reqs := requirements returns live stmt)
      (fuel := fuelFor layout (requirements returns live stmt))
      (layout := layout) hPrepare hNoDup

private theorem forStmt?_entry {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare : forStmt? returns layout live stmt = some (prep, finalLayout)) :
    Layout.entryWindowOk? finalLayout live = true :=
  (forStmt?_checked hPrepare).1

private theorem forStmt?_access {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare : forStmt? returns layout live stmt = some (prep, finalLayout)) :
    StmtAccess.accessible? returns finalLayout stmt = true :=
  (forStmt?_checked hPrepare).2

private theorem forStmt?_accessible {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare : forStmt? returns layout live stmt = some (prep, finalLayout)) :
    StmtAccess.Accessible returns finalLayout stmt :=
  StmtAccess.accessible?_sound (forStmt?_access hPrepare)

theorem forStmtAboveSuffix?_entry {protectedDepth : Nat}
    {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout)) :
    Layout.entryWindowOk? finalLayout live = true :=
  (forStmtAboveSuffix?_checked hPrepare).1

theorem forStmtAboveSuffix?_access {protectedDepth : Nat}
    {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout)) :
    StmtAccess.accessible? returns finalLayout stmt = true :=
  (forStmtAboveSuffix?_checked hPrepare).2

theorem forStmtAboveSuffix?_accessible {protectedDepth : Nat}
    {returns layout live : List Name}
    {stmt : Stmt} {prep : List Locals.Stmt} {finalLayout : List Name}
    (hPrepare :
      forStmtAboveSuffix? protectedDepth returns layout live stmt =
        some (prep, finalLayout)) :
    StmtAccess.Accessible returns finalLayout stmt :=
  StmtAccess.accessible?_sound (forStmtAboveSuffix?_access hPrepare)

end Prepare

namespace Checked

def scopedAfter (layout after : List Name) : List Name :=
  NameSet.union after layout

theorem mem_scopedAfter_of_mem_layout {layout after : List Name}
    {name : Name} (hName : name ∈ layout) :
    name ∈ scopedAfter layout after := by
  simp [scopedAfter, hName]

def Stmt.regularOutLayout (layout : List Name) : Stmt → List Name
  | .let_ name _value => name :: layout
  | _ => layout

mutual
  def Block.check? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Block → Option (List Name)
    | ⟨stmts⟩ => StmtList.check? returns ctx layout after stmts

  def Stmt.check? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Stmt → Option (List Name)
    | .block body => do
        let bodyCtx := ctx.withProtectedLayout layout
        let _bodyLayout ←
          Block.check? returns bodyCtx layout (scopedAfter layout after) body
        some layout
    | .if_ _cond body => do
        let bodyCtx := ctx.withProtectedLayout layout
        let _bodyLayout ←
          Block.check? returns bodyCtx layout (scopedAfter layout after) body
        some layout
    | .switch _scrutinee cases defaultBody =>
        let branchCtx := ctx.withProtectedLayout layout
        if CaseList.check? returns branchCtx layout (scopedAfter layout after)
              cases &&
            Default.check? returns branchCtx layout (scopedAfter layout after)
              defaultBody then
          some layout
        else
          none
    | .for_ init cond post body => do
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        let loopLayout ← Block.check? returns initCtx layout initAfter init
        if ExprAccess.expr? 0 loopLayout cond then
          let postAfter := scopedAfter loopLayout loopMentioned
          let bodyAfter := scopedAfter loopLayout postLive
          let postCtx := ctx.withProtectedLayout loopLayout
          let bodyLoopCtx :=
            ctx.withLoop (scopedAfter loopLayout after) bodyAfter
          let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
          let _postLayout ←
            Block.check? returns postCtx loopLayout postAfter post
          let _bodyLayout ←
            Block.check? returns bodyCheckCtx loopLayout bodyAfter body
          some layout
        else
          none
    | stmt => some (Stmt.regularOutLayout layout stmt)

  def StmtList.check? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : List Stmt → Option (List Name)
    | [] =>
        if Layout.entryWindowOk? layout after then
          some (Layout.trimDeadPrefix layout after)
        else
          none
    | stmt :: rest => do
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        let (_prep, preparedLayout) ←
          Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
            stmtLive stmt
        let nextLayout ← Stmt.check? returns ctx preparedLayout restLive stmt
        StmtList.check? returns ctx nextLayout after rest

  def CaseList.check? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : List (Word × Block) → Bool
    | [] => true
    | (_value, body) :: rest =>
        (Block.check? returns ctx layout after body).isSome &&
          CaseList.check? returns ctx layout after rest

  def Default.check? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Option Block → Bool
    | none => true
    | some body => (Block.check? returns ctx layout after body).isSome
end

structure LayoutWidthCheckResult where
  outLayout : List Name
  maxWidth : Nat

mutual
  def Block.widthCheck? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Block → Option LayoutWidthCheckResult
    | ⟨stmts⟩ => StmtList.widthCheck? returns ctx layout after stmts

  def Stmt.widthCheck? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Stmt → Option LayoutWidthCheckResult
    | .block body => do
        let bodyCtx := ctx.withProtectedLayout layout
        let bodyResult ←
          Block.widthCheck? returns bodyCtx layout
            (scopedAfter layout after) body
        some
          { outLayout := layout
            maxWidth := max layout.length bodyResult.maxWidth }
    | .if_ _cond body => do
        let bodyCtx := ctx.withProtectedLayout layout
        let bodyResult ←
          Block.widthCheck? returns bodyCtx layout
            (scopedAfter layout after) body
        some
          { outLayout := layout
            maxWidth := max layout.length bodyResult.maxWidth }
    | .switch _scrutinee cases defaultBody => do
        let branchCtx := ctx.withProtectedLayout layout
        let caseWidth ←
          CaseList.widthCheck? returns branchCtx layout
            (scopedAfter layout after) cases
        let defaultWidth ←
          Default.widthCheck? returns branchCtx layout
            (scopedAfter layout after) defaultBody
        some
          { outLayout := layout
            maxWidth := max layout.length (max caseWidth defaultWidth) }
    | .for_ init cond post body => do
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        let initResult ← Block.widthCheck? returns initCtx layout initAfter init
        if ExprAccess.expr? 0 initResult.outLayout cond then
          let postAfter := scopedAfter initResult.outLayout loopMentioned
          let bodyAfter := scopedAfter initResult.outLayout postLive
          let postCtx := ctx.withProtectedLayout initResult.outLayout
          let bodyLoopCtx :=
            ctx.withLoop (scopedAfter initResult.outLayout after) bodyAfter
          let bodyCheckCtx :=
            bodyLoopCtx.withProtectedLayout initResult.outLayout
          let postResult ←
            Block.widthCheck? returns postCtx initResult.outLayout postAfter
              post
          let bodyResult ←
            Block.widthCheck? returns bodyCheckCtx initResult.outLayout
              bodyAfter body
          some
            { outLayout := layout
              maxWidth :=
                max layout.length
                  (max initResult.maxWidth
                    (max postResult.maxWidth bodyResult.maxWidth)) }
        else
          none
    | stmt =>
        let outLayout := Stmt.regularOutLayout layout stmt
        some
          { outLayout := outLayout
            maxWidth := max layout.length outLayout.length }

  def StmtList.widthCheck? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) :
      List Stmt → Option LayoutWidthCheckResult
    | [] =>
        if Layout.entryWindowOk? layout after then
          let outLayout := Layout.trimDeadPrefix layout after
          some
            { outLayout := outLayout
              maxWidth := max layout.length outLayout.length }
        else
          none
    | stmt :: rest => do
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        let (_prep, preparedLayout) ←
          Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
            stmtLive stmt
        let stmtResult ←
          Stmt.widthCheck? returns ctx preparedLayout restLive stmt
        let restResult ←
          StmtList.widthCheck? returns ctx stmtResult.outLayout after rest
        some
          { outLayout := restResult.outLayout
            maxWidth :=
              max layout.length
                (max liveLayout.length
                  (max preparedLayout.length
                    (max stmtResult.maxWidth restResult.maxWidth))) }

  def CaseList.widthCheck? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : List (Word × Block) → Option Nat
    | [] => some layout.length
    | (_value, body) :: rest => do
        let bodyResult ← Block.widthCheck? returns ctx layout after body
        let restWidth ← CaseList.widthCheck? returns ctx layout after rest
        some (max layout.length (max bodyResult.maxWidth restWidth))

  def Default.widthCheck? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Option Block → Option Nat
    | none => some layout.length
    | some body => do
        let bodyResult ← Block.widthCheck? returns ctx layout after body
        some (max layout.length bodyResult.maxWidth)
end

def FunDef.check? (fn : FunDef) : Bool :=
  match
      Block.check? fn.returns { returns := fn.returns }
        (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body with
  | none => false
  | some layout => NamesAccess.names? 0 layout fn.returns

def FunList.check? : List FunDef → Bool
  | [] => true
  | fn :: rest => FunDef.check? fn && FunList.check? rest

def Program.check? (program : Program) : Bool :=
  FunList.check? program.functions &&
    (Block.check? [] {} [] [] program.body).isSome

def FunDef.maxLiveLayoutWidth? (fn : FunDef) : Option Nat := do
  let result ←
    Block.widthCheck? fn.returns { returns := fn.returns }
      (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body
  if NamesAccess.names? 0 result.outLayout fn.returns then
    some result.maxWidth
  else
    none

def FunList.maxLiveLayoutWidth? : List FunDef → Option Nat
  | [] => some 0
  | fn :: rest => do
      let headWidth ← FunDef.maxLiveLayoutWidth? fn
      let tailWidth ← FunList.maxLiveLayoutWidth? rest
      some (max headWidth tailWidth)

def Program.maxLiveLayoutWidth? (program : Program) : Option Nat := do
  let functionWidth ← FunList.maxLiveLayoutWidth? program.functions
  let bodyResult ← Block.widthCheck? [] {} [] [] program.body
  some (max functionWidth bodyResult.maxWidth)

mutual
  theorem Block.widthCheck?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {block : Block}
      {result : LayoutWidthCheckResult}
      (hCheck :
        Block.widthCheck? returns ctx layout after block = some result) :
      Block.check? returns ctx layout after block = some result.outLayout ∧
        layout.length ≤ result.maxWidth ∧
        result.outLayout.length ≤ result.maxWidth := by
    cases block with
    | mk stmts =>
        exact StmtList.widthCheck?_sound hCheck

  theorem Stmt.widthCheck?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {stmt : Stmt}
      {result : LayoutWidthCheckResult}
      (hCheck :
        Stmt.widthCheck? returns ctx layout after stmt = some result) :
      Stmt.check? returns ctx layout after stmt = some result.outLayout ∧
        layout.length ≤ result.maxWidth ∧
        result.outLayout.length ≤ result.maxWidth := by
    cases stmt with
    | block body =>
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Block.widthCheck? returns bodyCtx layout
              (scopedAfter layout after) body with
        | none =>
            simp [Stmt.widthCheck?, bodyCtx, hBody] at hCheck
        | some bodyResult =>
            have hBodySound := Block.widthCheck?_sound hBody
            simp [Stmt.widthCheck?, bodyCtx, hBody] at hCheck
            cases hCheck
            constructor
            · simp [Stmt.check?, bodyCtx, hBodySound.1]
            · constructor <;> simp
    | if_ cond body =>
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Block.widthCheck? returns bodyCtx layout
              (scopedAfter layout after) body with
        | none =>
            simp [Stmt.widthCheck?, bodyCtx, hBody] at hCheck
        | some bodyResult =>
            have hBodySound := Block.widthCheck?_sound hBody
            simp [Stmt.widthCheck?, bodyCtx, hBody] at hCheck
            cases hCheck
            constructor
            · simp [Stmt.check?, bodyCtx, hBodySound.1]
            · constructor <;> simp
    | switch scrutinee cases defaultBody =>
        let branchCtx := ctx.withProtectedLayout layout
        cases hCases :
            CaseList.widthCheck? returns branchCtx layout
              (scopedAfter layout after) cases with
        | none =>
            simp [Stmt.widthCheck?, branchCtx, hCases] at hCheck
        | some caseWidth =>
            cases hDefault :
                Default.widthCheck? returns branchCtx layout
                  (scopedAfter layout after) defaultBody with
            | none =>
                simp [Stmt.widthCheck?, branchCtx, hCases, hDefault] at hCheck
            | some defaultWidth =>
                have hCasesSound := CaseList.widthCheck?_sound hCases
                have hDefaultSound := Default.widthCheck?_sound hDefault
                simp [Stmt.widthCheck?, branchCtx, hCases, hDefault] at hCheck
                cases hCheck
                constructor
                · simp [Stmt.check?, branchCtx, hCasesSound.1,
                    hDefaultSound.1]
                · constructor <;> simp
    | for_ init cond post body =>
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        cases hInit :
            Block.widthCheck? returns initCtx layout initAfter init with
        | none =>
            simp [Stmt.widthCheck?, loopMentioned, postLive, bodyCtx,
              bodyLive, loopLive, initAfter, initCtx, hInit] at hCheck
        | some initResult =>
            cases hCond : ExprAccess.expr? 0 initResult.outLayout cond with
            | false =>
                simp [Stmt.widthCheck?, loopMentioned, postLive, bodyCtx,
                  bodyLive, loopLive, initAfter, initCtx, hInit, hCond]
                  at hCheck
            | true =>
                let postAfter := scopedAfter initResult.outLayout loopMentioned
                let bodyAfter := scopedAfter initResult.outLayout postLive
                let postCtx := ctx.withProtectedLayout initResult.outLayout
                let bodyLoopCtx :=
                  ctx.withLoop (scopedAfter initResult.outLayout after)
                    bodyAfter
                let bodyCheckCtx :=
                  bodyLoopCtx.withProtectedLayout initResult.outLayout
                cases hPost :
                    Block.widthCheck? returns postCtx initResult.outLayout
                      postAfter post with
                | none =>
                    simp [Stmt.widthCheck?, loopMentioned, postLive, bodyCtx,
                      bodyLive, loopLive, initAfter, postAfter, bodyAfter,
                      initCtx, postCtx, bodyLoopCtx, bodyCheckCtx, hInit,
                      hCond, hPost] at hCheck
                | some postResult =>
                    cases hBody :
                        Block.widthCheck? returns bodyCheckCtx
                          initResult.outLayout bodyAfter body with
                    | none =>
                        simp [Stmt.widthCheck?, loopMentioned, postLive,
                          bodyCtx, bodyLive, loopLive, initAfter, postAfter,
                          bodyAfter, initCtx, postCtx, bodyLoopCtx,
                          bodyCheckCtx, hInit, hCond, hPost, hBody] at hCheck
                    | some bodyResult =>
                        have hInitSound := Block.widthCheck?_sound hInit
                        have hPostSound := Block.widthCheck?_sound hPost
                        have hBodySound := Block.widthCheck?_sound hBody
                        simp [Stmt.widthCheck?, loopMentioned, postLive,
                          bodyCtx, bodyLive, loopLive, initAfter, postAfter,
                          bodyAfter, initCtx, postCtx, bodyLoopCtx,
                          bodyCheckCtx, hInit, hCond, hPost, hBody] at hCheck
                        cases hCheck
                        constructor
                        · simp [Stmt.check?, loopMentioned, postLive, bodyCtx,
                            bodyLive, loopLive, initAfter, postAfter,
                            bodyAfter, initCtx, postCtx, bodyLoopCtx,
                            bodyCheckCtx, hInitSound.1, hCond, hPostSound.1,
                            hBodySound.1]
                        · constructor <;> simp
    | expr expr =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]
    | let_ name value =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]
    | assign name value =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]
    | brk =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]
    | cont =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]
    | leave =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]
    | call targets functionName args =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]
    | terminal kind =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]
    | terminalArgs kind args =>
        simp [Stmt.widthCheck?, Stmt.check?, Stmt.regularOutLayout] at hCheck
        cases hCheck
        simp [Stmt.check?, Stmt.regularOutLayout]

  theorem StmtList.widthCheck?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {stmts : List Stmt}
      {result : LayoutWidthCheckResult}
      (hCheck :
        StmtList.widthCheck? returns ctx layout after stmts = some result) :
      StmtList.check? returns ctx layout after stmts = some result.outLayout ∧
        layout.length ≤ result.maxWidth ∧
        result.outLayout.length ≤ result.maxWidth := by
    cases stmts with
    | nil =>
        cases hEntry : Layout.entryWindowOk? layout after with
        | false =>
            simp [StmtList.widthCheck?, hEntry] at hCheck
        | true =>
            simp [StmtList.widthCheck?, hEntry] at hCheck
            cases hCheck
            simp [StmtList.check?, hEntry]
    | cons stmt rest =>
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        cases hPrepare :
            Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
              stmtLive stmt with
        | none =>
            simp [StmtList.widthCheck?, restLive, stmtLive, liveLayout,
              hPrepare] at hCheck
        | some prepareResult =>
            rcases prepareResult with ⟨prep, preparedLayout⟩
            cases hStmt :
                Stmt.widthCheck? returns ctx preparedLayout restLive stmt with
            | none =>
                simp [StmtList.widthCheck?, restLive, stmtLive, liveLayout,
                  hPrepare, hStmt] at hCheck
            | some stmtResult =>
                cases hRest :
                    StmtList.widthCheck? returns ctx stmtResult.outLayout after
                      rest with
                | none =>
                    simp [StmtList.widthCheck?, restLive, stmtLive, liveLayout,
                      hPrepare, hStmt, hRest] at hCheck
                | some restResult =>
                    have hStmtSound := Stmt.widthCheck?_sound hStmt
                    have hRestSound := StmtList.widthCheck?_sound hRest
                    simp [StmtList.widthCheck?, restLive, stmtLive, liveLayout,
                      hPrepare, hStmt, hRest] at hCheck
                    cases hCheck
                    constructor
                    · simp [StmtList.check?, restLive, stmtLive, liveLayout,
                        hPrepare, hStmtSound.1, hRestSound.1]
                    · constructor
                      · simp
                      · exact
                          Nat.le_trans hRestSound.2.2 (by
                            simp)

  theorem CaseList.widthCheck?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {cases : List (Word × Block)}
      {width : Nat}
      (hCheck :
        CaseList.widthCheck? returns ctx layout after cases = some width) :
      CaseList.check? returns ctx layout after cases = true ∧
        layout.length ≤ width := by
    cases cases with
    | nil =>
        simp [CaseList.widthCheck?] at hCheck
        cases hCheck
        simp [CaseList.check?]
    | cons head rest =>
        rcases head with ⟨value, body⟩
        cases hBody :
            Block.widthCheck? returns ctx layout after body with
        | none =>
            simp [CaseList.widthCheck?, hBody] at hCheck
        | some bodyResult =>
            cases hRest :
                CaseList.widthCheck? returns ctx layout after rest with
            | none =>
                simp [CaseList.widthCheck?, hBody, hRest] at hCheck
            | some restWidth =>
                have hBodySound := Block.widthCheck?_sound hBody
                have hRestSound := CaseList.widthCheck?_sound hRest
                simp [CaseList.widthCheck?, hBody, hRest] at hCheck
                cases hCheck
                constructor
                · simp [CaseList.check?, hBodySound.1, hRestSound.1]
                · simp

  theorem Default.widthCheck?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {defaultBody : Option Block} {width : Nat}
      (hCheck :
        Default.widthCheck? returns ctx layout after defaultBody = some width) :
      Default.check? returns ctx layout after defaultBody = true ∧
        layout.length ≤ width := by
    cases defaultBody with
    | none =>
        simp [Default.widthCheck?] at hCheck
        cases hCheck
        simp [Default.check?]
    | some body =>
        cases hBody :
            Block.widthCheck? returns ctx layout after body with
        | none =>
            simp [Default.widthCheck?, hBody] at hCheck
        | some bodyResult =>
            have hBodySound := Block.widthCheck?_sound hBody
            simp [Default.widthCheck?, hBody] at hCheck
            cases hCheck
            constructor
            · simp [Default.check?, hBodySound.1]
            · simp
end

theorem FunDef.maxLiveLayoutWidth?_check? {fn : FunDef} {width : Nat}
    (hCheck : FunDef.maxLiveLayoutWidth? fn = some width) :
    FunDef.check? fn = true := by
  unfold FunDef.maxLiveLayoutWidth? at hCheck
  cases hBlock :
      Block.widthCheck? fn.returns { returns := fn.returns }
        (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body with
  | none =>
      simp [hBlock] at hCheck
  | some result =>
      cases hNames : NamesAccess.names? 0 result.outLayout fn.returns with
      | false =>
          simp [hBlock, hNames] at hCheck
      | true =>
          have hSound := Block.widthCheck?_sound hBlock
          simp [hBlock, hNames] at hCheck
          cases hCheck
          simp [FunDef.check?, hSound.1, hNames]

theorem FunList.maxLiveLayoutWidth?_check? {functions : List FunDef}
    {width : Nat}
    (hCheck : FunList.maxLiveLayoutWidth? functions = some width) :
    FunList.check? functions = true := by
  induction functions generalizing width with
  | nil =>
      simp [FunList.maxLiveLayoutWidth?] at hCheck
      simp [FunList.check?]
  | cons fn rest ih =>
      unfold FunList.maxLiveLayoutWidth? at hCheck
      cases hHead : FunDef.maxLiveLayoutWidth? fn with
      | none =>
          simp [hHead] at hCheck
      | some headWidth =>
          cases hTail : FunList.maxLiveLayoutWidth? rest with
          | none =>
              simp [hHead, hTail] at hCheck
          | some tailWidth =>
              simp [hHead, hTail] at hCheck
              cases hCheck
              simp [FunList.check?, FunDef.maxLiveLayoutWidth?_check? hHead,
                ih hTail]

theorem Program.maxLiveLayoutWidth?_check? {program : Program} {width : Nat}
    (hCheck : Program.maxLiveLayoutWidth? program = some width) :
    Program.check? program = true := by
  unfold Program.maxLiveLayoutWidth? at hCheck
  cases hFunctions : FunList.maxLiveLayoutWidth? program.functions with
  | none =>
      simp [hFunctions] at hCheck
  | some functionWidth =>
      cases hBody : Block.widthCheck? [] {} [] [] program.body with
      | none =>
          simp [hFunctions, hBody] at hCheck
      | some bodyResult =>
          have hFunctionsSound :=
            FunList.maxLiveLayoutWidth?_check? hFunctions
          have hBodySound := Block.widthCheck?_sound hBody
          simp [hFunctions, hBody] at hCheck
          cases hCheck
          simp [Program.check?, hFunctionsSound, hBodySound.1]

mutual
  def Block.Sound (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Block → List Name → Prop
    | ⟨stmts⟩, outLayout =>
        StmtList.Sound returns ctx layout after stmts outLayout

  def Stmt.Sound (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Stmt → List Name → Prop
    | .block body, outLayout =>
        outLayout = layout ∧
          ∃ bodyLayout,
            Block.Sound returns (ctx.withProtectedLayout layout) layout
              (scopedAfter layout after) body bodyLayout
    | .if_ _cond body, outLayout =>
        outLayout = layout ∧
          ∃ bodyLayout,
            Block.Sound returns (ctx.withProtectedLayout layout) layout
              (scopedAfter layout after) body bodyLayout
    | .switch _scrutinee cases defaultBody, outLayout =>
        outLayout = layout ∧
          CaseList.Sound returns (ctx.withProtectedLayout layout) layout
            (scopedAfter layout after) cases ∧
            Default.Sound returns (ctx.withProtectedLayout layout) layout
              (scopedAfter layout after) defaultBody
    | .for_ init cond post body, outLayout =>
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        outLayout = layout ∧
          ∃ loopLayout postLayout bodyLayout,
            let postAfter := scopedAfter loopLayout loopMentioned
            let bodyAfter := scopedAfter loopLayout postLive
            let postCtx := ctx.withProtectedLayout loopLayout
            let bodyLoopCtx :=
              ctx.withLoop (scopedAfter loopLayout after) bodyAfter
            let bodyCheckCtx :=
              bodyLoopCtx.withProtectedLayout loopLayout
            Block.Sound returns (ctx.withProtectedLayout layout) layout
              initAfter init loopLayout ∧
              Locals.SourceLowering.Expr.Accessible loopLayout 0 cond ∧
              Block.Sound returns postCtx loopLayout postAfter post
                postLayout ∧
              Block.Sound returns bodyCheckCtx loopLayout bodyAfter body
                bodyLayout
    | stmt, outLayout =>
        outLayout = Stmt.regularOutLayout layout stmt

  def StmtList.Sound (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : List Stmt → List Name → Prop
    | [], outLayout =>
        outLayout = Layout.trimDeadPrefix layout after ∧
          (∀ {name : Name}, name ∈ after →
            ∃ idx,
              (Layout.trimDeadPrefix layout after)[idx]? = some name ∧
                idx + 1 ≤ 16)
    | stmt :: rest, outLayout =>
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        ∃ prep preparedLayout nextLayout,
          Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
            stmtLive stmt =
              some (prep, preparedLayout) ∧
            (∀ {name : Name}, name ∈ stmtLive →
              ∃ idx,
                (Layout.trimDeadPrefix preparedLayout stmtLive)[idx]? =
                    some name ∧
                  idx + 1 ≤ 16) ∧
            StmtAccess.Accessible returns preparedLayout stmt ∧
            Stmt.Sound returns ctx preparedLayout restLive stmt nextLayout ∧
            StmtList.Sound returns ctx nextLayout after rest outLayout

  def CaseList.Sound (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : List (Word × Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        (∃ bodyLayout, Block.Sound returns ctx layout after body bodyLayout) ∧
          CaseList.Sound returns ctx layout after rest

  def Default.Sound (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Option Block → Prop
    | none => True
    | some body =>
        ∃ bodyLayout, Block.Sound returns ctx layout after body bodyLayout
end

mutual
  def Block.LayoutsBoundedBy (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Block → List Name → Nat → Prop
    | ⟨stmts⟩, outLayout, width =>
        StmtList.LayoutsBoundedBy returns ctx layout after stmts outLayout
          width

  def Stmt.LayoutsBoundedBy (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Stmt → List Name → Nat → Prop
    | .block body, outLayout, width =>
        layout.length ≤ width ∧ outLayout.length ≤ width ∧
          outLayout = layout ∧
          ∃ bodyLayout,
            Block.LayoutsBoundedBy returns (ctx.withProtectedLayout layout)
              layout (scopedAfter layout after) body bodyLayout width
    | .if_ _cond body, outLayout, width =>
        layout.length ≤ width ∧ outLayout.length ≤ width ∧
          outLayout = layout ∧
          ∃ bodyLayout,
            Block.LayoutsBoundedBy returns (ctx.withProtectedLayout layout)
              layout (scopedAfter layout after) body bodyLayout width
    | .switch _scrutinee cases defaultBody, outLayout, width =>
        layout.length ≤ width ∧ outLayout.length ≤ width ∧
          outLayout = layout ∧
          CaseList.LayoutsBoundedBy returns (ctx.withProtectedLayout layout)
            layout (scopedAfter layout after) cases width ∧
          Default.LayoutsBoundedBy returns (ctx.withProtectedLayout layout)
            layout (scopedAfter layout after) defaultBody width
    | .for_ init cond post body, outLayout, width =>
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        layout.length ≤ width ∧ outLayout.length ≤ width ∧
          outLayout = layout ∧
          ∃ loopLayout postLayout bodyLayout,
            let postAfter := scopedAfter loopLayout loopMentioned
            let bodyAfter := scopedAfter loopLayout postLive
            let postCtx := ctx.withProtectedLayout loopLayout
            let bodyLoopCtx :=
              ctx.withLoop (scopedAfter loopLayout after) bodyAfter
            let bodyCheckCtx :=
              bodyLoopCtx.withProtectedLayout loopLayout
            Block.LayoutsBoundedBy returns (ctx.withProtectedLayout layout)
              layout initAfter init loopLayout width ∧
            Block.LayoutsBoundedBy returns postCtx loopLayout postAfter post
              postLayout width ∧
            Block.LayoutsBoundedBy returns bodyCheckCtx loopLayout bodyAfter
              body bodyLayout width
    | stmt, outLayout, width =>
        layout.length ≤ width ∧ outLayout.length ≤ width ∧
          outLayout = Stmt.regularOutLayout layout stmt

  def StmtList.LayoutsBoundedBy (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : List Stmt → List Name → Nat → Prop
    | [], outLayout, width =>
        layout.length ≤ width ∧ outLayout.length ≤ width ∧
          outLayout = Layout.trimDeadPrefix layout after
    | stmt :: rest, outLayout, width =>
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        layout.length ≤ width ∧ liveLayout.length ≤ width ∧
          ∃ prep preparedLayout nextLayout,
            Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
              stmtLive stmt =
              some (prep, preparedLayout) ∧
            preparedLayout.length ≤ width ∧
            Stmt.LayoutsBoundedBy returns ctx preparedLayout restLive stmt
              nextLayout width ∧
            StmtList.LayoutsBoundedBy returns ctx nextLayout after rest
              outLayout width

  def CaseList.LayoutsBoundedBy (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : List (Word × Block) → Nat → Prop
    | [], width => layout.length ≤ width
    | (_value, body) :: rest, width =>
        layout.length ≤ width ∧
          (∃ bodyLayout,
            Block.LayoutsBoundedBy returns ctx layout after body bodyLayout
              width) ∧
          CaseList.LayoutsBoundedBy returns ctx layout after rest width

  def Default.LayoutsBoundedBy (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Option Block → Nat → Prop
    | none, width => layout.length ≤ width
    | some body, width =>
        layout.length ≤ width ∧
          ∃ bodyLayout,
            Block.LayoutsBoundedBy returns ctx layout after body bodyLayout
              width
  end

theorem StmtList.layoutsBoundedBy_layout_length_le
    {returns : List Name} {ctx : Ctx} {layout after : List Name}
    {stmts : List Stmt} {outLayout : List Name} {width : Nat}
    (hBound :
      StmtList.LayoutsBoundedBy returns ctx layout after stmts outLayout
        width) :
    layout.length ≤ width := by
  cases stmts <;>
    simpa [StmtList.LayoutsBoundedBy] using hBound.1

theorem Block.layoutsBoundedBy_layout_length_le
    {returns : List Name} {ctx : Ctx} {layout after : List Name}
    {block : Block} {outLayout : List Name} {width : Nat}
    (hBound :
      Block.LayoutsBoundedBy returns ctx layout after block outLayout
        width) :
    layout.length ≤ width := by
  cases block with
  | mk stmts =>
      exact
        StmtList.layoutsBoundedBy_layout_length_le
          (stmts := stmts) hBound

theorem Stmt.layoutsBoundedBy_layout_length_le
    {returns : List Name} {ctx : Ctx} {layout after : List Name}
    {stmt : Stmt} {outLayout : List Name} {width : Nat}
    (hBound :
      Stmt.LayoutsBoundedBy returns ctx layout after stmt outLayout width) :
    layout.length ≤ width := by
  cases stmt <;>
    simp [Stmt.LayoutsBoundedBy] at hBound ⊢ <;>
    exact hBound.1

theorem CaseList.layoutsBoundedBy_layout_length_le
    {returns : List Name} {ctx : Ctx} {layout after : List Name}
    {cases : List (Word × Block)} {width : Nat}
    (hBound : CaseList.LayoutsBoundedBy returns ctx layout after cases width) :
    layout.length ≤ width := by
  cases cases with
  | nil =>
      simpa [CaseList.LayoutsBoundedBy] using hBound
  | cons head rest =>
      simpa [CaseList.LayoutsBoundedBy] using hBound.1

theorem Default.layoutsBoundedBy_layout_length_le
    {returns : List Name} {ctx : Ctx} {layout after : List Name}
    {defaultBody : Option Block} {width : Nat}
    (hBound :
      Default.LayoutsBoundedBy returns ctx layout after defaultBody width) :
    layout.length ≤ width := by
  cases defaultBody with
  | none =>
      simpa [Default.LayoutsBoundedBy] using hBound
  | some body =>
      simpa [Default.LayoutsBoundedBy] using hBound.1

  mutual
    def Block.syntaxSize : Block → Nat
      | ⟨stmts⟩ => StmtList.syntaxSize stmts + 1

    def Stmt.syntaxSize : Stmt → Nat
      | .block body => Block.syntaxSize body + 1
      | .if_ _cond body => Block.syntaxSize body + 1
      | .switch _scrutinee cases defaultBody =>
          CaseList.syntaxSize cases + Default.syntaxSize defaultBody + 1
      | .for_ init _cond post body =>
          Block.syntaxSize init + Block.syntaxSize post +
            Block.syntaxSize body + 1
      | _stmt => 1

    def StmtList.syntaxSize : List Stmt → Nat
      | [] => 0
      | stmt :: rest => Stmt.syntaxSize stmt + StmtList.syntaxSize rest + 1

    def CaseList.syntaxSize : List (Word × Block) → Nat
      | [] => 0
      | (_value, body) :: rest =>
          Block.syntaxSize body + CaseList.syntaxSize rest + 1

    def Default.syntaxSize : Option Block → Nat
      | none => 0
      | some body => Block.syntaxSize body + 1
  end

  set_option maxHeartbeats 800000
  mutual
  theorem Block.widthCheck?_layoutsBoundedBy {returns : List Name} :
      ∀ {ctx : Ctx} {layout after : List Name} {block : Block}
        {result : LayoutWidthCheckResult} {width : Nat},
        Block.widthCheck? returns ctx layout after block = some result →
        result.maxWidth ≤ width →
        Block.LayoutsBoundedBy returns ctx layout after block result.outLayout
          width
    | ctx, layout, after, ⟨stmts⟩, result, width, hCheck, hWidth =>
        StmtList.widthCheck?_layoutsBoundedBy hCheck hWidth
    termination_by ctx layout after block result width hCheck hWidth =>
      Block.syntaxSize block
    decreasing_by
      all_goals simp_wf
      all_goals try simp [Block.syntaxSize, Stmt.syntaxSize,
        StmtList.syntaxSize, CaseList.syntaxSize, Default.syntaxSize]
      all_goals omega

    theorem Stmt.widthCheck?_layoutsBoundedBy {returns : List Name} :
      ∀ {ctx : Ctx} {layout after : List Name} {stmt : Stmt}
        {result : LayoutWidthCheckResult} {width : Nat},
        Stmt.widthCheck? returns ctx layout after stmt = some result →
        result.maxWidth ≤ width →
        Stmt.LayoutsBoundedBy returns ctx layout after stmt result.outLayout
          width
    | ctx, layout, after, .block body, result, width, hCheck, hWidth => by
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Block.widthCheck? returns bodyCtx layout
              (scopedAfter layout after) body with
        | none =>
            simp [Stmt.widthCheck?, bodyCtx, hBody] at hCheck
        | some bodyResult =>
            simp [Stmt.widthCheck?, bodyCtx, hBody] at hCheck
            cases hCheck
            have hLayout : layout.length ≤ width :=
              Nat.le_trans (Nat.le_max_left _ _) hWidth
            have hBodyWidth : bodyResult.maxWidth ≤ width :=
              Nat.le_trans (Nat.le_max_right _ _) hWidth
            exact
              ⟨hLayout, hLayout, rfl,
                ⟨bodyResult.outLayout,
                  Block.widthCheck?_layoutsBoundedBy hBody hBodyWidth⟩⟩
    | ctx, layout, after, .if_ cond body, result, width, hCheck, hWidth => by
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Block.widthCheck? returns bodyCtx layout
              (scopedAfter layout after) body with
        | none =>
            simp [Stmt.widthCheck?, bodyCtx, hBody] at hCheck
        | some bodyResult =>
            simp [Stmt.widthCheck?, bodyCtx, hBody] at hCheck
            cases hCheck
            have hLayout : layout.length ≤ width :=
              Nat.le_trans (Nat.le_max_left _ _) hWidth
            have hBodyWidth : bodyResult.maxWidth ≤ width :=
              Nat.le_trans (Nat.le_max_right _ _) hWidth
            exact
              ⟨hLayout, hLayout, rfl,
                ⟨bodyResult.outLayout,
                  Block.widthCheck?_layoutsBoundedBy hBody hBodyWidth⟩⟩
    | ctx, layout, after, .switch scrutinee cases defaultBody, result, width,
        hCheck, hWidth => by
        let branchCtx := ctx.withProtectedLayout layout
        cases hCases :
            CaseList.widthCheck? returns branchCtx layout
              (scopedAfter layout after) cases with
        | none =>
            simp [Stmt.widthCheck?, branchCtx, hCases] at hCheck
        | some caseWidth =>
            cases hDefault :
                Default.widthCheck? returns branchCtx layout
                  (scopedAfter layout after) defaultBody with
            | none =>
                simp [Stmt.widthCheck?, branchCtx, hCases, hDefault] at hCheck
            | some defaultWidth =>
                simp [Stmt.widthCheck?, branchCtx, hCases, hDefault] at hCheck
                cases hCheck
                have hLayout : layout.length ≤ width :=
                  Nat.le_trans (Nat.le_max_left _ _) hWidth
                have hCaseWidth : caseWidth ≤ width :=
                  Nat.le_trans
                    (Nat.le_trans (Nat.le_max_left _ _)
                      (Nat.le_max_right layout.length
                        (max caseWidth defaultWidth)))
                    hWidth
                have hDefaultWidth : defaultWidth ≤ width :=
                  Nat.le_trans
                    (Nat.le_trans (Nat.le_max_right _ _)
                      (Nat.le_max_right layout.length
                        (max caseWidth defaultWidth)))
                    hWidth
                exact
                  ⟨hLayout, hLayout, rfl,
                    CaseList.widthCheck?_layoutsBoundedBy hCases hCaseWidth,
                    Default.widthCheck?_layoutsBoundedBy hDefault
                      hDefaultWidth⟩
    | ctx, layout, after, .for_ init cond post body, result, width, hCheck,
        hWidth => by
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        cases hInit :
            Block.widthCheck? returns initCtx layout initAfter init with
        | none =>
            simp [Stmt.widthCheck?, loopMentioned, postLive, bodyCtx,
              bodyLive, loopLive, initAfter, initCtx, hInit] at hCheck
        | some initResult =>
            cases hCond : ExprAccess.expr? 0 initResult.outLayout cond with
            | false =>
                simp [Stmt.widthCheck?, loopMentioned, postLive, bodyCtx,
                  bodyLive, loopLive, initAfter, initCtx, hInit, hCond]
                  at hCheck
            | true =>
                let postAfter := scopedAfter initResult.outLayout loopMentioned
                let bodyAfter := scopedAfter initResult.outLayout postLive
                let postCtx := ctx.withProtectedLayout initResult.outLayout
                let bodyLoopCtx :=
                  ctx.withLoop (scopedAfter initResult.outLayout after)
                    bodyAfter
                let bodyCheckCtx :=
                  bodyLoopCtx.withProtectedLayout initResult.outLayout
                cases hPost :
                    Block.widthCheck? returns postCtx initResult.outLayout
                      postAfter post with
                | none =>
                    simp [Stmt.widthCheck?, loopMentioned, postLive, bodyCtx,
                      bodyLive, loopLive, initAfter, postAfter, bodyAfter,
                      initCtx, postCtx, bodyLoopCtx, bodyCheckCtx, hInit,
                      hCond, hPost] at hCheck
                | some postResult =>
                    cases hBody :
                        Block.widthCheck? returns bodyCheckCtx
                          initResult.outLayout bodyAfter body with
                    | none =>
                        simp [Stmt.widthCheck?, loopMentioned, postLive,
                          bodyCtx, bodyLive, loopLive, initAfter, postAfter,
                          bodyAfter, initCtx, postCtx, bodyLoopCtx,
                          bodyCheckCtx, hInit, hCond, hPost, hBody] at hCheck
                    | some bodyResult =>
                        simp [Stmt.widthCheck?, loopMentioned, postLive,
                          bodyCtx, bodyLive, loopLive, initAfter, postAfter,
                          bodyAfter, initCtx, postCtx, bodyLoopCtx,
                          bodyCheckCtx, hInit, hCond, hPost, hBody] at hCheck
                        cases hCheck
                        have hLayout : layout.length ≤ width :=
                          Nat.le_trans (Nat.le_max_left _ _) hWidth
                        have hInitWidth : initResult.maxWidth ≤ width :=
                          Nat.le_trans
                            (Nat.le_trans (Nat.le_max_left _ _)
                              (Nat.le_max_right layout.length
                                (max initResult.maxWidth
                                  (max postResult.maxWidth
                                    bodyResult.maxWidth))))
                            hWidth
                        have hPostWidth : postResult.maxWidth ≤ width :=
                          Nat.le_trans
                            (Nat.le_trans
                              (Nat.le_trans (Nat.le_max_left _ _)
                                (Nat.le_max_right initResult.maxWidth
                                  (max postResult.maxWidth
                                    bodyResult.maxWidth)))
                              (Nat.le_max_right layout.length
                                (max initResult.maxWidth
                                  (max postResult.maxWidth
                                    bodyResult.maxWidth))))
                            hWidth
                        have hBodyWidth : bodyResult.maxWidth ≤ width :=
                          Nat.le_trans
                            (Nat.le_trans
                              (Nat.le_trans (Nat.le_max_right _ _)
                                (Nat.le_max_right initResult.maxWidth
                                  (max postResult.maxWidth
                                    bodyResult.maxWidth)))
                              (Nat.le_max_right layout.length
                                (max initResult.maxWidth
                                  (max postResult.maxWidth
                                    bodyResult.maxWidth))))
                            hWidth
                        exact
                          ⟨hLayout, hLayout, rfl, initResult.outLayout,
                            postResult.outLayout, bodyResult.outLayout,
                            Block.widthCheck?_layoutsBoundedBy hInit
                              hInitWidth,
                            Block.widthCheck?_layoutsBoundedBy hPost
                              hPostWidth,
                            Block.widthCheck?_layoutsBoundedBy hBody
                              hBodyWidth⟩
    | ctx, layout, after, .expr expr, result, width, hCheck, hWidth => by
        simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
          Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact
          ⟨by simpa using hWidth, by simpa using hWidth, rfl⟩
    | ctx, layout, after, .let_ name value, result, width, hCheck, hWidth => by
        simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
          Stmt.regularOutLayout] at hCheck
        cases hCheck
        have hOut : (name :: layout).length ≤ width := by
          simpa using hWidth
        have hIn : layout.length ≤ width :=
          Nat.le_trans (Nat.le_succ layout.length) hOut
        exact ⟨hIn, hOut, rfl⟩
    | ctx, layout, after, .assign name value, result, width, hCheck,
        hWidth => by
        simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
          Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact
          ⟨by simpa using hWidth, by simpa using hWidth, rfl⟩
    | ctx, layout, after, .brk, result, width, hCheck, hWidth => by
        simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
          Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact
          ⟨by simpa using hWidth, by simpa using hWidth, rfl⟩
    | ctx, layout, after, .cont, result, width, hCheck, hWidth => by
        simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
          Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact
          ⟨by simpa using hWidth, by simpa using hWidth, rfl⟩
    | ctx, layout, after, .leave, result, width, hCheck, hWidth => by
        simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
          Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact
          ⟨by simpa using hWidth, by simpa using hWidth, rfl⟩
    | ctx, layout, after, .call targets functionName args, result, width,
        hCheck, hWidth => by
        simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
          Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact
          ⟨by simpa using hWidth, by simpa using hWidth, rfl⟩
    | ctx, layout, after, .terminal kind, result, width, hCheck, hWidth => by
        simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
          Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact
          ⟨by simpa using hWidth, by simpa using hWidth, rfl⟩
    | ctx, layout, after, .terminalArgs kind args, result, width, hCheck,
        hWidth => by
          simp [Stmt.widthCheck?, Stmt.LayoutsBoundedBy,
            Stmt.regularOutLayout] at hCheck
          cases hCheck
          exact
            ⟨by simpa using hWidth, by simpa using hWidth, rfl⟩
    termination_by ctx layout after stmt result width hCheck hWidth =>
      Stmt.syntaxSize stmt
    decreasing_by
      all_goals simp_wf
      all_goals try simp [Block.syntaxSize, Stmt.syntaxSize,
        StmtList.syntaxSize, CaseList.syntaxSize, Default.syntaxSize]
      all_goals omega

    theorem StmtList.widthCheck?_layoutsBoundedBy {returns : List Name} :
      ∀ {ctx : Ctx} {layout after : List Name} {stmts : List Stmt}
        {result : LayoutWidthCheckResult} {width : Nat},
        StmtList.widthCheck? returns ctx layout after stmts = some result →
        result.maxWidth ≤ width →
        StmtList.LayoutsBoundedBy returns ctx layout after stmts
          result.outLayout width
    | ctx, layout, after, [], result, width, hCheck, hWidth => by
        cases hEntry : Layout.entryWindowOk? layout after with
        | false =>
            simp [StmtList.widthCheck?, hEntry] at hCheck
        | true =>
            simp [StmtList.widthCheck?, hEntry] at hCheck
            cases hCheck
            exact
              ⟨Nat.le_trans (Nat.le_max_left _ _) hWidth,
                Nat.le_trans (Nat.le_max_right _ _) hWidth, rfl⟩
    | ctx, layout, after, stmt :: rest, result, width, hCheck, hWidth => by
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        cases hPrepare :
            Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
              stmtLive stmt with
        | none =>
            simp [StmtList.widthCheck?, restLive, stmtLive, liveLayout,
              hPrepare] at hCheck
        | some prepareResult =>
            rcases prepareResult with ⟨prep, preparedLayout⟩
            cases hStmt :
                Stmt.widthCheck? returns ctx preparedLayout restLive stmt with
            | none =>
                simp [StmtList.widthCheck?, restLive, stmtLive, liveLayout,
                  hPrepare, hStmt] at hCheck
            | some stmtResult =>
                cases hRest :
                    StmtList.widthCheck? returns ctx stmtResult.outLayout after
                      rest with
                | none =>
                    simp [StmtList.widthCheck?, restLive, stmtLive, liveLayout,
                      hPrepare, hStmt, hRest] at hCheck
                | some restResult =>
                    simp [StmtList.widthCheck?, restLive, stmtLive, liveLayout,
                      hPrepare, hStmt, hRest] at hCheck
                    cases hCheck
                    have hLayout : layout.length ≤ width :=
                      Nat.le_trans (Nat.le_max_left _ _) hWidth
                    have hLive : liveLayout.length ≤ width :=
                      Nat.le_trans
                        (Nat.le_trans (Nat.le_max_left _ _)
                          (Nat.le_max_right layout.length
                            (max liveLayout.length
                              (max preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth)))))
                        hWidth
                    have hPrepared : preparedLayout.length ≤ width :=
                      Nat.le_trans
                        (Nat.le_trans
                          (Nat.le_trans (Nat.le_max_left _ _)
                            (Nat.le_max_right liveLayout.length
                              (max preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth))))
                          (Nat.le_max_right layout.length
                            (max liveLayout.length
                              (max preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth)))))
                        hWidth
                    have hStmtWidth : stmtResult.maxWidth ≤ width :=
                      Nat.le_trans
                        (Nat.le_trans
                          (Nat.le_trans
                            (Nat.le_trans (Nat.le_max_left _ _)
                              (Nat.le_max_right preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth)))
                            (Nat.le_max_right liveLayout.length
                              (max preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth))))
                          (Nat.le_max_right layout.length
                            (max liveLayout.length
                              (max preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth)))))
                        hWidth
                    have hRestWidth : restResult.maxWidth ≤ width :=
                      Nat.le_trans
                        (Nat.le_trans
                          (Nat.le_trans
                            (Nat.le_trans (Nat.le_max_right _ _)
                              (Nat.le_max_right preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth)))
                            (Nat.le_max_right liveLayout.length
                              (max preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth))))
                          (Nat.le_max_right layout.length
                            (max liveLayout.length
                              (max preparedLayout.length
                                (max stmtResult.maxWidth
                                  restResult.maxWidth)))))
                        hWidth
                    exact
                      ⟨hLayout, hLive, prep, preparedLayout,
                        stmtResult.outLayout, hPrepare, hPrepared,
                        Stmt.widthCheck?_layoutsBoundedBy hStmt hStmtWidth,
                          StmtList.widthCheck?_layoutsBoundedBy
                            (returns := returns) (ctx := ctx)
                            (layout := stmtResult.outLayout)
                            (after := after) (stmts := rest)
                            (result := restResult) (width := width)
                            hRest hRestWidth⟩
    termination_by ctx layout after stmts result width hCheck hWidth =>
      StmtList.syntaxSize stmts
    decreasing_by
      all_goals simp_wf
      all_goals try simp [Block.syntaxSize, Stmt.syntaxSize,
        StmtList.syntaxSize, CaseList.syntaxSize, Default.syntaxSize]
      all_goals omega

    theorem CaseList.widthCheck?_layoutsBoundedBy {returns : List Name} :
      ∀ {ctx : Ctx} {layout after : List Name}
        {cases : List (Word × Block)} {checkedWidth width : Nat},
        CaseList.widthCheck? returns ctx layout after cases =
          some checkedWidth →
        checkedWidth ≤ width →
        CaseList.LayoutsBoundedBy returns ctx layout after cases width
    | ctx, layout, after, [], checkedWidth, width, hCheck, hWidth => by
        simp [CaseList.widthCheck?] at hCheck
        cases hCheck
        exact hWidth
    | ctx, layout, after, (value, body) :: rest, checkedWidth, width, hCheck,
        hWidth => by
        cases hBody :
            Block.widthCheck? returns ctx layout after body with
        | none =>
            simp [CaseList.widthCheck?, hBody] at hCheck
        | some bodyResult =>
            cases hRest :
                CaseList.widthCheck? returns ctx layout after rest with
            | none =>
                simp [CaseList.widthCheck?, hBody, hRest] at hCheck
              | some restWidth =>
                  simp [CaseList.widthCheck?, hBody, hRest] at hCheck
                  cases hCheck
                  have hLayout : layout.length ≤ width :=
                    Nat.le_trans (Nat.le_max_left _ _) hWidth
                  have hBodyWidth : bodyResult.maxWidth ≤ width := by
                    exact
                      Nat.le_trans
                        (Nat.le_trans (Nat.le_max_left _ _)
                          (Nat.le_max_right layout.length
                            (max bodyResult.maxWidth restWidth)))
                        hWidth
                  have hRestWidth : restWidth ≤ width := by
                    exact
                      Nat.le_trans
                        (Nat.le_trans (Nat.le_max_right _ _)
                          (Nat.le_max_right layout.length
                            (max bodyResult.maxWidth restWidth)))
                        hWidth
                  exact
                    ⟨hLayout,
                      ⟨bodyResult.outLayout,
                        Block.widthCheck?_layoutsBoundedBy hBody hBodyWidth⟩,
                      CaseList.widthCheck?_layoutsBoundedBy hRest hRestWidth⟩
    termination_by ctx layout after cases checkedWidth width hCheck hWidth =>
      CaseList.syntaxSize cases
    decreasing_by
      all_goals simp_wf
      all_goals try simp [Block.syntaxSize, Stmt.syntaxSize,
        StmtList.syntaxSize, CaseList.syntaxSize, Default.syntaxSize]
      all_goals omega

    theorem Default.widthCheck?_layoutsBoundedBy {returns : List Name} :
      ∀ {ctx : Ctx} {layout after : List Name} {defaultBody : Option Block}
        {checkedWidth width : Nat},
        Default.widthCheck? returns ctx layout after defaultBody =
          some checkedWidth →
        checkedWidth ≤ width →
        Default.LayoutsBoundedBy returns ctx layout after defaultBody width
    | ctx, layout, after, none, checkedWidth, width, hCheck, hWidth => by
        simp [Default.widthCheck?] at hCheck
        cases hCheck
        exact hWidth
    | ctx, layout, after, some body, checkedWidth, width, hCheck, hWidth => by
          cases hBody :
              Block.widthCheck? returns ctx layout after body with
          | none =>
              simp [Default.widthCheck?, hBody] at hCheck
          | some bodyResult =>
              simp [Default.widthCheck?, hBody] at hCheck
              cases hCheck
              have hLayout : layout.length ≤ width :=
                Nat.le_trans (Nat.le_max_left _ _) hWidth
              have hBodyWidth : bodyResult.maxWidth ≤ width :=
                Nat.le_trans (Nat.le_max_right _ _) hWidth
              exact
                ⟨hLayout, bodyResult.outLayout,
                  Block.widthCheck?_layoutsBoundedBy hBody hBodyWidth⟩
    termination_by ctx layout after defaultBody checkedWidth width hCheck hWidth =>
      Default.syntaxSize defaultBody
    decreasing_by
      all_goals simp_wf
      all_goals try simp [Block.syntaxSize, Stmt.syntaxSize,
        StmtList.syntaxSize, CaseList.syntaxSize, Default.syntaxSize]
      all_goals omega
  end

theorem Block.widthCheck?_layoutsBoundedBy_self {returns : List Name}
    {ctx : Ctx} {layout after : List Name} {block : Block}
    {result : LayoutWidthCheckResult}
    (hCheck :
      Block.widthCheck? returns ctx layout after block = some result) :
    Block.LayoutsBoundedBy returns ctx layout after block result.outLayout
      result.maxWidth :=
  Block.widthCheck?_layoutsBoundedBy hCheck (Nat.le_refl _)

theorem Program.maxLiveLayoutWidth?_body_layoutsBoundedBy
    {program : Program} {width : Nat}
    (hCheck : Program.maxLiveLayoutWidth? program = some width) :
    ∃ bodyResult functionWidth,
      FunList.maxLiveLayoutWidth? program.functions = some functionWidth ∧
        Block.widthCheck? [] {} [] [] program.body = some bodyResult ∧
        bodyResult.maxWidth ≤ width ∧
        Block.LayoutsBoundedBy [] {} [] [] program.body bodyResult.outLayout
          width := by
  unfold Program.maxLiveLayoutWidth? at hCheck
  cases hFunctions : FunList.maxLiveLayoutWidth? program.functions with
  | none =>
      simp [hFunctions] at hCheck
  | some functionWidth =>
      cases hBody : Block.widthCheck? [] {} [] [] program.body with
      | none =>
          simp [hFunctions, hBody] at hCheck
      | some bodyResult =>
          simp [hFunctions, hBody] at hCheck
          cases hCheck
          have hBodyWidth : bodyResult.maxWidth ≤ max functionWidth bodyResult.maxWidth :=
            Nat.le_max_right functionWidth bodyResult.maxWidth
          exact
            ⟨bodyResult, functionWidth, rfl, rfl, hBodyWidth,
              Block.widthCheck?_layoutsBoundedBy hBody hBodyWidth⟩

mutual
  theorem Block.check?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {block : Block} {outLayout : List Name}
      (hCheck :
        Block.check? returns ctx layout after block = some outLayout) :
      Block.Sound returns ctx layout after block outLayout := by
    cases block with
    | mk stmts =>
        exact StmtList.check?_sound hCheck

  theorem Stmt.check?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {stmt : Stmt} {outLayout : List Name}
      (hCheck :
        Stmt.check? returns ctx layout after stmt = some outLayout) :
      Stmt.Sound returns ctx layout after stmt outLayout := by
    cases stmt with
    | block body =>
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Block.check? returns bodyCtx layout (scopedAfter layout after) body with
        | none =>
            simp [Stmt.check?, bodyCtx, hBody] at hCheck
        | some bodyLayout =>
            simp [Stmt.check?, bodyCtx, hBody] at hCheck
            cases hCheck
            exact
              ⟨rfl, ⟨bodyLayout, Block.check?_sound hBody⟩⟩
    | if_ cond body =>
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Block.check? returns bodyCtx layout (scopedAfter layout after) body with
        | none =>
            simp [Stmt.check?, bodyCtx, hBody] at hCheck
        | some bodyLayout =>
            simp [Stmt.check?, bodyCtx, hBody] at hCheck
            cases hCheck
            exact
              ⟨rfl, ⟨bodyLayout, Block.check?_sound hBody⟩⟩
    | switch scrutinee cases defaultBody =>
        let branchCtx := ctx.withProtectedLayout layout
        cases hCases :
            CaseList.check? returns branchCtx layout (scopedAfter layout after)
              cases <;>
          cases hDefault :
              Default.check? returns branchCtx layout (scopedAfter layout after)
                defaultBody <;>
          simp [Stmt.check?, branchCtx, hCases, hDefault] at hCheck
        cases hCheck
        exact
          ⟨rfl, CaseList.check?_sound hCases,
            Default.check?_sound hDefault⟩
    | for_ init cond post body =>
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        cases hInit :
            Block.check? returns initCtx layout initAfter init with
        | none =>
            simp [Stmt.check?, loopMentioned, postLive, bodyCtx, bodyLive,
              loopLive, initAfter, initCtx, hInit] at hCheck
        | some loopLayout =>
            cases hCond : ExprAccess.expr? 0 loopLayout cond with
            | false =>
                simp [Stmt.check?, loopMentioned, postLive, bodyCtx, bodyLive,
                  loopLive, initAfter, initCtx, hInit, hCond] at hCheck
            | true =>
                let postAfter := scopedAfter loopLayout loopMentioned
                let bodyAfter := scopedAfter loopLayout postLive
                let postCtx := ctx.withProtectedLayout loopLayout
                let bodyLoopCtx :=
                  ctx.withLoop (scopedAfter loopLayout after) bodyAfter
                let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
                cases hPost :
                    Block.check? returns postCtx loopLayout postAfter post with
                | none =>
                    simp [Stmt.check?, loopMentioned, postLive, bodyCtx,
                      bodyLive, loopLive, initAfter, postAfter, bodyAfter,
                      initCtx, postCtx, bodyLoopCtx, bodyCheckCtx, hInit,
                      hCond, hPost] at hCheck
                | some postLayout =>
                    cases hBody :
                        Block.check? returns bodyCheckCtx loopLayout bodyAfter
                          body with
                    | none =>
                        simp [Stmt.check?, loopMentioned, postLive, bodyCtx,
                          bodyLive, loopLive, initAfter, postAfter, bodyAfter,
                          initCtx, postCtx, bodyLoopCtx, bodyCheckCtx, hInit,
                          hCond, hPost, hBody] at hCheck
                    | some bodyLayout =>
                        simp [Stmt.check?, loopMentioned, postLive, bodyCtx,
                          bodyLive, loopLive, initAfter, postAfter, bodyAfter,
                          initCtx, postCtx, bodyLoopCtx, bodyCheckCtx, hInit,
                          hCond, hPost, hBody] at hCheck
                        cases hCheck
                        refine ⟨rfl, loopLayout, postLayout, bodyLayout, ?_⟩
                        exact
                          ⟨Block.check?_sound hInit,
                            ExprAccess.expr?_sound hCond,
                            Block.check?_sound hPost,
                            Block.check?_sound hBody⟩
    | expr expr =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm
    | let_ name value =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm
    | assign name value =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm
    | brk =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm
    | cont =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm
    | leave =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm
    | call targets functionName args =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm
    | terminal kind =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm
    | terminalArgs kind args =>
        simp [Stmt.check?, Stmt.Sound, Stmt.regularOutLayout] at hCheck ⊢
        exact hCheck.symm

  theorem StmtList.check?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {stmts : List Stmt}
      {outLayout : List Name}
      (hCheck :
        StmtList.check? returns ctx layout after stmts =
          some outLayout) :
      StmtList.Sound returns ctx layout after stmts outLayout := by
    cases stmts with
    | nil =>
        cases hEntry : Layout.entryWindowOk? layout after with
        | false =>
            simp [StmtList.check?, hEntry] at hCheck
        | true =>
            simp [StmtList.check?, hEntry] at hCheck
            cases hCheck
            exact
              ⟨rfl, Layout.entryWindowOk?_sound hEntry⟩
    | cons stmt rest =>
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        cases hPrepare :
            Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
              stmtLive stmt with
        | none =>
            simp [StmtList.check?, restLive, stmtLive, liveLayout, hPrepare]
              at hCheck
        | some prepareResult =>
            rcases prepareResult with ⟨prep, preparedLayout⟩
            cases hStmt :
                Stmt.check? returns ctx preparedLayout restLive stmt with
            | none =>
                simp [StmtList.check?, restLive, stmtLive, liveLayout,
                  hPrepare, hStmt] at hCheck
            | some nextLayout =>
                have hRest :
                    StmtList.check? returns ctx nextLayout after rest =
                      some outLayout := by
                  have hCheck' := hCheck
                  simp [StmtList.check?, restLive, stmtLive, liveLayout,
                    hPrepare, hStmt] at hCheck'
                  exact hCheck'
                exact
                  ⟨prep, preparedLayout, nextLayout, hPrepare,
                    Layout.entryWindowOk?_sound
                      (Prepare.forStmtAboveSuffix?_entry hPrepare),
                    Prepare.forStmtAboveSuffix?_accessible hPrepare,
                    Stmt.check?_sound hStmt,
                    StmtList.check?_sound hRest⟩

  theorem CaseList.check?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {cases : List (Word × Block)}
      (hCheck : CaseList.check? returns ctx layout after cases = true) :
      CaseList.Sound returns ctx layout after cases := by
    cases cases with
    | nil =>
        trivial
    | cons head rest =>
        rcases head with ⟨value, body⟩
        have hAnd :
            (Block.check? returns ctx layout after body).isSome = true ∧
              CaseList.check? returns ctx layout after rest = true := by
          simpa [CaseList.check?] using hCheck
        cases hBody :
            Block.check? returns ctx layout after body with
        | none =>
            simp [hBody] at hAnd
        | some bodyLayout =>
            exact
              ⟨⟨bodyLayout, Block.check?_sound hBody⟩,
                CaseList.check?_sound hAnd.2⟩

  theorem Default.check?_sound {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {defaultBody : Option Block}
      (hCheck :
        Default.check? returns ctx layout after defaultBody = true) :
      Default.Sound returns ctx layout after defaultBody := by
    cases defaultBody with
    | none =>
        trivial
    | some body =>
        cases hBody : Block.check? returns ctx layout after body with
        | none =>
            simp [Default.check?, hBody] at hCheck
        | some bodyLayout =>
            exact ⟨bodyLayout, Block.check?_sound hBody⟩
end

theorem FunDef.check?_sound {fn : FunDef}
    (hCheck : FunDef.check? fn = true) :
    ∃ layout,
      Block.Sound fn.returns { returns := fn.returns }
        (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body layout ∧
        NamesAccess.Accessible layout 0 fn.returns := by
  unfold FunDef.check? at hCheck
  cases hBlock :
      Block.check? fn.returns { returns := fn.returns }
        (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body with
  | none =>
      simp [hBlock] at hCheck
  | some layout =>
      simp [hBlock] at hCheck
      exact
        ⟨layout, Block.check?_sound hBlock,
          NamesAccess.names?_sound hCheck⟩

end Checked

namespace Lower

def cleanupToLive (layout live : List Name) : Locals.Stmt :=
  .cleanupTo (Layout.trimDeadPrefix layout live)

set_option maxHeartbeats 800000 in
mutual
  def Block.toLocals? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Block → Option (Locals.Block × List Name)
    | ⟨stmts⟩ => do
        let (lowerStmts, outLayout) ←
          StmtList.toLocals? returns ctx layout after stmts
        some ({ stmts := lowerStmts }, outLayout)

  def Stmt.toLocals? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) : Stmt → Option (List Locals.Stmt × List Name)
    | .block body => do
        let bodyCtx := ctx.withProtectedLayout layout
        let (lowerBody, _bodyLayout) ←
          Block.toLocals? returns bodyCtx layout
            (Checked.scopedAfter layout after) body
        some ([Locals.Stmt.block lowerBody], layout)
    | .if_ cond body => do
        let bodyCtx := ctx.withProtectedLayout layout
        let (lowerBody, _bodyLayout) ←
          Block.toLocals? returns bodyCtx layout
            (Checked.scopedAfter layout after) body
        some ([Locals.Stmt.if_ cond lowerBody], layout)
    | .switch scrutinee cases defaultBody => do
        let branchCtx := ctx.withProtectedLayout layout
        let lowerCases ←
          CaseList.toLocals? returns branchCtx layout
            (Checked.scopedAfter layout after) cases
        let lowerDefault ←
          Default.toLocals? returns branchCtx layout
            (Checked.scopedAfter layout after) defaultBody
        some ([Locals.Stmt.switch scrutinee lowerCases lowerDefault], layout)
    | .for_ init cond post body => do
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        let (lowerInit, loopLayout) ←
          Block.toLocals? returns initCtx layout initAfter init
        if ExprAccess.expr? 0 loopLayout cond then
          let postAfter := Checked.scopedAfter loopLayout loopMentioned
          let bodyAfter := Checked.scopedAfter loopLayout postLive
          let postCtx := ctx.withProtectedLayout loopLayout
          let bodyLoopCtx :=
            ctx.withLoop (Checked.scopedAfter loopLayout after) bodyAfter
          let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
          let (lowerPost, _postLayout) ←
            Block.toLocals? returns postCtx loopLayout postAfter post
          let (lowerBody, _bodyLayout) ←
            Block.toLocals? returns bodyCheckCtx loopLayout bodyAfter body
          some ([Locals.Stmt.for_ lowerInit cond lowerPost lowerBody], layout)
        else
          none
    | stmt =>
        some (Functions.Stmt.toLocals returns stmt,
          Checked.Stmt.regularOutLayout layout stmt)

  def StmtList.toLocals? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) :
      List Stmt → Option (List Locals.Stmt × List Name)
    | [] =>
        if Layout.entryWindowOk? layout after then
          let liveLayout := Layout.trimDeadPrefix layout after
          some ([Locals.Stmt.cleanupTo liveLayout], liveLayout)
        else
          none
    | stmt :: rest => do
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        let (prep, preparedLayout) ←
          Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
            stmtLive stmt
        let (lowerStmt, nextLayout) ←
          Stmt.toLocals? returns ctx preparedLayout restLive stmt
        let (lowerRest, outLayout) ←
          StmtList.toLocals? returns ctx nextLayout after rest
        some
          (cleanupToLive layout stmtLive ::
              (prep ++ (lowerStmt ++ lowerRest)),
            outLayout)

  def CaseList.toLocals? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) :
      List (Word × Block) → Option (List (Word × Locals.Block))
    | [] => some []
    | (value, body) :: rest => do
        let (lowerBody, _bodyLayout) ←
          Block.toLocals? returns ctx layout after body
        let lowerRest ← CaseList.toLocals? returns ctx layout after rest
        some ((value, lowerBody) :: lowerRest)

  def Default.toLocals? (returns : List Name) (ctx : Ctx)
      (layout after : List Name) :
      Option Block → Option (Option Locals.Block)
    | none => some none
    | some body => do
        let (lowerBody, _bodyLayout) ←
          Block.toLocals? returns ctx layout after body
        some (some lowerBody)
end

namespace SwitchLowering

theorem select_none_of_toLocals?
    {returns : List Name} {ctx : Ctx} {layout after : List Name}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {lowerCases : List (Word × Locals.Block)}
    {lowerDefault : Option Locals.Block} {value : Word}
    (hCases :
      CaseList.toLocals? returns ctx layout after cases = some lowerCases)
    (hDefault :
      Default.toLocals? returns ctx layout after defaultBody =
        some lowerDefault)
    (hSelect :
      EvmCompiler.Functions.Switch.select value cases defaultBody = none) :
    Locals.Direct.Switch.select value lowerCases lowerDefault = none := by
  induction cases generalizing lowerCases with
  | nil =>
      simp [CaseList.toLocals?] at hCases
      subst lowerCases
      cases defaultBody with
      | none =>
          simp [Default.toLocals?] at hDefault
          subst lowerDefault
          simp [Locals.Direct.Switch.select]
      | some body =>
          simp [EvmCompiler.Functions.Switch.select] at hSelect
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      simp only [CaseList.toLocals?] at hCases
      cases hBody :
          Block.toLocals? returns ctx layout after body with
      | none =>
          simp [hBody] at hCases
      | some loweredBody =>
          rcases loweredBody with ⟨lowerBody, bodyLayout⟩
          simp [hBody] at hCases
          cases hRest :
              CaseList.toLocals? returns ctx layout after rest with
          | none =>
              simp [hRest] at hCases
          | some lowerRest =>
              simp [hRest] at hCases
              rcases hCases with ⟨rfl⟩
              by_cases hEq : caseValue = value
              · simp [EvmCompiler.Functions.Switch.select, Locals.Direct.Switch.select, hEq] at hSelect
              · simp [EvmCompiler.Functions.Switch.select, Locals.Direct.Switch.select, hEq] at hSelect ⊢
                exact ih hRest hSelect

theorem select_some_of_toLocals?
    {returns : List Name} {ctx : Ctx} {layout after : List Name}
    {cases : List (Word × Block)} {defaultBody : Option Block}
    {lowerCases : List (Word × Locals.Block)}
    {lowerDefault : Option Locals.Block} {value : Word} {body : Block}
    (hCases :
      CaseList.toLocals? returns ctx layout after cases = some lowerCases)
    (hDefault :
      Default.toLocals? returns ctx layout after defaultBody =
        some lowerDefault)
    (hSelect :
      EvmCompiler.Functions.Switch.select value cases defaultBody = some body) :
    ∃ (lowerBody : Locals.Block) (bodyLayout : List Name),
      Locals.Direct.Switch.select value lowerCases lowerDefault =
        some lowerBody ∧
      Block.toLocals? returns ctx layout after body =
        some (lowerBody, bodyLayout) := by
  induction cases generalizing lowerCases with
  | nil =>
      simp [CaseList.toLocals?] at hCases
      subst lowerCases
      cases defaultBody with
      | none =>
          simp [EvmCompiler.Functions.Switch.select] at hSelect
      | some defaultBlock =>
          simp [EvmCompiler.Functions.Switch.select, Default.toLocals?] at hDefault hSelect
          cases hDefaultBody :
              Block.toLocals? returns ctx layout after defaultBlock with
          | none =>
              simp [hDefaultBody] at hDefault
          | some loweredDefault =>
              rcases loweredDefault with ⟨lowerBody, bodyLayout⟩
              simp [hDefaultBody] at hDefault
              rcases hDefault with ⟨rfl⟩
              cases hSelect
              exact
                ⟨lowerBody, bodyLayout,
                  by simp [Locals.Direct.Switch.select], hDefaultBody⟩
  | cons head rest ih =>
      rcases head with ⟨caseValue, caseBody⟩
      simp only [CaseList.toLocals?] at hCases
      cases hCaseBody :
          Block.toLocals? returns ctx layout after caseBody with
      | none =>
          simp [hCaseBody] at hCases
      | some loweredCase =>
          rcases loweredCase with ⟨lowerCaseBody, caseBodyLayout⟩
          simp [hCaseBody] at hCases
          cases hRest :
              CaseList.toLocals? returns ctx layout after rest with
          | none =>
              simp [hRest] at hCases
          | some lowerRest =>
              simp [hRest] at hCases
              rcases hCases with ⟨rfl⟩
              by_cases hEq : caseValue = value
              · simp [EvmCompiler.Functions.Switch.select, Locals.Direct.Switch.select, hEq] at hSelect ⊢
                cases hSelect
                exact ⟨caseBodyLayout, hCaseBody⟩
              · simp [EvmCompiler.Functions.Switch.select, Locals.Direct.Switch.select, hEq] at hSelect ⊢
                rcases ih hRest hSelect with
                  ⟨lowerBody, bodyLayout, hTargetSelect, hLowerBody⟩
                exact ⟨lowerBody, hTargetSelect, bodyLayout, hLowerBody⟩

end SwitchLowering

namespace ForLowering

theorem components_of_toLocals?
    {returns : List Name} {ctx : Ctx} {layout after : List Name}
    {init post body : Block} {cond : Expr 1}
    {lowerStmt : List Locals.Stmt} {outLayout : List Name}
    (hLower :
      Stmt.toLocals? returns ctx layout after
        (.for_ init cond post body) = some (lowerStmt, outLayout)) :
    let loopMentioned :=
      NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
        after]
    let postLive := Block.liveBefore ctx loopMentioned post
    let bodyCtx := ctx.withLoop after postLive
    let bodyLive := Block.liveBefore bodyCtx postLive body
    let loopLive :=
      NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
    let initAfter := NameSet.union loopLive layout
    ∃ lowerInit loopLayout lowerPost postLayout lowerBody bodyLayout,
      Block.toLocals? returns (ctx.withProtectedLayout layout) layout initAfter init =
        some (lowerInit, loopLayout) ∧
      ExprAccess.expr? 0 loopLayout cond = true ∧
      let postAfter := Checked.scopedAfter loopLayout loopMentioned
      let bodyAfter := Checked.scopedAfter loopLayout postLive
      let postCtx := ctx.withProtectedLayout loopLayout
      let bodyLoopCtx :=
        ctx.withLoop (Checked.scopedAfter loopLayout after) bodyAfter
      let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
      Block.toLocals? returns postCtx loopLayout postAfter post =
        some (lowerPost, postLayout) ∧
      Block.toLocals? returns bodyCheckCtx loopLayout bodyAfter body =
        some (lowerBody, bodyLayout) ∧
      lowerStmt = [Locals.Stmt.for_ lowerInit cond lowerPost lowerBody] ∧
      outLayout = layout := by
  simp only [Stmt.toLocals?] at hLower
  let loopMentioned :=
    NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
      after]
  let postLive := Block.liveBefore ctx loopMentioned post
  let bodyCtx := ctx.withLoop after postLive
  let bodyLive := Block.liveBefore bodyCtx postLive body
  let loopLive :=
    NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
  let initAfter := NameSet.union loopLive layout
  let initCtx := ctx.withProtectedLayout layout
  cases hInit :
      Block.toLocals? returns initCtx layout initAfter init with
  | none =>
    simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive, initAfter,
        initCtx, hInit] at hLower
  | some initResult =>
      rcases initResult with ⟨lowerInit, loopLayout⟩
      cases hCond : ExprAccess.expr? 0 loopLayout cond with
      | false =>
          simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
            initAfter, initCtx, hInit, hCond] at hLower
      | true =>
          let postAfter := Checked.scopedAfter loopLayout loopMentioned
          let bodyAfter := Checked.scopedAfter loopLayout postLive
          let postCtx := ctx.withProtectedLayout loopLayout
          let bodyLoopCtx :=
            ctx.withLoop (Checked.scopedAfter loopLayout after) bodyAfter
          let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
          cases hPost :
              Block.toLocals? returns postCtx loopLayout postAfter post with
          | none =>
              simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
                initAfter, postAfter, bodyAfter, initCtx, postCtx, bodyLoopCtx,
                bodyCheckCtx, hInit, hCond, hPost] at hLower
          | some postResult =>
              rcases postResult with ⟨lowerPost, postLayout⟩
              cases hBody :
                  Block.toLocals? returns bodyCheckCtx loopLayout bodyAfter body
                    with
              | none =>
                  simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
                    initAfter, postAfter, bodyAfter, initCtx, postCtx,
                    bodyLoopCtx, bodyCheckCtx, hInit, hCond, hPost, hBody] at hLower
              | some bodyResult =>
                  rcases bodyResult with ⟨lowerBody, bodyLayout⟩
                  simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
                    initAfter, postAfter, bodyAfter, initCtx, postCtx,
                    bodyLoopCtx, bodyCheckCtx, hInit, hCond, hPost, hBody] at hLower
                  rcases hLower with ⟨rfl, rfl⟩
                  exact
                    ⟨lowerInit, loopLayout, lowerPost, postLayout, lowerBody,
                      bodyLayout, hInit, hCond, hPost, hBody, rfl, rfl⟩

end ForLowering

namespace StmtList

theorem toLocals?_cons_components {returns : List Name} {ctx : Ctx}
    {layout after : List Name} {stmt : Stmt} {rest : List Stmt}
    {lowerStmts : List Locals.Stmt} {outLayout : List Name}
    (hLower :
      StmtList.toLocals? returns ctx layout after (stmt :: rest) =
        some (lowerStmts, outLayout)) :
    ∃ restLive stmtLive liveLayout prep preparedLayout lowerStmt nextLayout
        lowerRest,
      restLive = StmtList.liveBefore ctx after rest ∧
        stmtLive = Stmt.liveBefore ctx restLive stmt ∧
        liveLayout = Layout.trimDeadPrefix layout stmtLive ∧
        Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
          stmtLive stmt =
          some (prep, preparedLayout) ∧
        Layout.entryWindowOk? preparedLayout stmtLive = true ∧
        StmtAccess.accessible? returns preparedLayout stmt = true ∧
        Stmt.toLocals? returns ctx preparedLayout
          restLive stmt = some (lowerStmt, nextLayout) ∧
        StmtList.toLocals? returns ctx nextLayout after rest =
          some (lowerRest, outLayout) ∧
        lowerStmts =
          Lower.cleanupToLive layout stmtLive ::
            (prep ++ (lowerStmt ++ lowerRest)) := by
  simp only [StmtList.toLocals?] at hLower
  let restLive := StmtList.liveBefore ctx after rest
  let stmtLive := Stmt.liveBefore ctx restLive stmt
  let liveLayout := Layout.trimDeadPrefix layout stmtLive
  cases hPrepare :
      Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
        stmtLive stmt with
  | none =>
      simp [restLive, stmtLive, liveLayout, hPrepare] at hLower
  | some prepareResult =>
      rcases prepareResult with ⟨prep, preparedLayout⟩
      cases hStmt :
          Stmt.toLocals? returns ctx preparedLayout restLive stmt with
      | none =>
          simp [restLive, stmtLive, liveLayout, hPrepare, hStmt] at hLower
      | some stmtResult =>
          rcases stmtResult with ⟨lowerStmt, nextLayout⟩
          cases hRest :
              StmtList.toLocals? returns ctx nextLayout after rest with
          | none =>
              simp [restLive, stmtLive, liveLayout, hPrepare, hStmt, hRest]
                at hLower
          | some restResult =>
              rcases restResult with ⟨lowerRest, finalLayout⟩
              simp [restLive, stmtLive, liveLayout, hPrepare, hStmt, hRest]
                at hLower
              rcases hLower with ⟨hLowerStmts, hOutLayout⟩
              subst outLayout
              subst lowerStmts
              exact
                ⟨restLive, stmtLive, liveLayout, prep, preparedLayout,
                  lowerStmt, nextLayout, lowerRest, rfl, rfl, rfl,
                  hPrepare, Prepare.forStmtAboveSuffix?_entry hPrepare,
                  Prepare.forStmtAboveSuffix?_access hPrepare, hStmt, hRest,
                  rfl⟩

end StmtList

namespace FunDef

def toLocalsProc? (fn : FunDef) : Option Locals.Proc := do
  let entryLayout := fn.returns.reverse ++ fn.params.reverse
  let (lowerBody, layout) ←
    Block.toLocals? fn.returns { returns := fn.returns }
      entryLayout fn.returns fn.body
  if NamesAccess.names? 0 layout fn.returns then
    some
      { name := fn.name
        argc := fn.params.length
        retc := fn.returns.length
        entryLayout := fn.params.reverse
        body :=
          { stmts :=
              EvmCompiler.Functions.Lower.initReturns fn.returns ++
                lowerBody.stmts ++
                EvmCompiler.Functions.Lower.pushReturns fn.returns } }
  else
    none

end FunDef

namespace FunList

def toLocalsProcs? : List FunDef → Option (List Locals.Proc)
  | [] => some []
  | fn :: rest => do
      let lowerFn ← FunDef.toLocalsProc? fn
      let lowerRest ← toLocalsProcs? rest
      some (lowerFn :: lowerRest)

end FunList

namespace Program

def toLocals? (program : Program) : Option Locals.Program := do
  let procs ← FunList.toLocalsProcs? program.functions
  let (body, _layout) ← Block.toLocals? [] {} [] [] program.body
  some { procs := procs, body := body }

def toExpressions? (program : Program) : Option Expressions.Program := do
  let lower ← toLocals? program
  lower.toExpressions?

def compile? (program : Program) : Option Assembly.TargetProgram := do
  let lower ← toLocals? program
  lower.compile?

def toLocalsNoInternalCall? (program : Program) :
    Option Locals.Program :=
  if EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.check? program then
    toLocals? program
  else
    none

def toExpressionsNoInternalCall? (program : Program) :
    Option Expressions.Program := do
  let lower ← toLocalsNoInternalCall? program
  lower.toExpressions?

def compileNoInternalCall? (program : Program) :
    Option Assembly.TargetProgram := do
  let lower ← toLocalsNoInternalCall? program
  lower.compile?

theorem toLocals?_components {program : Program} {lower : Locals.Program}
    (hLower : toLocals? program = some lower) :
    ∃ lowerProcs lowerBody bodyLayout,
      FunList.toLocalsProcs? program.functions = some lowerProcs ∧
        Block.toLocals? [] {} [] [] program.body =
          some (lowerBody, bodyLayout) ∧
        lower = { procs := lowerProcs, body := lowerBody } := by
  unfold toLocals? at hLower
  cases hProcs : FunList.toLocalsProcs? program.functions with
  | none =>
      simp [hProcs] at hLower
  | some lowerProcs =>
      cases hBody : Block.toLocals? [] {} [] [] program.body with
      | none =>
          simp [hProcs, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨lowerBody, bodyLayout⟩
          simp [hProcs, hBody] at hLower
          exact ⟨lowerProcs, lowerBody, bodyLayout, rfl, rfl, hLower.symm⟩

theorem toLocalsNoInternalCall?_components {program : Program}
    {lower : Locals.Program}
    (hLower : toLocalsNoInternalCall? program = some lower) :
    EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      ∃ lowerProcs lowerBody bodyLayout,
        FunList.toLocalsProcs? program.functions = some lowerProcs ∧
          Block.toLocals? [] {} [] [] program.body =
            some (lowerBody, bodyLayout) ∧
          lower = { procs := lowerProcs, body := lowerBody } := by
  unfold toLocalsNoInternalCall? at hLower
  cases hNoCallCheck :
      EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.check? program with
  | false =>
      simp [hNoCallCheck] at hLower
  | true =>
      have hLiveLower : toLocals? program = some lower := by
        simpa [hNoCallCheck] using hLower
      exact
        ⟨EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.check?_sound
          hNoCallCheck,
          toLocals?_components hLiveLower⟩

end Program

set_option maxHeartbeats 800000 in
mutual
  theorem Block.toLocals?_checked {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {block : Block} {lower : Locals.Block}
      {outLayout : List Name}
      (hLower :
        Block.toLocals? returns ctx layout after block =
          some (lower, outLayout)) :
      Checked.Block.check? returns ctx layout after block = some outLayout := by
    cases block with
    | mk stmts =>
        simp only [Block.toLocals?, Checked.Block.check?] at hLower ⊢
        cases hList :
            StmtList.toLocals? returns ctx layout after stmts with
        | none =>
            simp [hList] at hLower
        | some result =>
            rcases result with ⟨lowerStmts, outLayout'⟩
            simp [hList] at hLower
            rcases hLower with ⟨_hLower, hOut⟩
            subst outLayout
            exact StmtList.toLocals?_checked hList

  theorem Stmt.toLocals?_checked {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {stmt : Stmt} {lower : List Locals.Stmt}
      {outLayout : List Name}
      (hLower :
        Stmt.toLocals? returns ctx layout after stmt =
          some (lower, outLayout)) :
      Checked.Stmt.check? returns ctx layout after stmt = some outLayout := by
    cases stmt with
    | expr expr =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2
    | let_ name value =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2
    | assign name value =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2
    | block body =>
        simp only [Stmt.toLocals?, Checked.Stmt.check?] at hLower ⊢
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Block.toLocals? returns bodyCtx layout
              (Checked.scopedAfter layout after) body with
        | none =>
            simp [bodyCtx, hBody] at hLower
        | some result =>
            rcases result with ⟨lowerBody, bodyLayout⟩
            simp [bodyCtx, hBody] at hLower
            rcases hLower with ⟨_hLower, hOut⟩
            subst outLayout
            have hBodyCheck := Block.toLocals?_checked hBody
            simp [bodyCtx, hBodyCheck]
    | if_ cond body =>
        simp only [Stmt.toLocals?, Checked.Stmt.check?] at hLower ⊢
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Block.toLocals? returns bodyCtx layout
              (Checked.scopedAfter layout after) body with
        | none =>
            simp [bodyCtx, hBody] at hLower
        | some result =>
            rcases result with ⟨lowerBody, bodyLayout⟩
            simp [bodyCtx, hBody] at hLower
            rcases hLower with ⟨_hLower, hOut⟩
            subst outLayout
            have hBodyCheck := Block.toLocals?_checked hBody
            simp [bodyCtx, hBodyCheck]
    | switch scrutinee cases defaultBody =>
        simp only [Stmt.toLocals?, Checked.Stmt.check?] at hLower ⊢
        let branchCtx := ctx.withProtectedLayout layout
        cases hCases :
            CaseList.toLocals? returns branchCtx layout
              (Checked.scopedAfter layout after) cases with
        | none =>
            simp [branchCtx, hCases] at hLower
        | some lowerCases =>
            cases hDefault :
                Default.toLocals? returns branchCtx layout
                  (Checked.scopedAfter layout after) defaultBody with
            | none =>
                simp [branchCtx, hCases, hDefault] at hLower
            | some lowerDefault =>
                simp [branchCtx, hCases, hDefault] at hLower
                rcases hLower with ⟨_hLower, hOut⟩
                subst outLayout
                have hCasesCheck := CaseList.toLocals?_checked hCases
                have hDefaultCheck := Default.toLocals?_checked hDefault
                simp [branchCtx, hCasesCheck, hDefaultCheck]
    | for_ init cond post body =>
        simp only [Stmt.toLocals?, Checked.Stmt.check?] at hLower ⊢
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        cases hInit :
            Block.toLocals? returns initCtx layout initAfter init with
        | none =>
            simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
              initAfter, initCtx, hInit] at hLower
        | some initResult =>
            rcases initResult with ⟨lowerInit, loopLayout⟩
            cases hCond : ExprAccess.expr? 0 loopLayout cond with
            | false =>
                simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
                  initAfter, initCtx, hInit, hCond] at hLower
            | true =>
                let postAfter := Checked.scopedAfter loopLayout loopMentioned
                let bodyAfter := Checked.scopedAfter loopLayout postLive
                let postCtx := ctx.withProtectedLayout loopLayout
                let bodyLoopCtx :=
                  ctx.withLoop (Checked.scopedAfter loopLayout after) bodyAfter
                let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
                cases hPost :
                    Block.toLocals? returns postCtx loopLayout postAfter post with
                | none =>
                    simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
                      initAfter, postAfter, bodyAfter, initCtx, postCtx,
                      bodyLoopCtx, bodyCheckCtx, hInit, hCond, hPost] at hLower
                | some postResult =>
                    rcases postResult with ⟨lowerPost, postLayout⟩
                    cases hBody :
                        Block.toLocals? returns bodyCheckCtx loopLayout
                          bodyAfter body with
                    | none =>
                        simp [loopMentioned, postLive, bodyCtx, bodyLive,
                          loopLive, initAfter, postAfter, bodyAfter, initCtx,
                          postCtx, bodyLoopCtx, bodyCheckCtx, hInit, hCond,
                          hPost, hBody] at hLower
                    | some bodyResult =>
                        rcases bodyResult with ⟨lowerBody, bodyLayout⟩
                        simp [loopMentioned, postLive, bodyCtx, bodyLive,
                          loopLive, initAfter, postAfter, bodyAfter, initCtx,
                          postCtx, bodyLoopCtx, bodyCheckCtx, hInit, hCond,
                          hPost, hBody] at hLower
                        rcases hLower with ⟨_hLower, hOut⟩
                        subst outLayout
                        have hInitCheck := Block.toLocals?_checked hInit
                        have hPostCheck := Block.toLocals?_checked hPost
                        have hBodyCheck := Block.toLocals?_checked hBody
                        simp [loopMentioned, postLive, bodyCtx, bodyLive,
                          loopLive, initAfter, postAfter, bodyAfter, initCtx,
                          postCtx, bodyLoopCtx, bodyCheckCtx, hInitCheck,
                          hCond, hPostCheck, hBodyCheck]
    | brk =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2
    | cont =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2
    | leave =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2
    | call targets functionName args =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2
    | terminal kind =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2
    | terminalArgs kind args =>
        simp [Stmt.toLocals?, Checked.Stmt.check?,
          Checked.Stmt.regularOutLayout] at hLower ⊢
        exact hLower.2

  theorem StmtList.toLocals?_checked {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {stmts : List Stmt}
      {lower : List Locals.Stmt} {outLayout : List Name}
      (hLower :
        StmtList.toLocals? returns ctx layout after stmts =
          some (lower, outLayout)) :
      Checked.StmtList.check? returns ctx layout after stmts =
        some outLayout := by
    cases stmts with
    | nil =>
        simp only [StmtList.toLocals?, Checked.StmtList.check?] at hLower ⊢
        cases hEntry : Layout.entryWindowOk? layout after <;>
          simp [hEntry] at hLower ⊢
        exact hLower.2
    | cons stmt rest =>
        simp only [StmtList.toLocals?, Checked.StmtList.check?] at hLower ⊢
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        cases hPrepare :
            Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
              stmtLive stmt with
        | none =>
            simp [restLive, stmtLive, liveLayout, hPrepare] at hLower
        | some prepareResult =>
            rcases prepareResult with ⟨prep, preparedLayout⟩
            cases hStmt :
                Stmt.toLocals? returns ctx preparedLayout restLive stmt with
            | none =>
                simp [restLive, stmtLive, liveLayout, hPrepare, hStmt]
                  at hLower
            | some stmtResult =>
                rcases stmtResult with ⟨lowerStmt, nextLayout⟩
                cases hRest :
                    StmtList.toLocals? returns ctx nextLayout after rest with
                | none =>
                    simp [restLive, stmtLive, liveLayout, hPrepare, hStmt,
                      hRest] at hLower
                | some restResult =>
                    rcases restResult with ⟨lowerRest, finalLayout⟩
                    simp [restLive, stmtLive, liveLayout, hPrepare, hStmt,
                      hRest] at hLower
                    rcases hLower with ⟨_hLower, hOut⟩
                    have hStmtCheck := Stmt.toLocals?_checked hStmt
                    have hRestCheck := StmtList.toLocals?_checked hRest
                    simpa [restLive, stmtLive, liveLayout, hPrepare,
                      hStmtCheck, hRestCheck]

  theorem CaseList.toLocals?_checked {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {cases : List (Word × Block)}
      {lower : List (Word × Locals.Block)}
      (hLower :
        CaseList.toLocals? returns ctx layout after cases = some lower) :
      Checked.CaseList.check? returns ctx layout after cases = true := by
    cases cases with
    | nil =>
        simpa [CaseList.toLocals?, Checked.CaseList.check?] using hLower
    | cons head rest =>
        rcases head with ⟨value, body⟩
        simp only [CaseList.toLocals?, Checked.CaseList.check?] at hLower ⊢
        cases hBody : Block.toLocals? returns ctx layout after body with
        | none =>
            simp [hBody] at hLower
        | some bodyResult =>
            rcases bodyResult with ⟨lowerBody, bodyLayout⟩
            cases hRest : CaseList.toLocals? returns ctx layout after rest with
            | none =>
                simp [hBody, hRest] at hLower
            | some lowerRest =>
                simp [hBody, hRest] at hLower
                cases hLower
                have hBodyCheck := Block.toLocals?_checked hBody
                have hRestCheck := CaseList.toLocals?_checked hRest
                simp [hBodyCheck, hRestCheck]

  theorem Default.toLocals?_checked {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {defaultBody : Option Block}
      {lower : Option Locals.Block}
      (hLower :
        Default.toLocals? returns ctx layout after defaultBody = some lower) :
      Checked.Default.check? returns ctx layout after defaultBody = true := by
    cases defaultBody with
    | none =>
        simpa [Default.toLocals?, Checked.Default.check?] using hLower
    | some body =>
        simp only [Default.toLocals?, Checked.Default.check?] at hLower ⊢
        cases hBody : Block.toLocals? returns ctx layout after body with
        | none =>
            simp [hBody] at hLower
        | some bodyResult =>
            rcases bodyResult with ⟨lowerBody, bodyLayout⟩
            simp [hBody] at hLower
            cases hLower
            have hBodyCheck := Block.toLocals?_checked hBody
            simp [hBodyCheck]
end


private theorem Scope.stmt_outEnv_contains_of_contains
    {env : List Name} {stmt : Stmt} {name : Name}
    (hContains : name ∈ env) :
    name ∈ Scope.Stmt.outEnv env stmt := by
  cases stmt <;> simp [Scope.Stmt.outEnv, hContains]

mutual
  theorem Checked.Block.check?_layoutRel {returns : List Name} {ctx : Ctx}
      {sourceEnv layout after : List Name} {block : Block}
      {outLayout : List Name}
      (hCheck :
        Checked.Block.check? returns ctx layout after block = some outLayout)
      (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ sourceEnv)
      (hNoDup : layout.Nodup)
      (hScoped : Scope.Block.Scoped sourceEnv block) :
      (∀ {name : Name}, name ∈ outLayout →
          name ∈ Scope.Block.outEnv sourceEnv block) ∧ outLayout.Nodup := by
    cases block with
    | mk stmts =>
        exact Checked.StmtList.check?_layoutRel hCheck hSubset hNoDup hScoped

  theorem Checked.Stmt.check?_layoutRel {returns : List Name} {ctx : Ctx}
      {sourceEnv layout after : List Name} {stmt : Stmt}
      {outLayout : List Name}
      (hCheck :
        Checked.Stmt.check? returns ctx layout after stmt = some outLayout)
      (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ sourceEnv)
      (hNoDup : layout.Nodup)
      (hScoped : Scope.Stmt.Scoped sourceEnv stmt) :
      (∀ {name : Name}, name ∈ outLayout →
          name ∈ Scope.Stmt.outEnv sourceEnv stmt) ∧ outLayout.Nodup := by
    cases stmt with
    | expr expr =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩
    | let_ name value =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        rcases hScoped with ⟨hFresh, _hValueScoped⟩
        cases hCheck
        refine ⟨?_, ?_⟩
        · intro needle hMem
          simp [Scope.Stmt.outEnv] at hMem ⊢
          exact hMem.imp_right (fun hTail => hSubset hTail)
        · exact List.Nodup.cons (fun hMem => hFresh (hSubset hMem)) hNoDup
    | assign name value =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩
    | block body =>
        simp only [Checked.Stmt.check?] at hCheck
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Checked.Block.check? returns bodyCtx layout
              (Checked.scopedAfter layout after) body with
        | none =>
            simp [bodyCtx, hBody] at hCheck
        | some bodyLayout =>
            simp [bodyCtx, hBody] at hCheck
            cases hCheck
            exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
              hNoDup⟩
    | if_ cond body =>
        simp only [Checked.Stmt.check?] at hCheck
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBody :
            Checked.Block.check? returns bodyCtx layout
              (Checked.scopedAfter layout after) body with
        | none =>
            simp [bodyCtx, hBody] at hCheck
        | some bodyLayout =>
            simp [bodyCtx, hBody] at hCheck
            cases hCheck
            exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
              hNoDup⟩
    | switch scrutinee cases defaultBody =>
        simp only [Checked.Stmt.check?] at hCheck
        let branchCtx := ctx.withProtectedLayout layout
        cases hCases :
            Checked.CaseList.check? returns branchCtx layout
              (Checked.scopedAfter layout after) cases <;>
          cases hDefault :
            Checked.Default.check? returns branchCtx layout
              (Checked.scopedAfter layout after) defaultBody <;>
          simp [branchCtx, hCases, hDefault] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩
    | for_ init cond post body =>
        simp only [Checked.Stmt.check?] at hCheck
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        cases hInit :
            Checked.Block.check? returns initCtx layout initAfter init with
        | none =>
            simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
              initAfter, initCtx, hInit] at hCheck
        | some loopLayout =>
            cases hCond : ExprAccess.expr? 0 loopLayout cond with
            | false =>
                simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
                  initAfter, initCtx, hInit, hCond] at hCheck
            | true =>
                let postAfter := Checked.scopedAfter loopLayout loopMentioned
                let bodyAfter := Checked.scopedAfter loopLayout postLive
                let postCtx := ctx.withProtectedLayout loopLayout
                let bodyLoopCtx :=
                  ctx.withLoop (Checked.scopedAfter loopLayout after) bodyAfter
                let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
                cases hPost :
                    Checked.Block.check? returns postCtx loopLayout postAfter post with
                | none =>
                    simp [loopMentioned, postLive, bodyCtx, bodyLive,
                      loopLive, initAfter, postAfter, bodyAfter, initCtx,
                      postCtx, bodyLoopCtx, bodyCheckCtx, hInit, hCond,
                      hPost] at hCheck
                | some postLayout =>
                    cases hBody :
                        Checked.Block.check? returns bodyCheckCtx loopLayout
                          bodyAfter body with
                    | none =>
                        simp [loopMentioned, postLive, bodyCtx, bodyLive,
                          loopLive, initAfter, postAfter, bodyAfter, initCtx,
                          postCtx, bodyLoopCtx, bodyCheckCtx, hInit, hCond,
                          hPost, hBody] at hCheck
                    | some bodyLayout =>
                        simp [loopMentioned, postLive, bodyCtx, bodyLive,
                          loopLive, initAfter, postAfter, bodyAfter, initCtx,
                          postCtx, bodyLoopCtx, bodyCheckCtx, hInit, hCond,
                          hPost, hBody] at hCheck
                        cases hCheck
                        exact
                          ⟨fun hMem => by
                              simpa [Scope.Stmt.outEnv] using hSubset hMem,
                            hNoDup⟩
    | brk =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩
    | cont =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩
    | leave =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩
    | call targets functionName args =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩
    | terminal kind =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩
    | terminalArgs kind args =>
        simp [Checked.Stmt.check?, Checked.Stmt.regularOutLayout] at hCheck
        cases hCheck
        exact ⟨fun hMem => by simpa [Scope.Stmt.outEnv] using hSubset hMem,
          hNoDup⟩

  theorem Checked.StmtList.check?_layoutRel {returns : List Name} {ctx : Ctx}
      {sourceEnv layout after : List Name} {stmts : List Stmt}
      {outLayout : List Name}
      (hCheck :
        Checked.StmtList.check? returns ctx layout after stmts =
          some outLayout)
      (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ sourceEnv)
      (hNoDup : layout.Nodup)
      (hScoped : Scope.StmtList.Scoped sourceEnv stmts) :
      (∀ {name : Name}, name ∈ outLayout →
          name ∈ Scope.StmtList.outEnv sourceEnv stmts) ∧ outLayout.Nodup := by
    cases stmts with
    | nil =>
        simp only [Checked.StmtList.check?] at hCheck
        cases hEntry : Layout.entryWindowOk? layout after <;>
          simp [hEntry] at hCheck
        cases hCheck
        refine ⟨?_, Layout.trimDeadPrefix_nodup hNoDup⟩
        intro name hMem
        simpa [Scope.StmtList.outEnv] using
          hSubset (Layout.mem_trimDeadPrefix hMem)
    | cons stmt rest =>
        simp only [Checked.StmtList.check?] at hCheck
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        cases hPrepare :
            Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
              stmtLive stmt with
        | none =>
            simp [restLive, stmtLive, liveLayout, hPrepare] at hCheck
        | some prepareResult =>
            rcases prepareResult with ⟨prep, preparedLayout⟩
            cases hStmt :
                Checked.Stmt.check? returns ctx preparedLayout restLive stmt with
            | none =>
                simp [restLive, stmtLive, liveLayout, hPrepare, hStmt]
                  at hCheck
            | some nextLayout =>
                cases hRest :
                    Checked.StmtList.check? returns ctx nextLayout after rest with
                | none =>
                    simp [restLive, stmtLive, liveLayout, hPrepare, hStmt,
                      hRest] at hCheck
                | some finalLayout =>
                    simp [restLive, stmtLive, liveLayout, hPrepare, hStmt,
                      hRest] at hCheck
                    cases hCheck
                    rcases hScoped with ⟨hStmtScoped, hRestScoped⟩
                    have hLiveNoDup : liveLayout.Nodup :=
                      Layout.trimDeadPrefix_nodup hNoDup
                    have hLiveSubset :
                        ∀ {name : Name}, name ∈ liveLayout →
                          name ∈ sourceEnv := by
                      intro name hMem
                      exact hSubset (Layout.mem_trimDeadPrefix hMem)
                    have hPreparedNoDup : preparedLayout.Nodup :=
                      Prepare.forStmtAboveSuffix?_nodup hPrepare hLiveNoDup
                    have hPreparedSubset :
                        ∀ {name : Name}, name ∈ preparedLayout →
                          name ∈ sourceEnv := by
                      intro name hMem
                      exact hLiveSubset
                        (Prepare.forStmtAboveSuffix?_mem hPrepare hMem)
                    have hNextRel :=
                      Checked.Stmt.check?_layoutRel hStmt hPreparedSubset
                        hPreparedNoDup hStmtScoped
                    exact
                      Checked.StmtList.check?_layoutRel
                        (sourceEnv := Scope.Stmt.outEnv sourceEnv stmt)
                        hRest hNextRel.1 hNextRel.2 hRestScoped
end

theorem Checked.Block.check?_nodup {returns : List Name} {ctx : Ctx}
    {sourceEnv layout after : List Name} {block : Block} {outLayout : List Name}
    (hCheck :
      Checked.Block.check? returns ctx layout after block = some outLayout)
    (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ sourceEnv)
    (hNoDup : layout.Nodup)
    (hScoped : Scope.Block.Scoped sourceEnv block) :
    outLayout.Nodup :=
  (Checked.Block.check?_layoutRel hCheck hSubset hNoDup hScoped).2

theorem Checked.Stmt.check?_nodup {returns : List Name} {ctx : Ctx}
    {sourceEnv layout after : List Name} {stmt : Stmt} {outLayout : List Name}
    (hCheck :
      Checked.Stmt.check? returns ctx layout after stmt = some outLayout)
    (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ sourceEnv)
    (hNoDup : layout.Nodup)
    (hScoped : Scope.Stmt.Scoped sourceEnv stmt) :
    outLayout.Nodup :=
  (Checked.Stmt.check?_layoutRel hCheck hSubset hNoDup hScoped).2

theorem Checked.StmtList.check?_nodup {returns : List Name} {ctx : Ctx}
    {sourceEnv layout after : List Name} {stmts : List Stmt}
    {outLayout : List Name}
    (hCheck :
      Checked.StmtList.check? returns ctx layout after stmts = some outLayout)
    (hSubset : ∀ {name : Name}, name ∈ layout → name ∈ sourceEnv)
    (hNoDup : layout.Nodup)
    (hScoped : Scope.StmtList.Scoped sourceEnv stmts) :
    outLayout.Nodup :=
  (Checked.StmtList.check?_layoutRel hCheck hSubset hNoDup hScoped).2

theorem stmt_toLocals?_regularOutLayout {returns : List Name} {ctx : Ctx}
    {layout after : List Name} {stmt : Stmt} {lower : List Locals.Stmt}
    {outLayout : List Name}
    (hLower :
      Stmt.toLocals? returns ctx layout after stmt =
        some (lower, outLayout)) :
    outLayout = Checked.Stmt.regularOutLayout layout stmt := by
  have hCheck := Stmt.toLocals?_checked hLower
  have hSound := Checked.Stmt.check?_sound hCheck
  cases stmt <;>
    simp [Checked.Stmt.Sound, Checked.Stmt.regularOutLayout] at hSound ⊢
  all_goals
    first
    | exact hSound
    | exact hSound.1

theorem FunDef.toLocalsProc?_checked {fn : FunDef} {proc : Locals.Proc}
    (hLower : FunDef.toLocalsProc? fn = some proc) :
    Checked.FunDef.check? fn = true := by
  simp only [FunDef.toLocalsProc?, Checked.FunDef.check?] at hLower ⊢
  cases hBody :
      Block.toLocals? fn.returns { returns := fn.returns }
        (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body with
  | none =>
      simp [hBody] at hLower
  | some result =>
      rcases result with ⟨lowerBody, layout⟩
      cases hNames : NamesAccess.names? 0 layout fn.returns with
      | false =>
          simp [hBody, hNames] at hLower
      | true =>
          simp [hBody, hNames] at hLower
          cases hLower
          have hBodyCheck := Block.toLocals?_checked hBody
          simp [hBodyCheck, hNames]

theorem FunDef.toLocalsProc?_components {fn : FunDef} {proc : Locals.Proc}
    (hLower : FunDef.toLocalsProc? fn = some proc) :
    ∃ lowerBody layout,
      Block.toLocals? fn.returns { returns := fn.returns }
          (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body =
        some (lowerBody, layout) ∧
      NamesAccess.Accessible layout 0 fn.returns ∧
      proc =
        { name := fn.name
          argc := fn.params.length
          retc := fn.returns.length
          entryLayout := fn.params.reverse
          body :=
            { stmts :=
                Lower.initReturns fn.returns ++
                  (lowerBody.stmts ++ Lower.pushReturns fn.returns) } } := by
  simp only [FunDef.toLocalsProc?] at hLower
  cases hBody :
      Block.toLocals? fn.returns { returns := fn.returns }
        (fn.returns.reverse ++ fn.params.reverse) fn.returns fn.body with
  | none =>
      simp [hBody] at hLower
  | some result =>
      rcases result with ⟨lowerBody, layout⟩
      cases hNames : NamesAccess.names? 0 layout fn.returns with
      | false =>
          simp [hBody, hNames] at hLower
      | true =>
          simp [hBody, hNames] at hLower
          cases hLower
          exact
            ⟨lowerBody, layout, rfl, NamesAccess.names?_sound hNames, rfl⟩

theorem FunList.toLocalsProcs?_checked :
    ∀ {fns : List FunDef} {procs : List Locals.Proc},
      FunList.toLocalsProcs? fns = some procs →
        Checked.FunList.check? fns = true
  | [], _procs, hLower => by
      simpa [FunList.toLocalsProcs?, Checked.FunList.check?] using hLower
  | fn :: rest, _procs, hLower => by
      simp only [FunList.toLocalsProcs?, Checked.FunList.check?]
        at hLower ⊢
      cases hFn : FunDef.toLocalsProc? fn with
      | none =>
          simp [hFn] at hLower
      | some lowerFn =>
          cases hRest : FunList.toLocalsProcs? rest with
          | none =>
              simp [hFn, hRest] at hLower
          | some lowerRest =>
              simp [hFn, hRest] at hLower
              have hFnCheck := FunDef.toLocalsProc?_checked hFn
              have hRestCheck := FunList.toLocalsProcs?_checked hRest
              simp [hFnCheck, hRestCheck]

theorem Program.toLocals?_checked {program : Program} {lower : Locals.Program}
    (hLower : Program.toLocals? program = some lower) :
    Checked.Program.check? program = true := by
  simp only [Program.toLocals?, Checked.Program.check?] at hLower ⊢
  cases hProcs : FunList.toLocalsProcs? program.functions with
  | none =>
      simp [hProcs] at hLower
  | some lowerProcs =>
      cases hBody : Block.toLocals? [] {} [] [] program.body with
      | none =>
          simp [hProcs, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨lowerBody, bodyLayout⟩
          simp [hProcs, hBody] at hLower
          cases hLower
          have hProcsCheck := FunList.toLocalsProcs?_checked hProcs
          have hBodyCheck := Block.toLocals?_checked hBody
          simp [hProcsCheck, hBodyCheck]

theorem Program.toLocalsNoInternalCall?_eq_some {program : Program}
    {lower : Locals.Program}
    (hLower : Program.toLocalsNoInternalCall? program = some lower) :
    EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Program.toLocals? program = some lower := by
  unfold Program.toLocalsNoInternalCall? at hLower
  cases hNoCall :
      EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.check? program with
  | false =>
      simp [hNoCall] at hLower
  | true =>
      have hLiveLower : Program.toLocals? program = some lower := by
        simpa [hNoCall] using hLower
      exact
        ⟨EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.check?_sound
          hNoCall, hLiveLower⟩

theorem Program.toLocalsNoInternalCall?_checked {program : Program}
    {lower : Locals.Program}
    (hLower : Program.toLocalsNoInternalCall? program = some lower) :
    EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Checked.Program.check? program = true := by
  rcases Program.toLocalsNoInternalCall?_eq_some hLower with
    ⟨hNoCall, hLiveLower⟩
  exact ⟨hNoCall, Program.toLocals?_checked hLiveLower⟩

theorem Program.toExpressions?_checked {program : Program}
    {lower : Expressions.Program}
    (hLower : Program.toExpressions? program = some lower) :
    Checked.Program.check? program = true := by
  unfold Program.toExpressions? at hLower
  cases hLocals : Program.toLocals? program with
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      exact Program.toLocals?_checked hLocals

theorem Program.toExpressionsNoInternalCall?_eq_some {program : Program}
    {lower : Expressions.Program}
    (hLower : Program.toExpressionsNoInternalCall? program = some lower) :
    ∃ locals : Locals.Program,
      Program.toLocalsNoInternalCall? program = some locals ∧
        locals.toExpressions? = some lower := by
  unfold Program.toExpressionsNoInternalCall? at hLower
  cases hLocals : Program.toLocalsNoInternalCall? program with
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      simp [hLocals] at hLower
      exact ⟨locals, rfl, hLower⟩

theorem Program.toExpressionsNoInternalCall?_checked {program : Program}
    {lower : Expressions.Program}
    (hLower : Program.toExpressionsNoInternalCall? program = some lower) :
    EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Checked.Program.check? program = true := by
  rcases Program.toExpressionsNoInternalCall?_eq_some hLower with
    ⟨locals, hLocals, _hExprs⟩
  exact Program.toLocalsNoInternalCall?_checked hLocals

theorem Program.compile?_checked {program : Program}
    {target : Assembly.TargetProgram}
    (hCompile : Program.compile? program = some target) :
    Checked.Program.check? program = true := by
  unfold Program.compile? at hCompile
  cases hLocals : Program.toLocals? program with
  | none =>
      simp [hLocals] at hCompile
  | some locals =>
      exact Program.toLocals?_checked hLocals

theorem Program.compileNoInternalCall?_checked {program : Program}
    {target : Assembly.TargetProgram}
    (hCompile : Program.compileNoInternalCall? program = some target) :
    EvmCompiler.Functions.LiveLayout.NoInternalCall.Program.Holds program ∧
      Checked.Program.check? program = true := by
  unfold Program.compileNoInternalCall? at hCompile
  cases hLocals : Program.toLocalsNoInternalCall? program with
  | none =>
      simp [hLocals] at hCompile
  | some locals =>
      exact Program.toLocalsNoInternalCall?_checked hLocals

theorem cleanupToLive_noCallCreate (layout live : List Name) :
    (cleanupToLive layout live).usesCallCreate = false := by
  rfl

set_option maxHeartbeats 800000 in
mutual
  theorem Block.toLocals?_noCallCreate {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {block : Block} {lower : Locals.Block}
      {outLayout : List Name}
      (hBlock : block.usesCallCreate = false)
      (hLower :
        Block.toLocals? returns ctx layout after block =
          some (lower, outLayout)) :
      lower.usesCallCreate = false := by
    cases block with
    | mk stmts =>
        simp only [Block.toLocals?] at hLower
        cases hList :
            StmtList.toLocals? returns ctx layout after stmts with
        | none =>
            simp [hList] at hLower
        | some result =>
            rcases result with ⟨lowerStmts, listLayout⟩
            simp [hList] at hLower
            rcases hLower with ⟨rfl, _hOut⟩
            exact StmtList.toLocals?_noCallCreate
              (by simpa [Block.usesCallCreate] using hBlock) hList

  theorem Stmt.toLocals?_noCallCreate {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {stmt : Stmt}
      {lower : List Locals.Stmt} {outLayout : List Name}
      (hStmt : stmt.usesCallCreate = false)
      (hLower :
        Stmt.toLocals? returns ctx layout after stmt =
          some (lower, outLayout)) :
      Locals.StmtList.usesCallCreate lower = false := by
    cases stmt with
    | expr expr =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns
          (.expr expr) hStmt
    | let_ name value =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns
          (.let_ name value) hStmt
    | assign name value =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns
          (.assign name value) hStmt
    | block body =>
        have hBody : body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp only [Stmt.toLocals?] at hLower
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBodyLower :
            Block.toLocals? returns bodyCtx layout
              (Checked.scopedAfter layout after) body with
        | none =>
            simp [bodyCtx, hBodyLower] at hLower
        | some result =>
            rcases result with ⟨lowerBody, bodyLayout⟩
            simp [bodyCtx, hBodyLower] at hLower
            rcases hLower with ⟨rfl, _hOut⟩
            have hBodyNo :=
              Block.toLocals?_noCallCreate hBody hBodyLower
            simp [Locals.StmtList.usesCallCreate,
              Locals.Stmt.usesCallCreate, hBodyNo]
    | if_ cond body =>
        have hParts :
            cond.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate] using hStmt
        simp only [Stmt.toLocals?] at hLower
        let bodyCtx := ctx.withProtectedLayout layout
        cases hBodyLower :
            Block.toLocals? returns bodyCtx layout
              (Checked.scopedAfter layout after) body with
        | none =>
            simp [bodyCtx, hBodyLower] at hLower
        | some result =>
            rcases result with ⟨lowerBody, bodyLayout⟩
            simp [bodyCtx, hBodyLower] at hLower
            rcases hLower with ⟨rfl, _hOut⟩
            have hBodyNo :=
              Block.toLocals?_noCallCreate hParts.2 hBodyLower
            simp [Locals.StmtList.usesCallCreate,
              Locals.Stmt.usesCallCreate, hParts.1, hBodyNo]
    | switch scrutinee cases defaultBody =>
        have hParts :
            scrutinee.usesCallCreate = false ∧
              CaseList.usesCallCreate cases = false ∧
                Default.usesCallCreate defaultBody = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        simp only [Stmt.toLocals?] at hLower
        let branchCtx := ctx.withProtectedLayout layout
        cases hCases :
            CaseList.toLocals? returns branchCtx layout
              (Checked.scopedAfter layout after) cases with
        | none =>
            simp [branchCtx, hCases] at hLower
        | some lowerCases =>
            cases hDefault :
                Default.toLocals? returns branchCtx layout
                  (Checked.scopedAfter layout after) defaultBody with
            | none =>
                simp [branchCtx, hCases, hDefault] at hLower
            | some lowerDefault =>
                simp [branchCtx, hCases, hDefault] at hLower
                rcases hLower with ⟨rfl, _hOut⟩
                have hCasesNo :=
                  CaseList.toLocals?_noCallCreate hParts.2.1 hCases
                have hDefaultNo :=
                  Default.toLocals?_noCallCreate hParts.2.2 hDefault
                simp [Locals.StmtList.usesCallCreate,
                  Locals.Stmt.usesCallCreate, hParts.1, hCasesNo,
                  hDefaultNo]
    | for_ init cond post body =>
        have hParts :
            init.usesCallCreate = false ∧ cond.usesCallCreate = false ∧
              post.usesCallCreate = false ∧ body.usesCallCreate = false := by
          simpa [Stmt.usesCallCreate, Bool.or_assoc] using hStmt
        simp only [Stmt.toLocals?] at hLower
        let loopMentioned :=
          NameSet.unions [Reads.expr cond, Reads.block post, Reads.block body,
            after]
        let postLive := Block.liveBefore ctx loopMentioned post
        let bodyCtx := ctx.withLoop after postLive
        let bodyLive := Block.liveBefore bodyCtx postLive body
        let loopLive :=
          NameSet.unions [Reads.expr cond, after, postLive, bodyLive]
        let initAfter := NameSet.union loopLive layout
        let initCtx := ctx.withProtectedLayout layout
        cases hInit :
            Block.toLocals? returns initCtx layout initAfter init with
        | none =>
            simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
              initAfter, initCtx, hInit] at hLower
        | some initResult =>
            rcases initResult with ⟨lowerInit, loopLayout⟩
            cases hCond : ExprAccess.expr? 0 loopLayout cond with
            | false =>
                simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
                  initAfter, initCtx, hInit, hCond] at hLower
            | true =>
                let postAfter := Checked.scopedAfter loopLayout loopMentioned
                let bodyAfter := Checked.scopedAfter loopLayout postLive
                let postCtx := ctx.withProtectedLayout loopLayout
                let bodyLoopCtx :=
                  ctx.withLoop (Checked.scopedAfter loopLayout after) bodyAfter
                let bodyCheckCtx := bodyLoopCtx.withProtectedLayout loopLayout
                cases hPost :
                    Block.toLocals? returns postCtx loopLayout postAfter post with
                | none =>
                    simp [loopMentioned, postLive, bodyCtx, bodyLive, loopLive,
                      initAfter, postAfter, bodyAfter, initCtx, postCtx,
                      bodyLoopCtx, bodyCheckCtx, hInit, hCond, hPost] at hLower
                | some postResult =>
                    rcases postResult with ⟨lowerPost, postLayout⟩
                    cases hBody :
                        Block.toLocals? returns bodyCheckCtx loopLayout
                          bodyAfter body with
                    | none =>
                        simp [loopMentioned, postLive, bodyCtx, bodyLive,
                          loopLive, initAfter, postAfter, bodyAfter, initCtx,
                          postCtx, bodyLoopCtx, bodyCheckCtx, hInit, hCond,
                          hPost, hBody] at hLower
                    | some bodyResult =>
                        rcases bodyResult with ⟨lowerBody, bodyLayout⟩
                        simp [loopMentioned, postLive, bodyCtx, bodyLive,
                          loopLive, initAfter, postAfter, bodyAfter, initCtx,
                          postCtx, bodyLoopCtx, bodyCheckCtx, hInit, hCond,
                          hPost, hBody] at hLower
                        rcases hLower with ⟨rfl, _hOut⟩
                        have hInitNo :=
                          Block.toLocals?_noCallCreate hParts.1 hInit
                        have hPostNo :=
                          Block.toLocals?_noCallCreate hParts.2.2.1 hPost
                        have hBodyNo :=
                          Block.toLocals?_noCallCreate hParts.2.2.2 hBody
                        simp [Locals.StmtList.usesCallCreate,
                          Locals.Stmt.usesCallCreate, hInitNo, hParts.2.1,
                          hPostNo, hBodyNo]
    | brk =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns .brk hStmt
    | cont =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns .cont hStmt
    | leave =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns .leave hStmt
    | call targets functionName args =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns
          (.call targets functionName args) hStmt
    | terminal kind =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns
          (.terminal kind) hStmt
    | terminalArgs kind args =>
        simp [Stmt.toLocals?] at hLower
        rcases hLower with ⟨rfl, _hOut⟩
        exact CompilerFacts.Stmt.toLocals_noCallCreate returns
          (.terminalArgs kind args) hStmt

  theorem StmtList.toLocals?_noCallCreate {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {stmts : List Stmt}
      {lower : List Locals.Stmt} {outLayout : List Name}
      (hStmts : StmtList.usesCallCreate stmts = false)
      (hLower :
        StmtList.toLocals? returns ctx layout after stmts =
          some (lower, outLayout)) :
      Locals.StmtList.usesCallCreate lower = false := by
    cases stmts with
    | nil =>
        simp only [StmtList.toLocals?] at hLower
        cases hEntry : Layout.entryWindowOk? layout after with
        | false =>
            simp [hEntry] at hLower
        | true =>
            simp [hEntry] at hLower
            rcases hLower with ⟨rfl, _hOut⟩
            simp [Locals.StmtList.usesCallCreate,
              Locals.Stmt.usesCallCreate, cleanupToLive_noCallCreate]
    | cons stmt rest =>
        have hParts :
            stmt.usesCallCreate = false ∧
              StmtList.usesCallCreate rest = false := by
          simpa [StmtList.usesCallCreate] using hStmts
        simp only [StmtList.toLocals?] at hLower
        let restLive := StmtList.liveBefore ctx after rest
        let stmtLive := Stmt.liveBefore ctx restLive stmt
        let liveLayout := Layout.trimDeadPrefix layout stmtLive
        cases hPrepare :
            Prepare.forStmtAboveSuffix? ctx.protectedDepth returns liveLayout
              stmtLive stmt with
        | none =>
            simp [restLive, stmtLive, liveLayout, hPrepare] at hLower
        | some prepareResult =>
            rcases prepareResult with ⟨prep, preparedLayout⟩
            cases hStmt :
                Stmt.toLocals? returns ctx preparedLayout
                  restLive stmt with
            | none =>
                simp [restLive, stmtLive, liveLayout, hPrepare, hStmt]
                  at hLower
            | some stmtResult =>
                rcases stmtResult with ⟨lowerStmt, nextLayout⟩
                cases hRest :
                    StmtList.toLocals? returns ctx nextLayout after rest with
                | none =>
                    simp [restLive, stmtLive, liveLayout, hPrepare, hStmt,
                      hRest] at hLower
                | some restResult =>
                    rcases restResult with ⟨lowerRest, finalLayout⟩
                    simp [restLive, stmtLive, liveLayout, hPrepare, hStmt,
                      hRest] at hLower
                    rcases hLower with ⟨rfl, _hOut⟩
                    have hPrepNo :=
                      Prepare.forStmtAboveSuffix?_noCallCreate hPrepare
                    have hStmtNo :=
                      Stmt.toLocals?_noCallCreate hParts.1 hStmt
                    have hRestNo :=
                      StmtList.toLocals?_noCallCreate hParts.2 hRest
                    have hStmtRestNo :
                        Locals.StmtList.usesCallCreate
                          (lowerStmt ++ lowerRest) = false :=
                      CompilerFacts.Locals.StmtList.usesCallCreate_append_eq_false
                        hStmtNo hRestNo
                    have hTailNo :
                        Locals.StmtList.usesCallCreate
                          (prep ++ (lowerStmt ++ lowerRest)) = false :=
                      CompilerFacts.Locals.StmtList.usesCallCreate_append_eq_false
                        hPrepNo hStmtRestNo
                    simp [Locals.StmtList.usesCallCreate,
                      Locals.Stmt.usesCallCreate, cleanupToLive_noCallCreate,
                      hTailNo]

  theorem CaseList.toLocals?_noCallCreate {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {cases : List (Word × Block)}
      {lower : List (Word × Locals.Block)}
      (hCases : CaseList.usesCallCreate cases = false)
      (hLower :
        CaseList.toLocals? returns ctx layout after cases = some lower) :
      Locals.CaseList.usesCallCreate lower = false := by
    cases cases with
    | nil =>
        simp [CaseList.toLocals?] at hLower
        subst lower
        rfl
    | cons head rest =>
        rcases head with ⟨value, body⟩
        have hParts :
            body.usesCallCreate = false ∧
              CaseList.usesCallCreate rest = false := by
          simpa [CaseList.usesCallCreate] using hCases
        simp only [CaseList.toLocals?] at hLower
        cases hBody : Block.toLocals? returns ctx layout after body with
        | none =>
            simp [hBody] at hLower
        | some bodyResult =>
            rcases bodyResult with ⟨lowerBody, bodyLayout⟩
            cases hRest : CaseList.toLocals? returns ctx layout after rest with
            | none =>
                simp [hBody, hRest] at hLower
            | some lowerRest =>
                simp [hBody, hRest] at hLower
                rcases hLower with ⟨rfl⟩
                have hBodyNo :=
                  Block.toLocals?_noCallCreate hParts.1 hBody
                have hRestNo :=
                  CaseList.toLocals?_noCallCreate hParts.2 hRest
                simp [Locals.CaseList.usesCallCreate, hBodyNo, hRestNo]

  theorem Default.toLocals?_noCallCreate {returns : List Name} {ctx : Ctx}
      {layout after : List Name} {defaultBody : Option Block}
      {lower : Option Locals.Block}
      (hDefault : Default.usesCallCreate defaultBody = false)
      (hLower :
        Default.toLocals? returns ctx layout after defaultBody = some lower) :
      Locals.Default.usesCallCreate lower = false := by
    cases defaultBody with
    | none =>
        simp [Default.toLocals?] at hLower
        subst lower
        rfl
    | some body =>
        have hBody : body.usesCallCreate = false := by
          simpa [Default.usesCallCreate] using hDefault
        simp only [Default.toLocals?] at hLower
        cases hLowerBody :
            Block.toLocals? returns ctx layout after body with
        | none =>
            simp [hLowerBody] at hLower
        | some bodyResult =>
            rcases bodyResult with ⟨lowerBody, bodyLayout⟩
            simp [hLowerBody] at hLower
            rcases hLower with ⟨rfl⟩
            exact Block.toLocals?_noCallCreate hBody hLowerBody
end

theorem FunDef.toLocalsProc?_noCallCreate {fn : FunDef}
    {proc : Locals.Proc}
    (hFn : fn.usesCallCreate = false)
    (hLower : FunDef.toLocalsProc? fn = some proc) :
    proc.usesCallCreate = false := by
  rcases fn with ⟨name, params, returns, body⟩
  simp only [FunDef.toLocalsProc?] at hLower
  cases hBody :
      Block.toLocals? returns { returns := returns }
        (returns.reverse ++ params.reverse) returns body with
  | none =>
      simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨lowerBody, layout⟩
      cases hNames : NamesAccess.names? 0 layout returns with
      | false =>
          simp [hBody, hNames] at hLower
      | true =>
          simp [hBody, hNames] at hLower
          rcases hLower with ⟨rfl⟩
          have hBodyNo :=
            Block.toLocals?_noCallCreate
              (by
                cases body with
                | mk stmts =>
                    simpa [FunDef.usesCallCreate, Block.usesCallCreate]
                      using hFn)
              hBody
          have hBodyStmtsNo :
              Locals.StmtList.usesCallCreate lowerBody.stmts = false := by
            cases lowerBody
            simpa [Locals.Block.usesCallCreate] using hBodyNo
          have hInit := CompilerFacts.Lower.initReturns_noCallCreate returns
          have hPush := CompilerFacts.Lower.pushReturns_noCallCreate returns
          simp [Locals.Proc.usesCallCreate, Locals.Block.usesCallCreate]
          exact
            CompilerFacts.Locals.StmtList.usesCallCreate_append_eq_false
              hInit
              (CompilerFacts.Locals.StmtList.usesCallCreate_append_eq_false
                hBodyStmtsNo hPush)

theorem FunList.toLocalsProcs?_noCallCreate :
    ∀ {fns : List FunDef} {procs : List Locals.Proc},
      FunList.usesCallCreate fns = false →
        FunList.toLocalsProcs? fns = some procs →
          Locals.ProcList.usesCallCreate procs = false
  | [], _procs, _hFns, hLower => by
      simp [FunList.toLocalsProcs?] at hLower
      subst _procs
      rfl
  | fn :: rest, _procs, hFns, hLower => by
      have hParts :
          fn.usesCallCreate = false ∧
            FunList.usesCallCreate rest = false := by
        simpa [FunList.usesCallCreate] using hFns
      simp only [FunList.toLocalsProcs?] at hLower
      cases hFn : FunDef.toLocalsProc? fn with
      | none =>
          simp [hFn] at hLower
      | some lowerFn =>
          cases hRest : FunList.toLocalsProcs? rest with
          | none =>
              simp [hFn, hRest] at hLower
          | some lowerRest =>
              simp [hFn, hRest] at hLower
              rcases hLower with ⟨rfl⟩
              have hFnNo :=
                FunDef.toLocalsProc?_noCallCreate hParts.1 hFn
              have hRestNo :=
                FunList.toLocalsProcs?_noCallCreate hParts.2 hRest
              simp [Locals.ProcList.usesCallCreate, hFnNo, hRestNo]

theorem Program.toLocals?_noCallCreate {program : Program}
    {lower : Locals.Program}
    (hProgram : program.usesCallCreate = false)
    (hLower : Program.toLocals? program = some lower) :
    lower.usesCallCreate = false := by
  have hParts :
      FunList.usesCallCreate program.functions = false ∧
        program.body.usesCallCreate = false := by
    simpa [Program.usesCallCreate] using hProgram
  simp only [Program.toLocals?] at hLower
  cases hProcs : FunList.toLocalsProcs? program.functions with
  | none =>
      simp [hProcs] at hLower
  | some lowerProcs =>
      cases hBody : Block.toLocals? [] {} [] [] program.body with
      | none =>
          simp [hProcs, hBody] at hLower
      | some bodyResult =>
          rcases bodyResult with ⟨lowerBody, bodyLayout⟩
          simp [hProcs, hBody] at hLower
          rcases hLower with ⟨rfl⟩
          have hProcsNo :=
            FunList.toLocalsProcs?_noCallCreate hParts.1 hProcs
          have hBodyNo :=
            Block.toLocals?_noCallCreate hParts.2 hBody
          simp [Locals.Program.usesCallCreate, hProcsNo, hBodyNo]

theorem Program.toLocalsNoInternalCall?_noCallCreate {program : Program}
    {lower : Locals.Program}
    (hProgram : program.usesCallCreate = false)
    (hLower : Program.toLocalsNoInternalCall? program = some lower) :
    lower.usesCallCreate = false := by
  rcases Program.toLocalsNoInternalCall?_eq_some hLower with
    ⟨_hNoInternalCall, hLiveLower⟩
  exact Program.toLocals?_noCallCreate hProgram hLiveLower

theorem Program.toExpressionsNoInternalCall?_noCallCreate
    {program : Program} {lower : Expressions.Program}
    (hProgram : program.usesCallCreate = false)
    (hLower : Program.toExpressionsNoInternalCall? program = some lower) :
    lower.usesCallCreate = false := by
  rcases Program.toExpressionsNoInternalCall?_eq_some hLower with
    ⟨locals, hLocals, hExprs⟩
  have hLocalsNo :=
    Program.toLocalsNoInternalCall?_noCallCreate hProgram hLocals
  exact
    Locals.CompilerFacts.Program.toExpressions?_noCallCreate
      locals hLocalsNo hExprs

end Lower

namespace Drop

theorem stackStoreRel_drop {layout : List Name}
    {store : Locals.Source.Store} {stack : EvmYul.Stack Word}
    (hRel : Locals.SourceLowering.StackStoreRel layout store stack)
    (n : Nat) :
    Locals.SourceLowering.StackStoreRel (layout.drop n) store
      (stack.drop n) := by
  rcases hRel with ⟨hLen, hLookup⟩
  constructor
  · simp [hLen]
  · intro idx name hLayout
    have hLayoutAt : layout[n + idx]? = some name := by
      simpa [List.getElem?_drop] using hLayout
    have hStackAt := hLookup hLayoutAt
    simpa [List.getElem?_drop] using hStackAt

theorem stateRel_drop {layout : List Name}
    {source : Locals.Source.State} {target cleaned : Locals.RunState}
    (hRel : Locals.SourceLowering.StateRel layout source target)
    {n : Nat}
    (hShared : cleaned.evm.toSharedState = target.evm.toSharedState)
    (hStack : cleaned.evm.stack = target.evm.stack.drop n) :
    Locals.SourceLowering.StateRel (layout.drop n) source cleaned := by
  rcases hRel with ⟨hSharedRel, hStackRel⟩
  constructor
  · simpa [hShared] using hSharedRel
  · rw [hStack]
    exact stackStoreRel_drop hStackRel n

theorem cleanupTo_stateRel_drop {ctx : Locals.Ctx}
    {targetDepth : Nat}
    {source : Locals.Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx targetDepth target = .ok cleaned)
    (hRel : Locals.SourceLowering.StateRel ctx.layout source target) :
    Locals.SourceLowering.StateRel
        (ctx.layout.drop (ctx.layout.length - targetDepth)) source cleaned ∧
      cleaned.returns = target.returns := by
  rcases Locals.Direct.Ctx.runCleanupTo_stack_drop hRun with
    ⟨_hDepth, hStack, hShared, hReturns⟩
  exact ⟨stateRel_drop hRel hShared hStack, hReturns⟩

theorem cleanupTo_trimDeadPrefix_stateRel {ctx : Locals.Ctx}
    {live : List Name}
    {source : Locals.Source.State} {target cleaned : Locals.RunState}
    (hRun :
      Locals.Direct.Ctx.runCleanupTo ctx
          (Layout.trimDeadPrefix ctx.layout live).length target =
        .ok cleaned)
    (hRel : Locals.SourceLowering.StateRel ctx.layout source target) :
    Locals.SourceLowering.StateRel
        (Layout.trimDeadPrefix ctx.layout live) source cleaned ∧
      cleaned.returns = target.returns := by
  rcases cleanupTo_stateRel_drop hRun hRel with ⟨hState, hReturns⟩
  have hDrop :
      ctx.layout.drop
          (ctx.layout.length -
            (Layout.trimDeadPrefix ctx.layout live).length) =
        Layout.trimDeadPrefix ctx.layout live := by
    rw [Layout.length_sub_trimDeadPrefix_eq_count,
      Layout.drop_trimDeadPrefixCount_eq_trimDeadPrefix]
  exact ⟨by simpa [hDrop] using hState, hReturns⟩

end Drop

namespace Examples

def lit0 : Expr 1 :=
  .lit (EvmYul.UInt256.ofNat 0)

def popVar (name : Name) : Stmt :=
  .expr (.prim .pop (Locals.ExprSeq.cons (.var name) .nil))

example :
    Layout.allAccessible?
      0
      (List.replicate 17 "dead" ++ ["x"]) ["x"] = false := by
  native_decide

example :
    Layout.entryWindowOk?
      (List.replicate 17 "dead" ++ ["x"]) ["x"] = true := by
  native_decide

example :
    ExprAccess.expr? 0 (List.replicate 20 "dead")
      (.lit (EvmYul.UInt256.ofNat 0)) = true := by
  native_decide

example :
    ExprAccess.expr? 0 (List.replicate 17 "dead" ++ ["x"])
      (.var "x") = false := by
  native_decide

example :
    ExprAccess.expr? 0
      (Layout.trimDeadPrefix (List.replicate 17 "dead" ++ ["x"]) ["x"])
      (.var "x") = true := by
  native_decide

def manyDeadProgram : Program :=
  { functions := []
    body :=
      { stmts :=
          [ .let_ "x" lit0
          , .let_ "d0" lit0
          , .let_ "d1" lit0
          , .let_ "d2" lit0
          , .let_ "d3" lit0
          , .let_ "d4" lit0
          , .let_ "d5" lit0
          , .let_ "d6" lit0
          , .let_ "d7" lit0
          , .let_ "d8" lit0
          , .let_ "d9" lit0
          , .let_ "d10" lit0
          , .let_ "d11" lit0
          , .let_ "d12" lit0
          , .let_ "d13" lit0
          , .let_ "d14" lit0
          , .let_ "d15" lit0
          , .let_ "d16" lit0
          , popVar "x" ] } }

example :
    Checked.Program.check? manyDeadProgram = true := by
  native_decide

example :
    (Lower.Program.toLocals? manyDeadProgram).isSome = true := by
  native_decide

example :
    (Lower.Program.toExpressions? manyDeadProgram).isSome = true := by
  native_decide

example :
    Checked.Program.check?
      { functions := []
        body :=
          { stmts :=
              [ .let_ "x" lit0
              , .let_ "d0" lit0
              , .let_ "d1" lit0
              , .let_ "d2" lit0
              , .let_ "d3" lit0
              , .let_ "d4" lit0
              , .let_ "d5" lit0
              , .let_ "d6" lit0
              , .let_ "d7" lit0
              , .let_ "d8" lit0
              , .let_ "d9" lit0
              , .let_ "d10" lit0
              , .let_ "d11" lit0
              , .let_ "d12" lit0
              , .let_ "d13" lit0
              , .let_ "d14" lit0
              , .let_ "d15" lit0
              , popVar "x"
              , popVar "d0"
              , popVar "d1"
              , popVar "d2"
              , popVar "d3"
              , popVar "d4"
              , popVar "d5"
              , popVar "d6"
              , popVar "d7"
              , popVar "d8"
              , popVar "d9"
              , popVar "d10"
              , popVar "d11"
              , popVar "d12"
              , popVar "d13"
              , popVar "d14"
              , popVar "d15" ] } } = false := by
  native_decide

example :
    FunDef.entryLive
      { name := "f"
        params := ["x"]
        returns := []
        body :=
          { stmts :=
              [ .let_ "dead" (.lit (EvmYul.UInt256.ofNat 0))
              , .expr (.prim .pop
                  (Locals.ExprSeq.cons (.var "x") .nil)) ] } } =
      ["x"] := by
  native_decide

end Examples

end LiveLayout
end Functions
end EvmCompiler
