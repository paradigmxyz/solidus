import EvmCompiler.Structured.Syntax

namespace EvmCompiler
namespace Structured
namespace InteractionStaticCost

/-!
Source-owned upper bounds for the number of TypedCfg control blocks needed to
realize one Structured execution. Every recursive source-control edge consumes
one unit of Structured fuel, so calls and loop iterations recurse only at a
strictly smaller index.
-/

structure LevelCost where
  block : Structured.Block -> Nat
  stmt : Structured.Stmt -> Nat
  loop : Structured.Code -> Structured.Block -> Structured.Block -> Nat

def levelCost (program : Structured.Program) : Nat -> LevelCost
  | 0 =>
      { block := fun _ => 0
        stmt := fun
          | .code _ | .brk | .cont | .leave | .terminal _ => 1
          | .if_ _ _ | .switch _ _ _ | .for_ _ _ _ _ | .call _ => 0
        loop := fun _ _ _ => 0 }
  | fuel + 1 =>
      let previous := levelCost program fuel
      { block := fun
          | ⟨[]⟩ => 1
          | ⟨stmt :: rest⟩ => previous.stmt stmt + previous.block ⟨rest⟩
        stmt := fun
          | .code _ => 1
          | .if_ _ body => 1 + previous.block body
          | .switch _ cases defaultBody =>
              1 +
                (max
                  (cases.foldr
                    (fun entry current =>
                      max (previous.block entry.2) current)
                    0)
                  (match defaultBody with
                  | none => 0
                  | some body => previous.block body) +
                cases.length + 1)
          | .for_ init cond post body =>
              previous.block init + previous.loop cond post body
          | .brk | .cont | .leave | .terminal _ => 1
          | .call _ =>
              3 +
                program.procs.foldr
                  (fun proc current =>
                    max (previous.block proc.body) current)
                  0
        loop := fun cond post body =>
          1 + previous.block body + previous.block post +
            previous.loop cond post body }

def blockBudget (program : Structured.Program) (fuel : Nat)
    (block : Structured.Block) : Nat :=
  (levelCost program fuel).block block

def stmtBudget (program : Structured.Program) (fuel : Nat)
    (stmt : Structured.Stmt) : Nat :=
  (levelCost program fuel).stmt stmt

def loopBudget (program : Structured.Program) (fuel : Nat)
    (cond : Structured.Code) (post body : Structured.Block) : Nat :=
  (levelCost program fuel).loop cond post body

def switchBodyBudget (program : Structured.Program) (fuel : Nat)
    (cases : List (Prod Word Structured.Block))
    (defaultBody : Option Structured.Block) : Nat :=
  max
    (cases.foldr
      (fun entry current =>
        max (blockBudget program fuel entry.2) current)
      0)
    (match defaultBody with
    | none => 0
    | some body => blockBudget program fuel body)

def procBodyBudget (program : Structured.Program) (fuel : Nat) : Nat :=
  program.procs.foldr
    (fun proc current =>
      max (blockBudget program fuel proc.body) current)
      0

@[simp] theorem stmtBudget_code
    (program : Structured.Program) (fuel : Nat) (code : Structured.Code) :
    stmtBudget program fuel (.code code) = 1 := by
  cases fuel <;> simp [stmtBudget, levelCost]

@[simp] theorem stmtBudget_brk
    (program : Structured.Program) (fuel : Nat) :
    stmtBudget program fuel .brk = 1 := by
  cases fuel <;> simp [stmtBudget, levelCost]

@[simp] theorem stmtBudget_cont
    (program : Structured.Program) (fuel : Nat) :
    stmtBudget program fuel .cont = 1 := by
  cases fuel <;> simp [stmtBudget, levelCost]

@[simp] theorem stmtBudget_leave
    (program : Structured.Program) (fuel : Nat) :
    stmtBudget program fuel .leave = 1 := by
  cases fuel <;> simp [stmtBudget, levelCost]

@[simp] theorem stmtBudget_terminal
    (program : Structured.Program) (fuel : Nat)
    (kind : Assembly.HaltKind) :
    stmtBudget program fuel (.terminal kind) = 1 := by
  cases fuel <;> simp [stmtBudget, levelCost]

@[simp] theorem blockBudget_zero
    (program : Structured.Program) (block : Structured.Block) :
    blockBudget program 0 block = 0 := by
  simp [blockBudget, levelCost]

@[simp] theorem blockBudget_nil_succ
    (program : Structured.Program) (fuel : Nat) :
    blockBudget program (Nat.succ fuel) ⟨[]⟩ = 1 := by
  simp [blockBudget, levelCost]

@[simp] theorem blockBudget_cons_succ
    (program : Structured.Program) (fuel : Nat)
    (stmt : Structured.Stmt) (rest : List Structured.Stmt) :
    blockBudget program (Nat.succ fuel) ⟨stmt :: rest⟩ =
      stmtBudget program fuel stmt + blockBudget program fuel ⟨rest⟩ := by
  simp [blockBudget, stmtBudget, levelCost]

@[simp] theorem stmtBudget_if_succ
    (program : Structured.Program) (fuel : Nat)
    (cond : Structured.Code) (body : Structured.Block) :
    stmtBudget program (Nat.succ fuel) (.if_ cond body) =
      1 + blockBudget program fuel body := by
  simp [stmtBudget, blockBudget, levelCost]

@[simp] theorem stmtBudget_switch_succ
    (program : Structured.Program) (fuel : Nat)
    (scrutinee : Structured.Code)
    (cases : List (Prod Word Structured.Block))
    (defaultBody : Option Structured.Block) :
    stmtBudget program (Nat.succ fuel)
        (.switch scrutinee cases defaultBody) =
      1 + (switchBodyBudget program fuel cases defaultBody +
        cases.length + 1) := by
  simp [stmtBudget, levelCost, switchBodyBudget, blockBudget]

@[simp] theorem stmtBudget_call_succ
    (program : Structured.Program) (fuel : Nat) (name : Structured.Name) :
    stmtBudget program (Nat.succ fuel) (.call name) =
      3 + procBodyBudget program fuel := by
  simp [stmtBudget, levelCost, procBodyBudget, blockBudget]

@[simp] theorem stmtBudget_for_succ
    (program : Structured.Program) (fuel : Nat)
    (init : Structured.Block) (cond : Structured.Code)
    (post body : Structured.Block) :
    stmtBudget program (Nat.succ fuel) (.for_ init cond post body) =
      blockBudget program fuel init +
        loopBudget program fuel cond post body := by
  simp [stmtBudget, blockBudget, loopBudget, levelCost]

@[simp] theorem loopBudget_zero
    (program : Structured.Program) (cond : Structured.Code)
    (post body : Structured.Block) :
    loopBudget program 0 cond post body = 0 := by
  simp [loopBudget, levelCost]

@[simp] theorem loopBudget_succ
    (program : Structured.Program) (fuel : Nat)
    (cond : Structured.Code) (post body : Structured.Block) :
    loopBudget program (Nat.succ fuel) cond post body =
      1 + blockBudget program fuel body +
        blockBudget program fuel post +
          loopBudget program fuel cond post body := by
  simp [loopBudget, blockBudget, levelCost]

theorem blockBudget_le_switchBodyBudget_of_mem
    {program : Structured.Program} {fuel : Nat}
    {cases : List (Prod Word Structured.Block)}
    {defaultBody : Option Structured.Block}
    {value : Word} {body : Structured.Block}
    (hMem : (value, body) ∈ cases) :
    blockBudget program fuel body <=
      switchBodyBudget program fuel cases defaultBody := by
  apply Nat.le_trans _ (Nat.le_max_left _ _)
  induction cases with
  | nil => simp at hMem
  | cons head rest ih =>
      simp only [List.mem_cons] at hMem
      simp only [List.foldr]
      cases hMem with
      | inl hHead =>
          cases hHead
          exact Nat.le_max_left _ _
      | inr hRest =>
          exact Nat.le_trans (ih hRest) (Nat.le_max_right _ _)

theorem blockBudget_le_switchBodyBudget_of_default
    {program : Structured.Program} {fuel : Nat}
    {cases : List (Prod Word Structured.Block)}
    {body : Structured.Block} :
    blockBudget program fuel body <=
      switchBodyBudget program fuel cases (some body) := by
  exact Nat.le_max_right _ _

theorem blockBudget_le_procBodyBudget_of_lookup
    {program : Structured.Program} {fuel : Nat}
    {name : Structured.Name} {proc : Structured.Proc}
    (hLookup : Structured.ProcList.lookup? name program.procs = some proc) :
    blockBudget program fuel proc.body <= procBodyBudget program fuel := by
  unfold procBodyBudget
  have listBound :
      forall procs,
        Structured.ProcList.lookup? name procs = some proc ->
          blockBudget program fuel proc.body <=
            procs.foldr
              (fun item current =>
                max (blockBudget program fuel item.body) current)
              0 := by
    intro procs hFound
    induction procs with
    | nil => simp [Structured.ProcList.lookup?] at hFound
    | cons head rest ih =>
        unfold Structured.ProcList.lookup? at hFound
        by_cases hName : head.name = name
        · simp [hName] at hFound
          cases hFound
          exact Nat.le_max_left _ _
        · simp [hName] at hFound
          exact Nat.le_trans (ih hFound) (Nat.le_max_right _ _)
  exact listBound program.procs hLookup

end InteractionStaticCost
end Structured
end EvmCompiler
