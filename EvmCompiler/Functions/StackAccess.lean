import EvmCompiler.Functions.LoweringCore
import EvmCompiler.Locals.StackModel

/-!
Checked top-16 accessibility for stack-only Functions lowering.

This owner knows symbolic layouts and EVM `DUP`/`SWAP` limits, but emits no
code and imports no compiler or effect semantics.
-/

namespace EvmCompiler
namespace Functions
namespace StackAccess

mutual
  def Expr.check? {results : Nat} (layout : Locals.Layout)
      (offset : Nat) : Functions.Expr results → Option Unit
    | .lit _ => some ()
    | .var name => do
        let depth ← Locals.Layout.lookupDepth? name layout
        let _ ← Locals.StackOp.dup? (offset + depth)
        some ()
    | .code _ => some ()
    | .prim _ args => ExprSeq.check? layout offset args

  def ExprSeq.check? {results : Nat} (layout : Locals.Layout)
      (offset : Nat) : Locals.ExprSeq results → Option Unit
    | .nil => some ()
    | .cons (left := left) head tail => do
        let _ ← Expr.check? layout offset head
        ExprSeq.check? layout (offset + left) tail
end

mutual
  def Expr.firstFailure? {results : Nat} (layout : Locals.Layout)
      (offset : Nat) : Functions.Expr results → Option (Name × Nat × Nat)
    | .lit _ | .code _ => none
    | .var name =>
        match Locals.Layout.lookupDepth? name layout with
        | none => some (name, offset, 0)
        | some depth =>
            if (Locals.StackOp.dup? (offset + depth)).isSome then none
            else some (name, offset, depth)
    | .prim _ args => ExprSeq.firstFailure? layout offset args

  def ExprSeq.firstFailure? {results : Nat} (layout : Locals.Layout)
      (offset : Nat) : Locals.ExprSeq results → Option (Name × Nat × Nat)
    | .nil => none
    | .cons (left := left) head tail =>
        match Expr.firstFailure? layout offset head with
        | some failure => some failure
        | none => ExprSeq.firstFailure? layout (offset + left) tail
end

def insertAccess (access : Name × Nat) : List (Name × Nat) → List (Name × Nat)
  | [] => [access]
  | head :: rest =>
      if head.2 < access.2 then access :: head :: rest
      else head :: insertAccess access rest

def sortAccesses (accesses : List (Name × Nat)) : List (Name × Nat) :=
  accesses.foldl (fun sorted access => insertAccess access sorted) []

def uniqueNames : List Name → List Name
  | [] => []
  | name :: rest =>
      name :: (uniqueNames rest).filter fun candidate => decide (candidate ≠ name)

mutual
  def Expr.accesses {results : Nat} (offset : Nat) :
      Functions.Expr results → List (Name × Nat)
    | .lit _ | .code _ => []
    | .var name => [(name, offset)]
    | .prim _ args => ExprSeq.accesses offset args

  def ExprSeq.accesses {results : Nat} (offset : Nat) :
      Locals.ExprSeq results → List (Name × Nat)
    | .nil => []
    | .cons (left := left) head tail =>
        Expr.accesses offset head ++ ExprSeq.accesses (offset + left) tail
end

def Expr.accessPriority {results : Nat}
    (expr : Functions.Expr results) : List Name :=
  uniqueNames ((sortAccesses (Expr.accesses 0 expr)).map Prod.fst)

def ExprSeq.accessPriority {results : Nat}
    (exprs : Locals.ExprSeq results) : List Name :=
  uniqueNames ((sortAccesses (ExprSeq.accesses 0 exprs)).map Prod.fst)

mutual
  theorem Expr.scoped_of_check
      {results : Nat} {layout sourceEnv : Locals.Layout} {offset : Nat}
      {expr : Functions.Expr results}
      (hCheck : Expr.check? layout offset expr = some ())
      (hScoped : Functions.Scope.ExprScoped sourceEnv expr) :
      Locals.Scope.ExprScoped layout expr := by
    cases expr with
    | lit value => trivial
    | var name =>
        simp only [Expr.check?] at hCheck
        obtain ⟨depth, hDepth, _hAccessible⟩ :=
          Option.bind_eq_some_iff.mp hCheck
        exact Locals.Layout.mem_of_lookupDepth?_eq_some hDepth
    | code code => exact False.elim hScoped
    | prim op args =>
        exact ExprSeq.scoped_of_check hCheck hScoped

  theorem ExprSeq.scoped_of_check
      {results : Nat} {layout sourceEnv : Locals.Layout} {offset : Nat}
      {exprs : Locals.ExprSeq results}
      (hCheck : ExprSeq.check? layout offset exprs = some ())
      (hScoped : Functions.Scope.ExprSeqScoped sourceEnv exprs) :
      Locals.Scope.ExprSeqScoped layout exprs := by
    cases exprs with
    | nil => trivial
    | @cons left right head tail =>
        simp only [ExprSeq.check?] at hCheck
        obtain ⟨_unit, hHead, hTail⟩ :=
          Option.bind_eq_some_iff.mp hCheck
        exact
          ⟨Expr.scoped_of_check hHead hScoped.1,
            ExprSeq.scoped_of_check hTail hScoped.2⟩
end

def assign? (layout : Locals.Layout) (name : Name)
    (value : Functions.Expr 1) : Option Unit := do
  let _ ← Expr.check? layout 0 value
  let depth ← Locals.Layout.lookupDepth? name layout
  let _ ← Locals.StackOp.swap? depth
  some ()

theorem assign_components
    {layout : Locals.Layout} {name : Name} {value : Functions.Expr 1}
    (hCheck : assign? layout name value = some ()) :
    ∃ depth swap,
      Expr.check? layout 0 value = some () ∧
        Locals.Layout.lookupDepth? name layout = some (depth + 1) ∧
        Locals.StackOp.swap? (depth + 1) = some swap := by
  unfold assign? at hCheck
  obtain ⟨_unit, hValue, hAfterValue⟩ :=
    Option.bind_eq_some_iff.mp hCheck
  obtain ⟨rawDepth, hDepth, hAfterDepth⟩ :=
    Option.bind_eq_some_iff.mp hAfterValue
  obtain ⟨swap, hSwap, _hDone⟩ :=
    Option.bind_eq_some_iff.mp hAfterDepth
  cases rawDepth with
  | zero => simp [Locals.StackOp.swap?] at hSwap
  | succ depth => exact ⟨depth, swap, hValue, hDepth, hSwap⟩

def assignTopWithOffset? (layout : Locals.Layout)
    (offset : Nat) (name : Name) : Option Unit := do
  let depth ← Locals.Layout.lookupDepth? name layout
  let _ ← Locals.StackOp.swap? (offset + depth)
  some ()

def returnedTargetsRev? (layout : Locals.Layout) :
    List Name → Option Unit
  | [] => some ()
  | name :: rest => do
      let _ ← assignTopWithOffset? layout rest.length name
      returnedTargetsRev? layout rest

def returnedTargets? (layout : Locals.Layout)
    (targets : List Name) : Option Unit :=
  returnedTargetsRev? layout targets.reverse

def call? (layout : Locals.Layout) (targets : List Name)
    (args : List (Functions.Expr 1)) : Option Unit := do
  let _ ← ExprSeq.check? layout 0 (Lower.argExprs args)
  returnedTargets? layout targets

namespace Stmt

def accessPriority : Functions.Stmt → List Name
  | .expr expr | .let_ _ expr => Expr.accessPriority expr
  | .assign name expr => Expr.accessPriority expr ++ [name]
  | .if_ condition _ | .for_ _ condition _ _ =>
      Expr.accessPriority condition
  | .switch scrutinee _ _ => Expr.accessPriority scrutinee
  | .call targets _ args =>
      ExprSeq.accessPriority (Lower.argExprs args) ++ targets.reverse
  | .terminalArgs _ args => ExprSeq.accessPriority args
  | .block _ | .brk | .cont | .leave | .terminal _ => []

/-- Check the accesses performed at the current statement boundary. Nested
statements whose relevant expression executes only after a child region are
left to the region scheduler. -/
def check? (layout : Locals.Layout) : Functions.Stmt -> Option Unit
  | .expr expr => Expr.check? layout 0 expr
  | .let_ _ value => Expr.check? layout 0 value
  | .assign name value => assign? layout name value
  | .if_ condition _ => Expr.check? layout 0 condition
  | .switch scrutinee _ _ => Expr.check? layout 0 scrutinee
  | .for_ _ _ _ _ => none
  | .call targets _ args => call? layout targets args
  | .terminal _ => some ()
  | .terminalArgs _ args => ExprSeq.check? layout 0 args
  | .block _ | .brk | .cont | .leave => none

end Stmt

theorem assignTopWithOffset_mem
    {layout : Locals.Layout} {offset : Nat} {name : Name}
    (hCheck : assignTopWithOffset? layout offset name = some ()) :
    name ∈ layout := by
  unfold assignTopWithOffset? at hCheck
  cases hDepth : Locals.Layout.lookupDepth? name layout with
  | none => simp [hDepth] at hCheck
  | some depth => exact Locals.Layout.mem_of_lookupDepth?_eq_some hDepth

theorem returnedTargetsRev_mem :
    ∀ {layout : Locals.Layout} {targets : List Name},
      returnedTargetsRev? layout targets = some () →
      ∀ name, name ∈ targets → name ∈ layout
  | layout, [], hCheck, name, hMem => by simp at hMem
  | layout, head :: rest, hCheck, name, hMem => by
      simp only [returnedTargetsRev?] at hCheck
      obtain ⟨_unit, hHead, hTail⟩ := Option.bind_eq_some_iff.mp hCheck
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hMem
      · exact assignTopWithOffset_mem hHead
      · exact returnedTargetsRev_mem hTail name hMem

theorem returnedTargets_mem
    {layout : Locals.Layout} {targets : List Name}
    (hCheck : returnedTargets? layout targets = some ()) :
    ∀ name, name ∈ targets → name ∈ layout := by
  intro name hMem
  apply returnedTargetsRev_mem hCheck name
  simpa using hMem

theorem call_targets_mem
    {layout : Locals.Layout} {targets : List Name}
    {args : List (Functions.Expr 1)}
    (hCheck : call? layout targets args = some ()) :
    ∀ name, name ∈ targets → name ∈ layout := by
  unfold call? at hCheck
  obtain ⟨_unit, _hArgs, hTargets⟩ := Option.bind_eq_some_iff.mp hCheck
  exact returnedTargets_mem hTargets

namespace Examples

def offsetPriorityExpr : Functions.Expr 1 :=
  .prim .add
    (.cons (.var "shallow") (.cons (.var "deep") .nil))

theorem larger_evaluation_offset_is_prioritized :
    Expr.accessPriority offsetPriorityExpr = ["deep", "shallow"] := by
  decide

theorem top16_accessible :
    Expr.check? ((List.range 16).map fun index => toString index)
      0 (.var "15") = some () := by
  decide

theorem below_top16_rejected :
    Expr.check? ((List.range 17).map fun index => toString index)
      0 (.var "16") = none := by
  decide

end Examples

end StackAccess
end Functions
end EvmCompiler
