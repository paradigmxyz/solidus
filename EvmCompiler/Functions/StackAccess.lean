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

namespace Examples

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
