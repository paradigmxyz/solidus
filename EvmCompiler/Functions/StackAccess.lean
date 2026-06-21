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

def assign? (layout : Locals.Layout) (name : Name)
    (value : Functions.Expr 1) : Option Unit := do
  let _ ← Expr.check? layout 0 value
  let depth ← Locals.Layout.lookupDepth? name layout
  let _ ← Locals.StackOp.swap? depth
  some ()

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
