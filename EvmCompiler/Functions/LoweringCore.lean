import EvmCompiler.Functions.SourceSemantics
import EvmCompiler.Locals.Syntax

namespace EvmCompiler
namespace Functions

namespace FunList

abbrev find? := Source.FunList.find?

end FunList

namespace Lower

def bindEntryLayout (layout : Locals.Layout) : Locals.Stmt :=
  .expr
    (Locals.Expr.code (results := 0)
      [Structured.BasicInstr.bindLocals 0 layout])

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def argExprs : (args : List (Expr 1)) → Locals.ExprSeq args.length
  | [] => .nil
  | arg :: rest =>
      by
        simpa [Nat.add_comm] using
          (Locals.ExprSeq.cons (left := 1) (right := rest.length)
            arg (argExprs rest))

def evalArgs : List (Expr 1) → List Locals.Stmt
  | [] => []
  | arg :: rest => [Locals.Stmt.exprs (argExprs (arg :: rest))]

def returnExprs : (names : List Name) → Locals.ExprSeq names.length
  | [] => .nil
  | name :: rest =>
      by
        simpa [Nat.add_comm] using
          (Locals.ExprSeq.cons (left := 1) (right := rest.length)
            (.var name) (returnExprs rest))

def pushReturns : List Name → List Locals.Stmt
  | [] => []
  | name :: rest => [Locals.Stmt.exprs (returnExprs (name :: rest))]

def initReturns : List Name → List Locals.Stmt
  | [] => []
  | name :: rest => Locals.Stmt.let_ name (.lit zero) :: initReturns rest

def assignReturnedTopsRev : List Name → List Locals.Stmt
  | [] => []
  | name :: rest =>
      Locals.Stmt.assignTopWithOffset rest.length name ::
        assignReturnedTopsRev rest

def assignReturnedTops (targets : List Name) : List Locals.Stmt :=
  assignReturnedTopsRev targets.reverse

end Lower
end Functions
end EvmCompiler
