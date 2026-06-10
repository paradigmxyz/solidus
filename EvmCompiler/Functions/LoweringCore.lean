import EvmCompiler.Functions.Syntax
import EvmCompiler.Locals.Syntax

namespace EvmCompiler
namespace Functions

namespace FunList

def find? (name : Name) : List FunDef → Option FunDef
  | [] => none
  | fn :: rest =>
      if fn.name = name then
        some fn
      else
        find? name rest

end FunList

namespace Lower

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
