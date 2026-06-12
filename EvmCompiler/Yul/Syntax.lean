import EvmCompiler.Objects.Syntax
import EvmYul.Yul.Ast

namespace EvmCompiler
namespace Yul

abbrev Word := Objects.Word
abbrev EVMState := Objects.EVMState
abbrev EVMException := Objects.EVMException
abbrev Name := Objects.Name
abbrev AstExpr := EvmYul.Yul.Ast.Expr
abbrev AstStmt := EvmYul.Yul.Ast.Stmt
abbrev AstFunctionDefinition := EvmYul.Yul.Ast.FunctionDefinition
abbrev AstContract := EvmYul.Yul.Ast.YulContract

structure Program where
  contract : AstContract
  memoryContract : MemoryContract.Contract :=
    MemoryContract.unrestricted

end Yul
end EvmCompiler
