import EvmCompiler.Objects.Syntax
import EvmCompiler.Assembly.Syntax
import EvmYul.Yul.Ast

namespace EvmCompiler
namespace Yul

-- `Word` is rebased directly onto the frozen `Assembly.Word` (both are the
-- `EvmYul.UInt256` abbrev; the old `Objects.Word` alias chained through mutable
-- files, letting `Objects.Word` escape the freeze cone). Definitionally identical.
abbrev Word := Assembly.Word
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
