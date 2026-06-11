import EvmCompiler.Structured.Semantics

namespace EvmCompiler
namespace Structured

abbrev LabelSupply := Nat

namespace LabelSupply

def label (supply : LabelSupply) (tag : Nat) : Assembly.Label :=
  Assembly.Label.generated supply tag

def next (supply : LabelSupply) : LabelSupply :=
  supply + 1

end LabelSupply

namespace ProcLabel

def entry (name : Name) : Assembly.Label :=
  Assembly.Label.named ("proc:" ++ name ++ ":entry")

def body (name : Name) : Assembly.Label :=
  Assembly.Label.named ("proc:" ++ name ++ ":body")

def exit (name : Name) : Assembly.Label :=
  Assembly.Label.named ("proc:" ++ name ++ ":exit")

def programEnd : Assembly.Label :=
  Assembly.Label.named "structured:program:end"

end ProcLabel

namespace Stmt

def callToken (supply : LabelSupply) : Word :=
  EvmYul.UInt256.ofNat supply

end Stmt

end Structured
end EvmCompiler
