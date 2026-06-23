import EvmYul.UInt256

namespace EvmCompiler
namespace MemoryContract

/-!
The production backend is stack-only and therefore reserves no compiler
memory. This singleton remains in program syntax so the adjacent semantic
interfaces do not encode frontend-specific memory policy.
-/

structure Contract where
  deriving DecidableEq, Inhabited, Repr

def unrestricted : Contract :=
  {}

end MemoryContract
end EvmCompiler
