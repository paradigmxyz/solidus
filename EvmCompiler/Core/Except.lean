import Mathlib.Data.List.Basic

namespace EvmCompiler

@[simp] theorem except_bind_error {ε α β : Type} (err : ε)
    (f : α → Except ε β) :
    (Except.error err >>= f) = Except.error err := rfl

@[simp] theorem except_bind_ok {ε α β : Type} (value : α)
    (f : α → Except ε β) :
    (Except.ok value >>= f) = f value := rfl

end EvmCompiler
