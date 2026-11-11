import EvmCompiler.Assembly.Semantics

namespace EvmCompiler
namespace Assembly
namespace StackShuffle

def swapInstr : Nat → Instr
  | 1 => .prim .swap1
  | 2 => .prim .swap2
  | 3 => .prim .swap3
  | 4 => .prim .swap4
  | 5 => .prim .swap5
  | 6 => .prim .swap6
  | 7 => .prim .swap7
  | 8 => .prim .swap8
  | 9 => .prim .swap9
  | 10 => .prim .swap10
  | 11 => .prim .swap11
  | 12 => .prim .swap12
  | 13 => .prim .swap13
  | 14 => .prim .swap14
  | 15 => .prim .swap15
  | 16 => .prim .swap16
  | _ => .prim .invalid

def dupInstr : Nat → Instr
  | 1 => .prim .dup1
  | 2 => .prim .dup2
  | 3 => .prim .dup3
  | 4 => .prim .dup4
  | 5 => .prim .dup5
  | 6 => .prim .dup6
  | 7 => .prim .dup7
  | 8 => .prim .dup8
  | 9 => .prim .dup9
  | 10 => .prim .dup10
  | 11 => .prim .dup11
  | 12 => .prim .dup12
  | 13 => .prim .dup13
  | 14 => .prim .dup14
  | 15 => .prim .dup15
  | 16 => .prim .dup16
  | _ => .prim .invalid

/-- Move the top stack item below `depth` visible items. -/
def sinkTopUnder : Nat → Program
  | 0 => []
  | depth + 1 => swapInstr (depth + 1) :: sinkTopUnder depth

/-- Move the item below `depth` visible items to the top. -/
def liftBuriedToTop : Nat → Program
  | 0 => []
  | depth + 1 => liftBuriedToTop depth ++ [swapInstr (depth + 1)]

/--
Check that an item exists below `depth` visible items without changing the
stack. The leading `DUP` preserves the return-dispatch underflow behavior; the
following `POP` removes the temporary copy.
-/
def guardBuried (depth : Nat) : Program :=
  [dupInstr (depth + 1), .prim .pop]

/-- Validate a buried item and then move it to the top of the stack. -/
def guardedLiftBuriedToTop (depth : Nat) : Program :=
  liftBuriedToTop depth

theorem lift_prefix_split {depth n : Nat} (h : n < depth) :
    ∃ tail, liftBuriedToTop depth = liftBuriedToTop n ++ swapInstr (n + 1) :: tail := by
  induction depth with
  | zero => omega
  | succ depth ih =>
      by_cases heq : n = depth
      · subst n
        exact ⟨[], by simp [liftBuriedToTop]⟩
      · obtain ⟨tail, ht⟩ := ih (by omega)
        exact ⟨tail ++ [swapInstr (depth + 1)], by simp [liftBuriedToTop, ht]⟩


/-- Remove the item below `depth` visible items, preserving their order. -/
def removeBuriedUnder (depth : Nat) : Program :=
  liftBuriedToTop depth ++ [.prim .pop]

end StackShuffle
end Assembly
end EvmCompiler
