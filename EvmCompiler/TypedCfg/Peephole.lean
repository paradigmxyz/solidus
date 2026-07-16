import EvmCompiler.TypedCfg.Syntax

/-!
# Adjacent-inverse peephole on `TypedCfg` block bodies

Milestone (b): the peephole *function* on a straight-line block body
(`List Instr`) together with its purely syntactic properties.  A `TypedCfg`
block body never contains control flow (labels/jumps live at the `Terminator`
level), so cancelling adjacent inverse instruction pairs inside a body can
never disturb the program's label/jump structure — only its straight-line
data plumbing.

The first supported rule is `push v ; pop → ε`.  Cancellation is performed
tail-first, so a nested cascade such as `push a ; push b ; pop ; pop`
collapses completely in a single pass.  Recursion is structural on the tail,
so the definition is obviously terminating.

Semantic correctness (that the peepholed body computes the same runtime data)
and the lowering integration land in milestone (c); this module only
establishes the shape of the transform.
-/

namespace EvmCompiler
namespace TypedCfg
namespace Peephole

/-- Cancel adjacent `push v ; pop` pairs in a straight-line body.

The tail is peepholed first; if the current instruction is a `push` and the
peepholed tail begins with a `pop`, both are dropped.  This collapses nested
cascades in one pass while remaining structurally recursive. -/
def peepholeBody : List Instr → List Instr
  | [] => []
  | instr :: rest =>
      match instr, peepholeBody rest with
      | .push _, .pop :: rest' => rest'
      | instr', tail => instr' :: tail

@[simp] theorem peepholeBody_nil : peepholeBody [] = [] := rfl

/-- Unfolding lemma exposing the two cases of `peepholeBody` on a cons. -/
theorem peepholeBody_cons (instr : Instr) (rest : List Instr) :
    peepholeBody (instr :: rest) =
      match instr, peepholeBody rest with
      | .push _, .pop :: rest' => rest'
      | instr', tail => instr' :: tail := rfl

/-- The peephole never grows a body. -/
theorem peepholeBody_length_le :
    ∀ body : List Instr, (peepholeBody body).length ≤ body.length
  | [] => by simp
  | instr :: rest => by
      have ih := peepholeBody_length_le rest
      rw [peepholeBody_cons]
      -- Split on the two match arms.
      split
      · -- cancelling arm: drop `push` and the leading `pop` of the tail.
        rename_i v rest' hEq
        -- `peepholeBody rest = .pop :: rest'`, and `rest'.length + 1 ≤ rest.length`.
        have hlen : (peepholeBody rest).length = rest'.length + 1 := by
          rw [hEq]; simp
        simp only [List.length_cons]
        omega
      · -- keep arm.
        simp only [List.length_cons]
        omega

end Peephole
end TypedCfg
end EvmCompiler
