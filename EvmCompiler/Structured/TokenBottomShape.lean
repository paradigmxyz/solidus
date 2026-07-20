import EvmCompiler.Structured.TypedCfgPreservation.Core

/-!
# The token-at-bottom shape invariant (`TokenBottomOrNone`)

Session 49 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-48 frontier item 1).

Every shape the `TypedCfgCompiler` emits keeps its compiler-owned return token — when it
carries one at all — as the **bottom** (deepest, last) visible slot.  Phrased on
`returnTokenDepth?`, this is

  `shape.returnTokenDepth? = none ∨ shape.returnTokenDepth? = some (shape.length - 1)`,

captured by `TokenBottomOrNone`.  This is exactly the static fact the token-owning block-entry
`StackRealizes` bridge (`stackRealizes_of_realizedWitnessFC_of_token_last`,
`InteractionHInvClose.lean`) needs to discharge its `hLast` hypothesis at an arbitrary reached
entry — see the total bridge `stackRealizes_of_realizedWitnessFC`.

**Key arithmetic.**  `TokenBottomOrNone` is equivalent to the "hidden suffix is at most one
slot" bound `shape.length ≤ sourceLength shape + 1` (the token, when present, is the *only*
slot below the source-visible prefix).  The hidden-suffix count `length − sourceLength` is
**exactly preserved** by every accepted `BasicInstr` (`length_balance_of_type`,
`TypedCfgPreservation/Core.lean:942`) and by the compiler's shape operations
(`pop` / `pushWords` / `afterCall` / `slots.tail`), so `TokenBottomOrNone` propagates from the
procedure-entry seed (`procEntry`, token at the bottom) through the whole generated body.

This file is the reusable arithmetic foundation: the predicate, its
`length ≤ sourceLength + 1` characterization, the token-owning "pin" extraction the bridge
consumes, the `procEntry` / `procExit` base cases, and the shape-operation preservation lemmas.
All statements are pure shape arithmetic — additive, no existing statement touched.
-/

namespace EvmCompiler
namespace Structured
namespace TokenBottomShape

/--
**The token-at-bottom shape invariant.**  A shape either carries no compiler-owned return
token, or carries it at the bottom (its deepest, last slot). -/
def TokenBottomOrNone (shape : TypedCfg.Shape) : Prop :=
  shape.returnTokenDepth? = none ∨
    shape.returnTokenDepth? = some (shape.length - 1)

/--
**Arithmetic characterization.**  Token-at-bottom-or-none is exactly the "hidden suffix is at
most one slot" bound.  With the token absent the hidden suffix is empty
(`sourceLength = length`); with it at the bottom the hidden suffix is the single token slot
(`sourceLength = length − 1`); anything deeper leaves a suffix of two or more. -/
theorem tokenBottomOrNone_iff_length_le {shape : TypedCfg.Shape} :
    TokenBottomOrNone shape ↔
      shape.length ≤ TypedCfgCompiler.Shape.sourceLength shape + 1 := by
  unfold TokenBottomOrNone
  cases hDepth : shape.returnTokenDepth? with
  | none =>
      have hEq :
          TypedCfgCompiler.Shape.sourceLength shape = shape.length := by
        unfold TypedCfgCompiler.Shape.sourceLength
        rw [TypedCfgCompilerFacts.Shape.sourceView_eq_self_of_returnTokenDepth?_eq_none hDepth]
      constructor
      · intro _; omega
      · intro _; exact Or.inl rfl
  | some depth =>
      have hSource :
          TypedCfgCompiler.Shape.sourceLength shape = depth :=
        TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some hDepth
      have hLt : depth < shape.length :=
        TypedCfgCompilerFacts.Shape.returnTokenDepth?_lt_length hDepth
      rw [hSource]
      constructor
      · rintro (h | h)
        · exact absurd h (by simp)
        · have hd : depth = shape.length - 1 := Option.some.inj h
          omega
      · intro hLe
        refine Or.inr ?_
        have hd : shape.length - 1 = depth := by omega
        rw [hd]

/--
**Token-owning "pin" extraction** — the form the bridge consumes.  When a `TokenBottomOrNone`
shape *does* carry a token, that token sits at the bottom. -/
theorem returnTokenDepth?_eq_pred_length_of_tokenBottomOrNone
    {shape : TypedCfg.Shape} {depth : Nat}
    (hTB : TokenBottomOrNone shape)
    (hSome : shape.returnTokenDepth? = some depth) :
    shape.returnTokenDepth? = some (shape.length - 1) := by
  rcases hTB with h | h
  · rw [hSome] at h; exact absurd h (by simp)
  · exact h

/-! ## Shape-operation preservation

`TokenBottomOrNone` is preserved by every shape operation the compiler threads a block input
through: prepending source words (`pushWords`), dropping source words (`pop` / `slots.tail`), and
their `afterCall` composition; and the procedure boundary shapes (`procEntry` / `procExit`) are
token-at-bottom base cases.  These are the "per-disjunct arithmetic" the token-at-bottom static
fact (frontier item 1) threads through the `BlockGenShapeReg` classifier. -/

private theorem drop_succ_tail {α : Type _} (l : List α) (n : Nat) :
    l.drop (n + 1) = l.tail.drop n := by
  cases l with
  | nil => simp
  | cons a t => rfl

/-- Source-visible length grows by one under prepending a `.word` slot. -/
theorem sourceLength_cons_word (shape : TypedCfg.Shape) :
    TypedCfgCompiler.Shape.sourceLength
        { shape with slots := .word :: shape.slots } =
      TypedCfgCompiler.Shape.sourceLength shape + 1 := by
  cases hDepth : shape.returnTokenDepth? with
  | none =>
      have hNewDepth :
          ({ shape with slots := .word :: shape.slots } :
            TypedCfg.Shape).returnTokenDepth? = none := by
        simpa [TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] using hDepth
      unfold TypedCfgCompiler.Shape.sourceLength
      rw [TypedCfgCompilerFacts.Shape.sourceView_eq_self_of_returnTokenDepth?_eq_none hNewDepth,
        TypedCfgCompilerFacts.Shape.sourceView_eq_self_of_returnTokenDepth?_eq_none hDepth]
      simp [TypedCfg.Shape.length]
  | some depth =>
      have hNewDepth :
          ({ shape with slots := .word :: shape.slots } :
            TypedCfg.Shape).returnTokenDepth? = some (depth + 1) := by
        simpa [TypedCfg.Shape.returnTokenDepth?,
          TypedCfg.Shape.returnTokenDepthList?] using hDepth
      have h1 :=
        TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some hNewDepth
      have h2 :=
        TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some hDepth
      omega

theorem length_pushWords (n : Nat) (shape : TypedCfg.Shape) :
    (TypedCfg.Shape.pushWords n shape).length = n + shape.length := by
  simp [TypedCfg.Shape.pushWords, TypedCfg.Shape.length]

theorem sourceLength_pushWords (n : Nat) (shape : TypedCfg.Shape) :
    TypedCfgCompiler.Shape.sourceLength (TypedCfg.Shape.pushWords n shape) =
      TypedCfgCompiler.Shape.sourceLength shape + n := by
  induction n with
  | zero => simp [TypedCfg.Shape.pushWords]
  | succ n ih =>
      have hStep :
          TypedCfg.Shape.pushWords (n + 1) shape =
            { (TypedCfg.Shape.pushWords n shape) with
              slots := .word :: (TypedCfg.Shape.pushWords n shape).slots } := by
        simp [TypedCfg.Shape.pushWords, List.replicate_succ]
      rw [hStep, sourceLength_cons_word, ih]; omega

theorem length_pop (n : Nat) (shape : TypedCfg.Shape) :
    (TypedCfg.Shape.pop n shape).length = shape.length - n := by
  simp [TypedCfg.Shape.pop, TypedCfg.Shape.length]

theorem sourceLength_pop {n : Nat} {shape : TypedCfg.Shape}
    (h : n ≤ TypedCfgCompiler.Shape.sourceLength shape) :
    TypedCfgCompiler.Shape.sourceLength (TypedCfg.Shape.pop n shape) =
      TypedCfgCompiler.Shape.sourceLength shape - n := by
  induction n generalizing shape with
  | zero => simp [TypedCfg.Shape.pop]
  | succ n ih =>
      have hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape := by omega
      have hTailSource :
          TypedCfgCompiler.Shape.sourceLength
              { shape with slots := shape.slots.tail } =
            TypedCfgCompiler.Shape.sourceLength shape - 1 :=
        TypedCfgCompilerFacts.Shape.sourceLength_tail_of_one_le shape hSource
      have hStep :
          TypedCfg.Shape.pop (n + 1) shape =
            TypedCfg.Shape.pop n { shape with slots := shape.slots.tail } := by
        simp only [TypedCfg.Shape.pop]; congr 1; exact drop_succ_tail shape.slots n
      have hn :
          n ≤ TypedCfgCompiler.Shape.sourceLength
              { shape with slots := shape.slots.tail } := by
        rw [hTailSource]; omega
      rw [hStep, ih hn, hTailSource]; omega

/-- **`pushWords` preserves token-at-bottom.**  Prepending source words leaves the token (if
any) at the bottom; the hidden suffix count is unchanged. -/
theorem tokenBottomOrNone_pushWords {n : Nat} {shape : TypedCfg.Shape}
    (h : TokenBottomOrNone shape) :
    TokenBottomOrNone (TypedCfg.Shape.pushWords n shape) := by
  rw [tokenBottomOrNone_iff_length_le] at h ⊢
  rw [length_pushWords, sourceLength_pushWords]
  omega

/-- **`pop` preserves token-at-bottom** (dropping ≤ `sourceLength` source words). -/
theorem tokenBottomOrNone_pop {n : Nat} {shape : TypedCfg.Shape}
    (hle : n ≤ TypedCfgCompiler.Shape.sourceLength shape)
    (h : TokenBottomOrNone shape) :
    TokenBottomOrNone (TypedCfg.Shape.pop n shape) := by
  rw [tokenBottomOrNone_iff_length_le] at h ⊢
  rw [length_pop, sourceLength_pop hle]
  have := TypedCfgCompilerFacts.Shape.sourceLength_le_length shape
  omega

/-- **`slots.tail` preserves token-at-bottom** (given a nonempty source-visible prefix — the
single-`pop` case). -/
theorem tokenBottomOrNone_tail {shape : TypedCfg.Shape}
    (hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape)
    (h : TokenBottomOrNone shape) :
    TokenBottomOrNone { shape with slots := shape.slots.tail } := by
  rw [tokenBottomOrNone_iff_length_le] at h ⊢
  rw [TypedCfgCompilerFacts.Shape.sourceLength_tail_of_one_le shape hSource,
    show ({ shape with slots := shape.slots.tail } : TypedCfg.Shape).length =
        shape.length - 1 by simp [TypedCfg.Shape.length]]
  have := TypedCfgCompilerFacts.Shape.sourceLength_le_length shape
  omega

/-- **`afterCall` preserves token-at-bottom.**  The call continuation shape
(`pushWords retc (pop argc input)`) keeps the token at the bottom. -/
theorem tokenBottomOrNone_afterCall {input output : TypedCfg.Shape} {argc retc : Nat}
    (hle : argc ≤ TypedCfgCompiler.Shape.sourceLength input)
    (hAfter : TypedCfgCompiler.Shape.afterCall input argc retc = some output)
    (h : TokenBottomOrNone input) :
    TokenBottomOrNone output := by
  unfold TypedCfgCompiler.Shape.afterCall at hAfter
  have hInputCount : argc ≤ input.length :=
    le_trans hle (TypedCfgCompilerFacts.Shape.sourceLength_le_length input)
  simp [hInputCount] at hAfter
  subst output
  exact tokenBottomOrNone_pushWords (tokenBottomOrNone_pop hle h)

/-- **Procedure-entry base case.**  `procEntry` places `.returnToken` as its last slot. -/
theorem tokenBottomOrNone_procEntry (proc : Structured.Proc) :
    TokenBottomOrNone (TypedCfgCompiler.Shape.procEntry proc) := by
  right
  have hlen : (TypedCfgCompiler.Shape.procEntry proc).length = proc.argc + 1 := by
    simp [TypedCfgCompiler.Shape.procEntry, TypedCfg.Shape.length]
  rw [TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry, hlen]; simp

/-- **Procedure-exit base case.**  `procExit` places `.returnToken` as its last slot. -/
theorem tokenBottomOrNone_procExit (proc : Structured.Proc) :
    TokenBottomOrNone (TypedCfgCompiler.Shape.procExit proc) := by
  right
  have hlen : (TypedCfgCompiler.Shape.procExit proc).length = proc.retc + 1 := by
    simp [TypedCfgCompiler.Shape.procExit, TypedCfg.Shape.length]
  rw [TypedCfgCompilerFacts.Call.returnTokenDepth?_procExit, hlen]; simp

/-- **Straight-line-fragment length balance.**  An accepted `Code.type?` fragment preserves the
hidden-suffix count `length − sourceLength` (the iterated `length_balance_of_type`); stated
additively so the subtraction never underflows. -/
theorem code_length_balance {code : Structured.Code} {input output : TypedCfg.Shape}
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    output.length + TypedCfgCompiler.Shape.sourceLength input =
      TypedCfgCompiler.Shape.sourceLength output + input.length := by
  induction code generalizing input output with
  | nil =>
      simp [TypedCfgCompiler.Code.type?] at hType
      subst output
      omega
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      cases hMiddle :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none => simp [hMiddle] at hType
      | some middle =>
          cases hSafe :
              TypedCfgCompiler.BasicInstr.sourceSafe? instr input middle with
          | false => simp [hMiddle, hSafe] at hType
          | true =>
              have hRestType :
                  TypedCfgCompiler.Code.type? rest middle = some output := by
                simpa [hMiddle, hSafe] using hType
              have hHead :=
                TypedCfgPreservation.BasicInstr.length_balance_of_type hMiddle hSafe
              have hRest := ih hRestType
              omega

/-- **`Code.type?` preserves token-at-bottom.**  The straight-line body of every generated block
carries its input's token position through to its output — the fallthrough-shape thread of the
token-at-bottom static fact. -/
theorem tokenBottomOrNone_of_code_type? {code : Structured.Code}
    {input output : TypedCfg.Shape}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (h : TokenBottomOrNone input) :
    TokenBottomOrNone output := by
  rw [tokenBottomOrNone_iff_length_le] at h ⊢
  have hBal := code_length_balance hType
  have h1 := TypedCfgCompilerFacts.Shape.sourceLength_le_length input
  have h2 := TypedCfgCompilerFacts.Shape.sourceLength_le_length output
  omega

end TokenBottomShape
end Structured
end EvmCompiler
