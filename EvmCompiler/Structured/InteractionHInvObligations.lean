import EvmCompiler.Structured.TypedCfgPreservation.GeneratedBoundary

/-!
# Per-disjunct `hInv` compiler-shape obligations (session 42)

Session 42 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-41 frontier).

The branch/machinery `hInv` dispatch legs (`InteractionHInvDispatch.lean`) each take, as a
source-quantified hypothesis, a compiler-shape fact that the disjunct field alone does not
carry — a `SourceFrameFits` transport across the block's own body, or the scrutinee-pop
existence.  This module banks those transports as standalone lemmas, so the strengthened
`BlockGenShapeReg` disjuncts can supply them at the capstone construction sites where the
enclosing construct's source-word guarantee is in scope.

* `caseEntryPop_popTransport` — the switch case-entry `pop` block transport.  From the
  scrutinee source word (`1 ≤ sourceLength input`, from the switch's `requireSourceWords? 1`)
  and the `.pop` typing, any source frame fitting `input` has a poppable top and the popped
  frame fits the `.pop` output (`= { input with slots := input.slots.tail }`, via
  `sourceFrameFits_tail`).

* `switchTest_popExists` — the same source-word guarantee gives the scrutinee-pop existence
  the `switchTest` leg's `openStep_test` needs (a target `.dup 0` reads the scrutinee, so the
  source stack must be non-empty).

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionHInvObligations

/--
**`caseEntryPop` pop-transport.**  The switch case-entry `pop` block pops the scrutinee.
Given the switch's scrutinee source word (`1 ≤ sourceLength input`) and the `.pop` typing
(`output = { input with slots := input.slots.tail }`), every source frame fitting `input`
has a poppable top and, after popping, fits the `.pop` output — exactly the
`caseEntryPop` dispatch leg's `hPopTransport`. -/
theorem caseEntryPop_popTransport
    {input output : TypedCfg.Shape}
    (hValueSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength input)
    (hType : TypedCfg.Instr.type? .pop input = some output) :
    ∀ source : RunState,
      TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length →
        ∃ (stack : EvmYul.Stack Word) (value : Word),
          source.evm.stack.pop = some (stack, value) ∧
            TypedCfgCompiler.Shape.SourceFrameFits output
              (source.withEVM { source.evm with stack := stack }).evm.stack.length := by
  have hOut : output = { input with slots := input.slots.tail } := by
    rcases input with ⟨slots, tail⟩
    cases slots with
    | nil => simp [TypedCfg.Instr.type?] at hType
    | cons s rest =>
        simp only [TypedCfg.Instr.type?] at hType
        exact (Option.some.inj hType).symm
  intro source hFits
  have hLen1 : 1 ≤ source.evm.stack.length := le_trans hValueSource hFits.1
  cases hStk : source.evm.stack with
  | nil => rw [hStk] at hLen1; simp at hLen1
  | cons hd tl =>
      refine ⟨tl, hd, ?_, ?_⟩
      · rfl
      · have hLenEq : source.evm.stack.length = tl.length + 1 := by
          rw [hStk]; simp
        have hFits' :
            TypedCfgCompiler.Shape.SourceFrameFits input (tl.length + 1) := by
          rw [← hLenEq]; exact hFits
        have hTail :=
          TypedCfgCompilerFacts.Shape.sourceFrameFits_tail hValueSource hFits'
        rw [hOut]
        simpa [RunState.withEVM] using hTail

/--
**`switchTest` scrutinee-pop existence.**  From the switch's scrutinee source word
(`1 ≤ sourceLength valueShape`), any source frame fitting `valueShape` has a poppable top —
the `switchTest` dispatch leg's `hPopExists`. -/
theorem switchTest_popExists
    {valueShape : TypedCfg.Shape}
    (hValueSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape) :
    ∀ source : RunState,
      TypedCfgCompiler.Shape.SourceFrameFits valueShape source.evm.stack.length →
        ∃ (stack : EvmYul.Stack Word) (value : Word),
          source.evm.stack.pop = some (stack, value) := by
  intro source hFits
  have hLen1 : 1 ≤ source.evm.stack.length := le_trans hValueSource hFits.1
  cases hStk : source.evm.stack with
  | nil => rw [hStk] at hLen1; simp at hLen1
  | cons hd tl => exact ⟨tl, hd, rfl⟩

end InteractionHInvObligations
end Structured
end EvmCompiler
