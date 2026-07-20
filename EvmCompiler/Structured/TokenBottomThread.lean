import EvmCompiler.Structured.TokenBottomShape
import EvmCompiler.Structured.InteractionHInvClose

/-!
# Threading the token-at-bottom shape invariant through the compiler classifier (frontier item 1)

Session 50 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-49 frontier item 1, option (a)).

`TokenBottomShape.lean` banked the complete arithmetic substrate (`TokenBottomOrNone`, its
`length ≤ sourceLength + 1` characterization, the token-owning pin, and op-preservation for
`pushWords`/`pop`/`tail`/`afterCall`/`procEntry`/`procExit`/`Code.type?`).  This module threads
that invariant through the compiler generation recursion — the additive classifier-threading
mirror of `genShapeReg_of_compile*` (`InteractionBlockGenShapeRegular.lean`) — and assembles the
program-level static fact

  `∀ label block, cfg.findBlock? label = some block → TokenBottomOrNone block.input`

which discharges the `hTB` premise of the total block-entry `StackRealizes` bridge
`stackRealizes_of_realizedWitnessFC` (`InteractionHInvClose.lean`) at an arbitrary reached entry.

The per-fragment payload is `TbResult`: every emitted block's input is `TokenBottomOrNone`, and
the fragment's fallthrough output (when present) is `TokenBottomOrNone`.  The fallthrough conjunct
is what makes sequential composition compose (the previous fragment's output seeds the next
fragment's input).  Each transition is one application of a banked op lemma from
`TokenBottomShape.lean`.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace TokenBottomThread

open TokenBottomShape (TokenBottomOrNone)

/--
**The per-fragment token-at-bottom payload.**  Every block the compiler result emits has a
`TokenBottomOrNone` input shape, and the result's fallthrough output (if any) is likewise
`TokenBottomOrNone`. -/
def TbResult (result : TypedCfgCompiler.Result) : Prop :=
  (∀ b ∈ result.blocks, TokenBottomOrNone b.input) ∧
    (∀ ft, result.fallthrough? = some ft → TokenBottomOrNone ft)

/-- `TbResult` is closed under `Result.append`: blocks concatenate, fallthrough is the right
fragment's. -/
theorem TbResult.append {left right : TypedCfgCompiler.Result}
    (hLeft : TbResult left) (hRight : TbResult right) :
    TbResult (left.append right) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rcases List.mem_append.mp hb with hL | hR
    · exact hLeft.1 b hL
    · exact hRight.1 b hR
  · intro ft hft
    exact hRight.2 ft hft

/-!
## The threading mutual

Mirrors `genShapeReg_of_compile*` but threads the (much lighter) `TokenBottomOrNone input`
hypothesis and concludes `TbResult result`.  Each disjunct's per-block/fallthrough obligation is
one banked op lemma from `TokenBottomShape.lean`.
-/

mutual

theorem tbResult_of_compileBlockFuel?
    {fuel : Nat} {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? fuel block ctx
          supply entry input regular = some result)
    (hInput : TokenBottomOrNone input) :
    TbResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
  | succ compilerFuel =>
      unfold TypedCfgCompiler.compileBlockFuel? at hCompile
      exact tbResult_of_compileStmtListFuel? hCompile hInput

theorem tbResult_of_compileStmtListFuel?
    {fuel : Nat} {stmts : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? fuel stmts ctx
          supply entry input regular = some result)
    (hInput : TokenBottomOrNone input) :
    TbResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
  | succ compilerFuel =>
      cases stmts with
      | nil =>
          simp [TypedCfgCompiler.compileStmtListFuel?,
            TypedCfgCompiler.mkBlock?] at hCompile
          cases hCompile
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_singleton] at hb
            subst b
            exact hInput
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hInput
      | cons stmt rest =>
          rcases
              TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
                hCompile with
            ⟨headResult, hHead, hNoTail | hTail⟩
          · rcases hNoTail with ⟨_hFallthrough, rfl⟩
            exact tbResult_of_compileStmtFuel? hHead hInput
          · rcases hTail with
              ⟨tailInput, tailResult, hHeadFall, hTailCompile, rfl⟩
            have hHeadTb := tbResult_of_compileStmtFuel? hHead hInput
            have hTailInput : TokenBottomOrNone tailInput :=
              hHeadTb.2 tailInput hHeadFall
            exact hHeadTb.append (tbResult_of_compileStmtListFuel? hTailCompile hTailInput)

theorem tbResult_of_compileStmtFuel?
    {fuel : Nat} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result)
    (hInput : TokenBottomOrNone input) :
    TbResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
  | succ compilerFuel =>
      cases stmt with
      | code code =>
          obtain ⟨output, hType, rfl⟩ :=
            TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_code hCompile
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_singleton] at hb
            subst b
            exact hInput
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact TokenBottomShape.tokenBottomOrNone_of_code_type? hType hInput
      | if_ cond body =>
          obtain
              ⟨output, _condition, bodyResult,
                hType, hSource, _hHead, hBody, _hBodyRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
          have hOutput : TokenBottomOrNone output :=
            TokenBottomShape.tokenBottomOrNone_of_code_type? hType hInput
          have hSourceLen : 1 ≤ TypedCfgCompiler.Shape.sourceLength output :=
            TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hTail : TokenBottomOrNone { output with slots := output.slots.tail } :=
            TokenBottomShape.tokenBottomOrNone_tail hSourceLen hOutput
          have hBodyTb := tbResult_of_compileBlockFuel? hBody hTail
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_cons] at hb
            rcases hb with rfl | hBodyMem
            · exact hInput
            · exact hBodyTb.1 b hBodyMem
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hTail
      | switch scrutinee cases defaultBody =>
          obtain
              ⟨valueShape, _valueSlot, caseResult, defaultResult,
                hType, hSource, hHead, hCases, hDefault, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch hCompile
          have hValue : TokenBottomOrNone valueShape :=
            TokenBottomShape.tokenBottomOrNone_of_code_type? hType hInput
          have hSourceLen : 1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape :=
            TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hPop :
              TypedCfg.Instr.type? .pop valueShape =
                some { valueShape with slots := valueShape.slots.tail } := by
            rcases valueShape with ⟨slots, tail⟩
            cases slots with
            | nil => simp at hHead
            | cons slot rest => simp [TypedCfg.Instr.type?]
          have hBodyShape :
              TokenBottomOrNone { valueShape with slots := valueShape.slots.tail } :=
            TokenBottomShape.tokenBottomOrNone_tail hSourceLen hValue
          have hCaseTb :=
            tbResult_of_compileCasesFuel? hHead hPop hCases hValue hBodyShape
          have hDefaultTb :=
            tbResult_of_compileDefaultFuel? hPop hDefault hValue hBodyShape
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_cons, List.mem_append] at hb
            rcases hb with (rfl | hCaseMem) | hDefaultMem
            · exact hInput
            · exact hCaseTb.1 b hCaseMem
            · exact hDefaultTb.1 b hDefaultMem
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hBodyShape
      | for_ init cond post body =>
          obtain
              ⟨initResult, loopInput, condOutput, _condition,
                bodyResult, postResult, hInit, hInitFallthrough,
                hType, hSource, _hHead, hBody, _hBodyRequire,
                hPost, _hPostRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Loop.components_of_compileStmtFuel?_for hCompile
          have hInitTb := tbResult_of_compileBlockFuel? hInit hInput
          have hLoopInput : TokenBottomOrNone loopInput :=
            hInitTb.2 loopInput hInitFallthrough
          have hCondOutput : TokenBottomOrNone condOutput :=
            TokenBottomShape.tokenBottomOrNone_of_code_type? hType hLoopInput
          have hSourceLen : 1 ≤ TypedCfgCompiler.Shape.sourceLength condOutput :=
            TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hBodyInput :
              TokenBottomOrNone { condOutput with slots := condOutput.slots.tail } :=
            TokenBottomShape.tokenBottomOrNone_tail hSourceLen hCondOutput
          have hBodyTb := tbResult_of_compileBlockFuel? hBody hBodyInput
          have hPostTb := tbResult_of_compileBlockFuel? hPost hBodyInput
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.append_assoc, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false] at hb
            rcases hb with hInitMem | rfl | hBodyMem | hPostMem
            · exact hInitTb.1 b hInitMem
            · exact hLoopInput
            · exact hBodyTb.1 b hBodyMem
            · exact hPostTb.1 b hPostMem
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hBodyInput
      | brk =>
          unfold TypedCfgCompiler.compileStmtFuel? at hCompile
          cases hLabel : ctx.breakLabel? with
          | none =>
              simp [TypedCfgCompiler.checkedJumpOrInvalid, hLabel] at hCompile
          | some label =>
              cases hShape : ctx.breakShape? with
              | none =>
                  simp [TypedCfgCompiler.checkedJumpOrInvalid,
                    hLabel, hShape] at hCompile
              | some expected =>
                  by_cases hInputEq : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    refine ⟨?_, ?_⟩
                    · intro b hb
                      simp only [List.mem_singleton] at hb
                      subst b
                      exact hInput
                    · intro ft hft
                      simp at hft
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInputEq] at hCompile
      | cont =>
          unfold TypedCfgCompiler.compileStmtFuel? at hCompile
          cases hLabel : ctx.continueLabel? with
          | none =>
              simp [TypedCfgCompiler.checkedJumpOrInvalid, hLabel] at hCompile
          | some label =>
              cases hShape : ctx.continueShape? with
              | none =>
                  simp [TypedCfgCompiler.checkedJumpOrInvalid,
                    hLabel, hShape] at hCompile
              | some expected =>
                  by_cases hInputEq : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    refine ⟨?_, ?_⟩
                    · intro b hb
                      simp only [List.mem_singleton] at hb
                      subst b
                      exact hInput
                    · intro ft hft
                      simp at hft
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInputEq] at hCompile
      | leave =>
          unfold TypedCfgCompiler.compileStmtFuel? at hCompile
          cases hLabel : ctx.leaveLabel? with
          | none =>
              simp [TypedCfgCompiler.checkedJumpOrInvalid, hLabel] at hCompile
          | some label =>
              cases hShape : ctx.leaveShape? with
              | none =>
                  simp [TypedCfgCompiler.checkedJumpOrInvalid,
                    hLabel, hShape] at hCompile
              | some expected =>
                  by_cases hInputEq : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    refine ⟨?_, ?_⟩
                    · intro b hb
                      simp only [List.mem_singleton] at hb
                      subst b
                      exact hInput
                    · intro ft hft
                      simp at hft
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInputEq] at hCompile
      | call name =>
          obtain ⟨proc, hLookup⟩ :=
            TypedCfgCompilerFacts.Call.exists_lookup_of_compileStmtFuel?_call hCompile
          obtain
              ⟨returnShape, _output, hSource, hAfter, _hType, rfl⟩ :=
            TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
              hLookup hCompile
          have hArgc : proc.argc ≤ TypedCfgCompiler.Shape.sourceLength input :=
            TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hReturn : TokenBottomOrNone returnShape :=
            TokenBottomShape.tokenBottomOrNone_afterCall hArgc hAfter hInput
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_singleton] at hb
            subst b
            exact hInput
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hReturn
      | terminal kind =>
          obtain ⟨_hSource, rfl⟩ :=
            TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal hCompile
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_singleton] at hb
            subst b
            exact hInput
          · intro ft hft
            simp at hft

theorem tbResult_of_compileCasesFuel?
    {fuel : Nat} {cases : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result}
    (hHead : valueShape.slots.head? = some slot)
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? fuel cases ctx
          base supply idx valueShape bodyShape regular = some result)
    (hValue : TokenBottomOrNone valueShape)
    (hBody : TokenBottomOrNone bodyShape) :
    TbResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
  | succ compilerFuel =>
      cases cases with
      | nil =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          refine ⟨?_, ?_⟩
          · intro b hb; simp at hb
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hBody
      | cons head rest =>
          rcases head with ⟨caseValue, body⟩
          obtain
              ⟨bodyResult, tail, hBodyCompile, _hBodyRequire,
                hTailCompile, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPop hCompile
          have hBodyTb := tbResult_of_compileBlockFuel? hBodyCompile hBody
          have hTailTb := tbResult_of_compileCasesFuel? hHead hPop hTailCompile hValue hBody
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_cons, List.mem_append] at hb
            rcases hb with (rfl | rfl | hBodyMem) | hTailMem
            · exact hValue
            · exact hValue
            · exact hBodyTb.1 b hBodyMem
            · exact hTailTb.1 b hTailMem
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hBody

theorem tbResult_of_compileDefaultFuel?
    {fuel : Nat} {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? fuel defaultBody ctx
          supply entry valueShape bodyShape regular = some result)
    (hValue : TokenBottomOrNone valueShape)
    (hBody : TokenBottomOrNone bodyShape) :
    TbResult result := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileDefaultFuel?] at hCompile
  | succ compilerFuel =>
      cases defaultBody with
      | none =>
          have hRes :=
            TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_none
              hPop hCompile
          subst hRes
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_singleton] at hb
            subst b
            exact hValue
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hBody
      | some body =>
          obtain ⟨bodyResult, hBodyCompile, _hBodyRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
              hPop hCompile
          have hBodyTb := tbResult_of_compileBlockFuel? hBodyCompile hBody
          refine ⟨?_, ?_⟩
          · intro b hb
            simp only [List.mem_cons] at hb
            rcases hb with rfl | hBodyMem
            · exact hValue
            · exact hBodyTb.1 b hBodyMem
          · intro ft hft
            simp only [Option.some.injEq] at hft
            subst ft
            exact hBody

end

end TokenBottomThread
end Structured
end EvmCompiler
