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

/-- **`compileBlock?`-level wrapper.**  The token-at-bottom drill inherited by `compileBlock?`
(the fuel-saturated `compileBlockFuel?`), exactly as `genShapeReg_of_compileBlock?` wraps the
strengthened capstone. -/
theorem tbResult_of_compileBlock?
    {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileBlock? block ctx supply entry input regular = some result)
    (hInput : TokenBottomOrNone input) :
    TbResult result := by
  have hFuel :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel block + 1) block ctx
          supply entry input regular = some result := by
    simpa [TypedCfgCompiler.compileBlock?] using hCompile
  exact tbResult_of_compileBlockFuel? hFuel hInput

/-! ## Program-boundary seeds and the per-entry static fact -/

/-- `Shape.caller` (the main-body root input) carries no return token, hence is
`TokenBottomOrNone`. -/
theorem tokenBottomOrNone_caller :
    TokenBottomOrNone TypedCfg.Shape.caller :=
  Or.inl rfl

/-- **Adapter-route seed is token-at-bottom.**  A proc-entry ADAPTER relabels `procEntry proc`
(length `argc + 1`, token at the bottom) to `bodyInput`; the relabel is length-preserving, and
`bodyInput` owns its return token at depth `argc`, so `bodyInput` is token-at-bottom. -/
theorem tokenBottomOrNone_of_adapter_frame
    {proc : Structured.Proc} {bodyInput : TypedCfg.Shape} {adapter : TypedCfg.Block}
    {entryLbl bodyLbl : Assembly.Label}
    (hFrame : bodyInput.returnTokenDepth? = some proc.argc)
    (hAdapter :
      TypedCfgCompiler.mkBlock? entryLbl (TypedCfgCompiler.Shape.procEntry proc)
        [.relabel bodyInput] (.jump bodyLbl) = some adapter) :
    TokenBottomOrNone bodyInput := by
  unfold TypedCfgCompiler.mkBlock? at hAdapter
  cases hBT :
      TypedCfg.Block.bodyType? [TypedCfg.Instr.relabel bodyInput]
        (TypedCfgCompiler.Shape.procEntry proc) with
  | none => simp [hBT] at hAdapter
  | some output =>
      have hType :
          TypedCfg.Instr.type? (.relabel bodyInput)
            (TypedCfgCompiler.Shape.procEntry proc) = some output := by
        simpa [TypedCfg.Block.bodyType?] using hBT
      have hOutInput : output = bodyInput := by
        simp only [TypedCfg.Instr.type?] at hType
        split at hType
        · exact (Option.some.inj hType).symm
        · exact absurd hType (by simp)
      have hLen : output.length = (TypedCfgCompiler.Shape.procEntry proc).length :=
        TypedCfg.Instr.length_of_type?_relabel hType
      have hProcLen :
          (TypedCfgCompiler.Shape.procEntry proc).length = proc.argc + 1 := by
        simp [TypedCfgCompiler.Shape.procEntry, TypedCfg.Shape.length]
      rw [hOutInput] at hLen
      right
      rw [hFrame]
      congr 1
      omega

/-- `mkBlock?` records its `input` argument verbatim as the emitted block's input shape. -/
theorem input_of_mkBlock?
    {label : Assembly.Label} {input : TypedCfg.Shape}
    {body : List TypedCfg.Instr} {term : TypedCfg.Terminator}
    {blk : TypedCfg.Block}
    (h : TypedCfgCompiler.mkBlock? label input body term = some blk) :
    blk.input = input := by
  unfold TypedCfgCompiler.mkBlock? at h
  cases hBT : TypedCfg.Block.bodyType? body input with
  | none => rw [hBT] at h; exact absurd h (by simp)
  | some output =>
      rw [hBT] at h
      have h2 :
          (some
            { label := label, input := input, body := body,
              output := output, term := term } : Option TypedCfg.Block) = some blk :=
        h
      rw [← Option.some.inj h2]

/-- **Proc-body membership inversion, token-at-bottom form.**  The additive mirror of
`mem_procBlocks_provenance` (`InteractionProcBlockProvenance.lean`) emitting `TokenBottomOrNone
input` on the recovered body-compile seed: `procEntry proc` (no-adapter route) or the relabel
target `bodyInput` (adapter route), both token-at-bottom. -/
theorem mem_procBlocks_tokenBottom
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs procs : List Structured.Proc}
    {supply next : LabelSupply}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    (hLower :
      TypedCfgCompiler.lowerProcBodiesWithShapes? entryShapes allProcs procs
          supply =
        some (procBlocks, next, procCalls))
    {block : TypedCfg.Block}
    (hMem : block ∈ procBlocks) :
    ∃ (proc : Structured.Proc) (bsupply : LabelSupply)
      (entry : Assembly.Label) (input : TypedCfg.Shape)
      (bodyResult : TypedCfgCompiler.Result),
      TypedCfgCompiler.compileBlock? proc.body
          { procs := allProcs
            leaveLabel? := some (ProcLabel.exit proc.name)
            leaveShape? := some (TypedCfgCompiler.Shape.procExit proc) }
          bsupply entry input (ProcLabel.exit proc.name) = some bodyResult ∧
      TokenBottomOrNone input ∧
      (block ∈ bodyResult.blocks ∨ block.input = TypedCfgCompiler.Shape.procEntry proc) := by
  induction procs generalizing supply next procBlocks procCalls with
  | nil =>
      simp only [TypedCfgCompiler.lowerProcBodiesWithShapes?, Option.some.injEq,
        Prod.mk.injEq] at hLower
      obtain ⟨hb, -, -⟩ := hLower
      subst hb
      simp at hMem
  | cons head rest ih =>
      unfold TypedCfgCompiler.lowerProcBodiesWithShapes? at hLower
      cases hShape : entryShapes.find? head.name with
      | none =>
          cases hBody :
              TypedCfgCompiler.compileBlock? head.body
                { procs := allProcs
                  leaveLabel? := some (ProcLabel.exit head.name)
                  leaveShape? :=
                    some (TypedCfgCompiler.Shape.procExit head) }
                supply (ProcLabel.entry head.name)
                (TypedCfgCompiler.Shape.procEntry head)
                (ProcLabel.exit head.name) with
          | none =>
              simp [hShape, hBody] at hLower
          | some compiled =>
              cases hRequire :
                  compiled.requireFallthrough?
                    (TypedCfgCompiler.Shape.procExit head) with
              | none =>
                  simp [hShape, hBody, hRequire] at hLower
              | some unit =>
                  cases unit
                  cases hTail :
                      TypedCfgCompiler.lowerProcBodiesWithShapes?
                        entryShapes allProcs rest compiled.next with
                  | none =>
                      simp [hShape, hBody, hRequire, hTail] at hLower
                  | some tailResult =>
                      rcases tailResult with ⟨tailBlocks, tailNext, tailCalls⟩
                      simp [hShape, hBody, hRequire, hTail] at hLower
                      rcases hLower with ⟨rfl, rfl, rfl⟩
                      simp only [List.mem_append] at hMem
                      rcases hMem with hHere | hThere
                      · exact
                          ⟨head, supply, ProcLabel.entry head.name,
                            TypedCfgCompiler.Shape.procEntry head, compiled,
                            hBody,
                            TokenBottomShape.tokenBottomOrNone_procEntry head,
                            Or.inl hHere⟩
                      · obtain
                          ⟨proc, bsupply, e, input, bodyResult,
                            hCompile, hTB, hDisj⟩ :=
                          ih hTail hThere
                        exact
                          ⟨proc, bsupply, e, input, bodyResult,
                            hCompile, hTB, hDisj⟩
      | some bodyInput =>
          cases hFrame :
              TypedCfgCompiler.Shape.requireReturnTokenDepth?
                head.argc bodyInput with
          | none =>
              simp [hShape, hFrame] at hLower
          | some unit =>
              cases unit
              cases hAdapter :
                  TypedCfgCompiler.mkBlock?
                    (ProcLabel.entry head.name)
                    (TypedCfgCompiler.Shape.procEntry head)
                    [.relabel bodyInput]
                    (.jump (ProcLabel.body head.name)) with
              | none =>
                  simp [hShape, hFrame, hAdapter] at hLower
              | some adapter =>
                  cases hBody :
                      TypedCfgCompiler.compileBlock? head.body
                        { procs := allProcs
                          leaveLabel? := some (ProcLabel.exit head.name)
                          leaveShape? :=
                            some (TypedCfgCompiler.Shape.procExit head) }
                        supply (ProcLabel.body head.name) bodyInput
                        (ProcLabel.exit head.name) with
                  | none =>
                      simp [hShape, hFrame, hAdapter, hBody] at hLower
                  | some compiled =>
                      cases hRequire :
                          compiled.requireFallthrough?
                            (TypedCfgCompiler.Shape.procExit head) with
                      | none =>
                          simp [hShape, hFrame, hAdapter, hBody, hRequire]
                            at hLower
                      | some unit =>
                          cases unit
                          cases hTail :
                              TypedCfgCompiler.lowerProcBodiesWithShapes?
                                entryShapes allProcs rest compiled.next with
                          | none =>
                              simp [hShape, hFrame, hAdapter, hBody, hRequire,
                                hTail] at hLower
                          | some tailResult =>
                              rcases tailResult with
                                ⟨tailBlocks, tailNext, tailCalls⟩
                              simp [hShape, hFrame, hAdapter, hBody, hRequire,
                                hTail] at hLower
                              rcases hLower with ⟨rfl, rfl, rfl⟩
                              have hTBbody : TokenBottomOrNone bodyInput :=
                                tokenBottomOrNone_of_adapter_frame
                                  (TypedCfgCompilerFacts.Shape.requireReturnTokenDepth?_eq_some_iff.mp
                                    hFrame)
                                  hAdapter
                              simp only [List.cons_append, List.mem_cons,
                                List.mem_append] at hMem
                              rcases hMem with hEq | hIn | hThere
                              · refine
                                  ⟨head, supply, ProcLabel.body head.name,
                                    bodyInput, compiled, hBody, hTBbody,
                                    Or.inr ?_⟩
                                subst hEq
                                exact input_of_mkBlock? hAdapter
                              · exact
                                  ⟨head, supply, ProcLabel.body head.name,
                                    bodyInput, compiled, hBody, hTBbody,
                                    Or.inl hIn⟩
                              · obtain
                                  ⟨proc, bsupply, e, input, bodyResult,
                                    hCompile, hTB, hDisj⟩ :=
                                  ih hTail hThere
                                exact
                                  ⟨proc, bsupply, e, input, bodyResult,
                                    hCompile, hTB, hDisj⟩

open TypedCfgPreservation (BlocksInProgram)
open TypedCfgPreservation.Program (GeneratedContext)

/-- **Main-body arm.**  Every main-category block input is token-at-bottom: the main body is
compiled from the token-free root `Shape.caller`, so the threading mutual carries
`TokenBottomOrNone` to every emitted block. -/
theorem main_tbResult
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg) :
    TbResult context.main :=
  tbResult_of_compileBlock? context.mainCompile tokenBottomOrNone_caller

/-- **Proc-body arm.**  Every proc-category block input is token-at-bottom: either it is a body
block of some proc (drilled by the threading mutual from the token-at-bottom seed) or it is a
proc-entry adapter whose input is `procEntry proc`. -/
theorem proc_tokenBottom
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.procBlocks) :
    TokenBottomOrNone block.input := by
  obtain ⟨proc, bsupply, entry, input, bodyResult, hCompile, hTB, hDisj⟩ :=
    mem_procBlocks_tokenBottom context.procsCompile hMem
  rcases hDisj with hBody | hAdapterInput
  · exact (tbResult_of_compileBlock? hCompile hTB).1 block hBody
  · rw [hAdapterInput]
    exact TokenBottomShape.tokenBottomOrNone_procEntry proc

/-- **The per-entry static token-at-bottom fact** (frontier item 1).  At an arbitrary reached
entry, the block found there has a token-at-bottom input shape.  Classifies the block with
`block_category` and dispatches: main / proc bodies via the threading arms, dispatch blocks are
`procExit` (token at bottom), the programEnd block's input is the main fallthrough (token-free or
token-at-bottom). -/
theorem tokenBottomOrNone_of_findBlock?
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {label : Assembly.Label} {block : TypedCfg.Block}
    (hFind : cfg.findBlock? label = some block) :
    TokenBottomOrNone block.input := by
  rcases context.block_category hFind with hMain | hProc | hDispatch | hEnd
  · exact (main_tbResult context).1 block hMain
  · exact proc_tokenBottom context hProc
  · obtain ⟨proc, _hProcMem, _hLookup, rfl⟩ :=
      dispatchBlock_provenance context hSourceWF hDispatch
    exact TokenBottomShape.tokenBottomOrNone_procExit proc
  · subst hEnd
    show TokenBottomOrNone (context.main.fallthrough?.getD TypedCfg.Shape.caller)
    cases hF : context.main.fallthrough? with
    | none =>
        simp only [hF, Option.getD_none]
        exact tokenBottomOrNone_caller
    | some ft =>
        simp only [hF, Option.getD_some]
        exact (main_tbResult context).2 ft hF

/-- **The total block-entry `StackRealizes` bridge, fully discharged** (frontier items 1 + 2).
Combines the total bridge `stackRealizes_of_realizedWitnessFC` (`InteractionHInvClose.lean`, total
modulo the `TokenBottomOrNone` premise) with the per-entry static fact
`tokenBottomOrNone_of_findBlock?`: at any reached entry whose strengthened witness holds, the
target stack realizes the block's input shape — no side condition. -/
theorem stackRealizes_of_realizedWitnessFC_total
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {label : Assembly.Label} {state : EVMState} {block : TypedCfg.Block}
    (hReal :
      InteractionFrameConsistent.realizedWitnessFC source cfg context.calls label state)
    (hFind : cfg.findBlock? label = some block) :
    TypedCfg.StackRealizes block.input state :=
  InteractionFrameConsistent.stackRealizes_of_realizedWitnessFC hReal hFind
    (tokenBottomOrNone_of_findBlock? context hSourceWF hFind)

end TokenBottomThread
end Structured
end EvmCompiler
