import EvmCompiler.Structured.InteractionMachineryCoupling

/-!
# Block-generation shape classification (route-2 provenance capstone)

Session 35 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-34).

The route-B `hInv` endgame needs, at each reachable CFG entry, the *static*
classification identifying which compiler construct emitted the block there — the
input each per-category successor supplier (`InteractionMachineryCoupling`,
`InteractionConstructCoupling`, `InteractionCodeConstructCoupling`) consumes.  This
module banks that classification predicate `BlockGenShape` (the re-corrected
NINE-disjunct predicate pinned in §Session-34) together with the strong-induction
mutual proving every block emitted by a successful compilation satisfies it.

* `codeFact_of_switchHead` — synthesises the `.code scrutinee` compile fact for the
  switch head block (the reverse of `mkCodeBlock?`), feeding the `codeHead` disjunct
  from the `switch` arm.
* `BlockGenShape cfg block` — the purely-static classification: compile facts +
  block-shape/type facts.  No runtime `StateRel`/`SourceFrameFits`/`openStep` — those
  are supplied separately by `hInv`.
* `GenShapeResult result cfg` — `∀ block ∈ result.blocks, BlockGenShape cfg block`,
  with an `append` lemma mirroring `ActiveResult.append`.
* the 5-function capstone mutual mirroring `activeResult_of_compile*`
  (`TypedCfgCompilerActive.lean:77`), threading `BlocksInProgram result cfg` down the
  recursion.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionBlockGenShape

/--
**Switch-head `.code` compile fact.**

The switch lowering emits its head block as
`mkCodeBlock? entry input scrutinee (.jump firstTest)`, which is byte-for-byte the
single block a `compileStmtFuel? (.code scrutinee) … (regular := firstTest)` emits.
This lemma reverse-engineers that `.code` emission: from the scrutinee's type fact it
produces the exact single-block `.code` compile result, so the `switch` arm of the
capstone mutual can classify its head via the `codeHead` disjunct.
-/
theorem codeFact_of_switchHead
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry firstTest : Assembly.Label} {input valueShape : TypedCfg.Shape}
    (hType : TypedCfgCompiler.Code.type? scrutinee input = some valueShape) :
    TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.code scrutinee) ctx
        supply entry input firstTest =
      some
        { blocks :=
            [{ label := entry
               input := input
               body := TypedCfgCompiler.Code.toCfg scrutinee
               output := valueShape
               term := .jump firstTest }]
          next := supply + 1
          calls := []
          fallthrough? := some valueShape } := by
  simp [TypedCfgCompiler.compileStmtFuel?, TypedCfgCompiler.mkCodeBlock?, hType]

/--
**The re-corrected NINE-disjunct block-generation classification predicate.**

`BlockGenShape cfg block` classifies `block` by the compiler construct that emitted it,
carrying exactly the static inputs the matching successor supplier consumes.  The three
head arms (`code`/`if`/`call`) carry the construct's compile fact plus
`BlocksInProgram result cfg`; the machinery arms carry the concrete block shape plus its
type/`findBlock?`/membership facts.  `nilJoin` covers both the empty-statement-list join
block and `brk`/`cont`/`leave` (§Session-34 correction 1); `terminalHalt` is the sole
vacuous arm.  Dispatch/programEnd blocks are NOT here — they are `block_category`'s other
arms.
-/
inductive BlockGenShape (cfg : TypedCfg.Program) : TypedCfg.Block → Prop where
  | codeHead
      {block : TypedCfg.Block}
      {compilerFuel : Nat} {code : Structured.Code}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {regular : Assembly.Label} {result : TypedCfgCompiler.Result}
      (hCompile :
        TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.code code) ctx
            supply block.label block.input regular = some result)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
      BlockGenShape cfg block
  | ifHead
      {block : TypedCfg.Block}
      {compilerFuel : Nat} {cond : Structured.Code} {body : Structured.Block}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {regular : Assembly.Label} {result : TypedCfgCompiler.Result}
      (hCompile :
        TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.if_ cond body) ctx
            supply block.label block.input regular = some result)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
      BlockGenShape cfg block
  | callHead
      {block : TypedCfg.Block}
      {compilerFuel : Nat} {name : Structured.Name} {proc : Structured.Proc}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {regular : Assembly.Label} {result : TypedCfgCompiler.Result}
      (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
      (hCompile :
        TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name) ctx
            supply block.label block.input regular = some result)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
      BlockGenShape cfg block
  | forCond
      {input output : TypedCfg.Shape}
      {label trueLabel falseLabel : Assembly.Label}
      {cond : Structured.Code}
      (hType : TypedCfgCompiler.Code.type? cond input = some output)
      (hSource : TypedCfgCompiler.Shape.requireSourceWords? 1 output = some ())
      (hFind :
        cfg.findBlock? label =
          some
            { label := label
              input := input
              body := TypedCfgCompiler.Code.toCfg cond
              output := output
              term := .jumpi trueLabel falseLabel }) :
      BlockGenShape cfg
        { label := label
          input := input
          body := TypedCfgCompiler.Code.toCfg cond
          output := output
          term := .jumpi trueLabel falseLabel }
  | switchTest
      {testLabel caseLabel nextTest : Assembly.Label}
      {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot} {caseValue : Word}
      {result : TypedCfgCompiler.Result}
      (hHead : valueShape.slots.head? = some slot)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
      (hMem :
        { label := testLabel
          input := valueShape
          body := [.dup 0, .push caseValue, .prim .eq]
          output := TypedCfgCompilerFacts.Switch.testOutput valueShape
          term := .jumpi caseLabel nextTest } ∈ result.blocks) :
      BlockGenShape cfg
        { label := testLabel
          input := valueShape
          body := [.dup 0, .push caseValue, .prim .eq]
          output := TypedCfgCompilerFacts.Switch.testOutput valueShape
          term := .jumpi caseLabel nextTest }
  | caseEntryPop
      {entry label : Assembly.Label}
      {input output : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result}
      (hType : TypedCfg.Instr.type? .pop input = some output)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
      (hMem :
        { label := entry
          input := input
          body := [.pop]
          output := output
          term := .jump label } ∈ result.blocks) :
      BlockGenShape cfg
        { label := entry
          input := input
          body := [.pop]
          output := output
          term := .jump label }
  | nilJoin
      {entry exitLabel : Assembly.Label} {input : TypedCfg.Shape}
      (hFind :
        cfg.findBlock? entry =
          some
            { label := entry
              input := input
              body := []
              output := input
              term := .jump exitLabel }) :
      BlockGenShape cfg
        { label := entry
          input := input
          body := []
          output := input
          term := .jump exitLabel }
  | procAdapter
      {entry bodyLabel : Assembly.Label}
      {blockInput relabelTarget output : TypedCfg.Shape}
      (hType :
        TypedCfg.Instr.type? (.relabel relabelTarget) blockInput = some output)
      (hFind :
        cfg.findBlock? entry =
          some
            { label := entry
              input := blockInput
              body := [.relabel relabelTarget]
              output := output
              term := .jump bodyLabel }) :
      BlockGenShape cfg
        { label := entry
          input := blockInput
          body := [.relabel relabelTarget]
          output := output
          term := .jump bodyLabel }
  | terminalHalt
      {entry : Assembly.Label} {input : TypedCfg.Shape}
      {kind : Assembly.HaltKind}
      (hFind :
        cfg.findBlock? entry =
          some
            { label := entry
              input := input
              body := []
              output := input
              term := .halt kind }) :
      BlockGenShape cfg
        { label := entry
          input := input
          body := []
          output := input
          term := .halt kind }

/--
Every block emitted by one Structured compiler result is classified by
`BlockGenShape` — the `BlockGenShape` analogue of `ActiveResult`.
-/
def GenShapeResult (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) : Prop :=
  ∀ block, block ∈ result.blocks → BlockGenShape cfg block

namespace GenShapeResult

theorem append
    {left right : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hLeft : GenShapeResult left cfg)
    (hRight : GenShapeResult right cfg) :
    GenShapeResult (left.append right) cfg := by
  intro block hMem
  rcases List.mem_append.mp hMem with hLeftMem | hRightMem
  · exact hLeft block hLeftMem
  · exact hRight block hRightMem

end GenShapeResult

/-!
## The block-generation classification capstone mutual

Mirrors `activeResult_of_compile*` (`TypedCfgCompilerActive.lean:77`) but concludes
`GenShapeResult result cfg`, threading `BlocksInProgram result cfg` down the recursion
(each sub-result's `BlocksInProgram` follows from block-list inclusion) and emitting the
matching `BlockGenShape` disjunct at each block.  No `ReturnTokenActive` invariant is
needed — the classification is purely structural.
-/

mutual

theorem genShape_of_compileBlockFuel?
    {fuel : Nat} {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? fuel block ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    GenShapeResult result cfg := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
  | succ compilerFuel =>
      unfold TypedCfgCompiler.compileBlockFuel? at hCompile
      exact genShape_of_compileStmtListFuel? hCompile hBlocks

theorem genShape_of_compileStmtListFuel?
    {fuel : Nat} {stmts : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? fuel stmts ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    GenShapeResult result cfg := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
  | succ compilerFuel =>
      cases stmts with
      | nil =>
          simp [TypedCfgCompiler.compileStmtListFuel?,
            TypedCfgCompiler.mkBlock?] at hCompile
          cases hCompile
          intro block hMem
          have hFind := hBlocks block hMem
          simp only [List.mem_singleton] at hMem
          subst block
          exact BlockGenShape.nilJoin hFind
      | cons stmt rest =>
          rcases
              TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
                hCompile with
            ⟨headResult, hHead, hNoTail | hTail⟩
          · rcases hNoTail with ⟨_hFallthrough, rfl⟩
            exact genShape_of_compileStmtFuel? hHead hBlocks
          · rcases hTail with
              ⟨tailInput, tailResult,
                _hFallthrough, hTailCompile, rfl⟩
            have hHeadBlocks :=
              TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
            have hTailBlocks :=
              TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
            exact
              (genShape_of_compileStmtFuel? hHead hHeadBlocks).append
                (genShape_of_compileStmtListFuel? hTailCompile hTailBlocks)

theorem genShape_of_compileStmtFuel?
    {fuel : Nat} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    GenShapeResult result cfg := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
  | succ compilerFuel =>
      cases stmt with
      | code code =>
          obtain ⟨output, _hType, rfl⟩ :=
            TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_code
              hCompile
          intro block hMem
          simp only [List.mem_singleton] at hMem
          subst block
          exact BlockGenShape.codeHead hCompile hBlocks
      | if_ cond body =>
          obtain
              ⟨output, _condition, bodyResult,
                _hType, _hSource, _hHead, hBody, _hRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
          have hBodyBlocks :
              TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
            intro b hb
            exact hBlocks b (List.mem_cons_of_mem _ hb)
          have hBodyGen := genShape_of_compileBlockFuel? hBody hBodyBlocks
          intro block hMem
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hBodyMem
          · exact BlockGenShape.ifHead hCompile hBlocks
          · exact hBodyGen block hBodyMem
      | switch scrutinee cases defaultBody =>
          obtain
              ⟨valueShape, _valueSlot, caseResult, defaultResult,
                hType, _hSource, hHead, hCases, hDefault, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch
              hCompile
          have hPop :
              TypedCfg.Instr.type? .pop valueShape =
                some { valueShape with slots := valueShape.slots.tail } := by
            rcases valueShape with ⟨slots, tail⟩
            cases slots with
            | nil => simp at hHead
            | cons slot rest => simp [TypedCfg.Instr.type?]
          have hCaseBlocks :
              TypedCfgPreservation.BlocksInProgram caseResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hDefaultBlocks :
              TypedCfgPreservation.BlocksInProgram defaultResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hCaseGen :=
            genShape_of_compileCasesFuel? hHead hPop hCases hCaseBlocks
          have hDefaultGen :=
            genShape_of_compileDefaultFuel? hPop hDefault hDefaultBlocks
          intro block hMem
          simp only [List.mem_cons, List.mem_append] at hMem
          rcases hMem with (rfl | hCaseMem) | hDefaultMem
          · refine
              BlockGenShape.codeHead
                (codeFact_of_switchHead
                  (compilerFuel := 0) (ctx := ctx) (supply := supply)
                  (firstTest :=
                    TypedCfgCompilerFacts.Switch.casesEntryLabel supply 0 cases)
                  hType) ?_
            intro b hb
            simp only [List.mem_singleton] at hb
            subst b
            refine hBlocks _ ?_
            simp
          · exact hCaseGen block hCaseMem
          · exact hDefaultGen block hDefaultMem
      | for_ init cond post body =>
          obtain
              ⟨initResult, loopInput, condOutput, _condition,
                bodyResult, postResult, hInit, _hInitFallthrough,
                hType, hSource, _hHead, hBody, _hBodyRequire,
                hPost, _hPostRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Loop.components_of_compileStmtFuel?_for hCompile
          have hInitBlocks :
              TypedCfgPreservation.BlocksInProgram initResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hBodyBlocks :
              TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hPostBlocks :
              TypedCfgPreservation.BlocksInProgram postResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hInitGen := genShape_of_compileBlockFuel? hInit hInitBlocks
          have hBodyGen := genShape_of_compileBlockFuel? hBody hBodyBlocks
          have hPostGen := genShape_of_compileBlockFuel? hPost hPostBlocks
          intro block hMem
          have hFind := hBlocks block hMem
          rcases List.mem_append.mp hMem with hBeforePost | hPostMem
          rcases List.mem_append.mp hBeforePost with hBeforeBody | hBodyMem
          rcases List.mem_append.mp hBeforeBody with hInitMem | hLoopMem
          · exact hInitGen block hInitMem
          · have hBlock :
                block =
                  { label := LabelSupply.label supply 0
                    input := loopInput
                    body := TypedCfgCompiler.Code.toCfg cond
                    output := condOutput
                    term :=
                      .jumpi (LabelSupply.label supply 1) regular } := by
              simpa using hLoopMem
            subst block
            exact BlockGenShape.forCond hType hSource hFind
          · exact hBodyGen block hBodyMem
          · exact hPostGen block hPostMem
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
                  by_cases hInput : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    intro block hMem
                    have hFind := hBlocks block hMem
                    simp only [List.mem_singleton] at hMem
                    subst block
                    exact BlockGenShape.nilJoin hFind
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
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
                  by_cases hInput : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    intro block hMem
                    have hFind := hBlocks block hMem
                    simp only [List.mem_singleton] at hMem
                    subst block
                    exact BlockGenShape.nilJoin hFind
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
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
                  by_cases hInput : input = expected
                  · subst expected
                    simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, TypedCfgCompiler.mkBlock?] at hCompile
                    cases hCompile
                    intro block hMem
                    have hFind := hBlocks block hMem
                    simp only [List.mem_singleton] at hMem
                    subst block
                    exact BlockGenShape.nilJoin hFind
                  · simp [TypedCfgCompiler.checkedJumpOrInvalid,
                      hLabel, hShape, hInput] at hCompile
      | call name =>
          obtain ⟨proc, hLookup⟩ :=
            TypedCfgCompilerFacts.Call.exists_lookup_of_compileStmtFuel?_call
              hCompile
          obtain
              ⟨returnShape, _output, _hSource, _hAfter, _hType, rfl⟩ :=
            TypedCfgCompilerFacts.Call.components_of_compileStmtFuel?_call
              hLookup hCompile
          intro block hMem
          simp only [List.mem_singleton] at hMem
          subst block
          exact BlockGenShape.callHead hLookup hCompile hBlocks
      | terminal kind =>
          obtain ⟨_hSource, rfl⟩ :=
            TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal
              hCompile
          intro block hMem
          have hFind := hBlocks block hMem
          simp only [List.mem_singleton] at hMem
          subst block
          exact BlockGenShape.terminalHalt hFind

theorem genShape_of_compileCasesFuel?
    {fuel : Nat} {cases : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hHead : valueShape.slots.head? = some slot)
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? fuel cases ctx
          base supply idx valueShape bodyShape regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    GenShapeResult result cfg := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
  | succ compilerFuel =>
      cases cases with
      | nil =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          intro block hMem
          simp at hMem
      | cons head rest =>
          rcases head with ⟨caseValue, body⟩
          obtain
              ⟨bodyResult, tail, hBodyCompile, _hRequire,
                hTailCompile, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPop hCompile
          have hBodyBlocks :
              TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hTailBlocks :
              TypedCfgPreservation.BlocksInProgram tail cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hBodyGen :=
            genShape_of_compileBlockFuel? hBodyCompile hBodyBlocks
          have hTailGen :=
            genShape_of_compileCasesFuel? hHead hPop hTailCompile hTailBlocks
          intro block hMem
          simp only [List.mem_cons, List.mem_append] at hMem
          rcases hMem with (rfl | rfl | hBodyMem) | hTailMem
          · refine BlockGenShape.switchTest hHead hBlocks ?_
            simp
          · refine BlockGenShape.caseEntryPop hPop hBlocks ?_
            simp
          · exact hBodyGen block hBodyMem
          · exact hTailGen block hTailMem

theorem genShape_of_compileDefaultFuel?
    {fuel : Nat} {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? fuel defaultBody ctx
          supply entry valueShape bodyShape regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    GenShapeResult result cfg := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileDefaultFuel?] at hCompile
  | succ compilerFuel =>
      cases defaultBody with
      | none =>
          have hEq :=
            TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_none
              hPop hCompile
          subst hEq
          intro block hMem
          simp only [List.mem_singleton] at hMem
          subst block
          refine BlockGenShape.caseEntryPop hPop hBlocks ?_
          simp
      | some body =>
          obtain ⟨bodyResult, hBodyCompile, _hRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
              hPop hCompile
          have hBodyBlocks :
              TypedCfgPreservation.BlocksInProgram bodyResult cfg := by
            intro b hb
            exact hBlocks b (List.mem_cons_of_mem _ hb)
          have hBodyGen :=
            genShape_of_compileBlockFuel? hBodyCompile hBodyBlocks
          intro block hMem
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hBodyMem
          · refine BlockGenShape.caseEntryPop hPop hBlocks ?_
            simp
          · exact hBodyGen block hBodyMem

end

end InteractionBlockGenShape
end Structured
end EvmCompiler
