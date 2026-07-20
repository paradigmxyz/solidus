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

end InteractionBlockGenShape
end Structured
end EvmCompiler
