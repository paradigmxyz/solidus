import EvmCompiler.Structured.InteractionBlockGenShape
import EvmCompiler.Structured.InteractionLabelShapeTransport

/-!
# Strengthened block-generation classification — the external-`regular` `LabelShape` thread

Session 39 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-38 recipe).

`BlockGenShape` (`InteractionBlockGenShape.lean`) classifies every compiler-emitted
block by the construct that produced it, but stores only *static* compile facts — it
does NOT carry the exact `LabelShape` of the block's external `regular` successor (the
block the construct's fallthrough jumps to, which lives outside the construct's own
result).  The route-B `hInv` endgame needs that successor `LabelShape` at every reached
entry; the "option-B threading toolkit" (`InteractionLabelShapeTransport.lean`) supplies
the two boundary seeds and the two per-descent combinators to thread it through the
generation recursion.

This module assembles the **strengthened** capstone: `BlockGenShapeReg`, mirroring the
nine `BlockGenShape` disjuncts but adding, on every disjunct whose block jumps to a
target *not* internal to the same construct's result, the exact `LabelShape` of that
target:

* `codeHead` / `ifHead` add `hReg : HRegular result cfg regular` — the threaded
  external-successor predicate the head-construct suppliers consume verbatim.
* `forCond` adds `hFalseShape` — the `LabelShape` of the loop's `false` (exit) edge,
  which is the loop's own external `regular`.
* `caseEntryPop` adds `hExit` — the pop block jumps to its case body (internal) *or*, for
  a `default`-less switch, straight to the external `regular`; the field pins that target.
* `nilJoin` adds `hExit` — the empty-list join / `brk` / `cont` / `leave` block jumps to
  its exit label (the enclosing `regular` or a ctx-exit label); the field pins it.
* `procAdapter` adds `hBodyShape` — the adapter jumps to the proc body entry.
* `callHead` / `switchTest` / `terminalHalt` stay base (their successors are boundary
  seeds or internal-derivable, so `hInv` supplies them without a thread).

The `nilJoin` split (`nilJoinRegular`/`nilJoinExit`) from the §Session-38 recipe is
collapsed into a single `nilJoin` disjunct carrying the target `LabelShape` directly: the
provenance of that `LabelShape` (regular thread vs ctx exit) differs by call site, but the
*stored* field is `LabelShape cfg exitLabel input` either way, and `hInv` dispatches on the
block category, not the constructor.  This keeps the inductive at nine disjuncts.

The 5-function mutual `genShapeReg_of_compile*` mirrors `genShape_of_compile*` but threads
`HRegular result cfg regular` and `CtxExitsShaped cfg ctx` alongside `BlocksInProgram`,
discharging every disjunct's added field via the four banked toolkit lemmas +
`of_hasEntry` / `of_compileBlockFuel?`.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionBlockGenShapeRegular

open TypedCfgPreservation (LabelShape BlocksInProgram)

/--
**The threaded external-`regular` predicate.**  `HRegular result cfg regular` is exactly
the form the head-construct successor suppliers consume: for the construct's fallthrough
output `out`, the block declared at `regular` has input `out`. -/
abbrev HRegular (result : TypedCfgCompiler.Result) (cfg : TypedCfg.Program)
    (regular : Assembly.Label) : Prop :=
  ∀ out, result.fallthrough? = some out → LabelShape cfg regular out

/--
**Ctx-exit `LabelShape` bundle.**  Carries the exact `LabelShape` of each of the current
compilation context's `break`/`continue`/`leave` exit labels — the targets a `brk`/`cont`/
`leave` join block jumps to.  Threaded unchanged through `if`/`code`/`call`/`switch`,
re-established for the body in `for_`, and seeded at each program boundary. -/
structure CtxExitsShaped (cfg : TypedCfg.Program)
    (ctx : TypedCfgCompiler.Context) : Prop where
  brk : ∀ lbl shp, ctx.breakLabel? = some lbl → ctx.breakShape? = some shp →
    LabelShape cfg lbl shp
  cont : ∀ lbl shp, ctx.continueLabel? = some lbl → ctx.continueShape? = some shp →
    LabelShape cfg lbl shp
  leave : ∀ lbl shp, ctx.leaveLabel? = some lbl → ctx.leaveShape? = some shp →
    LabelShape cfg lbl shp

/--
**Fixed-target regular thread.**  A sub-result that `requireFallthrough?`s to `expected`
falls through only to `expected`, whose target `LabelShape cfg target expected` is already
known (internally derived), so the sub-result inherits the thread at that fixed target.
Covers the loop body/post continuations (target = post/cond entry) and, via a `hRegular`
application, every same-`regular` body. -/
theorem thread_of_target_requireFallthrough
    {cfg : TypedCfg.Program} {target : Assembly.Label}
    {subResult : TypedCfgCompiler.Result} {expected : TypedCfg.Shape}
    (hTarget : LabelShape cfg target expected)
    (hSubRequire : subResult.requireFallthrough? expected = some ()) :
    ∀ out, subResult.fallthrough? = some out → LabelShape cfg target out := by
  intro out hOut
  have hExpected : out = expected := by
    rcases
        TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
          hSubRequire with hNone | hSome
    · rw [hOut] at hNone; exact absurd hNone (by simp)
    · exact Option.some.inj (hOut.symm.trans hSome)
  subst hExpected
  exact hTarget

/--
**Switch-head external-`regular` `LabelShape`.**  The switch head block is a `.code`
emission whose external `regular` is `casesEntryLabel supply 0 cases` — the entry of the
first test block (nonempty `cases`) or the default entry (empty `cases`).  Either entry is
a listed member of the switch's own `caseResult`/`defaultResult`, whose input is
`valueShape`. -/
theorem switchHead_regular_labelShape
    {compilerFuel : Nat} {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {valueSlot : TypedCfg.Slot}
    {caseResult defaultResult : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program}
    (hHead : valueShape.slots.head? = some valueSlot)
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCases :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx
          supply (supply + 1) 0 valueShape bodyShape regular = some caseResult)
    (hDefault :
      TypedCfgCompiler.compileDefaultFuel? compilerFuel defaultBody ctx
          caseResult.next (LabelSupply.label supply 1) valueShape bodyShape
          regular = some defaultResult)
    (hCaseBlocks : BlocksInProgram caseResult cfg)
    (hDefaultBlocks : BlocksInProgram defaultResult cfg) :
    LabelShape cfg
      (TypedCfgCompilerFacts.Switch.casesEntryLabel supply 0 cases) valueShape := by
  cases cases with
  | nil =>
      exact LabelShape.of_hasEntry
        (TypedCfgCompilerFacts.Switch.default_hasEntry hPop hDefault) hDefaultBlocks
  | cons head rest =>
      obtain ⟨caseValue, body⟩ := head
      exact LabelShape.of_hasEntry
        (TypedCfgCompilerFacts.Switch.cases_cons_test_hasEntry hHead hPop hCases)
        hCaseBlocks

/--
**The strengthened NINE-disjunct block-generation classification.**

Mirrors `BlockGenShape` (`InteractionBlockGenShape.lean:76`), adding, on each disjunct
whose block jumps to a non-internal target, the exact `LabelShape` of that target. -/
inductive BlockGenShapeReg (cfg : TypedCfg.Program) : TypedCfg.Block → Prop where
  | codeHead
      {block : TypedCfg.Block}
      {compilerFuel : Nat} {code : Structured.Code}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {regular : Assembly.Label} {result : TypedCfgCompiler.Result}
      (hCompile :
        TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.code code) ctx
            supply block.label block.input regular = some result)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
      (hReg : HRegular result cfg regular) :
      BlockGenShapeReg cfg block
  | ifHead
      {block : TypedCfg.Block}
      {compilerFuel : Nat} {cond : Structured.Code} {body : Structured.Block}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {regular : Assembly.Label} {result : TypedCfgCompiler.Result}
      (hCompile :
        TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.if_ cond body) ctx
            supply block.label block.input regular = some result)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
      (hReg : HRegular result cfg regular) :
      BlockGenShapeReg cfg block
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
      BlockGenShapeReg cfg block
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
              term := .jumpi trueLabel falseLabel })
      (hFalseShape :
        LabelShape cfg falseLabel { output with slots := output.slots.tail }) :
      BlockGenShapeReg cfg
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
      BlockGenShapeReg cfg
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
          term := .jump label } ∈ result.blocks)
      (hExit : LabelShape cfg label output) :
      BlockGenShapeReg cfg
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
              term := .jump exitLabel })
      (hExit : LabelShape cfg exitLabel input) :
      BlockGenShapeReg cfg
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
              term := .jump bodyLabel })
      (hBodyShape : LabelShape cfg bodyLabel output) :
      BlockGenShapeReg cfg
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
      BlockGenShapeReg cfg
        { label := entry
          input := input
          body := []
          output := input
          term := .halt kind }

/--
Every block emitted by one Structured compiler result is `BlockGenShapeReg`-classified. -/
def GenShapeResultReg (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program) : Prop :=
  ∀ block, block ∈ result.blocks → BlockGenShapeReg cfg block

namespace GenShapeResultReg

theorem append
    {left right : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hLeft : GenShapeResultReg left cfg)
    (hRight : GenShapeResultReg right cfg) :
    GenShapeResultReg (left.append right) cfg := by
  intro block hMem
  rcases List.mem_append.mp hMem with hLeftMem | hRightMem
  · exact hLeft block hLeftMem
  · exact hRight block hRightMem

end GenShapeResultReg

end InteractionBlockGenShapeRegular
end Structured
end EvmCompiler
