import EvmCompiler.Structured.InteractionBlockGenShape
import EvmCompiler.Structured.InteractionLabelShapeTransport
import EvmCompiler.Structured.InteractionHInvObligations

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
**Callee `procEntry` `LabelShape`/`WF` bundle** (the `callHead` group-(e) thread).  For every
proc reachable by a `.call` in the current compilation context (`lookup? name ctx.procs`),
carries the exact `LabelShape` of the callee's `ProcLabel.entry` block (whose input is the
callee's `procEntry` shape) together with the callee's well-formedness.  `ctx.procs` is
constant through the whole generation recursion (the compiler never rewrites it), so this
bundle threads UNCHANGED through every descent and is seeded at each program boundary from the
`GeneratedContext` (`LabelShape.procEntry`) + `source.WF` (`procWF_of_lookup?`). -/
structure ProcsShaped (cfg : TypedCfg.Program)
    (ctx : TypedCfgCompiler.Context) : Prop where
  get : ∀ {name : Structured.Name} {proc : Structured.Proc},
    Structured.ProcList.lookup? name ctx.procs = some proc →
    LabelShape cfg (ProcLabel.entry name)
        (TypedCfgCompiler.Shape.procEntry proc) ∧ proc.WF

/-- `ProcsShaped` depends only on `ctx.procs`, so it transfers across any context update that
preserves the proc list (the `break`/`continue`/`leave` re-scopings inside `for_`). -/
theorem ProcsShaped.of_procs_eq
    {cfg : TypedCfg.Program} {ctx ctx' : TypedCfgCompiler.Context}
    (h : ctx'.procs = ctx.procs)
    (hProcs : ProcsShaped cfg ctx) :
    ProcsShaped cfg ctx' :=
  ⟨fun hLookup => hProcs.get (h ▸ hLookup)⟩

/-- Seed `ProcsShaped` at a program boundary whose compile context's proc list is the source
program's (`ctx.procs = source.procs`): each callee's entry `LabelShape` is
`LabelShape.procEntry`, each callee's `WF` is `procWF_of_lookup?`. -/
theorem ProcsShaped.seed
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {ctx : TypedCfgCompiler.Context}
    (hProcsEq : ctx.procs = source.procs) :
    ProcsShaped cfg ctx :=
  ⟨fun {name proc} hLookup => by
    rw [hProcsEq] at hLookup
    have hName : proc.name = name :=
      Structured.ProcList.name_of_lookup? hLookup
    refine ⟨?_, Structured.Program.procWF_of_lookup? hSourceWF hLookup⟩
    have h := TypedCfgPreservation.LabelShape.procEntry context hLookup
    rw [hName] at h
    exact h⟩

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
inductive BlockGenShapeReg (cfg : TypedCfg.Program)
    (sourceProgram : Structured.Program)
    (calls : List TypedCfgCompiler.DispatchSite) : TypedCfg.Block → Prop where
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
      BlockGenShapeReg cfg sourceProgram calls block
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
      BlockGenShapeReg cfg sourceProgram calls block
  | callHead
      {block : TypedCfg.Block}
      {compilerFuel : Nat} {name : Structured.Name} {proc : Structured.Proc}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {regular : Assembly.Label} {result : TypedCfgCompiler.Result}
      (hProcs : ctx.procs = sourceProgram.procs)
      (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
      (hCompile :
        TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name) ctx
            supply block.label block.input regular = some result)
      (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg)
      (hResultCalls : TypedCfgPreservation.CallsInProgram result calls)
      (hEntryShape :
        LabelShape cfg (ProcLabel.entry name)
          (TypedCfgCompiler.Shape.procEntry proc))
      (hProcWF : proc.WF)
      (hReg : HRegular result cfg regular) :
      BlockGenShapeReg cfg sourceProgram calls block
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
        LabelShape cfg falseLabel { output with slots := output.slots.tail })
      (hTrueShape :
        LabelShape cfg trueLabel { output with slots := output.slots.tail }) :
      BlockGenShapeReg cfg sourceProgram calls
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
          term := .jumpi caseLabel nextTest } ∈ result.blocks)
      (hPopExists :
        ∀ source : RunState,
          TypedCfgCompiler.Shape.SourceFrameFits valueShape source.evm.stack.length →
            ∃ (stack : EvmYul.Stack Word) (value : Word),
              source.evm.stack.pop = some (stack, value))
      (hCaseShape : LabelShape cfg caseLabel valueShape)
      (hNextShape : LabelShape cfg nextTest valueShape) :
      BlockGenShapeReg cfg sourceProgram calls
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
      (hExit : LabelShape cfg label output)
      (hPopTransport :
        ∀ source : RunState,
          TypedCfgCompiler.Shape.SourceFrameFits input source.evm.stack.length →
            ∃ (stack : EvmYul.Stack Word) (value : Word),
              source.evm.stack.pop = some (stack, value) ∧
                TypedCfgCompiler.Shape.SourceFrameFits output
                  (source.withEVM
                    { source.evm with stack := stack }).evm.stack.length) :
      BlockGenShapeReg cfg sourceProgram calls
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
      BlockGenShapeReg cfg sourceProgram calls
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
      (hBodyShape : LabelShape cfg bodyLabel output)
      (hTransport :
        ∀ n, TypedCfgCompiler.Shape.SourceFrameFits blockInput n →
          TypedCfgCompiler.Shape.SourceFrameFits output n)
      (hInputActive : (blockInput.returnTokenDepth?).isSome) :
      BlockGenShapeReg cfg sourceProgram calls
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
      BlockGenShapeReg cfg sourceProgram calls
        { label := entry
          input := input
          body := []
          output := input
          term := .halt kind }

/--
Every block emitted by one Structured compiler result is `BlockGenShapeReg`-classified. -/
def GenShapeResultReg (result : TypedCfgCompiler.Result)
    (cfg : TypedCfg.Program)
    (sourceProgram : Structured.Program)
    (calls : List TypedCfgCompiler.DispatchSite) : Prop :=
  ∀ block, block ∈ result.blocks → BlockGenShapeReg cfg sourceProgram calls block

namespace GenShapeResultReg

theorem append
    {left right : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hLeft : GenShapeResultReg left cfg sourceProgram calls)
    (hRight : GenShapeResultReg right cfg sourceProgram calls) :
    GenShapeResultReg (left.append right) cfg sourceProgram calls := by
  intro block hMem
  rcases List.mem_append.mp hMem with hLeftMem | hRightMem
  · exact hLeft block hLeftMem
  · exact hRight block hRightMem

end GenShapeResultReg

/--
**Fixed-target regular thread (fallthrough form).**  Like
`thread_of_target_requireFallthrough`, but the sub-result's fallthrough shape is pinned
directly (`subResult.fallthrough? = some expected`) rather than via a `requireFallthrough?`
check.  Used for the loop `init` block, whose fallthrough is the loop entry shape. -/
theorem thread_of_target_fallthrough
    {cfg : TypedCfg.Program} {target : Assembly.Label}
    {subResult : TypedCfgCompiler.Result} {expected : TypedCfg.Shape}
    (hTarget : LabelShape cfg target expected)
    (hFall : subResult.fallthrough? = some expected) :
    ∀ out, subResult.fallthrough? = some out → LabelShape cfg target out := by
  intro out hOut
  have hExpected : out = expected := Option.some.inj (hOut.symm.trans hFall)
  subst hExpected
  exact hTarget

/-!
## The strengthened block-generation classification capstone mutual

Mirrors `genShape_of_compile*` (`InteractionBlockGenShape.lean:249`) but threads the
external-`regular` predicate `HRegular result cfg regular` and the ctx-exit bundle
`CtxExitsShaped cfg ctx` alongside `BlocksInProgram`, concluding `GenShapeResultReg`.  Each
disjunct's added `LabelShape` field is discharged by the threaded predicates + the
`thread_of_target_*` / `switchHead_regular_labelShape` helpers + `of_compileBlockFuel?`.
-/

mutual

theorem genShapeReg_of_compileBlockFuel?
    {fuel : Nat} {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? fuel block ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRegular : HRegular result cfg regular)
    (hCtx : CtxExitsShaped cfg ctx)
    (hProcs : ProcsShaped cfg ctx)
    (hProcsEq : ctx.procs = sourceProgram.procs)
    (hCalls : TypedCfgPreservation.CallsInProgram result calls) :
    GenShapeResultReg result cfg sourceProgram calls := by
  cases fuel with
  | zero =>
      simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
  | succ compilerFuel =>
      unfold TypedCfgCompiler.compileBlockFuel? at hCompile
      exact genShapeReg_of_compileStmtListFuel? hCompile hBlocks hRegular hCtx hProcs
        hProcsEq hCalls

theorem genShapeReg_of_compileStmtListFuel?
    {fuel : Nat} {stmts : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? fuel stmts ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRegular : HRegular result cfg regular)
    (hCtx : CtxExitsShaped cfg ctx)
    (hProcs : ProcsShaped cfg ctx)
    (hProcsEq : ctx.procs = sourceProgram.procs)
    (hCalls : TypedCfgPreservation.CallsInProgram result calls) :
    GenShapeResultReg result cfg sourceProgram calls := by
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
          exact BlockGenShapeReg.nilJoin hFind (hRegular _ rfl)
      | cons stmt rest =>
          rcases
              TypedCfgPreservation.Block.components_of_compileStmtListFuel?_cons
                hCompile with
            ⟨headResult, hHead, hNoTail | hTail⟩
          · rcases hNoTail with ⟨hFallthrough, rfl⟩
            exact
              genShapeReg_of_compileStmtFuel? hHead hBlocks
                (fun out hout => by
                  rw [hFallthrough] at hout; exact absurd hout (by simp))
                hCtx hProcs hProcsEq hCalls
          · rcases hTail with
              ⟨tailInput, tailResult, hHeadFall, hTailCompile, rfl⟩
            have hHeadBlocks :=
              TypedCfgPreservation.BlocksInProgram.left_of_append hBlocks
            have hTailBlocks :=
              TypedCfgPreservation.BlocksInProgram.right_of_append hBlocks
            have hHeadCalls :=
              TypedCfgPreservation.CallsInProgram.left_of_append hCalls
            have hTailCalls :=
              TypedCfgPreservation.CallsInProgram.right_of_append hCalls
            exact
              (genShapeReg_of_compileStmtFuel? hHead hHeadBlocks
                  (LabelShape.regularThread_tail_of_cons hHeadFall hTailCompile
                    hTailBlocks)
                  hCtx hProcs hProcsEq hHeadCalls).append
                (genShapeReg_of_compileStmtListFuel? hTailCompile hTailBlocks
                  hRegular hCtx hProcs hProcsEq hTailCalls)

theorem genShapeReg_of_compileStmtFuel?
    {fuel : Nat} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRegular : HRegular result cfg regular)
    (hCtx : CtxExitsShaped cfg ctx)
    (hProcs : ProcsShaped cfg ctx)
    (hProcsEq : ctx.procs = sourceProgram.procs)
    (hCalls : TypedCfgPreservation.CallsInProgram result calls) :
    GenShapeResultReg result cfg sourceProgram calls := by
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
          exact BlockGenShapeReg.codeHead hCompile hBlocks hRegular
      | if_ cond body =>
          obtain
              ⟨output, _condition, bodyResult,
                _hType, _hSource, _hHead, hBody, hBodyRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_if hCompile
          have hBodyBlocks : BlocksInProgram bodyResult cfg := by
            intro b hb
            exact hBlocks b (List.mem_cons_of_mem _ hb)
          have hBodyGen :=
            genShapeReg_of_compileBlockFuel? hBody hBodyBlocks
              (thread_of_target_requireFallthrough
                (hRegular { output with slots := output.slots.tail } rfl)
                hBodyRequire)
              hCtx hProcs hProcsEq hCalls
          intro block hMem
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hBodyMem
          · exact BlockGenShapeReg.ifHead hCompile hBlocks hRegular
          · exact hBodyGen block hBodyMem
      | switch scrutinee cases defaultBody =>
          obtain
              ⟨valueShape, _valueSlot, caseResult, defaultResult,
                hType, hSource, hHead, hCases, hDefault, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileStmtFuel?_switch
              hCompile
          have hPop :
              TypedCfg.Instr.type? .pop valueShape =
                some { valueShape with slots := valueShape.slots.tail } := by
            rcases valueShape with ⟨slots, tail⟩
            cases slots with
            | nil => simp at hHead
            | cons slot rest => simp [TypedCfg.Instr.type?]
          have hValueSource :
              1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape :=
            TypedCfgCompilerFacts.Shape.requireSourceWords?_eq_some_iff.mp hSource
          have hCaseBlocks : BlocksInProgram caseResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hDefaultBlocks : BlocksInProgram defaultResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hDefaultShape :
              LabelShape cfg (LabelSupply.label supply 1) valueShape :=
            LabelShape.of_hasEntry
              (TypedCfgCompilerFacts.Switch.default_hasEntry hPop hDefault)
              hDefaultBlocks
          have hCaseCalls : TypedCfgPreservation.CallsInProgram caseResult calls :=
            fun s hs => hCalls s (List.mem_append.mpr (Or.inl hs))
          have hDefaultCalls :
              TypedCfgPreservation.CallsInProgram defaultResult calls :=
            fun s hs => hCalls s (List.mem_append.mpr (Or.inr hs))
          have hCaseGen :=
            genShapeReg_of_compileCasesFuel? hHead hPop hCases hCaseBlocks
              (fun out hout => by
                rw [TypedCfgCompilerFacts.Switch.fallthrough_of_compileCasesFuel?
                  hHead hPop hCases] at hout
                obtain rfl := Option.some.inj hout
                exact hRegular _ rfl)
              hCtx hProcs hProcsEq hCaseCalls hValueSource hDefaultShape
          have hDefaultGen :=
            genShapeReg_of_compileDefaultFuel? hPop hDefault hDefaultBlocks
              (fun out hout => by
                rw [TypedCfgCompilerFacts.Switch.fallthrough_of_compileDefaultFuel?
                  hPop hDefault] at hout
                obtain rfl := Option.some.inj hout
                exact hRegular _ rfl)
              hCtx hProcs hProcsEq hDefaultCalls hValueSource
          intro block hMem
          simp only [List.mem_cons, List.mem_append] at hMem
          rcases hMem with (rfl | hCaseMem) | hDefaultMem
          · refine
              BlockGenShapeReg.codeHead
                (InteractionBlockGenShape.codeFact_of_switchHead
                  (compilerFuel := 0) (ctx := ctx) (supply := supply)
                  (firstTest :=
                    TypedCfgCompilerFacts.Switch.casesEntryLabel supply 0 cases)
                  hType) ?_ ?_
            · intro b hb
              simp only [List.mem_singleton] at hb
              subst b
              refine hBlocks _ ?_
              simp
            · intro out hout
              have hval : out = valueShape := (Option.some.inj hout).symm
              subst hval
              exact
                switchHead_regular_labelShape hHead hPop hCases hDefault
                  hCaseBlocks hDefaultBlocks
          · exact hCaseGen block hCaseMem
          · exact hDefaultGen block hDefaultMem
      | for_ init cond post body =>
          obtain
              ⟨initResult, loopInput, condOutput, _condition,
                bodyResult, postResult, hInit, hInitFallthrough,
                hType, hSource, _hHead, hBody, hBodyRequire,
                hPost, hPostRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Loop.components_of_compileStmtFuel?_for hCompile
          have hInitBlocks : BlocksInProgram initResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hBodyBlocks : BlocksInProgram bodyResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hPostBlocks : BlocksInProgram postResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hCondShape :
              LabelShape cfg (LabelSupply.label supply 0) loopInput :=
            ⟨{ label := LabelSupply.label supply 0
               input := loopInput
               body := TypedCfgCompiler.Code.toCfg cond
               output := condOutput
               term := .jumpi (LabelSupply.label supply 1) regular },
             hBlocks _
               (by simp only [List.mem_append, List.mem_singleton,
                 List.mem_cons]; tauto),
             rfl⟩
          have hCtxCleared :
              CtxExitsShaped cfg
                { ctx with
                  breakLabel? := none
                  breakShape? := none
                  continueLabel? := none
                  continueShape? := none } :=
            ⟨fun _ _ h _ => by simp at h,
             fun _ _ h _ => by simp at h, hCtx.leave⟩
          have hCtxBody :
              CtxExitsShaped cfg
                { ctx with
                  breakLabel? := some regular
                  breakShape? :=
                    some { condOutput with slots := condOutput.slots.tail }
                  continueLabel? := some (LabelSupply.label supply 2)
                  continueShape? :=
                    some { condOutput with slots := condOutput.slots.tail } } :=
            ⟨fun lbl shp hl hs => by
                obtain rfl := Option.some.inj hl
                obtain rfl := Option.some.inj hs
                exact hRegular _ rfl,
             fun lbl shp hl hs => by
                obtain rfl := Option.some.inj hl
                obtain rfl := Option.some.inj hs
                exact LabelShape.of_compileBlockFuel? hPost hPostBlocks,
             hCtx.leave⟩
          have hInitCalls : TypedCfgPreservation.CallsInProgram initResult calls :=
            fun s hs =>
              hCalls s (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hs))))
          have hBodyCalls : TypedCfgPreservation.CallsInProgram bodyResult calls :=
            fun s hs =>
              hCalls s (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hs))))
          have hPostCalls : TypedCfgPreservation.CallsInProgram postResult calls :=
            fun s hs => hCalls s (List.mem_append.mpr (Or.inr hs))
          have hInitGen :=
            genShapeReg_of_compileBlockFuel? hInit hInitBlocks
              (thread_of_target_fallthrough hCondShape hInitFallthrough)
              hCtxCleared (ProcsShaped.of_procs_eq (ctx := ctx) rfl hProcs)
              hProcsEq hInitCalls
          have hBodyGen :=
            genShapeReg_of_compileBlockFuel? hBody hBodyBlocks
              (thread_of_target_requireFallthrough
                (LabelShape.of_compileBlockFuel? hPost hPostBlocks) hBodyRequire)
              hCtxBody (ProcsShaped.of_procs_eq (ctx := ctx) rfl hProcs)
              hProcsEq hBodyCalls
          have hPostGen :=
            genShapeReg_of_compileBlockFuel? hPost hPostBlocks
              (thread_of_target_requireFallthrough hCondShape hPostRequire)
              hCtxCleared (ProcsShaped.of_procs_eq (ctx := ctx) rfl hProcs)
              hProcsEq hPostCalls
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
            exact BlockGenShapeReg.forCond hType hSource hFind (hRegular _ rfl)
              (LabelShape.of_compileBlockFuel? hBody hBodyBlocks)
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
                    exact
                      BlockGenShapeReg.nilJoin hFind
                        (hCtx.brk _ _ hLabel hShape)
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
                    exact
                      BlockGenShapeReg.nilJoin hFind
                        (hCtx.cont _ _ hLabel hShape)
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
                    exact
                      BlockGenShapeReg.nilJoin hFind
                        (hCtx.leave _ _ hLabel hShape)
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
          obtain ⟨hEntryShape, hProcWF⟩ := hProcs.get hLookup
          exact
            BlockGenShapeReg.callHead hProcsEq hLookup hCompile hBlocks hCalls
              hEntryShape hProcWF hRegular
      | terminal kind =>
          obtain ⟨_hSource, rfl⟩ :=
            TypedCfgCompilerFacts.Stmt.components_of_compileStmtFuel?_terminal
              hCompile
          intro block hMem
          have hFind := hBlocks block hMem
          simp only [List.mem_singleton] at hMem
          subst block
          exact BlockGenShapeReg.terminalHalt hFind

theorem genShapeReg_of_compileCasesFuel?
    {fuel : Nat} {cases : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hHead : valueShape.slots.head? = some slot)
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? fuel cases ctx
          base supply idx valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRegular : HRegular result cfg regular)
    (hCtx : CtxExitsShaped cfg ctx)
    (hProcs : ProcsShaped cfg ctx)
    (hProcsEq : ctx.procs = sourceProgram.procs)
    (hCalls : TypedCfgPreservation.CallsInProgram result calls)
    (hValueSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape)
    (hDefaultShape :
      LabelShape cfg (LabelSupply.label base 1) valueShape) :
    GenShapeResultReg result cfg sourceProgram calls := by
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
              ⟨bodyResult, tail, hBodyCompile, hBodyRequire,
                hTailCompile, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileCasesFuel?_cons
              hHead hPop hCompile
          have hBodyBlocks : BlocksInProgram bodyResult cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hTailBlocks : BlocksInProgram tail cfg := by
            intro b hb
            exact hBlocks b
              (by simp only [List.mem_cons, List.mem_append]; tauto)
          have hBodyCalls : TypedCfgPreservation.CallsInProgram bodyResult calls :=
            fun s hs => hCalls s (List.mem_append.mpr (Or.inl hs))
          have hTailCalls : TypedCfgPreservation.CallsInProgram tail calls :=
            fun s hs => hCalls s (List.mem_append.mpr (Or.inr hs))
          have hBodyGen :=
            genShapeReg_of_compileBlockFuel? hBodyCompile hBodyBlocks
              (thread_of_target_requireFallthrough (hRegular _ rfl) hBodyRequire)
              hCtx hProcs hProcsEq hBodyCalls
          have hTailGen :=
            genShapeReg_of_compileCasesFuel? hHead hPop hTailCompile hTailBlocks
              (fun out hout => by
                rw [TypedCfgCompilerFacts.Switch.fallthrough_of_compileCasesFuel?
                  hHead hPop hTailCompile] at hout
                obtain rfl := Option.some.inj hout
                exact hRegular _ rfl)
              hCtx hProcs hProcsEq hTailCalls hValueSource hDefaultShape
          intro block hMem
          simp only [List.mem_cons, List.mem_append] at hMem
          rcases hMem with (rfl | rfl | hBodyMem) | hTailMem
          · -- the switch test block
            have hNextShape :
                LabelShape cfg
                  (TypedCfgCompilerFacts.Switch.nextTestLabel base idx rest)
                  valueShape := by
              cases rest with
              | nil => exact hDefaultShape
              | cons headNext restNext =>
                  exact LabelShape.of_hasEntry
                    (TypedCfgCompilerFacts.Switch.cases_cons_test_hasEntry
                      hHead hPop hTailCompile) hTailBlocks
            exact BlockGenShapeReg.switchTest hHead hBlocks (by simp)
              (InteractionHInvObligations.switchTest_popExists hValueSource)
              (LabelShape.of_hasEntry
                (TypedCfgCompilerFacts.Switch.cases_cons_case_hasEntry
                  hHead hPop hCompile) hBlocks)
              hNextShape
          · -- the case-entry pop block
            refine BlockGenShapeReg.caseEntryPop hPop hBlocks (by simp)
              (LabelShape.of_compileBlockFuel? hBodyCompile hBodyBlocks) ?_
            exact InteractionHInvObligations.caseEntryPop_popTransport hValueSource hPop
          · exact hBodyGen block hBodyMem
          · exact hTailGen block hTailMem

theorem genShapeReg_of_compileDefaultFuel?
    {fuel : Nat} {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {sourceProgram : Structured.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hPop : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? fuel defaultBody ctx
          supply entry valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRegular : HRegular result cfg regular)
    (hCtx : CtxExitsShaped cfg ctx)
    (hProcs : ProcsShaped cfg ctx)
    (hProcsEq : ctx.procs = sourceProgram.procs)
    (hCalls : TypedCfgPreservation.CallsInProgram result calls)
    (hValueSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength valueShape) :
    GenShapeResultReg result cfg sourceProgram calls := by
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
          refine BlockGenShapeReg.caseEntryPop hPop hBlocks (by simp)
            (hRegular _ rfl) ?_
          exact InteractionHInvObligations.caseEntryPop_popTransport hValueSource hPop
      | some body =>
          obtain ⟨bodyResult, hBodyCompile, hBodyRequire, rfl⟩ :=
            TypedCfgCompilerFacts.Switch.components_of_compileDefaultFuel?_some
              hPop hCompile
          have hBodyBlocks : BlocksInProgram bodyResult cfg := by
            intro b hb
            exact hBlocks b (List.mem_cons_of_mem _ hb)
          have hBodyGen :=
            genShapeReg_of_compileBlockFuel? hBodyCompile hBodyBlocks
              (thread_of_target_requireFallthrough (hRegular _ rfl) hBodyRequire)
              hCtx hProcs hProcsEq hCalls
          intro block hMem
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hBodyMem
          · refine BlockGenShapeReg.caseEntryPop hPop hBlocks (by simp)
              (LabelShape.of_compileBlockFuel? hBodyCompile hBodyBlocks) ?_
            exact InteractionHInvObligations.caseEntryPop_popTransport hValueSource hPop
          · exact hBodyGen block hBodyMem

end

end InteractionBlockGenShapeRegular
end Structured
end EvmCompiler
