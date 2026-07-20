import EvmCompiler.Structured.TypedCfgPreservation.GeneratedBoundary

/-!
# Successor `LabelShape` transport — the WellTyped edge-extraction half

Session 37 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-36 frontier item 2).

The route-B `hInv` suppliers (`InteractionRealizedWitnessSuccessor.lean`) each consume
`hLabelShape : LabelShape cfg next restShape` for the *target* block `next` the current
block jumps to.  `LabelShape` (`GeneratedBoundary.lean:11`) is
`∃ block, cfg.findBlock? next = some block ∧ block.input = restShape` — a STRICT input
equality, which `realizedWitness_of_stateRel` (`InteractionBoundedOwnerRealized.lean:334`)
needs to rewrite the child `SourceFrameFits` onto the ambient block's declared input.

Two kinds of successor arise at each classified block:

* **Internal successors** — blocks that live in the *same* construct's compile `result`
  (e.g. an `if`'s body-entry `trueLabel`).  Their exact `LabelShape` is already available
  from the disjunct's own compile fact via `LabelShape.of_compileBlockFuel?` /
  `of_hasEntry` restricted to the sub-result (the forward proofs use exactly this,
  cf. `InteractionBranchPreservation.lean:543`).

* **The external `regular` successor** — the block the construct's fallthrough jumps to,
  which is NOT in the construct's own result.  Its exact `LabelShape` is a
  *generation-threaded* fact (the block declared at `regular` was generated with input =
  this construct's fallthrough output); the forward preservation proofs never needed it
  because they STOP at `regular` (recursive boundary), whereas the whole-program route-B
  invariant continues into it.  This is the genuine sticking point of sessions 26–35.

This module banks the **WellTyped edge-extraction** building block, which every
transport route needs regardless of how the exact shape is finally pinned: from the
ambient `cfg.WellTyped` (all blocks well-typed) alone, a block's `.jump`/`.jumpi`
terminator target is guaranteed to be a block *present in `cfg`* whose input is
`Shape.compatible` with the source block's output.  This supplies the **existence** of
the target block (the `∃ block, findBlock? … = some block` half of `LabelShape`) plus the
`compatible` relation; the remaining `compatible ⟶ exact` step is the generation-threaded
residual documented in the progress note.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation
namespace LabelShape

/--
**Ambient block extraction for a well-typed block.**  Any block that `cfg.findBlock?`
returns is a member of `cfg.blocks` and therefore well-typed under `cfg.WellTyped`. -/
theorem block_wellTyped_of_findBlock?
    {cfg : TypedCfg.Program} {label : Assembly.Label} {block : TypedCfg.Block}
    (hWT : cfg.WellTyped)
    (hFind : cfg.findBlock? label = some block) :
    block.WellTyped cfg := by
  have hMem : block ∈ cfg.blocks := by
    unfold TypedCfg.Program.findBlock? at hFind
    exact List.mem_of_find?_eq_some hFind
  exact List.forall_iff_forall_mem.mp hWT.2.1 block hMem

/--
**WellTyped `.jump` edge extraction.**  A block found in a well-typed `cfg` whose
terminator is `.jump target` guarantees the target names a block *present in `cfg`* whose
input is `Shape.compatible` with the source block's output.  Delivers the *existence* half
of `LabelShape cfg target …` (a concrete `LabelShape cfg target targetShape`) plus the
`compatible` relation to the source output. -/
theorem edge_jump_of_wellTyped
    {cfg : TypedCfg.Program} {label target : Assembly.Label}
    {block : TypedCfg.Block}
    (hWT : cfg.WellTyped)
    (hFind : cfg.findBlock? label = some block)
    (hTerm : block.term = .jump target) :
    ∃ targetShape,
      LabelShape cfg target targetShape ∧
        block.output.compatible targetShape = true := by
  have hBlockWT := block_wellTyped_of_findBlock? hWT hFind
  have hType := hBlockWT.2
  rw [hTerm] at hType
  simp only [TypedCfg.Terminator.type?, TypedCfg.Terminator.typeWith?] at hType
  cases hLS : cfg.labelShape? target with
  | none => rw [hLS] at hType; simp at hType
  | some targetShape =>
      rw [hLS] at hType
      simp only [Option.bind_eq_bind, Option.bind_some] at hType
      by_cases hCompat : block.output.compatible targetShape = true
      · obtain ⟨targetBlock, hTargetFind, hTargetInput⟩ :=
          Option.map_eq_some_iff.mp hLS
        exact ⟨targetShape, ⟨targetBlock, hTargetFind, hTargetInput⟩, hCompat⟩
      · simp only [hCompat, if_false] at hType
        exact absurd hType (by simp)

/-!
## Option-B boundary seeds — the external `regular` `LabelShape` in threaded form

The head-construct successor suppliers (`realizedWitness_of_if_compile` /
`realizedWitness_of_code_compile`, `InteractionConstructCoupling.lean:74` /
`InteractionCodeConstructCoupling.lean:205`) each consume the external `regular`
successor's `LabelShape` in the **threaded form**

    ∀ out, result.fallthrough? = some out → LabelShape cfg regular out

(the branch coupling pins `restShape = result.fallthrough?`, so the only shape ever
demanded at `regular`/`next` is the construct's fallthrough output).  Option B threads
exactly this predicate through the capstone mutual, seeded at the two program
boundaries.  These two lemmas ARE the seeds: at the main body the external `regular`
is `ProcLabel.programEnd` and at a proc body it is `ProcLabel.exit proc.name`, and the
already-banked `LabelShape.programEnd` / `LabelShape.procExit` pin the boundary block's
input — which, under the fallthrough hypothesis, is exactly `out`.
-/

/--
**Main-body boundary seed (option B).**  The external `regular` successor of the main
body is `ProcLabel.programEnd`, whose block input is `main.fallthrough?.getD caller`
(`LabelShape.programEnd`).  Under `main.fallthrough? = some out` that input is exactly
`out`, so `LabelShape cfg ProcLabel.programEnd out` — the threaded external-successor
seed the main composite feeds the capstone. -/
theorem main_regular_labelShape
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated : Program.GeneratedContext program entryShapes cfg)
    {out : TypedCfg.Shape}
    (hFallthrough : generated.main.fallthrough? = some out) :
    LabelShape cfg ProcLabel.programEnd out := by
  have h := programEnd generated
  rw [hFallthrough] at h
  simpa using h

/--
**Proc-body boundary seed (option B).**  The external `regular` successor of a proc
body is `ProcLabel.exit proc.name`, whose block input is `Shape.procExit proc`
(`LabelShape.procExit`).  The proc fragment's `requireFallthrough? (procExit) = some ()`
forces any actual body fallthrough output to be exactly `Shape.procExit proc`, so under
`bodyResult.fallthrough? = some out` we get `out = Shape.procExit proc` and hence
`LabelShape cfg (ProcLabel.exit proc.name) out` — the threaded external-successor seed
the proc composite feeds the capstone. -/
theorem proc_regular_labelShape
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated : Program.GeneratedContext program entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? name program.procs = some proc)
    {bodyResult : TypedCfgCompiler.Result} {out : TypedCfg.Shape}
    (hRequire :
      bodyResult.requireFallthrough? (TypedCfgCompiler.Shape.procExit proc) =
        some ())
    (hFallthrough : bodyResult.fallthrough? = some out) :
    LabelShape cfg (ProcLabel.exit proc.name) out := by
  have hOut : out = TypedCfgCompiler.Shape.procExit proc := by
    rcases
        TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp hRequire with
      hNone | hSome
    · rw [hFallthrough] at hNone; exact absurd hNone (by simp)
    · exact Option.some.inj (hFallthrough.symm.trans hSome)
  subst hOut
  exact procExit generated hLookup

/-!
## Option-B threading combinators — the per-recursive-call regular-thread transporters

The capstone mutual (`InteractionBlockGenShape.lean`) threads
`BlocksInProgram result cfg` down the generation recursion.  Option B threads a
second hypothesis alongside it — the **regular-thread**

    HRegular result cfg regular := ∀ out, result.fallthrough? = some out →
      LabelShape cfg regular out

(exactly the external-successor form the head-construct suppliers consume).  These
two combinators are what the strengthened mutual applies at each recursive descent to
produce the sub-call's regular-thread from the enclosing one:

* `regularThread_of_requireFallthrough` — SAME-`regular` inheritance: a sub-block
  compiled with the *same* `regular` that `requireFallthrough?`s to the enclosing
  fallthrough shape inherits the regular-thread.  Used by the `if`-body, the `switch`
  case bodies / default body, and the loop-body/post (all compiled with a shared
  continuation shape).

* `regularThread_tail_of_cons` — SEQUENTIAL threading: in a `stmt :: rest`
  decomposition the head is compiled with `regular := restLabel supply` (the tail's
  own entry), and the tail's entry block — present in the same enclosing result — has
  input exactly the head's fallthrough shape.  This is the "sequential continuation"
  core of option B, discharging the head's regular-thread internally with NO boundary
  appeal.

Together with the boundary seeds (`main_regular_labelShape` / `proc_regular_labelShape`)
these close every regular-thread obligation the strengthened capstone raises.
-/

/-- **Same-`regular` regular-thread inheritance.**  Given the enclosing regular-thread
`hRegular` (whose result falls through to `expected`) and a sub-result compiled with
the *same* `regular` whose `requireFallthrough?` pins it to that same `expected`, the
sub-result inherits the regular-thread: any actual sub-fallthrough output is `expected`,
whose `LabelShape cfg regular …` is the enclosing thread applied at `expected`. -/
theorem regularThread_of_requireFallthrough
    {cfg : TypedCfg.Program} {regular : Assembly.Label}
    {result subResult : TypedCfgCompiler.Result} {expected : TypedCfg.Shape}
    (hRegular :
      ∀ out, result.fallthrough? = some out → LabelShape cfg regular out)
    (hResultFall : result.fallthrough? = some expected)
    (hSubRequire : subResult.requireFallthrough? expected = some ()) :
    ∀ out, subResult.fallthrough? = some out → LabelShape cfg regular out := by
  intro out hOut
  have hExpected : out = expected := by
    rcases
        TypedCfgCompilerFacts.Result.requireFallthrough?_eq_some_iff.mp
          hSubRequire with hNone | hSome
    · rw [hOut] at hNone; exact absurd hNone (by simp)
    · exact Option.some.inj (hOut.symm.trans hSome)
  subst hExpected
  exact hRegular out hResultFall

/-- **Sequential (`stmt :: rest`) regular-thread for the head.**  The head statement of
a nonempty list is compiled with `regular := restLabel supply` — the entry label of the
compiled tail — and falls through to `tailInput`, exactly the tail entry block's input.
Since the tail result is in-program, its entry block gives `LabelShape cfg
(restLabel supply) tailInput`, discharging the head's regular-thread with no boundary
appeal (the "sequential continuation" core of option B). -/
theorem regularThread_tail_of_cons
    {cfg : TypedCfg.Program}
    {compilerFuel : Nat} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply nextSupply : LabelSupply}
    {regular : Assembly.Label} {tailInput : TypedCfg.Shape}
    {headResult tailResult : TypedCfgCompiler.Result}
    (hHeadFall : headResult.fallthrough? = some tailInput)
    (hTailCompile :
      TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
          nextSupply (TypedCfgCompiler.restLabel supply) tailInput regular =
        some tailResult)
    (hTailBlocks : BlocksInProgram tailResult cfg) :
    ∀ out, headResult.fallthrough? = some out →
      LabelShape cfg (TypedCfgCompiler.restLabel supply) out := by
  intro out hOut
  have hEq : out = tailInput :=
    Option.some.inj (hOut.symm.trans hHeadFall)
  subst hEq
  exact of_compileStmtListFuel? hTailCompile hTailBlocks

end LabelShape
end TypedCfgPreservation
end Structured
end EvmCompiler
