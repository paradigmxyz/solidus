import EvmCompiler.Structured.InteractionBlockProvenanceRoot

/-!
# The statement-list provenance DRILL (gate 2 engine, static route)

Session 32 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-31).

`InteractionBlockProvenanceRoot.lean` (session 31) turned `block_category`'s
main-body arm (`block ∈ context.main.blocks`) into the top-level
`compileStmtListFuel?` fact.  This module builds the **drill** that descends from a
`compileStmtListFuel? … = some result` fact plus `block ∈ result.blocks` down to the
*specific source construct* whose `compileStmtFuel?` emitted the block — the
per-construct compile fact the coupling suppliers
(`realizedWitness_of_{if,call,code}_compile`) consume.

The drill is pure syntactic bookkeeping over the compilation recursion: **no
semantics, no fuel-run coupling, no interaction transcript**.  It mirrors the
generation skeleton of `activeResult_of_compile*`
(`TypedCfgCompilerActive.lean`) MINUS the semantic payload — the very same
`head :: bodyResult.blocks` / `head.append tail` membership splits, but carrying a
*provenance* conclusion rather than `ActiveResult`.

## Phase 1 (this file): the one-layer membership dichotomies

For each `compileStmtFuel?` constructor and for the `compileStmtListFuel?`
nil/cons shapes, from `block ∈ result.blocks` recover *where in the emission* the
block sits: the entry-aligned head block, or a member of a named recursive
subfragment (`compileBlockFuel?` body / `compileCasesFuel?` / `compileDefaultFuel?`
result) — returning the subfragment's own compile fact so the drill can recurse.
These are the reusable substrate the assembled descent (and `block_category`'s
consumer) chains.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation
namespace BlockProvenanceDrill

open TypedCfgCompiler

/-! ### Statement-list membership dichotomies -/

/--
**Nil statement-list emission.**  Compiling the empty statement list emits exactly
one block — the join block, entry-labelled with a `.jump regular` terminator and an
empty body.  Every block in the result is that join block.
-/
theorem mem_of_compileStmtListFuel?_nil
    {compilerFuel : Nat}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtListFuel? (compilerFuel + 1) [] ctx supply entry input
          regular = some result)
    (hMem : block ∈ result.blocks) :
    block =
      { label := entry
        input := input
        body := []
        output := input
        term := .jump regular } := by
  simp only [compileStmtListFuel?, mkBlock?, TypedCfg.Block.bodyType?] at hCompile
  cases hCompile
  simpa using hMem

/--
**Cons statement-list membership dichotomy.**  A block emitted by compiling
`stmt :: rest` lands either in the head statement's emission or in the tail's — and
in each case the corresponding compile fact is exposed for the drill to recurse on.

Built directly on `components_of_compileStmtListFuel?_cons`
(`Core.lean`): the tail is present iff the head has a regular fallthrough.
-/
theorem mem_of_compileStmtListFuel?_cons
    {compilerFuel : Nat} {stmt : Structured.Stmt}
    {rest : List Structured.Stmt}
    {ctx : Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : Result} {block : TypedCfg.Block}
    (hCompile :
      compileStmtListFuel? (compilerFuel + 1) (stmt :: rest) ctx supply
          entry input regular = some result)
    (hMem : block ∈ result.blocks) :
    (∃ headResult,
      compileStmtFuel? compilerFuel stmt ctx supply entry input
          (restLabel supply) = some headResult ∧
      block ∈ headResult.blocks) ∨
    (∃ headResult tailInput tailResult,
      compileStmtFuel? compilerFuel stmt ctx supply entry input
          (restLabel supply) = some headResult ∧
      headResult.fallthrough? = some tailInput ∧
      compileStmtListFuel? compilerFuel rest ctx headResult.next
          (restLabel supply) tailInput regular = some tailResult ∧
      block ∈ tailResult.blocks) := by
  rcases Block.components_of_compileStmtListFuel?_cons hCompile with
    ⟨headResult, hHead, hNoTail | hTail⟩
  · rcases hNoTail with ⟨_hFallthrough, rfl⟩
    exact Or.inl ⟨result, hHead, hMem⟩
  · rcases hTail with ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    simp only [Result.append, List.mem_append] at hMem
    rcases hMem with hHeadMem | hTailMem
    · exact Or.inl ⟨headResult, hHead, hHeadMem⟩
    · exact
        Or.inr
          ⟨headResult, tailInput, tailResult, hHead, hFallthrough,
            hTailCompile, hTailMem⟩

end BlockProvenanceDrill
end TypedCfgPreservation
end Structured
end EvmCompiler
