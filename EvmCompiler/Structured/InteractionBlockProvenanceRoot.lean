import EvmCompiler.Structured.InteractionBlockProvenance

/-!
# Static block-provenance ROOTS (gate 2 of the route-2 `hInv`, static route)

Session 31 / route-B framing 2 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-31).

`block_category` (`InteractionBlockProvenance.lean:79`) splits a reached entry's
block into the four generated categories (main body / proc body / dispatch /
programEnd).  The `hInv` invariant then needs, for the three compiled-construct
arms, the *compile fact* of the source construct that generated the block at the
reached entry — the input to the per-construct coupling suppliers
(`realizedWitness_of_{if,call,code}_compile`, `realizedWitness_of_dispatch_jump`).

The **static-provenance route** (session-31 decision, evidence in the progress note)
recovers that compile fact by an induction over the CFG *generation* (the
`compileBlock?`/`compileStmtListFuel?`/`compileStmtFuel?` recursion), NOT over the
run: every block in the cfg is generated from some source construct, so a static
map «cfg block ↦ its compile fact» is decoupled from the run and reusable at every
reached entry.

This module lands the **ROOT** of that induction for the main-body category: it
turns `block_category`'s `block ∈ context.main.blocks` arm into the top-level
`compileStmtListFuel?` fact over `source.body.stmts` (with the block still a member
of that result) — the exact entry point the eventual statement-list provenance
drill inducts on.  The `mainCompile` field of `GeneratedContext` pins
`compileBlock? source.body … = some context.main`, and `compileBlock?` unfolds to a
`compileStmtListFuel?` call over the block's statements.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation
namespace Program
namespace GeneratedContext

/--
**Main-body provenance root.**  Every main-category block (`block ∈
context.main.blocks`, the first arm of `block_category`) is a member of the result
of compiling the source program's top-level body statement list.  This exposes the
`compileStmtListFuel?` fact — the entry point of the static statement-list
provenance drill — from the opaque `context.main` result.

Proof: `context.mainCompile` pins `compileBlock? source.body … = some context.main`;
`compileBlock?` is `compileBlockFuel? (blockFuel source.body + 1) …`, which unfolds
to `compileStmtListFuel? (blockFuel source.body) source.body.stmts …`. -/
theorem main_stmtList_provenance
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : GeneratedContext source entryShapes cfg)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.main.blocks) :
    TypedCfgCompiler.compileStmtListFuel?
        (TypedCfgCompiler.blockFuel source.body) source.body.stmts
        { procs := source.procs } 0 TypedCfgCompiler.entryLabel
        TypedCfg.Shape.caller ProcLabel.programEnd = some context.main ∧
      block ∈ context.main.blocks := by
  refine ⟨?_, hMem⟩
  have h := context.mainCompile
  unfold TypedCfgCompiler.compileBlock? at h
  simpa [TypedCfgCompiler.compileBlockFuel?] using h

end GeneratedContext
end Program
end TypedCfgPreservation
end Structured
end EvmCompiler
