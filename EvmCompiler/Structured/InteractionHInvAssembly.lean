import EvmCompiler.Structured.InteractionBlockGenShape

/-!
# `hInv` assembly ingredients (route-2 endgame glue)

Session 36 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-35).

The route-B master lever `AllEntriesRealized.of_openStep_invariant`
(`TypedCfg/InteractionEntryRealized.lean:271`) reduces the peephole endgame to a
single global `openStep`-jump invariant `hInv`.  §Session-35 landed the block-generation
classification capstone (`InteractionBlockGenShape.lean`: `genShape_of_compile*`) at the
`compileBlockFuel?` level.  This module banks the two remaining *static/localized*
ingredients the eventual `hInv` case split consumes but which the capstone itself does
not expose:

* **`genShape_of_compileBlock?`** — the public `compileBlock?`-level wrapper over the
  fuel-indexed capstone `genShape_of_compileBlockFuel?`, exactly analogous to
  `activeResult_of_compileBlock?` (`TypedCfgCompilerActive.lean:514`).  This is the form
  the provenance roots (`main_stmtList_provenance` / `procBlocks_provenance`) hand to the
  drill, which the `hInv` case split then `cases`-splits into the nine `BlockGenShape`
  disjuncts.

* **`dispatch_popReturn?_of_stateRel`** — the localized `StateRel`⟶frame-fact derivation
  for the DISPATCH arm (`block_category`'s third arm, outside `BlockGenShape`).  The
  return-dispatch successor supplier `realizedWitness_of_dispatch_jump`
  (`InteractionRealizedWitnessSuccessor.lean:149`) consumes `hPop :
  bodyState.popReturn? = some (frame, returned)`.  When the exit-block `StateRel` carries
  the return token at the head of its token list (`site.token :: tokens`), the source
  activation stack is non-empty and `popReturn?` succeeds *deterministically* — the popped
  frame and residual state are pinned by `StateRel.returns_cons_of_tokens_cons`
  (`TypedCfgPreservation/Core.lean:74`).  This discharges `hPop` from the `realizedWitness`
  `StateRel` alone, with **no** source run needed.  (The remaining two dispatch
  frame-facts `hAttach`/`hRetc` pin the popped frame's `retc` to `proc.retc`; that is a
  *procedure-identity* fact — genuinely not `StateRel`-derivable — supplied by the site
  provenance the `hInv` dispatch arm recovers alongside `hLookup`/`hSiteProc`/`hSiteMem`.)

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured

/--
**Public `compileBlock?`-level block-generation classification.**

The fuel-indexed capstone `genShape_of_compileBlockFuel?`
(`InteractionBlockGenShape.lean:251`) proves every block a successful compilation emits
is classified by `BlockGenShape`.  The public block compiler `compileBlock?` inherits it
directly, exactly as `activeResult_of_compileBlock?`
(`TypedCfgCompilerActive.lean:514`) inherits `ActiveResult`.

This is the form the eventual `hInv` case split consumes: the provenance roots recover a
`compileBlock? … = some result` fact with `block ∈ result.blocks`, and this wrapper hands
back `BlockGenShape cfg block` for the per-disjunct supplier dispatch.
-/
theorem genShape_of_compileBlock?
    {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileBlock? block ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    InteractionBlockGenShape.GenShapeResult result cfg := by
  have hFuel :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel block + 1) block ctx
          supply entry input regular = some result := by
    simpa [TypedCfgCompiler.compileBlock?] using hCompile
  exact InteractionBlockGenShape.genShape_of_compileBlockFuel? hFuel hBlocks

/--
**Localized `StateRel`⟶`popReturn?` derivation for the dispatch arm.**

At a procedure-exit block the return-dispatch successor supplier
`realizedWitness_of_dispatch_jump` needs `hPop : bodyState.popReturn? = some (frame,
returned)`.  When the exit block's `realizedWitness` `StateRel` carries the return token
at the head of its token list (`token :: tokens`), the source activation stack
`bodyState.returns` is non-empty (`StateRel.returns_cons_of_tokens_cons`), so `popReturn?`
succeeds and the popped frame / residual state are the deterministic head-split.

This discharges the `hPop` frame-fact from the `realizedWitness` `StateRel` alone — no
source run required.  (`hAttach`/`hRetc` remain supplied by the site provenance.)
-/
theorem dispatch_popReturn?_of_stateRel
    {bodyState : RunState} {token : Word} {tokens : List Word} {target : EVMState}
    (hRel :
      TypedCfgPreservation.StateRel bodyState (token :: tokens) target) :
    ∃ frame returns,
      bodyState.returns = frame :: returns ∧
        bodyState.popReturn? =
          some (frame, { bodyState with returns := returns }) := by
  obtain ⟨frame, returns, hReturns⟩ :=
    TypedCfgPreservation.StateRel.returns_cons_of_tokens_cons hRel
  refine ⟨frame, returns, hReturns, ?_⟩
  simp only [RunState.popReturn?, hReturns]

end Structured
end EvmCompiler
