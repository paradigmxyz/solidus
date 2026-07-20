import EvmCompiler.Structured.InteractionBlockGenShape
import EvmCompiler.Structured.InteractionBlockProvenanceRoot
import EvmCompiler.Structured.InteractionProcBlockProvenance

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

/--
**Dispatch arm: `dispatchBlocks` membership ⟶ owning-proc provenance.**

`block_category`'s THIRD arm hands `block ∈ dispatchBlocks source.procs (context.main.calls
++ context.procCalls)`.  `dispatchBlocks` is `source.procs.map (dispatchBlock · calls)`, so
every such block is the return-dispatch block of exactly one `proc ∈ source.procs`; its label
is `ProcLabel.exit proc.name`, its `input`/`output` the `procExit` shape, and its terminator
the `returnDispatch` over that proc's registered return sites.  This recovers the owning proc
together with the `lookup?`-witness (`source.WF` name-uniqueness) the return-dispatch successor
supplier `realizedWitness_of_dispatch_jump` consumes as `hLookup`, plus the exact block shape
(`= dispatchBlock proc context.calls`) the eventual dispatch `openStep` inversion turns on.

Additive; no existing statement touched. -/
theorem dispatchBlock_provenance
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {block : TypedCfg.Block}
    (hMem :
      block ∈
        TypedCfgCompiler.dispatchBlocks source.procs
          (context.main.calls ++ context.procCalls)) :
    ∃ proc : Structured.Proc,
      proc ∈ source.procs ∧
      Structured.ProcList.lookup? proc.name source.procs = some proc ∧
      block =
        TypedCfgCompiler.dispatchBlock proc
          (context.main.calls ++ context.procCalls) := by
  simp only [TypedCfgCompiler.dispatchBlocks, List.mem_map] at hMem
  obtain ⟨proc, hProcMem, hBlock⟩ := hMem
  exact
    ⟨proc, hProcMem,
      Structured.ProcList.lookup?_eq_some_of_mem hSourceWF.1 hProcMem rfl,
      hBlock.symm⟩

/--
**Main-body arm: block ⟶ `BlockGenShape` composite.**

Combines the main-body provenance root (`main_stmtList_provenance`) with the capstone
statement-list classifier (`genShape_of_compileStmtListFuel?`) and the main-result
in-program fact (`mainBlocks`) to conclude, from the FIRST arm of `block_category`
(`block ∈ context.main.blocks`), that the block is `BlockGenShape`-classified.

This is precisely the main-body case of the eventual `hInv` split: given the main-body
membership, hand the per-disjunct supplier dispatch a `BlockGenShape cfg block` fact.
No runtime data — purely static provenance ∘ classification.
-/
theorem main_blockGenShape
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.main.blocks) :
    InteractionBlockGenShape.BlockGenShape cfg block := by
  obtain ⟨hCompile, hMem'⟩ :=
    TypedCfgPreservation.Program.GeneratedContext.main_stmtList_provenance
      context hMem
  exact
    InteractionBlockGenShape.genShape_of_compileStmtListFuel?
      hCompile context.mainBlocks block hMem'

/--
**Proc-body arm: block ⟶ `BlockGenShape` composite.**

The proc-category sibling of `main_blockGenShape`.  From the SECOND arm of
`block_category` (`block ∈ context.procBlocks`) the strengthened provenance root
`procBlocks_provenance_inProgram` recovers, for some `proc ∈ source.procs`, the body
compile fact `compileBlock? proc.body … = some bodyResult` already promoted to
`BlocksInProgram bodyResult cfg`, together with the disjunction

* `block ∈ bodyResult.blocks` — the block is a compiled-body block; feed the body
  drill `genShape_of_compileBlock?` directly; or
* `block` IS `proc`'s entry ADAPTER (`mkBlock? (ProcLabel.entry proc.name)
  (Shape.procEntry proc) [.relabel input] (.jump (ProcLabel.body proc.name)) = some
  block`) — invert the adapter `mkBlock?` (exactly as `mkBlock?_label_input`) to
  expose the exact block shape and the `Instr.type? (.relabel input) …` fact, then
  classify it via `BlockGenShape.procAdapter`, whose `findBlock?` fact follows from
  `block ∈ cfg.blocks` (proc-blocks inclusion) + `LabelsUnique`.

Purely static provenance ∘ classification; feeds the per-disjunct supplier dispatch.
-/
theorem proc_blockGenShape
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.procBlocks) :
    InteractionBlockGenShape.BlockGenShape cfg block := by
  obtain
      ⟨proc, bsupply, entry, input, bodyResult,
        hProcMem, hCompile, hBlocks, hDisj⟩ :=
    context.procBlocks_provenance_inProgram hMem
  rcases hDisj with hBody | hAdapter
  · exact genShape_of_compileBlock? hCompile hBlocks block hBody
  · -- adapter case: invert `mkBlock?` to pin `block`, then classify via `procAdapter`.
    have hMemCfg : block ∈ cfg.blocks := by
      rw [context.cfgEq]
      simp only [List.append_assoc, List.mem_append]
      tauto
    have hFind :=
      TypedCfg.Program.findBlock?_eq_some_of_mem context.wellTyped.1 hMemCfg
    unfold TypedCfgCompiler.mkBlock? at hAdapter
    cases hBT :
        TypedCfg.Block.bodyType? [TypedCfg.Instr.relabel input]
          (TypedCfgCompiler.Shape.procEntry proc) with
    | none => simp [hBT] at hAdapter
    | some output =>
        simp [hBT] at hAdapter
        have hType :
            TypedCfg.Instr.type? (.relabel input)
              (TypedCfgCompiler.Shape.procEntry proc) = some output := by
          simpa [TypedCfg.Block.bodyType?] using hBT
        subst hAdapter
        exact InteractionBlockGenShape.BlockGenShape.procAdapter hType hFind

end Structured
end EvmCompiler
