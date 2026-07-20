import EvmCompiler.Structured.InteractionBlockGenShapeRegular
import EvmCompiler.Structured.InteractionBlockProvenanceRoot
import EvmCompiler.Structured.InteractionProcBlockProvenance

/-!
# Strengthened `hInv` classification composites (route-2 endgame glue, option-B thread)

Session 39 (see `TypedCfg/PEEPHOLE_PROGRESS.md` §Session-38 recipe, final paragraph).

The strengthened capstone `genShapeReg_of_compile*`
(`InteractionBlockGenShapeRegular.lean`) proves every compiled block is
`BlockGenShapeReg`-classified — the `BlockGenShape` classification enriched with the exact
`LabelShape` of each block's external `regular` successor — GIVEN the threaded predicates
`HRegular result cfg regular` and `CtxExitsShaped cfg ctx`.  This module discharges those
threaded predicates at the two program boundaries and packages the result as the
`compileBlock?`-level composites the eventual `hInv` case split consumes, exactly mirroring
`genShape_of_compileBlock?` / `main_blockGenShape` (`InteractionHInvAssembly.lean`) but
concluding `BlockGenShapeReg`.

* `genShapeReg_of_compileBlock?` — the public `compileBlock?`-level wrapper over the
  fuel-indexed strengthened capstone.

* `main_blockGenShapeReg` — the MAIN-body composite.  The main body is compiled with
  external `regular = ProcLabel.programEnd` and the empty (all-`none`) break/continue/leave
  context, so the boundary seed `LabelShape.main_regular_labelShape` discharges `HRegular`
  and `CtxExitsShaped` is vacuous.

Additive; no existing statement touched.  `peepholeBody`/public spine UNTOUCHED.
-/

namespace EvmCompiler
namespace Structured
namespace InteractionBlockGenShapeRegular

open TypedCfgPreservation (LabelShape BlocksInProgram)

/--
**Public `compileBlock?`-level strengthened classification.**  The fuel-indexed capstone
`genShapeReg_of_compileBlockFuel?` inherited by `compileBlock?`, exactly as
`genShape_of_compileBlock?` (`InteractionHInvAssembly.lean:58`) inherits the base
classification. -/
theorem genShapeReg_of_compileBlock?
    {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileBlock? block ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRegular : HRegular result cfg regular)
    (hCtx : CtxExitsShaped cfg ctx) :
    GenShapeResultReg result cfg := by
  have hFuel :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel block + 1) block ctx
          supply entry input regular = some result := by
    simpa [TypedCfgCompiler.compileBlock?] using hCompile
  exact genShapeReg_of_compileBlockFuel? hFuel hBlocks hRegular hCtx

/--
**Main-body arm: block ⟶ `BlockGenShapeReg` composite.**  The strengthened sibling of
`main_blockGenShape`.  Combines the main-body provenance root with the strengthened
statement-list classifier; the external-`regular` thread is the boundary seed
`main_regular_labelShape` (external `regular = ProcLabel.programEnd`) and the ctx-exit
bundle is vacuous (the main context has all break/continue/leave labels `none`). -/
theorem main_blockGenShapeReg
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.main.blocks) :
    BlockGenShapeReg cfg block := by
  obtain ⟨hCompile, hMem'⟩ :=
    TypedCfgPreservation.Program.GeneratedContext.main_stmtList_provenance
      context hMem
  refine
    genShapeReg_of_compileStmtListFuel? hCompile context.mainBlocks ?_ ?_ block hMem'
  · exact fun out hout =>
      TypedCfgPreservation.LabelShape.main_regular_labelShape context hout
  · exact
      ⟨fun _ _ h _ => by simp at h,
       fun _ _ h _ => by simp at h,
       fun _ _ h _ => by simp at h⟩

end InteractionBlockGenShapeRegular
end Structured
end EvmCompiler
