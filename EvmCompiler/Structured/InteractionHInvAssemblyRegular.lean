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
    {sourceProgram : Structured.Program}
    {calls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileBlock? block ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRegular : HRegular result cfg regular)
    (hCtx : CtxExitsShaped cfg ctx)
    (hProcs : ProcsShaped cfg ctx)
    (hProcsEq : ctx.procs = sourceProgram.procs)
    (hCalls : TypedCfgPreservation.CallsInProgram result calls) :
    GenShapeResultReg result cfg sourceProgram calls := by
  have hFuel :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel block + 1) block ctx
          supply entry input regular = some result := by
    simpa [TypedCfgCompiler.compileBlock?] using hCompile
  exact genShapeReg_of_compileBlockFuel? hFuel hBlocks hRegular hCtx hProcs
    hProcsEq hCalls

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
    (hSourceWF : source.WF)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.main.blocks) :
    BlockGenShapeReg cfg source context.calls block := by
  obtain ⟨hCompile, hMem'⟩ :=
    TypedCfgPreservation.Program.GeneratedContext.main_stmtList_provenance
      context hMem
  refine
    genShapeReg_of_compileStmtListFuel? hCompile context.mainBlocks ?_ ?_ ?_ rfl
      context.mainCalls block hMem'
  · exact fun out hout =>
      TypedCfgPreservation.LabelShape.main_regular_labelShape context hout
  · exact
      ⟨fun _ _ h _ => by simp at h,
       fun _ _ h _ => by simp at h,
       fun _ _ h _ => by simp at h⟩
  · exact ProcsShaped.seed context hSourceWF rfl

/--
**Proc-body arm: block ⟶ `BlockGenShapeReg` composite.**  The strengthened sibling of
`proc_blockGenShape`.  From the proc-category provenance root
`procBlocks_provenance_inProgram_fallthrough` (which additionally exposes the proc-exit
`requireFallthrough?` fact and, in the adapter disjunct, the body compile entry), the
external-`regular` thread is the boundary seed `proc_regular_labelShape` (external
`regular = ProcLabel.exit proc.name`) and the ctx-exit bundle has vacuous break/continue
with `leave = ProcLabel.exit proc.name` discharged by `LabelShape.procExit`.  The adapter
disjunct inverts `mkBlock?` exactly as in `proc_blockGenShape` and supplies `procAdapter`'s
new `hBodyShape` (the body-entry `LabelShape`; `output = input` under the `.relabel`
retype).  `source.WF` supplies the name-uniqueness discharging `proc ∈ source.procs ⟶
lookup? proc.name = some proc`. -/
theorem proc_blockGenShapeReg
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      TypedCfgPreservation.Program.GeneratedContext source entryShapes cfg)
    (hSourceWF : source.WF)
    {block : TypedCfg.Block}
    (hMem : block ∈ context.procBlocks) :
    BlockGenShapeReg cfg source context.calls block := by
  obtain ⟨proc, bsupply, entry, input, bodyResult,
      hProcMem, hCompile, hReq, hBlocks, hBodyCalls, hDisj⟩ :=
    context.procBlocks_provenance_inProgram_fallthrough hMem
  have hLookup :
      Structured.ProcList.lookup? proc.name source.procs = some proc :=
    Structured.ProcList.lookup?_eq_some_of_mem hSourceWF.1 hProcMem rfl
  rcases hDisj with hBody | ⟨hEntry, hDepth, hAdapter⟩
  · -- body case: feed the strengthened body drill with the proc-boundary seeds.
    refine
      genShapeReg_of_compileBlock? hCompile hBlocks ?_ ?_ ?_ rfl hBodyCalls
        block hBody
    · exact fun out hout =>
        TypedCfgPreservation.LabelShape.proc_regular_labelShape
          context hLookup hReq hout
    · exact
        ⟨fun _ _ h _ => by simp at h,
         fun _ _ h _ => by simp at h,
         fun _ _ hL hS => by
           obtain rfl := Option.some.inj hL
           obtain rfl := Option.some.inj hS
           exact TypedCfgPreservation.LabelShape.procExit context hLookup⟩
    · exact ProcsShaped.seed context hSourceWF rfl
  · -- adapter case: invert `mkBlock?`, classify via `procAdapter`.
    subst hEntry
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
        have hOutInput : output = input := by
          simp only [TypedCfg.Instr.type?] at hType
          split at hType
          · exact (Option.some.inj hType).symm
          · exact absurd hType (by simp)
        subst hAdapter
        refine BlockGenShapeReg.procAdapter hType hFind ?_ ?_ ?_
        · rw [hOutInput]
          exact
            TypedCfgPreservation.LabelShape.of_compileBlock? hCompile hBlocks
        · -- SourceFrameFits transport across the (runtime-no-op) relabel:
          -- procEntry proc and input both have returnTokenDepth? = some proc.argc,
          -- so both frame-fits reduce to (n = proc.argc).
          intro n hFits
          rw [hOutInput]
          have hProcDepth :
              (TypedCfgCompiler.Shape.procEntry proc).returnTokenDepth? =
                some proc.argc :=
            TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc
          exact
            (TypedCfgCompilerFacts.Shape.sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some
                hDepth).mpr
              ((TypedCfgCompilerFacts.Shape.sourceFrameFits_iff_eq_of_returnTokenDepth?_eq_some
                  hProcDepth).mp hFits)
        · -- the adapter's input is the proc-entry shape, which owns the return token
          rw [TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc]; rfl

end InteractionBlockGenShapeRegular
end Structured
end EvmCompiler
