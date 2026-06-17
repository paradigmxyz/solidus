import EvmCompiler.Structured.TypedCfgCompilerEntry

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation

/--
The unique ambient CFG block at `label` expects `shape`.
-/
def LabelShape (cfg : TypedCfg.Program)
    (label : Assembly.Label) (shape : TypedCfg.Shape) : Prop :=
  ∃ block,
    cfg.findBlock? label = some block ∧
      block.input = shape

namespace LabelShape

theorem eq
    {cfg : TypedCfg.Program} {label : Assembly.Label}
    {left right : TypedCfg.Shape}
    (hLeft : LabelShape cfg label left)
    (hRight : LabelShape cfg label right) :
    left = right := by
  rcases hLeft with ⟨leftBlock, hLeftFind, hLeftInput⟩
  rcases hRight with ⟨rightBlock, hRightFind, hRightInput⟩
  have hBlock : leftBlock = rightBlock :=
    Option.some.inj (hLeftFind.symm.trans hRightFind)
  subst rightBlock
  exact hLeftInput.symm.trans hRightInput

theorem of_hasEntry
    {cfg : TypedCfg.Program} {result : TypedCfgCompiler.Result}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    (hEntry : TypedCfgCompilerFacts.HasEntry result entry input)
    (hBlocks : BlocksInProgram result cfg) :
    LabelShape cfg entry input := by
  rcases hEntry with ⟨block, hMem, hLabel, hInput⟩
  subst entry
  exact ⟨block, hBlocks block hMem, hInput⟩

theorem of_compileBlockFuel?
    {fuel : Nat} {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? fuel block ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    LabelShape cfg entry input :=
  of_hasEntry
    (TypedCfgCompilerFacts.block_hasEntry hCompile)
    hBlocks

theorem of_compileBlock?
    {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileBlock? block ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    LabelShape cfg entry input := by
  apply of_compileBlockFuel? (hBlocks := hBlocks)
  simpa [TypedCfgCompiler.compileBlock?] using hCompile

theorem of_compileStmtListFuel?
    {fuel : Nat} {stmts : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? fuel stmts ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    LabelShape cfg entry input :=
  of_hasEntry
    (TypedCfgCompilerFacts.stmtList_hasEntry hCompile)
    hBlocks

theorem of_compileStmtFuel?
    {fuel : Nat} {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    LabelShape cfg entry input :=
  of_hasEntry
    (TypedCfgCompilerFacts.stmt_hasEntry hCompile)
    hBlocks

theorem procExit
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      Program.GeneratedContext program entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? name program.procs = some proc) :
    LabelShape cfg (ProcLabel.exit proc.name)
      (TypedCfgCompiler.Shape.procExit proc) := by
  refine
    ⟨TypedCfgCompiler.dispatchBlock proc generated.calls,
      generated.dispatchBlock hLookup, rfl⟩

theorem procEntry
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      Program.GeneratedContext program entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    (hLookup :
      Structured.ProcList.lookup? name program.procs = some proc) :
    LabelShape cfg (ProcLabel.entry proc.name)
      (TypedCfgCompiler.Shape.procEntry proc) := by
  obtain ⟨fragment, hBlocks, _hCalls⟩ :=
    generated.procFragment_of_lookup? hLookup
  rcases fragment.route with hDirect | hAdapter
  · rcases hDirect with ⟨hEntry, hInput⟩
    simpa [hEntry, hInput] using
      (of_compileBlockFuel?
        fragment.compile hBlocks)
  · rcases hAdapter with
      ⟨adapter, _hEntry, _hInput, _hFrame,
        hAdapterCompile, hAdapterMem⟩
    have hMem : adapter ∈ cfg.blocks := by
      have hBlocksEq :
          cfg.blocks =
            generated.main.blocks ++ generated.procBlocks ++
              TypedCfgCompiler.dispatchBlocks program.procs
                generated.calls ++
              [{ label := ProcLabel.programEnd
                 input :=
                   generated.main.fallthrough?.getD
                     TypedCfg.Shape.caller
                 body := []
                 output :=
                   generated.main.fallthrough?.getD
                     TypedCfg.Shape.caller
                 term := .invalid }] :=
        congrArg TypedCfg.Program.blocks generated.cfgEq
      rw [hBlocksEq]
      simp [hAdapterMem, List.append_assoc]
    have hFind :=
      TypedCfg.Program.findBlock?_eq_some_of_mem
        generated.wellTyped.1 hMem
    obtain ⟨hLabel, hInput⟩ :=
      TypedCfgCompilerFacts.mkBlock?_label_input hAdapterCompile
    refine ⟨adapter, ?_, hInput⟩
    simpa [hLabel] using hFind

end LabelShape

end TypedCfgPreservation
end Structured
end EvmCompiler
