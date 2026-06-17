import EvmCompiler.Structured.TypedCfgCompilerActive
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

/--
Entry classification for one dynamic Structured activation.

The top activation has no realized return tokens. Every procedure activation
instead carries a compiler-owned return token in its TypedCfg input shape.
-/
def ActivationInput
    (tokens : List Word) (input : TypedCfg.Shape) : Prop :=
  tokens = [] ∨ TypedCfgCompilerFacts.ReturnTokenActive input

namespace ActivationInput

theorem top (input : TypedCfg.Shape) :
    ActivationInput [] input :=
  Or.inl rfl

theorem active
    {tokens : List Word} {input : TypedCfg.Shape}
    (hActive : TypedCfgCompilerFacts.ReturnTokenActive input) :
    ActivationInput tokens input :=
  Or.inr hActive

theorem code
    {tokens : List Word} {code : Structured.Code}
    {input output : TypedCfg.Shape}
    (hActivation : ActivationInput tokens input)
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    ActivationInput tokens output := by
  rcases hActivation with hTop | hActive
  · exact Or.inl hTop
  · exact Or.inr (hActive.code hType)

theorem tail
    {tokens : List Word} {shape : TypedCfg.Shape}
    (hActivation : ActivationInput tokens shape)
    (hSource : 1 ≤ TypedCfgCompiler.Shape.sourceLength shape) :
    ActivationInput tokens
      { shape with slots := shape.slots.tail } := by
  rcases hActivation with hTop | hActive
  · exact Or.inl hTop
  · exact Or.inr (hActive.tail hSource)

theorem stmtFallthrough
    {tokens : List Word} {fuel : Nat}
    {stmt : Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input output : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hActivation : ActivationInput tokens input)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? fuel stmt ctx
          supply entry input regular = some result)
    (hFallthrough : result.fallthrough? = some output) :
    ActivationInput tokens output := by
  rcases hActivation with hTop | hActive
  · exact Or.inl hTop
  · exact
      Or.inr
        ((TypedCfgCompilerFacts.activeResult_of_compileStmtFuel?
          hActive hCompile).fallthrough output hFallthrough)

theorem blockFallthrough
    {tokens : List Word} {fuel : Nat}
    {block : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input output : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hActivation : ActivationInput tokens input)
    (hCompile :
      TypedCfgCompiler.compileBlockFuel? fuel block ctx
          supply entry input regular = some result)
    (hFallthrough : result.fallthrough? = some output) :
    ActivationInput tokens output := by
  rcases hActivation with hTop | hActive
  · exact Or.inl hTop
  · exact
      Or.inr
        ((TypedCfgCompilerFacts.activeResult_of_compileBlockFuel?
          hActive hCompile).fallthrough output hFallthrough)

end ActivationInput

namespace SourceFrameFits

theorem of_returnTokenDepth_eq_stackLength
    {shape : TypedCfg.Shape} {stackLength depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hLength : stackLength = depth) :
    TypedCfgCompiler.Shape.SourceFrameFits shape stackLength := by
  constructor
  · rw [
      TypedCfgCompilerFacts.Shape.sourceLength_eq_of_returnTokenDepth?_eq_some
        hDepth,
      hLength]
  · intro actualDepth hActualDepth
    have hDepthEq : actualDepth = depth :=
      Option.some.inj (hActualDepth.symm.trans hDepth)
    omega

theorem procEntry_of_splitArgs
    {proc : Structured.Proc}
    {stack args callerStack : EvmYul.Stack Word}
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc stack =
        some (args, callerStack)) :
    TypedCfgCompiler.Shape.SourceFrameFits
      (TypedCfgCompiler.Shape.procEntry proc) args.length := by
  apply of_returnTokenDepth_eq_stackLength
  · exact TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc
  · exact
      (TypedCfgPreservation.CallStack.splitArgs?_eq_some hSplit).1

end SourceFrameFits

namespace Program.ProcFragment

theorem input_sourceFrameFits_of_splitArgs
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs : List Structured.Proc} {proc : Structured.Proc}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    (fragment :
      Program.ProcFragment
        entryShapes allProcs proc procBlocks procCalls)
    {stack args callerStack : EvmYul.Stack Word}
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc stack =
        some (args, callerStack)) :
    TypedCfgCompiler.Shape.SourceFrameFits
      fragment.input args.length := by
  apply SourceFrameFits.of_returnTokenDepth_eq_stackLength
  · exact fragment.input_returnTokenDepth
  · exact
      (TypedCfgPreservation.CallStack.splitArgs?_eq_some hSplit).1

end Program.ProcFragment

end TypedCfgPreservation
end Structured
end EvmCompiler
