import EvmCompiler.Structured.ObserverActivationBoundary
import EvmCompiler.Structured.TypedCfgCompilerEntry

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace OutcomeSimulation

abbrev Continuations :=
  TypedCfgPreservation.OutcomeSimulation.Continuations

/--
The unique CFG block at `label` expects `shape`.
-/
def LabelShape (cfg : TypedCfg.Program)
    (label : Assembly.Label) (shape : TypedCfg.Shape) : Prop :=
  ∃ block,
    cfg.findBlock? label = some block ∧
      block.input = shape

namespace LabelShape

theorem of_hasEntry
    {cfg : TypedCfg.Program} {result : TypedCfgCompiler.Result}
    {entry : Assembly.Label} {input : TypedCfg.Shape}
    (hEntry : TypedCfgCompilerFacts.HasEntry result entry input)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
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
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
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
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    LabelShape cfg entry input := by
  apply of_compileBlockFuel? (hBlocks := hBlocks)
  simpa [TypedCfgCompiler.compileBlock?] using hCompile

theorem procExit
    {program : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (generated :
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
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
      TypedCfgPreservation.Program.GeneratedContext
        program entryShapes cfg)
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

namespace ProcFragment

theorem input_returnTokenDepth
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs : List Structured.Proc} {proc : Structured.Proc}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    (fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes allProcs proc procBlocks procCalls) :
    fragment.input.returnTokenDepth? = some proc.argc := by
  rcases fragment.route with hDirect | hAdapter
  · rcases hDirect with ⟨_hEntry, hInput⟩
    simpa [hInput] using
      TypedCfgCompilerFacts.Call.returnTokenDepth?_procEntry proc
  · rcases hAdapter with
      ⟨_adapter, _hEntry, _hInput, hFrame,
        _hCompile, _hMem⟩
    exact
      TypedCfgCompilerFacts.Shape.requireReturnTokenDepth?_eq_some_iff.mp
        hFrame

theorem entry_ne_exit
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {allProcs : List Structured.Proc} {proc : Structured.Proc}
    {procBlocks : List TypedCfg.Block}
    {procCalls : List TypedCfgCompiler.DispatchSite}
    (fragment :
      TypedCfgPreservation.Program.ProcFragment
        entryShapes allProcs proc procBlocks procCalls) :
    fragment.entry ≠ ProcLabel.exit proc.name := by
  rcases fragment.route with hDirect | hAdapter
  · rcases hDirect with ⟨hEntry, _hInput⟩
    rw [hEntry]
    intro hEq
    have hString :
        "proc:" ++ proc.name ++ ":entry" =
          "proc:" ++ proc.name ++ ":exit" := by
      injection hEq
    have hList := congrArg String.toList hString
    simp [ProcLabel.entry, ProcLabel.exit,
      String.toList_append, List.append_assoc] at hList
    exact
      (by decide :
        (":entry".toList : List Char) ≠ ":exit".toList) hList
  · rcases hAdapter with
      ⟨_adapter, hEntry, _hInput, _hFrame,
        _hCompile, _hMem⟩
    rw [hEntry]
    intro hEq
    have hString :
        "proc:" ++ proc.name ++ ":body" =
          "proc:" ++ proc.name ++ ":exit" := by
      injection hEq
    have hList := congrArg String.toList hString
    simp [ProcLabel.body, ProcLabel.exit,
      String.toList_append, List.append_assoc] at hList
    exact
      (by decide :
        (":body".toList : List Char) ≠ ":exit".toList) hList

end ProcFragment

/--
The jump target belongs to the source activation that owns the CFG label.
-/
def OwnsJump {transcript : Trace}
    (cfg : TypedCfg.Program)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) (label : Assembly.Label)
    (target : EVMState) : Prop :=
  ∃ block,
    cfg.findBlock? label = some block ∧
      FrameMatches source tokens block.input target

namespace OwnsJump

theorem of_frameMatches
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {label : Assembly.Label}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hShape : LabelShape cfg label shape)
    (hFrame : FrameMatches source tokens shape target) :
    OwnsJump cfg source tokens label target := by
  rcases hShape with ⟨block, hFind, rfl⟩
  exact ⟨block, hFind, hFrame⟩

theorem congr_returns
    {transcript : Trace} {cfg : TypedCfg.Program}
    {left right : ObserverSemantics.State transcript}
    {tokens : List Word} {label : Assembly.Label}
    {target : EVMState}
    (hReturns : left.source.returns = right.source.returns)
    (hOwned : OwnsJump cfg left tokens label target) :
    OwnsJump cfg right tokens label target := by
  rcases hOwned with ⟨block, hFind, hFrame⟩
  exact
    ⟨block, hFind,
      (FrameMatches.congr_returns hReturns).mp hFrame⟩

theorem reject_extension
    {transcript : Trace} {cfg : TypedCfg.Program}
    {ancestor child : ObserverSemantics.State transcript}
    {ancestorTokens childTokens : List Word}
    {label : Assembly.Label} {shape : TypedCfg.Shape}
    {target : EVMState} {depth : Nat}
    (hOwned : OwnsJump cfg ancestor ancestorTokens label target)
    (hShape : LabelShape cfg label shape)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hExtension :
      ActivationExtension
        ancestor.source.returns ancestorTokens
        child.source.returns childTokens)
    (hAncestorHidden :
      ∃ hidden : EvmYul.Stack Word,
        TypedCfgPreservation.realizeStack
            [] ancestor.source.returns ancestorTokens = some hidden)
    (hChild : FrameMatches child childTokens shape target) :
    False := by
  rcases hOwned with ⟨ownerBlock, hOwnerFind, hOwnerFrame⟩
  rcases hShape with ⟨childBlock, hChildFind, hChildInput⟩
  have hBlockEq : ownerBlock = childBlock :=
    Option.some.inj (hOwnerFind.symm.trans hChildFind)
  subst ownerBlock
  subst shape
  exact
    (FrameMatches.not_of_extension
      hDepth hExtension hAncestorHidden hChild) hOwnerFrame

end OwnsJump

/--
Every accepted jump is activation-owned at its unique checked CFG input.
-/
def ActivationOwned {transcript : Trace}
    (cfg : TypedCfg.Program)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word)
    (accept : TypedCfg.Outcome → Prop) : Prop :=
  ∀ label target,
    accept (.jump label target) →
      OwnsJump cfg source tokens label target

namespace ActivationOwned

theorem reject_extension
    {transcript : Trace} {cfg : TypedCfg.Program}
    {ancestor child : ObserverSemantics.State transcript}
    {ancestorTokens childTokens : List Word}
    {accept : TypedCfg.Outcome → Prop}
    {label : Assembly.Label} {shape : TypedCfg.Shape}
    {target : EVMState} {depth : Nat}
    (hOwned : ActivationOwned cfg ancestor ancestorTokens accept)
    (hAccepted : accept (.jump label target))
    (hShape : LabelShape cfg label shape)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hExtension :
      ActivationExtension
        ancestor.source.returns ancestorTokens
        child.source.returns childTokens)
    (hAncestorHidden :
      ∃ hidden : EvmYul.Stack Word,
        TypedCfgPreservation.realizeStack
            [] ancestor.source.returns ancestorTokens = some hidden)
    (hChild : FrameMatches child childTokens shape target) :
    False :=
  OwnsJump.reject_extension
    (hOwned label target hAccepted)
    hShape hDepth hExtension hAncestorHidden hChild

theorem jumpAt
    {transcript : Trace} {cfg : TypedCfg.Program}
    {outerSource source : ObserverSemantics.State transcript}
    {tokens : List Word} {next : Assembly.Label}
    {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop}
    (hOwned : ActivationOwned cfg outerSource tokens accept)
    (hReturns :
      outerSource.source.returns = source.source.returns)
    (hShape : LabelShape cfg next shape) :
    ActivationOwned cfg source tokens
      (JumpAt source tokens next shape accept) := by
  intro label target hAccept
  rcases hAccept with hCurrent | hOuter
  · rcases hCurrent with ⟨rfl, hFrame⟩
    exact
      OwnsJump.of_frameMatches hShape hFrame
  · exact
      OwnsJump.congr_returns hReturns
        (hOwned label target hOuter)

end ActivationOwned

/--
A target outcome has reached one of the Structured fragment's semantic
continuations or has halted.
-/
def TargetBoundary (continuations : Continuations) :
    TypedCfg.Outcome → Prop
  | .jump label _ =>
      label = continuations.regular ∨
        continuations.breakLabel? = some label ∨
        continuations.continueLabel? = some label ∨
        continuations.leaveLabel? = some label
  | .halt _ _ => True
  | .fallthrough _ | .returnDispatch _ | .invalid _ => False

/--
An enclosing observer boundary cannot accept any label allocated at or after
`supply`.
-/
def GeneratedFresh
    (accept : TypedCfg.Outcome → Prop) (supply : LabelSupply) : Prop :=
  ∀ scope tag target,
    supply ≤ scope →
    ¬ accept (.jump (.generated scope tag) target)

/--
A statement boundary may additionally accept its one regular continuation.
Every other label allocated at or after `supply` remains internal.
-/
def GeneratedFreshExcept
    (accept : TypedCfg.Outcome → Prop) (supply : LabelSupply)
    (regular : Assembly.Label) : Prop :=
  ∀ scope tag target,
    supply ≤ scope →
    .generated scope tag ≠ regular →
    ¬ accept (.jump (.generated scope tag) target)

/--
The label was allocated before `supply`, or is a stable named label.
-/
def LabelBeforeSupply
    (label : Assembly.Label) (supply : LabelSupply) : Prop :=
  match label with
  | .named _ => True
  | .generated scope _ => scope < supply

namespace LabelBeforeSupply

theorem generated_ne
    {label : Assembly.Label} {supply scope tag : Nat}
    (hBefore : LabelBeforeSupply label supply)
    (hScope : supply ≤ scope) :
    .generated scope tag ≠ label := by
  cases label with
  | named name =>
      simp
  | generated prior priorTag =>
      simp only [LabelBeforeSupply] at hBefore
      intro hEq
      cases hEq
      omega

end LabelBeforeSupply

/--
Every semantic continuation was allocated before the current compiler supply.
-/
structure ContinuationsBeforeSupply
    (continuations :
      TypedCfgPreservation.OutcomeSimulation.Continuations)
    (supply : LabelSupply) : Prop where
  regular :
    LabelBeforeSupply continuations.regular supply
  breakLabel :
    ∀ label, continuations.breakLabel? = some label →
      LabelBeforeSupply label supply
  continueLabel :
    ∀ label, continuations.continueLabel? = some label →
      LabelBeforeSupply label supply
  leaveLabel :
    ∀ label, continuations.leaveLabel? = some label →
      LabelBeforeSupply label supply

/--
At a statement boundary the regular continuation is either inherited from an
older compiler generation or is the current statement-list tail label.
-/
def RegularAtSupply
    (regular : Assembly.Label) (supply : LabelSupply) : Prop :=
  LabelBeforeSupply regular supply ∨
    regular = TypedCfgCompiler.restLabel supply

namespace RegularAtSupply

theorem before_succ
    {regular : Assembly.Label} {supply : LabelSupply}
    (hRegular : RegularAtSupply regular supply) :
    LabelBeforeSupply regular (supply + 1) := by
  rcases hRegular with hBefore | rfl
  · cases regular with
    | named name =>
        trivial
    | generated scope tag =>
        simp only [LabelBeforeSupply] at hBefore ⊢
        omega
  · simp [LabelBeforeSupply, TypedCfgCompiler.restLabel]

theorem current_generated_ne
    {regular : Assembly.Label} {supply tag : Nat}
    (hRegular : RegularAtSupply regular supply)
    (hTag : tag ≠ 100) :
    .generated supply tag ≠ regular := by
  rcases hRegular with hBefore | rfl
  · exact hBefore.generated_ne (Nat.le_refl supply)
  · simpa [TypedCfgCompiler.restLabel] using hTag

end RegularAtSupply

namespace GeneratedFresh

theorem mono
    {accept : TypedCfg.Outcome → Prop} {supply next : LabelSupply}
    (hFresh : GeneratedFresh accept supply)
    (hSupply : supply ≤ next) :
    GeneratedFresh accept next := by
  intro scope tag target hNext
  exact hFresh scope tag target (Nat.le_trans hSupply hNext)

theorem except
    {accept : TypedCfg.Outcome → Prop} {supply : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFresh accept supply) :
    GeneratedFreshExcept accept supply regular := by
  intro scope tag target hScope _hNe
  exact hFresh scope tag target hScope

theorem jumpAt
    {transcript : Trace}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {next : Assembly.Label}
    {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop} {supply : LabelSupply}
    (hFresh : GeneratedFresh accept supply) :
    GeneratedFreshExcept
      (JumpAt source tokens next shape accept) supply next := by
  intro scope tag target hScope hNe
  simp only [JumpAt]
  push_neg
  exact
    ⟨fun hEq => (hNe hEq).elim,
      hFresh scope tag target hScope⟩

end GeneratedFresh

theorem targetBoundary_generatedFresh
    {continuations : Continuations} {supply : LabelSupply}
    (hBefore :
      ContinuationsBeforeSupply continuations supply) :
    GeneratedFresh (TargetBoundary continuations) supply := by
  intro scope tag target hScope hAccepted
  rcases hAccepted with
    hRegular | hBreak | hContinue | hLeave
  · exact hBefore.regular.generated_ne hScope hRegular
  · exact
      (hBefore.breakLabel _ hBreak).generated_ne hScope rfl
  · exact
      (hBefore.continueLabel _ hContinue).generated_ne hScope rfl
  · exact
      (hBefore.leaveLabel _ hLeave).generated_ne hScope rfl

namespace GeneratedFreshExcept

theorem mono
    {accept : TypedCfg.Outcome → Prop} {supply next : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hSupply : supply ≤ next) :
    GeneratedFreshExcept accept next regular := by
  intro scope tag target hNext hNe
  exact
    hFresh scope tag target
      (Nat.le_trans hSupply hNext) hNe

theorem reject
    {accept : TypedCfg.Outcome → Prop} {supply scope tag : Nat}
    {regular : Assembly.Label} {target : EVMState}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular) :
    ¬ accept (.jump (.generated scope tag) target) :=
  hFresh scope tag target hScope hNe

theorem toFresh
    {accept : TypedCfg.Outcome → Prop} {supply next : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hSupply : supply ≤ next)
    (hRegularBefore :
      ∀ scope tag, next ≤ scope →
        .generated scope tag ≠ regular) :
    GeneratedFresh accept next := by
  intro scope tag target hScope
  exact
    hFresh scope tag target
      (Nat.le_trans hSupply hScope)
      (hRegularBefore scope tag hScope)

theorem toFresh_of_regularBefore
    {accept : TypedCfg.Outcome → Prop} {supply next : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hSupply : supply ≤ next)
    (hRegularBefore : LabelBeforeSupply regular next) :
    GeneratedFresh accept next :=
  toFresh hFresh hSupply
    (fun scope tag hScope =>
      hRegularBefore.generated_ne hScope)

theorem reject_switch_caseBody
    {accept : TypedCfg.Outcome → Prop} {supply caseIdx : Nat}
    {regular : Assembly.Label} {target : EVMState}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hRegular : RegularAtSupply regular supply) :
    ¬ accept
      (.jump (TypedCfgCompiler.switchBodyLabel supply caseIdx) target) :=
  hFresh.reject (Nat.le_refl supply)
    (hRegular.current_generated_ne (by omega))

theorem reject_switch_defaultBody
    {accept : TypedCfg.Outcome → Prop} {supply next : Nat}
    {regular : Assembly.Label} {target : EVMState}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hRegular : RegularAtSupply regular supply)
    (hNext : supply + 1 ≤ next) :
    ¬ accept (.jump (.generated next 2000) target) :=
  hFresh.reject (by omega)
    (hRegular.before_succ.generated_ne hNext)

end GeneratedFreshExcept

end OutcomeSimulation
end ObserverAdequacy
end Structured
end EvmCompiler
