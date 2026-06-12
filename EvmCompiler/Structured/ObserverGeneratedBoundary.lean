import EvmCompiler.Structured.ObserverActivationBoundary
import EvmCompiler.Structured.TypedCfgCompilerActive
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

theorem of_compileStmtListFuel?
    {fuel : Nat} {stmts : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? fuel stmts ctx
          supply entry input regular = some result)
    (hBlocks : TypedCfgPreservation.BlocksInProgram result cfg) :
    LabelShape cfg entry input :=
  of_hasEntry
    (TypedCfgCompilerFacts.stmtList_hasEntry hCompile)
    hBlocks

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
    (hChild : FrameMatches child childTokens shape target) :
    False := by
  rcases hOwned with ⟨ownerBlock, hOwnerFind, hOwnerFrame⟩
  rcases hShape with ⟨childBlock, hChildFind, hChildInput⟩
  have hBlockEq : ownerBlock = childBlock :=
    Option.some.inj (hOwnerFind.symm.trans hChildFind)
  subst ownerBlock
  subst shape
  have hAncestorHidden :
      ∃ hidden : EvmYul.Stack Word,
        TypedCfgPreservation.realizeStack
            [] ancestor.source.returns ancestorTokens = some hidden := by
    unfold FrameMatches at hOwnerFrame
    rw [hDepth] at hOwnerFrame
    exact ⟨hOwnerFrame.choose, hOwnerFrame.choose_spec.1⟩
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

theorem congr_returns
    {transcript : Trace} {cfg : TypedCfg.Program}
    {left right : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    (hOwned : ActivationOwned cfg left tokens accept)
    (hReturns : left.source.returns = right.source.returns) :
    ActivationOwned cfg right tokens accept := by
  intro label target hAccept
  exact
    OwnsJump.congr_returns hReturns
      (hOwned label target hAccept)

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
    (hChild : FrameMatches child childTokens shape target) :
    False :=
  OwnsJump.reject_extension
    (hOwned label target hAccepted)
    hShape hDepth hExtension hChild

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
The owner activation is the current activation or one of its strict dynamic
ancestors.
-/
inductive ActivationAncestor :
    List Structured.ReturnDest → List Word →
      List Structured.ReturnDest → List Word → Prop where
  | refl (returns : List Structured.ReturnDest) (tokens : List Word) :
      ActivationAncestor returns tokens returns tokens
  | extension
      {ownerReturns currentReturns : List Structured.ReturnDest}
      {ownerTokens currentTokens : List Word}
      (hExtension :
        ActivationExtension ownerReturns ownerTokens
          currentReturns currentTokens) :
      ActivationAncestor ownerReturns ownerTokens
        currentReturns currentTokens

namespace ActivationAncestor

theorem push
    {ownerReturns currentReturns childReturns :
      List Structured.ReturnDest}
    {ownerTokens currentTokens childTokens : List Word}
    (hOwner :
      ActivationAncestor ownerReturns ownerTokens
        currentReturns currentTokens)
    (hChild :
      ActivationExtension currentReturns currentTokens
        childReturns childTokens) :
    ActivationAncestor ownerReturns ownerTokens
      childReturns childTokens := by
  cases hOwner with
  | refl =>
      exact .extension hChild
  | extension hExtension =>
      exact .extension (hExtension.trans hChild)

theorem extension_after
    {ownerReturns currentReturns childReturns :
      List Structured.ReturnDest}
    {ownerTokens currentTokens childTokens : List Word}
    (hOwner :
      ActivationAncestor ownerReturns ownerTokens
        currentReturns currentTokens)
    (hChild :
      ActivationExtension currentReturns currentTokens
        childReturns childTokens) :
    ActivationExtension ownerReturns ownerTokens
      childReturns childTokens := by
  cases hOwner with
  | refl =>
      exact hChild
  | extension hExtension =>
      exact hExtension.trans hChild

end ActivationAncestor

/--
Every accepted jump is owned by the current activation or a checked dynamic
ancestor. This is the recursive boundary invariant used by mutual adequacy.
-/
def ActivationProtected {transcript : Trace}
    (cfg : TypedCfg.Program)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word)
    (accept : TypedCfg.Outcome → Prop) : Prop :=
  ∀ label target,
    accept (.jump label target) →
      ∃ owner : ObserverSemantics.State transcript,
        ∃ ownerTokens block,
          cfg.findBlock? label = some block ∧
            FrameMatches owner ownerTokens block.input target ∧
            ActivationAncestor
              owner.source.returns ownerTokens
              source.source.returns tokens

namespace ActivationProtected

theorem of_owned
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    (hOwned : ActivationOwned cfg source tokens accept) :
    ActivationProtected cfg source tokens accept := by
  intro label target hAccept
  rcases hOwned label target hAccept with
    ⟨block, hFind, hFrame⟩
  exact
    ⟨source, tokens, block, hFind, hFrame,
      ActivationAncestor.refl _ _⟩

theorem congr_returns
    {transcript : Trace} {cfg : TypedCfg.Program}
    {left right : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    (hProtected : ActivationProtected cfg left tokens accept)
    (hReturns : left.source.returns = right.source.returns) :
    ActivationProtected cfg right tokens accept := by
  intro label target hAccept
  rcases hProtected label target hAccept with
    ⟨owner, ownerTokens, block, hFind, hFrame, hAncestor⟩
  refine ⟨owner, ownerTokens, block, hFind, hFrame, ?_⟩
  simpa [hReturns] using hAncestor

theorem reject_extension
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source child : ObserverSemantics.State transcript}
    {tokens childTokens : List Word}
    {accept : TypedCfg.Outcome → Prop}
    {label : Assembly.Label} {shape : TypedCfg.Shape}
    {target : EVMState} {depth : Nat}
    (hProtected : ActivationProtected cfg source tokens accept)
    (hAccepted : accept (.jump label target))
    (hShape : LabelShape cfg label shape)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hExtension :
      ActivationExtension
        source.source.returns tokens
        child.source.returns childTokens)
    (hChild : FrameMatches child childTokens shape target) :
    False := by
  rcases hProtected label target hAccepted with
    ⟨owner, ownerTokens, block, hFind, hOwnerFrame, hOwner⟩
  rcases hShape with ⟨shapeBlock, hShapeFind, hInput⟩
  have hBlockEq : block = shapeBlock :=
    Option.some.inj (hFind.symm.trans hShapeFind)
  subst block
  subst shape
  exact
    OwnsJump.reject_extension
      ⟨shapeBlock, hShapeFind, hOwnerFrame⟩
      ⟨shapeBlock, hShapeFind, rfl⟩
      hDepth (hOwner.extension_after hExtension) hChild

theorem jumpAt
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {next : Assembly.Label}
    {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop}
    (hProtected : ActivationProtected cfg source tokens accept)
    (hShape : LabelShape cfg next shape) :
    ActivationProtected cfg source tokens
      (JumpAt source tokens next shape accept) := by
  intro label target hAccept
  rcases hAccept with hCurrent | hOuter
  · rcases hCurrent with ⟨rfl, hFrame⟩
    rcases hShape with ⟨block, hFind, rfl⟩
    exact
      ⟨source, tokens, block, hFind, hFrame,
        ActivationAncestor.refl _ _⟩
  · exact hProtected label target hOuter

theorem pushJumpAt
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source child : ObserverSemantics.State transcript}
    {tokens childTokens : List Word} {next : Assembly.Label}
    {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop}
    (hProtected : ActivationProtected cfg source tokens accept)
    (hExtension :
      ActivationExtension
        source.source.returns tokens
        child.source.returns childTokens)
    (hShape : LabelShape cfg next shape) :
    ActivationProtected cfg child childTokens
      (JumpAt child childTokens next shape accept) := by
  intro label target hAccept
  rcases hAccept with hCurrent | hOuter
  · rcases hCurrent with ⟨rfl, hFrame⟩
    rcases hShape with ⟨block, hFind, rfl⟩
    exact
      ⟨child, childTokens, block, hFind, hFrame,
        ActivationAncestor.refl _ _⟩
  · rcases hProtected label target hOuter with
      ⟨owner, ownerTokens, block, hFind, hFrame, hOwner⟩
    exact
      ⟨owner, ownerTokens, block, hFind, hFrame,
        hOwner.push hExtension⟩

end ActivationProtected

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

theorem mono
    {label : Assembly.Label} {supply next : LabelSupply}
    (hBefore : LabelBeforeSupply label supply)
    (hSupply : supply ≤ next) :
    LabelBeforeSupply label next := by
  cases label with
  | named name =>
      trivial
  | generated scope tag =>
      simp only [LabelBeforeSupply] at hBefore ⊢
      exact Nat.lt_of_lt_of_le hBefore hSupply

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

theorem advance
    {regular : Assembly.Label} {supply next : LabelSupply}
    (hRegular : RegularAtSupply regular supply)
    (hNext : supply + 1 ≤ next) :
    RegularAtSupply regular next :=
  Or.inl (hRegular.before_succ.mono hNext)

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

theorem jumpAt_rest
    {transcript : Trace}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop} {supply : LabelSupply}
    {regular : Assembly.Label}
    (hFresh : GeneratedFreshExcept accept supply regular)
    (hRegular : RegularAtSupply regular supply) :
    GeneratedFreshExcept
      (JumpAt source tokens (TypedCfgCompiler.restLabel supply)
        shape accept)
      supply (TypedCfgCompiler.restLabel supply) := by
  intro scope tag target hScope hNe hAccepted
  rcases hAccepted with hCurrent | hOuter
  · exact hNe hCurrent.1
  · apply hFresh scope tag target hScope
    rcases hRegular with hBefore | hRest
    · exact hBefore.generated_ne hScope
    · intro hEq
      apply hNe
      exact hEq.trans hRest
    exact hOuter

end GeneratedFreshExcept

/--
Activation-aware freshness for recursive procedure execution.

A generated label at or after `supply`, other than the current regular
continuation, may be accepted only when that acceptance belongs to a strict
dynamic ancestor. This permits recursive executions to reuse the procedure's
static labels without treating an ancestor continuation as a boundary of the
current activation.
-/
def ActivationFreshExcept {transcript : Trace}
    (cfg : TypedCfg.Program)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word)
    (accept : TypedCfg.Outcome → Prop)
    (supply : LabelSupply) (regular : Assembly.Label) : Prop :=
  ∀ scope tag target,
    supply ≤ scope →
      .generated scope tag ≠ regular →
      accept (.jump (.generated scope tag) target) →
        ∃ owner : ObserverSemantics.State transcript,
          ∃ ownerTokens block,
            cfg.findBlock? (.generated scope tag) = some block ∧
              FrameMatches owner ownerTokens block.input target ∧
              ActivationExtension
                owner.source.returns ownerTokens
                source.source.returns tokens

namespace ActivationFreshExcept

theorem of_generated
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply : LabelSupply} {regular : Assembly.Label}
    (hFresh : GeneratedFreshExcept accept supply regular) :
    ActivationFreshExcept cfg source tokens accept supply regular := by
  intro scope tag target hScope hNe hAccepted
  exact (hFresh scope tag target hScope hNe hAccepted).elim

theorem mono
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply next : LabelSupply} {regular : Assembly.Label}
    (hFresh :
      ActivationFreshExcept cfg source tokens accept supply regular)
    (hSupply : supply ≤ next) :
    ActivationFreshExcept cfg source tokens accept next regular := by
  intro scope tag target hScope hNe hAccepted
  exact
    hFresh scope tag target
      (Nat.le_trans hSupply hScope) hNe hAccepted

theorem congr_returns
    {transcript : Trace} {cfg : TypedCfg.Program}
    {left right : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply : LabelSupply} {regular : Assembly.Label}
    (hFresh :
      ActivationFreshExcept cfg left tokens accept supply regular)
    (hReturns : left.source.returns = right.source.returns) :
    ActivationFreshExcept cfg right tokens accept supply regular := by
  intro scope tag target hScope hNe hAccepted
  rcases hFresh scope tag target hScope hNe hAccepted with
    ⟨owner, ownerTokens, block, hFind, hFrame, hExtension⟩
  refine ⟨owner, ownerTokens, block, hFind, hFrame, ?_⟩
  simpa [hReturns] using hExtension

theorem jumpAt_rest
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop} {supply : LabelSupply}
    {regular : Assembly.Label}
    (hFresh :
      ActivationFreshExcept cfg source tokens accept supply regular)
    (hRegular : RegularAtSupply regular supply) :
    ActivationFreshExcept cfg source tokens
      (JumpAt source tokens (TypedCfgCompiler.restLabel supply)
        shape accept)
      supply (TypedCfgCompiler.restLabel supply) := by
  intro scope tag target hScope hNe hAccepted
  rcases hAccepted with hCurrent | hOuter
  · exact (hNe hCurrent.1).elim
  · apply hFresh scope tag target hScope
    · rcases hRegular with hBefore | hRest
      · exact hBefore.generated_ne hScope
      · intro hEq
        exact hNe (hEq.trans hRest)
    · exact hOuter

theorem pushJumpAt
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source child : ObserverSemantics.State transcript}
    {tokens childTokens : List Word}
    {accept : TypedCfg.Outcome → Prop}
    {next : Assembly.Label} {shape : TypedCfg.Shape}
    {supply : LabelSupply}
    (hProtected : ActivationProtected cfg source tokens accept)
    (hExtension :
      ActivationExtension
        source.source.returns tokens
        child.source.returns childTokens) :
    ActivationFreshExcept cfg child childTokens
      (JumpAt child childTokens next shape accept) supply next := by
  intro scope tag target _hScope hNe hAccepted
  rcases hAccepted with hCurrent | hOuter
  · exact (hNe hCurrent.1).elim
  · rcases hProtected _ _ hOuter with
      ⟨owner, ownerTokens, block, hFind, hFrame, hAncestor⟩
    exact
      ⟨owner, ownerTokens, block, hFind, hFrame,
        hAncestor.extension_after hExtension⟩

theorem reject
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply scope tag : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape} {target : EVMState} {depth : Nat}
    (hFresh :
      ActivationFreshExcept cfg source tokens accept supply regular)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular)
    (hAccepted : accept (.jump (.generated scope tag) target))
    (hShape : LabelShape cfg (.generated scope tag) shape)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCurrent : FrameMatches source tokens shape target) :
    False := by
  rcases hFresh scope tag target hScope hNe hAccepted with
    ⟨owner, ownerTokens, block, hFind, hOwnerFrame, hExtension⟩
  exact
    OwnsJump.reject_extension
      ⟨block, hFind, hOwnerFrame⟩
      hShape hDepth hExtension hCurrent

end ActivationFreshExcept

/--
The complete recursive acceptance contract for one Structured compiler
fragment. `ownership` tracks who owns every accepted jump; `fresh` states that
new generated labels can be accepted only by strict ancestors.
-/
structure RecursiveBoundary {transcript : Trace}
    (cfg : TypedCfg.Program)
    (source : ObserverSemantics.State transcript)
    (tokens : List Word)
    (accept : TypedCfg.Outcome → Prop)
    (supply : LabelSupply) (regular : Assembly.Label) : Prop where
  ownership : ActivationProtected cfg source tokens accept
  fresh :
    ActivationFreshExcept cfg source tokens accept supply regular

namespace RecursiveBoundary

theorem congr_returns
    {transcript : Trace} {cfg : TypedCfg.Program}
    {left right : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply : LabelSupply} {regular : Assembly.Label}
    (hBoundary :
      RecursiveBoundary cfg left tokens accept supply regular)
    (hReturns : left.source.returns = right.source.returns) :
    RecursiveBoundary cfg right tokens accept supply regular :=
  ⟨hBoundary.ownership.congr_returns hReturns,
    hBoundary.fresh.congr_returns hReturns⟩

theorem mono
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply next : LabelSupply} {regular : Assembly.Label}
    (hBoundary :
      RecursiveBoundary cfg source tokens accept supply regular)
    (hSupply : supply ≤ next) :
    RecursiveBoundary cfg source tokens accept next regular :=
  ⟨hBoundary.ownership, hBoundary.fresh.mono hSupply⟩

theorem jumpAt_rest
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape}
    (hBoundary :
      RecursiveBoundary cfg source tokens accept supply regular)
    (hRegular : RegularAtSupply regular supply)
    (hShape :
      LabelShape cfg (TypedCfgCompiler.restLabel supply) shape) :
    RecursiveBoundary cfg source tokens
      (JumpAt source tokens (TypedCfgCompiler.restLabel supply)
        shape accept)
      supply (TypedCfgCompiler.restLabel supply) :=
  ⟨hBoundary.ownership.jumpAt hShape,
    hBoundary.fresh.jumpAt_rest hRegular⟩

theorem pushJumpAt
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source child : ObserverSemantics.State transcript}
    {tokens childTokens : List Word}
    {accept : TypedCfg.Outcome → Prop}
    {next : Assembly.Label} {shape : TypedCfg.Shape}
    {supply : LabelSupply} {regular : Assembly.Label}
    (hBoundary :
      RecursiveBoundary cfg source tokens accept supply regular)
    (hExtension :
      ActivationExtension
        source.source.returns tokens
        child.source.returns childTokens)
    (hShape : LabelShape cfg next shape)
    (childSupply : LabelSupply) :
    RecursiveBoundary cfg child childTokens
      (JumpAt child childTokens next shape accept)
      childSupply next :=
  ⟨hBoundary.ownership.pushJumpAt hExtension hShape,
    ActivationFreshExcept.pushJumpAt
      hBoundary.ownership hExtension⟩

theorem reject
    {transcript : Trace} {cfg : TypedCfg.Program}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {accept : TypedCfg.Outcome → Prop}
    {supply scope tag : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape} {target : EVMState} {depth : Nat}
    (hBoundary :
      RecursiveBoundary cfg source tokens accept supply regular)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular)
    (hAccepted : accept (.jump (.generated scope tag) target))
    (hShape : LabelShape cfg (.generated scope tag) shape)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCurrent : FrameMatches source tokens shape target) :
    False :=
  hBoundary.fresh.reject
    hScope hNe hAccepted hShape hDepth hCurrent

end RecursiveBoundary

end OutcomeSimulation
end ObserverAdequacy
end Structured
end EvmCompiler
