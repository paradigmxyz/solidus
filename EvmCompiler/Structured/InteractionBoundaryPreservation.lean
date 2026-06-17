import EvmCompiler.Structured.InteractionControlPreservation
import EvmCompiler.Structured.TypedCfgPreservation.GeneratedBoundary

namespace EvmCompiler
namespace Structured
namespace InteractionBoundaryPreservation

namespace OpenOutcome

abbrev StopPolicy :=
  InteractionControlPreservation.OpenOutcome.StopPolicy

/--
Every continuation recognized by one compiler boundary has its checked input
shape in the ambient CFG.
-/
structure BoundaryShapes
    (cfg : TypedCfg.Program)
    (result : TypedCfgCompiler.Result)
    (ctx : TypedCfgCompiler.Context)
    (regular : Assembly.Label) : Prop where
  regular :
    ∀ {shape},
      result.fallthrough? = some shape →
        TypedCfgPreservation.LabelShape cfg regular shape
  break_ :
    ∀ {label shape},
      ctx.breakLabel? = some label →
        ctx.breakShape? = some shape →
          TypedCfgPreservation.LabelShape cfg label shape
  continue_ :
    ∀ {label shape},
      ctx.continueLabel? = some label →
        ctx.continueShape? = some shape →
          TypedCfgPreservation.LabelShape cfg label shape
  leave :
    ∀ {label shape},
      ctx.leaveLabel? = some label →
        ctx.leaveShape? = some shape →
          TypedCfgPreservation.LabelShape cfg label shape

/--
Every jump stopped by `policy` belongs to the current Structured activation or
to one of its checked dynamic ancestors.
-/
def StopPolicy.ActivationProtected
    (cfg : TypedCfg.Program)
    (returns : List ReturnDest) (tokens : List Word)
    (policy : StopPolicy) : Prop :=
  ∀ label target,
    policy label target = true →
      ∃ ownerReturns ownerTokens block,
        cfg.findBlock? label = some block ∧
          TypedCfgPreservation.ActivationFrameMatches
            ownerReturns ownerTokens block.input target ∧
          TypedCfgPreservation.ActivationAncestor
            ownerReturns ownerTokens returns tokens

namespace StopPolicy.ActivationProtected

theorem empty
    (cfg : TypedCfg.Program)
    (returns : List ReturnDest) (tokens : List Word) :
    StopPolicy.ActivationProtected cfg returns tokens
      (fun _ _ => false) := by
  intro label target hStop
  simp at hStop

theorem congr_returns
    {cfg : TypedCfg.Program}
    {left right : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    (hProtected :
      StopPolicy.ActivationProtected cfg left tokens policy)
    (hReturns : left = right) :
    StopPolicy.ActivationProtected cfg right tokens policy := by
  subst right
  exact hProtected

theorem extend
    {cfg : TypedCfg.Program}
    {ancestorReturns childReturns : List ReturnDest}
    {ancestorTokens childTokens : List Word}
    {policy : StopPolicy}
    (hProtected :
      StopPolicy.ActivationProtected
        cfg ancestorReturns ancestorTokens policy)
    (hExtension :
      TypedCfgPreservation.ActivationExtension
        ancestorReturns ancestorTokens childReturns childTokens) :
    StopPolicy.ActivationProtected
      cfg childReturns childTokens policy := by
  intro label target hStopped
  rcases hProtected label target hStopped with
    ⟨ownerReturns, ownerTokens, block,
      hFind, hFrame, hOwner⟩
  exact
    ⟨ownerReturns, ownerTokens, block,
      hFind, hFrame, hOwner.push hExtension⟩

theorem reject_extension
    {cfg : TypedCfg.Program}
    {ancestorReturns childReturns : List ReturnDest}
    {ancestorTokens childTokens : List Word}
    {policy : StopPolicy}
    {label : Assembly.Label} {shape : TypedCfg.Shape}
    {target : EVMState} {depth : Nat}
    (hProtected :
      StopPolicy.ActivationProtected
        cfg ancestorReturns ancestorTokens policy)
    (hStopped : policy label target = true)
    (hShape :
      TypedCfgPreservation.LabelShape cfg label shape)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hExtension :
      TypedCfgPreservation.ActivationExtension
        ancestorReturns ancestorTokens childReturns childTokens)
    (hChild :
      TypedCfgPreservation.ActivationFrameMatches
        childReturns childTokens shape target) :
    False := by
  rcases hProtected label target hStopped with
    ⟨ownerReturns, ownerTokens, ownerBlock,
      hOwnerFind, hOwnerFrame, hOwner⟩
  rcases hShape with ⟨shapeBlock, hShapeFind, hInput⟩
  have hBlockEq : ownerBlock = shapeBlock :=
    Option.some.inj (hOwnerFind.symm.trans hShapeFind)
  subst ownerBlock
  subst shape
  have hOwnerHidden :
      ∃ hidden : EvmYul.Stack Word,
        TypedCfgPreservation.realizeStack
            [] ownerReturns ownerTokens = some hidden := by
    unfold TypedCfgPreservation.ActivationFrameMatches at hOwnerFrame
    rw [hDepth] at hOwnerFrame
    exact ⟨hOwnerFrame.choose, hOwnerFrame.choose_spec.1⟩
  exact
    (TypedCfgPreservation.ActivationFrameMatches.not_of_extension
      hDepth (hOwner.extension_after hExtension)
      hOwnerHidden hChild) hOwnerFrame

theorem eq_false_of_extension
    {cfg : TypedCfg.Program}
    {ancestorReturns childReturns : List ReturnDest}
    {ancestorTokens childTokens : List Word}
    {policy : StopPolicy}
    {label : Assembly.Label} {shape : TypedCfg.Shape}
    {target : EVMState} {depth : Nat}
    (hProtected :
      StopPolicy.ActivationProtected
        cfg ancestorReturns ancestorTokens policy)
    (hShape :
      TypedCfgPreservation.LabelShape cfg label shape)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hExtension :
      TypedCfgPreservation.ActivationExtension
        ancestorReturns ancestorTokens childReturns childTokens)
    (hChild :
      TypedCfgPreservation.ActivationFrameMatches
        childReturns childTokens shape target) :
    policy label target = false := by
  cases hStop : policy label target with
  | false =>
      rfl
  | true =>
      exact False.elim
        (hProtected.reject_extension
          hStop hShape hDepth hExtension hChild)

theorem eq_false_of_stateRel_extension
    {cfg : TypedCfg.Program}
    {ancestorReturns : List ReturnDest}
    {ancestorTokens childTokens : List Word}
    {policy : StopPolicy}
    {source : RunState} {target : EVMState}
    {label : Assembly.Label} {shape : TypedCfg.Shape}
    {depth : Nat}
    (hProtected :
      StopPolicy.ActivationProtected
        cfg ancestorReturns ancestorTokens policy)
    (hShape :
      TypedCfgPreservation.LabelShape cfg label shape)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hExtension :
      TypedCfgPreservation.ActivationExtension
        ancestorReturns ancestorTokens source.returns childTokens)
    (hRel :
      TypedCfgPreservation.StateRel source childTokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        shape source.evm.stack.length) :
    policy label target = false :=
  hProtected.eq_false_of_extension
    hShape hDepth hExtension
      (TypedCfgPreservation.ActivationFrameMatches.of_stateRel
        hRel hFits)

theorem push
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {regular : Assembly.Label}
    (hOuter :
      StopPolicy.ActivationProtected cfg returns tokens outer)
    (hShapes : BoundaryShapes cfg result ctx regular) :
    StopPolicy.ActivationProtected cfg returns tokens
      (InteractionControlPreservation.OpenOutcome.pushStopJump
        result ctx regular returns tokens outer) := by
  intro label target hStopped
  by_cases hOuterStopped : outer label target = true
  · exact hOuter label target hOuterStopped
  have hLocal :
      InteractionControlPreservation.OpenOutcome.stopJump
          result ctx regular returns tokens label target =
        true := by
    simpa [
      InteractionControlPreservation.OpenOutcome.pushStopJump,
      hOuterStopped] using hStopped
  simp only [
    InteractionControlPreservation.OpenOutcome.stopJump,
    Bool.or_eq_true_iff] at hLocal
  rcases hLocal with hBeforeLeave | hLeave
  · rcases hBeforeLeave with hBeforeContinue | hContinue
    · rcases hBeforeContinue with hRegular | hBreak
      · rcases
            InteractionControlPreservation.OpenOutcome.continuationMatches?_eq_true_iff.mp
              hRegular with
          ⟨shape, hLabel, hShape, hFrame⟩
        have hLabelEq : regular = label :=
          Option.some.inj hLabel
        subst label
        rcases hShapes.regular hShape with
          ⟨block, hFind, hInput⟩
        refine
          ⟨returns, tokens, block, hFind, ?_,
            TypedCfgPreservation.ActivationAncestor.refl returns tokens⟩
        simpa [hInput] using hFrame
      · rcases
            InteractionControlPreservation.OpenOutcome.continuationMatches?_eq_true_iff.mp
              hBreak with
          ⟨shape, hLabel, hShape, hFrame⟩
        rcases hShapes.break_ hLabel hShape with
          ⟨block, hFind, hInput⟩
        refine
          ⟨returns, tokens, block, hFind, ?_,
            TypedCfgPreservation.ActivationAncestor.refl returns tokens⟩
        simpa [hInput] using hFrame
    · rcases
          InteractionControlPreservation.OpenOutcome.continuationMatches?_eq_true_iff.mp
            hContinue with
        ⟨shape, hLabel, hShape, hFrame⟩
      rcases hShapes.continue_ hLabel hShape with
        ⟨block, hFind, hInput⟩
      refine
        ⟨returns, tokens, block, hFind, ?_,
          TypedCfgPreservation.ActivationAncestor.refl returns tokens⟩
      simpa [hInput] using hFrame
  · rcases
        InteractionControlPreservation.OpenOutcome.continuationMatches?_eq_true_iff.mp
          hLeave with
      ⟨shape, hLabel, hShape, hFrame⟩
    rcases hShapes.leave hLabel hShape with
      ⟨block, hFind, hInput⟩
    refine
      ⟨returns, tokens, block, hFind, ?_,
        TypedCfgPreservation.ActivationAncestor.refl returns tokens⟩
    simpa [hInput] using hFrame

end StopPolicy.ActivationProtected

/--
Activation-aware freshness for recursive procedure execution.

A generated label at or after `supply`, other than the current regular
continuation, may be stopped only when that stop belongs to a strict dynamic
ancestor. Recursive calls may therefore reuse static CFG labels without
mistaking an ancestor continuation for a boundary of the current activation.
-/
def StopPolicy.ActivationFreshExcept
    (cfg : TypedCfg.Program)
    (returns : List ReturnDest) (tokens : List Word)
    (policy : StopPolicy)
    (supply : LabelSupply) (regular : Assembly.Label) : Prop :=
  ∀ scope tag target,
    supply ≤ scope →
      .generated scope tag ≠ regular →
      policy (.generated scope tag) target = true →
        ∃ ownerReturns ownerTokens block,
          cfg.findBlock? (.generated scope tag) = some block ∧
            TypedCfgPreservation.ActivationFrameMatches
              ownerReturns ownerTokens block.input target ∧
            TypedCfgPreservation.ActivationExtension
              ownerReturns ownerTokens returns tokens

namespace StopPolicy.ActivationFreshExcept

theorem of_static
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply : LabelSupply} {regular : Assembly.Label}
    (hFresh :
      InteractionControlPreservation.OpenOutcome.StopPolicy.FreshExceptAt
        policy regular supply) :
    StopPolicy.ActivationFreshExcept
      cfg returns tokens policy supply regular := by
  intro scope tag target hScope hNe hStopped
  rw [hFresh scope tag target hScope hNe] at hStopped
  cases hStopped

theorem mono
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply next : LabelSupply} {regular : Assembly.Label}
    (hFresh :
      StopPolicy.ActivationFreshExcept
        cfg returns tokens policy supply regular)
    (hSupply : supply ≤ next) :
    StopPolicy.ActivationFreshExcept
      cfg returns tokens policy next regular := by
  intro scope tag target hScope hNe hStopped
  exact
    hFresh scope tag target
      (Nat.le_trans hSupply hScope) hNe hStopped

theorem congr_returns
    {cfg : TypedCfg.Program}
    {left right : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply : LabelSupply} {regular : Assembly.Label}
    (hFresh :
      StopPolicy.ActivationFreshExcept
        cfg left tokens policy supply regular)
    (hReturns : left = right) :
    StopPolicy.ActivationFreshExcept
      cfg right tokens policy supply regular := by
  subst right
  exact hFresh

theorem reject
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply scope tag : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hFresh :
      StopPolicy.ActivationFreshExcept
        cfg returns tokens policy supply regular)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular)
    (hStopped : policy (.generated scope tag) target = true)
    (hShape :
      TypedCfgPreservation.LabelShape
        cfg (.generated scope tag) shape)
    (hActivation :
      TypedCfgPreservation.ActivationInput tokens shape)
    (hCurrent :
      TypedCfgPreservation.ActivationFrameMatches
        returns tokens shape target) :
    False := by
  rcases hFresh scope tag target hScope hNe hStopped with
    ⟨ownerReturns, ownerTokens, ownerBlock,
      hOwnerFind, hOwnerFrame, hExtension⟩
  rcases hShape with ⟨shapeBlock, hShapeFind, hInput⟩
  have hBlockEq : ownerBlock = shapeBlock :=
    Option.some.inj (hOwnerFind.symm.trans hShapeFind)
  subst ownerBlock
  subst shape
  rcases hActivation with hTop | hActive
  · exact hExtension.childTokens_ne_nil hTop
  · rcases hActive with ⟨depth, hDepth⟩
    have hOwnerHidden :
        ∃ hidden : EvmYul.Stack Word,
          TypedCfgPreservation.realizeStack
              [] ownerReturns ownerTokens = some hidden := by
      unfold TypedCfgPreservation.ActivationFrameMatches at hOwnerFrame
      rw [hDepth] at hOwnerFrame
      exact ⟨hOwnerFrame.choose, hOwnerFrame.choose_spec.1⟩
    exact
      (TypedCfgPreservation.ActivationFrameMatches.not_of_extension
        hDepth hExtension hOwnerHidden hCurrent) hOwnerFrame

theorem eq_false
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply scope tag : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hFresh :
      StopPolicy.ActivationFreshExcept
        cfg returns tokens policy supply regular)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular)
    (hShape :
      TypedCfgPreservation.LabelShape
        cfg (.generated scope tag) shape)
    (hActivation :
      TypedCfgPreservation.ActivationInput tokens shape)
    (hCurrent :
      TypedCfgPreservation.ActivationFrameMatches
        returns tokens shape target) :
    policy (.generated scope tag) target = false := by
  cases hStopped : policy (.generated scope tag) target with
  | false =>
      rfl
  | true =>
      exact False.elim
        (hFresh.reject hScope hNe hStopped
          hShape hActivation hCurrent)

theorem eq_false_of_stateRel
    {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {supply scope tag : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hFresh :
      StopPolicy.ActivationFreshExcept
        cfg source.returns tokens policy supply regular)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular)
    (hShape :
      TypedCfgPreservation.LabelShape
        cfg (.generated scope tag) shape)
    (hActivation :
      TypedCfgPreservation.ActivationInput tokens shape)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        shape source.evm.stack.length) :
    policy (.generated scope tag) target = false :=
  hFresh.eq_false hScope hNe hShape hActivation
    (TypedCfgPreservation.ActivationFrameMatches.of_stateRel
      hRel hFits)

theorem push
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular regular : Assembly.Label}
    {supply : LabelSupply}
    (hFresh :
      StopPolicy.ActivationFreshExcept
        cfg returns tokens outer supply boundaryRegular)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply) :
    StopPolicy.ActivationFreshExcept cfg returns tokens
      (InteractionControlPreservation.OpenOutcome.pushStopJump
        result ctx regular returns tokens outer)
      supply regular := by
  intro scope tag target hScope hNe hStopped
  simp only [
    InteractionControlPreservation.OpenOutcome.pushStopJump,
    Bool.or_eq_true_iff] at hStopped
  rcases hStopped with hOuter | hLocal
  · exact
      hFresh scope tag target hScope
        (hBefore.regular.generated_ne hScope) hOuter
  · have hLocalFalse :
        InteractionControlPreservation.OpenOutcome.stopJump
            result ctx regular returns tokens
            (.generated scope tag) target =
          false :=
      InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false_of_regular_ne
        hBefore hNe hScope returns tokens target
    rw [hLocalFalse] at hLocal
    cases hLocal

theorem push_child
    {cfg : TypedCfg.Program}
    {ancestorReturns childReturns : List ReturnDest}
    {ancestorTokens childTokens : List Word}
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular regular : Assembly.Label}
    {supply : LabelSupply}
    (hProtected :
      StopPolicy.ActivationProtected
        cfg ancestorReturns ancestorTokens outer)
    (hExtension :
      TypedCfgPreservation.ActivationExtension
        ancestorReturns ancestorTokens childReturns childTokens)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply) :
    StopPolicy.ActivationFreshExcept cfg childReturns childTokens
      (InteractionControlPreservation.OpenOutcome.pushStopJump
        result ctx regular childReturns childTokens outer)
      supply regular := by
  intro scope tag target hScope hNe hStopped
  simp only [
    InteractionControlPreservation.OpenOutcome.pushStopJump,
    Bool.or_eq_true_iff] at hStopped
  rcases hStopped with hOuter | hLocal
  · rcases hProtected _ _ hOuter with
      ⟨ownerReturns, ownerTokens, block,
        hFind, hFrame, hOwner⟩
    exact
      ⟨ownerReturns, ownerTokens, block,
        hFind, hFrame, hOwner.extension_after hExtension⟩
  · have hLocalFalse :
        InteractionControlPreservation.OpenOutcome.stopJump
            result ctx regular childReturns childTokens
            (.generated scope tag) target =
          false :=
      InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false_of_regular_ne
        hBefore hNe hScope childReturns childTokens target
    rw [hLocalFalse] at hLocal
    cases hLocal

end StopPolicy.ActivationFreshExcept

/--
The recursive target-boundary contract for one Structured compiler fragment.

`ownership` tracks which dynamic activation owns each stopped jump. `fresh`
permits newly generated labels to stop only for strict dynamic ancestors.
-/
structure StopPolicy.RecursiveBoundary
    (cfg : TypedCfg.Program)
    (returns : List ReturnDest) (tokens : List Word)
    (policy : StopPolicy)
    (supply : LabelSupply) (regular : Assembly.Label) : Prop where
  ownership :
    StopPolicy.ActivationProtected cfg returns tokens policy
  fresh :
    StopPolicy.ActivationFreshExcept
      cfg returns tokens policy supply regular

namespace StopPolicy.RecursiveBoundary

theorem congr_returns
    {cfg : TypedCfg.Program}
    {left right : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply : LabelSupply} {regular : Assembly.Label}
    (hBoundary :
      StopPolicy.RecursiveBoundary
        cfg left tokens policy supply regular)
    (hReturns : left = right) :
    StopPolicy.RecursiveBoundary
      cfg right tokens policy supply regular :=
  ⟨hBoundary.ownership.congr_returns hReturns,
    hBoundary.fresh.congr_returns hReturns⟩

theorem mono
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply next : LabelSupply} {regular : Assembly.Label}
    (hBoundary :
      StopPolicy.RecursiveBoundary
        cfg returns tokens policy supply regular)
    (hSupply : supply ≤ next) :
    StopPolicy.RecursiveBoundary
      cfg returns tokens policy next regular :=
  ⟨hBoundary.ownership, hBoundary.fresh.mono hSupply⟩

/--
Change the distinguished regular continuation while retaining the same
activation and supply. The previous regular label predates every generated
label in the fragment, so it cannot be the generated label under inspection.
-/
theorem rebase_regular
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply : LabelSupply} {oldRegular newRegular : Assembly.Label}
    (hBoundary :
      StopPolicy.RecursiveBoundary
        cfg returns tokens policy supply oldRegular)
    (hOldBefore :
      TypedCfgCompilerFacts.LabelBeforeSupply oldRegular supply) :
    StopPolicy.RecursiveBoundary
      cfg returns tokens policy supply newRegular := by
  refine ⟨hBoundary.ownership, ?_⟩
  intro scope tag target hScope _hNewNe hStopped
  exact
    hBoundary.fresh scope tag target hScope
      (hOldBefore.generated_ne hScope) hStopped

theorem rebase_current
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {policy : StopPolicy}
    {supply : LabelSupply} {oldRegular newRegular : Assembly.Label}
    (hBoundary :
      StopPolicy.RecursiveBoundary
        cfg returns tokens policy supply oldRegular)
    (hOld :
      TypedCfgCompilerFacts.RegularAtSupply oldRegular supply)
    (hNew :
      newRegular = TypedCfgCompiler.restLabel supply) :
    StopPolicy.RecursiveBoundary
      cfg returns tokens policy supply newRegular := by
  rcases hOld with hBefore | hCurrent
  · exact hBoundary.rebase_regular hBefore
  · have hEq : oldRegular = newRegular :=
      hCurrent.trans hNew.symm
    cases hEq
    exact hBoundary

theorem push_current
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular regular : Assembly.Label}
    {supply : LabelSupply}
    (hBoundary :
      StopPolicy.RecursiveBoundary
        cfg returns tokens outer supply boundaryRegular)
    (hBoundaryRegular :
      TypedCfgCompilerFacts.RegularAtSupply boundaryRegular supply)
    (hBefore :
      TypedCfgCompilerFacts.NonregularLabelsBeforeSupply ctx supply)
    (hRegular :
      regular = TypedCfgCompiler.restLabel supply)
    (hShapes : BoundaryShapes cfg result ctx regular) :
    StopPolicy.RecursiveBoundary cfg returns tokens
      (InteractionControlPreservation.OpenOutcome.pushStopJump
        result ctx regular returns tokens outer)
      supply regular := by
  refine
    ⟨hBoundary.ownership.push hShapes, ?_⟩
  intro scope tag target hScope hNe hStopped
  simp only [
    InteractionControlPreservation.OpenOutcome.pushStopJump,
    Bool.or_eq_true_iff] at hStopped
  rcases hStopped with hOuter | hLocal
  · apply hBoundary.fresh scope tag target hScope
    · rcases hBoundaryRegular with hOld | hCurrent
      · exact hOld.generated_ne hScope
      · rw [hCurrent, ← hRegular]
        exact hNe
    · exact hOuter
  · have hFull :
        TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
          ctx (.named "") supply :=
      hBefore.with_regular (by trivial)
    have hLocalFalse :
        InteractionControlPreservation.OpenOutcome.stopJump
            result ctx regular returns tokens
            (.generated scope tag) target =
          false :=
      InteractionControlPreservation.OpenOutcome.stopJump_generated_eq_false_of_regular_ne
        hFull hNe hScope returns tokens target
    rw [hLocalFalse] at hLocal
    cases hLocal

theorem push
    {cfg : TypedCfg.Program}
    {returns : List ReturnDest} {tokens : List Word}
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular regular : Assembly.Label}
    {supply : LabelSupply}
    (hBoundary :
      StopPolicy.RecursiveBoundary
        cfg returns tokens outer supply boundaryRegular)
    (hShapes : BoundaryShapes cfg result ctx regular)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx boundaryRegular supply) :
    StopPolicy.RecursiveBoundary cfg returns tokens
      (InteractionControlPreservation.OpenOutcome.pushStopJump
        result ctx regular returns tokens outer)
      supply regular :=
  ⟨hBoundary.ownership.push hShapes,
    hBoundary.fresh.push hBefore⟩

theorem push_child
    {cfg : TypedCfg.Program}
    {ancestorReturns childReturns : List ReturnDest}
    {ancestorTokens childTokens : List Word}
    {outer : StopPolicy}
    {result : TypedCfgCompiler.Result}
    {ctx : TypedCfgCompiler.Context}
    {boundaryRegular regular : Assembly.Label}
    {parentSupply childSupply : LabelSupply}
    (hBoundary :
      StopPolicy.RecursiveBoundary
        cfg ancestorReturns ancestorTokens outer
          parentSupply boundaryRegular)
    (hExtension :
      TypedCfgPreservation.ActivationExtension
        ancestorReturns ancestorTokens childReturns childTokens)
    (hShapes : BoundaryShapes cfg result ctx regular)
    (hBefore :
      TypedCfgCompilerFacts.ContinuationLabelsBeforeSupply
        ctx regular childSupply) :
    StopPolicy.RecursiveBoundary cfg childReturns childTokens
      (InteractionControlPreservation.OpenOutcome.pushStopJump
        result ctx regular childReturns childTokens outer)
      childSupply regular :=
  ⟨(hBoundary.ownership.extend hExtension).push hShapes,
    StopPolicy.ActivationFreshExcept.push_child
      hBoundary.ownership hExtension hBefore⟩

theorem eq_false_of_stateRel
    {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {policy : StopPolicy}
    {supply scope tag : LabelSupply} {regular : Assembly.Label}
    {shape : TypedCfg.Shape} {target : EVMState}
    (hBoundary :
      StopPolicy.RecursiveBoundary
        cfg source.returns tokens policy supply regular)
    (hScope : supply ≤ scope)
    (hNe : .generated scope tag ≠ regular)
    (hShape :
      TypedCfgPreservation.LabelShape
        cfg (.generated scope tag) shape)
    (hActivation :
      TypedCfgPreservation.ActivationInput tokens shape)
    (hRel : TypedCfgPreservation.StateRel source tokens target)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits
        shape source.evm.stack.length) :
    policy (.generated scope tag) target = false :=
  hBoundary.fresh.eq_false_of_stateRel
    hScope hNe hShape hActivation hRel hFits

end StopPolicy.RecursiveBoundary

end OpenOutcome

end InteractionBoundaryPreservation
end Structured
end EvmCompiler
