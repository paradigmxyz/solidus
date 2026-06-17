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

end OpenOutcome

end InteractionBoundaryPreservation
end Structured
end EvmCompiler
