import EvmCompiler.Structured.ObserverFrameInvariant

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace OutcomeSimulation

abbrev ActivationExtension :=
  TypedCfgPreservation.ActivationExtension

namespace ActivationExtension

theorem one (returns : List Structured.ReturnDest) (tokens : List Word)
    (frame : Structured.ReturnDest) (token : Word) :
    ActivationExtension returns tokens
      (frame :: returns) (token :: tokens) :=
  TypedCfgPreservation.ActivationExtension.one
    returns tokens frame token

theorem trans
    {ancestorReturns : List Structured.ReturnDest}
    {ancestorTokens : List Word}
    {middleReturns : List Structured.ReturnDest}
    {middleTokens : List Word}
    {childReturns : List Structured.ReturnDest}
    {childTokens : List Word}
    (hFirst :
      ActivationExtension ancestorReturns ancestorTokens
        middleReturns middleTokens)
    (hSecond :
      ActivationExtension middleReturns middleTokens
        childReturns childTokens) :
    ActivationExtension ancestorReturns ancestorTokens
      childReturns childTokens :=
  TypedCfgPreservation.ActivationExtension.trans hFirst hSecond

theorem childTokens_ne_nil
    {ancestorReturns childReturns : List Structured.ReturnDest}
    {ancestorTokens childTokens : List Word}
    (hExtension :
      ActivationExtension ancestorReturns ancestorTokens
        childReturns childTokens) :
    childTokens ≠ [] :=
  TypedCfgPreservation.ActivationExtension.childTokens_ne_nil hExtension

theorem realize_length_lt
    {ancestorReturns childReturns : List Structured.ReturnDest}
    {ancestorTokens childTokens : List Word}
    {ancestorHidden childHidden : EvmYul.Stack Word}
    (hExtension :
      ActivationExtension ancestorReturns ancestorTokens
        childReturns childTokens)
    (hAncestor :
      TypedCfgPreservation.realizeStack
          [] ancestorReturns ancestorTokens = some ancestorHidden)
    (hChild :
      TypedCfgPreservation.realizeStack
          [] childReturns childTokens = some childHidden) :
    ancestorHidden.length < childHidden.length :=
  TypedCfgPreservation.ActivationExtension.realize_length_lt
    hExtension hAncestor hChild

end ActivationExtension

/--
A target state belongs to the same dynamic Structured activation as `source`.

Caller shapes do not contain a compiler-owned return token, so global emitted
label uniqueness is sufficient there. Active procedure shapes contain a return
token at an exact source-visible depth; matching the realized hidden-frame
length prevents a recursive activation from being mistaken for its caller at
the same static CFG label.
-/
abbrev FrameMatches {transcript : Trace}
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) (shape : TypedCfg.Shape)
    (target : EVMState) : Prop :=
  TypedCfgPreservation.ActivationFrameMatches
    source.source.returns tokens shape target

/--
Accept a jump to `next` only in the source activation that owns the
continuation. Other outcomes are delegated to the enclosing boundary.
-/
def JumpAt {transcript : Trace}
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) (next : Assembly.Label)
    (shape : TypedCfg.Shape)
    (accept : TypedCfg.Outcome → Prop) :
    TypedCfg.Outcome → Prop
  | outcome@(.jump label target) =>
      (label = next ∧ FrameMatches source tokens shape target) ∨
        accept outcome
  | outcome => accept outcome

namespace FrameMatches

theorem congr_returns
    {transcript : Trace} {shape : TypedCfg.Shape}
    {left right : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState}
    (hReturns : left.source.returns = right.source.returns) :
    FrameMatches left tokens shape target ↔
      FrameMatches right tokens shape target := by
  exact
    TypedCfgPreservation.ActivationFrameMatches.congr_returns hReturns

theorem of_rel
    {transcript : Trace} {shape : TypedCfg.Shape}
    {initial final : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hReturns : final.source.returns = initial.source.returns)
    (hRel : ObserverPreservation.StateRel final tokens target trace)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape
        final.source.evm.stack.length) :
    FrameMatches initial tokens shape target := by
  exact
    (TypedCfgPreservation.ActivationFrameMatches.congr_returns
      hReturns).mp
      (TypedCfgPreservation.ActivationFrameMatches.of_stateRel
        hRel.1 hFits)

theorem of_at
    {transcript : Trace} {shape : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hRel :
      ObserverPreservation.StateRel.At
        shape source tokens target trace) :
    FrameMatches source tokens shape target :=
  of_rel rfl hRel.rel hRel.sourceFrameFits

theorem not_of_pushed_return
    {transcript : Trace} {shape : TypedCfg.Shape}
    {caller child : ObserverSemantics.State transcript}
    {tokens : List Word} {token : Word}
    {frame : Structured.ReturnDest}
    {target : EVMState} {depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hReturns :
      child.source.returns = frame :: caller.source.returns)
    (hCallerHidden :
      ∃ hidden : EvmYul.Stack Word,
        TypedCfgPreservation.realizeStack
            [] caller.source.returns tokens = some hidden)
    (hChild :
      FrameMatches child (token :: tokens) shape target) :
    ¬ FrameMatches caller tokens shape target := by
  have hExtension :
      TypedCfgPreservation.ActivationExtension
        caller.source.returns tokens child.source.returns
          (token :: tokens) := by
    rw [hReturns]
    exact
      TypedCfgPreservation.ActivationExtension.one
        caller.source.returns tokens frame token
  exact
    TypedCfgPreservation.ActivationFrameMatches.not_of_extension
      hDepth hExtension hCallerHidden hChild

theorem not_of_extension
    {transcript : Trace} {shape : TypedCfg.Shape}
    {ancestor child : ObserverSemantics.State transcript}
    {ancestorTokens childTokens : List Word}
    {target : EVMState} {depth : Nat}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hExtension :
      ActivationExtension
        ancestor.source.returns ancestorTokens
        child.source.returns childTokens)
    (hAncestorHidden :
      ∃ hidden : EvmYul.Stack Word,
        TypedCfgPreservation.realizeStack
            [] ancestor.source.returns ancestorTokens = some hidden)
    (hChild :
      FrameMatches child childTokens shape target) :
    ¬ FrameMatches ancestor ancestorTokens shape target :=
  TypedCfgPreservation.ActivationFrameMatches.not_of_extension
    hDepth hExtension hAncestorHidden hChild

end FrameMatches

namespace JumpAt

theorem of_accept
    {transcript : Trace}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {next : Assembly.Label}
    {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop}
    {outcome : TypedCfg.Outcome}
    (hAccept : accept outcome) :
    JumpAt source tokens next shape accept outcome := by
  cases outcome <;> simp [JumpAt, hAccept]

theorem jump
    {transcript : Trace}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {next : Assembly.Label}
    {shape : TypedCfg.Shape}
    {accept : TypedCfg.Outcome → Prop}
    {target : EVMState}
    (hFrame : FrameMatches source tokens shape target) :
    JumpAt source tokens next shape accept (.jump next target) := by
  exact Or.inl ⟨rfl, hFrame⟩

theorem of_rel
    {transcript : Trace} {shape : TypedCfg.Shape}
    {initial final : ObserverSemantics.State transcript}
    {tokens : List Word} {next : Assembly.Label}
    {accept : TypedCfg.Outcome → Prop}
    {target : EVMState} {trace : Trace}
    (hReturns : final.source.returns = initial.source.returns)
    (hRel : ObserverPreservation.StateRel final tokens target trace)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape
        final.source.evm.stack.length) :
    JumpAt initial tokens next shape accept (.jump next target) :=
  jump (FrameMatches.of_rel hReturns hRel hFits)

end JumpAt

end OutcomeSimulation
end ObserverAdequacy
end Structured
end EvmCompiler
