import EvmCompiler.Structured.ObserverFrameInvariant

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace OutcomeSimulation

/--
One or more compiler-managed call frames extending an ancestor activation.
-/
inductive ActivationExtension :
    List Structured.ReturnDest → List Word →
      List Structured.ReturnDest → List Word → Prop where
  | one (returns : List Structured.ReturnDest) (tokens : List Word)
      (frame : Structured.ReturnDest) (token : Word) :
      ActivationExtension returns tokens
        (frame :: returns) (token :: tokens)
  | push
      {returns : List Structured.ReturnDest} {tokens : List Word}
      {currentReturns : List Structured.ReturnDest}
      {currentTokens : List Word}
      (frame : Structured.ReturnDest) (token : Word)
      (hExtension :
        ActivationExtension returns tokens currentReturns currentTokens) :
      ActivationExtension returns tokens
        (frame :: currentReturns) (token :: currentTokens)

namespace ActivationExtension

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
      childReturns childTokens := by
  induction hSecond with
  | one frame token =>
      exact .push frame token hFirst
  | push frame token hExtension ih =>
      exact .push frame token ih

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
    ancestorHidden.length < childHidden.length := by
  induction hExtension generalizing childHidden with
  | one frame token =>
      have hAppend :=
        TypedCfgPreservation.realizeStack_append_prefix
          ([token] ++ frame.callerStack) []
          ancestorReturns ancestorTokens
      rw [hAncestor] at hAppend
      have hExpected :
          TypedCfgPreservation.realizeStack
              [] (frame :: ancestorReturns)
                (token :: ancestorTokens) =
            some ([token] ++ frame.callerStack ++ ancestorHidden) := by
        simp only [TypedCfgPreservation.realizeStack]
        simpa [List.append_assoc] using hAppend
      have hChildEq :
          childHidden =
            [token] ++ frame.callerStack ++ ancestorHidden :=
        Option.some.inj (hChild.symm.trans hExpected)
      subst childHidden
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  | @push currentReturns currentTokens frame token hCurrent ih =>
      cases hMiddle :
          TypedCfgPreservation.realizeStack
            [] currentReturns currentTokens with
      | none =>
          have hAppend :=
            TypedCfgPreservation.realizeStack_append_prefix
              ([token] ++ frame.callerStack) []
              currentReturns currentTokens
          rw [hMiddle] at hAppend
          have hImpossible :
              TypedCfgPreservation.realizeStack
                  [] (frame :: currentReturns)
                    (token :: currentTokens) = none := by
            simp only [TypedCfgPreservation.realizeStack]
            simpa [List.append_assoc] using hAppend
          rw [hImpossible] at hChild
          cases hChild
      | some middleHidden =>
          have hAppend :=
            TypedCfgPreservation.realizeStack_append_prefix
              ([token] ++ frame.callerStack) []
              currentReturns currentTokens
          rw [hMiddle] at hAppend
          have hExpected :
              TypedCfgPreservation.realizeStack
                  [] (frame :: currentReturns)
                    (token :: currentTokens) =
                some
                  ([token] ++ frame.callerStack ++ middleHidden) := by
            simp only [TypedCfgPreservation.realizeStack]
            simpa [List.append_assoc] using hAppend
          have hChildEq :
              childHidden =
                [token] ++ frame.callerStack ++ middleHidden :=
            Option.some.inj (hChild.symm.trans hExpected)
          subst childHidden
          have hAncestorLt :=
            ih hMiddle
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega

end ActivationExtension

/--
A target state belongs to the same dynamic Structured activation as `source`.

Caller shapes do not contain a compiler-owned return token, so global emitted
label uniqueness is sufficient there. Active procedure shapes contain a return
token at an exact source-visible depth; matching the realized hidden-frame
length prevents a recursive activation from being mistaken for its caller at
the same static CFG label.
-/
def FrameMatches {transcript : Trace}
    (source : ObserverSemantics.State transcript)
    (tokens : List Word) (shape : TypedCfg.Shape)
    (target : EVMState) : Prop :=
  match shape.returnTokenDepth? with
  | none => True
  | some depth =>
      ∃ hidden : EvmYul.Stack Word,
        TypedCfgPreservation.realizeStack
            [] source.source.returns tokens = some hidden ∧
          target.stack.length = depth + hidden.length

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
  unfold FrameMatches
  cases hDepth : shape.returnTokenDepth? with
  | none =>
      trivial
  | some depth =>
      let hAt :
          ObserverPreservation.StateRel.At
            shape final tokens target trace :=
        ObserverPreservation.StateRel.At.ofFits hRel hFits
      obtain ⟨hidden, hHidden, hStack⟩ :=
        ObserverPreservation.StateRel.targetStack_decompose hAt
      refine ⟨hidden, ?_, ?_⟩
      · simpa [hReturns] using hHidden
      · have hSourceLength :
            final.source.evm.stack.length = depth :=
          hFits.2 depth hDepth
        rw [hStack, List.length_append, hSourceLength]

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
  rcases hCallerHidden with ⟨callerHidden, hCallerHidden⟩
  unfold FrameMatches at hChild ⊢
  rw [hDepth] at hChild ⊢
  rcases hChild with ⟨childHidden, hChildHidden, hChildLength⟩
  intro hCaller
  rcases hCaller with
    ⟨callerHidden', hCallerHidden', hCallerLength⟩
  have hCallerHiddenEq : callerHidden' = callerHidden := by
    exact Option.some.inj (hCallerHidden'.symm.trans hCallerHidden)
  subst callerHidden'
  have hExpected :
      TypedCfgPreservation.realizeStack
          [] child.source.returns (token :: tokens) =
        some ([token] ++ frame.callerStack ++ callerHidden) := by
    rw [hReturns]
    simp only [TypedCfgPreservation.realizeStack]
    have hAppend :=
      TypedCfgPreservation.realizeStack_append_prefix
        ([token] ++ frame.callerStack) []
        caller.source.returns tokens
    rw [hCallerHidden] at hAppend
    simpa [List.append_assoc] using hAppend
  have hChildHiddenEq :
      childHidden = [token] ++ frame.callerStack ++ callerHidden := by
    exact Option.some.inj (hChildHidden.symm.trans hExpected)
  subst childHidden
  simp only [List.length_append, List.length_cons, List.length_nil] at hChildLength
  omega

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
    ¬ FrameMatches ancestor ancestorTokens shape target := by
  rcases hAncestorHidden with
    ⟨ancestorHidden, hAncestorHidden⟩
  unfold FrameMatches at hChild ⊢
  rw [hDepth] at hChild ⊢
  rcases hChild with ⟨childHidden, hChildHidden, hChildLength⟩
  intro hAncestor
  rcases hAncestor with
    ⟨ancestorHidden', hAncestorHidden', hAncestorLength⟩
  have hAncestorEq : ancestorHidden' = ancestorHidden :=
    Option.some.inj (hAncestorHidden'.symm.trans hAncestorHidden)
  subst ancestorHidden'
  have hLengthLt :=
    ActivationExtension.realize_length_lt
      hExtension hAncestorHidden hChildHidden
  omega

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
