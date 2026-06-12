import EvmCompiler.Structured.ObserverFrameInvariant

namespace EvmCompiler
namespace Structured
namespace ObserverAdequacy
namespace OutcomeSimulation

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
