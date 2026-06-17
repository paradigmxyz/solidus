import EvmCompiler.Structured.ObserverAdequacyArtifact

namespace EvmCompiler
namespace Structured

namespace ObserverPreservation
namespace StateRel

theorem At.sourceFrameFits
    {transcript : Trace} {shape : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hRel : At shape source tokens target trace) :
    TypedCfgCompiler.Shape.SourceFrameFits shape
      source.source.evm.stack.length :=
  ⟨hRel.sourceStack, hRel.sourceFrame⟩

theorem At.ofFits
    {transcript : Trace} {shape : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hRel : StateRel source tokens target trace)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits shape
        source.source.evm.stack.length) :
    At shape source tokens target trace :=
  ⟨hRel, hFits.1, hFits.2⟩

theorem targetStack_decompose
    {transcript : Trace} {shape : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hRel : At shape source tokens target trace) :
    ∃ hidden : EvmYul.Stack Word,
      TypedCfgPreservation.realizeStack
          [] source.source.returns tokens = some hidden ∧
      target.stack = source.source.evm.stack ++ hidden := by
  rcases hRel.rel.1 with ⟨realized, hRealize, hSame⟩
  have hAppend :=
    TypedCfgPreservation.realizeStack_append_prefix
      source.source.evm.stack [] source.source.returns tokens
  cases hHidden :
      TypedCfgPreservation.realizeStack
        [] source.source.returns tokens with
  | none =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
  | some hidden =>
      simp [hHidden] at hAppend
      rw [hAppend] at hRealize
      cases hRealize
      exact
        ⟨hidden, rfl,
          by simpa using Assembly.SameRuntimeData.stack_eq hSame⟩

theorem targetStack_eq_source_append_hidden
    {transcript : Trace} {shape : TypedCfg.Shape}
    {source : ObserverSemantics.State transcript}
    {tokens : List Word} {target : EVMState} {trace : Trace}
    (hRel : At shape source tokens target trace) :
    ∃ hidden : EvmYul.Stack Word,
      target.stack = source.source.evm.stack ++ hidden := by
  obtain ⟨hidden, _hHidden, hStack⟩ :=
    targetStack_decompose hRel
  exact ⟨hidden, hStack⟩

end StateRel
end ObserverPreservation

namespace ObserverAdequacy
namespace Code

/--
Typed observer execution respects the symbolic stack lower bound.
-/
def ShapeSound (code : Structured.Code) : Prop :=
  ∀ {transcript : Trace} {input output : TypedCfg.Shape}
      {source final : ObserverSemantics.State transcript},
    TypedCfgCompiler.Code.type? code input = some output →
      TypedCfgCompiler.Shape.sourceLength input ≤
        source.source.evm.stack.length →
      ObserverSemantics.Code.run code source = .ok final →
      TypedCfgCompiler.Shape.sourceLength output ≤
        final.source.evm.stack.length

/--
Every straight-line fragment accepted by the existing Structured-to-TypedCfg
body typer is shape-sound under observer replay.
-/
theorem shapeSound (code : Structured.Code) : ShapeSound code := by
  intro transcript input output source final hType hBound hRun
  induction code generalizing input output source final with
  | nil =>
      simp [TypedCfgCompiler.Code.type?,
        TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?,
        ObserverSemantics.Code.run,
        EffectSemantics.Code.run] at hType hRun
      cases hType
      cases hRun
      exact hBound
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
        cases hSafe :
            TypedCfgCompiler.BasicInstr.sourceSafe? instr input middle with
        | false =>
          simp [hHeadType, hSafe] at hType
        | true =>
          have hTailType :
              TypedCfgCompiler.Code.type? rest middle = some output := by
            simpa [hHeadType, hSafe] using hType
          unfold ObserverSemantics.Code.run at hRun
          rw [EffectSemantics.Code.run_cons] at hRun
          simp only [ObserverSemantics.stateModel_evm,
            ObserverSemantics.stateModel_withEVM] at hRun
          cases hStep : instr.step source.source.evm with
          | error err =>
              simp [hStep, Bind.bind, Except.bind] at hRun
          | ok evm =>
              simp only [hStep, Bind.bind, Except.bind] at hRun
              cases hAfter :
                  (ObserverSemantics.handler transcript).afterInstr instr
                    (source.withSource
                      (source.source.withEVM evm)) with
              | error err =>
                  rw [hAfter] at hRun
                  contradiction
              | ok middleState =>
                  rw [hAfter] at hRun
                  have hStepBound :
                      TypedCfgCompiler.Shape.sourceLength middle ≤
                        evm.stack.length :=
                    TypedCfgPreservation.BasicInstr.step_sourceLength_bound_of_type
                      hSafe hBound hStep
                  have hAfterLength :=
                    ObserverSemantics.handler_stack_length hAfter
                  have hMiddleBound :
                      TypedCfgCompiler.Shape.sourceLength middle ≤
                        middleState.source.evm.stack.length := by
                    have hLength :
                        middleState.source.evm.stack.length =
                          evm.stack.length := by
                      simpa [RunState.withEVM] using hAfterLength
                    omega
                  exact ih hTailType hMiddleBound hRun

/--
Typed observer execution preserves the source-frame invariant: caller frames
retain their lower bound and active procedure frames retain their exact
source-visible length.
-/
theorem sourceFrameFits
    (code : Structured.Code)
    {transcript : Trace} {input output : TypedCfg.Shape}
    {source final : ObserverSemantics.State transcript}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hFits :
      TypedCfgCompiler.Shape.SourceFrameFits input
        source.source.evm.stack.length)
    (hRun : ObserverSemantics.Code.run code source = .ok final) :
    TypedCfgCompiler.Shape.SourceFrameFits output
      final.source.evm.stack.length := by
  induction code generalizing input output source final with
  | nil =>
      simp [TypedCfgCompiler.Code.type?,
        TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?,
        ObserverSemantics.Code.run,
        EffectSemantics.Code.run] at hType hRun
      cases hType
      cases hRun
      exact hFits
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
        cases hSafe :
            TypedCfgCompiler.BasicInstr.sourceSafe? instr input middle with
        | false =>
          simp [hHeadType, hSafe] at hType
        | true =>
          have hTailType :
              TypedCfgCompiler.Code.type? rest middle = some output := by
            simpa [hHeadType, hSafe] using hType
          unfold ObserverSemantics.Code.run at hRun
          rw [EffectSemantics.Code.run_cons] at hRun
          simp only [ObserverSemantics.stateModel_evm,
            ObserverSemantics.stateModel_withEVM] at hRun
          cases hStep : instr.step source.source.evm with
          | error err =>
              simp [hStep, Bind.bind, Except.bind] at hRun
          | ok evm =>
              simp only [hStep, Bind.bind, Except.bind] at hRun
              cases hAfter :
                  (ObserverSemantics.handler transcript).afterInstr instr
                    (source.withSource
                      (source.source.withEVM evm)) with
              | error err =>
                  rw [hAfter] at hRun
                  contradiction
              | ok middleState =>
                  rw [hAfter] at hRun
                  have hStepFits :
                      TypedCfgCompiler.Shape.SourceFrameFits middle
                        evm.stack.length :=
                    TypedCfgPreservation.BasicInstr.step_sourceFrameFits_of_type
                      hHeadType hSafe hFits hStep
                  have hAfterLength :=
                    ObserverSemantics.handler_stack_length hAfter
                  have hMiddleFits :
                      TypedCfgCompiler.Shape.SourceFrameFits middle
                        middleState.source.evm.stack.length := by
                    rw [hAfterLength]
                    simpa [RunState.withEVM] using hStepFits
                  exact ih hTailType hMiddleFits hRun

end Code
end ObserverAdequacy
end Structured
end EvmCompiler
