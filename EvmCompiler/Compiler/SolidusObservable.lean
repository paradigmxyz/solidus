import EvmCompiler.Solidus.Defs
import EvmCompiler.Solidity.RawAstSourcePreservation

/-!
# Bridging `RawSourceBytecodePrefixDoneRel` to the Solidus spec vocabulary

This file discharges the single relational obligation consumed by the public
correctness theorem (`EvmCompiler/Correctness.lean`): every finished
raw-source / open-bytecode pair related by the composed compiler relation
`RawSourceBytecodePrefixDoneRel` is observable through the frozen
`Solidus.ObservableDoneRel`.

The proof unpacks the composed relation into its adjacent-pass witnesses and
threads the source shape (`error` / regular / explicit halt / revert) forward.
Every intermediate EVM-side pass preserves the shared state up to
`Assembly.SameRuntimeData` (equal except for the compiler-owned `pc` /
`execLength`), so the whole observable machine record is transported by
equality; only the initial Yul-to-Functions pass performs the genuine
`SharedState .Yul → SharedState .EVM` translation packaged as
`FunctionsInteractionRelation.SharedRel` / `TerminalSharedRel`.
-/

namespace EvmCompiler
namespace Solidus

open Assembly (SameRuntimeData)

/-- `HaltKind.output` depends only on the observable machine record, so it is
invariant under `SameRuntimeData`. -/
private theorem haltKind_output_congr {kind : Assembly.HaltKind}
    {left right : Assembly.EVMState}
    (hRel : SameRuntimeData left right) :
    kind.output left = kind.output right := by
  have hShared : left.toSharedState = right.toSharedState :=
    SameRuntimeData.shared_eq hRel
  cases kind <;>
    simp [Assembly.HaltKind.output, hShared]

/-- From the Yul→Functions terminal shared relation and an equality pinning an
EVM state's shared record to the related target, reconstruct `FinalStateObs`. -/
private theorem finalStateObs_of_terminalSharedRel
    {shared : EvmYul.SharedState .Yul} {w : EvmYul.SharedState .EVM}
    {target : Assembly.EVMState}
    (hRel : Yul.FunctionsInteractionRelation.TerminalSharedRel shared w)
    (hEq : target.toSharedState = w) :
    FinalStateObs shared target where
  world := by rw [hEq]; exact hRel.openWorld
  gasAvailable := by rw [hEq]; exact hRel.machine.gasAvailable
  activeWords := by rw [hEq]; exact hRel.machine.activeWords
  memory := by rw [hEq]; exact hRel.machine.memory
  returnBuffer := by rw [hEq]; exact hRel.machine.output

/-- Shared EVM-side tail (passes F4/F5): a source-safe TypedCfg halt is realised
as a bytecode-level halted result whose observable machine record is
`SameRuntimeData` to the (safe) terminal step of the CFG halt state, and whose
output already satisfies the STOP/RETURN output convention. -/
private theorem evmHaltTail
    {assembly : Assembly.Program} {kind : Assembly.HaltKind}
    {cfgState : Assembly.EVMState}
    {assemblyDone targetDone : Assembly.Source.ExecutionOutcome}
    (hSafe : Assembly.InteractionSemantics.Terminal.SafeAt kind cfgState)
    (hRun :
      TypedCfg.InteractionPreservation.OpenOutcome.Simulates
        assembly (.halt kind cfgState) assemblyDone)
    (hCompact : Assembly.Compact.RuntimeOutcomeRel targetDone assemblyDone) :
    ∃ (hlt : Assembly.Halt) (cfgFinal : Assembly.EVMState),
      targetDone = .ok (.halted hlt) ∧
        hlt.kind = kind ∧
        Assembly.Target.stepInstr (.prim kind.toPrimOp) cfgState = .ok cfgFinal ∧
        SameRuntimeData hlt.state cfgFinal ∧
        hlt.output = kind.output hlt.state := by
  simp only
    [TypedCfg.InteractionPreservation.OpenOutcome.Simulates] at hRun
  obtain ⟨simulated, hSameSim, hAsm⟩ := hRun
  obtain ⟨simFinal, hSimStep⟩ :=
    Assembly.InteractionSemantics.Terminal.SafeAt.of_sameRuntimeData
      hSameSim hSafe
  obtain ⟨cfgFinal, hCfgStep⟩ := hSafe
  have hKind : (Assembly.TargetInstr.prim kind.toPrimOp).haltKind? = some kind := by
    cases kind <;> rfl
  have hAsm' : assemblyDone =
      .ok (.halted { kind := kind, state := simFinal,
                      output := kind.output simFinal }) := by
    rw [hAsm]
    unfold Assembly.Target.stepInstrResult
    rw [hSimStep, hKind]
    rfl
  have hCongr :=
    Assembly.PrimOp.terminal_step_map_eraseRuntimeControl kind hSameSim
  have hSimStep' : kind.toPrimOp.step simulated = .ok simFinal := hSimStep
  have hCfgStep' : kind.toPrimOp.step cfgState = .ok cfgFinal := hCfgStep
  rw [hSimStep', hCfgStep'] at hCongr
  simp only [Except.map] at hCongr
  have hSameFinals : SameRuntimeData simFinal cfgFinal := Except.ok.inj hCongr
  rw [hAsm'] at hCompact
  obtain ⟨tr, htd, hRes⟩ :
      ∃ tr, targetDone = .ok tr ∧
        Assembly.Compact.StepResultRuntimeRel tr
          (.halted { kind := kind, state := simFinal,
                      output := kind.output simFinal }) := by
    cases hCompact with
    | ok hRes => exact ⟨_, rfl, hRes⟩
  cases tr with
  | running _ => exact hRes.elim
  | halted hlt =>
      simp only [Assembly.Compact.StepResultRuntimeRel] at hRes
      obtain ⟨hKindEq, hSameState, hOutEq⟩ := hRes
      refine ⟨hlt, cfgFinal, htd, hKindEq, hCfgStep, ?_, ?_⟩
      · exact SameRuntimeData.trans hSameState hSameFinals
      · rw [hOutEq]
        exact (haltKind_output_congr hSameState).symm

/-- Threading for an explicit source halt/revert: the middle Functions halt
outcome relates to a bytecode-level halted result whose shared record is the
(post-terminal) Functions halt shared state, with the output convention. -/
private theorem terminalTail
    {program : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {generated : Structured.TypedCfgPreservation.Program.GeneratedContext
      program entryShapes cfg}
    {assembly : Assembly.Program}
    {kind : Assembly.HaltKind}
    {tgt : Locals.Source.State}
    {structuredDone : Except Expressions.EVMException
      Expressions.InteractionSemantics.Outcome}
    {cfgDone : Except TypedCfg.EVMException TypedCfg.Outcome}
    {assemblyDone targetDone : Assembly.Source.ExecutionOutcome}
    (hControl :
      Functions.StackStatementPreservation.ControlScopedOutcomeRel
        {} [] Locals.Ctx.initial [] [] Functions.Source.Ctx.initial
        (.ok (Functions.Source.Effectful.Outcome.halt kind tgt)) structuredDone)
    (hPrefix :
      Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel
        generated structuredDone cfgDone)
    (hRun :
      TypedCfg.InteractionPreservation.OpenBlock.RunSimulates
        assembly cfgDone assemblyDone)
    (hCompact : Assembly.Compact.RuntimeOutcomeRel targetDone assemblyDone) :
    ∃ hlt : Assembly.Halt,
      targetDone = .ok (.halted hlt) ∧ hlt.kind = kind ∧
        hlt.state.toSharedState = tgt.shared ∧
        hlt.output = hlt.kind.output hlt.state := by
  have hTS := Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel.targetSafe
    hPrefix
  simp only
    [Functions.StackStatementPreservation.ControlScopedOutcomeRel] at hControl
  cases hControl with
  | ok hRes =>
      cases hRes with
      | halt hSharedEq =>
          -- hSharedEq : tgt.shared = (structured target).evm.toSharedState
          simp only
            [Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel]
            at hPrefix
          cases hPrefix with
          | @ok _ cfgOutcome hPre =>
              cases cfgOutcome with
              | fallthrough _ => exact hPre.elim
              | jump _ _ => exact hPre.elim
              | returnDispatch _ => exact hPre.elim
              | invalid _ => exact hPre.elim
              | halt cfgKind cfgState =>
                  obtain ⟨hOutcomeRel, _hFits, _hRestored⟩ := hPre
                  obtain ⟨tgtEVM, targetFinal, hEq, hStep, hHaltState⟩ :=
                    Structured.TypedCfgPreservation.OutcomeSimulation.Rel.halt_elim
                      hOutcomeRel
                  cases hEq
                  have hSafe :
                      Assembly.InteractionSemantics.Terminal.SafeAt kind cfgState := by
                    simpa
                      [TypedCfg.InteractionSemantics.Program.PrefixAssemblySafe]
                      using hTS
                  simp only
                    [TypedCfg.InteractionPreservation.OpenBlock.RunSimulates] at hRun
                  obtain ⟨hlt, cfgFinal, hTarget, hKindEq, hCfgStep,
                      hSameState, hOut⟩ :=
                    evmHaltTail hSafe hRun hCompact
                  -- `cfgFinal = targetFinal`: both are the terminal step of `cfgState`.
                  have hStep' :
                      Assembly.Target.stepInstr (.prim kind.toPrimOp) cfgState
                        = .ok targetFinal := hStep
                  have hcf : cfgFinal = targetFinal := by
                    rw [hCfgStep] at hStep'; exact Except.ok.inj hStep'
                  -- targetFinal.toSharedState = (structured target).evm.toSharedState
                  obtain ⟨tokens, stack, _hReal, hSame2⟩ := hHaltState
                  refine ⟨hlt, hTarget, hKindEq, ?_, ?_⟩
                  · rw [SameRuntimeData.shared_eq hSameState, hcf,
                      SameRuntimeData.shared_eq hSame2]
                    exact hSharedEq.symm
                  · rw [hKindEq]; exact hOut

end Solidus
end EvmCompiler

namespace EvmCompiler
namespace Solidity.Raw.SourcePreservation.RawSourceBytecodePrefixDoneRel

open Solidus (ObservableDoneRel FinalStateObs)
open Assembly (SameRuntimeData)

/-- **Main bridge.** Every finished raw-source / open-bytecode pair related by
the composed compiler relation is observable through `ObservableDoneRel`. -/
theorem observable
    {artifact : Solidity.Frontend.Program.Artifact}
    {sourceDone : Except Yul.InteractionSemantics.Failure
      Yul.InteractionSemantics.State}
    {targetDone : Assembly.Source.ExecutionOutcome}
    (h : EvmCompiler.Solidity.RawAst.Raw.SourcePreservation.RawSourceBytecodePrefixDoneRel
      artifact sourceDone targetDone) :
    Solidus.ObservableDoneRel sourceDone targetDone := by
  obtain ⟨ordered, hSame, hVerified⟩ := h
  have hSameEq : sourceDone = ordered := hSame
  subst hSameEq
  obtain ⟨generated, hCompact⟩ := hVerified
  obtain ⟨assemblyDone, hAssembly, hCompactRel⟩ := hCompact
  obtain ⟨cfgDone, hCfg, hRun⟩ := hAssembly
  obtain ⟨structuredDone, hExpr, hPrefix⟩ := hCfg
  obtain ⟨middle, hDone, hControl⟩ := hExpr
  obtain ⟨used, hC⟩ := hDone
  cases hC with
  | @error sourceFailure functionsError hErr =>
      simp only
        [Functions.StackStatementPreservation.ControlScopedOutcomeRel] at hControl
      cases hControl with
      | @error _ structError hStruct =>
          simp only
            [Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel]
            at hPrefix
          cases hPrefix with
          | @error _ cfgError hCfgErr =>
              simp only
                [TypedCfg.InteractionPreservation.OpenBlock.RunSimulates] at hRun
              subst hRun
              cases hCompactRel with
              | @error targetError _ hEq =>
                  refine ObservableDoneRel.error ?_ ?_
                  · -- The error channel forwards only the five non-halt
                    -- exceptions: each surviving `ErrorRel` case is one of them.
                    rcases sourceFailure with ⟨exception, state⟩
                    cases exception <;>
                      simp [Yul.FunctionsInteractionPrimitive.ErrorRel,
                        Solidus.ForwardedException] at hErr ⊢
                  intro hOOF
                  have hCfgOOF : cfgError = .OutOfFuel := by
                    have hTE : targetError = cfgError := hEq
                    rw [← hTE]; exact hOOF
                  have hStructOOF : structError = .OutOfFuel := hCfgErr hCfgOOF
                  have hFnOOF : functionsError = .OutOfFuel := hStruct hStructOOF
                  subst hFnOOF
                  rcases sourceFailure with ⟨exception, state⟩
                  cases exception <;>
                    simp [Yul.FunctionsInteractionPrimitive.ErrorRel] at hErr ⊢
  | @regular fnSource fnTarget hScoped hDomain =>
      obtain ⟨shared, vars, hSourceEq, hSharedRel, _hVarsRel⟩ := hScoped.state
      subst hSourceEq
      simp only
        [Functions.StackStatementPreservation.ControlScopedOutcomeRel] at hControl
      cases hControl with
      | ok hRes =>
          cases hRes with
          | regular _hCovers hLocalState =>
              -- `hLocalState.shared : (structured target).evm.toSharedState = fnTarget.shared`
              have hTS := Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel.targetSafe
                hPrefix
              simp only
                [Structured.InteractionTruncationOwnerPreservation.OpenOutcome.GeneratedProgram.PrefixDoneRel]
                at hPrefix
              cases hPrefix with
              | @ok _ cfgOutcome hPre =>
                  cases cfgOutcome with
                  | fallthrough _ => exact hPre.elim
                  | jump _ _ => exact hPre.elim
                  | returnDispatch _ => exact hPre.elim
                  | invalid _ => exact hPre.elim
                  | halt cfgKind cfgState =>
                      cases cfgKind with
                      | «return» => exact hPre.elim
                      | revert => exact hPre.elim
                      | selfdestruct => exact hPre.elim
                      | stop =>
                          obtain ⟨hCfgStateRel, _hFits, _hRestored⟩ := hPre
                          have hSafe :
                              Assembly.InteractionSemantics.Terminal.SafeAt
                                .stop cfgState := by
                            simpa
                              [TypedCfg.InteractionSemantics.Program.PrefixAssemblySafe]
                              using hTS
                          simp only
                            [TypedCfg.InteractionPreservation.OpenBlock.RunSimulates]
                            at hRun
                          obtain ⟨hlt, cfgFinal, hTarget, hKindEq, hCfgStep,
                              hSameState, hOut⟩ :=
                            Solidus.evmHaltTail hSafe hRun hCompactRel
                          -- Pin the CFG halt state's shared record back to the Yul source.
                          have hCfgShared :
                              cfgState.toSharedState = fnTarget.shared := by
                            obtain ⟨stack, _hReal, hSame⟩ := hCfgStateRel
                            rw [SameRuntimeData.shared_eq hSame]
                            exact hLocalState.shared
                          subst hTarget
                          -- `cfgFinal = evmStop cfgState` clears only returnData / H_return.
                          have hStopStep :
                              Assembly.PrimOp.stop.step cfgState = .ok cfgFinal :=
                            hCfgStep
                          have hcfgFinal :
                              cfgFinal =
                                { cfgState with
                                    toMachineState :=
                                      (cfgState.toMachineState.setReturnData
                                        ByteArray.empty).setHReturn
                                        ByteArray.empty } :=
                            Except.ok.inj (hStopStep.symm.trans rfl)
                          have hFinalShared :
                              hlt.state.toSharedState =
                                { fnTarget.shared with
                                    returnData := ByteArray.empty
                                    H_return := ByteArray.empty } := by
                            rw [SameRuntimeData.shared_eq hSameState, hcfgFinal,
                              ← hCfgShared]
                            rfl
                          -- STOP-cleared source shared relates terminally.
                          have hObs0 :
                              FinalStateObs
                                { shared with H_return := ByteArray.empty }
                                hlt.state :=
                            Solidus.finalStateObs_of_terminalSharedRel
                              (Yul.FunctionsInteractionRelation.TerminalSharedRel.stop
                                hSharedRel)
                              hFinalShared
                          -- The spec's regular constructor compares against the
                          -- source shared state with its stale pre-STOP return
                          -- buffer scratch cleared — exactly `hObs0`.
                          exact ObservableDoneRel.regular hKindEq hObs0
                            (by rw [hKindEq]; exact hOut)
  | @brk _ _ scope hScope _ _ =>
      exact absurd hScope (by simp)
  | @cont _ _ scope hScope _ _ =>
      exact absurd hScope (by simp)
  | @leave _ _ scope hScope _ _ =>
      exact absurd hScope (by simp)
  | @terminal sourceFailure functionsOutcome hTerm =>
      cases hTerm with
      | @stop src value tgt hState =>
          obtain ⟨ss, vs, hSrcEq, hTermShared, _hVars⟩ := hState
          subst hSrcEq
          obtain ⟨hlt, hTarget, hKindEq, hSharedEq2, hOut⟩ :=
            Solidus.terminalTail hControl hPrefix hRun hCompactRel
          subst hTarget
          exact ObservableDoneRel.halt (Or.inl hKindEq)
            (Solidus.finalStateObs_of_terminalSharedRel hTermShared hSharedEq2)
            hOut
      | @return_ src value tgt hState =>
          obtain ⟨ss, vs, hSrcEq, hTermShared, _hVars⟩ := hState
          subst hSrcEq
          obtain ⟨hlt, hTarget, hKindEq, hSharedEq2, hOut⟩ :=
            Solidus.terminalTail hControl hPrefix hRun hCompactRel
          subst hTarget
          exact ObservableDoneRel.halt (Or.inr (Or.inl hKindEq))
            (Solidus.finalStateObs_of_terminalSharedRel hTermShared hSharedEq2)
            hOut
      | @selfdestruct src value tgt hState =>
          obtain ⟨ss, vs, hSrcEq, hTermShared, _hVars⟩ := hState
          subst hSrcEq
          obtain ⟨hlt, hTarget, hKindEq, hSharedEq2, hOut⟩ :=
            Solidus.terminalTail hControl hPrefix hRun hCompactRel
          subst hTarget
          exact ObservableDoneRel.halt (Or.inr (Or.inr hKindEq))
            (Solidus.finalStateObs_of_terminalSharedRel hTermShared hSharedEq2)
            hOut
      | @revert src tgt hState =>
          obtain ⟨ss, vs, hSrcEq, hTermShared, _hVars⟩ := hState
          subst hSrcEq
          obtain ⟨hlt, hTarget, hKindEq, hSharedEq2, hOut⟩ :=
            Solidus.terminalTail hControl hPrefix hRun hCompactRel
          subst hTarget
          exact ObservableDoneRel.revert hKindEq
            (Solidus.finalStateObs_of_terminalSharedRel hTermShared hSharedEq2)
            hOut

end Solidity.Raw.SourcePreservation.RawSourceBytecodePrefixDoneRel
end EvmCompiler
