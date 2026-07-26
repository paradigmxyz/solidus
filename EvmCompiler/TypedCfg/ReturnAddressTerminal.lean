import EvmCompiler.TypedCfg.ReturnAddressPreservation

namespace EvmCompiler
namespace TypedCfg
namespace ReturnAddressPreservation

theorem haltStep_shared_of_prefix
    {target source : Assembly.EVMState}
    {kind : Assembly.HaltKind}
    (hShared : target.toSharedState = source.toSharedState)
    (hBound : kind.argCount ≤ target.stack.length)
    (hTop :
      target.stack.take kind.argCount =
        source.stack.take kind.argCount)
    (hSafe :
      Assembly.InteractionSemantics.Terminal.SafeAt kind source) :
    ∃ targetFinal sourceFinal,
      Assembly.Target.stepInstr (.prim kind.toPrimOp) target =
          .ok targetFinal ∧
        Assembly.Target.stepInstr (.prim kind.toPrimOp) source =
          .ok sourceFinal ∧
        targetFinal.toSharedState = sourceFinal.toSharedState := by
  cases kind with
  | stop =>
      rcases hSafe with ⟨sourceFinal, hSource⟩
      cases target with
      | mk targetShared targetPc targetStack targetExec =>
          cases source with
          | mk sourceShared sourcePc sourceStack sourceExec =>
              simp only at hShared
              subst sourceShared
              cases hSource
              exact ⟨_, _, rfl, rfl, rfl⟩
  | «return» =>
      cases target with
      | mk targetShared targetPc targetStack targetExec =>
          cases source with
          | mk sourceShared sourcePc sourceStack sourceExec =>
              simp only [Assembly.HaltKind.argCount] at hBound hTop
              simp only at hShared
              subst sourceShared
              cases targetStack with
              | nil => simp at hBound
              | cons targetA targetRest =>
                  cases targetRest with
                  | nil => simp at hBound
                  | cons targetB targetTail =>
                      cases sourceStack with
                      | nil => simp at hTop
                      | cons sourceA sourceRest =>
                          cases sourceRest with
                          | nil => simp at hTop
                          | cons sourceB sourceTail =>
                              simp only [List.take, List.cons.injEq] at hTop
                              rcases hTop with ⟨rfl, rfl, _⟩
                              cases hTargetRun :
                                  Assembly.Target.stepInstr
                                    (.prim
                                      Assembly.HaltKind.return.toPrimOp)
                                    { toSharedState := targetShared,
                                      pc := targetPc,
                                      stack :=
                                        targetA :: targetB :: targetTail,
                                      execLength := targetExec } with
                              | error error =>
                                  change
                                    EvmYul.EVM.binaryMachineStateOp
                                        EvmYul.MachineState.evmReturn
                                        { toSharedState := targetShared,
                                          pc := targetPc,
                                          stack :=
                                            targetA :: targetB :: targetTail,
                                          execLength := targetExec } =
                                      .error error at hTargetRun
                                  simp [EvmYul.EVM.binaryMachineStateOp,
                                    EvmYul.Stack.pop2,
                                    Assembly.PrimStep.idRun_eq]
                                    at hTargetRun
                              | ok targetFinal =>
                                  cases hSourceRun :
                                      Assembly.Target.stepInstr
                                        (.prim
                                          Assembly.HaltKind.return.toPrimOp)
                                        { toSharedState := targetShared,
                                          pc := sourcePc,
                                          stack :=
                                            targetA :: targetB :: sourceTail,
                                          execLength := sourceExec } with
                                  | error error =>
                                      change
                                        EvmYul.EVM.binaryMachineStateOp
                                            EvmYul.MachineState.evmReturn
                                            { toSharedState := targetShared,
                                              pc := sourcePc,
                                              stack :=
                                                targetA :: targetB ::
                                                  sourceTail,
                                              execLength := sourceExec } =
                                          .error error at hSourceRun
                                      simp [EvmYul.EVM.binaryMachineStateOp,
                                        EvmYul.Stack.pop2,
                                        Assembly.PrimStep.idRun_eq]
                                        at hSourceRun
                                  | ok sourceFinal =>
                                      refine
                                        ⟨targetFinal, sourceFinal,
                                          rfl, rfl, ?_⟩
                                      change
                                        EvmYul.EVM.binaryMachineStateOp
                                            EvmYul.MachineState.evmReturn
                                            { toSharedState := targetShared,
                                              pc := targetPc,
                                              stack :=
                                                targetA :: targetB ::
                                                  targetTail,
                                              execLength := targetExec } =
                                          .ok targetFinal at hTargetRun
                                      change
                                        EvmYul.EVM.binaryMachineStateOp
                                            EvmYul.MachineState.evmReturn
                                            { toSharedState := targetShared,
                                              pc := sourcePc,
                                              stack :=
                                                targetA :: targetB ::
                                                  sourceTail,
                                              execLength := sourceExec } =
                                          .ok sourceFinal at hSourceRun
                                      simp [EvmYul.EVM.binaryMachineStateOp,
                                        EvmYul.Stack.pop2,
                                        Assembly.PrimStep.idRun_eq]
                                        at hTargetRun hSourceRun
                                      subst targetFinal
                                      subst sourceFinal
                                      rfl
  | revert =>
      cases target with
      | mk targetShared targetPc targetStack targetExec =>
          cases source with
          | mk sourceShared sourcePc sourceStack sourceExec =>
              simp only [Assembly.HaltKind.argCount] at hBound hTop
              simp only at hShared
              subst sourceShared
              cases targetStack with
              | nil => simp at hBound
              | cons targetA targetRest =>
                  cases targetRest with
                  | nil => simp at hBound
                  | cons targetB targetTail =>
                      cases sourceStack with
                      | nil => simp at hTop
                      | cons sourceA sourceRest =>
                          cases sourceRest with
                          | nil => simp at hTop
                          | cons sourceB sourceTail =>
                              simp only [List.take, List.cons.injEq] at hTop
                              rcases hTop with ⟨rfl, rfl, _⟩
                              cases hTargetRun :
                                  Assembly.Target.stepInstr
                                    (.prim
                                      Assembly.HaltKind.revert.toPrimOp)
                                    { toSharedState := targetShared,
                                      pc := targetPc,
                                      stack :=
                                        targetA :: targetB :: targetTail,
                                      execLength := targetExec } with
                              | error error =>
                                  change
                                    EvmYul.EVM.binaryMachineStateOp
                                        EvmYul.MachineState.evmRevert
                                        { toSharedState := targetShared,
                                          pc := targetPc,
                                          stack :=
                                            targetA :: targetB :: targetTail,
                                          execLength := targetExec } =
                                      .error error at hTargetRun
                                  simp [EvmYul.EVM.binaryMachineStateOp,
                                    EvmYul.Stack.pop2,
                                    Assembly.PrimStep.idRun_eq]
                                    at hTargetRun
                              | ok targetFinal =>
                                  cases hSourceRun :
                                      Assembly.Target.stepInstr
                                        (.prim
                                          Assembly.HaltKind.revert.toPrimOp)
                                        { toSharedState := targetShared,
                                          pc := sourcePc,
                                          stack :=
                                            targetA :: targetB :: sourceTail,
                                          execLength := sourceExec } with
                                  | error error =>
                                      change
                                        EvmYul.EVM.binaryMachineStateOp
                                            EvmYul.MachineState.evmRevert
                                            { toSharedState := targetShared,
                                              pc := sourcePc,
                                              stack :=
                                                targetA :: targetB ::
                                                  sourceTail,
                                              execLength := sourceExec } =
                                          .error error at hSourceRun
                                      simp [EvmYul.EVM.binaryMachineStateOp,
                                        EvmYul.Stack.pop2,
                                        Assembly.PrimStep.idRun_eq]
                                        at hSourceRun
                                  | ok sourceFinal =>
                                      refine
                                        ⟨targetFinal, sourceFinal,
                                          rfl, rfl, ?_⟩
                                      change
                                        EvmYul.EVM.binaryMachineStateOp
                                            EvmYul.MachineState.evmRevert
                                            { toSharedState := targetShared,
                                              pc := targetPc,
                                              stack :=
                                                targetA :: targetB ::
                                                  targetTail,
                                              execLength := targetExec } =
                                          .ok targetFinal at hTargetRun
                                      change
                                        EvmYul.EVM.binaryMachineStateOp
                                            EvmYul.MachineState.evmRevert
                                            { toSharedState := targetShared,
                                              pc := sourcePc,
                                              stack :=
                                                targetA :: targetB ::
                                                  sourceTail,
                                              execLength := sourceExec } =
                                          .ok sourceFinal at hSourceRun
                                      simp [EvmYul.EVM.binaryMachineStateOp,
                                        EvmYul.Stack.pop2,
                                        Assembly.PrimStep.idRun_eq]
                                        at hTargetRun hSourceRun
                                      subst targetFinal
                                      subst sourceFinal
                                      rfl
  | selfdestruct =>
      cases target with
      | mk targetShared targetPc targetStack targetExec =>
          cases source with
          | mk sourceShared sourcePc sourceStack sourceExec =>
              simp only [Assembly.HaltKind.argCount] at hBound hTop
              simp only at hShared
              subst sourceShared
              cases targetStack with
              | nil => simp at hBound
              | cons targetA targetTail =>
                  cases sourceStack with
                  | nil => simp at hTop
                  | cons sourceA sourceTail =>
                      simp only [List.take, List.cons.injEq] at hTop
                      rcases hTop with ⟨rfl, _⟩
                      rcases hSafe with ⟨sourceFinal, hSource⟩
                      cases hPermission : targetShared.executionEnv.perm
                      · simp [Assembly.HaltKind.toPrimOp,
                          Assembly.PrimOp.step_selfdestruct_of_static,
                          hPermission] at hSource
                      · let targetInitial : Assembly.EVMState :=
                          { toSharedState := targetShared,
                            pc := targetPc,
                            stack := targetA :: targetTail,
                            execLength := targetExec }
                        let sourceInitial : Assembly.EVMState :=
                          { toSharedState := targetShared,
                            pc := sourcePc,
                            stack := targetA :: sourceTail,
                            execLength := sourceExec }
                        let targetExpected :=
                          EvmYul.EVM.selfdestructState
                            targetInitial targetA targetTail
                        let sourceExpected :=
                          EvmYul.EVM.selfdestructState
                            sourceInitial targetA sourceTail
                        have hTargetStep :
                            Assembly.Target.stepInstr
                                (.prim
                                  Assembly.HaltKind.selfdestruct.toPrimOp)
                                targetInitial =
                              .ok targetExpected := by
                          change
                            Assembly.PrimOp.selfdestruct.step targetInitial =
                              .ok targetExpected
                          rw [
                            Assembly.PrimOp.step_selfdestruct_of_permitted _
                              hPermission]
                          exact EvmYul.EVM.step_selfdestruct_of_stack
                            _ targetA targetTail rfl
                        have hSourceStep :
                            Assembly.Target.stepInstr
                                (.prim
                                  Assembly.HaltKind.selfdestruct.toPrimOp)
                                sourceInitial =
                              .ok sourceExpected := by
                          change
                            Assembly.PrimOp.selfdestruct.step sourceInitial =
                              .ok sourceExpected
                          rw [
                            Assembly.PrimOp.step_selfdestruct_of_permitted _
                              hPermission]
                          exact EvmYul.EVM.step_selfdestruct_of_stack
                            _ targetA sourceTail rfl
                        change
                          Assembly.Target.stepInstr
                              (.prim
                                Assembly.HaltKind.selfdestruct.toPrimOp)
                              sourceInitial =
                            .ok sourceFinal at hSource
                        have hSourceRun := hSource
                        rw [hSourceStep] at hSource
                        have hFinal : sourceExpected = sourceFinal :=
                          Except.ok.inj hSource
                        exact
                          ⟨targetExpected, sourceFinal,
                            hTargetStep, hSourceRun,
                            by rw [← hFinal]; rfl⟩

theorem haltStep_shared_of_runtimeRel
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite} {shape : Shape}
    {target source : Assembly.EVMState}
    {kind : Assembly.HaltKind}
    (hBound : kind.argCount ≤ shape.length)
    (hPlain :
      ReturnAddressRelation.PlainSlots
        (shape.slots.take kind.argCount))
    (hRel :
      ReturnAddressRelation.RuntimeRel
        resolve sites shape target source)
    (hSafe :
      Assembly.InteractionSemantics.Terminal.SafeAt kind source) :
    ∃ targetFinal sourceFinal,
      Assembly.Target.stepInstr (.prim kind.toPrimOp) target =
          .ok targetFinal ∧
        Assembly.Target.stepInstr (.prim kind.toPrimOp) source =
          .ok sourceFinal ∧
        targetFinal.toSharedState = sourceFinal.toSharedState := by
  apply haltStep_shared_of_prefix
  · exact hRel.1
  · exact
      Nat.le_trans hBound
        (ReturnAddressRelation.runtimeRel_stack_lengths hRel).1
  · apply ReturnAddressRelation.stackRel_take_eq_of_plain
    · simpa [Shape.length] using hBound
    · exact hPlain
    · exact hRel.2
  · exact hSafe

/-- A source-safe TypedCfg halt is realized by the physical-return Assembly
program with the same halt kind and the same post-halt shared state. Stack
suffixes may retain different logical/physical return words and are
deliberately not part of this terminal observation. -/
theorem LoweredBlockResultRel.targetHalt_shared
    {assembly : Assembly.Program}
    {resolve : ReturnAddressRelation.Resolver}
    {sites : List ReturnSite} {output : Shape}
    {target : Assembly.Source.ExecutionOutcome}
    {kind : Assembly.HaltKind} {source : Assembly.EVMState}
    (hBound : kind.argCount ≤ output.length)
    (hPlain :
      ReturnAddressRelation.PlainSlots
        (output.slots.take kind.argCount))
    (hRel :
      LoweredBlockResultRel assembly resolve sites output
        target (.ok (.halt kind source)))
    (hSafe :
      Assembly.InteractionSemantics.Terminal.SafeAt kind source) :
    ∃ targetFinal sourceFinal,
      target =
          .ok (.halted
            { kind := kind
              state := targetFinal
              output := kind.output targetFinal }) ∧
        Assembly.Target.stepInstr (.prim kind.toPrimOp) source =
          .ok sourceFinal ∧
        targetFinal.toSharedState = sourceFinal.toSharedState := by
  have hTermRel :
      LoweredTerminatorResultRel assembly resolve sites output
        target (.ok (.halt kind source)) := by
    cases target <;> exact hRel
  rcases hTermRel with ⟨middle, hTarget, hSource⟩
  cases middle with
  | error middleError =>
      cases hSource
  | ok middleOutcome =>
      cases hSource with
      | ok hOutcome =>
          cases middleOutcome with
          | fallthrough middleState =>
              cases hOutcome
          | jump next middleState =>
              cases hOutcome
          | returnDispatch middleState =>
              cases hOutcome
          | invalid middleState =>
              cases hOutcome
          | halt middleKind middleState =>
              rcases hOutcome with
                ⟨hKind, hRuntime⟩
              subst middleKind
              change
                TypedCfg.Preservation.Outcome.Simulates
                  assembly (.halt kind middleState) target
                at hTarget
              obtain
                  ⟨targetFinal, sourceFinal,
                    hTargetStep, hSourceStep, hShared⟩ :=
                haltStep_shared_of_runtimeRel
                  hBound hPlain hRuntime hSafe
              subst target
              unfold Assembly.Target.stepInstrResult
              rw [hTargetStep]
              have hHalt :
                  (Assembly.TargetInstr.prim
                    kind.toPrimOp).haltKind? =
                    some kind := by
                cases kind <;> rfl
              rw [hHalt]
              exact
                ⟨targetFinal, sourceFinal, rfl,
                  hSourceStep, hShared⟩

end ReturnAddressPreservation
end TypedCfg
end EvmCompiler
