import EvmCompiler.Yul.FunctionsInteractionPrimitive

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionTerminal

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation

inductive PrimitiveDoneRel (kind : Assembly.HaltKind) :
    Except Yul.InteractionSemantics.Failure
        (Yul.InteractionSemantics.State × List Word) →
      Except EVMException Functions.InteractionSemantics.State → Prop where
  | error {source target} :
      ErrorRel source target →
        PrimitiveDoneRel kind (.error source) (.error target)
  | terminal {source target} :
      FunctionsInteractionRelation.TerminalFailureRel source
          (Functions.Source.Effectful.Outcome.halt kind target) →
        PrimitiveDoneRel kind (.error source) (.ok target)

private theorem sourcePrimCall_stop
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) :
    EvmYul.Yul.primCall (fuel + 1) (.Ok shared vars)
        (.StopArith .STOP) [] =
      .error
        (.YulHalt
          (.Ok { shared with H_return := ByteArray.empty } vars)
          (EvmYul.UInt256.ofNat 0)) := by
  have hStep :
      (EvmYul.step (τ := .Yul) (.StopArith .STOP) (arg := none))
          (.Ok shared vars) [] =
        .error
          (.YulHalt
            (.Ok { shared with H_return := ByteArray.empty } vars)
            (EvmYul.UInt256.ofNat 0)) := by
    rfl
  simp [EvmYul.Yul.primCall, hStep]

private theorem sourcePrimCall_return
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (address size : Word) :
    EvmYul.Yul.primCall (fuel + 1) (.Ok shared vars)
        (.System .RETURN) [address, size] =
      .error
        (.YulHalt
          (.Ok
            { shared with
                toMachineState :=
                  shared.toMachineState.evmReturn address size }
            vars)
          (EvmYul.UInt256.ofNat 1)) := by
  have hStep :
      (EvmYul.step (τ := .Yul) (.System .RETURN) (arg := none))
          (.Ok shared vars) [address, size] =
        .error
          (.YulHalt
            (.Ok
              { shared with
                  toMachineState :=
                    shared.toMachineState.evmReturn address size }
              vars)
            (EvmYul.UInt256.ofNat 1)) := by
    rfl
  simp [EvmYul.Yul.primCall, hStep]

private theorem sourcePrimCall_revert
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (address size : Word) :
    EvmYul.Yul.primCall (fuel + 1) (.Ok shared vars)
        (.System .REVERT) [address, size] =
      .error
        (.Revert
          (.Ok
            { shared with
                toMachineState :=
                  shared.toMachineState.evmRevert address size }
            vars)) := by
  have hStep :
      (EvmYul.step (τ := .Yul) (.System .REVERT) (arg := none))
          (.Ok shared vars) [address, size] =
        .error
          (.Revert
            (.Ok
              { shared with
                  toMachineState :=
                    shared.toMachineState.evmRevert address size }
              vars)) := by
    rfl
  simp [EvmYul.Yul.primCall, hStep]

private theorem sourcePrimCall_selfdestruct
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (recipient : Word)
    (hPerm : shared.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) (.Ok shared vars)
        (.System .SELFDESTRUCT) [recipient] =
      .error
        (.YulHalt
          (EvmYul.Yul.selfdestructState
            (.Ok shared vars) recipient)
          (EvmYul.UInt256.ofNat 0)) := by
  have hStep :
      (EvmYul.step (τ := .Yul) (.System .SELFDESTRUCT) (arg := none))
          (.Ok shared vars) [recipient] =
        .error
          (.YulHalt
            (EvmYul.Yul.selfdestructState
              (.Ok shared vars) recipient)
            (EvmYul.UInt256.ofNat 0)) := by
    rfl
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv,
    hPerm, hStep]

private theorem sourcePrimCall_selfdestruct_static
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) (recipient : Word)
    (hPerm : shared.executionEnv.perm = false) :
    EvmYul.Yul.primCall (fuel + 1) (.Ok shared vars)
        (.System .SELFDESTRUCT) [recipient] =
      .error .StaticModeViolation := by
  simp [EvmYul.Yul.primCall, EvmYul.Yul.State.executionEnv, hPerm,
    MonadExcept.throw, MonadExceptOf.throw, instMonadExceptOfExcept,
    Except.bind]
  change
    (Except.error .StaticModeViolation :
      Except EvmYul.Yul.Exception
        (EvmYul.Yul.State × List Word)) =
      .error .StaticModeViolation
  rfl

theorem stop
    (fuel : Nat)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hPerm : source.sharedState.executionEnv.perm = true)
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel .stop)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 2) source (.StopArith .STOP) [])
      (Functions.InteractionSemantics.primitiveSemantics.terminal
        .stop target []) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
  let sourceFinal : Yul.InteractionSemantics.State :=
    .Ok { sourceShared with H_return := ByteArray.empty } sourceVars
  let targetFinal : Functions.InteractionSemantics.State :=
    target.withShared
      { target.shared with
          returnData := ByteArray.empty
          H_return := ByteArray.empty }
  have hSource :
      Yul.InteractionSemantics.Primitive.openEval
          (fuel + 2) (.Ok sourceShared sourceVars) (.StopArith .STOP) [] =
        .done
          (.error
            { exception := .YulHalt sourceFinal
                (EvmYul.UInt256.ofNat 0)
              state := sourceFinal }) := by
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?,
      sourcePrimCall_stop, sourceFinal,
      Yul.InteractionSemantics.State.afterException]
  have hTarget :
      Functions.InteractionSemantics.primitiveSemantics.terminal
          .stop target [] =
        .done (.ok targetFinal) := by
    rfl
  rw [hSource, hTarget]
  apply Simulation.Interaction.ForwardRel.done
  apply PrimitiveDoneRel.terminal
  apply FunctionsInteractionRelation.TerminalFailureRel.stop
  exact
    ⟨{ sourceShared with H_return := ByteArray.empty }, sourceVars,
      rfl, FunctionsInteractionRelation.TerminalSharedRel.stop hShared,
      by simpa [targetFinal, Locals.Source.State.withShared] using hVars⟩

theorem return_
    (fuel : Nat) (address size : Word)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel .return)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 2) source (.System .RETURN) [address, size])
      (Functions.InteractionSemantics.primitiveSemantics.terminal
        .return target [size, address]) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
  let sourceFinal : Yul.InteractionSemantics.State :=
    .Ok
      { sourceShared with
          toMachineState :=
            sourceShared.toMachineState.evmReturn address size }
      sourceVars
  let targetFinal : Functions.InteractionSemantics.State :=
    target.withShared
      { target.shared with
          toMachineState :=
            target.shared.toMachineState.evmReturn address size }
  have hSource :
      Yul.InteractionSemantics.Primitive.openEval
          (fuel + 2) (.Ok sourceShared sourceVars)
            (.System .RETURN) [address, size] =
        .done
          (.error
            { exception := .YulHalt sourceFinal
                (EvmYul.UInt256.ofNat 1)
              state := sourceFinal }) := by
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?,
      sourcePrimCall_return, sourceFinal,
      Yul.InteractionSemantics.State.afterException]
  have hTarget :
      Functions.InteractionSemantics.primitiveSemantics.terminal
          .return target [size, address] =
        .done (.ok targetFinal) := by
    rfl
  rw [hSource, hTarget]
  apply Simulation.Interaction.ForwardRel.done
  apply PrimitiveDoneRel.terminal
  apply FunctionsInteractionRelation.TerminalFailureRel.return_
  exact
    ⟨{ sourceShared with
          toMachineState :=
            sourceShared.toMachineState.evmReturn address size },
      sourceVars, rfl,
      FunctionsInteractionRelation.TerminalSharedRel.evmReturn
        hShared address size,
      by simpa [targetFinal, Locals.Source.State.withShared] using hVars⟩

theorem revert
    (fuel : Nat) (address size : Word)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel .revert)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 2) source (.System .REVERT) [address, size])
      (Functions.InteractionSemantics.primitiveSemantics.terminal
        .revert target [size, address]) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
  let sourceFinal : Yul.InteractionSemantics.State :=
    .Ok
      { sourceShared with
          toMachineState :=
            sourceShared.toMachineState.evmRevert address size }
      sourceVars
  let targetFinal : Functions.InteractionSemantics.State :=
    target.withShared
      { target.shared with
          toMachineState :=
            target.shared.toMachineState.evmRevert address size }
  have hSource :
      Yul.InteractionSemantics.Primitive.openEval
          (fuel + 2) (.Ok sourceShared sourceVars)
            (.System .REVERT) [address, size] =
        .done
          (.error
            { exception := .Revert sourceFinal
              state := sourceFinal }) := by
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?,
      sourcePrimCall_revert, sourceFinal,
      Yul.InteractionSemantics.State.afterException]
  have hTarget :
      Functions.InteractionSemantics.primitiveSemantics.terminal
          .revert target [size, address] =
        .done (.ok targetFinal) := by
    rfl
  rw [hSource, hTarget]
  apply Simulation.Interaction.ForwardRel.done
  apply PrimitiveDoneRel.terminal
  apply FunctionsInteractionRelation.TerminalFailureRel.revert
  exact
    ⟨{ sourceShared with
          toMachineState :=
            sourceShared.toMachineState.evmRevert address size },
      sourceVars, rfl,
      FunctionsInteractionRelation.TerminalSharedRel.evmRevert
        hShared address size,
      by simpa [targetFinal, Locals.Source.State.withShared] using hVars⟩

theorem selfdestruct
    (fuel : Nat) (recipient : Word)
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hRel : FunctionsInteractionRelation.StateRel source target) :
    Simulation.Interaction.ForwardRel Truncated
      (PrimitiveDoneRel .selfdestruct)
      (Yul.InteractionSemantics.Primitive.openEval
        (fuel + 2) source (.System .SELFDESTRUCT) [recipient])
      (Functions.InteractionSemantics.primitiveSemantics.terminal
        .selfdestruct target [recipient]) := by
  rcases hRel with
    ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩
  by_cases hSourcePerm : sourceShared.executionEnv.perm = true
  · have hTargetPerm : target.shared.executionEnv.perm = true := by
      rw [← hShared.executionEnv.permission]
      exact hSourcePerm
    let sourceFinal :=
      EvmYul.Yul.selfdestructState
        (.Ok sourceShared sourceVars) recipient
    let targetShared :=
      (EvmYul.EVM.selfdestructState
        { toSharedState := target.shared
          pc := EvmYul.UInt256.ofNat 0
          stack := [recipient]
          execLength := 0 }
        recipient []).toSharedState
    let targetFinal : Functions.InteractionSemantics.State :=
      target.withShared targetShared
    have hSource :
        Yul.InteractionSemantics.Primitive.openEval
            (fuel + 2) (.Ok sourceShared sourceVars)
              (.System .SELFDESTRUCT) [recipient] =
          .done
            (.error
              { exception := .YulHalt sourceFinal
                  (EvmYul.UInt256.ofNat 0)
                state := sourceFinal }) := by
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?,
        sourcePrimCall_selfdestruct, hSourcePerm, sourceFinal,
        Yul.InteractionSemantics.State.afterException]
    have hTarget :
        Functions.InteractionSemantics.primitiveSemantics.terminal
            .selfdestruct target [recipient] =
          .done (.ok targetFinal) := by
      have hStep :
          Assembly.HaltKind.selfdestruct.toPrimOp.step
              { toSharedState := target.shared
                pc := EvmYul.UInt256.ofNat 0
                stack := [recipient]
                execLength := 0 } =
            .ok
              (EvmYul.EVM.selfdestructState
                { toSharedState := target.shared
                  pc := EvmYul.UInt256.ofNat 0
                  stack := [recipient]
                  execLength := 0 }
                recipient []) := by
        let isolated : Assembly.EVMState :=
          { toSharedState := target.shared
            pc := EvmYul.UInt256.ofNat 0
            stack := [recipient]
            execLength := 0 }
        have hRaw :
            EvmYul.step (τ := .EVM) .SELFDESTRUCT none isolated =
              .ok (EvmYul.EVM.selfdestructState
                isolated recipient []) :=
          EvmYul.EVM.step_selfdestruct_of_stack _ recipient [] rfl
        change Assembly.PrimOp.selfdestruct.step isolated = _
        rw [Assembly.PrimOp.step_selfdestruct_of_permitted
          isolated hTargetPerm, hRaw]
      simp only [Functions.InteractionSemantics.primitiveSemantics,
        Locals.InteractionSemantics.primitiveSemantics,
        Locals.InteractionSemantics.Primitive.openTerminal,
        Locals.InteractionSemantics.Primitive.isolated,
        Structured.Terminal.step, Assembly.Target.stepInstr_prim]
      simp only [List.reverse_singleton]
      rw [hStep]
      rfl
    rw [hSource, hTarget]
    apply Simulation.Interaction.ForwardRel.done
    apply PrimitiveDoneRel.terminal
    apply FunctionsInteractionRelation.TerminalFailureRel.selfdestruct
    exact
      ⟨sourceFinal.sharedState, sourceVars, by
          simp [sourceFinal, EvmYul.Yul.selfdestructState,
            EvmYul.Yul.State.setState,
            EvmYul.Yul.State.setMachineState,
            EvmYul.Yul.State.sharedState],
        FunctionsInteractionRelation.TerminalSharedRel.selfdestruct
          hShared sourceVars recipient,
        by simpa [targetFinal, targetShared,
          Locals.Source.State.withShared] using hVars⟩
  · have hSourceStatic : sourceShared.executionEnv.perm = false := by
      cases hPermission : sourceShared.executionEnv.perm with
      | false => rfl
      | true => exact (hSourcePerm hPermission).elim
    have hTargetStatic : target.shared.executionEnv.perm = false := by
      simpa [hSourceStatic] using hShared.executionEnv.permission.symm
    have hSource :
        Yul.InteractionSemantics.Primitive.openEval
            (fuel + 2) (.Ok sourceShared sourceVars)
              (.System .SELFDESTRUCT) [recipient] =
          .done
            (.error
              { exception := .StaticModeViolation
                state := .Ok sourceShared sourceVars }) := by
      simp [Yul.InteractionSemantics.Primitive.openEval,
        Yul.InteractionSemantics.Primitive.closedEval,
        Yul.InteractionSemantics.Primitive.fail,
        Simulation.ExternalKind.ofYulOperation?,
        Simulation.CallKind.ofYulOperation?,
        Simulation.CreateKind.ofYulOperation?,
        sourcePrimCall_selfdestruct_static, hSourceStatic,
        Yul.InteractionSemantics.State.afterException]
    have hTarget :
        Functions.InteractionSemantics.primitiveSemantics.terminal
            .selfdestruct target [recipient] =
          .done (.error .StaticModeViolation) := by
      have hStep :
          Structured.Terminal.step .selfdestruct
              (Locals.InteractionSemantics.Primitive.isolated
                target [recipient]) =
            .error .StaticModeViolation := by
        change Assembly.PrimOp.selfdestruct.step
            (Locals.InteractionSemantics.Primitive.isolated
              target [recipient]) = _
        apply Assembly.PrimOp.step_selfdestruct_of_static
        simpa [Locals.InteractionSemantics.Primitive.isolated] using
          hTargetStatic
      simp only [Functions.InteractionSemantics.primitiveSemantics,
        Locals.InteractionSemantics.primitiveSemantics,
        Locals.InteractionSemantics.Primitive.openTerminal]
      rw [hStep]
      rfl
    rw [hSource, hTarget]
    exact Simulation.Interaction.ForwardRel.done
      (PrimitiveDoneRel.error trivial)

end FunctionsInteractionTerminal
end Yul
end EvmCompiler
