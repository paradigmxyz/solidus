import EvmCompiler.Functions.AllocationInteractionLeave
import EvmCompiler.Locals.PrimitivePreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionTerminal

open AllocationInteractionRelation
open AllocationInteractionComposition

abbrev Word := Assembly.Word

namespace Machine

theorem evmReturn_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : Compiler.MemoryRelation.MachineRel contract source target)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (address size : Word)
    (hAllowed :
      Simulation.MemorySafety.RegionAllowed contract
        address.toNat size.toNat)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat size.toNat)
    (hHost : address.toNat + size.toNat < USize.size) :
    Compiler.MemoryRelation.MachineRel contract
        (source.evmReturn address size)
        (target.evmReturn address size) ∧
      target.activeWords.toNat ≤
        (target.evmReturn address size).activeWords.toNat ∧
      (target.evmReturn address size).activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  obtain ⟨hRead, hExpanded, hFinalNoWrap, hActiveMono⟩ :=
    Compiler.MemoryRelation.MachineRel.readRange_both
      hRel hTargetNoWrap address.toNat size.toNat hAllowed
        hExpansion hHost
  refine ⟨?_, ?_, ?_⟩
  · rcases hExpanded with ⟨hMemory, hActive, hReturnData, _hOutput⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [EvmYul.MachineState.evmReturn] using hMemory
    · simpa [EvmYul.MachineState.evmReturn] using hActive
    · simpa [EvmYul.MachineState.evmReturn] using hReturnData
    · simpa [EvmYul.MachineState.evmReturn] using hRead
  · simpa [EvmYul.MachineState.evmReturn] using hActiveMono
  · simpa [EvmYul.MachineState.evmReturn] using hFinalNoWrap

theorem evmRevert_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : Compiler.MemoryRelation.MachineRel contract source target)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (address size : Word)
    (hAllowed :
      Simulation.MemorySafety.RegionAllowed contract
        address.toNat size.toNat)
    (hExpansion :
      Compiler.MemoryRelation.ExpansionNoWrap
        address.toNat size.toNat)
    (hHost : address.toNat + size.toNat < USize.size) :
    Compiler.MemoryRelation.MachineRel contract
        (source.evmRevert address size)
        (target.evmRevert address size) ∧
      target.activeWords.toNat ≤
        (target.evmRevert address size).activeWords.toNat ∧
      (target.evmRevert address size).activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
  have hActiveLe :
      source.activeWords.toNat ≤ target.activeWords.toNat := by
    cases hReservation : contract.scratch? with
    | none =>
        have hEq : source.activeWords = target.activeWords := by
          simpa [hReservation] using hRel.activeWords
        exact le_of_eq (congrArg EvmYul.UInt256.toNat hEq)
    | some reservation =>
        simpa [hReservation] using hRel.activeWords
  have hSourceNoWrap :
      source.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size :=
    lt_of_le_of_lt
      (Nat.mul_le_mul_right MemoryContract.wordBytes hActiveLe)
      hTargetNoWrap
  have hSourceMBytes :=
    Compiler.MemoryRelation.M_activeBytes_lt_of_expansionNoWrap
      hSourceNoWrap hExpansion
  have hTargetMBytes :=
    Compiler.MemoryRelation.M_activeBytes_lt_of_expansionNoWrap
      hTargetNoWrap hExpansion
  have hSourceM :
      EvmYul.MachineState.M source.activeWords.toNat
          address.toNat size.toNat < EvmYul.UInt256.size := by
    have hBytes := hSourceMBytes
    simp [MemoryContract.wordBytes] at hBytes
    omega
  have hTargetM :
      EvmYul.MachineState.M target.activeWords.toNat
          address.toNat size.toNat < EvmYul.UInt256.size := by
    have hBytes := hTargetMBytes
    simp [MemoryContract.wordBytes] at hBytes
    omega
  have hSourceRound :
      (EvmYul.UInt256.ofNat
        (EvmYul.MachineState.M source.activeWords.toNat
          address.toNat size.toNat)).toNat =
        EvmYul.MachineState.M source.activeWords.toNat
          address.toNat size.toNat :=
    EvmYul.UInt256.toNat_ofNat_of_lt hSourceM
  have hTargetRound :
      (EvmYul.UInt256.ofNat
        (EvmYul.MachineState.M target.activeWords.toNat
          address.toNat size.toNat)).toNat =
        EvmYul.MachineState.M target.activeWords.toNat
          address.toNat size.toNat :=
    EvmYul.UInt256.toNat_ofNat_of_lt hTargetM
  have sourceEq :
      source.evmRevert address size = source.evmReturn address size := by
    unfold EvmYul.MachineState.evmRevert
    change
      { source.evmReturn address size with
          activeWords :=
            EvmYul.UInt256.ofNat
              (EvmYul.MachineState.M
                (EvmYul.UInt256.ofNat
                  (EvmYul.MachineState.M source.activeWords.toNat
                    address.toNat size.toNat)).toNat
                address.toNat size.toNat) } =
        source.evmReturn address size
    rw [hSourceRound]
    cases hSize : size.toNat with
    | zero =>
        simp [EvmYul.MachineState.evmReturn,
          EvmYul.MachineState.M, hSize]
    | succ length =>
        simp [EvmYul.MachineState.evmReturn,
          EvmYul.MachineState.M, hSize, Nat.max_assoc]
  have targetEq :
      target.evmRevert address size = target.evmReturn address size := by
    unfold EvmYul.MachineState.evmRevert
    change
      { target.evmReturn address size with
          activeWords :=
            EvmYul.UInt256.ofNat
              (EvmYul.MachineState.M
                (EvmYul.UInt256.ofNat
                  (EvmYul.MachineState.M target.activeWords.toNat
                    address.toNat size.toNat)).toNat
                address.toNat size.toNat) } =
        target.evmReturn address size
    rw [hTargetRound]
    cases hSize : size.toNat with
    | zero =>
        simp [EvmYul.MachineState.evmReturn,
          EvmYul.MachineState.M, hSize]
    | succ length =>
        simp [EvmYul.MachineState.evmReturn,
          EvmYul.MachineState.M, hSize, Nat.max_assoc]
  rw [sourceEq, targetEq]
  exact
    evmReturn_both hRel hTargetNoWrap address size
      hAllowed hExpansion hHost

end Machine

/-- Source-approved terminal operation in canonical Functions argument order. -/
inductive Invocation (contract : MemoryContract.Contract) :
    Assembly.HaltKind → List Word → Prop where
  | stop : Invocation contract .stop []
  | return (address size : Word)
      (allowed :
        Simulation.MemorySafety.RegionAllowed contract
          address.toNat size.toNat)
      (expansion :
        Compiler.MemoryRelation.ExpansionNoWrap
          address.toNat size.toNat)
      (host : address.toNat + size.toNat < USize.size) :
      Invocation contract .return [size, address]
  | revert (address size : Word)
      (allowed :
        Simulation.MemorySafety.RegionAllowed contract
          address.toNat size.toNat)
      (expansion :
        Compiler.MemoryRelation.ExpansionNoWrap
          address.toNat size.toNat)
      (host : address.toNat + size.toNat < USize.size) :
      Invocation contract .revert [size, address]
  | selfdestruct (recipient : Word) :
      Invocation contract .selfdestruct [recipient]

theorem Invocation.of_memorySafe
    {contract : MemoryContract.Contract}
    {kind : Assembly.HaltKind} {values : List Word}
    (hSafe :
      Simulation.MemorySafety.TerminalMemorySafe contract kind values) :
    Invocation contract kind values := by
  cases kind with
  | stop =>
      cases hReverse : values.reverse with
      | nil =>
          have hValues : values = [] := by
            rw [← List.reverse_reverse values, hReverse]
            rfl
          subst values
          exact .stop
      | cons head tail =>
          simp [Simulation.MemorySafety.TerminalMemorySafe,
            hReverse] at hSafe
  | «return» =>
      cases hReverse : values.reverse with
      | nil =>
          simp [Simulation.MemorySafety.TerminalMemorySafe,
            hReverse] at hSafe
      | cons address rest =>
          cases rest with
          | nil =>
              simp [Simulation.MemorySafety.TerminalMemorySafe,
                hReverse] at hSafe

          | cons size tail =>
              cases tail with
              | nil =>
                  have hValues : values = [size, address] := by
                    rw [← List.reverse_reverse values, hReverse]
                    rfl
                  subst values
                  exact .return address size hSafe.1 hSafe.2.1 hSafe.2.2
              | cons third tail =>
                  simp [Simulation.MemorySafety.TerminalMemorySafe,
                    hReverse] at hSafe
  | revert =>
      cases hReverse : values.reverse with
      | nil =>
          simp [Simulation.MemorySafety.TerminalMemorySafe,
            hReverse] at hSafe
      | cons address rest =>
          cases rest with
          | nil =>
              simp [Simulation.MemorySafety.TerminalMemorySafe,
                hReverse] at hSafe
          | cons size tail =>
              cases tail with
              | nil =>
                  have hValues : values = [size, address] := by
                    rw [← List.reverse_reverse values, hReverse]
                    rfl
                  subst values
                  exact .revert address size hSafe.1 hSafe.2.1 hSafe.2.2
              | cons third tail =>
                  simp [Simulation.MemorySafety.TerminalMemorySafe,
                    hReverse] at hSafe
  | selfdestruct =>
      cases hReverse : values.reverse with
      | nil =>
          simp [Simulation.MemorySafety.TerminalMemorySafe,
            hReverse] at hSafe
      | cons recipient tail =>
          cases tail with
          | nil =>
              have hValues : values = [recipient] := by
                rw [← List.reverse_reverse values, hReverse]
                rfl
              subst values
              exact .selfdestruct recipient
          | cons next tail =>
              simp [Simulation.MemorySafety.TerminalMemorySafe,
                hReverse] at hSafe

@[simp] theorem Invocation.values_length
    {contract : MemoryContract.Contract}
    {kind : Assembly.HaltKind} {values : List Word}
    (invocation : Invocation contract kind values) :
    values.length = kind.argCount := by
  cases invocation <;> rfl

@[simp] theorem structured_terminal_stop
    (shared : EvmYul.SharedState .EVM) :
    Locals.Source.PrimitiveSemantics.structured.terminal .stop shared [] =
      .ok
        { shared with
          returnData := ByteArray.empty
          H_return := ByteArray.empty } := by
  rfl

@[simp] theorem structured_terminal_return
    (shared : EvmYul.SharedState .EVM) (address size : Word) :
    Locals.Source.PrimitiveSemantics.structured.terminal
        .return shared [size, address] =
      .ok
        { shared with
          toMachineState := shared.toMachineState.evmReturn address size } := by
  rfl

@[simp] theorem structured_terminal_revert
    (shared : EvmYul.SharedState .EVM) (address size : Word) :
    Locals.Source.PrimitiveSemantics.structured.terminal
        .revert shared [size, address] =
      .ok
        { shared with
          toMachineState := shared.toMachineState.evmRevert address size } := by
  rfl

@[simp] theorem structured_terminal_selfdestruct
    (shared : EvmYul.SharedState .EVM) (recipient : Word) :
    Locals.Source.PrimitiveSemantics.structured.terminal
        .selfdestruct shared [recipient] =
      .ok
        ((EvmYul.EVM.selfdestructState
          { toSharedState := shared
            pc := EvmYul.UInt256.ofNat 0
            stack := [recipient]
            execLength := 0 }
          recipient []).toSharedState) := by
  rfl

theorem Invocation.eval_exists
    {contract : MemoryContract.Contract}
    {kind : Assembly.HaltKind} {values : List Word}
    (invocation : Invocation contract kind values)
    (shared : EvmYul.SharedState .EVM) :
    ∃ final,
      Locals.Source.PrimitiveSemantics.structured.terminal
        kind shared values = .ok final := by
  cases invocation with
  | stop => exact ⟨_, structured_terminal_stop shared⟩
  | «return» address size _ _ _ =>
      exact ⟨_, structured_terminal_return shared address size⟩
  | revert address size _ _ _ =>
      exact ⟨_, structured_terminal_revert shared address size⟩
  | selfdestruct recipient =>
      exact ⟨_, structured_terminal_selfdestruct shared recipient⟩

/-- Canonical terminal execution preserves the allocation shared relation. -/
theorem Invocation.simulate
    {contract : MemoryContract.Contract}
    {kind : Assembly.HaltKind} {values : List Word}
    {sourceShared sourceFinal targetShared : EvmYul.SharedState .EVM}
    (invocation : Invocation contract kind values)
    (hRel : SharedRel contract sourceShared targetShared)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.terminal
          kind sourceShared values = .ok sourceFinal) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.terminal
          kind targetShared values = .ok targetFinal ∧
        SharedRel contract sourceFinal targetFinal ∧
        targetFinal.toMachineState.memory =
          targetShared.toMachineState.memory ∧
        targetShared.toMachineState.activeWords.toNat ≤
          targetFinal.toMachineState.activeWords.toNat ∧
        targetFinal.toMachineState.activeWords.toNat *
            MemoryContract.wordBytes < EvmYul.UInt256.size := by
  cases invocation with
  | stop =>
      rw [structured_terminal_stop] at hEval
      cases hEval
      refine
        ⟨{ targetShared with
            returnData := ByteArray.empty
            H_return := ByteArray.empty },
          structured_terminal_stop targetShared, ?_, rfl,
          Nat.le_refl _, hTargetNoWrap⟩
      refine ⟨?_, hRel.world⟩
      refine ⟨?_, ?_, rfl, rfl⟩
      · simpa using hRel.machine.memory
      · simpa using hRel.machine.activeWords
  | «return» address size hAllowed hExpansion hHost =>
      rw [structured_terminal_return] at hEval
      cases hEval
      obtain ⟨hMachine, hActiveMono, hFinalNoWrap⟩ :=
        Machine.evmReturn_both hRel.machine hTargetNoWrap
          address size hAllowed hExpansion hHost
      refine
        ⟨{ targetShared with
            toMachineState :=
              targetShared.toMachineState.evmReturn address size },
          structured_terminal_return targetShared address size,
          ⟨hMachine, hRel.world⟩, ?_, hActiveMono, hFinalNoWrap⟩
      rfl
  | revert address size hAllowed hExpansion hHost =>
      rw [structured_terminal_revert] at hEval
      cases hEval
      obtain ⟨hMachine, hActiveMono, hFinalNoWrap⟩ :=
        Machine.evmRevert_both hRel.machine hTargetNoWrap
          address size hAllowed hExpansion hHost
      refine
        ⟨{ targetShared with
            toMachineState :=
              targetShared.toMachineState.evmRevert address size },
          structured_terminal_revert targetShared address size,
          ⟨hMachine, hRel.world⟩, ?_, hActiveMono, hFinalNoWrap⟩
      rfl
  | selfdestruct recipient =>
      rw [structured_terminal_selfdestruct] at hEval
      cases hEval
      let sourceState : Assembly.EVMState :=
        { toSharedState := sourceShared
          pc := EvmYul.UInt256.ofNat 0
          stack := [recipient]
          execLength := 0 }
      let targetState : Assembly.EVMState :=
        { toSharedState := targetShared
          pc := EvmYul.UInt256.ofNat 0
          stack := [recipient]
          execLength := 0 }
      let sourceFinal :=
        (EvmYul.EVM.selfdestructState sourceState recipient []).toSharedState
      let targetFinal :=
        (EvmYul.EVM.selfdestructState targetState recipient []).toSharedState
      refine ⟨targetFinal, ?_, ?_, ?_, Nat.le_refl _, ?_⟩
      · simpa [targetFinal, targetState] using
          structured_terminal_selfdestruct targetShared recipient
      · refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [sourceFinal, targetFinal, sourceState, targetState,
              EvmYul.EVM.selfdestructState] using hRel.machine.memory
          · simpa [sourceFinal, targetFinal, sourceState, targetState,
              EvmYul.EVM.selfdestructState] using hRel.machine.activeWords
          · simpa [sourceFinal, targetFinal, sourceState, targetState,
              EvmYul.EVM.selfdestructState] using hRel.machine.returnData
          · simp [sourceFinal, targetFinal, sourceState, targetState,
              EvmYul.EVM.selfdestructState,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC,
              EvmYul.MachineState.setHReturn]
        · simpa [sourceFinal, targetFinal, sourceState, targetState,
            EvmYul.EVM.selfdestructState,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC,
            EvmYul.MachineState.setHReturn, hRel.world]
      · simp [targetFinal, targetState,
          EvmYul.EVM.selfdestructState,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC,
          EvmYul.MachineState.setHReturn]
      · simpa [targetFinal, targetState,
          EvmYul.EVM.selfdestructState,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC,
          EvmYul.MachineState.setHReturn] using hTargetNoWrap

/--
One source-approved terminal invocation produces related canonical open
terminal computations from any live allocation representation.
-/
theorem Invocation.forward_shared
    {contract : MemoryContract.Contract} {plan : Plan}
    {kind : Assembly.HaltKind} {values : List Word}
    {source : SourceState} {target : TargetState}
    {sourceSharedFinal : EvmYul.SharedState .EVM}
    {baseStack : List Word}
    (invocation : Invocation contract kind values)
    (hShared : SharedRel contract source.shared target.evm.toSharedState)
    (hTargetNoWrap :
      target.evm.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.terminal
          kind source.shared values = .ok sourceSharedFinal)
    (hStack : target.evm.stack = values.reverse ++ baseStack) :
    ∃ sourceFinal targetFinal,
      Locals.InteractionSemantics.Primitive.openTerminal
          kind source values = .done (.ok sourceFinal) ∧
        Structured.InteractionSemantics.Terminal.openStep
          kind target = .done (.ok targetFinal) ∧
        HaltStateRel contract plan sourceFinal targetFinal := by
  obtain
      ⟨targetSharedFinal, hTargetEval, hSharedRel,
        _hMemory, _hActive, _hFinalNoWrap⟩ :=
    invocation.simulate hShared hTargetNoWrap hEval
  obtain
      ⟨targetEvmFinal, hTargetStep, hFinalShared,
        _isolated, _hIsolated, _hFinalStack⟩ :=
    Locals.Source.PrimitiveSemantics.structured_terminal_step_exists
      hTargetEval rfl hStack
  let sourceFinal := source.withShared sourceSharedFinal
  let targetFinal := target.withEVM targetEvmFinal
  have hSourceBound :
      kind.argCount ≤
        (Locals.InteractionSemantics.Primitive.isolated
          source values).stack.length := by
    simp [Locals.InteractionSemantics.Primitive.isolated,
      List.length_reverse, invocation.values_length]
  obtain ⟨sourceEvmFinal, hSourceStep⟩ :=
    Structured.Terminal.exists_step_of_argCount_le
      kind (Locals.InteractionSemantics.Primitive.isolated source values)
        hSourceBound
  have hSourceEval' :
      sourceEvmFinal.toSharedState = sourceSharedFinal := by
    unfold Locals.Source.PrimitiveSemantics.structured at hEval
    change
      (match
          Structured.Terminal.step kind
            (Locals.InteractionSemantics.Primitive.isolated source values)
        with
        | .ok state' => Except.ok state'.toSharedState
        | .error err => Except.error err) =
        .ok sourceSharedFinal at hEval
    rw [hSourceStep] at hEval
    exact Except.ok.inj hEval
  have hSourceOpen :
      Locals.InteractionSemantics.Primitive.openTerminal
          kind source values = .done (.ok sourceFinal) := by
    unfold Locals.InteractionSemantics.Primitive.openTerminal
      Simulation.Interaction.map
    change
      Simulation.Interaction.bind
          (.done
            (Structured.Terminal.step kind
              (Locals.InteractionSemantics.Primitive.isolated source values)))
          _ = _
    rw [hSourceStep]
    change
      Simulation.Interaction.done
          (.ok (source.withShared sourceEvmFinal.toSharedState)) =
        Simulation.Interaction.done (.ok sourceFinal)
    rw [hSourceEval']
  have hTargetOpenStep :
      Assembly.InteractionSemantics.PrimOp.openStep
          kind.toPrimOp target.evm = .done (.ok targetEvmFinal) := by
    have hExternal :
        Simulation.ExternalKind.ofEVMOperation?
            kind.toPrimOp.toEVM = none := by
      cases kind <;> rfl
    have hGas : kind.toPrimOp ≠ .gas := by
      cases kind <;> simp [Assembly.HaltKind.toPrimOp]
    have hMsize : kind.toPrimOp ≠ .msize := by
      cases kind <;> simp [Assembly.HaltKind.toPrimOp]
    rw [Assembly.InteractionSemantics.PrimOp.openStep_closed
      hExternal hGas hMsize]
    have hPrimitiveStep :
        kind.toPrimOp.step target.evm = .ok targetEvmFinal := by
      simpa [Structured.Terminal.step] using hTargetStep
    rw [hPrimitiveStep]
  have hTargetOpen :
      Structured.InteractionSemantics.Terminal.openStep
          kind target = .done (.ok targetFinal) := by
    unfold Structured.InteractionSemantics.Terminal.openStep
      Simulation.Interaction.map
    rw [hTargetOpenStep]
    rfl
  refine ⟨sourceFinal, targetFinal, hSourceOpen, hTargetOpen, ?_⟩
  refine ⟨?_⟩
  simpa [sourceFinal, targetFinal, hFinalShared] using hSharedRel

theorem Invocation.forward
    {contract : MemoryContract.Contract} {plan : Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {kind : Assembly.HaltKind} {values : List Word}
    {source : SourceState} {target : TargetState}
    {sourceSharedFinal : EvmYul.SharedState .EVM}
    {baseStack : List Word}
    (invocation : Invocation contract kind values)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase mode
        source target)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.terminal
          kind source.shared values = .ok sourceSharedFinal)
    (hStack : target.evm.stack = values.reverse ++ baseStack) :
    ∃ sourceFinal targetFinal,
      Locals.InteractionSemantics.Primitive.openTerminal
          kind source values = .done (.ok sourceFinal) ∧
        Structured.InteractionSemantics.Terminal.openStep
          kind target = .done (.ok targetFinal) ∧
        HaltStateRel contract plan sourceFinal targetFinal := by
  exact invocation.forward_shared hRel.shared hRel.activeNoWrap hEval hStack

namespace TerminalLeaf

theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {kind : Assembly.HaltKind}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminal kind) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    loweredStmts = [.terminal kind] ∧
      lowerFinal = lowerState ∧
      compiledStmts =
        Locals.codeStmt localsCtx.cleanupAll ++ [.terminal kind] ∧
      localsFinal = localsCtx := by
  simp [AllocationLowering.lowerStmt] at hLower
  rcases hLower with ⟨rfl, rfl⟩
  simp [Locals.Block.compileOpen, Locals.Stmt.compile] at hCompile
  rcases hCompile with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem args_compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminalArgs kind args) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ lowered code,
      AllocationLowering.lowerExprSeq lowerCtx lowerState args =
          some lowered ∧
        Locals.ExprSeq.compileCode localsCtx 0 lowered = some code ∧
        loweredStmts = [.terminalArgs kind lowered] ∧
        lowerFinal = lowerState ∧
        compiledStmts = [.code code, .terminal kind] ∧
        localsFinal = localsCtx := by
  cases hLowerArgs :
      AllocationLowering.lowerExprSeq lowerCtx lowerState args with
  | none => simp [AllocationLowering.lowerStmt, hLowerArgs] at hLower
  | some lowered =>
      simp [AllocationLowering.lowerStmt, hLowerArgs] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      cases hCode : Locals.ExprSeq.compileCode localsCtx 0 lowered with
      | none =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile,
            hCode] at hCompile
      | some code =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile,
            Locals.codeStmt, hCode] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact ⟨lowered, code, rfl, hCode, rfl, rfl, rfl, rfl⟩

end TerminalLeaf

/-- Terminal-with-arguments preservation through both ordinary compilers. -/
theorem terminalArgs_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns live : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hArgsSafe : AllocationInteractionSafety.ExprSeqSafe contract args source)
    (hTerminalSafe :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result =>
              Simulation.MemorySafety.TerminalMemorySafe
                contract kind result.2)
        (Functions.InteractionSemantics.ExprSeq.openEval args source))
    (hScoped : Functions.Scope.ExprSeqScoped live args)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminalArgs kind args) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerFinal localsFinal plan
        returns live frameBase mode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.terminalArgs kind args) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 3) { stmts := compiledStmts } target) := by
  obtain ⟨lowered, code, hLowerArgs, hCompileCode,
      rfl, rfl, rfl, rfl⟩ :=
    TerminalLeaf.args_compiler_shape hLower hCompile
  have hArgs :=
    AllocationInteractionExpressionRecursive.forwardExprSeq
      hArgsSafe hInvariant.compiler hScoped hLowerArgs hCompileCode
        hInvariant.state
  have hArgsStrong :=
    Simulation.Interaction.Rel.strengthen_left hArgs hTerminalSafe
  rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_terminal]
  unfold Functions.InteractionSemantics.Stmt.openRun
    Functions.Source.Canonical.Stmt.run
  simp only [Functions.Source.Effectful.Control.Stmt.run]
  change
    Simulation.Interaction.Rel _
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.ExprSeq.openEval args source)
        (fun result =>
          Simulation.Interaction.bind
            (Locals.InteractionSemantics.Primitive.openTerminal
              kind result.1 result.2)
            (fun final =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.halt kind final,
                  sourceCtx))))
      (Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun code target)
        (fun afterArgs =>
          Simulation.Interaction.bind
            (Structured.InteractionSemantics.Terminal.openStep kind afterArgs)
            (fun final =>
              Simulation.Interaction.pure
                (Structured.EffectSemantics.Outcome.halt kind final))))
  apply Simulation.Interaction.Rel.bind_custom hArgsStrong
  intro sourceDone targetDone hDone
  rcases hDone with ⟨hRelated, hSafeDone⟩
  cases hRelated with
  | error hError =>
      exact Simulation.Interaction.Rel.done
        (Simulation.Interaction.ExceptRel.error hError)
  | @ok sourceResult targetAfterArgs hArgsResult =>
      rcases sourceResult with ⟨sourceAfterArgs, values⟩
      have invocation := Invocation.of_memorySafe hSafeDone
      obtain ⟨sourceSharedFinal, hSourceEval⟩ :=
        invocation.eval_exists sourceAfterArgs.shared
      obtain
          ⟨sourceFinal, targetFinal,
            hSourceTerminal, hTargetTerminal, hHalt⟩ :=
        invocation.forward hArgsResult.state hSourceEval hArgsResult.stack
      change
        Simulation.Interaction.Rel _
          (Simulation.Interaction.bind
            (Locals.InteractionSemantics.Primitive.openTerminal
              kind sourceAfterArgs values)
            (fun final =>
              Simulation.Interaction.pure
                (Functions.Source.Effectful.Outcome.halt kind final,
                  sourceCtx)))
          (Simulation.Interaction.bind
            (Structured.InteractionSemantics.Terminal.openStep
              kind targetAfterArgs)
            (fun final =>
              Simulation.Interaction.pure
                (Structured.EffectSemantics.Outcome.halt kind final)))
      rw [hSourceTerminal, hTargetTerminal]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      refine ControlResultRel.nonregular (mode := mode) (by simp)
        (SameFrame.refl mode)
        (Functions.Source.Ctx.SameControl.refl sourceCtx) ?_
      exact ActivationOutcomeRel.halt kind hHalt

/-- Plain terminal preservation after compiler-owned complete stack cleanup. -/
theorem terminal_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns live : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {sourceFuel targetExtra frameBase : Nat}
    {mode : ActivationMode}
    {kind : Assembly.HaltKind}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hMemory :
      Simulation.MemorySafety.TerminalMemorySafe contract kind [])
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminal kind) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenControlResultRel contract lowerCtx lowerFinal localsFinal plan
        returns live frameBase mode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.terminal kind) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 3) { stmts := compiledStmts } target) := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    TerminalLeaf.compiler_shape hLower hCompile
  obtain
      ⟨targetAfterCleanup, hCleanupRun,
        hCleanupStack, hCleanupShared, _hCleanupReturns⟩ :=
    Locals.InteractionPreservation.Code.openRun_replicate_pop
      localsFinal.layout.length (by rw [hInvariant.stackLength])
  have hCleanupRun' :
      Structured.InteractionSemantics.Code.openRun
          localsFinal.cleanupAll target =
        .done (.ok targetAfterCleanup) := by
    simpa [Locals.Ctx.cleanupAll] using hCleanupRun
  have hAfterStack : targetAfterCleanup.evm.stack = [] := by
    rw [hCleanupStack, hInvariant.stackLength.symm]
    exact List.drop_length
  have hAfterShared :
      SharedRel contract source.shared
        targetAfterCleanup.evm.toSharedState := by
    rw [hCleanupShared]
    exact hInvariant.state.shared
  have hAfterNoWrap :
      targetAfterCleanup.evm.activeWords.toNat *
          MemoryContract.wordBytes < EvmYul.UInt256.size := by
    rw [show
      targetAfterCleanup.evm.activeWords = target.evm.activeWords by
        exact
          congrArg
            (fun shared : EvmYul.SharedState .EVM =>
              shared.toMachineState.activeWords)
            hCleanupShared]
    exact hInvariant.state.activeNoWrap
  have invocation := Invocation.of_memorySafe hMemory
  obtain ⟨sourceSharedFinal, hSourceEval⟩ :=
    invocation.eval_exists source.shared
  obtain
      ⟨sourceFinal, targetFinal,
        hSourceTerminal, hTargetTerminal, hHalt⟩ :=
    invocation.forward_shared
      (plan := plan) (baseStack := [])
      hAfterShared hAfterNoWrap hSourceEval (by simpa using hAfterStack)
  have hSource :
      Functions.InteractionSemantics.Stmt.openRun
          sourceProgram sourceCtx sourceFuel (.terminal kind) source =
        .done
          (.ok
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
              sourceCtx)) := by
    unfold Functions.InteractionSemantics.Stmt.openRun
      Functions.Source.Canonical.Stmt.run
    simp only [Functions.Source.Effectful.Control.Stmt.run]
    unfold Functions.InteractionSemantics.primitiveSemantics
    unfold Locals.InteractionSemantics.primitiveSemantics
    change
      Simulation.Interaction.bind
          (Locals.InteractionSemantics.Primitive.openTerminal kind source [])
          (fun state' =>
            Simulation.Interaction.pure
              (Functions.Source.Effectful.Outcome.halt kind state',
                sourceCtx)) =
        .done
          (.ok
            (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
              sourceCtx))
    rw [hSourceTerminal]
    rfl
  have hTarget :
      Expressions.InteractionSemantics.Block.openRun
          targetProgram (targetExtra + 3)
          { stmts := [.code localsFinal.cleanupAll, .terminal kind] }
          target =
        .done
          (.ok (Structured.EffectSemantics.Outcome.halt kind targetFinal)) := by
    rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_code_terminal]
    rw [hCleanupRun']
    change
      Simulation.Interaction.bind
          (Structured.InteractionSemantics.Terminal.openStep
            kind targetAfterCleanup)
          (fun final =>
            Simulation.Interaction.pure
              (Structured.EffectSemantics.Outcome.halt kind final)) =
        .done
          (.ok (Structured.EffectSemantics.Outcome.halt kind targetFinal))
    rw [hTargetTerminal]
    rfl
  have hTargetCompiled :
      Expressions.InteractionSemantics.Block.openRun
          targetProgram (targetExtra + 3)
          { stmts :=
              Locals.codeStmt localsFinal.cleanupAll ++ [.terminal kind] }
          target =
        .done
          (.ok (Structured.EffectSemantics.Outcome.halt kind targetFinal)) := by
    simpa [Locals.codeStmt] using hTarget
  rw [hSource, hTargetCompiled]
  apply Simulation.Interaction.Rel.done
  apply Simulation.Interaction.ExceptRel.ok
  refine ControlResultRel.nonregular (mode := mode) (by simp)
    (SameFrame.refl mode)
    (Functions.Source.Ctx.SameControl.refl sourceCtx) ?_
  exact ActivationOutcomeRel.halt kind hHalt

end AllocationInteractionTerminal
end Functions
end EvmCompiler
