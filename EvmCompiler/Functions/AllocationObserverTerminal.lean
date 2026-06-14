import EvmCompiler.Functions.AllocationObserverExpression
import EvmCompiler.Locals.PrimitivePreservation

namespace EvmCompiler
namespace Functions
namespace AllocationObserverTerminal

open AllocationObserverRelation

abbrev Word := Assembly.Word

namespace Machine

/--
Related machines perform the same source-approved terminal memory read.

`RETURN` and `REVERT` differ only in the eventual halt mode; both populate
`H_return` from the same padded range and perform the same active-memory
expansion.
-/
theorem evmReturn_both
    {contract : MemoryContract.Contract}
    {source target : EvmYul.MachineState}
    (hRel : Compiler.MemoryRelation.MachineRel contract source target)
    (hTargetNoWrap :
      target.activeWords.toNat * MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (address size : Word)
    (hAllowed :
      AllocationObserverSafety.RegionAllowed contract
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
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
  obtain ⟨hRead, hExpanded, hFinalNoWrap, hActiveMono⟩ :=
    Compiler.MemoryRelation.MachineRel.readRange_both
      hRel hTargetNoWrap address.toNat size.toNat hAllowed
        hExpansion hHost
  refine ⟨?_, ?_, ?_⟩
  · rcases hExpanded with
      ⟨hMemory, hActive, hReturnData, _hOutput⟩
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
      AllocationObserverSafety.RegionAllowed contract
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
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
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
          address.toNat size.toNat <
        EvmYul.UInt256.size := by
    have hBytes := hSourceMBytes
    simp [MemoryContract.wordBytes] at hBytes
    omega
  have hTargetM :
      EvmYul.MachineState.M target.activeWords.toNat
          address.toNat size.toNat <
        EvmYul.UInt256.size := by
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
          EvmYul.MachineState.M, hSize,
          Nat.max_assoc]
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
          EvmYul.MachineState.M, hSize,
          Nat.max_assoc]
  rw [sourceEq, targetEq]
  exact
    evmReturn_both hRel hTargetNoWrap address size
      hAllowed hExpansion hHost

end Machine

/--
Decoded successful terminal invocation in canonical Functions argument order.
-/
inductive Invocation (contract : MemoryContract.Contract) :
    Assembly.HaltKind → List Word → Prop where
  | stop : Invocation contract .stop []
  | return (address size : Word)
      (allowed :
        AllocationObserverSafety.RegionAllowed contract
          address.toNat size.toNat)
      (expansion :
        Compiler.MemoryRelation.ExpansionNoWrap
          address.toNat size.toNat)
      (host : address.toNat + size.toNat < USize.size) :
      Invocation contract .return [size, address]
  | revert (address size : Word)
      (allowed :
        AllocationObserverSafety.RegionAllowed contract
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
      AllocationObserverSafety.TerminalMemorySafe contract kind values) :
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
          simp [AllocationObserverSafety.TerminalMemorySafe,
            hReverse] at hSafe
  | «return» =>
      cases hReverse : values.reverse with
      | nil =>
          simp [AllocationObserverSafety.TerminalMemorySafe,
            hReverse] at hSafe
      | cons address rest =>
        cases rest with
        | nil =>
            simp [AllocationObserverSafety.TerminalMemorySafe,
              hReverse] at hSafe
        | cons size tail =>
          cases tail with
          | nil =>
              have hValues : values = [size, address] := by
                rw [← List.reverse_reverse values, hReverse]
                rfl
              subst values
              exact
                .return address size hSafe.1 hSafe.2.1 hSafe.2.2
          | cons third tail =>
              simp [AllocationObserverSafety.TerminalMemorySafe,
                hReverse] at hSafe
  | revert =>
      cases hReverse : values.reverse with
      | nil =>
          simp [AllocationObserverSafety.TerminalMemorySafe,
            hReverse] at hSafe
      | cons address rest =>
        cases rest with
        | nil =>
            simp [AllocationObserverSafety.TerminalMemorySafe,
              hReverse] at hSafe
        | cons size tail =>
          cases tail with
          | nil =>
              have hValues : values = [size, address] := by
                rw [← List.reverse_reverse values, hReverse]
                rfl
              subst values
              exact
                .revert address size hSafe.1 hSafe.2.1 hSafe.2.2
          | cons third tail =>
              simp [AllocationObserverSafety.TerminalMemorySafe,
                hReverse] at hSafe
  | selfdestruct =>
      cases hReverse : values.reverse with
      | nil =>
          simp [AllocationObserverSafety.TerminalMemorySafe,
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
            simp [AllocationObserverSafety.TerminalMemorySafe,
              hReverse] at hSafe

@[simp] theorem structured_terminal_stop
    (shared : EvmYul.SharedState .EVM) :
    Locals.Source.PrimitiveSemantics.structured.terminal
        .stop shared [] =
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
          toMachineState :=
            shared.toMachineState.evmReturn address size } := by
  rfl

@[simp] theorem structured_terminal_revert
    (shared : EvmYul.SharedState .EVM) (address size : Word) :
    Locals.Source.PrimitiveSemantics.structured.terminal
        .revert shared [size, address] =
      .ok
        { shared with
          toMachineState :=
            shared.toMachineState.evmRevert address size } := by
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

/--
Canonical terminal execution preserves the allocation shared-state relation.
-/
theorem Invocation.simulate
    {contract : MemoryContract.Contract}
    {kind : Assembly.HaltKind} {values : List Word}
    {sourceShared sourceFinal targetShared :
      EvmYul.SharedState .EVM}
    (invocation : Invocation contract kind values)
    (hRel : SharedRel contract sourceShared targetShared)
    (hTargetNoWrap :
      targetShared.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      Locals.Source.PrimitiveSemantics.structured.terminal
          kind sourceShared values =
        .ok sourceFinal) :
    ∃ targetFinal,
      Locals.Source.PrimitiveSemantics.structured.terminal
          kind targetShared values =
        .ok targetFinal ∧
      SharedRel contract sourceFinal targetFinal ∧
      targetFinal.toMachineState.memory =
        targetShared.toMachineState.memory ∧
      targetShared.toMachineState.activeWords.toNat ≤
        targetFinal.toMachineState.activeWords.toNat ∧
      targetFinal.toMachineState.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size := by
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
      refine
        ⟨targetFinal, ?_, ?_, ?_, Nat.le_refl _, ?_⟩
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
Observer-state terminal preservation from the shared observable relation over
an arbitrary target stack suffix.

This core form intentionally does not require live-local realization. Plain
terminal statements discard the complete compiler-local stack before halting,
so only cursor/shared-state agreement and the target no-wrap fact survive to
the terminal boundary.
-/
theorem Invocation.forward_shared_observer
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {kind : Assembly.HaltKind} {values : List Word}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {baseStack : EvmYul.Stack Word}
    (invocation : Invocation contract kind values)
    (hCursor : source.cursor = target.cursor)
    (hShared :
      SharedRel contract source.source.shared
        target.source.evm.toSharedState)
    (hTargetNoWrap :
      target.source.evm.activeWords.toNat *
          MemoryContract.wordBytes <
        EvmYul.UInt256.size)
    (hEval :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind source values =
        .ok sourceFinal)
    (hStack :
      target.source.evm.stack = values.reverse ++ baseStack) :
    ∃ evmFinal,
      Structured.Terminal.step kind target.source.evm =
          .ok evmFinal ∧
        HaltStateRel contract plan sourceFinal
          (target.withSource (target.source.withEVM evmFinal)) ∧
        (target.withSource
            (target.source.withEVM evmFinal)).source.evm.toMachineState.memory =
          target.source.evm.toMachineState.memory ∧
        target.source.evm.activeWords.toNat ≤
          (target.withSource
            (target.source.withEVM evmFinal)).source.evm.activeWords.toNat ∧
        (target.withSource
            (target.source.withEVM evmFinal)).source.evm.activeWords.toNat *
              MemoryContract.wordBytes <
          EvmYul.UInt256.size := by
  unfold Functions.ObserverSemantics.primitiveSemantics at hEval
  unfold Locals.ObserverSemantics.primitiveSemantics at hEval
  cases hSourceEval :
      Locals.Source.PrimitiveSemantics.structured.terminal
        kind source.source.shared values with
  | error err =>
      simp [hSourceEval] at hEval
  | ok sourceSharedFinal =>
      simp [hSourceEval] at hEval
      subst sourceFinal
      obtain
          ⟨targetSharedFinal, hTargetEval, hSharedRel,
            hMemory, hActive, hFinalNoWrap⟩ :=
        invocation.simulate hShared hTargetNoWrap hSourceEval
      obtain
          ⟨evmFinal, hStep, hFinalShared, _isolated, _hIsolated,
            _hFinalStack⟩ :=
        Locals.Source.PrimitiveSemantics.structured_terminal_step_exists
          hTargetEval rfl hStack
      refine
        ⟨evmFinal, hStep, ?_, ?_, ?_, ?_⟩
      · refine ⟨hCursor, ?_⟩
        simpa [Simulation.ResourceReplay.State.withSource,
          Structured.RunState.withEVM, Locals.Source.State.withShared,
          hFinalShared] using hSharedRel
      · simpa [Simulation.ResourceReplay.State.withSource,
          Structured.RunState.withEVM, hFinalShared] using hMemory
      · simpa [Simulation.ResourceReplay.State.withSource,
          Structured.RunState.withEVM, hFinalShared] using hActive
      · simpa [Simulation.ResourceReplay.State.withSource,
          Structured.RunState.withEVM, hFinalShared] using hFinalNoWrap

/--
Observer-state terminal preservation over an arbitrary target stack suffix.

Terminal execution preserves the observer cursor and relates only shared
observable state. Named-local and scratch-frame realization is intentionally
discarded because no continuation can observe it after a halt.
-/
theorem Invocation.forward_observer
    {transcript : Assembly.ResourceTrace}
    {contract : MemoryContract.Contract}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name} {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {kind : Assembly.HaltKind} {values : List Word}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {baseStack : EvmYul.Stack Word}
    (invocation : Invocation contract kind values)
    (hRel :
      ActivationStateRel contract plan live stackOffset frameBase
        mode source target)
    (hEval :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind source values =
        .ok sourceFinal)
    (hStack :
      target.source.evm.stack = values.reverse ++ baseStack) :
    ∃ evmFinal,
      Structured.Terminal.step kind target.source.evm =
          .ok evmFinal ∧
        HaltStateRel contract plan sourceFinal
          (target.withSource (target.source.withEVM evmFinal)) ∧
        (target.withSource
            (target.source.withEVM evmFinal)).source.evm.toMachineState.memory =
          target.source.evm.toMachineState.memory ∧
        target.source.evm.activeWords.toNat ≤
          (target.withSource
            (target.source.withEVM evmFinal)).source.evm.activeWords.toNat ∧
        (target.withSource
            (target.source.withEVM evmFinal)).source.evm.activeWords.toNat *
              MemoryContract.wordBytes <
          EvmYul.UInt256.size := by
  exact
    invocation.forward_shared_observer
      hRel.base.cursor hRel.base.core.shared hRel.activeNoWrap hEval hStack

end AllocationObserverTerminal
end Functions
end EvmCompiler
