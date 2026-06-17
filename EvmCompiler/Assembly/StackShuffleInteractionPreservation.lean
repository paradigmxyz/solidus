import EvmCompiler.Assembly.InteractionPreservation
import EvmCompiler.Assembly.StackShufflePreservation

namespace EvmCompiler
namespace Assembly
namespace StackShuffle
namespace InteractionPreservation

open Assembly.InteractionPreservation

private theorem state_eq_of_fields
    {left right : EVMState}
    (hShared : left.toSharedState = right.toSharedState)
    (hPc : left.pc = right.pc)
    (hStack : left.stack = right.stack)
    (hExec : left.execLength = right.execLength) :
    left = right := by
  cases left
  cases right
  simp_all

theorem openStepAt_dupInstr_eq_done
    {n : Nat} (hOne : 1 ≤ n) (hBound : n ≤ 16)
    {program : Program} {pc : Nat} {state : EVMState} :
    InteractionSemantics.Source.openStepAt
        program pc (dupInstr n) state =
      .done (Source.stepAt program pc (dupInstr n) state) := by
  interval_cases n <;> rfl

theorem openStepAt_swapInstr_eq_done
    {n : Nat} (hOne : 1 ≤ n) (hBound : n ≤ 16)
    {program : Program} {pc : Nat} {state : EVMState} :
    InteractionSemantics.Source.openStepAt
        program pc (swapInstr n) state =
      .done (Source.stepAt program pc (swapInstr n) state) := by
  interval_cases n <;> rfl

/--
One generated return-dispatch probe consumes exactly four Assembly source
instructions. Its final conditional jump remains inside the caller-owned
region when the supplied policy marks that instruction as internal.
-/
theorem dispatchTest_openRunUntilTransferWithPolicy
    (continueTransfer : Instr → Bool)
    {front suffix : List Word} {token probe : Word}
    {label : Label} {dest : Nat} {pre post : Program}
    {state : EVMState} (fuel : Nat)
    (hContinue : continueTransfer (.jumpi label) = true)
    (hFits :
      Program.PCFitsFrom pre
        [dupInstr (front.length + 1), .push probe, .prim .eq, .jumpi label])
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hBound : front.length < 16)
    (hLabel :
      (pre ++
          [dupInstr (front.length + 1), .push probe, .prim .eq, .jumpi label] ++
          post).labelPc label = some dest) :
    let final : EVMState :=
      { state with
        stack := front ++ token :: suffix
        pc :=
          if probe = token then EvmYul.UInt256.ofNat dest
          else
            (pre ++
              [dupInstr (front.length + 1), .push probe, .prim .eq,
                .jumpi label]).pcAfter }
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++
          [dupInstr (front.length + 1), .push probe, .prim .eq, .jumpi label] ++
          post)
        (fuel + 4)
        { state with stack := front ++ token :: suffix } =
      InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++
          [dupInstr (front.length + 1), .push probe, .prim .eq, .jumpi label] ++
          post)
        fuel final := by
  let duplicate := dupInstr (front.length + 1)
  let start : EVMState :=
    { state with stack := front ++ token :: suffix }
  let afterDup : EVMState :=
    start.replaceStackAndIncrPC (token :: front ++ token :: suffix)
  let afterPush : EVMState :=
    afterDup.replaceStackAndIncrPC
      (probe :: token :: front ++ token :: suffix) (pcΔ := 33)
  let afterEq : EVMState :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.eq probe token :: front ++ token :: suffix)
  let final : EVMState :=
    { state with
      stack := front ++ token :: suffix
      pc :=
        if probe = token then EvmYul.UInt256.ofNat dest
        else
          (pre ++
            [dupInstr (front.length + 1), .push probe, .prim .eq,
              .jumpi label]).pcAfter }
  have hDupStep :
      Target.stepInstr (targetInstr duplicate) start = .ok afterDup := by
    rw [show duplicate = dupInstr (front.length + 1) from rfl]
    rw [dupInstr_step_eq_dup (by omega) (by omega)]
    simpa [afterDup, start, List.append_assoc] using
      (dup_append_token (state := state) (front := front)
        (suffix := suffix) (token := token))
  have hPushStep :
      Target.stepInstr (targetInstr (.push probe)) afterDup =
        .ok afterPush := by
    simp [targetInstr, afterPush, afterDup, Target.stepInstr,
      EvmYul.Stack.push, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hEqStep :
      Target.stepInstr (targetInstr (.prim .eq)) afterPush =
        .ok afterEq := by
    simp [targetInstr, afterEq, afterPush, afterDup,
      Target.stepInstr, PrimOp.step, PrimOp.continuingStep?,
      PrimStep.run, EvmYul.EVM.execBinOp, EvmYul.Stack.push,
      EvmYul.Stack.pop2, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hDupByte : duplicate.byteSize = 1 :=
    dupInstr_byteSize (by omega) (by omega)
  have hAfterDupPc : afterDup.pc = (pre ++ [duplicate]).pcAfter := by
    have hPcState : state.pc = pre.pcAfter := by
      simpa [start] using hPc
    calc
      afterDup.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
        simp [afterDup, start, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ = pre.pcAfter + EvmYul.UInt256.ofNat 1 := by rw [hPcState]
      _ = EvmYul.UInt256.ofNat (pre.byteLength + 1) := by
        rw [Program.pcAfter, UInt256_ofNat_add]
      _ = (pre ++ [duplicate]).pcAfter := by
        simp [Program.pcAfter, Program.byteLength_append,
          Program.byteLength, hDupByte]
  have hAfterPushPc :
      afterPush.pc = (pre ++ [duplicate, .push probe]).pcAfter := by
    calc
      afterPush.pc = afterDup.pc + EvmYul.UInt256.ofNat 33 := by
        simp [afterPush, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ = (pre ++ [duplicate]).pcAfter + EvmYul.UInt256.ofNat 33 := by
        rw [hAfterDupPc]
      _ =
          EvmYul.UInt256.ofNat ((pre ++ [duplicate]).byteLength + 33) := by
        rw [Program.pcAfter, UInt256_ofNat_add]
      _ = (pre ++ [duplicate, .push probe]).pcAfter := by
        simp [Program.pcAfter, Program.byteLength_append,
          Program.byteLength, Instr.byteSize, Instr.push32Size, Nat.add_assoc]
  have hAfterEqPc :
      afterEq.pc =
        (pre ++ [duplicate, .push probe, .prim .eq]).pcAfter := by
    calc
      afterEq.pc = afterPush.pc + EvmYul.UInt256.ofNat 1 := by
        simp [afterEq, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ =
          (pre ++ [duplicate, .push probe]).pcAfter +
            EvmYul.UInt256.ofNat 1 := by
        rw [hAfterPushPc]
      _ =
          EvmYul.UInt256.ofNat
            ((pre ++ [duplicate, .push probe]).byteLength + 1) := by
        rw [Program.pcAfter, UInt256_ofNat_add]
      _ = (pre ++ [duplicate, .push probe, .prim .eq]).pcAfter := by
        simp [Program.pcAfter, Program.byteLength_append,
          Program.byteLength, Instr.byteSize, Nat.add_assoc]
  have hDupPlain :
      Source.stepAtResult
          (pre ++ duplicate ::
            (.push probe :: .prim .eq :: .jumpi label :: post))
          pre.byteLength duplicate start =
        .ok (.running afterDup) := by
    have hWhole :=
      source_stepResult_local
        (instr := duplicate) (pre := pre)
        (post := .push probe :: .prim .eq :: .jumpi label :: post)
        (state := start) (final := afterDup)
        (dupInstr_sourceLocal (by omega) (by omega))
        (dupInstr_haltKind?_none (by omega) (by omega))
        hFits.1 (by simpa [start] using hPc) hDupStep
    have hWhole' :
        Source.stepResult
            (pre ++ duplicate ::
              (.push probe :: .prim .eq :: .jumpi label :: post))
            start =
          .ok (.running afterDup) := by
      simpa using hWhole
    rw [source_stepResult_at_boundary hFits.1
      (by simpa [start] using hPc)] at hWhole'
    exact hWhole'
  have hDupOpen :
      InteractionSemantics.Source.openStepAtResult
          (pre ++ duplicate ::
            (.push probe :: .prim .eq :: .jumpi label :: post))
          pre.byteLength duplicate start =
        .done (.ok (.running afterDup)) := by
    rw [source_openStepAtResult_eq_done_of_stepAt
      (openStepAt_dupInstr_eq_done (by omega) (by omega))]
    exact congrArg Simulation.Interaction.done hDupPlain
  have hPushPlain :
      Source.stepAtResult
          ((pre ++ [duplicate]) ++
            .push probe :: .prim .eq :: .jumpi label :: post)
          (pre ++ [duplicate]).byteLength (.push probe) afterDup =
        .ok (.running afterPush) := by
    have hWhole :=
      source_stepResult_local
        (instr := Instr.push probe) (pre := pre ++ [duplicate])
        (post := .prim .eq :: .jumpi label :: post)
        (state := afterDup) (final := afterPush)
        (by simp [SourceLocalInstr]) rfl hFits.2.1 hAfterDupPc hPushStep
    have hWhole' :
        Source.stepResult
            ((pre ++ [duplicate]) ++
              .push probe :: .prim .eq :: .jumpi label :: post)
            afterDup =
          .ok (.running afterPush) := by
      simpa using hWhole
    rw [source_stepResult_at_boundary hFits.2.1 hAfterDupPc] at hWhole'
    exact hWhole'
  have hPushOpen :
      InteractionSemantics.Source.openStepAtResult
          ((pre ++ [duplicate]) ++
            .push probe :: .prim .eq :: .jumpi label :: post)
          (pre ++ [duplicate]).byteLength (.push probe) afterDup =
        .done (.ok (.running afterPush)) := by
    rw [source_openStepAtResult_eq_done_of_stepAt (by rfl)]
    exact congrArg Simulation.Interaction.done hPushPlain
  have hEqPlain :
      Source.stepAtResult
          ((pre ++ [duplicate, .push probe]) ++
            .prim .eq :: .jumpi label :: post)
          (pre ++ [duplicate, .push probe]).byteLength
          (.prim .eq) afterPush =
        .ok (.running afterEq) := by
    have hEqFits :
        (pre ++ [duplicate, .push probe]).PCFits := by
      simpa [duplicate, List.append_assoc] using hFits.2.2.1
    have hWhole :=
      source_stepResult_local
        (instr := Instr.prim .eq)
        (pre := pre ++ [duplicate, Instr.push probe])
        (post := .jumpi label :: post)
        (state := afterPush) (final := afterEq)
        (by simp [SourceLocalInstr]) rfl
        hEqFits hAfterPushPc hEqStep
    have hWhole' :
        Source.stepResult
            ((pre ++ [duplicate, .push probe]) ++
              .prim .eq :: .jumpi label :: post)
            afterPush =
          .ok (.running afterEq) := by
      simpa using hWhole
    rw [source_stepResult_at_boundary hEqFits hAfterPushPc] at hWhole'
    exact hWhole'
  have hEqOpen :
      InteractionSemantics.Source.openStepAtResult
          ((pre ++ [duplicate, .push probe]) ++
            .prim .eq :: .jumpi label :: post)
          (pre ++ [duplicate, .push probe]).byteLength
          (.prim .eq) afterPush =
        .done (.ok (.running afterEq)) := by
    rw [source_openStepAtResult_eq_done_of_stepAt
      (source_openStepAt_prim_closed (by rfl) (by decide) (by decide))]
    exact congrArg Simulation.Interaction.done hEqPlain
  have hLabel' :
      ((pre ++ [duplicate, .push probe, .prim .eq]) ++
        .jumpi label :: post).labelPc label = some dest := by
    simpa [duplicate, List.append_assoc] using hLabel
  have hLabelActual :
      (pre ++ duplicate ::
        .push probe :: .prim .eq :: .jumpi label :: post).labelPc label =
          some dest := by
    simpa [List.append_assoc] using hLabel'
  let jumpFinal : EVMState :=
    { afterEq with
      stack := front ++ token :: suffix
      pc :=
        if probe = token then EvmYul.UInt256.ofNat dest
        else Source.jumpiFallthroughPc afterEq }
  have hAfterEqStack :
      afterEq.stack =
        EvmYul.UInt256.eq probe token :: front ++ token :: suffix := by
    simp [afterEq, afterPush, afterDup, start,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hJumpPlain :
      Source.stepAtResult
          ((pre ++ [duplicate, .push probe, .prim .eq]) ++
            .jumpi label :: post)
          (pre ++ [duplicate, .push probe, .prim .eq]).byteLength
          (.jumpi label) afterEq =
        .ok (.running jumpFinal) := by
    simp [Source.stepAtResult, Source.stepAt, hLabelActual, hAfterEqStack,
      EvmYul.Stack.pop, uint256_eq_ne_zero, jumpFinal,
      Instr.haltKind?, Source.invalid, List.append_assoc]
  have hJumpOpen :
      InteractionSemantics.Source.openStepAtResult
          ((pre ++ [duplicate, .push probe, .prim .eq]) ++
            .jumpi label :: post)
          (pre ++ [duplicate, .push probe, .prim .eq]).byteLength
          (.jumpi label) afterEq =
        .done (.ok (.running jumpFinal)) := by
    rw [source_openStepAtResult_eq_done_of_stepAt (by rfl)]
    exact congrArg Simulation.Interaction.done hJumpPlain
  have hDupFlow :
      duplicate.classifyFlowWith continueTransfer start
          (.running afterDup) =
        .next afterDup := by
    let n := front.length
    have hn : n < 16 := by simpa [n] using hBound
    change
      (dupInstr (n + 1)).classifyFlowWith continueTransfer start
          (.running afterDup) =
        .next afterDup
    interval_cases n <;> rfl
  have hPushFlow :
      (Instr.push probe).classifyFlowWith continueTransfer afterDup
          (.running afterPush) =
        .next afterPush := by
    rfl
  have hEqFlow :
      (Instr.prim .eq).classifyFlowWith continueTransfer afterPush
          (.running afterEq) =
        .next afterEq := by
    rfl
  have hJumpFlow :
      (Instr.jumpi label).classifyFlowWith continueTransfer afterEq
          (.running jumpFinal) =
        .next jumpFinal := by
    simp [Instr.classifyFlowWith, hAfterEqStack,
      EvmYul.Stack.pop, hContinue]
  have hFallthroughPc :
      Source.jumpiFallthroughPc afterEq =
        (pre ++
          [duplicate, .push probe, .prim .eq, .jumpi label]).pcAfter := by
    calc
      Source.jumpiFallthroughPc afterEq =
          (afterEq.pc +
            EvmYul.UInt256.ofNat Instr.push32Size) +
            EvmYul.UInt256.ofNat 1 := rfl
      _ =
          ((pre ++ [duplicate, .push probe, .prim .eq]).pcAfter +
            EvmYul.UInt256.ofNat Instr.push32Size) +
            EvmYul.UInt256.ofNat 1 := by
        rw [hAfterEqPc]
      _ =
          (pre ++ [duplicate, .push probe, .prim .eq]).pcAfter +
            (EvmYul.UInt256.ofNat Instr.push32Size +
              EvmYul.UInt256.ofNat 1) := by
        exact UInt256_add_assoc _ _ _
      _ =
          (pre ++ [duplicate, .push probe, .prim .eq]).pcAfter +
            EvmYul.UInt256.ofNat (Instr.push32Size + 1) := by
        rw [UInt256_ofNat_add]
      _ =
          (pre ++
            [duplicate, .push probe, .prim .eq, .jumpi label]).pcAfter := by
        simpa [Instr.byteSize, Instr.jumpSize] using
          (Program.pcAfter_snoc
            (pre ++ [duplicate, .push probe, .prim .eq])
            (.jumpi label)).symm
  have hJumpFinalEq : jumpFinal = final := by
    unfold jumpFinal final
    by_cases hEq : probe = token
    · simp only [hEq, if_true]
      cases state
      simp [afterEq, afterPush, afterDup, start,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
    · simp only [hEq, if_false]
      rw [hFallthroughPc]
      rw [show duplicate = dupInstr (front.length + 1) from rfl]
      cases state
      simp [afterEq, afterPush, afterDup, start,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  dsimp only
  rw [show
    pre ++
        [dupInstr (front.length + 1), .push probe, .prim .eq, .jumpi label] ++
        post =
      pre ++ duplicate :: (.push probe :: .prim .eq :: .jumpi label :: post) by
    simp [duplicate]]
  rw [show fuel + 4 = (fuel + 3) + 1 by omega]
  rw [source_openRunUntilTransferWithPolicy_succ_of_step_running
    continueTransfer (fuel + 3) hFits.1
    (by simpa [start] using hPc) hDupOpen hDupFlow]
  rw [show
    pre ++ duplicate :: (.push probe :: .prim .eq :: .jumpi label :: post) =
      (pre ++ [duplicate]) ++ .push probe :: (.prim .eq :: .jumpi label :: post) by
    simp]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [source_openRunUntilTransferWithPolicy_succ_of_step_running
    continueTransfer (fuel + 2) hFits.2.1 hAfterDupPc
    hPushOpen hPushFlow]
  rw [show
    (pre ++ [duplicate]) ++ .push probe :: (.prim .eq :: .jumpi label :: post) =
      (pre ++ [duplicate, .push probe]) ++ .prim .eq :: (.jumpi label :: post) by
    simp]
  have hEqFits :
      (pre ++ [duplicate, .push probe]).PCFits := by
    simpa [duplicate, List.append_assoc] using hFits.2.2.1
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [source_openRunUntilTransferWithPolicy_succ_of_step_running
    continueTransfer (fuel + 1) hEqFits hAfterPushPc hEqOpen hEqFlow]
  rw [show
    (pre ++ [duplicate, .push probe]) ++ .prim .eq :: (.jumpi label :: post) =
      (pre ++ [duplicate, .push probe, .prim .eq]) ++ .jumpi label :: post by
    simp]
  have hJumpFits :
      (pre ++ [duplicate, .push probe, .prim .eq]).PCFits := by
    simpa [duplicate, List.append_assoc] using hFits.2.2.2.1
  rw [source_openRunUntilTransferWithPolicy_succ_of_step_running
    continueTransfer fuel hJumpFits hAfterEqPc hJumpOpen hJumpFlow]
  rw [hJumpFinalEq]

/--
The straight-line stack shuffle that lifts a buried word consumes exactly its
instruction-list length and then resumes the shared transfer runner.
-/
theorem liftBuriedToTop_openRunUntilTransferWithPolicy
    (continueTransfer : Instr → Bool)
    {front suffix : List Word} {token : Word}
    {pre post : Program} {state : EVMState} (fuel : Nat)
    (hFits : Program.PCFitsFrom pre (liftBuriedToTop front.length))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hBound : front.length ≤ 16) :
    let final : EVMState :=
      { state with
        stack := token :: front ++ suffix
        pc := (pre ++ liftBuriedToTop front.length).pcAfter }
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++ liftBuriedToTop front.length ++ post)
        (fuel + (liftBuriedToTop front.length).length)
        { state with stack := front ++ token :: suffix } =
      InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++ liftBuriedToTop front.length ++ post)
        fuel final := by
  induction front using List.reverseRecOn
      generalizing state suffix token pre post fuel with
  | nil =>
      have hPc' : state.pc = pre.pcAfter := by
        simpa using hPc
      simp [liftBuriedToTop, hPc']
  | append_singleton front last ih =>
      have hSwapBound : front.length + 1 ≤ 16 := by
        simpa [List.length_append] using hBound
      have hFrontBound : front.length ≤ 16 := by omega
      let swap := swapInstr (front.length + 1)
      have hCodeEq :
          liftBuriedToTop (front ++ [last]).length =
            liftBuriedToTop front.length ++ [swap] := by
        simp [liftBuriedToTop, List.length_append, swap]
      have hFitsAppend :
          Program.PCFitsFrom pre
            (liftBuriedToTop front.length ++ [swap]) := by
        simpa [hCodeEq] using hFits
      have hLiftFits :
          Program.PCFitsFrom pre (liftBuriedToTop front.length) :=
        Program.PCFitsFrom.left hFitsAppend
      have hSwapFits :
          Program.PCFitsFrom (pre ++ liftBuriedToTop front.length)
            [swap] :=
        Program.PCFitsFrom.right hFitsAppend
      let mid : EVMState :=
        { state with
          stack := last :: front ++ token :: suffix
          pc := (pre ++ liftBuriedToTop front.length).pcAfter }
      have hLift :=
        ih (state := state) (suffix := token :: suffix) (token := last)
          (pre := pre) (post := [swap] ++ post)
          (fuel := fuel + 1)
          hLiftFits
          (by simpa [List.append_assoc] using hPc)
          hFrontBound
      have hLift' :
          InteractionSemantics.Source.openRunUntilTransferWithPolicy
              continueTransfer
              (pre ++
                liftBuriedToTop (front ++ [last]).length ++ post)
              ((fuel + 1) +
                (liftBuriedToTop front.length).length)
              { state with stack :=
                  (front ++ [last]) ++ token :: suffix } =
            InteractionSemantics.Source.openRunUntilTransferWithPolicy
              continueTransfer
              (pre ++
                liftBuriedToTop (front ++ [last]).length ++ post)
              (fuel + 1) mid := by
        rw [hCodeEq]
        simpa [mid, List.append_assoc] using hLift
      have hCodeLen :
          (liftBuriedToTop (front ++ [last]).length).length =
            (liftBuriedToTop front.length).length + 1 := by
        rw [hCodeEq]
        simp
      rw [show
        fuel + (liftBuriedToTop (front ++ [last]).length).length =
          (fuel + 1) + (liftBuriedToTop front.length).length by
        rw [hCodeLen]
        omega]
      rw [hLift']
      let finalState : EVMState :=
        mid.replaceStackAndIncrPC
          (token :: front ++ [last] ++ suffix)
      have hMidRecord :
          { mid with stack := last :: front ++ [token] ++ suffix } =
            mid := by
        rw [show
          last :: front ++ [token] ++ suffix =
            last :: front ++ token :: suffix by
          simp [List.append_assoc]]
      have hSwapStep :
          Target.stepInstr (targetInstr swap) mid =
            .ok finalState := by
        rw [← hMidRecord]
        rw [show swap = swapInstr (front.length + 1) from rfl]
        rw [swapInstr_step_eq_swap (by omega) hSwapBound]
        exact
          swap_snoc (state := mid) (front := front) (suffix := suffix)
            (top := last) (last := token)
      have hSwapPlain :
          Source.stepAtResult
              ((pre ++ liftBuriedToTop front.length) ++
                swap :: post)
              (pre ++ liftBuriedToTop front.length).byteLength
              swap mid =
            .ok (.running finalState) := by
        have hWhole :=
          source_stepResult_local
            (instr := swap)
            (pre := pre ++ liftBuriedToTop front.length)
            (post := post) (state := mid) (final := finalState)
            (swapInstr_sourceLocal (n := front.length + 1)
              (by omega) hSwapBound)
            (swapInstr_haltKind?_none (n := front.length + 1)
              (by omega) hSwapBound)
            (Program.PCFitsFrom.start hSwapFits)
            (by simp [mid])
            hSwapStep
        have hWhole' :
            Source.stepResult
                ((pre ++ liftBuriedToTop front.length) ++
                  swap :: post)
                mid =
              .ok (.running finalState) := by
          simpa using hWhole
        rw [source_stepResult_at_boundary
          (Program.PCFitsFrom.start hSwapFits)
          (by simp [mid])] at hWhole'
        exact hWhole'
      have hSwapOpen :
          InteractionSemantics.Source.openStepAtResult
              ((pre ++ liftBuriedToTop front.length) ++
                swap :: post)
              (pre ++ liftBuriedToTop front.length).byteLength
              swap mid =
            .done (.ok (.running finalState)) := by
        rw [source_openStepAtResult_eq_done_of_stepAt
          (openStepAt_swapInstr_eq_done
            (n := front.length + 1) (by omega) hSwapBound)]
        exact congrArg Simulation.Interaction.done hSwapPlain
      have hSwapFlow :
          swap.classifyFlowWith continueTransfer mid
              (.running finalState) =
            .next finalState := by
        let n := front.length
        have hn : n < 16 := by omega
        change
          (swapInstr (n + 1)).classifyFlowWith continueTransfer mid
              (.running finalState) =
            .next finalState
        interval_cases n <;> rfl
      have hFinalPc :
          finalState.pc =
            (pre ++
              liftBuriedToTop (front ++ [last]).length).pcAfter := by
        calc
          finalState.pc = mid.pc + EvmYul.UInt256.ofNat 1 := by
            simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          _ =
              (pre ++ liftBuriedToTop front.length).pcAfter +
                EvmYul.UInt256.ofNat 1 := by
            simp [mid]
          _ =
              (pre ++ liftBuriedToTop front.length ++ [swap]).pcAfter := by
            have hSwapByte :
                swap.byteSize = 1 :=
              swapInstr_byteSize (by omega) hSwapBound
            simp [Program.pcAfter, Program.byteLength_append,
              Program.byteLength, hSwapByte, UInt256_ofNat_add,
              Nat.add_assoc]
          _ =
              (pre ++
                liftBuriedToTop (front ++ [last]).length).pcAfter := by
            rw [hCodeEq]
            simp [List.append_assoc]
      let final : EVMState :=
        { state with
          stack := token :: (front ++ [last]) ++ suffix
          pc :=
            (pre ++
              liftBuriedToTop (front ++ [last]).length).pcAfter }
      have hFinalEq : finalState = final := by
        apply state_eq_of_fields
        · simp [finalState, final, mid,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        · exact hFinalPc
        · simp [finalState, final, mid, List.append_assoc,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        · simp [finalState, final, mid,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
      rw [show
        pre ++ liftBuriedToTop (front ++ [last]).length ++ post =
          (pre ++ liftBuriedToTop front.length) ++ swap :: post by
        rw [hCodeEq]
        simp [List.append_assoc]]
      rw [source_openRunUntilTransferWithPolicy_succ_of_step_running
        continueTransfer fuel
        (Program.PCFitsFrom.start hSwapFits)
        (by simp [mid])
        hSwapOpen hSwapFlow]
      rw [hFinalEq]

/--
Removing a buried word consumes the lift sequence and one final `POP`, then
resumes the shared transfer runner with the surrounding stack order restored.
-/
theorem removeBuriedUnder_openRunUntilTransferWithPolicy
    (continueTransfer : Instr → Bool)
    {front suffix : List Word} {token : Word}
    {pre post : Program} {state : EVMState} (fuel : Nat)
    (hFits :
      Program.PCFitsFrom pre (removeBuriedUnder front.length))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hBound : front.length ≤ 16) :
    let final : EVMState :=
      { state with
        stack := front ++ suffix
        pc := (pre ++ removeBuriedUnder front.length).pcAfter }
    InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++ removeBuriedUnder front.length ++ post)
        (fuel + (removeBuriedUnder front.length).length)
        { state with stack := front ++ token :: suffix } =
      InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++ removeBuriedUnder front.length ++ post)
        fuel final := by
  have hLiftFits :
      Program.PCFitsFrom pre (liftBuriedToTop front.length) :=
    Program.PCFitsFrom.left
      (by simpa [removeBuriedUnder, List.append_assoc] using hFits)
  have hPopFits :
      Program.PCFitsFrom
        (pre ++ liftBuriedToTop front.length) [.prim .pop] :=
    Program.PCFitsFrom.right
      (by simpa [removeBuriedUnder, List.append_assoc] using hFits)
  let mid : EVMState :=
    { state with
      stack := token :: front ++ suffix
      pc := (pre ++ liftBuriedToTop front.length).pcAfter }
  have hLift :=
    liftBuriedToTop_openRunUntilTransferWithPolicy
      continueTransfer
      (front := front) (suffix := suffix) (token := token)
      (pre := pre) (post := [.prim .pop] ++ post)
      (state := state) (fuel := fuel + 1)
      hLiftFits hPc hBound
  have hLift' :
      InteractionSemantics.Source.openRunUntilTransferWithPolicy
          continueTransfer
          (pre ++ removeBuriedUnder front.length ++ post)
          ((fuel + 1) + (liftBuriedToTop front.length).length)
          { state with stack := front ++ token :: suffix } =
        InteractionSemantics.Source.openRunUntilTransferWithPolicy
          continueTransfer
          (pre ++ removeBuriedUnder front.length ++ post)
          (fuel + 1) mid := by
    simpa [removeBuriedUnder, mid, List.append_assoc] using hLift
  rw [show
    fuel + (removeBuriedUnder front.length).length =
      (fuel + 1) + (liftBuriedToTop front.length).length by
    simp [removeBuriedUnder]
    omega]
  rw [hLift']
  let finalState : EVMState :=
    mid.replaceStackAndIncrPC (front ++ suffix)
  have hMidRecord :
      { mid with stack := token :: front ++ suffix } = mid := by
    rfl
  have hPopStep :
      Target.stepInstr (targetInstr (.prim .pop)) mid =
        .ok finalState := by
    rw [← hMidRecord]
    exact pop_cons_step
  have hPopPlain :
      Source.stepAtResult
          ((pre ++ liftBuriedToTop front.length) ++
            .prim .pop :: post)
          (pre ++ liftBuriedToTop front.length).byteLength
          (.prim .pop) mid =
        .ok (.running finalState) := by
    have hWhole :=
      source_stepResult_local
        (instr := Instr.prim .pop)
        (pre := pre ++ liftBuriedToTop front.length)
        (post := post) (state := mid) (final := finalState)
        (by simp [SourceLocalInstr]) rfl
        (Program.PCFitsFrom.start hPopFits)
        (by simp [mid])
        hPopStep
    have hWhole' :
        Source.stepResult
            ((pre ++ liftBuriedToTop front.length) ++
              .prim .pop :: post)
            mid =
          .ok (.running finalState) := by
      simpa using hWhole
    rw [source_stepResult_at_boundary
      (Program.PCFitsFrom.start hPopFits)
      (by simp [mid])] at hWhole'
    exact hWhole'
  have hPopOpen :
      InteractionSemantics.Source.openStepAtResult
          ((pre ++ liftBuriedToTop front.length) ++
            .prim .pop :: post)
          (pre ++ liftBuriedToTop front.length).byteLength
          (.prim .pop) mid =
        .done (.ok (.running finalState)) := by
    rw [source_openStepAtResult_eq_done_of_stepAt
      (source_openStepAt_prim_closed (by rfl) (by decide) (by decide))]
    exact congrArg Simulation.Interaction.done hPopPlain
  have hPopFlow :
      (Instr.prim .pop).classifyFlowWith continueTransfer mid
          (.running finalState) =
        .next finalState := by
    rfl
  have hFinalPc :
      finalState.pc =
        (pre ++ removeBuriedUnder front.length).pcAfter := by
    calc
      finalState.pc = mid.pc + EvmYul.UInt256.ofNat 1 := by
        simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ =
          (pre ++ liftBuriedToTop front.length).pcAfter +
            EvmYul.UInt256.ofNat 1 := by
        simp [mid]
      _ =
          (pre ++ liftBuriedToTop front.length ++
            [Instr.prim .pop]).pcAfter := by
        simp [Program.pcAfter, Program.byteLength_append,
          Program.byteLength, Instr.byteSize, UInt256_ofNat_add,
          Nat.add_assoc]
      _ = (pre ++ removeBuriedUnder front.length).pcAfter := by
        simp [removeBuriedUnder, List.append_assoc]
  let final : EVMState :=
    { state with
      stack := front ++ suffix
      pc := (pre ++ removeBuriedUnder front.length).pcAfter }
  have hFinalEq : finalState = final := by
    apply state_eq_of_fields
    · simp [finalState, final, mid,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
    · exact hFinalPc
    · simp [finalState, final, mid,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
    · simp [finalState, final, mid,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC]
  rw [show
    pre ++ removeBuriedUnder front.length ++ post =
      (pre ++ liftBuriedToTop front.length) ++
        Instr.prim .pop :: post by
    simp [removeBuriedUnder, List.append_assoc]]
  rw [source_openRunUntilTransferWithPolicy_succ_of_step_running
    continueTransfer fuel
    (Program.PCFitsFrom.start hPopFits)
    (by simp [mid])
    hPopOpen hPopFlow]
  rw [hFinalEq]

end InteractionPreservation
end StackShuffle
end Assembly
end EvmCompiler
