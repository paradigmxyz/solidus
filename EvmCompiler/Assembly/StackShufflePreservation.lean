import EvmCompiler.Assembly.StackShuffle
import Mathlib.Tactic.IntervalCases

namespace EvmCompiler
namespace Assembly
namespace StackShuffle

def targetInstr : Instr → TargetInstr
  | .prim op => .prim op
  | .push value => .push32 value
  | .label _ => .jumpdest
  | .jump _ | .jumpi _ => .prim .invalid

def SourceLocalInstr : Instr → Prop
  | .jump _ | .jumpi _ => False
  | _ => True

theorem source_stepAt_eq_targetInstr {instr : Instr}
    (hLocal : SourceLocalInstr instr)
    {program : Program} {pc : Nat} {state : EVMState} :
    Source.stepAt program pc instr state =
      Target.stepInstr (targetInstr instr) state := by
  cases instr with
  | label _ => rfl
  | prim _ => rfl
  | push _ => rfl
  | jump _ => cases hLocal
  | jumpi _ => cases hLocal

theorem source_stepResult_local {instr : Instr}
    {pre post : Program} {state final : EVMState}
    (hLocal : SourceLocalInstr instr)
    (hNoHalt : instr.haltKind? = none)
    (hFit : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hStep : Target.stepInstr (targetInstr instr) state = .ok final) :
    Source.stepResult (pre ++ [instr] ++ post) state =
      .ok (.running final) := by
  unfold Source.stepResult
  have hAt :
      Program.instrAtPc (pre ++ [instr] ++ post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Program.instrAtPc
    rw [hPc, hFit]
    simpa using
      Program.instrAtPcFrom_append_boundary_cons pre post instr 0
  rw [hAt]
  simp [Source.stepAtResult, source_stepAt_eq_targetInstr hLocal,
    hStep, hNoHalt, Bind.bind, Except.bind]

theorem swapInstr_step_eq_swap {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) (state : EVMState) :
    Target.stepInstr (targetInstr (swapInstr n)) state =
      EvmYul.swap n state := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> rfl

theorem dupInstr_step_eq_dup {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) (state : EVMState) :
    Target.stepInstr (targetInstr (dupInstr n)) state =
      EvmYul.dup n state := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> rfl

theorem swapInstr_sourceLocal {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    SourceLocalInstr (swapInstr n) := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> simp [swapInstr, SourceLocalInstr]

theorem dupInstr_sourceLocal {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    SourceLocalInstr (dupInstr n) := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> simp [dupInstr, SourceLocalInstr]

theorem swapInstr_haltKind?_none {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    (swapInstr n).haltKind? = none := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> rfl

theorem dupInstr_haltKind?_none {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    (dupInstr n).haltKind? = none := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> rfl

theorem swapInstr_byteSize {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    (swapInstr n).byteSize = 1 := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> rfl

theorem dupInstr_byteSize {n : Nat}
    (hOne : 1 ≤ n) (hBound : n ≤ 16) :
    (dupInstr n).byteSize = 1 := by
  have hCases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨
      n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨
      n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hCases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst n <;> rfl

theorem swap_snoc {state : EVMState} {front suffix : List Word}
    {top last : Word} :
    EvmYul.swap (front.length + 1)
        { state with stack := top :: front ++ [last] ++ suffix } =
      .ok (EvmYul.EVM.State.replaceStackAndIncrPC
        { state with stack := top :: front ++ [last] ++ suffix }
        (last :: front ++ [top] ++ suffix)) := by
  have hTake :
      List.take (front.length + 1) (front ++ last :: suffix) =
        front ++ [last] := by
    simpa [List.length_append] using
      (List.take_left (l₁ := front ++ [last]) (l₂ := suffix))
  have hDrop :
      List.drop (front.length + 1) (front ++ last :: suffix) =
        suffix := by
    simpa [List.length_append] using
      (List.drop_left (l₁ := front ++ [last]) (l₂ := suffix))
  have hLast :
      (top :: (front ++ [last])).getLast?.getD default = last := by
    have hLast? : (top :: (front ++ [last])).getLast? = some last := by
      simpa using (List.getLast?_concat (l := top :: front) (a := last))
    simp [hLast?]
  have hDropLast : (front ++ [last]).dropLast = front := by
    simpa using (List.dropLast_concat (l₁ := front) (b := last))
  simp [EvmYul.swap, hTake, hDrop, hLast, hDropLast,
    List.length_append, List.append_assoc]

theorem dup_append_token {state : EVMState} {front suffix : List Word}
    {token : Word} :
    EvmYul.dup (front.length + 1)
        { state with stack := front ++ [token] ++ suffix } =
      .ok (EvmYul.EVM.State.replaceStackAndIncrPC
        { state with stack := front ++ [token] ++ suffix }
        (token :: front ++ [token] ++ suffix)) := by
  have hTake :
      List.take (front.length + 1) (front ++ token :: suffix) =
        front ++ [token] := by
    simpa [List.length_append] using
      (List.take_left (l₁ := front ++ [token]) (l₂ := suffix))
  simp [EvmYul.dup, hTake, List.length_append, List.append_assoc]

theorem uint256_eq_ne_zero (left right : Word) :
    (EvmYul.UInt256.eq left right != EvmYul.UInt256.ofNat 0) =
      decide (left = right) := by
  have hOne :
      (EvmYul.UInt256.ofNat 1 != EvmYul.UInt256.ofNat 0) = true := by
    simp [bne, EvmYul.instBEqUInt256, EvmYul.instBEqUInt256.beq,
      EvmYul.UInt256.ofNat, Id.run]
    unfold EvmYul.UInt256.size
    omega
  have hZero :
      (EvmYul.UInt256.ofNat 0 != EvmYul.UInt256.ofNat 0) = false := by
    simp [bne, EvmYul.instBEqUInt256, EvmYul.instBEqUInt256.beq,
      EvmYul.UInt256.ofNat, Id.run]
  by_cases hEq : left = right
  · subst right
    simp [EvmYul.UInt256.eq, hOne]
  · simp [EvmYul.UInt256.eq, hEq, hZero]

theorem dispatchCondition_source_exists {state : EVMState}
    {front suffix : List Word} {token probe : Word}
    {pre post : Program}
    (hFits :
      Program.PCFitsFrom pre
        [dupInstr (front.length + 1), .push probe, .prim .eq])
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hBound : front.length < 16) :
    Source.Eventually
      (pre ++ [dupInstr (front.length + 1), .push probe, .prim .eq] ++ post)
      { state with stack := front ++ token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                EvmYul.UInt256.eq probe token :: front ++ token :: suffix ∧
              eraseControl final =
                eraseControl
                  { state with stack :=
                      EvmYul.UInt256.eq probe token ::
                        front ++ token :: suffix } ∧
              final.pc =
                (pre ++
                  [dupInstr (front.length + 1), .push probe, .prim .eq]).pcAfter
        | _ => False) := by
  let duplicate := dupInstr (front.length + 1)
  let start : EVMState :=
    { state with stack := front ++ token :: suffix }
  let afterDup : EVMState :=
    start.replaceStackAndIncrPC (token :: front ++ token :: suffix)
  let afterPush : EVMState :=
    afterDup.replaceStackAndIncrPC
      (probe :: token :: front ++ token :: suffix) (pcΔ := 33)
  let finalState : EVMState :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.eq probe token :: front ++ token :: suffix)
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
        .ok finalState := by
    simp [targetInstr, finalState, afterPush, afterDup,
      Target.stepInstr, PrimOp.step, PrimOp.continuingStep?,
      PrimStep.run, EvmYul.EVM.execBinOp, EvmYul.Stack.push,
      EvmYul.Stack.pop2, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hDupByte : duplicate.byteSize = 1 :=
    dupInstr_byteSize (by omega) (by omega)
  have hAfterDupPc : afterDup.pc = (pre ++ [duplicate]).pcAfter := by
    have hPcState : state.pc = pre.pcAfter := by simpa [start] using hPc
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
  have hDupSource :
      Source.stepResult
          (pre ++ [duplicate] ++
            ([Instr.push probe, Instr.prim .eq] ++ post))
          start =
        .ok (.running afterDup) := by
    exact source_stepResult_local
      (instr := duplicate) (pre := pre)
      (post := [Instr.push probe, Instr.prim .eq] ++ post)
      (state := start) (final := afterDup)
      (dupInstr_sourceLocal (by omega) (by omega))
      (dupInstr_haltKind?_none (by omega) (by omega))
      hFits.1 (by simpa [start] using hPc) hDupStep
  have hPushSource :
      Source.stepResult
          (pre ++ [duplicate] ++
            ([Instr.push probe, Instr.prim .eq] ++ post))
          afterDup =
        .ok (.running afterPush) := by
    simpa [List.append_assoc] using
      (source_stepResult_local
        (instr := Instr.push probe) (pre := pre ++ [duplicate])
        (post := [Instr.prim .eq] ++ post)
        (state := afterDup) (final := afterPush)
        (by simp [SourceLocalInstr]) rfl hFits.2.1 hAfterDupPc hPushStep)
  have hEqSource :
      Source.stepResult
          (pre ++ [duplicate] ++
            ([Instr.push probe, Instr.prim .eq] ++ post))
          afterPush =
        .ok (.running finalState) := by
    simpa [List.append_assoc] using
      (source_stepResult_local
        (instr := Instr.prim .eq)
        (pre := pre ++ [duplicate, Instr.push probe])
        (post := post) (state := afterPush) (final := finalState)
        (by simp [SourceLocalInstr]) rfl
        (by simpa [duplicate, List.append_assoc] using hFits.2.2.1)
        hAfterPushPc hEqStep)
  refine ⟨3, .ok (.running finalState), ?_, ?_⟩
  · unfold Source.runNResult
    rw [show
      pre ++ [dupInstr (front.length + 1), .push probe, .prim .eq] ++ post =
        pre ++ [duplicate] ++ ([.push probe, .prim .eq] ++ post) by
      simp [duplicate, List.append_assoc]]
    change
      (do
        let result ←
          Source.stepResult
            (pre ++ [duplicate] ++
              ([Instr.push probe, Instr.prim .eq] ++ post))
            start
        match result with
        | .running state' =>
            Source.runNResult
              (pre ++ [duplicate] ++
                ([Instr.push probe, Instr.prim .eq] ++ post))
              2 state'
        | .halted halt => .ok (.halted halt)) =
        .ok (.running finalState)
    rw [hDupSource]
    simp only [Bind.bind, Except.bind]
    unfold Source.runNResult
    rw [hPushSource]
    simp only [Bind.bind, Except.bind]
    unfold Source.runNResult
    rw [hEqSource]
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp [finalState, afterPush, afterDup,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
    · simp [finalState, afterPush, afterDup, start, eraseControl, eraseGas,
        EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC]
    · calc
        finalState.pc = afterPush.pc + EvmYul.UInt256.ofNat 1 := by
          simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC]
        _ =
            (pre ++ [duplicate, .push probe]).pcAfter +
              EvmYul.UInt256.ofNat 1 := by rw [hAfterPushPc]
        _ =
            EvmYul.UInt256.ofNat
              ((pre ++ [duplicate, .push probe]).byteLength + 1) := by
          rw [Program.pcAfter, UInt256_ofNat_add]
        _ =
            (pre ++ [duplicate, .push probe, .prim .eq]).pcAfter := by
          simp [Program.pcAfter, Program.byteLength_append,
            Program.byteLength, Instr.byteSize, Nat.add_assoc]
        _ =
            (pre ++ [dupInstr (front.length + 1), .push probe, .prim .eq]).pcAfter := by
          rfl

theorem dispatchTest_source_exists {state : EVMState}
    {front suffix : List Word} {token probe : Word}
    {label : Label} {dest : Nat} {pre post : Program}
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
    Source.Eventually
      (pre ++
        [dupInstr (front.length + 1), .push probe, .prim .eq, .jumpi label] ++
        post)
      { state with stack := front ++ token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack = front ++ token :: suffix ∧
              eraseControl final =
                eraseControl { state with stack := front ++ token :: suffix } ∧
              final.pc =
                if probe = token then EvmYul.UInt256.ofNat dest
                else
                  (pre ++
                    [dupInstr (front.length + 1), .push probe, .prim .eq,
                      .jumpi label]).pcAfter
        | _ => False) := by
  let conditionCode : Program :=
    [dupInstr (front.length + 1), .push probe, .prim .eq]
  have hFitsCond : Program.PCFitsFrom pre conditionCode :=
    Program.PCFitsFrom.left
      (by simpa [conditionCode] using hFits)
  have hFitsJump :
      Program.PCFitsFrom (pre ++ conditionCode) [.jumpi label] :=
    Program.PCFitsFrom.right
      (by simpa [conditionCode] using hFits)
  have hCondition :=
    dispatchCondition_source_exists
      (state := state) (front := front) (suffix := suffix)
      (token := token) (probe := probe) (pre := pre)
      (post := [.jumpi label] ++ post)
      (by simpa [conditionCode] using hFitsCond) hPc hBound
  refine
    Source.Eventually.bind_running
      (program :=
        pre ++
          [dupInstr (front.length + 1), .push probe, .prim .eq, .jumpi label] ++
          post)
      (middle := fun mid =>
        mid.stack =
            EvmYul.UInt256.eq probe token :: front ++ token :: suffix ∧
          eraseControl mid =
            eraseControl
              { state with stack :=
                  EvmYul.UInt256.eq probe token :: front ++ token :: suffix } ∧
          mid.pc = (pre ++ conditionCode).pcAfter)
      ?_ ?_
  · exact Source.Eventually.mono
      (by simpa [conditionCode, List.append_assoc] using hCondition)
      (by
        intro outcome hResult
        cases outcome with
        | error err => cases hResult
        | ok result =>
            cases result with
            | halted halt => cases hResult
            | running mid =>
                rcases hResult with ⟨hStack, hErase, hPcMid⟩
                exact ⟨hStack, hErase, by simpa [conditionCode] using hPcMid⟩)
  · intro mid hMid
    let final : EVMState :=
      { mid with
        stack := front ++ token :: suffix
        pc :=
          if probe = token then EvmYul.UInt256.ofNat dest
          else Source.jumpiFallthroughPc mid }
    have hMidStack :
        mid.stack =
          EvmYul.UInt256.eq probe token :: front ++ token :: suffix :=
      hMid.1
    have hLabel' :
        ((pre ++ conditionCode) ++ [Instr.jumpi label] ++ post).labelPc label =
          some dest := by
      simpa [conditionCode, List.append_assoc] using hLabel
    have hLabel'' :
        (pre ++ (conditionCode ++ Instr.jumpi label :: post)).labelPc label =
          some dest := by
      simpa [List.append_assoc] using hLabel'
    have hStep :
        Source.stepResult
            ((pre ++ conditionCode) ++ [Instr.jumpi label] ++ post) mid =
          .ok (.running final) := by
      unfold Source.stepResult
      have hAt :
          Program.instrAtPc
              ((pre ++ conditionCode) ++ [Instr.jumpi label] ++ post)
              mid.pc.toNat =
            some ((pre ++ conditionCode).byteLength, Instr.jumpi label) := by
        unfold Program.instrAtPc
        rw [hMid.2.2, Program.PCFitsFrom.start hFitsJump]
        simpa using
          Program.instrAtPcFrom_append_boundary_cons
            (pre ++ conditionCode) post (Instr.jumpi label) 0
      rw [hAt]
      simp [Source.stepAtResult, Source.stepAt, hLabel'', hMidStack,
        EvmYul.Stack.pop, uint256_eq_ne_zero, final,
        Instr.haltKind?, Source.invalid, List.append_assoc]
    refine ⟨1, .ok (.running final), ?_, ?_⟩
    · unfold Source.runNResult
      rw [show
        pre ++
            [dupInstr (front.length + 1), .push probe, .prim .eq,
              .jumpi label] ++ post =
          (pre ++ conditionCode) ++ [.jumpi label] ++ post by
        simp [conditionCode, List.append_assoc]]
      rw [hStep]
      rfl
    · refine ⟨?_, ?_, ?_⟩
      · simp [final]
      · calc
          eraseControl final =
              eraseControl { mid with stack := front ++ token :: suffix } := by
            simp [final, eraseControl, eraseGas]
          _ =
              eraseControl { state with stack := front ++ token :: suffix } := by
            simpa using
              (eraseControl_with_stack_congr
                (left := mid)
                (right :=
                  { state with stack :=
                      EvmYul.UInt256.eq probe token ::
                        front ++ token :: suffix })
                (stack := front ++ token :: suffix)
                hMid.2.1)
      · by_cases hEq : probe = token
        · simp [final, hEq]
        · have hDupByte :
              (dupInstr (front.length + 1)).byteSize = 1 :=
            dupInstr_byteSize (n := front.length + 1) (by omega) (by omega)
          simp [final, hEq, Source.jumpiFallthroughPc, hMid.2.2,
            conditionCode, Program.pcAfter, Program.byteLength_append,
            Program.byteLength, Instr.byteSize, Instr.push32Size,
            Instr.jumpSize, hDupByte, UInt256_ofNat_add, Nat.add_assoc]

theorem liftBuriedToTop_source_exists {state : EVMState}
    {front suffix : List Word} {token : Word}
    {pre post : Program}
    (hFits : Program.PCFitsFrom pre (liftBuriedToTop front.length))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hBound : front.length ≤ 16) :
    Source.Eventually
      (pre ++ liftBuriedToTop front.length ++ post)
      { state with stack := front ++ token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack = token :: front ++ suffix ∧
              eraseControl final =
                eraseControl { state with stack := token :: front ++ suffix } ∧
              final.pc = (pre ++ liftBuriedToTop front.length).pcAfter
        | _ => False) := by
  induction front using List.reverseRecOn generalizing state suffix token pre post with
  | nil =>
      exact Source.Eventually.pure (by simpa [liftBuriedToTop] using hPc)
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
          Program.PCFitsFrom (pre ++ liftBuriedToTop front.length) [swap] :=
        Program.PCFitsFrom.right hFitsAppend
      have hLift :=
        ih (state := state) (suffix := token :: suffix) (token := last)
          (pre := pre) (post := [swap] ++ post)
          hLiftFits
          (by simpa [List.append_assoc] using hPc)
          hFrontBound
      refine
        Source.Eventually.bind_running
          (program := pre ++ liftBuriedToTop (front ++ [last]).length ++ post)
          (middle := fun targetAfterLift =>
            targetAfterLift.stack = last :: front ++ token :: suffix ∧
              eraseControl targetAfterLift =
                eraseControl { state with stack := last :: front ++ token :: suffix } ∧
              targetAfterLift.pc =
                (pre ++ liftBuriedToTop front.length).pcAfter)
          ?_ ?_
      · exact Source.Eventually.mono
          (by
            rw [hCodeEq]
            simpa [List.append_assoc] using hLift)
          (by
            intro outcome hResult
            cases outcome with
            | error err => cases hResult
            | ok result =>
                cases result with
                | halted halt => cases hResult
                | running mid =>
                    rcases hResult with ⟨hStack, hErase, hPcMid⟩
                    exact ⟨by simpa [List.append_assoc] using hStack,
                      by simpa [List.append_assoc] using hErase, hPcMid⟩)
      · intro mid hMid
        have hMidRecord :
            { mid with stack := last :: front ++ [token] ++ suffix } = mid := by
          rw [show last :: front ++ [token] ++ suffix =
              last :: front ++ token :: suffix by simp [List.append_assoc]]
          rw [← hMid.1]
        let finalState : EVMState :=
          mid.replaceStackAndIncrPC (token :: front ++ [last] ++ suffix)
        have hStep :
            Target.stepInstr (targetInstr swap) mid = .ok finalState := by
          rw [← hMidRecord]
          rw [show swap = swapInstr (front.length + 1) from rfl]
          rw [swapInstr_step_eq_swap (by omega) hSwapBound]
          exact swap_snoc (state := mid) (front := front) (suffix := suffix)
            (top := last) (last := token)
        refine ⟨1, .ok (.running finalState), ?_, ?_⟩
        · rw [show
            pre ++ liftBuriedToTop (front ++ [last]).length ++ post =
              (pre ++ liftBuriedToTop front.length) ++ [swap] ++ post by
              rw [hCodeEq]
              simp [List.append_assoc]]
          unfold Source.runNResult
          rw [source_stepResult_local
            (instr := swap)
            (pre := pre ++ liftBuriedToTop front.length)
            (post := post) (state := mid) (final := finalState)
            (swapInstr_sourceLocal (n := front.length + 1) (by omega)
              hSwapBound)
            (swapInstr_haltKind?_none (n := front.length + 1) (by omega)
              hSwapBound)
            (Program.PCFitsFrom.start hSwapFits)
            hMid.2.2 hStep]
          rfl
        · refine ⟨?_, ?_, ?_⟩
          · simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC, List.append_assoc]
          · calc
              eraseControl finalState =
                  eraseControl
                    { mid with stack := token :: front ++ [last] ++ suffix } := by
                simp [finalState, eraseControl, eraseGas,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
              _ =
                  eraseControl
                    { state with stack := token :: front ++ [last] ++ suffix } := by
                simpa [List.append_assoc] using
                  (eraseControl_with_stack_congr
                    (left := mid)
                    (right :=
                      { state with stack := last :: front ++ token :: suffix })
                    (stack := token :: front ++ [last] ++ suffix)
                    hMid.2.1)
          · calc
              finalState.pc = mid.pc + EvmYul.UInt256.ofNat 1 := by
                simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC]
              _ =
                  (pre ++ liftBuriedToTop front.length).pcAfter +
                    EvmYul.UInt256.ofNat 1 := by rw [hMid.2.2]
              _ =
                  EvmYul.UInt256.ofNat
                    ((pre ++ liftBuriedToTop front.length).byteLength + 1) := by
                rw [Program.pcAfter, UInt256_ofNat_add]
              _ = (pre ++ liftBuriedToTop front.length ++ [swap]).pcAfter := by
                have hSwapByte : swap.byteSize = 1 := by
                  exact swapInstr_byteSize (by omega) hSwapBound
                simp [Program.pcAfter, Program.byteLength_append,
                  Program.byteLength, hSwapByte, Nat.add_assoc]
              _ = (pre ++ liftBuriedToTop (front ++ [last]).length).pcAfter := by
                rw [hCodeEq]
                simp [List.append_assoc]

theorem pop_cons_step {state : EVMState} {top : Word}
    {suffix : List Word} :
    Target.stepInstr (.prim .pop) { state with stack := top :: suffix } =
      .ok (({ state with stack := top :: suffix }).replaceStackAndIncrPC suffix) :=
  rfl

theorem removeBuriedUnder_source_exists {state : EVMState}
    {front suffix : List Word} {token : Word}
    {pre post : Program}
    (hFits : Program.PCFitsFrom pre (removeBuriedUnder front.length))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hBound : front.length ≤ 16) :
    Source.Eventually
      (pre ++ removeBuriedUnder front.length ++ post)
      { state with stack := front ++ token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack = front ++ suffix ∧
              eraseControl final =
                eraseControl { state with stack := front ++ suffix } ∧
              final.pc = (pre ++ removeBuriedUnder front.length).pcAfter
        | _ => False) := by
  have hFitsLift :
      Program.PCFitsFrom pre (liftBuriedToTop front.length) :=
    Program.PCFitsFrom.left
      (by simpa [removeBuriedUnder, List.append_assoc] using hFits)
  have hFitsPop :
      Program.PCFitsFrom (pre ++ liftBuriedToTop front.length) [.prim .pop] :=
    Program.PCFitsFrom.right
      (by simpa [removeBuriedUnder, List.append_assoc] using hFits)
  have hLift :=
    liftBuriedToTop_source_exists
      (state := state) (front := front) (suffix := suffix)
      (token := token) (pre := pre) (post := [.prim .pop] ++ post)
      hFitsLift hPc hBound
  refine
    Source.Eventually.bind_running
      (program := pre ++ removeBuriedUnder front.length ++ post)
      (middle := fun mid =>
        mid.stack = token :: front ++ suffix ∧
          eraseControl mid =
            eraseControl { state with stack := token :: front ++ suffix } ∧
          mid.pc = (pre ++ liftBuriedToTop front.length).pcAfter)
      ?_ ?_
  · exact Source.Eventually.mono
      (by simpa [removeBuriedUnder, List.append_assoc] using hLift)
      (by
        intro outcome hResult
        cases outcome with
        | error err => cases hResult
        | ok result =>
            cases result with
            | halted halt => cases hResult
            | running mid => exact hResult)
  · intro mid hMid
    have hMidRecord :
        { mid with stack := token :: front ++ suffix } = mid := by
      rw [← hMid.1]
    let finalState : EVMState :=
      mid.replaceStackAndIncrPC (front ++ suffix)
    have hPopStep :
        Target.stepInstr (targetInstr (.prim .pop)) mid = .ok finalState := by
      rw [← hMidRecord]
      exact pop_cons_step (state := mid) (top := token)
        (suffix := front ++ suffix)
    refine ⟨1, .ok (.running finalState), ?_, ?_⟩
    · rw [show
        pre ++ removeBuriedUnder front.length ++ post =
          (pre ++ liftBuriedToTop front.length) ++ [.prim .pop] ++ post by
          simp [removeBuriedUnder, List.append_assoc]]
      unfold Source.runNResult
      rw [source_stepResult_local
        (instr := .prim .pop)
        (pre := pre ++ liftBuriedToTop front.length)
        (post := post) (state := mid) (final := finalState)
        (by simp [SourceLocalInstr]) rfl
        (Program.PCFitsFrom.start hFitsPop)
        hMid.2.2 hPopStep]
      rfl
    · refine ⟨?_, ?_, ?_⟩
      · simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · calc
          eraseControl finalState =
              eraseControl { mid with stack := front ++ suffix } := by
            simp [finalState, eraseControl, eraseGas,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          _ = eraseControl { state with stack := front ++ suffix } :=
            by
              simpa using
                (eraseControl_with_stack_congr
                  (left := mid)
                  (right :=
                    { state with stack := token :: front ++ suffix })
                  (stack := front ++ suffix)
                  hMid.2.1)
      · calc
          finalState.pc = mid.pc + EvmYul.UInt256.ofNat 1 := by
            simp [finalState, EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC]
          _ =
              (pre ++ liftBuriedToTop front.length).pcAfter +
                EvmYul.UInt256.ofNat 1 := by rw [hMid.2.2]
          _ =
              EvmYul.UInt256.ofNat
                ((pre ++ liftBuriedToTop front.length).byteLength + 1) := by
            rw [Program.pcAfter, UInt256_ofNat_add]
          _ = (pre ++ removeBuriedUnder front.length).pcAfter := by
            simp [removeBuriedUnder, Program.pcAfter,
              Program.byteLength_append, Program.byteLength, Instr.byteSize,
              Nat.add_assoc]

end StackShuffle
end Assembly
end EvmCompiler
