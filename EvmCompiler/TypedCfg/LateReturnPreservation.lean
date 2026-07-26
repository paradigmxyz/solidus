import EvmCompiler.TypedCfg.LateReturnProbe
import EvmCompiler.TypedCfg.ReturnAddressExecution

namespace EvmCompiler
namespace TypedCfg
namespace LateReturnPreservation

open ReturnAddressPreservation

def selectedAddress (resolve : Assembly.Label → Option Nat)
    (token : Word) (site : ReturnSite) : Word :=
  if site.token = token then
    match resolve site.target with
    | some dest => EvmYul.UInt256.ofNat dest
    | none => EvmYul.UInt256.ofNat 0
  else
    EvmYul.UInt256.ofNat 0

theorem uint256_mul_one (value : Word) :
    EvmYul.UInt256.mul value (EvmYul.UInt256.ofNat 1) = value := by
  rcases value with ⟨value⟩
  change EvmYul.UInt256.mk
      (value * Fin.ofNat EvmYul.UInt256.size 1) =
    EvmYul.UInt256.mk value
  congr 1
  exact Fin.mul_one value

theorem uint256_mul_zero (value : Word) :
    EvmYul.UInt256.mul value (EvmYul.UInt256.ofNat 0) =
      EvmYul.UInt256.ofNat 0 := by
  rcases value with ⟨value⟩
  change EvmYul.UInt256.mk
      (value * Fin.ofNat EvmYul.UInt256.size 0) =
    EvmYul.UInt256.mk (Fin.ofNat EvmYul.UInt256.size 0)
  congr 1

theorem mul_eq_selectedAddress
    (resolve : Assembly.Label → Option Nat)
    (token : Word) (site : ReturnSite) {dest : Nat}
    (hResolve : resolve site.target = some dest) :
    EvmYul.UInt256.mul
        (EvmYul.UInt256.ofNat dest)
        (EvmYul.UInt256.eq site.token token) =
      selectedAddress resolve token site := by
  by_cases hToken : site.token = token
  · subst token
    simpa [selectedAddress, hResolve, EvmYul.UInt256.eq] using
      uint256_mul_one (EvmYul.UInt256.ofNat dest)
  · simpa [selectedAddress, hResolve, EvmYul.UInt256.eq, hToken] using
      uint256_mul_zero (EvmYul.UInt256.ofNat dest)

theorem pushLabelMul_source_run
    {state : Assembly.EVMState}
    {condition : Word} {suffix : List Word}
    {label : Label} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul])
    (hPc :
      ({ state with stack := condition :: suffix }).pc =
        pre.pcAfter)
    (hLabel :
      (pre ++
          [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
        post).labelPc label = some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
            post)
          2 { state with stack := condition :: suffix } =
        .ok (.running final) ∧
      final.stack =
          EvmYul.UInt256.mul
              (EvmYul.UInt256.ofNat dest) condition ::
            suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              EvmYul.UInt256.mul
                  (EvmYul.UInt256.ofNat dest) condition ::
                suffix } ∧
      final.pc =
        (pre ++
          [Assembly.Instr.pushLabel label,
            Assembly.Instr.prim .mul]).pcAfter := by
  let start : Assembly.EVMState :=
    { state with stack := condition :: suffix }
  let afterPush : Assembly.EVMState :=
    start.replaceStackAndIncrPC
      (EvmYul.UInt256.ofNat dest :: condition :: suffix)
      (pcΔ := Assembly.Instr.push32Size)
  let final : Assembly.EVMState :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.mul
          (EvmYul.UInt256.ofNat dest) condition :: suffix)
  have hPushFits : pre.PCFits :=
    Assembly.Program.PCFitsFrom.start hFits
  have hAfterPushFits :
      (pre ++ [Assembly.Instr.pushLabel label]).PCFits :=
    Assembly.Program.PCFitsFrom.start
      (by
        simpa [List.append_assoc] using
          (Assembly.Program.PCFitsFrom.right hFits))
  have hLabel' :
      (pre ++ Assembly.Instr.pushLabel label ::
          Assembly.Instr.prim .mul :: post).labelPc label =
        some dest := by
    simpa [List.append_assoc] using hLabel
  have hPushRun :
      Assembly.Source.runNResult
          (pre ++
            [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
            post)
          1 start =
        .ok (.running afterPush) := by
    rw [show
      pre ++
          [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
          post =
        pre ++ Assembly.Instr.pushLabel label ::
          (Assembly.Instr.prim .mul :: post) by
      simp [List.append_assoc]]
    rw [
      Assembly.InteractionPreservation.source_runNResult_one_at_boundary
        hPushFits (by simpa [start] using hPc)]
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt, hLabel',
      afterPush, start, Assembly.Target.stepInstr,
      Assembly.Target.stepInstrWith, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Assembly.Instr.haltKind?,
      Assembly.Instr.push32Size]
  have hAfterPushPc :
      afterPush.pc =
        (pre ++ [Assembly.Instr.pushLabel label]).pcAfter := by
    calc
      afterPush.pc =
          start.pc +
            EvmYul.UInt256.ofNat Assembly.Instr.push32Size := by
        simp [afterPush, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, Assembly.Instr.push32Size]
      _ =
          pre.pcAfter +
            EvmYul.UInt256.ofNat Assembly.Instr.push32Size := by
        rw [show start.pc = pre.pcAfter by simpa [start] using hPc]
      _ =
          EvmYul.UInt256.ofNat
            (pre.byteLength + Assembly.Instr.push32Size) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ = (pre ++ [Assembly.Instr.pushLabel label]).pcAfter := by
        simp [Assembly.Program.pcAfter,
          Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, Assembly.Instr.byteSize]
  have hMulStep :
      Assembly.Target.stepInstr (Assembly.TargetInstr.prim .mul) afterPush =
        .ok final := by
    simp [final, afterPush, start, Assembly.Target.stepInstr,
      Assembly.Target.stepInstrWith, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.push, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hMulRun :
      Assembly.Source.runNResult
          (pre ++
            [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
            post)
          1 afterPush =
        .ok (.running final) := by
    rw [show
      pre ++
          [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
          post =
        (pre ++ [Assembly.Instr.pushLabel label]) ++
          Assembly.Instr.prim .mul :: post by
      simp [List.append_assoc]]
    rw [
      Assembly.InteractionPreservation.source_runNResult_one_at_boundary
        hAfterPushFits hAfterPushPc]
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      hMulStep, Assembly.Instr.haltKind?, Assembly.PrimOp.haltKind?]
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · change
      Assembly.Source.runNResult
          (pre ++
            [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
            post)
          2 start =
        .ok (.running final)
    rw [show 2 = 1 + 1 by omega]
    calc
      Assembly.Source.runNResult
          (pre ++
            [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
            post)
          (1 + 1) start =
          Assembly.Source.runNResult
            (pre ++
              [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
              post)
            1 afterPush :=
        Assembly.Source.runNResult_add_of_running
          (pre ++
            [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
            post)
          1 1 hPushRun
      _ = .ok (.running final) := hMulRun
  · simp [final, afterPush, start,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [final, afterPush, start, Assembly.eraseRuntimeControl,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · calc
      final.pc = afterPush.pc + EvmYul.UInt256.ofNat 1 := by
        simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ =
          (pre ++ [Assembly.Instr.pushLabel label]).pcAfter +
            EvmYul.UInt256.ofNat 1 := by rw [hAfterPushPc]
      _ =
          EvmYul.UInt256.ofNat
            ((pre ++
              [Assembly.Instr.pushLabel label]).byteLength + 1) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ =
          (pre ++
            [Assembly.Instr.pushLabel label,
              Assembly.Instr.prim .mul]).pcAfter := by
        simp [Assembly.Program.pcAfter,
          Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, Assembly.Instr.byteSize,
          Nat.add_assoc]

theorem pushLabelMul_source_exists
    {state : Assembly.EVMState}
    {condition : Word} {suffix : List Word}
    {label : Label} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul])
    (hPc :
      ({ state with stack := condition :: suffix }).pc =
        pre.pcAfter)
    (hLabel :
      (pre ++
          [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++
        post).labelPc label = some dest) :
    Assembly.Source.Eventually
      (pre ++
        [Assembly.Instr.pushLabel label, Assembly.Instr.prim .mul] ++ post)
      { state with stack := condition :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                EvmYul.UInt256.mul
                    (EvmYul.UInt256.ofNat dest) condition ::
                  suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      EvmYul.UInt256.mul
                          (EvmYul.UInt256.ofNat dest) condition ::
                        suffix } ∧
              final.pc =
                (pre ++
                  [Assembly.Instr.pushLabel label,
                    Assembly.Instr.prim .mul]).pcAfter
        | _ => False) := by
  obtain ⟨final, hRun, hStack, hRuntime, hFinalPc⟩ :=
    pushLabelMul_source_run hFits hPc hLabel
  exact
    ⟨2, .ok (.running final), hRun,
      hStack, hRuntime, hFinalPc⟩

theorem add_source_run
    {state : Assembly.EVMState}
    {left right : Word} {suffix : List Word}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre [Assembly.Instr.prim .add])
    (hPc :
      ({ state with stack := left :: right :: suffix }).pc =
        pre.pcAfter) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++ [Assembly.Instr.prim .add] ++ post)
          1 { state with stack := left :: right :: suffix } =
        .ok (.running final) ∧
      final.stack = EvmYul.UInt256.add left right :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack := EvmYul.UInt256.add left right :: suffix } ∧
      final.pc = (pre ++ [Assembly.Instr.prim .add]).pcAfter := by
  let start : Assembly.EVMState :=
    { state with stack := left :: right :: suffix }
  let final : Assembly.EVMState :=
    start.replaceStackAndIncrPC
      (EvmYul.UInt256.add left right :: suffix)
  have hStep :
      Assembly.Target.stepInstr (Assembly.TargetInstr.prim .add) start =
        .ok final := by
    simp [final, start, Assembly.Target.stepInstr,
      Assembly.Target.stepInstrWith, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.push, EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hSourceStep :
      Assembly.Source.stepAt
          (pre ++ Assembly.Instr.prim .add :: post)
          pre.byteLength (Assembly.Instr.prim .add) start =
        .ok final :=
    hStep
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · rw [show
      pre ++ [Assembly.Instr.prim .add] ++ post =
        pre ++ Assembly.Instr.prim .add :: post by simp]
    rw [
      Assembly.InteractionPreservation.source_runNResult_one_at_boundary
        (Assembly.Program.PCFitsFrom.start hFits)
        (by simpa [start] using hPc)]
    change
      (do
        let state' ←
          Assembly.Source.stepAt
            (pre ++ Assembly.Instr.prim .add :: post)
            pre.byteLength (Assembly.Instr.prim .add) start
        Except.ok (Assembly.StepResult.running state')) =
      Except.ok (Assembly.StepResult.running final)
    rw [hSourceStep]
    rfl
  · simp [final, start, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [final, start, Assembly.eraseRuntimeControl,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · calc
      final.pc = start.pc + EvmYul.UInt256.ofNat 1 := by
        simp [final, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ = pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
        rw [show start.pc = pre.pcAfter by simpa [start] using hPc]
      _ = EvmYul.UInt256.ofNat (pre.byteLength + 1) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ = (pre ++ [Assembly.Instr.prim .add]).pcAfter := by
        simp [Assembly.Program.pcAfter,
          Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, Assembly.Instr.byteSize]

theorem add_source_exists
    {state : Assembly.EVMState}
    {left right : Word} {suffix : List Word}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre [Assembly.Instr.prim .add])
    (hPc :
      ({ state with stack := left :: right :: suffix }).pc =
        pre.pcAfter) :
    Assembly.Source.Eventually
      (pre ++ [Assembly.Instr.prim .add] ++ post)
      { state with stack := left :: right :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack = EvmYul.UInt256.add left right :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack := EvmYul.UInt256.add left right :: suffix } ∧
              final.pc = (pre ++ [Assembly.Instr.prim .add]).pcAfter
        | _ => False) := by
  obtain ⟨final, hRun, hStack, hRuntime, hFinalPc⟩ :=
    add_source_run hFits hPc
  exact
    ⟨1, .ok (.running final), hRun,
      hStack, hRuntime, hFinalPc⟩

theorem firstSelection_source_exists
    {state : Assembly.EVMState}
    {token : Word} {suffix : List Word}
    {site : ReturnSite} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (LateReturnProbe.Terminator.firstSelection site))
    (hPc :
      ({ state with stack := token :: suffix }).pc = pre.pcAfter)
    (hLabel :
      (pre ++ LateReturnProbe.Terminator.firstSelection site ++ post).labelPc
          site.target =
        some dest) :
    Assembly.Source.Eventually
      (pre ++ LateReturnProbe.Terminator.firstSelection site ++ post)
      { state with stack := token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                selectedAddress
                    (pre ++
                      LateReturnProbe.Terminator.firstSelection site ++
                      post).labelPc
                    token site ::
                  token :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      selectedAddress
                          (pre ++
                            LateReturnProbe.Terminator.firstSelection site ++
                            post).labelPc
                          token site ::
                        token :: suffix } ∧
              final.pc =
                (pre ++
                  LateReturnProbe.Terminator.firstSelection site).pcAfter
        | _ => False) := by
  let conditionCode : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 1
    , .push site.token
    , .prim .eq
    ]
  let selectCode : Assembly.Program :=
    [.pushLabel site.target, .prim .mul]
  let condition := EvmYul.UInt256.eq site.token token
  let selected :=
    selectedAddress
      (pre ++ LateReturnProbe.Terminator.firstSelection site ++ post).labelPc
      token site
  have hCodeEq :
      LateReturnProbe.Terminator.firstSelection site =
        conditionCode ++ selectCode := by
    simp [LateReturnProbe.Terminator.firstSelection,
      conditionCode, selectCode]
  have hConditionFits :
      Assembly.Program.PCFitsFrom pre conditionCode := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [hCodeEq, List.append_assoc] using hFits
  have hSelectFits :
      Assembly.Program.PCFitsFrom (pre ++ conditionCode) selectCode := by
    have hAll :
        Assembly.Program.PCFitsFrom pre (conditionCode ++ selectCode) := by
      simpa [hCodeEq] using hFits
    exact Assembly.Program.PCFitsFrom.right hAll
  have hCondition :=
    Assembly.StackShuffle.dispatchCondition_source_exists
      (state := state) (front := []) (suffix := suffix)
      (token := token) (probe := site.token)
      (pre := pre) (post := selectCode ++ post)
      (by simpa [conditionCode] using hConditionFits)
      (by simpa using hPc)
      (by simp)
  have hCondition' :
      Assembly.Source.Eventually
        (pre ++ conditionCode ++ selectCode ++ post)
        { state with stack := token :: suffix }
        (fun outcome =>
          match outcome with
          | .ok (.running mid) =>
              mid.stack = condition :: token :: suffix ∧
                Assembly.eraseRuntimeControl mid =
                  Assembly.eraseRuntimeControl
                    { state with stack := condition :: token :: suffix } ∧
                mid.pc = (pre ++ conditionCode).pcAfter
          | _ => False) := by
    simpa [conditionCode, condition, List.append_assoc] using hCondition
  rw [show
    pre ++ LateReturnProbe.Terminator.firstSelection site ++ post =
      pre ++ conditionCode ++ selectCode ++ post by
    simp [hCodeEq, List.append_assoc]]
  apply Assembly.Source.Eventually.bind_running hCondition'
  intro mid hMid
  have hMidRecord :
      { mid with stack := condition :: token :: suffix } = mid := by
    rw [← hMid.1]
  have hLabel' :
      ((pre ++ conditionCode) ++ selectCode ++ post).labelPc
          site.target =
        some dest := by
    simpa [hCodeEq, List.append_assoc] using hLabel
  have hSelectRaw :=
    pushLabelMul_source_exists
      (state := mid) (condition := condition)
      (suffix := token :: suffix)
      (label := site.target) (dest := dest)
      (pre := pre ++ conditionCode) (post := post)
      (by simpa [selectCode] using hSelectFits)
      (by simpa [hMidRecord] using hMid.2.2)
      (by simpa [selectCode, List.append_assoc] using hLabel')
  have hSelected :
      EvmYul.UInt256.mul (EvmYul.UInt256.ofNat dest) condition =
        selected := by
    simpa [condition, selected, hCodeEq, List.append_assoc] using
      (mul_eq_selectedAddress
        (pre ++
          LateReturnProbe.Terminator.firstSelection site ++ post).labelPc
        token site hLabel)
  have hSelectedEq :
      selected =
        selectedAddress
          (pre ++ conditionCode ++ selectCode ++ post).labelPc
          token site := by
    simp [selected, hCodeEq, List.append_assoc]
  rw [hMidRecord] at hSelectRaw
  apply Assembly.Source.Eventually.mono
    (by simpa [selectCode, List.append_assoc] using hSelectRaw)
  intro outcome hOutcome
  cases outcome with
  | error err => cases hOutcome
  | ok result =>
      cases result with
      | halted halt => cases hOutcome
      | running final =>
          rcases hOutcome with
            ⟨hFinalStack, hFinalRuntime, hFinalPc⟩
          refine ⟨?_, ?_, ?_⟩
          · simpa [hSelected, hSelectedEq] using hFinalStack
          · calc
              Assembly.eraseRuntimeControl final =
                  Assembly.eraseRuntimeControl
                    { mid with stack := selected :: token :: suffix } := by
                simpa [hSelected] using hFinalRuntime
              _ =
                  Assembly.eraseRuntimeControl
                    { state with stack := selected :: token :: suffix } := by
                exact
                  Assembly.eraseRuntimeControl_with_stack_congr
                    (left := mid)
                    (right :=
                      { state with stack := condition :: token :: suffix })
                    (stack := selected :: token :: suffix)
                    hMid.2.1
              _ =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack :=
                        selectedAddress
                            (pre ++ conditionCode ++ selectCode ++ post).labelPc
                            token site ::
                          token :: suffix } := by
                rw [hSelectedEq]
          · simpa [hCodeEq, conditionCode, selectCode,
              List.append_assoc] using hFinalPc

theorem firstSelection_source_run
    {state : Assembly.EVMState}
    {token : Word} {suffix : List Word}
    {site : ReturnSite} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (LateReturnProbe.Terminator.firstSelection site))
    (hPc :
      ({ state with stack := token :: suffix }).pc = pre.pcAfter)
    (hLabel :
      (pre ++ LateReturnProbe.Terminator.firstSelection site ++ post).labelPc
          site.target =
        some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            LateReturnProbe.Terminator.firstSelection site ++ post)
          (LateReturnProbe.Terminator.firstSelection site).length
          { state with stack := token :: suffix } =
        .ok (.running final) ∧
      final.stack =
          selectedAddress
              (pre ++
                LateReturnProbe.Terminator.firstSelection site ++
                post).labelPc
              token site ::
            token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              selectedAddress
                  (pre ++
                    LateReturnProbe.Terminator.firstSelection site ++
                    post).labelPc
                  token site ::
                token :: suffix } ∧
      final.pc =
        (pre ++
          LateReturnProbe.Terminator.firstSelection site).pcAfter := by
  let conditionCode : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 1
    , .push site.token
    , .prim .eq
    ]
  let selectCode : Assembly.Program :=
    [.pushLabel site.target, .prim .mul]
  let condition := EvmYul.UInt256.eq site.token token
  let selected :=
    selectedAddress
      (pre ++ LateReturnProbe.Terminator.firstSelection site ++ post).labelPc
      token site
  have hCodeEq :
      LateReturnProbe.Terminator.firstSelection site =
        conditionCode ++ selectCode := by
    simp [LateReturnProbe.Terminator.firstSelection,
      conditionCode, selectCode]
  have hConditionFits :
      Assembly.Program.PCFitsFrom pre conditionCode := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [hCodeEq, List.append_assoc] using hFits
  have hSelectFits :
      Assembly.Program.PCFitsFrom (pre ++ conditionCode) selectCode := by
    have hAll :
        Assembly.Program.PCFitsFrom pre (conditionCode ++ selectCode) := by
      simpa [hCodeEq] using hFits
    exact Assembly.Program.PCFitsFrom.right hAll
  obtain ⟨mid, hConditionRun, hMidStack, hMidRuntime, hMidPc⟩ :=
    Assembly.StackShuffle.dispatchCondition_source_run
      (state := state) (front := []) (suffix := suffix)
      (token := token) (probe := site.token)
      (pre := pre) (post := selectCode ++ post)
      (by simpa [conditionCode] using hConditionFits)
      (by simpa using hPc)
      (by simp)
  have hConditionRun' :
      Assembly.Source.runNResult
          (pre ++ conditionCode ++ selectCode ++ post)
          conditionCode.length
          { state with stack := token :: suffix } =
        .ok (.running mid) := by
    simpa [conditionCode, List.append_assoc] using hConditionRun
  have hMidStack' :
      mid.stack = condition :: token :: suffix := by
    simpa [condition] using hMidStack
  have hMidPc' : mid.pc = (pre ++ conditionCode).pcAfter := by
    simpa [conditionCode] using hMidPc
  have hLabel' :
      ((pre ++ conditionCode) ++ selectCode ++ post).labelPc
          site.target =
        some dest := by
    simpa [hCodeEq, List.append_assoc] using hLabel
  obtain ⟨final, hSelectRun, hFinalStack,
      hFinalRuntime, hFinalPc⟩ :=
    pushLabelMul_source_run
      (state := mid) (condition := condition)
      (suffix := token :: suffix)
      (label := site.target) (dest := dest)
      (pre := pre ++ conditionCode) (post := post)
      (by simpa [selectCode] using hSelectFits)
      (by simpa [hMidStack'] using hMidPc')
      (by simpa [selectCode, List.append_assoc] using hLabel')
  have hSelectRun' :
      Assembly.Source.runNResult
          (pre ++ conditionCode ++ selectCode ++ post)
          selectCode.length mid =
        .ok (.running final) := by
    have hMidRecord :
        { mid with stack := condition :: token :: suffix } = mid := by
      rw [← hMidStack']
    rw [hMidRecord] at hSelectRun
    simpa [selectCode, List.append_assoc] using hSelectRun
  have hSelected :
      EvmYul.UInt256.mul (EvmYul.UInt256.ofNat dest) condition =
        selected := by
    simpa [condition, selected, hCodeEq, List.append_assoc] using
      (mul_eq_selectedAddress
        (pre ++
          LateReturnProbe.Terminator.firstSelection site ++ post).labelPc
        token site hLabel)
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · rw [hCodeEq]
    rw [show
      (conditionCode ++ selectCode).length =
        conditionCode.length + selectCode.length by simp]
    simpa [List.append_assoc] using
      ((Assembly.Source.runNResult_add_of_running
          (pre ++ conditionCode ++ selectCode ++ post)
          conditionCode.length selectCode.length hConditionRun').trans
        hSelectRun')
  · simpa [hSelected, selected] using hFinalStack
  · calc
      Assembly.eraseRuntimeControl final =
          Assembly.eraseRuntimeControl
            { mid with stack := selected :: token :: suffix } := by
        simpa [hSelected] using hFinalRuntime
      _ =
          Assembly.eraseRuntimeControl
            { state with stack := selected :: token :: suffix } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := mid)
            (right :=
              { state with stack := condition :: token :: suffix })
            (stack := selected :: token :: suffix)
            hMidRuntime
      _ =
          Assembly.eraseRuntimeControl
            { state with
              stack :=
                selectedAddress
                    (pre ++
                      LateReturnProbe.Terminator.firstSelection site ++
                      post).labelPc
                    token site ::
                  token :: suffix } := by
        rfl
  · simpa [hCodeEq, conditionCode, selectCode,
      List.append_assoc] using hFinalPc

theorem nextSelection_source_exists
    {state : Assembly.EVMState}
    {token accumulator : Word} {suffix : List Word}
    {site : ReturnSite} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (LateReturnProbe.Terminator.nextSelection site))
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hLabel :
      (pre ++ LateReturnProbe.Terminator.nextSelection site ++ post).labelPc
          site.target =
        some dest) :
    Assembly.Source.Eventually
      (pre ++ LateReturnProbe.Terminator.nextSelection site ++ post)
      { state with stack := accumulator :: token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                EvmYul.UInt256.add
                    (selectedAddress
                      (pre ++
                        LateReturnProbe.Terminator.nextSelection site ++
                        post).labelPc
                      token site)
                    accumulator ::
                  token :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      EvmYul.UInt256.add
                          (selectedAddress
                            (pre ++
                              LateReturnProbe.Terminator.nextSelection site ++
                              post).labelPc
                            token site)
                          accumulator ::
                        token :: suffix } ∧
              final.pc =
                (pre ++
                  LateReturnProbe.Terminator.nextSelection site).pcAfter
        | _ => False) := by
  let conditionCode : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 2
    , .push site.token
    , .prim .eq
    ]
  let selectCode : Assembly.Program :=
    [.pushLabel site.target, .prim .mul]
  let addCode : Assembly.Program :=
    [.prim .add]
  let condition := EvmYul.UInt256.eq site.token token
  let selected :=
    selectedAddress
      (pre ++ LateReturnProbe.Terminator.nextSelection site ++ post).labelPc
      token site
  have hCodeEq :
      LateReturnProbe.Terminator.nextSelection site =
        conditionCode ++ selectCode ++ addCode := by
    simp [LateReturnProbe.Terminator.nextSelection,
      conditionCode, selectCode, addCode, List.append_assoc]
  have hAllFits :
      Assembly.Program.PCFitsFrom pre
        (conditionCode ++ selectCode ++ addCode) := by
    simpa [hCodeEq] using hFits
  have hConditionFits :
      Assembly.Program.PCFitsFrom pre conditionCode :=
    Assembly.Program.PCFitsFrom.left hAllFits
  have hAfterConditionFits :
      Assembly.Program.PCFitsFrom (pre ++ conditionCode)
        (selectCode ++ addCode) :=
    Assembly.Program.PCFitsFrom.right hAllFits
  have hSelectFits :
      Assembly.Program.PCFitsFrom (pre ++ conditionCode) selectCode :=
    Assembly.Program.PCFitsFrom.left hAfterConditionFits
  have hAddFits :
      Assembly.Program.PCFitsFrom
        (pre ++ conditionCode ++ selectCode) addCode := by
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right hAfterConditionFits)
  have hCondition :=
    Assembly.StackShuffle.dispatchCondition_source_exists
      (state := state) (front := [accumulator]) (suffix := suffix)
      (token := token) (probe := site.token)
      (pre := pre) (post := selectCode ++ addCode ++ post)
      (by simpa [conditionCode] using hConditionFits)
      (by simpa using hPc)
      (by simp)
  have hCondition' :
      Assembly.Source.Eventually
        (pre ++ conditionCode ++ selectCode ++ addCode ++ post)
        { state with stack := accumulator :: token :: suffix }
        (fun outcome =>
          match outcome with
          | .ok (.running mid) =>
              mid.stack =
                  condition :: accumulator :: token :: suffix ∧
                Assembly.eraseRuntimeControl mid =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack :=
                        condition :: accumulator :: token :: suffix } ∧
                mid.pc = (pre ++ conditionCode).pcAfter
          | _ => False) := by
    simpa [conditionCode, condition, List.append_assoc] using hCondition
  rw [show
    pre ++ LateReturnProbe.Terminator.nextSelection site ++ post =
      pre ++ conditionCode ++ selectCode ++ addCode ++ post by
    simp [hCodeEq, List.append_assoc]]
  apply Assembly.Source.Eventually.bind_running hCondition'
  intro conditioned hConditioned
  have hConditionedRecord :
      { conditioned with
          stack := condition :: accumulator :: token :: suffix } =
        conditioned := by
    rw [← hConditioned.1]
  have hLabel' :
      ((pre ++ conditionCode) ++ selectCode ++ addCode ++ post).labelPc
          site.target =
        some dest := by
    simpa [hCodeEq, List.append_assoc] using hLabel
  have hSelectRaw :=
    pushLabelMul_source_exists
      (state := conditioned) (condition := condition)
      (suffix := accumulator :: token :: suffix)
      (label := site.target) (dest := dest)
      (pre := pre ++ conditionCode) (post := addCode ++ post)
      (by simpa [selectCode] using hSelectFits)
      (by simpa [hConditionedRecord] using hConditioned.2.2)
      (by simpa [selectCode, List.append_assoc] using hLabel')
  have hSelected :
      EvmYul.UInt256.mul (EvmYul.UInt256.ofNat dest) condition =
        selected := by
    simpa [condition, selected, hCodeEq, List.append_assoc] using
      (mul_eq_selectedAddress
        (pre ++
          LateReturnProbe.Terminator.nextSelection site ++ post).labelPc
        token site hLabel)
  have hSelectedEq :
      selected =
        selectedAddress
          (pre ++ conditionCode ++ selectCode ++ addCode ++ post).labelPc
          token site := by
    simp [selected, hCodeEq, List.append_assoc]
  rw [hConditionedRecord] at hSelectRaw
  have hSelect :
      Assembly.Source.Eventually
        (pre ++ conditionCode ++ selectCode ++ addCode ++ post)
        conditioned
        (fun outcome =>
          match outcome with
          | .ok (.running mid) =>
              mid.stack = selected :: accumulator :: token :: suffix ∧
                Assembly.eraseRuntimeControl mid =
                  Assembly.eraseRuntimeControl
                    { conditioned with
                      stack :=
                        selected :: accumulator :: token :: suffix } ∧
                mid.pc =
                  (pre ++ conditionCode ++ selectCode).pcAfter
          | _ => False) := by
    apply Assembly.Source.Eventually.mono
      (by simpa [selectCode, addCode, List.append_assoc] using hSelectRaw)
    intro outcome hOutcome
    cases outcome with
    | error err => cases hOutcome
    | ok result =>
        cases result with
        | halted halt => cases hOutcome
        | running mid =>
            simpa [hSelected] using hOutcome
  apply Assembly.Source.Eventually.bind_running hSelect
  intro selectedState hSelectedState
  have hSelectedRecord :
      { selectedState with
          stack := selected :: accumulator :: token :: suffix } =
        selectedState := by
    rw [← hSelectedState.1]
  have hAdd :=
    add_source_exists
      (state := selectedState) (left := selected)
      (right := accumulator) (suffix := token :: suffix)
      (pre := pre ++ conditionCode ++ selectCode) (post := post)
      (by simpa [addCode] using hAddFits)
      (by simpa [hSelectedRecord] using hSelectedState.2.2)
  rw [hSelectedRecord] at hAdd
  apply Assembly.Source.Eventually.mono
    (by simpa [addCode, List.append_assoc] using hAdd)
  intro outcome hOutcome
  cases outcome with
  | error err => cases hOutcome
  | ok result =>
      cases result with
      | halted halt => cases hOutcome
      | running final =>
          rcases hOutcome with
            ⟨hFinalStack, hFinalRuntime, hFinalPc⟩
          refine ⟨?_, ?_, ?_⟩
          · simpa [hSelectedEq] using hFinalStack
          · calc
              Assembly.eraseRuntimeControl final =
                  Assembly.eraseRuntimeControl
                    { selectedState with
                      stack :=
                        EvmYul.UInt256.add selected accumulator ::
                          token :: suffix } := hFinalRuntime
              _ =
                  Assembly.eraseRuntimeControl
                    { conditioned with
                      stack :=
                        EvmYul.UInt256.add selected accumulator ::
                          token :: suffix } := by
                exact
                  Assembly.eraseRuntimeControl_with_stack_congr
                    (left := selectedState)
                    (right :=
                      { conditioned with
                        stack :=
                          selected :: accumulator :: token :: suffix })
                    (stack :=
                      EvmYul.UInt256.add selected accumulator ::
                        token :: suffix)
                    hSelectedState.2.1
              _ =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack :=
                        EvmYul.UInt256.add selected accumulator ::
                          token :: suffix } := by
                exact
                  Assembly.eraseRuntimeControl_with_stack_congr
                    (left := conditioned)
                    (right :=
                      { state with
                        stack :=
                          condition :: accumulator :: token :: suffix })
                    (stack :=
                      EvmYul.UInt256.add selected accumulator ::
                        token :: suffix)
                    hConditioned.2.1
              _ =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack :=
                        EvmYul.UInt256.add
                            (selectedAddress
                              (pre ++
                                conditionCode ++ selectCode ++ addCode ++
                                post).labelPc
                              token site)
                            accumulator ::
                          token :: suffix } := by
                rw [hSelectedEq]
          · simpa [hCodeEq, conditionCode, selectCode, addCode,
              List.append_assoc] using hFinalPc

theorem nextSelection_source_run
    {state : Assembly.EVMState}
    {token accumulator : Word} {suffix : List Word}
    {site : ReturnSite} {dest : Nat}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (LateReturnProbe.Terminator.nextSelection site))
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hLabel :
      (pre ++ LateReturnProbe.Terminator.nextSelection site ++ post).labelPc
          site.target =
        some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            LateReturnProbe.Terminator.nextSelection site ++ post)
          (LateReturnProbe.Terminator.nextSelection site).length
          { state with stack := accumulator :: token :: suffix } =
        .ok (.running final) ∧
      final.stack =
          EvmYul.UInt256.add
              (selectedAddress
                (pre ++
                  LateReturnProbe.Terminator.nextSelection site ++
                  post).labelPc
                token site)
              accumulator ::
            token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              EvmYul.UInt256.add
                  (selectedAddress
                    (pre ++
                      LateReturnProbe.Terminator.nextSelection site ++
                      post).labelPc
                    token site)
                  accumulator ::
                token :: suffix } ∧
      final.pc =
        (pre ++
          LateReturnProbe.Terminator.nextSelection site).pcAfter := by
  let conditionCode : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 2
    , .push site.token
    , .prim .eq
    ]
  let selectCode : Assembly.Program :=
    [.pushLabel site.target, .prim .mul]
  let addCode : Assembly.Program := [.prim .add]
  let condition := EvmYul.UInt256.eq site.token token
  let selected :=
    selectedAddress
      (pre ++ LateReturnProbe.Terminator.nextSelection site ++ post).labelPc
      token site
  have hCodeEq :
      LateReturnProbe.Terminator.nextSelection site =
        conditionCode ++ selectCode ++ addCode := by
    simp [LateReturnProbe.Terminator.nextSelection,
      conditionCode, selectCode, addCode, List.append_assoc]
  have hAllFits :
      Assembly.Program.PCFitsFrom pre
        (conditionCode ++ selectCode ++ addCode) := by
    simpa [hCodeEq] using hFits
  have hConditionFits :
      Assembly.Program.PCFitsFrom pre conditionCode :=
    Assembly.Program.PCFitsFrom.left hAllFits
  have hAfterConditionFits :
      Assembly.Program.PCFitsFrom (pre ++ conditionCode)
        (selectCode ++ addCode) :=
    Assembly.Program.PCFitsFrom.right hAllFits
  have hSelectFits :
      Assembly.Program.PCFitsFrom (pre ++ conditionCode) selectCode :=
    Assembly.Program.PCFitsFrom.left hAfterConditionFits
  have hAddFits :
      Assembly.Program.PCFitsFrom
        (pre ++ conditionCode ++ selectCode) addCode := by
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right hAfterConditionFits)
  obtain ⟨conditioned, hConditionRun, hConditionedStack,
      hConditionedRuntime, hConditionedPc⟩ :=
    Assembly.StackShuffle.dispatchCondition_source_run
      (state := state) (front := [accumulator]) (suffix := suffix)
      (token := token) (probe := site.token)
      (pre := pre) (post := selectCode ++ addCode ++ post)
      (by simpa [conditionCode] using hConditionFits)
      (by simpa using hPc)
      (by simp)
  have hConditionRun' :
      Assembly.Source.runNResult
          (pre ++ conditionCode ++ selectCode ++ addCode ++ post)
          conditionCode.length
          { state with stack := accumulator :: token :: suffix } =
        .ok (.running conditioned) := by
    simpa [conditionCode, List.append_assoc] using hConditionRun
  have hConditionedStack' :
      conditioned.stack =
        condition :: accumulator :: token :: suffix := by
    simpa [condition] using hConditionedStack
  have hConditionedPc' :
      conditioned.pc = (pre ++ conditionCode).pcAfter := by
    simpa [conditionCode] using hConditionedPc
  have hLabel' :
      ((pre ++ conditionCode) ++ selectCode ++ addCode ++ post).labelPc
          site.target =
        some dest := by
    simpa [hCodeEq, List.append_assoc] using hLabel
  obtain ⟨selectedState, hSelectRun, hSelectedStack,
      hSelectedRuntime, hSelectedPc⟩ :=
    pushLabelMul_source_run
      (state := conditioned) (condition := condition)
      (suffix := accumulator :: token :: suffix)
      (label := site.target) (dest := dest)
      (pre := pre ++ conditionCode) (post := addCode ++ post)
      (by simpa [selectCode] using hSelectFits)
      (by simpa [hConditionedStack'] using hConditionedPc')
      (by simpa [selectCode, List.append_assoc] using hLabel')
  have hSelected :
      EvmYul.UInt256.mul (EvmYul.UInt256.ofNat dest) condition =
        selected := by
    simpa [condition, selected, hCodeEq, List.append_assoc] using
      (mul_eq_selectedAddress
        (pre ++
          LateReturnProbe.Terminator.nextSelection site ++ post).labelPc
        token site hLabel)
  have hSelectRun' :
      Assembly.Source.runNResult
          (pre ++ conditionCode ++ selectCode ++ addCode ++ post)
          selectCode.length conditioned =
        .ok (.running selectedState) := by
    have hConditionedRecord :
        { conditioned with
            stack := condition :: accumulator :: token :: suffix } =
          conditioned := by
      rw [← hConditionedStack']
    rw [hConditionedRecord] at hSelectRun
    simpa [selectCode, List.append_assoc] using hSelectRun
  have hSelectedStack' :
      selectedState.stack =
        selected :: accumulator :: token :: suffix := by
    simpa [hSelected] using hSelectedStack
  have hSelectedPc' :
      selectedState.pc =
        (pre ++ conditionCode ++ selectCode).pcAfter := by
    simpa [selectCode, List.append_assoc] using hSelectedPc
  obtain ⟨final, hAddRun, hFinalStack, hFinalRuntime, hFinalPc⟩ :=
    add_source_run
      (state := selectedState) (left := selected)
      (right := accumulator) (suffix := token :: suffix)
      (pre := pre ++ conditionCode ++ selectCode) (post := post)
      (by simpa [addCode] using hAddFits)
      (by simpa [hSelectedStack'] using hSelectedPc')
  have hAddRun' :
      Assembly.Source.runNResult
          (pre ++ conditionCode ++ selectCode ++ addCode ++ post)
          addCode.length selectedState =
        .ok (.running final) := by
    have hSelectedRecord :
        { selectedState with
            stack := selected :: accumulator :: token :: suffix } =
          selectedState := by
      rw [← hSelectedStack']
    rw [hSelectedRecord] at hAddRun
    simpa [addCode, List.append_assoc] using hAddRun
  have hFirstTwoRun :
      Assembly.Source.runNResult
          (pre ++ conditionCode ++ selectCode ++ addCode ++ post)
          (conditionCode.length + selectCode.length)
          { state with stack := accumulator :: token :: suffix } =
        .ok (.running selectedState) :=
    (Assembly.Source.runNResult_add_of_running
      (pre ++ conditionCode ++ selectCode ++ addCode ++ post)
      conditionCode.length selectCode.length hConditionRun').trans
      hSelectRun'
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · rw [hCodeEq]
    rw [show
      (conditionCode ++ selectCode ++ addCode).length =
        (conditionCode.length + selectCode.length) + addCode.length by
      simp [Nat.add_assoc]]
    simpa [List.append_assoc] using
      ((Assembly.Source.runNResult_add_of_running
          (pre ++ conditionCode ++ selectCode ++ addCode ++ post)
          (conditionCode.length + selectCode.length) addCode.length
          hFirstTwoRun).trans hAddRun')
  · simpa [selected] using hFinalStack
  · calc
      Assembly.eraseRuntimeControl final =
          Assembly.eraseRuntimeControl
            { selectedState with
              stack :=
                EvmYul.UInt256.add selected accumulator ::
                  token :: suffix } := hFinalRuntime
      _ =
          Assembly.eraseRuntimeControl
            { conditioned with
              stack :=
                EvmYul.UInt256.add selected accumulator ::
                  token :: suffix } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := selectedState)
            (right :=
              { conditioned with
                stack := selected :: accumulator :: token :: suffix })
            (stack :=
              EvmYul.UInt256.add selected accumulator ::
                token :: suffix)
            (by simpa [hSelected] using hSelectedRuntime)
      _ =
          Assembly.eraseRuntimeControl
            { state with
              stack :=
                EvmYul.UInt256.add selected accumulator ::
                  token :: suffix } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := conditioned)
            (right :=
              { state with
                stack :=
                  condition :: accumulator :: token :: suffix })
            (stack :=
              EvmYul.UInt256.add selected accumulator ::
                token :: suffix)
            hConditionedRuntime
      _ =
          Assembly.eraseRuntimeControl
            { state with
              stack :=
                EvmYul.UInt256.add
                    (selectedAddress
                      (pre ++
                        LateReturnProbe.Terminator.nextSelection site ++
                        post).labelPc
                      token site)
                    accumulator ::
                  token :: suffix } := by
        rfl
  · simpa [hCodeEq, conditionCode, selectCode, addCode,
      List.append_assoc] using hFinalPc

theorem nextSelections_source_exists
    {state : Assembly.EVMState}
    {token accumulator : Word} {suffix : List Word}
    {sites : List ReturnSite}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (sites.flatMap LateReturnProbe.Terminator.nextSelection))
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      ∀ site ∈ sites,
        ∃ dest,
          (pre ++
              sites.flatMap LateReturnProbe.Terminator.nextSelection ++
              post).labelPc site.target =
            some dest) :
    Assembly.Source.Eventually
      (pre ++
        sites.flatMap LateReturnProbe.Terminator.nextSelection ++ post)
      { state with stack := accumulator :: token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                sites.foldl
                    (fun value site =>
                      EvmYul.UInt256.add
                        (selectedAddress
                          (pre ++
                            sites.flatMap
                              LateReturnProbe.Terminator.nextSelection ++
                            post).labelPc
                          token site)
                        value)
                    accumulator ::
                  token :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      sites.foldl
                          (fun value site =>
                            EvmYul.UInt256.add
                              (selectedAddress
                                (pre ++
                                  sites.flatMap
                                    LateReturnProbe.Terminator.nextSelection ++
                                  post).labelPc
                                token site)
                              value)
                          accumulator ::
                        token :: suffix } ∧
              final.pc =
                (pre ++
                  sites.flatMap
                    LateReturnProbe.Terminator.nextSelection).pcAfter
        | _ => False) := by
  induction sites generalizing pre state accumulator with
  | nil =>
      apply Assembly.Source.Eventually.pure
      exact ⟨rfl, rfl, by simpa using hPc⟩
  | cons site rest ih =>
      let headCode :=
        LateReturnProbe.Terminator.nextSelection site
      let tailCode :=
        rest.flatMap LateReturnProbe.Terminator.nextSelection
      have hProgramEq :
          pre ++ headCode ++ tailCode ++ post =
            pre ++
              (site :: rest).flatMap
                LateReturnProbe.Terminator.nextSelection ++ post := by
        simp [headCode, tailCode, List.append_assoc]
      have hResolverEq :
          (pre ++
              (site :: rest).flatMap
                LateReturnProbe.Terminator.nextSelection ++ post).labelPc =
            (pre ++ headCode ++ tailCode ++ post).labelPc :=
        congrArg Assembly.Program.labelPc hProgramEq.symm
      have hFoldStepEq :
          (fun value candidate =>
            EvmYul.UInt256.add
              (selectedAddress
                (pre ++
                  (site :: rest).flatMap
                    LateReturnProbe.Terminator.nextSelection ++ post).labelPc
                token candidate)
              value) =
            (fun value candidate =>
              EvmYul.UInt256.add
                (selectedAddress
                  (pre ++ headCode ++ tailCode ++ post).labelPc
                  token candidate)
                value) := by
        funext value candidate
        rw [hResolverEq]
      have hSelectedSiteEq :
          selectedAddress
              (pre ++
                (site :: rest).flatMap
                  LateReturnProbe.Terminator.nextSelection ++ post).labelPc
              token site =
            selectedAddress
              (pre ++ headCode ++ tailCode ++ post).labelPc
              token site := by
        rw [hResolverEq]
      have hFoldEq :
          (site :: rest).foldl
              (fun value candidate =>
                EvmYul.UInt256.add
                  (selectedAddress
                    (pre ++
                      (site :: rest).flatMap
                        LateReturnProbe.Terminator.nextSelection ++ post).labelPc
                    token candidate)
                  value)
              accumulator =
            (site :: rest).foldl
              (fun value candidate =>
                EvmYul.UInt256.add
                  (selectedAddress
                    (pre ++ headCode ++ tailCode ++ post).labelPc
                    token candidate)
                  value)
              accumulator :=
        congrArg
          (fun step => (site :: rest).foldl step accumulator)
          hFoldStepEq
      have hEraseFoldEq :
          Assembly.eraseRuntimeControl
              { state with
                stack :=
                  (site :: rest).foldl
                      (fun value candidate =>
                        EvmYul.UInt256.add
                          (selectedAddress
                            (pre ++
                              (site :: rest).flatMap
                                LateReturnProbe.Terminator.nextSelection ++
                              post).labelPc
                            token candidate)
                          value)
                      accumulator ::
                    token :: suffix } =
            Assembly.eraseRuntimeControl
              { state with
                stack :=
                  (site :: rest).foldl
                      (fun value candidate =>
                        EvmYul.UInt256.add
                          (selectedAddress
                            (pre ++ headCode ++ tailCode ++ post).labelPc
                            token candidate)
                          value)
                      accumulator ::
                    token :: suffix } := by
        rw [hFoldEq]
      have hAllFits :
          Assembly.Program.PCFitsFrom pre (headCode ++ tailCode) := by
        simpa [headCode, tailCode, List.append_assoc] using hFits
      have hHeadFits :
          Assembly.Program.PCFitsFrom pre headCode :=
        Assembly.Program.PCFitsFrom.left hAllFits
      have hTailFits :
          Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode :=
        Assembly.Program.PCFitsFrom.right hAllFits
      obtain ⟨dest, hDest⟩ := hResolved site (by simp)
      have hDest' :
          (pre ++ headCode ++ tailCode ++ post).labelPc site.target =
            some dest := by
        simpa [headCode, tailCode, List.append_assoc] using hDest
      have hHead :=
        nextSelection_source_exists
          (state := state) (token := token) (accumulator := accumulator)
          (suffix := suffix) (site := site) (dest := dest)
          (pre := pre) (post := tailCode ++ post)
          hHeadFits hPc
          (by simpa [headCode, List.append_assoc] using hDest')
      let nextAccumulator :=
        EvmYul.UInt256.add
          (selectedAddress
            (pre ++ headCode ++ tailCode ++ post).labelPc token site)
          accumulator
      have hHead' :
          Assembly.Source.Eventually
            (pre ++ headCode ++ tailCode ++ post)
            { state with stack := accumulator :: token :: suffix }
            (fun outcome =>
              match outcome with
              | .ok (.running mid) =>
                  mid.stack = nextAccumulator :: token :: suffix ∧
                    Assembly.eraseRuntimeControl mid =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack := nextAccumulator :: token :: suffix } ∧
                    mid.pc = (pre ++ headCode).pcAfter
              | _ => False) := by
        simpa [headCode, nextAccumulator, List.append_assoc] using hHead
      rw [show
        pre ++
            (site :: rest).flatMap
              LateReturnProbe.Terminator.nextSelection ++ post =
          pre ++ headCode ++ tailCode ++ post by
        simp [headCode, tailCode, List.append_assoc]]
      apply Assembly.Source.Eventually.bind_running hHead'
      intro mid hMid
      have hTailResolved :
          ∀ candidate ∈ rest,
            ∃ candidateDest,
              ((pre ++ headCode) ++ tailCode ++ post).labelPc
                  candidate.target =
                some candidateDest := by
        intro candidate hCandidate
        obtain ⟨candidateDest, hCandidateDest⟩ :=
          hResolved candidate (by simp [hCandidate])
        exact
          ⟨candidateDest,
            by
              simpa [headCode, tailCode, List.append_assoc] using
                hCandidateDest⟩
      have hTail :=
        ih
          (pre := pre ++ headCode) (state := mid)
          (accumulator := nextAccumulator)
          hTailFits
          (by simpa [hMid.1] using hMid.2.2)
          hTailResolved
      have hMidRecord :
          { mid with stack := nextAccumulator :: token :: suffix } = mid := by
        rw [← hMid.1]
      rw [hMidRecord] at hTail
      apply Assembly.Source.Eventually.mono
        (by simpa [tailCode, List.append_assoc] using hTail)
      intro outcome hOutcome
      cases outcome with
      | error err => cases hOutcome
      | ok result =>
          cases result with
          | halted halt => cases hOutcome
          | running final =>
              rcases hOutcome with
                ⟨hFinalStack, hFinalRuntime, hFinalPc⟩
              refine ⟨?_, ?_, ?_⟩
              · simpa [nextAccumulator, headCode, tailCode,
                  List.append_assoc] using hFinalStack
              · calc
                  Assembly.eraseRuntimeControl final =
                      Assembly.eraseRuntimeControl
                        { mid with
                          stack :=
                            rest.foldl
                                (fun value candidate =>
                                  EvmYul.UInt256.add
                                    (selectedAddress
                                      (pre ++
                                        headCode ++ tailCode ++ post).labelPc
                                      token candidate)
                                    value)
                                nextAccumulator ::
                              token :: suffix } := by
                    simpa [headCode, tailCode,
                      List.append_assoc] using hFinalRuntime
                  _ =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack :=
                            rest.foldl
                                (fun value candidate =>
                                  EvmYul.UInt256.add
                                    (selectedAddress
                                      (pre ++
                                        headCode ++ tailCode ++ post).labelPc
                                      token candidate)
                                    value)
                                nextAccumulator ::
                              token :: suffix } := by
                    exact
                      Assembly.eraseRuntimeControl_with_stack_congr
                        (left := mid)
                        (right :=
                          { state with
                            stack := nextAccumulator :: token :: suffix })
                        (stack :=
                          rest.foldl
                              (fun value candidate =>
                                EvmYul.UInt256.add
                                  (selectedAddress
                                    (pre ++
                                      headCode ++ tailCode ++ post).labelPc
                                    token candidate)
                                  value)
                              nextAccumulator ::
                            token :: suffix)
                        hMid.2.1
              · simpa [headCode, tailCode, List.append_assoc] using
                  hFinalPc

theorem nextSelections_source_run
    {state : Assembly.EVMState}
    {token accumulator : Word} {suffix : List Word}
    {sites : List ReturnSite}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (sites.flatMap LateReturnProbe.Terminator.nextSelection))
    (hPc :
      ({ state with stack := accumulator :: token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      ∀ site ∈ sites,
        ∃ dest,
          (pre ++
              sites.flatMap LateReturnProbe.Terminator.nextSelection ++
              post).labelPc site.target =
            some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            sites.flatMap LateReturnProbe.Terminator.nextSelection ++ post)
          (sites.flatMap
            LateReturnProbe.Terminator.nextSelection).length
          { state with stack := accumulator :: token :: suffix } =
        .ok (.running final) ∧
      final.stack =
          sites.foldl
              (fun value site =>
                EvmYul.UInt256.add
                  (selectedAddress
                    (pre ++
                      sites.flatMap
                        LateReturnProbe.Terminator.nextSelection ++
                      post).labelPc
                    token site)
                  value)
              accumulator ::
            token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              sites.foldl
                  (fun value site =>
                    EvmYul.UInt256.add
                      (selectedAddress
                        (pre ++
                          sites.flatMap
                            LateReturnProbe.Terminator.nextSelection ++
                          post).labelPc
                        token site)
                      value)
                  accumulator ::
                token :: suffix } ∧
      final.pc =
        (pre ++
          sites.flatMap
            LateReturnProbe.Terminator.nextSelection).pcAfter := by
  induction sites generalizing pre state accumulator with
  | nil =>
      let start : Assembly.EVMState :=
        { state with stack := accumulator :: token :: suffix }
      refine ⟨start, ?_, rfl, rfl, ?_⟩
      · simp [start, Assembly.Source.runNResult,
          Assembly.Control.runNResultWith]
      · simpa [start] using hPc
  | cons site rest ih =>
      let headCode :=
        LateReturnProbe.Terminator.nextSelection site
      let tailCode :=
        rest.flatMap LateReturnProbe.Terminator.nextSelection
      have hAllFits :
          Assembly.Program.PCFitsFrom pre (headCode ++ tailCode) := by
        simpa [headCode, tailCode, List.append_assoc] using hFits
      have hHeadFits :
          Assembly.Program.PCFitsFrom pre headCode :=
        Assembly.Program.PCFitsFrom.left hAllFits
      have hTailFits :
          Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode :=
        Assembly.Program.PCFitsFrom.right hAllFits
      obtain ⟨dest, hDest⟩ := hResolved site (by simp)
      have hDest' :
          (pre ++ headCode ++ tailCode ++ post).labelPc site.target =
            some dest := by
        simpa [headCode, tailCode, List.append_assoc] using hDest
      obtain ⟨mid, hHeadRun, hMidStack, hMidRuntime, hMidPc⟩ :=
        nextSelection_source_run
          (state := state) (token := token) (accumulator := accumulator)
          (suffix := suffix) (site := site) (dest := dest)
          (pre := pre) (post := tailCode ++ post)
          hHeadFits hPc
          (by simpa [headCode, List.append_assoc] using hDest')
      let nextAccumulator :=
        EvmYul.UInt256.add
          (selectedAddress
            (pre ++ headCode ++ tailCode ++ post).labelPc token site)
          accumulator
      have hHeadRun' :
          Assembly.Source.runNResult
              (pre ++ headCode ++ tailCode ++ post)
              headCode.length
              { state with stack := accumulator :: token :: suffix } =
            .ok (.running mid) := by
        simpa [headCode, tailCode, List.append_assoc] using hHeadRun
      have hMidStack' :
          mid.stack = nextAccumulator :: token :: suffix := by
        simpa [nextAccumulator, headCode, tailCode,
          List.append_assoc] using hMidStack
      have hMidPc' : mid.pc = (pre ++ headCode).pcAfter := by
        simpa [headCode] using hMidPc
      have hTailResolved :
          ∀ candidate ∈ rest,
            ∃ candidateDest,
              ((pre ++ headCode) ++ tailCode ++ post).labelPc
                  candidate.target =
                some candidateDest := by
        intro candidate hCandidate
        obtain ⟨candidateDest, hCandidateDest⟩ :=
          hResolved candidate (by simp [hCandidate])
        exact
          ⟨candidateDest,
            by
              simpa [headCode, tailCode, List.append_assoc] using
                hCandidateDest⟩
      obtain ⟨final, hTailRun, hFinalStack,
          hFinalRuntime, hFinalPc⟩ :=
        ih
          (pre := pre ++ headCode) (state := mid)
          (accumulator := nextAccumulator)
          hTailFits
          (by simpa [hMidStack'] using hMidPc')
          hTailResolved
      have hTailRun' :
          Assembly.Source.runNResult
              (pre ++ headCode ++ tailCode ++ post)
              tailCode.length mid =
            .ok (.running final) := by
        have hMidRecord :
            { mid with stack := nextAccumulator :: token :: suffix } =
              mid := by
          rw [← hMidStack']
        rw [hMidRecord] at hTailRun
        simpa [tailCode, List.append_assoc] using hTailRun
      refine ⟨final, ?_, ?_, ?_, ?_⟩
      · rw [show
          (site :: rest).flatMap
              LateReturnProbe.Terminator.nextSelection =
            headCode ++ tailCode by
          simp [headCode, tailCode]]
        rw [List.length_append]
        simpa [List.append_assoc] using
          ((Assembly.Source.runNResult_add_of_running
              (pre ++ headCode ++ tailCode ++ post)
              headCode.length tailCode.length hHeadRun').trans
            hTailRun')
      · simpa [nextAccumulator, headCode, tailCode,
          List.append_assoc] using hFinalStack
      · calc
          Assembly.eraseRuntimeControl final =
              Assembly.eraseRuntimeControl
                { mid with
                  stack :=
                    rest.foldl
                        (fun value candidate =>
                          EvmYul.UInt256.add
                            (selectedAddress
                              (pre ++
                                headCode ++ tailCode ++ post).labelPc
                              token candidate)
                            value)
                        nextAccumulator ::
                      token :: suffix } := by
            simpa [headCode, tailCode,
              List.append_assoc] using hFinalRuntime
          _ =
              Assembly.eraseRuntimeControl
                { state with
                  stack :=
                    rest.foldl
                        (fun value candidate =>
                          EvmYul.UInt256.add
                            (selectedAddress
                              (pre ++
                                headCode ++ tailCode ++ post).labelPc
                              token candidate)
                            value)
                        nextAccumulator ::
                      token :: suffix } := by
            exact
              Assembly.eraseRuntimeControl_with_stack_congr
                (left := mid)
                (right :=
                  { state with
                    stack := nextAccumulator :: token :: suffix })
                (stack :=
                  rest.foldl
                      (fun value candidate =>
                        EvmYul.UInt256.add
                          (selectedAddress
                            (pre ++
                              headCode ++ tailCode ++ post).labelPc
                            token candidate)
                          value)
                      nextAccumulator ::
                    token :: suffix)
                (by
                  simpa [nextAccumulator, headCode, tailCode,
                    List.append_assoc] using hMidRuntime)
          _ =
              Assembly.eraseRuntimeControl
                { state with
                  stack :=
                    (site :: rest).foldl
                        (fun value candidate =>
                          EvmYul.UInt256.add
                            (selectedAddress
                              (pre ++
                                (site :: rest).flatMap
                                  LateReturnProbe.Terminator.nextSelection ++
                                post).labelPc
                              token candidate)
                            value)
                        accumulator ::
                      token :: suffix } := by
            simp [nextAccumulator, headCode, tailCode,
              List.append_assoc]
      · simpa [headCode, tailCode, List.append_assoc] using hFinalPc

def selectedAddressSum (resolve : Assembly.Label → Option Nat)
    (token : Word) : List ReturnSite → Word
  | [] => EvmYul.UInt256.ofNat 0
  | site :: rest =>
      rest.foldl
        (fun accumulator candidate =>
          EvmYul.UInt256.add
            (selectedAddress resolve token candidate)
            accumulator)
        (selectedAddress resolve token site)

theorem uint256_add_zero (value : Word) :
    EvmYul.UInt256.add value (EvmYul.UInt256.ofNat 0) = value := by
  rcases value with ⟨value⟩
  change EvmYul.UInt256.mk
      (value + Fin.ofNat EvmYul.UInt256.size 0) =
    EvmYul.UInt256.mk value
  congr 1
  exact Fin.add_zero value

theorem uint256_zero_add (value : Word) :
    EvmYul.UInt256.add (EvmYul.UInt256.ofNat 0) value = value := by
  rcases value with ⟨value⟩
  change EvmYul.UInt256.mk
      (Fin.ofNat EvmYul.UInt256.size 0 + value) =
    EvmYul.UInt256.mk value
  congr 1
  exact Fin.zero_add value

theorem selectedAddress_eq_zero_of_ne
    (resolve : Assembly.Label → Option Nat)
    (token : Word) (site : ReturnSite)
    (hNe : site.token ≠ token) :
    selectedAddress resolve token site =
      EvmYul.UInt256.ofNat 0 := by
  simp [selectedAddress, hNe]

theorem selectedAddress_eq_of_eq
    (resolve : Assembly.Label → Option Nat)
    (token : Word) (site : ReturnSite) {dest : Nat}
    (hToken : site.token = token)
    (hResolve : resolve site.target = some dest) :
    selectedAddress resolve token site =
      EvmYul.UInt256.ofNat dest := by
  simp [selectedAddress, hToken, hResolve]

theorem foldl_selectedAddress_eq_initial_of_all_ne
    (resolve : Assembly.Label → Option Nat)
    (token : Word) (sites : List ReturnSite)
    (initial : Word)
    (hNe : ∀ site ∈ sites, site.token ≠ token) :
    sites.foldl
        (fun value site =>
          EvmYul.UInt256.add
            (selectedAddress resolve token site) value)
        initial =
      initial := by
  induction sites generalizing initial with
  | nil => rfl
  | cons site rest ih =>
      have hHead : site.token ≠ token :=
        hNe site (by simp)
      have hRest :
          ∀ candidate ∈ rest, candidate.token ≠ token := by
        intro candidate hCandidate
        exact hNe candidate (by simp [hCandidate])
      simp only [List.foldl_cons]
      rw [selectedAddress_eq_zero_of_ne resolve token site hHead]
      rw [uint256_zero_add]
      exact ih initial hRest

theorem selectedAddressSum_eq_zero_of_all_ne
    (resolve : Assembly.Label → Option Nat)
    (token : Word) (sites : List ReturnSite)
    (hNe : ∀ site ∈ sites, site.token ≠ token) :
    selectedAddressSum resolve token sites =
      EvmYul.UInt256.ofNat 0 := by
  cases sites with
  | nil => rfl
  | cons first rest =>
      have hFirst : first.token ≠ token :=
        hNe first (by simp)
      have hRest :
          ∀ site ∈ rest, site.token ≠ token := by
        intro site hSite
        exact hNe site (by simp [hSite])
      simp only [selectedAddressSum]
      rw [selectedAddress_eq_zero_of_ne resolve token first hFirst]
      exact
        foldl_selectedAddress_eq_initial_of_all_ne
          resolve token rest (EvmYul.UInt256.ofNat 0) hRest

theorem selectedAddressSum_eq_of_unique
    {resolve : Assembly.Label → Option Nat}
    {token : Word} {sites : List ReturnSite}
    {selected : ReturnSite} {dest : Nat}
    (hUnique : ReturnAddressRelation.TokensUnique sites)
    (hMem : selected ∈ sites)
    (hToken : selected.token = token)
    (hResolve : resolve selected.target = some dest) :
    selectedAddressSum resolve token sites =
      EvmYul.UInt256.ofNat dest := by
  induction sites with
  | nil => simp at hMem
  | cons head rest ih =>
      rcases hUnique with ⟨hFresh, hRestUnique⟩
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl hHead =>
          subst selected
          have hRestNe :
              ∀ site ∈ rest, site.token ≠ token := by
            intro site hSite hSiteToken
            exact
              (hFresh site hSite)
                (hToken.trans hSiteToken.symm)
          simp only [selectedAddressSum]
          rw [selectedAddress_eq_of_eq
            resolve token head hToken hResolve]
          exact
            foldl_selectedAddress_eq_initial_of_all_ne
              resolve token rest (EvmYul.UInt256.ofNat dest)
              hRestNe
      | inr hSelectedRest =>
          have hHeadNe : head.token ≠ token := by
            intro hHeadToken
            exact
              (hFresh selected hSelectedRest)
                (hHeadToken.trans hToken.symm)
          have hRestResult :=
            ih hRestUnique hSelectedRest
          cases rest with
          | nil => simp at hSelectedRest
          | cons first tail =>
              simp only [selectedAddressSum, List.foldl_cons]
              rw [selectedAddress_eq_zero_of_ne
                resolve token head hHeadNe]
              rw [uint256_add_zero]
              exact hRestResult

theorem selectionCode_source_exists
    {state : Assembly.EVMState}
    {token : Word} {suffix : List Word}
    {first : ReturnSite} {rest : List ReturnSite}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (LateReturnProbe.Terminator.selectionCode (first :: rest)))
    (hPc :
      ({ state with stack := token :: suffix }).pc = pre.pcAfter)
    (hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++
              LateReturnProbe.Terminator.selectionCode (first :: rest) ++
              post).labelPc site.target =
            some dest) :
    Assembly.Source.Eventually
      (pre ++
        LateReturnProbe.Terminator.selectionCode (first :: rest) ++ post)
      { state with stack := token :: suffix }
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack =
                selectedAddressSum
                    (pre ++
                      LateReturnProbe.Terminator.selectionCode
                        (first :: rest) ++
                      post).labelPc
                    token (first :: rest) ::
                  token :: suffix ∧
              Assembly.eraseRuntimeControl final =
                Assembly.eraseRuntimeControl
                  { state with
                    stack :=
                      selectedAddressSum
                          (pre ++
                            LateReturnProbe.Terminator.selectionCode
                              (first :: rest) ++
                            post).labelPc
                          token (first :: rest) ::
                        token :: suffix } ∧
              final.pc =
                (pre ++
                  LateReturnProbe.Terminator.selectionCode
                    (first :: rest)).pcAfter
        | _ => False) := by
  let headCode :=
    LateReturnProbe.Terminator.firstSelection first
  let tailCode :=
    rest.flatMap LateReturnProbe.Terminator.nextSelection
  have hCodeEq :
      LateReturnProbe.Terminator.selectionCode (first :: rest) =
        headCode ++ tailCode := by
    simp [LateReturnProbe.Terminator.selectionCode,
      headCode, tailCode]
  have hAllFits :
      Assembly.Program.PCFitsFrom pre (headCode ++ tailCode) := by
    simpa [hCodeEq] using hFits
  have hHeadFits :
      Assembly.Program.PCFitsFrom pre headCode :=
    Assembly.Program.PCFitsFrom.left hAllFits
  have hTailFits :
      Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode :=
    Assembly.Program.PCFitsFrom.right hAllFits
  obtain ⟨firstDest, hFirstDest⟩ :=
    hResolved first (by simp)
  have hFirst :=
    firstSelection_source_exists
      (state := state) (token := token) (suffix := suffix)
      (site := first) (dest := firstDest)
      (pre := pre) (post := tailCode ++ post)
      hHeadFits hPc
      (by simpa [hCodeEq, headCode, List.append_assoc] using hFirstDest)
  let firstValue :=
    selectedAddress
      (pre ++ headCode ++ tailCode ++ post).labelPc token first
  have hFirst' :
      Assembly.Source.Eventually
        (pre ++ headCode ++ tailCode ++ post)
        { state with stack := token :: suffix }
        (fun outcome =>
          match outcome with
          | .ok (.running mid) =>
              mid.stack = firstValue :: token :: suffix ∧
                Assembly.eraseRuntimeControl mid =
                  Assembly.eraseRuntimeControl
                    { state with stack := firstValue :: token :: suffix } ∧
                mid.pc = (pre ++ headCode).pcAfter
          | _ => False) := by
    simpa [headCode, firstValue, List.append_assoc] using hFirst
  rw [show
    pre ++
        LateReturnProbe.Terminator.selectionCode (first :: rest) ++ post =
      pre ++ headCode ++ tailCode ++ post by
    simp [hCodeEq, List.append_assoc]]
  apply Assembly.Source.Eventually.bind_running hFirst'
  intro mid hMid
  have hTailResolved :
      ∀ site ∈ rest,
        ∃ dest,
          ((pre ++ headCode) ++ tailCode ++ post).labelPc site.target =
            some dest := by
    intro site hSite
    obtain ⟨dest, hDest⟩ :=
      hResolved site (by simp [hSite])
    exact
      ⟨dest,
        by simpa [hCodeEq, headCode, tailCode,
            List.append_assoc] using hDest⟩
  have hTail :=
    nextSelections_source_exists
      (state := mid) (token := token) (accumulator := firstValue)
      (suffix := suffix) (sites := rest)
      (pre := pre ++ headCode) (post := post)
      hTailFits
      (by simpa [hMid.1] using hMid.2.2)
      hTailResolved
  have hMidRecord :
      { mid with stack := firstValue :: token :: suffix } = mid := by
    rw [← hMid.1]
  rw [hMidRecord] at hTail
  apply Assembly.Source.Eventually.mono
    (by simpa [tailCode, List.append_assoc] using hTail)
  intro outcome hOutcome
  cases outcome with
  | error err => cases hOutcome
  | ok result =>
      cases result with
      | halted halt => cases hOutcome
      | running final =>
          rcases hOutcome with
            ⟨hFinalStack, hFinalRuntime, hFinalPc⟩
          refine ⟨?_, ?_, ?_⟩
          · simpa [selectedAddressSum, firstValue,
              headCode, tailCode, List.append_assoc] using hFinalStack
          · calc
              Assembly.eraseRuntimeControl final =
                  Assembly.eraseRuntimeControl
                    { mid with
                      stack :=
                        rest.foldl
                            (fun value site =>
                              EvmYul.UInt256.add
                                (selectedAddress
                                  (pre ++
                                    headCode ++ tailCode ++ post).labelPc
                                  token site)
                                value)
                            firstValue ::
                          token :: suffix } := by
                simpa [headCode, tailCode,
                  List.append_assoc] using hFinalRuntime
              _ =
                  Assembly.eraseRuntimeControl
                    { state with
                      stack :=
                        rest.foldl
                            (fun value site =>
                              EvmYul.UInt256.add
                                (selectedAddress
                                  (pre ++
                                    headCode ++ tailCode ++ post).labelPc
                                  token site)
                                value)
                            firstValue ::
                          token :: suffix } := by
                exact
                  Assembly.eraseRuntimeControl_with_stack_congr
                    (left := mid)
                    (right :=
                      { state with
                        stack := firstValue :: token :: suffix })
                    (stack :=
                      rest.foldl
                          (fun value site =>
                            EvmYul.UInt256.add
                              (selectedAddress
                                (pre ++
                                  headCode ++ tailCode ++ post).labelPc
                                token site)
                              value)
                          firstValue ::
                        token :: suffix)
                    hMid.2.1
          · simpa [hCodeEq, headCode, tailCode,
              List.append_assoc] using hFinalPc

theorem selectionCode_source_run
    {state : Assembly.EVMState}
    {token : Word} {suffix : List Word}
    {first : ReturnSite} {rest : List ReturnSite}
    {pre post : Assembly.Program}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (LateReturnProbe.Terminator.selectionCode (first :: rest)))
    (hPc :
      ({ state with stack := token :: suffix }).pc = pre.pcAfter)
    (hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++
              LateReturnProbe.Terminator.selectionCode (first :: rest) ++
              post).labelPc site.target =
            some dest) :
    ∃ final,
      Assembly.Source.runNResult
          (pre ++
            LateReturnProbe.Terminator.selectionCode (first :: rest) ++
            post)
          (LateReturnProbe.Terminator.selectionCode
            (first :: rest)).length
          { state with stack := token :: suffix } =
        .ok (.running final) ∧
      final.stack =
          selectedAddressSum
              (pre ++
                LateReturnProbe.Terminator.selectionCode
                  (first :: rest) ++
                post).labelPc
              token (first :: rest) ::
            token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              selectedAddressSum
                  (pre ++
                    LateReturnProbe.Terminator.selectionCode
                      (first :: rest) ++
                    post).labelPc
                  token (first :: rest) ::
                token :: suffix } ∧
      final.pc =
        (pre ++
          LateReturnProbe.Terminator.selectionCode
            (first :: rest)).pcAfter := by
  let headCode :=
    LateReturnProbe.Terminator.firstSelection first
  let tailCode :=
    rest.flatMap LateReturnProbe.Terminator.nextSelection
  have hCodeEq :
      LateReturnProbe.Terminator.selectionCode (first :: rest) =
        headCode ++ tailCode := by
    simp [LateReturnProbe.Terminator.selectionCode,
      headCode, tailCode]
  have hAllFits :
      Assembly.Program.PCFitsFrom pre (headCode ++ tailCode) := by
    simpa [hCodeEq] using hFits
  have hHeadFits :
      Assembly.Program.PCFitsFrom pre headCode :=
    Assembly.Program.PCFitsFrom.left hAllFits
  have hTailFits :
      Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode :=
    Assembly.Program.PCFitsFrom.right hAllFits
  obtain ⟨firstDest, hFirstDest⟩ :=
    hResolved first (by simp)
  obtain ⟨mid, hHeadRun, hMidStack, hMidRuntime, hMidPc⟩ :=
    firstSelection_source_run
      (state := state) (token := token) (suffix := suffix)
      (site := first) (dest := firstDest)
      (pre := pre) (post := tailCode ++ post)
      hHeadFits hPc
      (by simpa [hCodeEq, headCode, List.append_assoc] using hFirstDest)
  let firstValue :=
    selectedAddress
      (pre ++ headCode ++ tailCode ++ post).labelPc token first
  have hHeadRun' :
      Assembly.Source.runNResult
          (pre ++ headCode ++ tailCode ++ post)
          headCode.length
          { state with stack := token :: suffix } =
        .ok (.running mid) := by
    simpa [headCode, tailCode, List.append_assoc] using hHeadRun
  have hMidStack' :
      mid.stack = firstValue :: token :: suffix := by
    simpa [firstValue, headCode, tailCode,
      List.append_assoc] using hMidStack
  have hMidPc' : mid.pc = (pre ++ headCode).pcAfter := by
    simpa [headCode] using hMidPc
  have hTailResolved :
      ∀ site ∈ rest,
        ∃ dest,
          ((pre ++ headCode) ++ tailCode ++ post).labelPc site.target =
            some dest := by
    intro site hSite
    obtain ⟨dest, hDest⟩ :=
      hResolved site (by simp [hSite])
    exact
      ⟨dest,
        by simpa [hCodeEq, headCode, tailCode,
            List.append_assoc] using hDest⟩
  obtain ⟨final, hTailRun, hFinalStack,
      hFinalRuntime, hFinalPc⟩ :=
    nextSelections_source_run
      (state := mid) (token := token) (accumulator := firstValue)
      (suffix := suffix) (sites := rest)
      (pre := pre ++ headCode) (post := post)
      hTailFits
      (by simpa [hMidStack'] using hMidPc')
      hTailResolved
  have hTailRun' :
      Assembly.Source.runNResult
          (pre ++ headCode ++ tailCode ++ post)
          tailCode.length mid =
        .ok (.running final) := by
    have hMidRecord :
        { mid with stack := firstValue :: token :: suffix } = mid := by
      rw [← hMidStack']
    rw [hMidRecord] at hTailRun
    simpa [tailCode, List.append_assoc] using hTailRun
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · rw [hCodeEq, List.length_append]
    simpa [List.append_assoc] using
      ((Assembly.Source.runNResult_add_of_running
          (pre ++ headCode ++ tailCode ++ post)
          headCode.length tailCode.length hHeadRun').trans hTailRun')
  · simpa [selectedAddressSum, firstValue,
      headCode, tailCode, List.append_assoc] using hFinalStack
  · calc
      Assembly.eraseRuntimeControl final =
          Assembly.eraseRuntimeControl
            { mid with
              stack :=
                rest.foldl
                    (fun value site =>
                      EvmYul.UInt256.add
                        (selectedAddress
                          (pre ++
                            headCode ++ tailCode ++ post).labelPc
                          token site)
                        value)
                    firstValue ::
                  token :: suffix } := by
        simpa [headCode, tailCode,
          List.append_assoc] using hFinalRuntime
      _ =
          Assembly.eraseRuntimeControl
            { state with
              stack :=
                rest.foldl
                    (fun value site =>
                      EvmYul.UInt256.add
                        (selectedAddress
                          (pre ++
                            headCode ++ tailCode ++ post).labelPc
                          token site)
                        value)
                    firstValue ::
                  token :: suffix } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := mid)
            (right :=
              { state with stack := firstValue :: token :: suffix })
            (stack :=
              rest.foldl
                  (fun value site =>
                    EvmYul.UInt256.add
                      (selectedAddress
                        (pre ++ headCode ++ tailCode ++ post).labelPc
                        token site)
                      value)
                  firstValue ::
                token :: suffix)
            (by
              simpa [firstValue, headCode, tailCode,
                List.append_assoc] using hMidRuntime)
      _ =
          Assembly.eraseRuntimeControl
            { state with
              stack :=
                selectedAddressSum
                    (pre ++
                      LateReturnProbe.Terminator.selectionCode
                        (first :: rest) ++
                      post).labelPc
                    token (first :: rest) ::
                  token :: suffix } := by
        simp [selectedAddressSum, firstValue, hCodeEq,
          headCode, tailCode, List.append_assoc]
  · simpa [hCodeEq, headCode, tailCode,
      List.append_assoc] using hFinalPc

theorem selectionCode_returnGuard
    (sites : List ReturnSite) :
    ∀ instr ∈ LateReturnProbe.Terminator.selectionCode sites,
      ReturnGuardInstr instr := by
  intro instr hInstr
  cases sites with
  | nil =>
      simp [LateReturnProbe.Terminator.selectionCode] at hInstr
  | cons first rest =>
      simp only [
        LateReturnProbe.Terminator.selectionCode,
        LateReturnProbe.Terminator.firstSelection,
        LateReturnProbe.Terminator.nextSelection,
        List.mem_append, List.mem_cons, List.mem_singleton,
        List.mem_flatMap] at hInstr
      rcases hInstr with
        hInstr | ⟨site, _hSite, hInstr⟩
      · rcases hInstr with
          rfl | rfl | rfl | rfl | rfl | hImpossible
        all_goals simp_all [ReturnGuardInstr,
          Assembly.StackShuffle.dupInstr]
      · rcases hInstr with
          rfl | rfl | rfl | rfl | rfl | rfl | hImpossible
        all_goals simp_all [ReturnGuardInstr,
          Assembly.StackShuffle.dupInstr]

theorem lateReturnTail_openRunUntilTransferWithPolicy
    {caseLabel : Label} {destination : Word}
    {suffix : List Word} {pre post : Assembly.Program}
    {state : Assembly.EVMState}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        [ Assembly.StackShuffle.dupInstr 1
        , .jumpi caseLabel
        , .prim .invalid
        , .label caseLabel
        , .jumpDynamic
        ])
    (hPc :
      ({ state with stack := destination :: suffix }).pc =
        pre.pcAfter)
    (hLabels :
      ((pre ++
          [ Assembly.StackShuffle.dupInstr 1
          , .jumpi caseLabel
          , .prim .invalid
          , .label caseLabel
          , .jumpDynamic
          ] ++ post).labels).Nodup) :
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++
          [ Assembly.StackShuffle.dupInstr 1
          , .jumpi caseLabel
          , .prim .invalid
          , .label caseLabel
          , .jumpDynamic
          ] ++ post)
        5
        { state with stack := destination :: suffix } =
      if destination = EvmYul.UInt256.ofNat 0 then
        .done (.error .InvalidInstruction)
      else
        .done
          (.ok
            (.running
              { state with stack := suffix, pc := destination })) := by
  let duplicate := Assembly.StackShuffle.dupInstr 1
  let tail : Assembly.Program :=
    [ .jumpi caseLabel
    , .prim .invalid
    , .label caseLabel
    , .jumpDynamic
    ]
  let start : Assembly.EVMState :=
    { state with stack := destination :: suffix }
  let afterDup : Assembly.EVMState :=
    start.replaceStackAndIncrPC
      (destination :: destination :: suffix)
  have hAllFits :
      Assembly.Program.PCFitsFrom pre (duplicate :: tail) := by
    simpa [duplicate, tail] using hFits
  have hDupFits : pre.PCFits := hAllFits.1
  have hDupCodeFits :
      Assembly.Program.PCFitsFrom pre [duplicate] :=
    Assembly.Program.PCFitsFrom.left hAllFits
  have hTailFits :
      Assembly.Program.PCFitsFrom (pre ++ [duplicate]) tail := by
    simpa [List.append_assoc] using hAllFits.2
  have hDupStep :
      Assembly.Target.stepInstr
          (Assembly.StackShuffle.targetInstr duplicate) start =
        .ok afterDup := by
    rw [show duplicate = Assembly.StackShuffle.dupInstr 1 from rfl]
    rw [Assembly.StackShuffle.dupInstr_step_eq_dup (by omega) (by omega)]
    simpa [afterDup, start, List.append_assoc] using
      (Assembly.StackShuffle.dup_append_token
        (state := state) (front := [])
        (suffix := suffix) (token := destination))
  have hDupSource :
      Assembly.Source.stepResult
          (pre ++ duplicate :: (tail ++ post)) start =
        .ok (.running afterDup) := by
    simpa [List.append_assoc] using
      Assembly.StackShuffle.source_stepResult_local
        (instr := duplicate) (pre := pre)
        (post := tail ++ post)
        (state := start) (final := afterDup)
        (Assembly.StackShuffle.dupInstr_sourceLocal
          (by omega) (by omega))
        (Assembly.StackShuffle.dupInstr_haltKind?_none
          (by omega) (by omega))
        hDupFits (by simpa [start] using hPc) hDupStep
  have hDupRun :
      Assembly.Source.runNResult
          (pre ++ duplicate :: (tail ++ post)) 1 start =
        .ok (.running afterDup) := by
    unfold Assembly.Source.runNResult Assembly.Control.runNResultWith
    rw [hDupSource]
    rfl
  have hAfterDupPc :
      afterDup.pc = (pre ++ [duplicate]).pcAfter := by
    calc
      afterDup.pc = start.pc + EvmYul.UInt256.ofNat 1 := by
        simp [afterDup, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      _ = pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
        rw [show start.pc = pre.pcAfter by simpa [start] using hPc]
      _ = (pre ++ [duplicate]).pcAfter := by
        simpa [duplicate, Assembly.StackShuffle.dupInstr,
          Assembly.Instr.byteSize]
          using (Assembly.Program.pcAfter_snoc pre duplicate).symm
  have hDupOpen :=
    returnGuardCode_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (code := [duplicate]) (pre := pre) (post := tail ++ post)
      (state := start) (final := afterDup) 4
      (by
        intro instr hInstr
        simp only [List.mem_singleton] at hInstr
        subst instr
        simp [duplicate, Assembly.StackShuffle.dupInstr,
          ReturnGuardInstr])
      hDupCodeFits
      (by simpa [start] using hPc)
      (by simpa [List.append_assoc] using hDupRun)
  have hTailRaw :=
    dynamicReturnTail_openRunUntilTransferWithPolicy
      (caseLabel := caseLabel)
      (accumulator := destination) (token := destination)
      (suffix := suffix)
      (pre := pre ++ [duplicate]) (post := post)
      (state := afterDup)
      (by simpa [tail] using hTailFits)
      (by simp [afterDup, start, hAfterDupPc])
      (by
        simpa [duplicate, tail, List.append_assoc] using hLabels)
  have hTail :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ duplicate :: (tail ++ post)) 4 afterDup =
        if destination = EvmYul.UInt256.ofNat 0 then
          .done (.error .InvalidInstruction)
        else
          .done
            (.ok
              (.running
                { state with
                  stack := suffix
                  pc := destination })) := by
    simpa [afterDup, start, tail, List.append_assoc] using hTailRaw
  have hDupOpen' :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ duplicate :: (tail ++ post)) 5 start =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ duplicate :: (tail ++ post)) 4 afterDup := by
    simpa [List.append_assoc] using hDupOpen
  simpa [duplicate, tail, start, List.append_assoc] using
    hDupOpen'.trans hTail

set_option maxHeartbeats 1000000 in
theorem dynamicReturnCode_openRunUntilTransfer_to_tail
    {depth : Nat} {first : ReturnSite} {rest : List ReturnSite}
    {token : Word} {target : Assembly.EVMState}
    {pre post : Assembly.Program}
    (hBound : depth < 16)
    (hTargetGet : target.stack[depth]? = some token)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (LateReturnProbe.Terminator.dynamicReturnCode
          depth (first :: rest)))
    (hPc : target.pc = pre.pcAfter)
    (hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++
              LateReturnProbe.Terminator.dynamicReturnCode
                depth (first :: rest) ++
              post).labelPc site.target =
            some dest) :
    let accumulator :=
      selectedAddressSum
        (pre ++
          LateReturnProbe.Terminator.dynamicReturnCode
            depth (first :: rest) ++
          post).labelPc
        token (first :: rest)
    ∃ tested,
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            LateReturnProbe.Terminator.dynamicReturnCode
              depth (first :: rest) ++
            post)
          (LateReturnProbe.Terminator.dynamicReturnCode
            depth (first :: rest)).length
          target =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            LateReturnProbe.Terminator.dynamicReturnCode
              depth (first :: rest) ++
            post)
          5 tested ∧
      tested.stack = accumulator :: target.stack.eraseIdx depth ∧
      Assembly.eraseRuntimeControl tested =
        Assembly.eraseRuntimeControl
          { target with
            stack := accumulator :: target.stack.eraseIdx depth } ∧
      tested.pc =
        (pre ++
          Assembly.StackShuffle.guardedLiftBuriedToTop depth ++
          LateReturnProbe.Terminator.selectionCode (first :: rest) ++
          Assembly.StackShuffle.removeBuriedUnder 1).pcAfter := by
  let front := target.stack.take depth
  let suffix := target.stack.drop (depth + 1)
  let lift := Assembly.StackShuffle.guardedLiftBuriedToTop depth
  let selection :=
    LateReturnProbe.Terminator.selectionCode (first :: rest)
  let remove := Assembly.StackShuffle.removeBuriedUnder 1
  let tail : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 1
    , .jumpi first.caseLabel
    , .prim .invalid
    , .label first.caseLabel
    , .jumpDynamic
    ]
  let code :=
    LateReturnProbe.Terminator.dynamicReturnCode
      depth (first :: rest)
  let whole := pre ++ code ++ post
  let accumulator :=
    selectedAddressSum whole.labelPc token (first :: rest)
  have hTargetStack :
      target.stack = front ++ token :: suffix := by
    simpa [front, suffix] using
      (ReturnAddressRelation.list_eq_take_get_drop hTargetGet)
  have hDepthLt : depth < target.stack.length :=
    (List.getElem?_eq_some_iff.mp hTargetGet).choose
  have hFrontLength : front.length = depth := by
    simp [front, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hDepthLt)]
  have hErase :
      target.stack.eraseIdx depth = front ++ suffix := by
    simpa [front, suffix] using
      (ReturnAddressRelation.eraseIdx_eq_take_drop_of_get? hTargetGet)
  have hCodeEq :
      code = lift ++ selection ++ remove ++ tail := by
    simp [code, lift, selection, remove, tail,
      LateReturnProbe.Terminator.dynamicReturnCode,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (lift ++ selection ++ remove ++ tail) := by
    simpa [code, hCodeEq] using hFits
  have hLiftFits :
      Assembly.Program.PCFitsFrom pre lift := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [List.append_assoc] using hFitsAll
  have hAfterLiftFits :
      Assembly.Program.PCFitsFrom (pre ++ lift)
        (selection ++ remove ++ tail) := by
    apply Assembly.Program.PCFitsFrom.right
    simpa [List.append_assoc] using hFitsAll
  have hSelectionFits :
      Assembly.Program.PCFitsFrom (pre ++ lift) selection := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [List.append_assoc] using hAfterLiftFits
  have hAfterSelectionFits :
      Assembly.Program.PCFitsFrom
        (pre ++ lift ++ selection) (remove ++ tail) := by
    have hAfterLiftFits' :
        Assembly.Program.PCFitsFrom (pre ++ lift)
          (selection ++ (remove ++ tail)) := by
      simpa [List.append_assoc] using hAfterLiftFits
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right hAfterLiftFits')
  have hRemoveFits :
      Assembly.Program.PCFitsFrom
        (pre ++ lift ++ selection) remove :=
    Assembly.Program.PCFitsFrom.left hAfterSelectionFits
  let lifted : Assembly.EVMState :=
    { target with
      stack := token :: (front ++ suffix)
      pc := (pre ++ lift).pcAfter }
  have hInitialRecord :
      { target with stack := front ++ token :: suffix } = target := by
    cases target
    simpa using hTargetStack.symm
  have hLift :=
    Assembly.StackShuffle.InteractionPreservation.guardedLiftBuriedToTop_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (front := front) (suffix := suffix) (token := token)
      (pre := pre) (post := selection ++ remove ++ tail ++ post)
      (state := target)
      (fuel := (5 + remove.length) + selection.length)
      (by simpa [hFrontLength, lift] using hLiftFits)
      (by simpa [hInitialRecord] using hPc)
      (by omega)
  have hLiftOpen :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          whole code.length target =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          whole ((5 + remove.length) + selection.length) lifted := by
    have hLift' := hLift
    rw [hFrontLength] at hLift'
    rw [hInitialRecord] at hLift'
    rw [show
      code.length =
        ((5 + remove.length) + selection.length) + lift.length by
      rw [hCodeEq]
      simp [tail]
      omega]
    simpa [whole, hCodeEq, lift, lifted,
      List.append_assoc] using hLift'
  have hResolvedSelection :
      ∀ site ∈ first :: rest,
        ∃ dest,
          ((pre ++ lift) ++ selection ++ remove ++ tail ++ post).labelPc
              site.target =
            some dest := by
    intro site hSite
    obtain ⟨dest, hDest⟩ := hResolved site hSite
    exact
      ⟨dest,
        by
          simpa [whole, code, hCodeEq,
            List.append_assoc] using hDest⟩
  obtain ⟨selected, hSelectionRun, hSelectedStack,
      hSelectedRuntime, hSelectedPc⟩ :=
    selectionCode_source_run
      (state := lifted) (token := token)
      (suffix := front ++ suffix)
      (first := first) (rest := rest)
      (pre := pre ++ lift) (post := remove ++ tail ++ post)
      (by simpa [selection] using hSelectionFits)
      (by simp [lifted])
      (by
        intro site hSite
        simpa [selection, List.append_assoc] using
          hResolvedSelection site hSite)
  have hLiftedRecord :
      { lifted with stack := token :: (front ++ suffix) } = lifted := by
    rfl
  have hSelectionRun' :
      Assembly.Source.runNResult
          ((pre ++ lift) ++ selection ++ (remove ++ tail ++ post))
          selection.length lifted =
        .ok (.running selected) := by
    have hRun := hSelectionRun
    rw [hLiftedRecord] at hRun
    simpa [selection, List.append_assoc] using hRun
  have hSelectionOpenRaw :=
    returnGuardCode_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (code := selection) (pre := pre ++ lift)
      (post := remove ++ tail ++ post)
      (state := lifted) (final := selected)
      (5 + remove.length)
      (by
        intro instr hInstr
        exact
          selectionCode_returnGuard (first :: rest)
            instr (by simpa [selection] using hInstr))
      hSelectionFits (by simp [lifted]) hSelectionRun'
  have hSelectionOpen :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          whole ((5 + remove.length) + selection.length) lifted =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          whole (5 + remove.length) selected := by
    simpa [whole, hCodeEq, List.append_assoc] using hSelectionOpenRaw
  have hSelectedStack' :
      selected.stack =
        accumulator :: token :: (front ++ suffix) := by
    simpa [accumulator, whole, code, hCodeEq, selection,
      List.append_assoc] using hSelectedStack
  have hSelectedPc' :
      selected.pc = (pre ++ lift ++ selection).pcAfter := by
    simpa [selection, List.append_assoc] using hSelectedPc
  have hSelectedRecord :
      { selected with
        stack := accumulator :: token :: (front ++ suffix) } =
      selected := by
    rw [← hSelectedStack']
  let tested : Assembly.EVMState :=
    { selected with
      stack := accumulator :: (front ++ suffix)
      pc := (pre ++ lift ++ selection ++ remove).pcAfter }
  have hRemoveRaw :=
    Assembly.StackShuffle.InteractionPreservation.removeBuriedUnder_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (front := [accumulator]) (suffix := front ++ suffix)
      (token := token)
      (pre := pre ++ lift ++ selection)
      (post := tail ++ post)
      (state := selected) (fuel := 5)
      (by simpa [remove] using hRemoveFits)
      (by simpa [hSelectedRecord] using hSelectedPc')
      (by simp)
  have hRemoveOpen :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          whole (5 + remove.length) selected =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          whole 5 tested := by
    have hRemove := hRemoveRaw
    simp only [List.length_singleton, List.singleton_append] at hRemove
    rw [hSelectedRecord] at hRemove
    simpa [whole, hCodeEq, remove, tested,
      List.append_assoc] using hRemove
  refine
    ⟨tested,
      hLiftOpen.trans (hSelectionOpen.trans hRemoveOpen),
      ?_, ?_, ?_⟩
  · simp [tested, hErase, accumulator, whole, code,
      List.append_assoc]
  · calc
      Assembly.eraseRuntimeControl tested =
          Assembly.eraseRuntimeControl
              { selected with
              stack := accumulator :: (front ++ suffix) } := by
        simp [tested, Assembly.eraseRuntimeControl]
      _ =
          Assembly.eraseRuntimeControl
              { lifted with
              stack := accumulator :: (front ++ suffix) } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := selected)
            (right :=
                { lifted with
                stack := accumulator :: token :: (front ++ suffix) })
            (stack := accumulator :: (front ++ suffix))
            (by
              simpa [accumulator, whole, code, hCodeEq,
                selection, List.append_assoc] using hSelectedRuntime)
      _ =
          Assembly.eraseRuntimeControl
              { target with
              stack := accumulator :: (front ++ suffix) } := by
        cases target
        rfl
      _ =
          Assembly.eraseRuntimeControl
            { target with
              stack := accumulator :: target.stack.eraseIdx depth } := by
        simp [hErase]
  · simp [tested, lift, selection, remove, List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem returnDispatch_openRunUntilTransfer_rel
    {shape : Shape} {returnCount depth : Nat}
    {first : ReturnSite} {rest : List ReturnSite}
    {token : Word}
    {code pre post : Assembly.Program} {state : Assembly.EVMState}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hCode :
      code =
        LateReturnProbe.Terminator.dynamicReturnCode
          depth (first :: rest))
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = some token)
    (hUnique :
      ReturnAddressRelation.TokensUnique (first :: rest))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolvedNonzero :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++ code ++ post).labelPc site.target = some dest ∧
            EvmYul.UInt256.ofNat dest ≠ EvmYul.UInt256.ofNat 0)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Simulation.Interaction.Rel
      (TypedCfg.Preservation.Block.RunSimulates (pre ++ code ++ post))
      (.done
        (.ok
          (TypedCfg.Block.runTerm shape
            (.returnDispatch returnCount (first :: rest)) state)))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++ code ++ post) code.length state) := by
  subst returnCount
  subst code
  let code :=
    LateReturnProbe.Terminator.dynamicReturnCode
      depth (first :: rest)
  let lift := Assembly.StackShuffle.guardedLiftBuriedToTop depth
  let selection :=
    LateReturnProbe.Terminator.selectionCode (first :: rest)
  let remove := Assembly.StackShuffle.removeBuriedUnder 1
  let tail : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 1
    , .jumpi first.caseLabel
    , .prim .invalid
    , .label first.caseLabel
    , .jumpDynamic
    ]
  have hCodeEq :
      code = lift ++ selection ++ remove ++ tail := by
    simp [code, lift, selection, remove, tail,
      LateReturnProbe.Terminator.dynamicReturnCode,
      List.append_assoc]
  have hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++ code ++ post).labelPc site.target =
            some dest := by
    intro site hSite
    obtain ⟨dest, hDest, _hNonzero⟩ :=
      hResolvedNonzero site hSite
    exact ⟨dest, by simpa [code] using hDest⟩
  obtain ⟨tested, hPrefixRun, hTestedStack,
      hTestedRuntime, hTestedPc⟩ :=
    dynamicReturnCode_openRunUntilTransfer_to_tail
      (depth := depth) (first := first) (rest := rest)
      (token := token) (target := state)
      (pre := pre) (post := post)
      hBound hGet
      (by simpa [code] using hFits)
      hPc
      (by simpa [code] using hResolved)
  let accumulator :=
    selectedAddressSum
      (pre ++ code ++ post).labelPc token (first :: rest)
  have hTestedStack' :
      tested.stack =
        accumulator :: state.stack.eraseIdx depth := by
    simpa [accumulator, code] using hTestedStack
  have hTestedRecord :
      { tested with
        stack := accumulator :: state.stack.eraseIdx depth } =
      tested := by
    cases tested
    simpa using hTestedStack'.symm
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (lift ++ selection ++ remove ++ tail) := by
    simpa [code, hCodeEq] using hFits
  have hTailFits :
      Assembly.Program.PCFitsFrom
        (pre ++ lift ++ selection ++ remove) tail := by
    have hFirst :
        Assembly.Program.PCFitsFrom pre
          ((lift ++ selection ++ remove) ++ tail) := by
      simpa [List.append_assoc] using hFitsAll
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right hFirst)
  have hTailRunRaw :=
    lateReturnTail_openRunUntilTransferWithPolicy
      (caseLabel := first.caseLabel)
      (destination := accumulator)
      (suffix := state.stack.eraseIdx depth)
      (pre := pre ++ lift ++ selection ++ remove)
      (post := post) (state := tested)
      (by simpa [tail] using hTailFits)
      (by
        simpa [hTestedRecord, lift, selection, remove,
          List.append_assoc] using hTestedPc)
      (by
        simpa [code, hCodeEq, tail,
          List.append_assoc] using hLabels)
  have hTailRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) 5 tested =
        if accumulator = EvmYul.UInt256.ofNat 0 then
          .done (.error .InvalidInstruction)
        else
          .done
            (.ok
              (.running
                { tested with
                  stack := state.stack.eraseIdx depth
                  pc := accumulator })) := by
    have hRun := hTailRunRaw
    rw [hTestedRecord] at hRun
    simpa [hCodeEq, tail, List.append_assoc] using hRun
  have hFullRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++ code ++ post) code.length state =
        if accumulator = EvmYul.UInt256.ofNat 0 then
          .done (.error .InvalidInstruction)
        else
          .done
            (.ok
              (.running
                { tested with
                  stack := state.stack.eraseIdx depth
                  pc := accumulator })) := by
    have hPrefixRun' :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ code ++ post) code.length state =
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (pre ++ code ++ post) 5 tested := by
      simpa [code] using hPrefixRun
    exact hPrefixRun'.trans hTailRun
  cases hFind :
      TypedCfg.Block.ReturnSite.findTarget?
        token (first :: rest) with
  | none =>
      have hAccumulatorZero :
          accumulator = EvmYul.UInt256.ofNat 0 := by
        apply selectedAddressSum_eq_zero_of_all_ne
        exact
          TypedCfg.Preservation.ReturnSite.findTarget?_eq_none_all_ne
            hFind
      rw [hFullRun, hAccumulatorZero]
      apply Simulation.Interaction.Rel.done
      simp [TypedCfg.Preservation.Block.RunSimulates,
        TypedCfg.Block.runTerm, hDepth, hGet, hFind,
        TypedCfg.Preservation.Outcome.Simulates]
  | some targetLabel =>
      obtain ⟨selected, hSelectedMem,
          hSelectedToken, hSelectedTarget⟩ :=
        TypedCfg.Block.ReturnSite.mem_token_of_findTarget?_eq_some
          hFind
      obtain ⟨dest, hResolve, hDestNonzero⟩ :=
        hResolvedNonzero selected hSelectedMem
      have hAccumulatorSelected :
          accumulator = EvmYul.UInt256.ofNat dest := by
        apply selectedAddressSum_eq_of_unique
          hUnique hSelectedMem hSelectedToken
        simpa [code] using hResolve
      have hTestedRuntimeSelected :
          Assembly.eraseRuntimeControl tested =
            Assembly.eraseRuntimeControl
              { state with
                stack := EvmYul.UInt256.ofNat dest ::
                  state.stack.eraseIdx depth } := by
        calc
          Assembly.eraseRuntimeControl tested =
              Assembly.eraseRuntimeControl
                { state with
                  stack := accumulator ::
                    state.stack.eraseIdx depth } :=
            hTestedRuntime
          _ =
              Assembly.eraseRuntimeControl
                { state with
                  stack := EvmYul.UInt256.ofNat dest ::
                    state.stack.eraseIdx depth } := by
            rw [hAccumulatorSelected]
      rw [hFullRun, hAccumulatorSelected, if_neg hDestNonzero]
      apply Simulation.Interaction.Rel.done
      simp [TypedCfg.Block.runTerm, hDepth, hGet, hFind,
        TypedCfg.Preservation.Block.RunSimulates,
        TypedCfg.Preservation.Outcome.Simulates]
      refine ⟨dest, ?_, rfl, ?_⟩
      · simpa [hSelectedTarget, code] using hResolve
      · show
          Assembly.SameRuntimeData
            { tested with
              stack := state.stack.eraseIdx depth
              pc := EvmYul.UInt256.ofNat dest }
            { state with stack := state.stack.eraseIdx depth }
        calc
          Assembly.eraseRuntimeControl
              { tested with
                stack := state.stack.eraseIdx depth
                pc := EvmYul.UInt256.ofNat dest } =
              Assembly.eraseRuntimeControl
                { tested with
                  stack := state.stack.eraseIdx depth } := by
            rfl
          _ =
              Assembly.eraseRuntimeControl
                { state with
                  stack := state.stack.eraseIdx depth } := by
            exact
              Assembly.eraseRuntimeControl_with_stack_congr
                (left := tested)
                (right :=
                  { state with
                    stack :=
                      EvmYul.UInt256.ofNat dest ::
                        state.stack.eraseIdx depth })
                (stack := state.stack.eraseIdx depth)
                hTestedRuntimeSelected

/--
When the logical return token is absent, the first instruction of late
materialisation is its guarded `DUP`; that instruction fails before any label
address is materialised.
-/
theorem returnDispatch_missing_token_openRunUntilTransfer_rel
    {shape : Shape} {returnCount depth : Nat}
    {first : ReturnSite} {rest : List ReturnSite}
    {code pre post : Assembly.Program} {state : Assembly.EVMState}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hCode :
      code =
        LateReturnProbe.Terminator.dynamicReturnCode
          depth (first :: rest))
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = none)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Simulation.Interaction.Rel
      (TypedCfg.Preservation.Block.RunSimulates (pre ++ code ++ post))
      (.done
        (.ok
          (TypedCfg.Block.runTerm shape
            (.returnDispatch returnCount (first :: rest)) state)))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre ++ code ++ post) code.length state) := by
  subst returnCount
  subst code
  let duplicate :=
    Assembly.StackShuffle.dupInstr (depth + 1)
  let tail : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 1
    , .jumpi first.caseLabel
    , .prim .invalid
    , .label first.caseLabel
    , .jumpDynamic
    ]
  let restCode : Assembly.Program :=
    Assembly.Instr.prim .pop ::
      (Assembly.StackShuffle.liftBuriedToTop depth ++
        LateReturnProbe.Terminator.selectionCode (first :: rest) ++
        Assembly.StackShuffle.removeBuriedUnder 1 ++ tail)
  have hCodeHead :
      LateReturnProbe.Terminator.dynamicReturnCode
          depth (first :: rest) =
        duplicate :: restCode := by
    simp [LateReturnProbe.Terminator.dynamicReturnCode,
      Assembly.StackShuffle.guardedLiftBuriedToTop,
      Assembly.StackShuffle.guardBuried, duplicate, restCode, tail,
      List.append_assoc]
  have hFitsHead :
      Assembly.Program.PCFitsFrom pre (duplicate :: restCode) := by
    simpa [hCodeHead] using hFits
  have hLen : state.stack.length ≤ depth := by
    rw [List.getElem?_eq_none_iff] at hGet
    exact hGet
  have hDupError :
      Assembly.Target.stepInstr
          (Assembly.StackShuffle.targetInstr duplicate) state =
        .error .StackUnderflow := by
    rw [show
      duplicate =
        Assembly.StackShuffle.dupInstr (depth + 1) from rfl]
    rw [Assembly.StackShuffle.dupInstr_step_eq_dup
      (by omega) (by omega)]
    simp [EvmYul.dup,
      show ¬depth + 1 ≤ state.stack.length by omega]
  have hDupOpen :
      Assembly.InteractionSemantics.Source.openStepAtResult
          (pre ++ duplicate :: (restCode ++ post))
          pre.byteLength duplicate state =
        .done (.error .StackUnderflow) := by
    rw [
      Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
        (Assembly.StackShuffle.InteractionPreservation.openStepAt_dupInstr_eq_done
          (n := depth + 1) (by omega) (by omega))]
    have hLocal :
        Assembly.StackShuffle.SourceLocalInstr duplicate := by
      simpa [duplicate] using
        (Assembly.StackShuffle.dupInstr_sourceLocal
          (n := depth + 1) (by omega) (by omega))
    simp only [Assembly.Source.stepAtResult]
    rw [Assembly.StackShuffle.source_stepAt_eq_targetInstr hLocal,
      hDupError]
    rfl
  have hRunBase :=
    Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_error
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        (pre := pre) (post := restCode ++ post)
        (instr := duplicate) (state := state)
        (err := .StackUnderflow)
        restCode.length hFitsHead.1 hPc hDupOpen
  have hRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          (pre ++
            LateReturnProbe.Terminator.dynamicReturnCode
              depth (first :: rest) ++ post)
          (LateReturnProbe.Terminator.dynamicReturnCode
            depth (first :: rest)).length state =
        .done (.error .StackUnderflow) := by
    rw [hCodeHead]
    simpa [List.append_assoc] using hRunBase
  rw [hRun]
  apply Simulation.Interaction.Rel.done
  simp [TypedCfg.Preservation.Block.RunSimulates,
    TypedCfg.Block.runTerm, hDepth, hGet,
    TypedCfg.Preservation.Outcome.Simulates]

namespace Terminator

/--
The local token-side condition needed by late return materialisation.  Direct
terminators have no return-token obligation.
-/
def ReturnTokensUnique : TypedCfg.Terminator → Prop
  | .returnDispatch _ sites =>
      ReturnAddressRelation.TokensUnique sites
  | _ => True

/--
Only direct terminators need the standard symbolic-target premise.  Late
return dispatchers resolve their selected physical target through the stronger
nonzero condition below and do not emit the standard per-case labels.
-/
def DirectTargetsResolve
    (program : Assembly.Program) : TypedCfg.Terminator → Prop
  | .returnDispatch _ _ => True
  | term =>
      TypedCfg.Preservation.Terminator.ResolvedTargets program term

/--
Every physical return target used by a late dispatcher resolves to a nonzero
EVM word.  Zero is reserved as the fail-closed "no case selected" sentinel.
-/
def ReturnTargetsResolveNonzero
    (program : Assembly.Program) : TypedCfg.Terminator → Prop
  | .returnDispatch _ sites =>
      ∀ site ∈ sites,
        ∃ dest,
          program.labelPc site.target = some dest ∧
            EvmYul.UInt256.ofNat dest ≠ EvmYul.UInt256.ofNat 0
  | _ => True

set_option maxHeartbeats 1000000 in
/--
Adjacent open-world preservation for every successfully late-lowered
terminator.  Direct terminators reuse the standard lowering theorem; only a
return dispatcher enters the late-address proof above.
-/
theorem lowerAt?_openRunUntilTransfer_rel
    {shape : Shape} {term : TypedCfg.Terminator}
    {code pre post : Assembly.Program} {state : Assembly.EVMState}
    (hLower :
      LateReturnProbe.Terminator.lowerAt? shape term = some code)
    (hUnique : ReturnTokensUnique term)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      DirectTargetsResolve (pre ++ code ++ post) term)
    (hResolvedNonzero :
      ReturnTargetsResolveNonzero (pre ++ code ++ post) term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Simulation.Interaction.Rel
      (TypedCfg.Preservation.Block.RunSimulates
        (pre ++ code ++ post))
      (.done (TypedCfg.Block.runTermChecked shape term state))
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy term)
        (pre ++ code ++ post) code.length state) := by
  cases term with
  | fallthrough next =>
      have hStandard :
          TypedCfg.Terminator.lowerAt? shape (.fallthrough next) =
            some code := by
        simpa [LateReturnProbe.Terminator.lowerAt?] using hLower
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (TypedCfg.InteractionPreservation.Terminator.lowerAt?_openRunUntilTransfer_rel_of_direct
            (term := .fallthrough next)
            (by simp [TypedCfg.Preservation.Terminator.Direct])
            hStandard hFits hPc hResolved)
  | jump target =>
      have hStandard :
          TypedCfg.Terminator.lowerAt? shape (.jump target) =
            some code := by
        simpa [LateReturnProbe.Terminator.lowerAt?] using hLower
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (TypedCfg.InteractionPreservation.Terminator.lowerAt?_openRunUntilTransfer_rel_of_direct
            (term := .jump target)
            (by simp [TypedCfg.Preservation.Terminator.Direct])
            hStandard hFits hPc hResolved)
  | jumpi target next =>
      have hStandard :
          TypedCfg.Terminator.lowerAt? shape (.jumpi target next) =
            some code := by
        simpa [LateReturnProbe.Terminator.lowerAt?] using hLower
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (TypedCfg.InteractionPreservation.Terminator.lowerAt?_openRunUntilTransfer_rel_of_direct
            (term := .jumpi target next)
            (by simp [TypedCfg.Preservation.Terminator.Direct])
            hStandard hFits hPc hResolved)
  | halt kind =>
      have hStandard :
          TypedCfg.Terminator.lowerAt? shape (.halt kind) =
            some code := by
        simpa [LateReturnProbe.Terminator.lowerAt?] using hLower
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (TypedCfg.InteractionPreservation.Terminator.lowerAt?_openRunUntilTransfer_rel_of_direct
            (term := .halt kind)
            (by simp [TypedCfg.Preservation.Terminator.Direct])
            hStandard hFits hPc hResolved)
  | invalid =>
      have hStandard :
          TypedCfg.Terminator.lowerAt? shape .invalid =
            some code := by
        simpa [LateReturnProbe.Terminator.lowerAt?] using hLower
      simpa [TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy,
        Assembly.InteractionSemantics.Source.openRunUntilTransfer] using
        (TypedCfg.InteractionPreservation.Terminator.lowerAt?_openRunUntilTransfer_rel_of_direct
            (term := .invalid)
            (by simp [TypedCfg.Preservation.Terminator.Direct])
            hStandard hFits hPc hResolved)
  | returnDispatch returnCount sites =>
      by_cases hSmall :
          sites.length ≤
            LateReturnProbe.Terminator.standardReturnSiteLimit
      · have hStandard :
            TypedCfg.Terminator.lowerAt? shape
                (.returnDispatch returnCount sites) =
              some code := by
          simpa [LateReturnProbe.Terminator.lowerAt?, hSmall] using hLower
        have hResolvedControl :
            TypedCfg.Preservation.Terminator.ResolvedControl
              (pre ++ code ++ post)
              (.returnDispatch returnCount sites) := by
          constructor
          · intro target hTarget
            simp only [TypedCfg.Terminator.targets,
              List.mem_map] at hTarget
            rcases hTarget with ⟨site, hSite, rfl⟩
            obtain ⟨dest, hDest, _hNonzero⟩ :=
              hResolvedNonzero site hSite
            exact ⟨dest, hDest⟩
          · intro label hLabel
            have hInstr :
                Assembly.Instr.label label ∈ code :=
              TypedCfg.Terminator.definedLabel_instr_mem_of_lowerAt?
                hStandard hLabel
            have hGlobal :
                Assembly.Instr.label label ∈ pre ++ code ++ post := by
              simp [hInstr]
            exact
              Assembly.Program.labelPc_exists_of_mem_labels
                (pre ++ code ++ post)
                (Assembly.Program.mem_labels_of_label_mem hGlobal)
        exact
          TypedCfg.InteractionPreservation.Terminator.lowerAt?_openRunUntilTransfer_rel
            hStandard hFits hPc hResolvedControl hLabels
      · cases hDepth : shape.returnTokenDepth? with
        | none =>
            simp [LateReturnProbe.Terminator.lowerAt?, hSmall, hDepth]
              at hLower
        | some depth =>
            cases sites with
            | nil =>
                simp at hSmall
            | cons first rest =>
                have hSmall' :
                    ¬rest.length + 1 ≤
                      LateReturnProbe.Terminator.standardReturnSiteLimit := by
                  simpa using hSmall
                by_cases hCount : depth = returnCount
                · subst returnCount
                  by_cases hBound : depth < 16
                  · have hCodeEq :
                        code =
                            LateReturnProbe.Terminator.dynamicReturnCode
                              depth (first :: rest) := by
                      simpa [LateReturnProbe.Terminator.lowerAt?, hSmall',
                        hDepth, hBound] using hLower.symm
                    cases hGet : state.stack[depth]? with
                    | none =>
                        simpa [
                          TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy] using
                          (returnDispatch_missing_token_openRunUntilTransfer_rel
                            (shape := shape) (returnCount := depth)
                            (depth := depth) (first := first) (rest := rest)
                            (code := code) (pre := pre) (post := post)
                            (state := state)
                            hDepth rfl hCodeEq hBound hGet hFits hPc)
                    | some token =>
                        simpa [
                          TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy] using
                          (returnDispatch_openRunUntilTransfer_rel
                            (shape := shape) (returnCount := depth)
                            (depth := depth) (first := first) (rest := rest)
                            (token := token)
                            (code := code) (pre := pre) (post := post)
                            (state := state)
                            hDepth rfl hCodeEq hBound hGet
                            (by simpa [ReturnTokensUnique] using hUnique)
                            hFits hPc
                            (by
                              simpa [ReturnTargetsResolveNonzero] using
                                hResolvedNonzero)
                            hLabels)
                  · simp [LateReturnProbe.Terminator.lowerAt?, hSmall',
                      hDepth, hBound] at hLower
                · simp [LateReturnProbe.Terminator.lowerAt?, hSmall',
                    hDepth, hCount] at hLower

end Terminator

namespace Block

private theorem bind_self_rel_of_allDone
    {Error Source LeftTarget RightTarget : Type}
    {property : Except Error Source → Prop}
    {doneRel :
      Except Error LeftTarget → Except Error RightTarget → Prop}
    {interaction : Simulation.Interaction Error Source}
    {leftNext :
      Source → Simulation.Interaction Error LeftTarget}
    {rightNext :
      Source → Simulation.Interaction Error RightTarget}
    (hInteraction :
      Simulation.Interaction.AllDone property interaction)
    (hError :
      ∀ err, property (.error err) →
        doneRel (.error err) (.error err))
    (hNext :
      ∀ value, property (.ok value) →
        Simulation.Interaction.Rel doneRel
          (leftNext value) (rightNext value)) :
    Simulation.Interaction.Rel doneRel
      (Simulation.Interaction.bind interaction leftNext)
      (Simulation.Interaction.bind interaction rightNext) := by
  induction hInteraction with
  | @done outcome hDone =>
      cases outcome with
      | error err =>
          exact .done (hError err hDone)
      | ok value =>
          exact hNext value hDone
  | request hResume ih =>
      exact .request ih

set_option maxHeartbeats 1000000 in
/--
Unchanged typed body execution composes with the late-lowered terminator.  The
only extra premises are the two fail-closed return-dispatch conditions.
-/
theorem lowerBodyThenTerm_openRun_rel
    {body : List TypedCfg.Instr} {input output : Shape}
    {term : TypedCfg.Terminator}
    {bodyCode termCode pre post : Assembly.Program}
    {state : Assembly.EVMState}
    (hBody :
      TypedCfg.Block.lowerBodyFrom? body input =
        some (bodyCode, output))
    (hTerm :
      LateReturnProbe.Terminator.lowerAt? output term =
        some termCode)
    (hUnique : Terminator.ReturnTokensUnique term)
    (hBodyFits :
      Assembly.Program.PCFitsFrom pre bodyCode)
    (hTermFits :
      Assembly.Program.PCFitsFrom (pre ++ bodyCode) termCode)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Terminator.DirectTargetsResolve
        (pre ++ bodyCode ++ termCode ++ post) term)
    (hResolvedNonzero :
      Terminator.ReturnTargetsResolveNonzero
        (pre ++ bodyCode ++ termCode ++ post) term)
    (hLabels :
      ((pre ++ bodyCode ++ termCode ++ post).labels).Nodup) :
    Simulation.Interaction.Rel
      (TypedCfg.Preservation.Block.RunSimulates
        (pre ++ bodyCode ++ termCode ++ post))
      (do
        let (mid, actualOutput) ←
          TypedCfg.InteractionSemantics.Block.openRunBody
            body input state
        if actualOutput = output then
          match TypedCfg.Block.runTermChecked output term mid with
          | .ok outcome => pure outcome
          | .error err => throw err
        else
          throw .InvalidInstruction)
      (do
        let bodyResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            (pre ++ bodyCode ++ termCode ++ post)
            bodyCode.length state
        match bodyResult with
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              (pre ++ bodyCode ++ termCode ++ post)
              termCode.length mid
        | .halted halt =>
            pure (.halted halt)) := by
  let program := pre ++ bodyCode ++ termCode ++ post
  let sourceBody :=
    TypedCfg.InteractionSemantics.Block.openRunBody
      body input state
  have hBodyRun :=
    TypedCfg.InteractionPreservation.Block.lowerBodyFrom?_source_openRunNResult
        (pre := pre) (post := termCode ++ post)
        hBody hBodyFits hPc
  have hBodyRun' :
      Assembly.InteractionSemantics.Source.openRunNResult
          program bodyCode.length state =
        Simulation.Interaction.map
          (fun result => Assembly.StepResult.running result.1)
          sourceBody := by
    simpa [program, sourceBody, List.append_assoc] using hBodyRun
  have hTargetEq :
      (do
        let bodyResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            program bodyCode.length state
        match bodyResult with
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              program termCode.length mid
        | .halted halt =>
            pure (.halted halt)) =
        Simulation.Interaction.bind sourceBody
          (fun result =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              program termCode.length result.1) := by
    rw [hBodyRun']
    change
      Simulation.Interaction.bind
          (Simulation.Interaction.bind sourceBody
            (fun result =>
              Simulation.Interaction.pure
                (Assembly.StepResult.running result.1)))
          (fun bodyResult =>
            match bodyResult with
            | .running mid =>
                Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                  (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                    term)
                  program termCode.length mid
            | .halted halt =>
                pure (.halted halt)) =
        Simulation.Interaction.bind sourceBody
          (fun result =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              program termCode.length result.1)
    rw [Simulation.Interaction.bind_assoc]
    congr 1
  rw [show
    pre ++ bodyCode ++ termCode ++ post = program by
    rfl]
  rw [hTargetEq]
  have hBodyEnd :=
    TypedCfg.InteractionPreservation.Block.openRunBody_atLoweredEnd
      (state := state) hBody
  have hRel :
      Simulation.Interaction.Rel
        (TypedCfg.Preservation.Block.RunSimulates program)
        (Simulation.Interaction.bind sourceBody
          (fun result =>
            if result.2 = output then
              match TypedCfg.Block.runTermChecked
                  output term result.1 with
              | .ok outcome => pure outcome
              | .error err => throw err
            else
              throw .InvalidInstruction))
        (Simulation.Interaction.bind sourceBody
          (fun result =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                term)
              program termCode.length result.1)) := by
    refine
      bind_self_rel_of_allDone
        (property :=
          TypedCfg.InteractionPreservation.Instr.AtLoweredEnd
            state bodyCode output)
        (doneRel := TypedCfg.Preservation.Block.RunSimulates program)
        (interaction := sourceBody)
        (leftNext := fun result =>
          if result.2 = output then
            match TypedCfg.Block.runTermChecked
                output term result.1 with
            | .ok outcome => pure outcome
            | .error err => throw err
          else
            throw .InvalidInstruction)
        (rightNext := fun result =>
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
              term)
            program termCode.length result.1)
        (by simpa [sourceBody] using hBodyEnd) ?_ ?_
    · intro err hError
      rfl
    · intro result hResult
      rcases result with ⟨mid, actualOutput⟩
      change
        mid.pc =
            state.pc +
              EvmYul.UInt256.ofNat bodyCode.byteLength ∧
          actualOutput = output at hResult
      rcases hResult with ⟨hMidDelta, hOutput⟩
      subst actualOutput
      have hMidPc :
          mid.pc = (pre ++ bodyCode).pcAfter := by
        calc
          mid.pc =
              state.pc +
                EvmYul.UInt256.ofNat bodyCode.byteLength :=
            hMidDelta
          _ =
              pre.pcAfter +
                EvmYul.UInt256.ofNat bodyCode.byteLength := by
            rw [hPc]
          _ = (pre ++ bodyCode).pcAfter := by
            exact
              (Assembly.Program.pcAfter_append pre bodyCode).symm
      have hTermRun :=
        Terminator.lowerAt?_openRunUntilTransfer_rel
          (pre := pre ++ bodyCode) (post := post)
          hTerm hUnique hTermFits hMidPc
          (by simpa [program, List.append_assoc] using hResolved)
          (by
            simpa [program, List.append_assoc] using
              hResolvedNonzero)
          (by simpa [program, List.append_assoc] using hLabels)
      cases hChecked :
          TypedCfg.Block.runTermChecked output term mid with
      | error err =>
          simpa [program, hChecked] using hTermRun
      | ok outcome =>
          simpa [program, hChecked] using hTermRun
  simpa [sourceBody] using hRel

set_option maxHeartbeats 1000000 in
/-- Whole-block adjacent preservation for late return materialisation. -/
theorem lower?_openRun_rel
    {block : TypedCfg.Block} {code pre post : Assembly.Program}
    {state : Assembly.EVMState}
    (hLower : LateReturnProbe.Block.lower? block = some code)
    (hUnique : Terminator.ReturnTokensUnique block.term)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Terminator.DirectTargetsResolve
        (pre ++ code ++ post) block.term)
    (hResolvedNonzero :
      Terminator.ReturnTargetsResolveNonzero
        (pre ++ code ++ post) block.term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Simulation.Interaction.Rel
      (TypedCfg.Preservation.Block.RunSimulates
        (pre ++ code ++ post))
      (TypedCfg.InteractionSemantics.Block.openRun
        block state.incrPC)
      (LateReturnProbe.CompiledBlock.openRun
        block (pre ++ code ++ post) state) := by
  unfold LateReturnProbe.Block.lower? at hLower
  cases hBody :
      TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm :
            LateReturnProbe.Terminator.lowerAt?
              block.output block.term with
        | none =>
            simp [hBody, hTerm] at hLower
        | some termCode =>
            simp [hBody, hTerm] at hLower
            subst code
            let program :=
              pre ++
                (Assembly.Instr.label block.label ::
                  bodyCode ++ termCode) ++ post
            let entry := state.incrPC
            have hLabelOpen :
                Assembly.InteractionSemantics.Source.openStepAtResult
                    (pre ++ Assembly.Instr.label block.label ::
                      ((bodyCode ++ termCode) ++ post))
                    pre.byteLength
                    (.label block.label) state =
                  .done (.ok (.running entry)) := by
              rw [
                Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
                  (by rfl)]
              simp [Assembly.Source.stepAtResult,
                Assembly.Source.stepAt,
                Assembly.Instr.haltKind?,
                Assembly.Target.stepInstr, entry]
            have hLabelRun :
                Assembly.InteractionSemantics.Source.openRunNResult
                    program 1 state =
                  .done (.ok (.running entry)) := by
              rw [show
                program =
                  pre ++ Assembly.Instr.label block.label ::
                    ((bodyCode ++ termCode) ++ post) by
                simp [program, List.append_assoc]]
              rw [
                Assembly.InteractionPreservation.source_openRunNResult_one_at_boundary
                  hFits.1 hPc]
              exact hLabelOpen
            have hEntryPc :
                entry.pc =
                  (pre ++
                    [Assembly.Instr.label block.label]).pcAfter := by
              calc
                entry.pc =
                    state.pc + EvmYul.UInt256.ofNat 1 := rfl
                _ =
                    pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
                  rw [hPc]
                _ =
                    (pre ++
                      [Assembly.Instr.label block.label]).pcAfter := by
                  simp [Assembly.Program.pcAfter,
                    Assembly.Program.byteLength_append,
                    Assembly.Program.byteLength,
                    Assembly.Instr.byteSize,
                    Assembly.UInt256_ofNat_add]
            have hBodyFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label])
                  bodyCode :=
              Assembly.Program.PCFitsFrom.left hFits.2
            have hTermFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label] ++
                    bodyCode)
                  termCode := by
              simpa [List.append_assoc] using
                Assembly.Program.PCFitsFrom.right hFits.2
            have hRest :=
              lowerBodyThenTerm_openRun_rel
                (body := block.body) (input := block.input)
                (output := block.output) (term := block.term)
                (bodyCode := bodyCode) (termCode := termCode)
                (pre :=
                  pre ++ [Assembly.Instr.label block.label])
                (post := post) (state := entry)
                hBody hTerm hUnique hBodyFits hTermFits hEntryPc
                (by simpa [program, List.append_assoc] using hResolved)
                (by
                  simpa [program, List.append_assoc] using
                    hResolvedNonzero)
                (by simpa [program, List.append_assoc] using hLabels)
            have hCompiledRun :
                LateReturnProbe.CompiledBlock.openRun
                    block program state =
                  (do
                    let bodyResult ←
                      Assembly.InteractionSemantics.Source.openRunNResult
                        program bodyCode.length entry
                    match bodyResult with
                    | .running mid =>
                        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                          (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                            block.term)
                          program termCode.length mid
                    | .halted halt =>
                        pure (.halted halt)) := by
              simp [LateReturnProbe.CompiledBlock.openRun,
                hBody, hTerm, hLabelRun]
              change
                Simulation.Interaction.bind
                    ((.done
                      (.ok (Assembly.StepResult.running entry))) :
                        Assembly.InteractionSemantics.OpenStepResult)
                    (fun labelResult =>
                      match labelResult with
                      | Assembly.StepResult.halted halt =>
                          pure (Assembly.StepResult.halted halt)
                      | Assembly.StepResult.running entry =>
                          do
                            let bodyResult ←
                              Assembly.InteractionSemantics.Source.openRunNResult
                                program bodyCode.length entry
                            match bodyResult with
                            | Assembly.StepResult.halted halt =>
                                pure (Assembly.StepResult.halted halt)
                            | Assembly.StepResult.running mid =>
                                Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                                  (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                                    block.term)
                                  program termCode.length mid) =
                  (do
                    let bodyResult ←
                      Assembly.InteractionSemantics.Source.openRunNResult
                        program bodyCode.length entry
                    match bodyResult with
                    | Assembly.StepResult.running mid =>
                        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                          (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                            block.term)
                          program termCode.length mid
                    | Assembly.StepResult.halted halt =>
                        pure (Assembly.StepResult.halted halt))
              rw [Simulation.Interaction.bind_done_ok]
              change
                Simulation.Interaction.bind
                    (Assembly.InteractionSemantics.Source.openRunNResult
                      program bodyCode.length entry)
                    (fun bodyResult =>
                      match bodyResult with
                      | Assembly.StepResult.halted halt =>
                          pure (Assembly.StepResult.halted halt)
                      | Assembly.StepResult.running mid =>
                          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                            (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                              block.term)
                            program termCode.length mid) =
                  Simulation.Interaction.bind
                    (Assembly.InteractionSemantics.Source.openRunNResult
                      program bodyCode.length entry)
                    (fun bodyResult =>
                      match bodyResult with
                      | Assembly.StepResult.running mid =>
                          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                            (TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
                              block.term)
                            program termCode.length mid
                      | Assembly.StepResult.halted halt =>
                          pure (Assembly.StepResult.halted halt))
              congr 1
              funext bodyResult
              cases bodyResult <;> rfl
            change
              Simulation.Interaction.Rel
                (TypedCfg.Preservation.Block.RunSimulates program)
                (TypedCfg.InteractionSemantics.Block.openRun
                  block entry)
                (LateReturnProbe.CompiledBlock.openRun
                  block program state)
            rw [hCompiledRun]
            simpa [
              TypedCfg.InteractionSemantics.Block.openRun,
              TypedCfg.InteractionSemantics.Block.openRunBody,
              TypedCfg.Control.Block.run,
              program, entry, List.append_assoc] using hRest
      · simp [hBody, hOutput] at hLower

end Block

namespace Program

theorem returnTargetsResolveNonzero_of_check
    {program : TypedCfg.Program} {assembly : Assembly.Program}
    (hCheck :
      LateReturnProbe.Program.returnTargetsResolveNonzero?
          program assembly =
        true) :
    ∀ site ∈ ReturnAddressLower.Program.returnSites program,
      ∃ dest,
        assembly.labelPc site.target = some dest ∧
          EvmYul.UInt256.ofNat dest ≠ EvmYul.UInt256.ofNat 0 := by
  intro site hSite
  unfold LateReturnProbe.Program.returnTargetsResolveNonzero? at hCheck
  have hSiteCheck :=
    (List.all_eq_true.mp hCheck) site hSite
  cases hResolve : assembly.labelPc site.target with
  | none =>
      simp [hResolve] at hSiteCheck
  | some dest =>
      refine ⟨dest, rfl, ?_⟩
      simpa [hResolve] using hSiteCheck

theorem returnTokensUnique_of_check
    {program : TypedCfg.Program} {block : TypedCfg.Block}
    (hCheck :
      LateReturnProbe.Program.localReturnTokensUnique? program = true)
    (hBlock : block ∈ program.blocks) :
    Terminator.ReturnTokensUnique block.term := by
  unfold LateReturnProbe.Program.localReturnTokensUnique? at hCheck
  have hBlockCheck :=
    (List.all_eq_true.mp hCheck) block hBlock
  cases hTerm : block.term with
  | returnDispatch _ sites =>
      exact
        (ReturnAddressRelation.tokensUnique?_eq_true_iff sites).mp
          (by
            simpa [ReturnAddressLower.Terminator.sites, hTerm] using
              hBlockCheck)
  | fallthrough _ | jump _ | jumpi _ _ | halt _ | invalid =>
      trivial

set_option maxHeartbeats 1000000 in
/--
One source CFG step is simulated by the corresponding late-lowered Assembly
block, with both dispatcher side conditions discharged from executable gates.
-/
theorem lower?_step_open_rel
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : Assembly.EVMState} {entryPc : Nat}
    (hLower : LateReturnProbe.Program.lower? program = some target)
    (hAccepted : target.acceptedWithDynamic = true)
    (hFits : target.PCFits)
    (hLocalUnique :
      LateReturnProbe.Program.localReturnTokensUnique? program = true)
    (hNonzero :
      LateReturnProbe.Program.returnTargetsResolveNonzero?
          program target =
        true)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    Simulation.Interaction.Rel
      (TypedCfg.Preservation.Block.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openStep
        program label state.incrPC)
      (LateReturnProbe.CompiledBlock.openRun
        block target state) := by
  rcases
      LateReturnProbe.Program.lower?_fragment_of_findBlock?
        hLower hFind with
    ⟨fragment⟩
  have hBlock : block ∈ program.blocks :=
    List.mem_of_find?_eq_some hFind
  have hBlockLabel : block.label = label := by
    have hFound :
        (block.label == label) = true :=
      @List.find?_some TypedCfg.Block
        (fun candidate : TypedCfg.Block =>
          candidate.label == label)
        block program.blocks hFind
    exact beq_iff_eq.mp hFound
  subst label
  have hLabels : target.labels.Nodup :=
    Assembly.Program.labels_nodup_of_acceptedWithDynamic hAccepted
  have hCodeFits :
      Assembly.Program.PCFitsFrom fragment.pre fragment.code := by
    apply Assembly.Program.PCFitsFrom.of_append
    rw [← fragment.target_eq]
    exact hFits
  have hResolveDirect :
      TypedCfg.Preservation.Terminator.Direct block.term →
        TypedCfg.Preservation.Terminator.ResolvedTargets
          target block.term := by
    intro hDirect symbolic hSymbolic
    rcases
        LateReturnProbe.Block.target_instr_mem_of_lower?_of_direct
          fragment.lower hDirect hSymbolic with
      ⟨instr, hInstr, hInstrTarget⟩
    have hInstrGlobal : instr ∈ target := by
      rw [fragment.target_eq]
      simp [hInstr]
    exact
      Assembly.Program.target_resolves_of_acceptedWithDynamic
        hAccepted hInstrGlobal hInstrTarget
  have hResolved :
      Terminator.DirectTargetsResolve target block.term := by
    cases hTerm : block.term with
    | returnDispatch returnCount sites =>
        trivial
    | fallthrough next =>
        simpa [Terminator.DirectTargetsResolve, hTerm] using
          (hResolveDirect
            (by
              simp [TypedCfg.Preservation.Terminator.Direct,
                hTerm]))
    | jump next =>
        simpa [Terminator.DirectTargetsResolve, hTerm] using
          (hResolveDirect
            (by
              simp [TypedCfg.Preservation.Terminator.Direct,
                hTerm]))
    | jumpi next fallback =>
        simpa [Terminator.DirectTargetsResolve, hTerm] using
          (hResolveDirect
            (by
              simp [TypedCfg.Preservation.Terminator.Direct,
                hTerm]))
    | halt kind =>
        simpa [Terminator.DirectTargetsResolve, hTerm] using
          (hResolveDirect
            (by
              simp [TypedCfg.Preservation.Terminator.Direct,
                hTerm]))
    | invalid =>
        simpa [Terminator.DirectTargetsResolve, hTerm] using
          (hResolveDirect
            (by
              simp [TypedCfg.Preservation.Terminator.Direct,
                hTerm]))
  have hAllNonzero :=
    returnTargetsResolveNonzero_of_check hNonzero
  have hResolvedNonzero :
      Terminator.ReturnTargetsResolveNonzero target block.term := by
    cases hTerm : block.term with
    | returnDispatch returnCount sites =>
        intro site hSite
        apply hAllNonzero site
        apply ReturnAddressLower.term_site_mem_returnSites hBlock
        simpa [ReturnAddressLower.Terminator.sites, hTerm] using
          hSite
    | fallthrough next =>
        simp [Terminator.ReturnTargetsResolveNonzero]
    | jump next =>
        simp [Terminator.ReturnTargetsResolveNonzero]
    | jumpi next fallback =>
        simp [Terminator.ReturnTargetsResolveNonzero]
    | halt kind =>
        simp [Terminator.ReturnTargetsResolveNonzero]
    | invalid =>
        simp [Terminator.ReturnTargetsResolveNonzero]
  have hUnique :
      Terminator.ReturnTokensUnique block.term :=
    returnTokensUnique_of_check hLocalUnique hBlock
  rcases
      LateReturnProbe.Block.lower?_starts_with_label fragment.lower with
    ⟨tail, hCode⟩
  have hEntryLabel :
      target.labelPc block.label =
        some fragment.pre.byteLength := by
    have hNodup :
        (fragment.pre ++
          Assembly.Instr.label block.label ::
            (tail ++ fragment.post)).labels.Nodup := by
      simpa [fragment.target_eq, hCode, List.append_assoc] using
        hLabels
    have hAt :=
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        fragment.pre (tail ++ fragment.post) hNodup
    simpa [fragment.target_eq, hCode, List.append_assoc] using hAt
  have hEntryPcEq :
      entryPc = fragment.pre.byteLength := by
    rw [hEntryLabel] at hLabelPc
    exact (Option.some.inj hLabelPc).symm
  have hStatePc : state.pc = fragment.pre.pcAfter := by
    calc
      state.pc = EvmYul.UInt256.ofNat entryPc := hPc
      _ =
          EvmYul.UInt256.ofNat fragment.pre.byteLength := by
        rw [hEntryPcEq]
      _ = fragment.pre.pcAfter := rfl
  have hResolvedFragment :
      Terminator.DirectTargetsResolve
        (fragment.pre ++ fragment.code ++ fragment.post)
        block.term := by
    rw [← fragment.target_eq]
    exact hResolved
  have hNonzeroFragment :
      Terminator.ReturnTargetsResolveNonzero
        (fragment.pre ++ fragment.code ++ fragment.post)
        block.term := by
    rw [← fragment.target_eq]
    exact hResolvedNonzero
  have hLabelsFragment :
      ((fragment.pre ++ fragment.code ++
        fragment.post).labels).Nodup := by
    rw [← fragment.target_eq]
    exact hLabels
  have hRun :=
    Block.lower?_openRun_rel
      (block := block) (code := fragment.code)
      (pre := fragment.pre) (post := fragment.post)
      (state := state) fragment.lower hUnique hCodeFits hStatePc
      hResolvedFragment hNonzeroFragment hLabelsFragment
  rw [fragment.target_eq]
  simpa [TypedCfg.InteractionSemantics.Program.openStep,
    TypedCfg.Control.Program.step, hFind] using hRun

theorem lower?_step_openRunSimulates_rel
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : Assembly.EVMState} {entryPc : Nat}
    (hLower : LateReturnProbe.Program.lower? program = some target)
    (hAccepted : target.acceptedWithDynamic = true)
    (hFits : target.PCFits)
    (hLocalUnique :
      LateReturnProbe.Program.localReturnTokensUnique? program = true)
    (hNonzero :
      LateReturnProbe.Program.returnTargetsResolveNonzero?
          program target =
        true)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    Simulation.Interaction.Rel
      (TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openStep
        program label state.incrPC)
      (LateReturnProbe.CompiledBlock.openRun
        block target state) := by
  apply Simulation.Interaction.Rel.mono
    (lower?_step_open_rel
      hLower hAccepted hFits hLocalUnique hNonzero
      hFind hLabelPc hPc)
  intro sourceDone targetDone hSim
  exact
    TypedCfg.InteractionPreservation.OpenBlock.of_preservation hSim

theorem lower?_step_openRunSimulates_rel_of_related
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {targetState sourceState : Assembly.EVMState} {entryPc : Nat}
    (hLower : LateReturnProbe.Program.lower? program = some target)
    (hAccepted : target.acceptedWithDynamic = true)
    (hFits : target.PCFits)
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hLocalUnique :
      LateReturnProbe.Program.localReturnTokensUnique? program = true)
    (hNonzero :
      LateReturnProbe.Program.returnTargetsResolveNonzero?
          program target =
        true)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc :
      targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC) :
    Simulation.Interaction.Rel
      (TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openStep
        program label sourceState)
      (LateReturnProbe.CompiledBlock.openRun
        block target targetState) := by
  have hSource :=
    TypedCfg.InteractionCongruence.Program.openStep_runtimeRel
      (label := label) (target := sourceState)
      (source := targetState.incrPC)
      hTyped hIndependent hRuntime
  have hCompiled :=
    lower?_step_openRunSimulates_rel
      hLower hAccepted hFits hLocalUnique hNonzero
      hFind hLabelPc hPc
  have hTrans :=
    Simulation.Interaction.Rel.trans hSource hCompiled
  apply Simulation.Interaction.Rel.mono hTrans
  intro sourceDone targetDone hComposite
  rcases hComposite with
    ⟨middleDone, hSourceRuntime, hTargetSim⟩
  exact
    TypedCfg.InteractionPreservation.OpenBlock.runtime_left
      hSourceRuntime hTargetSim

theorem compiled_openStep_eq_of_labelPc
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : Assembly.EVMState} {entryPc : Nat}
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    LateReturnProbe.CompiledProgram.openStep
        program target state =
      LateReturnProbe.CompiledBlock.openRun
        block target state := by
  have hToNat :=
    Assembly.Program.toNat_ofNat_labelPc hFits hLabelPc
  have hAt :=
    Assembly.Program.instrAtPc_of_labelPc hLabelPc
  unfold LateReturnProbe.CompiledProgram.openStep
  rw [hPc, hToNat, hAt]
  simp [hFind]

theorem compiled_openStep_eq_error_of_labelPc
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {state : Assembly.EVMState} {entryPc : Nat}
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = none)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    LateReturnProbe.CompiledProgram.openStep
        program target state =
      .done (.error .InvalidInstruction) := by
  have hToNat :=
    Assembly.Program.toNat_ofNat_labelPc hFits hLabelPc
  have hAt :=
    Assembly.Program.instrAtPc_of_labelPc hLabelPc
  unfold LateReturnProbe.CompiledProgram.openStep
  rw [hPc, hToNat, hAt]
  simp [hFind]

theorem lower?_compiledStep_open_rel
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {targetState sourceState : Assembly.EVMState}
    {entryPc : Nat}
    (hLower : LateReturnProbe.Program.lower? program = some target)
    (hAccepted : target.acceptedWithDynamic = true)
    (hFits : target.PCFits)
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hLocalUnique :
      LateReturnProbe.Program.localReturnTokensUnique? program = true)
    (hNonzero :
      LateReturnProbe.Program.returnTargetsResolveNonzero?
          program target =
        true)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc :
      targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC) :
    Simulation.Interaction.Rel
      (TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openStep
        program label sourceState)
      (LateReturnProbe.CompiledProgram.openStep
        program target targetState) := by
  cases hFind : program.findBlock? label with
  | none =>
      rw [compiled_openStep_eq_error_of_labelPc
        hFits hFind hLabelPc hPc]
      simp only [
        TypedCfg.InteractionSemantics.Program.openStep,
        TypedCfg.Control.Program.step, hFind]
      change
        Simulation.Interaction.Rel
          (TypedCfg.InteractionPreservation.OpenBlock.RunSimulates target)
          (.done (.ok (.invalid sourceState)))
          (.done (.error .InvalidInstruction))
      apply Simulation.Interaction.Rel.done
      exact ⟨.InvalidInstruction, rfl⟩
  | some block =>
      rw [compiled_openStep_eq_of_labelPc
        hFits hFind hLabelPc hPc]
      exact
        lower?_step_openRunSimulates_rel_of_related
          hLower hAccepted hFits hTyped hIndependent
          hLocalUnique hNonzero
          hFind hLabelPc hPc hRuntime

open TypedCfg.InteractionPreservation

set_option maxHeartbeats 1000000 in
/-- Fuel-indexed whole-program preservation for late return materialisation. -/
theorem lower?_openRunN_rel
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label}
    {targetState sourceState : Assembly.EVMState}
    {entryPc : Nat} (fuel : Nat)
    (hLower : LateReturnProbe.Program.lower? program = some target)
    (hAccepted : target.acceptedWithDynamic = true)
    (hFits : target.PCFits)
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hLocalUnique :
      LateReturnProbe.Program.localReturnTokensUnique? program = true)
    (hNonzero :
      LateReturnProbe.Program.returnTargetsResolveNonzero?
          program target =
        true)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc :
      targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData sourceState targetState.incrPC) :
    Simulation.Interaction.Rel
      (OpenBlock.RunSimulates target)
      (TypedCfg.InteractionSemantics.Program.openRunN
        program fuel label sourceState)
      (LateReturnProbe.CompiledProgram.openRunN
        program target fuel targetState) := by
  induction fuel generalizing
      label targetState sourceState entryPc with
  | zero =>
      simp only [
        TypedCfg.InteractionSemantics.Program.openRunN_zero,
        LateReturnProbe.CompiledProgram.openRunN_zero]
      apply Simulation.Interaction.Rel.done
      have hTargetRuntime :
          Assembly.SameRuntimeData targetState sourceState :=
        Assembly.SameRuntimeData.trans
          (Assembly.SameRuntimeData.incrPC_right
            (Assembly.SameRuntimeData.refl targetState))
          hRuntime.symm
      exact
        ⟨entryPc, hLabelPc, hPc, hTargetRuntime⟩
  | succ fuel ih =>
      rw [
        TypedCfg.InteractionSemantics.Program.openRunN_succ,
        LateReturnProbe.CompiledProgram.openRunN_succ]
      have hStepBase :=
        lower?_compiledStep_open_rel
          hLower hAccepted hFits hTyped hIndependent
          hLocalUnique hNonzero
          hLabelPc hPc hRuntime
      have hStep :=
        Simulation.Interaction.Rel.strengthen_left hStepBase
          (TypedCfg.InteractionCongruence.Program.openStep_admissibleProgramStep
            program label sourceState)
      apply Simulation.Interaction.Rel.bind_custom hStep
      intro sourceDone targetDone hDone
      rcases hDone with ⟨hSim, hAdmissible⟩
      cases sourceDone with
      | error sourceError =>
          cases targetDone with
          | error targetError =>
              unfold OpenBlock.RunSimulates at hSim
              cases hSim
              exact .done rfl
          | ok targetResult =>
              unfold OpenBlock.RunSimulates at hSim
              cases hSim
      | ok sourceOutcome =>
          cases sourceOutcome with
          | fallthrough final =>
              exact hAdmissible.elim
          | returnDispatch final =>
              exact hAdmissible.elim
          | jump next sourceAfter =>
              cases targetDone with
              | error targetError =>
                  unfold OpenBlock.RunSimulates
                    OpenOutcome.Simulates
                    TypedCfg.Preservation.Outcome.Simulates
                    TypedCfg.Preservation.Outcome.RunningAt at hSim
                  rcases hSim with
                    ⟨dest, hDest, hImpossible⟩
                  exact hImpossible.elim
              | ok targetResult =>
                  cases targetResult with
                  | halted halt =>
                      unfold OpenBlock.RunSimulates
                        OpenOutcome.Simulates
                        TypedCfg.Preservation.Outcome.Simulates
                        TypedCfg.Preservation.Outcome.RunningAt at hSim
                      rcases hSim with
                        ⟨dest, hDest, hImpossible⟩
                      exact hImpossible.elim
                  | running targetAfter =>
                      unfold OpenBlock.RunSimulates
                        OpenOutcome.Simulates
                        TypedCfg.Preservation.Outcome.Simulates
                        TypedCfg.Preservation.Outcome.RunningAt at hSim
                      rcases hSim with
                        ⟨dest, hDest, hTargetPc, hData⟩
                      exact
                        ih hDest hTargetPc
                          (Assembly.SameRuntimeData.incrPC_right
                            hData.symm)
          | halt kind sourceFinal =>
              cases targetDone with
              | error targetError =>
                  exact .done hSim
              | ok targetResult =>
                  cases targetResult with
                  | halted halt =>
                      exact .done hSim
                  | running targetAfter =>
                      unfold OpenBlock.RunSimulates
                        OpenOutcome.Simulates at hSim
                      rcases hSim with
                        ⟨simulated, hData, hTarget⟩
                      unfold Assembly.Target.stepInstrResult at hTarget
                      cases hRun :
                          Assembly.Target.stepInstr
                            (.prim kind.toPrimOp) simulated with
                      | error error =>
                          rw [hRun] at hTarget
                          cases hTarget
                      | ok final =>
                          rw [hRun] at hTarget
                          have hKind :
                              (Assembly.TargetInstr.prim
                                kind.toPrimOp).haltKind? =
                                some kind := by
                            cases kind <;> rfl
                          rw [hKind] at hTarget
                          cases hTarget
          | invalid sourceFinal =>
              cases targetDone with
              | error targetError =>
                  exact .done hSim
              | ok targetResult =>
                  unfold OpenBlock.RunSimulates
                    OpenOutcome.Simulates
                    TypedCfg.Preservation.Outcome.Simulates at hSim
                  rcases hSim with ⟨error, hError⟩
                  cases hError

end Program

end LateReturnPreservation
end TypedCfg
end EvmCompiler
