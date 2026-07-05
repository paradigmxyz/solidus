import EvmCompiler.Assembly.StackHeadroom
import EvmCompiler.Assembly.GasfulBridgeLayout
import EvmCompiler.Assembly.GasfulBridgeRecursive

/-!
# Soundness of the stack-headroom certificate against the gasful EVM

The validated abstract-stack-set table of
`EvmCompiler.Assembly.StackHeadroom` is proved sound along every reachable
gasful frame state (`HeightPoint`): some admitted abstract stack agrees cell
by cell with the concrete operand stack (`Agrees`), by mirroring the compact
control-point step lemmas of the gasful bridge layout module and adding
abstract-stack bookkeeping (exact for `PUSH`/`DUP`/`SWAP`/`EQ`, declared
arity with unknown outputs otherwise).  The headroom cap on every admitted
abstract stack then makes the interpreter's `StackOverflow` precheck
unreachable.
-/

namespace EvmCompiler
namespace Assembly
namespace StackHeadroom

open EvmCompiler.Assembly.GasfulBridge

/-! ## Abstract-stack agreement -/

/-- Agreement of one abstract cell with a concrete word: known cells are
exact, unknown cells accept anything. -/
def AgreesVal : Option Word → Word → Prop
  | none, _ => True
  | some v, w => v = w

theorem agreesVal_none {w : Word} : AgreesVal none w := by
  simp [AgreesVal]

theorem agreesVal_some {v w : Word} (h : AgreesVal (some v) w) : v = w := h

theorem word_beq_eq_decide (a b : Word) :
    (a == b) = decide (a = b) := by
  cases a with | mk av =>
  cases b with | mk bv =>
  by_cases h : av = bv
  · subst h
    simp [BEq.beq, EvmYul.instBEqUInt256.beq]
  · have hNe : EvmYul.UInt256.mk av ≠ EvmYul.UInt256.mk bv := by
      intro hEq
      exact h (congrArg EvmYul.UInt256.val hEq)
    simp [BEq.beq, EvmYul.instBEqUInt256.beq, h, hNe]

theorem word_bne_eq_true_iff {a b : Word} : (a != b) = true ↔ a ≠ b := by
  simp [bne, word_beq_eq_decide]

/-- Abstract-stack agreement: cellwise, hence in particular equal lengths. -/
abbrev Agrees (astack : AbsStack) (stack : List Word) : Prop :=
  List.Forall₂ AgreesVal astack stack

theorem agrees_length {astack : AbsStack} {stack : List Word}
    (h : Agrees astack stack) : astack.length = stack.length :=
  h.length_eq

theorem agrees_cons {av : Option Word} {w : Word} {astack : AbsStack}
    {stack : List Word} (hv : AgreesVal av w) (h : Agrees astack stack) :
    Agrees (av :: astack) (w :: stack) :=
  List.Forall₂.cons hv h

theorem agrees_cons_inv {av : Option Word} {astack : AbsStack}
    {stack : List Word} (h : Agrees (av :: astack) stack) :
    ∃ w rest, stack = w :: rest ∧ AgreesVal av w ∧ Agrees astack rest := by
  cases h with
  | cons hv hrest => exact ⟨_, _, rfl, hv, hrest⟩

theorem agrees_append {a₁ a₂ : AbsStack} {s₁ s₂ : List Word}
    (h₁ : Agrees a₁ s₁) (h₂ : Agrees a₂ s₂) :
    Agrees (a₁ ++ a₂) (s₁ ++ s₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hv _ ih => simpa using List.Forall₂.cons hv ih

theorem agrees_take {astack : AbsStack} {stack : List Word}
    (h : Agrees astack stack) :
    ∀ n, Agrees (astack.take n) (stack.take n) := by
  induction h with
  | nil => intro n; simpa using List.Forall₂.nil
  | cons hv _ ih =>
      intro n
      cases n with
      | zero => simpa using List.Forall₂.nil
      | succ n => simpa using List.Forall₂.cons hv (ih n)

theorem agrees_drop {astack : AbsStack} {stack : List Word}
    (h : Agrees astack stack) :
    ∀ n, Agrees (astack.drop n) (stack.drop n) := by
  induction h with
  | nil => intro n; simpa using List.Forall₂.nil
  | cons hv hrest ih =>
      intro n
      cases n with
      | zero => simpa using List.Forall₂.cons hv hrest
      | succ n => simpa using ih n

theorem agrees_getElem? {astack : AbsStack} {stack : List Word}
    {i : Nat} {v : Word}
    (h : Agrees astack stack) (hGet : astack[i]? = some (some v)) :
    stack[i]? = some v := by
  induction h generalizing i with
  | nil => simp at hGet
  | cons hv _ ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
          subst hGet
          simp only [List.getElem?_cons_zero, Option.some.injEq]
          exact (agreesVal_some hv).symm
      | succ i =>
          simpa using ih (by simpa using hGet)

theorem agrees_replicate_none (ws : List Word) :
    Agrees (List.replicate ws.length none) ws := by
  induction ws with
  | nil => exact List.Forall₂.nil
  | cons w ws ih =>
      simpa [List.replicate] using
        List.Forall₂.cons (show AgreesVal none w from trivial) ih

/-- The certified per-state fact: some admitted abstract stack at the current
program counter agrees with the concrete operand stack. -/
def HeightPoint (table : StackTable) (state : EVMState) : Prop :=
  ∃ astack, memStack table state.pc astack = true ∧
    Agrees astack state.stack

theorem afterEVMInstructionChargeAt_stack (state : EVMState) :
    (afterEVMInstructionChargeAt state).stack = state.stack := by
  simp [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]

theorem afterEVMInstructionChargeAt_pc (state : EVMState) :
    (afterEVMInstructionChargeAt state).pc = state.pc := by
  simp [afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]

/-! ## Concrete stack contents of primitive steps -/

theorem primStep_run_bin_stack {f : EvmYul.Primop.Binary}
    {state next : EvmYul.EVM.State} {x y : Word} {rest : List Word}
    (hStack : state.stack = x :: y :: rest)
    (hRun : (PrimStep.bin f).run state = .ok next) :
    next.stack = f x y :: rest := by
  simp only [PrimStep.run, EvmYul.EVM.execBinOp, hStack,
    EvmYul.Stack.pop2, Id.run] at hRun
  cases hRun
  simp [EvmYul.EVM.State.replaceStackAndIncrPC, EvmYul.EVM.State.incrPC,
    EvmYul.Stack.push]

theorem primStep_run_dup_stack {n : Nat}
    {state next : EvmYul.EVM.State}
    (hPos : 1 ≤ n)
    (hLen : n ≤ state.stack.length)
    (hRun : (PrimStep.dup n).run state = .ok next) :
    ∃ v, state.stack[n - 1]? = some v ∧ next.stack = v :: state.stack := by
  have hIdx : n - 1 < state.stack.length := by omega
  refine ⟨state.stack[n - 1], List.getElem?_eq_getElem hIdx, ?_⟩
  have hTake : (state.stack.take n).length = n := by
    simp [hLen]
  have hGetL : (state.stack.take n).getLast? =
      some state.stack[n - 1] := by
    rw [List.getLast?_eq_getElem?, hTake,
      List.getElem?_take_of_lt (show n - 1 < n by omega)]
    exact List.getElem?_eq_getElem hIdx
  have hLast := List.getLast!_of_getLast? hGetL
  have hRun' : EvmYul.dup n state = .ok next := hRun
  simp only [EvmYul.dup] at hRun'
  rw [if_pos hTake] at hRun'
  injection hRun' with hNext
  subst hNext
  simp only [EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]
  rw [hLast]

theorem primStep_run_swap_stack {n : Nat}
    {state next : EvmYul.EVM.State} {top : Word} {rest : List Word}
    (hPos : 1 ≤ n)
    (hStack : state.stack = top :: rest)
    (hLen : n ≤ rest.length)
    (hRun : (PrimStep.swap n).run state = .ok next) :
    ∃ z, rest[n - 1]? = some z ∧
      next.stack = z :: (rest.take (n - 1) ++ top :: rest.drop n) := by
  have hIdx : n - 1 < rest.length := by omega
  refine ⟨rest[n - 1], List.getElem?_eq_getElem hIdx, ?_⟩
  have hTakeRest : rest.take n = rest.take (n - 1) ++ [rest[n - 1]] := by
    have h1 : rest.take (n - 1 + 1) =
        rest.take (n - 1) ++ rest[n - 1]?.toList := List.take_succ
    rw [List.getElem?_eq_getElem hIdx] at h1
    simpa [show n - 1 + 1 = n from by omega] using h1
  have hTop : state.stack.take (n + 1) =
      top :: (rest.take (n - 1) ++ [rest[n - 1]]) := by
    rw [hStack, List.take_succ_cons, hTakeRest]
  have hTopLen : (state.stack.take (n + 1)).length = n + 1 := by
    rw [hTop]
    simp [List.length_take]
    omega
  have hBottom : state.stack.drop (n + 1) = rest.drop n := by
    rw [hStack]
    simp
  have hGetL : (state.stack.take (n + 1)).getLast? =
      some rest[n - 1] := by
    rw [hTop]
    show ((top :: rest.take (n - 1)) ++ [rest[n - 1]]).getLast? = _
    exact List.getLast?_concat
  have hLast := List.getLast!_of_getLast? hGetL
  have hTail : (state.stack.take (n + 1)).tail!.dropLast =
      rest.take (n - 1) := by
    rw [hTop]
    show (rest.take (n - 1) ++ [rest[n - 1]]).dropLast = rest.take (n - 1)
    exact List.dropLast_concat
  have hHead : (state.stack.take (n + 1)).head! = top := by
    rw [hTop]
    rfl
  have hRun' : EvmYul.swap n state = .ok next := hRun
  simp only [EvmYul.swap] at hRun'
  rw [if_pos hTopLen] at hRun'
  injection hRun' with hNext
  subst hNext
  simp only [EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC]
  rw [hLast, hTail, hHead, hBottom]
  simp

/-- Every successful nonterminal primitive leaves the stack below its
declared operands untouched: the final stack is exactly `output` fresh words
over the input stack with `input` words dropped. -/
theorem step_stack_split_of_stackArity
    {op : PrimOp} {input output : Nat}
    {state final : EvmYul.EVM.State}
    (hArity : op.stackArity? = some (input, output))
    (hBound : input ≤ state.stack.length)
    (hRun : op.step state = .ok final) :
    ∃ outs : List Word, outs.length = output ∧
      final.stack = outs ++ state.stack.drop input := by
  have hSplit : state.stack = state.stack.take input ++
      state.stack.drop input := (List.take_append_drop input state.stack).symm
  have hTakeLen : (state.stack.take input).length = input := by
    simp [hBound]
  have hFramed :
      op.step
          { state with
              stack := state.stack.take input ++ state.stack.drop input } =
        .ok final := by
    rw [← hSplit]
    exact hRun
  obtain ⟨final0, hRun0⟩ :=
    PrimOp.exists_step_of_stackArity_le_of_append_step
      (state := { state with stack := state.stack.take input })
      (hidden := state.stack.drop input) hArity (by simp [hTakeLen]) hFramed
  have hAppend :=
    PrimOp.step_append_stack_of_stackArity_le
      (state := { state with stack := state.stack.take input })
      (state.stack.drop input) hArity (by simp [hTakeLen]) hRun0
  have hBothOk : (Except.ok final :
      Except EvmYul.EVM.ExecutionException EvmYul.EVM.State) =
      .ok { final0 with
        stack := final0.stack ++ state.stack.drop input } :=
    hFramed.symm.trans hAppend
  have hEq : final = { final0 with
      stack := final0.stack ++ state.stack.drop input } :=
    Except.ok.inj hBothOk
  refine ⟨final0.stack, ?_, by rw [hEq]⟩
  have hLen := PrimOp.step_stack_length_of_stackArity hArity hRun0
  simpa [hTakeLen] using hLen

/-- Agreement preservation for one nonterminal continuing primitive: the
abstract effect `absPrim?` tracks the concrete step cell by cell. -/
theorem agrees_absPrim_step
    {op : PrimOp} {primStep : PrimStep} {input output : Nat}
    {astack astack' : AbsStack}
    {state next : EvmYul.EVM.State}
    (hContinuing : op.continuingStep? = some primStep)
    (hArity : op.stackArity? = some (input, output))
    (hAbs : absPrim? op astack = some astack')
    (hAgrees : Agrees astack state.stack)
    (hPrim : op.step state = .ok next) :
    Agrees astack' next.stack := by
  by_cases hEqOp : op = .eq
  · subst op
    have hPrimStep : primStep = .bin EvmYul.UInt256.eq := by
      simpa [PrimOp.continuingStep?] using hContinuing.symm
    subst primStep
    rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
    simp [absPrim?] at hAbs
    cases astack with
    | nil => cases hAbs
    | cons av arest =>
        cases arest with
        | nil => cases hAbs
        | cons bv arest2 =>
            injection hAbs with hAbs'
            subst hAbs'
            obtain ⟨x, stail, hS1, hav, hAg1⟩ := agrees_cons_inv hAgrees
            obtain ⟨y, srest, hS2, hbv, hAgRest⟩ := agrees_cons_inv hAg1
            subst hS2
            have hStackC : state.stack = x :: y :: srest := hS1
            have hNextStack := primStep_run_bin_stack hStackC hPrim
            rw [hNextStack]
            refine agrees_cons ?_ hAgRest
            cases av with
            | none => exact agreesVal_none
            | some a' =>
                cases bv with
                | none => exact agreesVal_none
                | some b' =>
                    have hax : a' = x := agreesVal_some hav
                    have hby : b' = y := agreesVal_some hbv
                    show AgreesVal (some (EvmYul.UInt256.eq a' b'))
                      (EvmYul.UInt256.eq x y)
                    rw [hax, hby]
                    exact rfl
  · simp only [absPrim?, if_neg hEqOp, hContinuing] at hAbs
    split at hAbs
    · -- DUP: cell-precise duplication
      rename_i n heq
      injection heq with heq'
      subst heq'
      rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
      split at hAbs
      · rename_i hCond
        obtain ⟨hPos, hLenA⟩ := hCond
        injection hAbs with hAbs'
        subst hAbs'
        have hLenC : n ≤ state.stack.length := by
          rw [← agrees_length hAgrees]
          exact hLenA
        obtain ⟨v, hGetC, hNextStack⟩ :=
          primStep_run_dup_stack hPos hLenC hPrim
        rw [hNextStack]
        show Agrees ((astack[n - 1]?.getD none) :: astack)
          (v :: state.stack)
        refine agrees_cons ?_ hAgrees
        cases hCell : astack[n - 1]? with
        | none =>
            simp only [hCell, Option.getD_none]
            exact agreesVal_none
        | some cell =>
            cases cell with
            | none =>
                simp only [hCell, Option.getD_some]
                exact agreesVal_none
            | some u =>
                have hU := agrees_getElem? hAgrees hCell
                rw [hGetC] at hU
                injection hU with hU
                simp only [hCell, Option.getD_some]
                show AgreesVal (some u) v
                exact hU.symm
      · cases hAbs
    · -- SWAP: cell-precise exchange
      rename_i n heq
      injection heq with heq'
      subst heq'
      rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
      split at hAbs
      · rename_i hCond
        obtain ⟨hPos, hLenA⟩ := hCond
        injection hAbs with hAbs'
        subst hAbs'
        cases astack with
        | nil => simp at hLenA
        | cons av arest =>
            obtain ⟨x, stail, hS1, hav, hAgRest⟩ :=
              agrees_cons_inv hAgrees
            have hLenRest : n ≤ stail.length := by
              have hL := agrees_length hAgRest
              simp only [List.length_cons] at hLenA
              omega
            obtain ⟨z, hGetZ, hNextStack⟩ :=
              primStep_run_swap_stack hPos hS1 hLenRest hPrim
            rw [hNextStack]
            show Agrees
              ((arest[n - 1]?.getD none) ::
                (arest.take (n - 1) ++ av :: arest.drop n))
              (z :: (stail.take (n - 1) ++ x :: stail.drop n))
            refine agrees_cons ?_
              (agrees_append (agrees_take hAgRest (n - 1))
                (agrees_cons hav (agrees_drop hAgRest n)))
            cases hCell : arest[n - 1]? with
            | none =>
                simp only [hCell, Option.getD_none]
                exact agreesVal_none
            | some cell =>
                cases cell with
                | none =>
                    simp only [hCell, Option.getD_some]
                    exact agreesVal_none
                | some u =>
                    have hU := agrees_getElem? hAgRest hCell
                    rw [hGetZ] at hU
                    injection hU with hU
                    simp only [hCell, Option.getD_some]
                    show AgreesVal (some u) z
                    exact hU.symm
      · cases hAbs
    · -- generic: declared arity, unknown outputs, untouched suffix
      simp only [hArity] at hAbs
      split at hAbs
      · rename_i hBound
        injection hAbs with hAbs'
        subst hAbs'
        have hBoundC : input ≤ state.stack.length := by
          rw [← agrees_length hAgrees]
          exact hBound
        obtain ⟨outs, hOutsLen, hFinal⟩ :=
          step_stack_split_of_stackArity hArity hBoundC hPrim
        rw [hFinal]
        refine agrees_append ?_ (agrees_drop hAgrees input)
        rw [← hOutsLen]
        exact agrees_replicate_none outs
      · cases hAbs

/-! ## Per-control-point abstract-stack preservation

Each lemma mirrors the corresponding `artifactFramePoint_*_step` lemma of
`GasfulBridgeLayout`, replaying the exact successor-state identification and
reading the successor abstract stack off the validated table. -/

theorem heightPoint_label_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .label label)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_label_entry_mem hCompile hBlock hInstr
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  have hDecoded :
      EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (EvmYul.Operation.JUMPDEST, none) := by
    simpa [hCode, hStatePc] using hBytesDecoded
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hExact := evm_step_jumpdest_eq_next fuel state none
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [hExact] at hStep
      have hNext : next = (afterEVMInstructionChargeAt state).incrPC := by
        simpa using hStep.symm
      subst next
      obtain ⟨astack, hMemPc, hAgrees⟩ := hHeight
      have hEntry :
          memStack cert.table (EvmYul.UInt256.ofNat block.compactPc)
            astack = true := by
        rw [← hPc]; exact hMemPc
      have hOk := check?_blockOk hCheck hBlock
      simp only [blockOk?, hInstr] at hOk
      have hSucc := all_stacksAt_apply hOk hEntry
      have hNextPc :
          ((afterEVMInstructionChargeAt state).incrPC).pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        simp [EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add]
      have hNextStack :
          ((afterEVMInstructionChargeAt state).incrPC).stack = state.stack := by
        simp [EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas]
      refine ⟨astack, ?_, ?_⟩
      · rw [hNextPc]
        exact hSucc
      · rw [hNextStack]
        exact hAgrees

theorem heightPoint_push_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {value : Word} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .push value)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  obtain ⟨width, located, hWidth, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_push_entry_mem hCompile hBlock hInstr
  have hLocatedValid :=
    (List.forall_iff_forall_mem.mp
      (Compact.compile?_valid hCompile).wellFormed.1) located hMem
  rw [hLocatedInstr] at hLocatedValid
  have hFits : Compact.FitsWidth width value.toNat := by
    simpa [Compact.Instr.Valid] using hLocatedValid
  obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
    ⟨hFits.1, hFits.2.1⟩
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  have hDecoded : EvmYul.EVM.decode state.executionEnv.code state.pc =
      some (op, some (value, width)) := by
    simpa [hCode, hStatePc] using hBytesDecoded
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hExact := evm_step_push_eq_next fuel state value hFits hOp
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [hExact] at hStep
      have hNext : next = gasfulPushNext width value state := by
        simpa using hStep.symm
      subst next
      obtain ⟨astack, hMemPc, hAgrees⟩ := hHeight
      have hEntry :
          memStack cert.table (EvmYul.UInt256.ofNat block.compactPc)
            astack = true := by
        rw [← hPc]; exact hMemPc
      have hSize : Compact.sourceInstrSizeAt? artifact.pinnedPushPcs
          artifact.branchWidth block.sourcePc block.sourceInstr =
            some (width + 1) := by
        simp [hInstr, Compact.sourceInstrSizeAt?, hWidth]
      have hOk := check?_blockOk hCheck hBlock
      rw [hInstr] at hSize
      simp only [blockOk?, hInstr, hSize] at hOk
      have hSucc := all_stacksAt_apply hOk hEntry
      have hNextPc :
          (gasfulPushNext width value state).pc =
            EvmYul.UInt256.ofNat (block.compactPc + (width + 1)) := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add,
          Nat.add_assoc]
      have hNextStack :
          (gasfulPushNext width value state).stack =
            value :: state.stack := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
      refine ⟨some value :: astack, ?_, ?_⟩
      · rw [hNextPc]
        exact hSucc
      · rw [hNextStack]
        exact agrees_cons rfl hAgrees

theorem heightPoint_branch_push_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {label : Label} {isJumpi : Bool} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_branch_entry_mem hCompile hBlock hInstr
  have hLocatedValid :=
    (List.forall_iff_forall_mem.mp
      (Compact.compile?_valid hCompile).wellFormed.1) located hMem
  rw [hLocatedInstr] at hLocatedValid
  have hFits : Compact.FitsWidth artifact.branchWidth
      (EvmYul.UInt256.ofNat dest).toNat := by
    simpa [Compact.Instr.Valid] using hLocatedValid
  obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
    ⟨hFits.1, hFits.2.1⟩
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  rw [hLocatedInstr] at hInstrDecoded
  simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
  subst decoded
  have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
    hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
  have hDecoded :
      EvmYul.EVM.decode state.executionEnv.code state.pc =
        some (op, some (EvmYul.UInt256.ofNat dest,
          artifact.branchWidth)) := by
    simpa [hCode, hStatePc] using hBytesDecoded
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hExact := evm_step_push_eq_next fuel state
        (EvmYul.UInt256.ofNat dest) hFits hOp
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      rw [hExact] at hStep
      have hNext : next = gasfulPushNext artifact.branchWidth
          (EvmYul.UInt256.ofNat dest) state := by
        simpa using hStep.symm
      subst next
      obtain ⟨astack, hMemPc, hAgrees⟩ := hHeight
      have hEntry :
          memStack cert.table (EvmYul.UInt256.ofNat block.compactPc)
            astack = true := by
        rw [← hPc]; exact hMemPc
      have hSucc :
          memStack cert.table
              (EvmYul.UInt256.ofNat
                (block.compactPc + artifact.branchWidth + 1))
              (some (EvmYul.UInt256.ofNat dest) :: astack) = true := by
        have hOk := check?_blockOk hCheck hBlock
        cases hJumpi : isJumpi
        · rw [hJumpi] at hInstr
          simp only [Bool.false_eq_true, if_false] at hInstr
          simp only [blockOk?, hInstr, hLookup, Bool.and_eq_true] at hOk
          have hFlow := all_stacksAt_apply hOk.1 hEntry
          exact hFlow
        · rw [hJumpi] at hInstr
          simp only [if_true] at hInstr
          simp only [blockOk?, hInstr, hLookup, Bool.and_eq_true] at hOk
          have hFlow := all_stacksAt_apply hOk.1 hEntry
          exact hFlow
      have hNextPc :
          (gasfulPushNext artifact.branchWidth
              (EvmYul.UInt256.ofNat dest) state).pc =
            EvmYul.UInt256.ofNat
              (block.compactPc + artifact.branchWidth + 1) := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, chargeGas, hPc, uint256_ofNat_add,
          Nat.add_assoc]
      have hNextStack :
          (gasfulPushNext artifact.branchWidth
              (EvmYul.UInt256.ofNat dest) state).stack =
            EvmYul.UInt256.ofNat dest :: state.stack := by
        simp [gasfulPushNext, EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push,
          afterEVMInstructionChargeAt, afterMemoryChargeAt, chargeGas]
      refine ⟨some (EvmYul.UInt256.ofNat dest) :: astack, ?_, ?_⟩
      · rw [hNextPc]
        exact hSucc
      · rw [hNextStack]
        exact agrees_cons rfl hAgrees

/-- Abstract-stack inversion at a `JUMP` midpoint: every admitted midpoint
abstract stack pops to an admitted abstract stack of the jump target. -/
theorem branchMid_jump_stacks
    {artifact : Compact.Artifact} {cert : Cert}
    {block : Compact.SourceBlock} {label : Label}
    {dest : Nat} {mv : Option Word} {mrest : AbsStack}
    (hCheck : check? artifact cert = true)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .jump label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hMid :
      memStack cert.table
          (EvmYul.UInt256.ofNat
            (block.compactPc + artifact.branchWidth + 1)) (mv :: mrest) =
        true) :
    memStack cert.table (EvmYul.UInt256.ofNat dest) mrest = true := by
  have hOk := check?_blockOk hCheck hBlock
  simp only [blockOk?, hInstr, hLookup, Bool.and_eq_true] at hOk
  have hCase := all_stacksAt_apply hOk.2 hMid
  simpa using hCase

/-- Abstract-stack inversion at a `JUMPI` midpoint: every admitted midpoint
abstract stack pops to admitted abstract stacks of the still-possible branch
targets, where a known condition cell (which must agree with the concrete
condition) selects a single target. -/
theorem branchMid_jumpi_stacks
    {artifact : Compact.Artifact} {cert : Cert}
    {block : Compact.SourceBlock} {label : Label}
    {dest : Nat} {mv cv : Option Word} {mtail : AbsStack} {cond : Word}
    (hCheck : check? artifact cert = true)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .jumpi label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hMid :
      memStack cert.table
          (EvmYul.UInt256.ofNat
            (block.compactPc + artifact.branchWidth + 1))
          (mv :: cv :: mtail) = true)
    (hCv : AgreesVal cv cond) :
    (cond ≠ EvmYul.UInt256.ofNat 0 →
        memStack cert.table (EvmYul.UInt256.ofNat dest) mtail = true) ∧
      (cond = EvmYul.UInt256.ofNat 0 →
        memStack cert.table
            (EvmYul.UInt256.ofNat
              (block.compactPc + artifact.branchWidth + 2)) mtail =
          true) := by
  have hOk := check?_blockOk hCheck hBlock
  simp only [blockOk?, hInstr, hLookup, Bool.and_eq_true] at hOk
  have hCase := all_stacksAt_apply hOk.2 hMid
  cases cv with
  | some c =>
      have hcEq : c = cond := agreesVal_some hCv
      subst hcEq
      have hIf :
          (if c = EvmYul.UInt256.ofNat 0 then
              memStack cert.table
                (EvmYul.UInt256.ofNat
                  (block.compactPc + artifact.branchWidth + 2)) mtail
            else memStack cert.table (EvmYul.UInt256.ofNat dest) mtail) =
            true := hCase
      by_cases hc : c = EvmYul.UInt256.ofNat 0
      · rw [if_pos hc] at hIf
        exact ⟨fun hne => absurd hc hne, fun _ => hIf⟩
      · rw [if_neg hc] at hIf
        exact ⟨fun _ => hIf, fun hzero => absurd hzero hc⟩
  | none =>
      have hBoth : (memStack cert.table (EvmYul.UInt256.ofNat dest) mtail &&
          memStack cert.table
            (EvmYul.UInt256.ofNat
              (block.compactPc + artifact.branchWidth + 2)) mtail) =
          true := hCase
      simp only [Bool.and_eq_true] at hBoth
      exact ⟨fun _ => hBoth.1, fun _ => hBoth.2⟩

theorem heightPoint_branchMid_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {label : Label} {isJumpi : Bool}
    {dest : Nat} {rest : EvmYul.Stack Word} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr =
      if isJumpi then .jumpi label else .jump label)
    (hLookup : Compact.lookupLabel? artifact.labels label = some dest)
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (block.compactPc + artifact.branchWidth + 1))
    (hStack : state.stack = EvmYul.UInt256.ofNat dest :: rest)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  obtain ⟨mid, hMemMid, hAgrees⟩ := hHeight
  have hMidEntry :
      memStack cert.table
          (EvmYul.UInt256.ofNat
            (block.compactPc + artifact.branchWidth + 1)) mid = true := by
    rw [← hPc]; exact hMemMid
  obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
    compact_branch_midpoint_mem hCompile hBlock hInstr
  obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
    hDecode.decodes located hMem
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
        hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
      cases hJumpi : isJumpi
      · -- JUMP
        rw [hJumpi] at hLocatedInstr hInstr
        simp only [Bool.false_eq_true, if_false] at hLocatedInstr hInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMP, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        have hExact :=
          evm_step_jump_eq_next fuel state none rest
            (EvmYul.UInt256.ofNat dest) hStack
        rw [hDecoded] at hStep
        simp only [Option.getD_some] at hStep
        rw [hExact] at hStep
        have hNext :
            next = gasfulJumpNext state rest (EvmYul.UInt256.ofNat dest) := by
          simpa using hStep.symm
        subst next
        rw [hStack] at hAgrees
        cases hAgrees with
        | cons hv hAgreesRest =>
            rename_i mv mrest
            have hDestMem :=
              branchMid_jump_stacks hCheck hBlock hInstr hLookup hMidEntry
            have hNextPc :
                (gasfulJumpNext state rest (EvmYul.UInt256.ofNat dest)).pc =
                  EvmYul.UInt256.ofNat dest := by
              simp [gasfulJumpNext]
            have hNextStack :
                (gasfulJumpNext state rest
                    (EvmYul.UInt256.ofNat dest)).stack = rest := by
              simp [gasfulJumpNext]
            refine ⟨mrest, ?_, ?_⟩
            · rw [hNextPc]
              exact hDestMem
            · rw [hNextStack]
              exact hAgreesRest
      · -- JUMPI
        rw [hJumpi] at hLocatedInstr hInstr
        simp only [if_true] at hLocatedInstr hInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMPI, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        have hPair :
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)) =
              (EvmYul.Operation.JUMPI, none) := by
          simp [hDecoded]
        have hEnough : ¬ state.stack.length < 2 := by
          simpa [decodedOperationAt, hPair, EvmYul.EVM.δ] using
            hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
        cases rest with
        | nil =>
            exfalso
            apply hEnough
            simp [hStack]
        | cons cond tail =>
            have hStack' : state.stack =
                EvmYul.UInt256.ofNat dest :: cond :: tail := by
              simpa using hStack
            have hExact :=
              evm_step_jumpi_eq_next fuel state none tail
                (EvmYul.UInt256.ofNat dest) cond hStack'
            rw [hDecoded] at hStep
            simp only [Option.getD_some] at hStep
            rw [hExact] at hStep
            have hNext : next = gasfulJumpiNext state tail
                (EvmYul.UInt256.ofNat dest) cond := by
              simpa using hStep.symm
            subst next
            rw [hStack'] at hAgrees
            cases hAgrees with
            | cons hv hAgrees1 =>
                cases hAgrees1 with
                | cons hCv hAgreesTail =>
                    rename_i mv cv mtail
                    have hBoth :=
                      branchMid_jumpi_stacks hCheck hBlock hInstr hLookup
                        hMidEntry hCv
                    by_cases hCond : cond != EvmYul.UInt256.ofNat 0
                    · have hNextPc :
                          (gasfulJumpiNext state tail
                              (EvmYul.UInt256.ofNat dest) cond).pc =
                            EvmYul.UInt256.ofNat dest := by
                        simp [gasfulJumpiNext, hCond]
                      have hNextStack :
                          (gasfulJumpiNext state tail
                              (EvmYul.UInt256.ofNat dest) cond).stack =
                            tail := by
                        simp [gasfulJumpiNext]
                      refine ⟨mtail, ?_, ?_⟩
                      · rw [hNextPc]
                        exact hBoth.1 (word_bne_eq_true_iff.mp hCond)
                      · rw [hNextStack]
                        exact hAgreesTail
                    · have hCondEq : cond = EvmYul.UInt256.ofNat 0 := by
                        by_contra hne
                        exact hCond (word_bne_eq_true_iff.mpr hne)
                      have hNextPc :
                          (gasfulJumpiNext state tail
                              (EvmYul.UInt256.ofNat dest) cond).pc =
                            EvmYul.UInt256.ofNat
                              (block.compactPc + artifact.branchWidth +
                                2) := by
                        simp [gasfulJumpiNext, hCond, hPc]
                        rw [uint256_ofNat_add]
                      have hNextStack :
                          (gasfulJumpiNext state tail
                              (EvmYul.UInt256.ofNat dest) cond).stack =
                            tail := by
                        simp [gasfulJumpiNext]
                      refine ⟨mtail, ?_, ?_⟩
                      · rw [hNextPc]
                        exact hBoth.2 hCondEq
                      · rw [hNextStack]
                        exact hAgreesTail

theorem heightPoint_sentinel_no_success
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {state next : EVMState} {stepFuel : Nat}
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hCode : state.executionEnv.code = bytes)
    (hPc : state.pc = EvmYul.UInt256.ofNat
      (Compact.Program.codeByteLength artifact.program.code))
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) : False :=
  artifactFramePoint_sentinel_no_success hSentinel hCode hPc hStep

theorem stackArity?_isSome_of_continuingStep
    {op : PrimOp} {primStep : PrimStep}
    (hContinuing : op.continuingStep? = some primStep) :
    ∃ input output, op.stackArity? = some (input, output) := by
  cases op <;>
    first
      | exact ⟨_, _, rfl⟩
      | simp [PrimOp.continuingStep?] at hContinuing

theorem heightPoint_prim_continuing_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {op : PrimOp} {primStep : PrimStep}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim op)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hContinuing : op.continuingStep? = some primStep)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hDecodedOp : decodedOperationAt state = op.toEVM := by
        simp [decodedOperationAt, hDecoded]
      have hStaticPermits : continuingPrimStaticPermits state op :=
        continuingPrimStaticPermits_of_static_check hPrefix.static hDecodedOp
      have hGasful :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (op.toEVM, none)) (afterMemoryChargeAt state) =
            .ok next := by
        simpa [hDecoded] using hStep
      have hPrim :
          op.step (afterEVMInstructionChargeAt state) = .ok next := by
        rw [← hGasful]
        exact (evm_step_continuing_prim_after_charges hContinuing trivial
          hStaticPermits).symm
      by_cases hInvalid : op = .invalid
      · subst op
        rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
        have hStepInvalid : primStep = .invalid := by
          simpa [PrimOp.continuingStep?] using hContinuing.symm
        subst primStep
        simp [PrimStep.run] at hPrim
      · obtain ⟨input, output, hArity⟩ :=
          stackArity?_isSome_of_continuingStep hContinuing
        have hNextPcRaw := PrimOp.step_pc_of_stackArity hArity hPrim
        have hNextPc : next.pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
          rw [hNextPcRaw, afterEVMInstructionChargeAt_pc, hPc,
            uint256_ofNat_add]
        obtain ⟨astack, hMemPc, hAgrees⟩ := hHeight
        have hEntry :
            memStack cert.table
                (EvmYul.UInt256.ofNat block.compactPc) astack = true := by
          rw [← hPc]; exact hMemPc
        have hOk := check?_blockOk hCheck hBlock
        simp only [blockOk?, hInstr, if_neg hInvalid, hArity] at hOk
        have hFlow := all_stacksAt_apply hOk hEntry
        cases hAbs : absPrim? op astack with
        | none =>
            rw [hAbs] at hFlow
            cases hFlow
        | some astack' =>
        rw [hAbs] at hFlow
        refine ⟨astack', ?_, ?_⟩
        · rw [hNextPc]
          exact hFlow
        · exact agrees_absPrim_step hContinuing hArity hAbs
            (by
              rw [afterEVMInstructionChargeAt_stack]
              exact hAgrees) hPrim

theorem heightPoint_resource_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (kind : Simulation.ResourceQuery)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (resourcePrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some ((resourcePrimOp kind).toEVM, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded] using hStep
      rw [evm_step_resource_eq] at hActual
      cases hActual
      obtain ⟨astack, hMemPc, hAgrees⟩ := hHeight
      have hEntry :
          memStack cert.table (EvmYul.UInt256.ofNat block.compactPc)
            astack = true := by
        rw [← hPc]; exact hMemPc
      have hArity :
          (resourcePrimOp kind).stackArity? = some (0, 1) := by
        cases kind <;> rfl
      have hOk := check?_blockOk hCheck hBlock
      have hInvalid : resourcePrimOp kind ≠ .invalid := by
        cases kind <;> simp [resourcePrimOp]
      simp only [blockOk?, hInstr, if_neg hInvalid, hArity] at hOk
      have hFlow := all_stacksAt_apply hOk hEntry
      have hAbs : absPrim? (resourcePrimOp kind) astack =
          some (none :: astack) := by
        cases kind <;>
          simp [absPrim?, PrimOp.continuingStep?, PrimOp.stackArity?,
            resourcePrimOp, EvmYul.EVM.δ, EvmYul.EVM.α, PrimOp.toEVM,
            List.replicate]
      rw [hAbs] at hFlow
      have hNextPc :
          (gasfulResourceNext kind state).pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        simp [gasfulResourceNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hPc, uint256_ofNat_add]
      have hNextLen :
          (gasfulResourceNext kind state).stack.length =
            state.stack.length + 1 := by
        cases kind <;>
          simp [gasfulResourceNext, afterEVMInstructionChargeAt,
            afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      have hNextTail :
          (gasfulResourceNext kind state).stack.tail = state.stack := by
        cases kind <;>
          simp [gasfulResourceNext, afterEVMInstructionChargeAt,
            afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      cases hNS : (gasfulResourceNext kind state).stack with
      | nil =>
          rw [hNS] at hNextLen
          simp at hNextLen
      | cons v tl =>
          have hTl : tl = state.stack := by
            have hT := hNextTail
            rw [hNS] at hT
            simpa using hT
          subst hTl
          refine ⟨none :: astack, ?_, ?_⟩
          · rw [hNextPc]
            exact hFlow
          · rw [hNS]
            exact agrees_cons agreesVal_none hAgrees

theorem heightPoint_pc_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state next : EVMState} {block : Compact.SourceBlock}
    {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim .pc)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (EvmYul.Operation.PC, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded, PrimOp.toEVM] using hStep
      rw [evm_step_pc_eq_next] at hActual
      cases hActual
      obtain ⟨astack, hMemPc, hAgrees⟩ := hHeight
      have hEntry :
          memStack cert.table (EvmYul.UInt256.ofNat block.compactPc)
            astack = true := by
        rw [← hPc]; exact hMemPc
      have hOk := check?_blockOk hCheck hBlock
      have hInvalid : PrimOp.pc ≠ PrimOp.invalid := by simp
      have hArity : PrimOp.pc.stackArity? = some (0, 1) := rfl
      simp only [blockOk?, hInstr, if_neg hInvalid, hArity] at hOk
      have hFlow := all_stacksAt_apply hOk hEntry
      have hAbs : absPrim? PrimOp.pc astack = some (none :: astack) := by
        simp [absPrim?, PrimOp.continuingStep?, PrimOp.stackArity?,
          EvmYul.EVM.δ, EvmYul.EVM.α, PrimOp.toEVM, List.replicate]
      rw [hAbs] at hFlow
      have hNextPc :
          (gasfulPcNext state).pc =
            EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, hPc, uint256_ofNat_add]
      have hNextLen :
          (gasfulPcNext state).stack.length =
            state.stack.length + 1 := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      have hNextTail :
          (gasfulPcNext state).stack.tail = state.stack := by
        simp [gasfulPcNext, afterEVMInstructionChargeAt,
          afterMemoryChargeAt, afterDynamicChargeAt, chargeGas,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
      cases hNS : (gasfulPcNext state).stack with
      | nil =>
          rw [hNS] at hNextLen
          simp at hNextLen
      | cons v tl =>
          have hTl : tl = state.stack := by
            have hT := hNextTail
            rw [hNS] at hT
            simpa using hT
          subst hTl
          refine ⟨none :: astack, ?_, ?_⟩
          · rw [hNextPc]
            exact hFlow
          · rw [hNS]
            exact agrees_cons agreesVal_none hAgrees

theorem callPrimOp_args_arity
    (kind : Simulation.CallKind) (operands : Simulation.CallOperands) :
    (callPrimOp kind).stackArity? =
      some ((Simulation.CallKind.args kind operands).length, 1) := by
  cases kind <;> rfl

theorem createPrimOp_args_arity
    (kind : Simulation.CreateKind) (operands : Simulation.CreateOperands) :
    (createPrimOp kind).stackArity? =
      some ((Simulation.CreateKind.args kind operands).length, 1) := by
  cases kind <;> rfl

theorem heightPoint_call_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (kind : Simulation.CallKind)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (callPrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  have hOpEq : (callPrimOp kind).toEVM = kind.toEVMOperation := by
    cases kind <;> rfl
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simp [decodedOperationAt, hDecoded, hOpEq]
  obtain ⟨rest, operands, hOperands⟩ :=
    call_operands_of_stackEnough_kind kind hPrefix.static.stackLimit
      hDecodedOp
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (kind.toEVMOperation, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded, hOpEq] using hStep
      obtain ⟨response, hResponse⟩ :=
        evm_step_call_responseStateRel_at kind hDecodedOp hOperands hActual
      have hStack :=
        CallKind.stack_eq_args_append_of_evmOperands hOperands
      have hLen : state.stack.length =
          (Simulation.CallKind.args kind operands).length + rest.length := by
        rw [hStack]; simp
      have hNextLen : next.stack.length = rest.length + 1 := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCall,
          EvmYul.EVM.State.incrPC]
      have hNextTail : next.stack.tail = rest := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCall,
          EvmYul.EVM.State.incrPC]
      have hNextPc : next.pc =
          EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        calc
          next.pc =
              (InteractionSemantics.EVMState.finishCall
                (afterDynamicChargeAt state) rest operands.callLocal
                  response).pc := hResponse.pc_eq
          _ = state.pc + EvmYul.UInt256.ofNat 1 := by
            simp [InteractionSemantics.EVMState.finishCall,
              InteractionSemantics.EVMState.installWorld,
              afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
              EvmYul.EVM.State.incrPC]
          _ = EvmYul.UInt256.ofNat (block.compactPc + 1) := by
            rw [hPc, uint256_ofNat_add]
      obtain ⟨astack, hMemPc, hAgrees⟩ := hHeight
      have hEntry :
          memStack cert.table (EvmYul.UInt256.ofNat block.compactPc)
            astack = true := by
        rw [← hPc]; exact hMemPc
      have hArity := callPrimOp_args_arity kind operands
      have hInvalid : callPrimOp kind ≠ .invalid := by
        cases kind <;> simp [callPrimOp]
      have hOk := check?_blockOk hCheck hBlock
      simp only [blockOk?, hInstr, if_neg hInvalid, hArity] at hOk
      have hFlow := all_stacksAt_apply hOk hEntry
      have hNe : callPrimOp kind ≠ .eq := by
        cases kind <;> simp [callPrimOp]
      have hCont : (callPrimOp kind).continuingStep? = none := by
        cases kind <;> rfl
      have hBound :
          (Simulation.CallKind.args kind operands).length ≤
            astack.length := by
        rw [agrees_length hAgrees]
        omega
      have hAbs : absPrim? (callPrimOp kind) astack =
          some (none ::
            astack.drop
              (Simulation.CallKind.args kind operands).length) := by
        simp [absPrim?, hNe, hCont, hArity, List.replicate]
        simpa using hBound
      rw [hAbs] at hFlow
      obtain ⟨v, tl, hNS⟩ :
          ∃ v tl, next.stack = v :: tl := by
        cases hCase : next.stack with
        | nil => rw [hCase] at hNextLen; simp at hNextLen
        | cons v tl => exact ⟨v, tl, rfl⟩
      have hTl : tl = rest := by
        have := hNextTail
        rw [hNS] at this
        simpa using this
      subst hTl
      refine ⟨none ::
        astack.drop (Simulation.CallKind.args kind operands).length,
        ?_, ?_⟩
      · rw [hNextPc]
        exact hFlow
      · rw [hNS]
        refine agrees_cons agreesVal_none ?_
        have hDrop := agrees_drop hAgrees
          (Simulation.CallKind.args kind operands).length
        rw [hStack, List.drop_left] at hDrop
        exact hDrop

theorem heightPoint_create_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {state next : EVMState}
    {block : Compact.SourceBlock} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (kind : Simulation.CreateKind)
    (hCode : state.executionEnv.code = bytes)
    (hBlock : block ∈ artifact.blocks)
    (hInstr : block.sourceInstr = .prim (createPrimOp kind))
    (hPc : state.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hHeight : HeightPoint cert.table state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .ok next) :
    HeightPoint cert.table next := by
  have hDecoded := artifact_prim_decode hCompile hDecode hCode hBlock
    hInstr hPc
  have hOpEq : (createPrimOp kind).toEVM = kind.toEVMOperation := by
    cases kind <;> rfl
  have hDecodedOp : decodedOperationAt state = kind.toEVMOperation := by
    simp [decodedOperationAt, hDecoded, hOpEq]
  obtain ⟨rest, operands, hOperands⟩ :=
    create_operands_of_stackEnough_kind kind hPrefix.static.stackLimit
      hDecodedOp
  cases stepFuel with
  | zero => simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
      have hActual :
          EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
              (some (kind.toEVMOperation, none))
              (afterMemoryChargeAt state) = .ok next := by
        simpa [hDecoded, hOpEq] using hStep
      obtain ⟨response, hResponse⟩ :=
        evm_step_create_responseStateRel_at kind hDecodedOp hOperands hActual
      have hStack :=
        CreateKind.stack_eq_args_append_of_evmOperands hOperands
      have hLen : state.stack.length =
          (Simulation.CreateKind.args kind operands).length +
            rest.length := by
        rw [hStack]; simp
      have hNextLen : next.stack.length = rest.length + 1 := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCreate,
          EvmYul.EVM.State.incrPC]
      have hNextTail : next.stack.tail = rest := by
        have hStackEq := hResponse.openStateRel.stack_eq
        rw [hStackEq]
        simp [InteractionSemantics.EVMState.finishCreate,
          EvmYul.EVM.State.incrPC]
      have hNextPc : next.pc =
          EvmYul.UInt256.ofNat (block.compactPc + 1) := by
        calc
          next.pc =
              (InteractionSemantics.EVMState.finishCreate
                (afterDynamicChargeAt state) rest operands.createLocal
                  response).pc := hResponse.pc_eq
          _ = state.pc + EvmYul.UInt256.ofNat 1 := by
            simp [InteractionSemantics.EVMState.finishCreate,
              InteractionSemantics.EVMState.installWorld,
              afterDynamicChargeAt, afterMemoryChargeAt, chargeGas,
              EvmYul.EVM.State.incrPC]
          _ = EvmYul.UInt256.ofNat (block.compactPc + 1) := by
            rw [hPc, uint256_ofNat_add]
      obtain ⟨astack, hMemPc, hAgrees⟩ := hHeight
      have hEntry :
          memStack cert.table (EvmYul.UInt256.ofNat block.compactPc)
            astack = true := by
        rw [← hPc]; exact hMemPc
      have hArity := createPrimOp_args_arity kind operands
      have hInvalid : createPrimOp kind ≠ .invalid := by
        cases kind <;> simp [createPrimOp]
      have hOk := check?_blockOk hCheck hBlock
      simp only [blockOk?, hInstr, if_neg hInvalid, hArity] at hOk
      have hFlow := all_stacksAt_apply hOk hEntry
      have hNe : createPrimOp kind ≠ .eq := by
        cases kind <;> simp [createPrimOp]
      have hCont : (createPrimOp kind).continuingStep? = none := by
        cases kind <;> rfl
      have hBound :
          (Simulation.CreateKind.args kind operands).length ≤
            astack.length := by
        rw [agrees_length hAgrees]
        omega
      have hAbs : absPrim? (createPrimOp kind) astack =
          some (none ::
            astack.drop
              (Simulation.CreateKind.args kind operands).length) := by
        simp [absPrim?, hNe, hCont, hArity, List.replicate]
        simpa using hBound
      rw [hAbs] at hFlow
      obtain ⟨v, tl, hNS⟩ :
          ∃ v tl, next.stack = v :: tl := by
        cases hCase : next.stack with
        | nil => rw [hCase] at hNextLen; simp at hNextLen
        | cons v tl => exact ⟨v, tl, rfl⟩
      have hTl : tl = rest := by
        have := hNextTail
        rw [hNS] at this
        simpa using this
      subst hTl
      refine ⟨none ::
        astack.drop (Simulation.CreateKind.args kind operands).length,
        ?_, ?_⟩
      · rw [hNextPc]
        exact hFlow
      · rw [hNS]
        refine agrees_cons agreesVal_none ?_
        have hDrop := agrees_drop hAgrees
          (Simulation.CreateKind.args kind operands).length
        rw [hStack, List.drop_left] at hDrop
        exact hDrop

/-! ## The height invariant along reachable frame states -/

theorem heightPoint_step
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {current next : EVMState} {stepFuel : Nat}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes current)
    (hHeight : HeightPoint cert.table current)
    (hPrefix : XSstoreStipendChecksPass validJumps current)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt current)
        (some
          ((EvmYul.EVM.decode current.executionEnv.code current.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt current) = .ok next)
    (hContinues : haltOutputAt next (decodedOperationAt current) = none) :
    HeightPoint cert.table next := by
  rcases hPoint with ⟨hCode, hControl⟩
  cases hControl with
  | boundary block hBlock hPc =>
      generalize hInstr : block.sourceInstr = instr
      cases instr with
      | label label =>
          exact heightPoint_label_step hCompile hDecode hCheck hCode hBlock
            hInstr hPc hHeight hStep
      | push value =>
          exact heightPoint_push_step hCompile hDecode hCheck hCode hBlock
            hInstr hPc hHeight hStep
      | jump label =>
          exact heightPoint_branch_push_step hCompile hDecode hCheck hCode
            hBlock (isJumpi := false) (by simpa using hInstr) hPc hHeight
            hStep
      | jumpi label =>
          exact heightPoint_branch_push_step hCompile hDecode hCheck hCode
            hBlock (isJumpi := true) (by simpa using hInstr) hPc hHeight
            hStep
      | pushLabel target =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | jumpDynamic =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | prim op =>
          have hDecoded := artifact_prim_decode hCompile hDecode hCode
            hBlock hInstr hPc
          cases hContinuing : op.continuingStep? with
          | some primStep =>
              exact heightPoint_prim_continuing_step hCompile hDecode hCheck
                hCode hBlock hInstr hPc hContinuing hPrefix hHeight hStep
          | none =>
              by_cases hPcOp : op = .pc
              · subst op
                exact heightPoint_pc_step hCompile hDecode hCheck hCode
                  hBlock hInstr hPc hHeight hStep
              · by_cases hGasOp : op = .gas
                · subst op
                  exact heightPoint_resource_step hCompile hDecode hCheck
                    .gas hCode hBlock
                    (by simpa [resourcePrimOp] using hInstr) hPc hHeight
                    hStep
                · by_cases hStopOp : op = .stop
                  · subst op
                    have hDecodedOp :
                        decodedOperationAt current =
                          EvmYul.Operation.STOP := by
                      simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
                    simp [hDecodedOp, haltOutputAt] at hContinues
                  · by_cases hReturnOp : op = .return
                    · subst op
                      have hDecodedOp :
                          decodedOperationAt current =
                            EvmYul.Operation.RETURN := by
                        simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
                      simp [hDecodedOp, haltOutputAt] at hContinues
                    · by_cases hRevertOp : op = .revert
                      · subst op
                        have hDecodedOp :
                            decodedOperationAt current =
                              EvmYul.Operation.REVERT := by
                          simp [decodedOperationAt, hDecoded, PrimOp.toEVM]
                        simp [hDecodedOp, haltOutputAt] at hContinues
                      · by_cases hSelfdestructOp : op = .selfdestruct
                        · subst op
                          have hDecodedOp :
                              decodedOperationAt current =
                                EvmYul.Operation.SELFDESTRUCT := by
                            simp [decodedOperationAt, hDecoded,
                              PrimOp.toEVM]
                          simp [hDecodedOp, haltOutputAt] at hContinues
                        · have hMsizeOp : op ≠ .msize := by
                            intro h
                            subst op
                            simp [PrimOp.continuingStep?] at hContinuing
                          have hValid :
                              EvmYul.EVM.δ op.toEVM ≠ none := by
                            have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
                            simpa [decodedOperationAt, hDecoded] using hRaw
                          rcases primOp_external_of_no_continuing op hValid
                              hPcOp hGasOp hMsizeOp hStopOp hReturnOp
                              hRevertOp hSelfdestructOp hContinuing with
                            ⟨kind, hCall⟩ | ⟨kind, hCreate⟩
                          · subst op
                            exact heightPoint_call_step hCompile hDecode
                              hCheck kind hCode hBlock hInstr hPc hPrefix
                              hHeight hStep
                          · subst op
                            exact heightPoint_create_step hCompile hDecode
                              hCheck kind hCode hBlock hInstr hPc hPrefix
                              hHeight hStep
  | branchMid block hBlock label isJumpi dest rest hInstr hLookup hPc
      hStack =>
      exact heightPoint_branchMid_step hCompile hDecode hCheck hCode hBlock
        hInstr hLookup hPc hStack hPrefix hHeight hStep
  | sentinel hPc =>
      exact False.elim
        (heightPoint_sentinel_no_success hSentinel hCode hPc hStep)

theorem heightPoint_initial {cert : Cert} {artifact : Compact.Artifact}
    {initial : EVMState}
    (hCheck : check? artifact cert = true)
    (hPc : initial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : initial.stack = []) :
    HeightPoint cert.table initial := by
  refine ⟨[], ?_, ?_⟩
  · rw [hPc]
    exact check?_anchor hCheck
  · rw [hStack]
    exact List.Forall₂.nil

theorem reach_heightPoint
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hFrame : ArtifactFrameInvariant artifact bytes validJumps initial)
    (hInitialHeight : HeightPoint cert.table initial) :
    ∀ state, FrameReachable validJumps initial state →
      HeightPoint cert.table state := by
  intro state hReach
  induction hReach with
  | initial => exact hInitialHeight
  | @next current next stepFuel hReach hPrefix hStep hContinues ih =>
      exact heightPoint_step hCompile hDecode hCheck hSentinel
        (hFrame current hReach) ih hPrefix hStep hContinues

/-! ## No reachable stack overflow -/

theorem prim_alpha_le_delta_succ (op : PrimOp) :
    (EvmYul.EVM.α op.toEVM).getD 0 ≤ (EvmYul.EVM.δ op.toEVM).getD 0 + 1 ∧
      (EvmYul.EVM.δ op.toEVM).getD 0 ≤ 20 := by
  cases op <;> exact ⟨by decide, by decide⟩

theorem pushOp_alpha_le_delta_succ
    {width : Nat} {op : EVMOp} {value : Word}
    (hFits : Compact.FitsWidth width value.toNat)
    (hOp : Compact.pushOp? width = some op) :
    (EvmYul.EVM.α op).getD 0 ≤ (EvmYul.EVM.δ op).getD 0 + 1 ∧
      (EvmYul.EVM.δ op).getD 0 ≤ 20 := by
  have hPos := hFits.1
  have hLe := hFits.2.1
  interval_cases width <;>
    simp [Compact.pushOp?] at hOp <;> cases hOp <;>
    exact ⟨by decide, by decide⟩

theorem decoded_alpha_le_delta_succ
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {state : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes state) :
    (EvmYul.EVM.α (decodedOperationAt state)).getD 0 ≤
        (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 + 1 ∧
      (EvmYul.EVM.δ (decodedOperationAt state)).getD 0 ≤ 20 := by
  rcases hPoint with ⟨hCode, hControl⟩
  cases hControl with
  | boundary block hBlock hPc =>
      generalize hInstr : block.sourceInstr = instr
      cases instr with
      | label label =>
          obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_label_entry_mem hCompile hBlock hInstr
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (EvmYul.Operation.JUMPDEST, none) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          simp [decodedOperationAt, hDecoded]
          exact ⟨by decide, by decide⟩
      | push value =>
          obtain ⟨width, located, hWidth, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_push_entry_mem hCompile hBlock hInstr
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth width value.toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (value, width)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          have hGoal := pushOp_alpha_le_delta_succ hFits hOp
          simpa [decodedOperationAt, hDecoded] using hGoal
      | jump label =>
          obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_branch_entry_mem hCompile hBlock
              (isJumpi := false) (by simpa using hInstr)
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth artifact.branchWidth
              (EvmYul.UInt256.ofNat dest).toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (EvmYul.UInt256.ofNat dest,
                  artifact.branchWidth)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          have hGoal := pushOp_alpha_le_delta_succ hFits hOp
          simpa [decodedOperationAt, hDecoded] using hGoal
      | jumpi label =>
          obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_branch_entry_mem hCompile hBlock
              (isJumpi := true) (by simpa using hInstr)
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth artifact.branchWidth
              (EvmYul.UInt256.ofNat dest).toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (EvmYul.UInt256.ofNat dest,
                  artifact.branchWidth)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          have hGoal := pushOp_alpha_le_delta_succ hFits hOp
          simpa [decodedOperationAt, hDecoded] using hGoal
      | pushLabel target =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | jumpDynamic =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | prim op =>
          have hDecoded := artifact_prim_decode hCompile hDecode hCode
            hBlock hInstr hPc
          have hGoal := prim_alpha_le_delta_succ op
          simpa [decodedOperationAt, hDecoded] using hGoal
  | branchMid block hBlock label isJumpi dest rest hInstr hLookup hPc
      hStack =>
      obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
        compact_branch_midpoint_mem hCompile hBlock hInstr
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
        hDecode.decodes located hMem
      have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
        hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
      cases hJumpi : isJumpi
      · rw [hJumpi] at hLocatedInstr
        simp only [Bool.false_eq_true, if_false] at hLocatedInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMP, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        simp [decodedOperationAt, hDecoded]
        exact ⟨by decide, by decide⟩
      · rw [hJumpi] at hLocatedInstr
        simp only [if_true] at hLocatedInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMPI, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        simp [decodedOperationAt, hDecoded]
        exact ⟨by decide, by decide⟩
  | sentinel hPc =>
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
      simp [Compact.Instr.decoded?] at hInstrDecoded
      subst decoded
      have hDecoded :
          EvmYul.EVM.decode state.executionEnv.code state.pc =
            some (EvmYul.Operation.INVALID, none) := by
        simpa [hCode, hPc] using hBytesDecoded
      simp [decodedOperationAt, hDecoded]
      exact ⟨by decide, by decide⟩

theorem noOverflow_of_heightPoint
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {state : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes state)
    (hHeight : HeightPoint cert.table state) :
    ¬ stackOverflowAt state := by
  intro hOverflow
  unfold stackOverflowAt at hOverflow
  obtain ⟨astack, hMem, hAgrees⟩ := hHeight
  have hLen : state.stack.length ≤ stackCap := by
    rw [← agrees_length hAgrees]
    exact memStack_length_le_cap (check?_bounded hCheck) hMem
  obtain ⟨hNet, hDelta⟩ :=
    decoded_alpha_le_delta_succ hCompile hDecode hSentinel hPoint
  unfold stackCap at hLen
  omega

/-- Certified programs never trip the interpreter's stack-limit precheck at
any reachable frame state. -/
theorem reach_noOverflow
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hFrame : ArtifactFrameInvariant artifact bytes validJumps initial)
    (hInitialHeight : HeightPoint cert.table initial) :
    ∀ state, FrameReachable validJumps initial state →
      ¬ stackOverflowAt state := by
  intro state hReach
  exact noOverflow_of_heightPoint hCompile hDecode hCheck hSentinel
    (hFrame state hReach)
    (reach_heightPoint hCompile hDecode hCheck hSentinel hFrame
      hInitialHeight state hReach)

/-! ## The gasful interpreter cannot report `StackOverflow` on certified code

`EvmYul.EVM.X` raises `StackOverflow` only from its per-step precheck, which
`reach_noOverflow` rules out at every reachable state.  The remaining error
sources (the step functions themselves and child frames) carry other labels,
established below. -/

theorem primStep_run_error_ne_stackOverflow
    {primStep : PrimStep} {state : EvmYul.EVM.State}
    {err : EVMException}
    (hRun : primStep.run state = .error err) :
    err ≠ EvmYul.EVM.ExecutionException.StackOverflow := by
  intro hEq
  subst hEq
  cases primStep <;>
    simp only [PrimStep.run, EvmYul.EVM.execBinOp, EvmYul.EVM.execUnOp,
      EvmYul.EVM.execTriOp, EvmYul.EVM.executionEnvOp,
      EvmYul.EVM.unaryExecutionEnvOp, EvmYul.EVM.machineStateOp,
      EvmYul.EVM.binaryMachineStateOp, EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.dup, EvmYul.swap] at hRun <;>
    (repeat' split at hRun) <;>
    first
      | cases Except.error.inj hRun
      | cases hRun
      | simp_all

/-- On certified code, a failing charged step at any generated control point
never carries the `StackOverflow` label. -/
theorem step_error_ne_stackOverflow_at
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray}
    {validJumps : Array Word} {state : EVMState} {stepFuel : Nat}
    {err : EVMException}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hPoint : ArtifactFramePoint artifact bytes state)
    (hPrefix : XSstoreStipendChecksPass validJumps state)
    (hStep :
      EvmYul.EVM.step stepFuel (dynamicGasCostAt state)
        (some
          ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
            (EvmYul.Operation.STOP, none)))
        (afterMemoryChargeAt state) = .error err) :
    err ≠ EvmYul.EVM.ExecutionException.StackOverflow := by
  intro hEq
  subst hEq
  rcases hPoint with ⟨hCode, hControl⟩
  cases stepFuel with
  | zero =>
      simp [EvmYul.EVM.step] at hStep
  | succ fuel =>
  cases hControl with
  | boundary block hBlock hPc =>
      generalize hInstr : block.sourceInstr = instr
      cases instr with
      | label label =>
          obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_label_entry_mem hCompile hBlock hInstr
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (EvmYul.Operation.JUMPDEST, none) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_jumpdest_eq_next fuel state none] at hStep
          cases hStep
      | push value =>
          obtain ⟨width, located, hWidth, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_push_entry_mem hCompile hBlock hInstr
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth width value.toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (value, width)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_push_eq_next fuel state value hFits hOp] at hStep
          cases hStep
      | jump label =>
          obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_branch_entry_mem hCompile hBlock
              (isJumpi := false) (by simpa using hInstr)
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth artifact.branchWidth
              (EvmYul.UInt256.ofNat dest).toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (EvmYul.UInt256.ofNat dest,
                  artifact.branchWidth)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_push_eq_next fuel state
            (EvmYul.UInt256.ofNat dest) hFits hOp] at hStep
          cases hStep
      | jumpi label =>
          obtain ⟨dest, located, hLookup, hMem, hLocatedPc, hLocatedInstr⟩ :=
            compact_branch_entry_mem hCompile hBlock
              (isJumpi := true) (by simpa using hInstr)
          have hLocatedValid :=
            (List.forall_iff_forall_mem.mp
              (Compact.compile?_valid hCompile).wellFormed.1) located hMem
          rw [hLocatedInstr] at hLocatedValid
          have hFits : Compact.FitsWidth artifact.branchWidth
              (EvmYul.UInt256.ofNat dest).toNat := by
            simpa [Compact.Instr.Valid] using hLocatedValid
          obtain ⟨op, hOp⟩ := Compact.exists_pushOp_of_width
            ⟨hFits.1, hFits.2.1⟩
          obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
            hDecode.decodes located hMem
          rw [hLocatedInstr] at hInstrDecoded
          simp [Compact.Instr.decoded?, hOp] at hInstrDecoded
          subst decoded
          have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
            hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
          have hDecoded :
              EvmYul.EVM.decode state.executionEnv.code state.pc =
                some (op, some (EvmYul.UInt256.ofNat dest,
                  artifact.branchWidth)) := by
            simpa [hCode, hStatePc] using hBytesDecoded
          rw [hDecoded] at hStep
          simp only [Option.getD_some] at hStep
          rw [evm_step_push_eq_next fuel state
            (EvmYul.UInt256.ofNat dest) hFits hOp] at hStep
          cases hStep
      | pushLabel target =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | jumpDynamic =>
          obtain ⟨_compactSize, _hSize, hEmit⟩ :=
            (Compact.compile?_blocksValid hCompile).block_emit_of_mem hBlock
          rw [hInstr] at hEmit
          simp [Compact.emitSourceBlock?, Compact.emitInstrRev?] at hEmit
      | prim op =>
          have hDecoded := artifact_prim_decode hCompile hDecode hCode
            hBlock hInstr hPc
          cases hContinuing : op.continuingStep? with
          | some primStep =>
              have hDecodedOp : decodedOperationAt state = op.toEVM := by
                simp [decodedOperationAt, hDecoded]
              have hStaticPermits : continuingPrimStaticPermits state op :=
                continuingPrimStaticPermits_of_static_check hPrefix.static
                  hDecodedOp
              have hGasful :
                  EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                      (some (op.toEVM, none)) (afterMemoryChargeAt state) =
                    .error EvmYul.EVM.ExecutionException.StackOverflow := by
                simpa [hDecoded] using hStep
              have hPrim :
                  op.step (afterEVMInstructionChargeAt state) =
                    .error EvmYul.EVM.ExecutionException.StackOverflow := by
                rw [← hGasful]
                exact (evm_step_continuing_prim_after_charges hContinuing
                  trivial hStaticPermits).symm
              rw [PrimOp.step_eq_continuingStep_run hContinuing] at hPrim
              exact primStep_run_error_ne_stackOverflow hPrim rfl
          | none =>
              by_cases hPcOp : op = .pc
              · subst op
                have hActual :
                    EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                        (some (EvmYul.Operation.PC, none))
                        (afterMemoryChargeAt state) =
                      .error
                        EvmYul.EVM.ExecutionException.StackOverflow := by
                  simpa [hDecoded, PrimOp.toEVM] using hStep
                rw [evm_step_pc_eq_next] at hActual
                cases hActual
              · by_cases hGasOp : op = .gas
                · subst op
                  have hActual :
                      EvmYul.EVM.step (fuel + 1) (dynamicGasCostAt state)
                          (some ((resourcePrimOp .gas).toEVM, none))
                          (afterMemoryChargeAt state) =
                        .error
                          EvmYul.EVM.ExecutionException.StackOverflow := by
                    simpa [hDecoded, resourcePrimOp, PrimOp.toEVM]
                      using hStep
                  rw [evm_step_resource_eq] at hActual
                  cases hActual
                · by_cases hStopOp : op = .stop
                  · subst op
                    have hPair :
                        ((EvmYul.EVM.decode state.executionEnv.code
                            state.pc).getD
                          (EvmYul.Operation.STOP, none)) =
                          (EvmYul.Operation.STOP, none) := by
                      simp [hDecoded, PrimOp.toEVM]
                    rw [hPair] at hStep
                    have hOk :=
                      evm_step_stop_after_charges
                        (fuel := fuel) (state := state)
                    rw [hPair] at hOk
                    rw [hOk] at hStep
                    cases hStep
                  · by_cases hReturnOp : op = .return
                    · subst op
                      have hEnough : ¬ state.stack.length < 2 := by
                        have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                        simpa [decodedOperationAt, hDecoded, PrimOp.toEVM,
                          EvmYul.EVM.δ] using hRaw
                      match hStack : state.stack with
                      | [] => exact hEnough (by simp [hStack])
                      | [top] => exact hEnough (by simp [hStack])
                      | top :: second :: rest =>
                          have hPop :
                              (afterEVMInstructionChargeAt
                                  state).stack.pop2 =
                                some ⟨rest, top, second⟩ := by
                            rw [afterEVMInstructionChargeAt_stack, hStack]
                            rfl
                          have hPair :
                              ((EvmYul.EVM.decode state.executionEnv.code
                                  state.pc).getD
                                (EvmYul.Operation.STOP, none)) =
                                (EvmYul.Operation.RETURN, none) := by
                            simp [hDecoded, PrimOp.toEVM]
                          rw [hPair] at hStep
                          have hOk :=
                            evm_step_return_after_charges
                              (fuel := fuel) (state := state) hPop
                          rw [hPair] at hOk
                          rw [hOk] at hStep
                          cases hStep
                    · by_cases hRevertOp : op = .revert
                      · subst op
                        have hEnough : ¬ state.stack.length < 2 := by
                          have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                          simpa [decodedOperationAt, hDecoded,
                            PrimOp.toEVM, EvmYul.EVM.δ] using hRaw
                        match hStack : state.stack with
                        | [] => exact hEnough (by simp [hStack])
                        | [top] => exact hEnough (by simp [hStack])
                        | top :: second :: rest =>
                            have hPop :
                                (afterEVMInstructionChargeAt
                                    state).stack.pop2 =
                                  some ⟨rest, top, second⟩ := by
                              rw [afterEVMInstructionChargeAt_stack,
                                hStack]
                              rfl
                            have hPair :
                                ((EvmYul.EVM.decode
                                    state.executionEnv.code
                                    state.pc).getD
                                  (EvmYul.Operation.STOP, none)) =
                                  (EvmYul.Operation.REVERT, none) := by
                              simp [hDecoded, PrimOp.toEVM]
                            rw [hPair] at hStep
                            have hOk :=
                              evm_step_revert_after_charges
                                (fuel := fuel) (state := state) hPop
                            rw [hPair] at hOk
                            rw [hOk] at hStep
                            cases hStep
                      · by_cases hSelfdestructOp : op = .selfdestruct
                        · subst op
                          have hEnough : ¬ state.stack.length < 1 := by
                            have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
                            simpa [decodedOperationAt, hDecoded,
                              PrimOp.toEVM, EvmYul.EVM.δ] using hRaw
                          match hStack : state.stack with
                          | [] => exact hEnough (by simp [hStack])
                          | recipient :: rest =>
                              have hPair :
                                  ((EvmYul.EVM.decode
                                      state.executionEnv.code
                                      state.pc).getD
                                    (EvmYul.Operation.STOP, none)) =
                                    (EvmYul.Operation.SELFDESTRUCT,
                                      none) := by
                                simp [hDecoded, PrimOp.toEVM]
                              rw [hPair] at hStep
                              rw [evm_step_selfdestruct_eq_next fuel state
                                recipient rest hStack] at hStep
                              cases hStep
                        · have hMsizeOp : op ≠ .msize := by
                            intro h
                            subst op
                            simp [PrimOp.continuingStep?] at hContinuing
                          have hValid :
                              EvmYul.EVM.δ op.toEVM ≠ none := by
                            have hRaw := hPrefix.static.stackLimit.memoryAccess.jumps.stack.opcodeValid_raw
                            simpa [decodedOperationAt, hDecoded] using hRaw
                          rcases primOp_external_of_no_continuing op hValid
                              hPcOp hGasOp hMsizeOp hStopOp hReturnOp
                              hRevertOp hSelfdestructOp hContinuing with
                            ⟨kind, hCall⟩ | ⟨kind, hCreate⟩
                          · subst op
                            have hOpEq :
                                (callPrimOp kind).toEVM =
                                  kind.toEVMOperation := by
                              cases kind <;> rfl
                            have hDecodedOp :
                                decodedOperationAt state =
                                  kind.toEVMOperation := by
                              simp [decodedOperationAt, hDecoded, hOpEq]
                            obtain ⟨rest, operands, hOperands⟩ :=
                              call_operands_of_stackEnough_kind kind
                                hPrefix.static.stackLimit hDecodedOp
                            have hActual :
                                EvmYul.EVM.step (fuel + 1)
                                    (dynamicGasCostAt state)
                                    (some (kind.toEVMOperation, none))
                                    (afterMemoryChargeAt state) =
                                  .error
                                    EvmYul.EVM.ExecutionException.StackOverflow := by
                              simpa [hDecoded, hOpEq] using hStep
                            have hErr :=
                              evm_step_call_error_eq_outOfFuel_at
                                hOperands hActual
                            cases hErr
                          · subst op
                            have hOpEq :
                                (createPrimOp kind).toEVM =
                                  kind.toEVMOperation := by
                              cases kind <;> rfl
                            have hDecodedOp :
                                decodedOperationAt state =
                                  kind.toEVMOperation := by
                              simp [decodedOperationAt, hDecoded, hOpEq]
                            obtain ⟨rest, operands, hOperands⟩ :=
                              create_operands_of_stackEnough_kind kind
                                hPrefix.static.stackLimit hDecodedOp
                            have hActual :
                                EvmYul.EVM.step (fuel + 1)
                                    (dynamicGasCostAt state)
                                    (some (kind.toEVMOperation, none))
                                    (afterMemoryChargeAt state) =
                                  .error
                                    EvmYul.EVM.ExecutionException.StackOverflow := by
                              simpa [hDecoded, hOpEq] using hStep
                            have hErr :=
                              evm_step_create_positive_error_eq_outOfGas_at
                                hOperands hActual
                            cases hErr
  | branchMid block hBlock label isJumpi dest rest hInstr hLookup hPc
      hStack =>
      obtain ⟨located, hMem, hLocatedPc, hLocatedInstr⟩ :=
        compact_branch_midpoint_mem hCompile hBlock hInstr
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ :=
        hDecode.decodes located hMem
      have hStatePc : state.pc = EvmYul.UInt256.ofNat located.pc :=
        hPc.trans (congrArg EvmYul.UInt256.ofNat hLocatedPc.symm)
      cases hJumpi : isJumpi
      · rw [hJumpi] at hLocatedInstr
        simp only [Bool.false_eq_true, if_false] at hLocatedInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMP, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        rw [hDecoded] at hStep
        simp only [Option.getD_some] at hStep
        rw [evm_step_jump_eq_next fuel state none rest
          (EvmYul.UInt256.ofNat dest) hStack] at hStep
        cases hStep
      · rw [hJumpi] at hLocatedInstr
        simp only [if_true] at hLocatedInstr
        rw [hLocatedInstr] at hInstrDecoded
        simp [Compact.Instr.decoded?] at hInstrDecoded
        subst decoded
        have hDecoded :
            EvmYul.EVM.decode state.executionEnv.code state.pc =
              some (EvmYul.Operation.JUMPI, none) := by
          simpa [hCode, hStatePc] using hBytesDecoded
        have hPair :
            ((EvmYul.EVM.decode state.executionEnv.code state.pc).getD
              (EvmYul.Operation.STOP, none)) =
              (EvmYul.Operation.JUMPI, none) := by
          simp [hDecoded]
        have hEnough : ¬ state.stack.length < 2 := by
          simpa [decodedOperationAt, hPair, EvmYul.EVM.δ] using
            hPrefix.static.stackLimit.memoryAccess.jumps.stack.stackEnough
        cases rest with
        | nil =>
            exact hEnough (by simp [hStack])
        | cons cond tail =>
            have hStack' : state.stack =
                EvmYul.UInt256.ofNat dest :: cond :: tail := by
              simpa using hStack
            rw [hDecoded] at hStep
            simp only [Option.getD_some] at hStep
            rw [evm_step_jumpi_eq_next fuel state none tail
              (EvmYul.UInt256.ofNat dest) cond hStack'] at hStep
            cases hStep
  | sentinel hPc =>
      obtain ⟨decoded, hInstrDecoded, hBytesDecoded⟩ := hSentinel
      simp [Compact.Instr.decoded?] at hInstrDecoded
      subst decoded
      have hDecoded :
          EvmYul.EVM.decode state.executionEnv.code state.pc =
            some (EvmYul.Operation.INVALID, none) := by
        simpa [hCode, hPc] using hBytesDecoded
      rw [hDecoded] at hStep
      simp only [Option.getD_some] at hStep
      change EvmYul.step (τ := .EVM) EvmYul.Operation.INVALID none
        { { afterMemoryChargeAt state with
              execLength := (afterMemoryChargeAt state).execLength + 1 } with
          gasAvailable := (afterMemoryChargeAt state).gasAvailable -
            EvmYul.UInt256.ofNat (dynamicGasCostAt state) } =
        Except.error EvmYul.EVM.ExecutionException.StackOverflow at hStep
      change (Except.error EvmYul.EVM.ExecutionException.InvalidInstruction :
          Except EVMException EVMState) =
        Except.error EvmYul.EVM.ExecutionException.StackOverflow at hStep
      cases hStep

/-- Fuel induction over `EvmYul.EVM.X`: with the reachable no-overflow
invariant and step-error classification, the frame run never reports
`StackOverflow`. -/
theorem x_ne_stackOverflow_of_invariants
    {validJumps : Array Word} {initial : EVMState}
    (hNoOverflow :
      ∀ s, FrameReachable validJumps initial s → ¬ stackOverflowAt s)
    (hStepErr :
      ∀ (s : EVMState) (stepFuel : Nat) (err : EVMException),
        FrameReachable validJumps initial s →
        XSstoreStipendChecksPass validJumps s →
        EvmYul.EVM.step stepFuel (dynamicGasCostAt s)
            (some
              ((EvmYul.EVM.decode s.executionEnv.code s.pc).getD
                (EvmYul.Operation.STOP, none)))
            (afterMemoryChargeAt s) = .error err →
        err ≠ EvmYul.EVM.ExecutionException.StackOverflow) :
    ∀ (fuel : Nat) (s : EVMState), FrameReachable validJumps initial s →
      EvmYul.EVM.X fuel validJumps s ≠
        .error EvmYul.EVM.ExecutionException.StackOverflow := by
  intro fuel
  induction fuel with
  | zero =>
      intro s _hReach hEq
      simp [EvmYul.EVM.X] at hEq
  | succ f ih =>
      intro s hReach hEq
      by_cases hMem : s.gasAvailable.toNat < memoryExpansionCostAt s
      · rw [x_outOfGas_before_memory_charge hMem] at hEq
        cases Except.error.inj hEq
      by_cases hDyn :
          (afterMemoryChargeAt s).gasAvailable.toNat < dynamicGasCostAt s
      · rw [x_outOfGas_before_dynamic_charge hMem hDyn] at hEq
        cases Except.error.inj hEq
      have hGas : XGasChecksPass s := ⟨hMem, hDyn⟩
      by_cases hOpc : EvmYul.EVM.δ (decodedOperationAt s) = none
      · rw [x_invalid_instruction_after_gas_checks hGas hOpc] at hEq
        cases Except.error.inj hEq
      by_cases hUnder :
          s.stack.length < (EvmYul.EVM.δ (decodedOperationAt s)).getD 0
      · rw [x_stack_underflow_after_gas_opcode_check hGas hOpc hUnder]
          at hEq
        cases Except.error.inj hEq
      have hOpcode : XOpcodeStackChecksPass s := ⟨hGas, hOpc, hUnder⟩
      by_cases hBJ : badJumpAt validJumps s
      · rw [x_bad_jump_destination_after_stack_check hOpcode hBJ] at hEq
        cases Except.error.inj hEq
      by_cases hBJI : badJumpiAt validJumps s
      · rw [x_bad_jumpi_destination_after_stack_check hOpcode hBJI] at hEq
        cases Except.error.inj hEq
      have hJumps : XJumpChecksPass validJumps s := ⟨hOpcode, hBJ, hBJI⟩
      by_cases hRdc : invalidReturnDataCopyAt s
      · rw [x_invalid_returndatacopy_after_jump_checks hJumps hRdc] at hEq
        cases Except.error.inj hEq
      have hMemoryAccess : XMemoryAccessChecksPass validJumps s :=
        ⟨hJumps, hRdc⟩
      have hNoOverflowAt : ¬ stackOverflowAt s := hNoOverflow s hReach
      have hStackLimit : XStackLimitChecksPass validJumps s :=
        ⟨hMemoryAccess, hNoOverflowAt⟩
      by_cases hStatic : staticModeViolationAt s
      · rw [x_static_mode_violation_after_stack_limit_checks hStackLimit
          hStatic] at hEq
        cases Except.error.inj hEq
      have hStaticPass : XStaticChecksPass validJumps s :=
        ⟨hStackLimit, hStatic⟩
      by_cases hSstore : sstoreStipendOutOfGasAt s
      · rw [x_sstore_stipend_outOfGas_after_static_check hStaticPass
          hSstore] at hEq
        cases Except.error.inj hEq
      have hPrefixS : XSstoreStipendChecksPass validJumps s :=
        ⟨hStaticPass, hSstore⟩
      by_cases hCreateBig :
          EvmYul.Operation.isCreate (decodedOperationAt s) = true ∧
            (EvmYul.UInt256.ofNat 49152) <
              s.stack[2]?.getD (EvmYul.UInt256.ofNat 0)
      · have hCreateOp :=
          operation_eq_create_or_create2_of_isCreate hCreateBig.1
        rw [x_create_initcode_outOfGas_after_sstore_check hPrefixS
          hCreateOp hCreateBig.2] at hEq
        cases Except.error.inj hEq
      · have hX :=
          x_after_prechecks_of_step_result (fuel := f)
            (validJumps := validJumps) hPrefixS hCreateBig rfl
        rw [hX] at hEq
        cases hStepRes :
            EvmYul.EVM.step f (dynamicGasCostAt s)
              (some
                ((EvmYul.EVM.decode s.executionEnv.code s.pc).getD
                  (EvmYul.Operation.STOP, none)))
              (afterMemoryChargeAt s) with
        | error err =>
            rw [hStepRes] at hEq
            simp only [xPostStepExceptResult] at hEq
            exact hStepErr s f err hReach hPrefixS hStepRes
              (Except.error.inj hEq)
        | ok nxt =>
            rw [hStepRes] at hEq
            simp only [xPostStepExceptResult] at hEq
            cases hHalt : haltOutputAt nxt (decodedOperationAt s) with
            | none =>
                have hRun :
                    xPostStepResult f validJumps (decodedOperationAt s)
                        nxt =
                      EvmYul.EVM.X f validJumps nxt := by
                  unfold xPostStepResult
                  rw [hHalt]
                rw [hRun] at hEq
                exact ih nxt
                  (FrameReachable.next hReach hPrefixS hStepRes hHalt) hEq
            | some output =>
                have hOk :
                    ∃ result,
                      xPostStepResult f validJumps (decodedOperationAt s)
                          nxt =
                        .ok result := by
                  unfold xPostStepResult
                  simp only [hHalt]
                  split
                  · exact ⟨_, rfl⟩
                  · exact ⟨_, rfl⟩
                obtain ⟨result, hOk⟩ := hOk
                rw [hOk] at hEq
                cases hEq

/-- Crown composition at the compact-artifact level: on certified code
entered at pc `0` with an empty stack, the gasful frame interpreter can
never return `StackOverflow`. -/
theorem x_ne_stackOverflow_of_cert
    {source : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Compact.Artifact} {bytes : ByteArray} {cert : Cert}
    {validJumps : Array Word} {initial : EVMState}
    (hCompile : Compact.compile? source pinnedPushPcs = some artifact)
    (hDecode : Compact.DecodingCorrect artifact.program bytes)
    (hCheck : check? artifact cert = true)
    (hSentinel : Compact.decodeAt bytes
      (Compact.Program.codeByteLength artifact.program.code)
      (.prim .invalid))
    (hFrame : ArtifactFrameInvariant artifact bytes validJumps initial)
    (hPc : initial.pc = EvmYul.UInt256.ofNat 0)
    (hStack : initial.stack = []) :
    ∀ fuel, EvmYul.EVM.X fuel validJumps initial ≠
      .error EvmYul.EVM.ExecutionException.StackOverflow := by
  intro fuel
  have hInitialHeight := heightPoint_initial hCheck hPc hStack
  exact x_ne_stackOverflow_of_invariants
    (reach_noOverflow hCompile hDecode hCheck hSentinel hFrame
      hInitialHeight)
    (fun s stepFuel err hReach hPrefix hStep =>
      step_error_ne_stackOverflow_at hCompile hDecode hSentinel
        (hFrame s hReach) hPrefix hStep)
    fuel initial .initial

/-! ## Escape-free refinement view -/

/-- `RunRefinesOpen` with the `stackOverflow` escape constructor removed. -/
inductive RunRefinesOpenNoStackOverflow
    (gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState))
    (openRun : Simulation.Interaction EVMException StepResult) :
    Simulation.Interaction.Transcript → Prop where
  | completed {transcript openDone} :
      Simulation.Interaction.Executes openRun transcript openDone →
      DoneRel gasful openDone →
      RunRefinesOpenNoStackOverflow gasful openRun transcript
  | exceptionalFrame {transcript gasErr openErr} :
      gasErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      openErr ≠ EvmYul.EVM.ExecutionException.OutOfFuel →
      gasful = .error gasErr →
      Simulation.Interaction.Executes openRun transcript (.error openErr) →
      RunRefinesOpenNoStackOverflow gasful openRun transcript
  | outOfGas {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.OutOfGass →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoStackOverflow gasful openRun transcript
  | outOfFuel {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.OutOfFuel →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoStackOverflow gasful openRun transcript
  | badJumpDestination {transcript} :
      gasful = .error EvmYul.EVM.ExecutionException.BadJumpDestination →
      Simulation.Interaction.Follows openRun transcript →
      RunRefinesOpenNoStackOverflow gasful openRun transcript

/-- Any refinement witness whose gasful side is known not to be a
`StackOverflow` error loses the escape constructor. -/
theorem runRefinesOpenNoStackOverflow_of_ne
    {gasful : Except EVMException (EvmYul.EVM.ExecutionResult EVMState)}
    {openRun : Simulation.Interaction EVMException StepResult}
    {transcript : Simulation.Interaction.Transcript}
    (hRefines : GasfulBridge.RunRefinesOpen gasful openRun transcript)
    (hNe :
      gasful ≠ .error EvmYul.EVM.ExecutionException.StackOverflow) :
    RunRefinesOpenNoStackOverflow gasful openRun transcript := by
  cases hRefines with
  | completed hExec hDone => exact .completed hExec hDone
  | exceptionalFrame hGasErr hOpenErr hGas hExec =>
      exact .exceptionalFrame hGasErr hOpenErr hGas hExec
  | outOfGas hGas hFollow => exact .outOfGas hGas hFollow
  | outOfFuel hFuel hFollow => exact .outOfFuel hFuel hFollow
  | badJumpDestination hBad hFollow => exact .badJumpDestination hBad hFollow
  | stackOverflow hOverflow hFollow => exact absurd hOverflow hNe

end StackHeadroom
end Assembly
end EvmCompiler
