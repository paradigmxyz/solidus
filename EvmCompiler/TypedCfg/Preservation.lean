import EvmCompiler.TypedCfg.Lower
import Mathlib.Tactic.IntervalCases

namespace EvmCompiler
namespace TypedCfg
namespace Preservation

theorem source_step_at_boundary
    {pre post : Assembly.Program} {instr : Assembly.Instr}
    {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.step (pre ++ instr :: post) state =
      Assembly.Source.stepAt (pre ++ instr :: post)
        pre.byteLength instr state := by
  unfold Assembly.Source.step
  have hAt :
      Assembly.Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post instr 0
  rw [hAt]

theorem source_runN_one_at_boundary
    {pre post : Assembly.Program} {instr : Assembly.Instr}
    {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runN (pre ++ instr :: post) 1 state =
      Assembly.Source.stepAt (pre ++ instr :: post)
        pre.byteLength instr state := by
  unfold Assembly.Source.runN
  rw [source_step_at_boundary hFits hPc]
  cases hStep :
      Assembly.Source.stepAt (pre ++ instr :: post)
        pre.byteLength instr state <;>
    simp only [Bind.bind, Except.bind, Assembly.Source.runN]

theorem source_stepResult_at_boundary
    {pre post : Assembly.Program} {instr : Assembly.Instr}
    {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.stepResult (pre ++ instr :: post) state =
      Assembly.Source.stepAtResult (pre ++ instr :: post)
        pre.byteLength instr state := by
  unfold Assembly.Source.stepResult
  have hAt :
      Assembly.Program.instrAtPc (pre ++ instr :: post) state.pc.toNat =
        some (pre.byteLength, instr) := by
    unfold Assembly.Program.instrAtPc
    rw [hPc, hFits]
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post instr 0
  rw [hAt]

theorem source_runNResult_one_at_boundary
    {pre post : Assembly.Program} {instr : Assembly.Instr}
    {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runNResult (pre ++ instr :: post) 1 state =
      Assembly.Source.stepAtResult (pre ++ instr :: post)
        pre.byteLength instr state := by
  unfold Assembly.Source.runNResult
  rw [source_stepResult_at_boundary hFits hPc]
  cases hStep :
      Assembly.Source.stepAtResult (pre ++ instr :: post)
        pre.byteLength instr state with
  | error err =>
      simp only [Bind.bind, Except.bind]
  | ok result =>
      cases result <;>
        simp only [Bind.bind, Except.bind, Assembly.Source.runNResult]

namespace Outcome

/--
Relates a TypedCfg control outcome to an Assembly execution outcome.

TypedCfg deliberately records only that an invalid path was reached, so every
concrete Assembly exception refines that source outcome. Jump outcomes retain
the symbolic target and are related through the assembled program's label map.
-/
def Simulates (program : Assembly.Program) :
    TypedCfg.Outcome → Assembly.Source.ExecutionOutcome → Prop
  | .fallthrough state, outcome =>
      outcome = .ok (.running state)
  | .jump target state, outcome =>
      ∃ dest,
        program.labelPc target = some dest ∧
          outcome =
            .ok (.running (Assembly.Source.jumpPc dest state))
  | .returnDispatch _state, _outcome =>
      False
  | .halt kind state, outcome =>
      outcome =
        Assembly.Target.stepInstrResult
          (.prim kind.toPrimOp) state
  | .invalid _state, outcome =>
      ∃ error, outcome = .error error

end Outcome

namespace Terminator

def Direct : Terminator → Prop
  | .returnDispatch _ _ => False
  | _ => True

def ResolvedTargets
    (program : Assembly.Program) (term : Terminator) : Prop :=
  ∀ target, target ∈ term.targets →
    ∃ dest, program.labelPc target = some dest

end Terminator

theorem uint256_add_zero (value : EvmYul.UInt256) :
    value + EvmYul.UInt256.ofNat 0 = value := by
  cases value with
  | mk value =>
      change
        EvmYul.UInt256.mk (value + 0) =
          EvmYul.UInt256.mk value
      exact congrArg EvmYul.UInt256.mk (add_zero value)

theorem uint256_add_assoc
    (left middle right : EvmYul.UInt256) :
    (left + middle) + right = left + (middle + right) := by
  cases left with
  | mk left =>
      cases middle with
      | mk middle =>
          cases right with
          | mk right =>
              change
                EvmYul.UInt256.mk ((left + middle) + right) =
                  EvmYul.UInt256.mk (left + (middle + right))
              exact
                congrArg EvmYul.UInt256.mk
                  (add_assoc left middle right)

theorem uint256_bne_zero_of_ne
    (value : EvmYul.UInt256)
    (hNe : value ≠ EvmYul.UInt256.ofNat 0) :
    (value != EvmYul.UInt256.ofNat 0) = true := by
  cases value with
  | mk value =>
      simp [bne, EvmYul.instBEqUInt256,
        EvmYul.instBEqUInt256.beq,
        EvmYul.UInt256.ofNat, Id.run] at hNe ⊢
      exact hNe

theorem uint256_bne_zero_self :
    (EvmYul.UInt256.ofNat 0 !=
      EvmYul.UInt256.ofNat 0) = false := by
  simp [bne, EvmYul.instBEqUInt256,
    EvmYul.instBEqUInt256.beq,
    EvmYul.UInt256.ofNat, Id.run]

theorem primStep_run_pc {step : Assembly.PrimStep}
    {state final : EVMState}
    (hRun : step.run state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases step <;>
    simp [Assembly.PrimStep.run, EvmYul.EVM.execBinOp,
      EvmYul.EVM.execUnOp, EvmYul.EVM.execTriOp,
      EvmYul.EVM.executionEnvOp, EvmYul.EVM.unaryExecutionEnvOp,
      EvmYul.EVM.machineStateOp, EvmYul.EVM.binaryMachineStateOp,
      EvmYul.EVM.binaryMachineStateOp',
      EvmYul.EVM.ternaryMachineStateOp, EvmYul.EVM.stateOp,
      EvmYul.EVM.unaryStateOp, EvmYul.EVM.binaryStateOp,
      EvmYul.EVM.ternaryCopyOp, EvmYul.EVM.quaternaryCopyOp,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hRun ⊢
  all_goals
    try
      cases hRun
      rfl
  all_goals
    try
      simp [EvmYul.dup, EvmYul.swap,
        EvmYul.EVM.State.replaceStackAndIncrPC,
        EvmYul.EVM.State.incrPC] at hRun
    repeat' split at hRun
  all_goals
    try simp_all
  all_goals
    cases hRun
    rfl

theorem primOp_step_pc_of_stackArity
    {op : Assembly.PrimOp} {input output : Nat}
    {state final : EVMState}
    (hArity : op.stackArity? = some (input, output))
    (hRun : op.step state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases hCont : op.continuingStep? with
  | some step =>
      rw [Assembly.PrimOp.step_eq_continuingStep_run hCont] at hRun
      exact primStep_run_pc hRun
  | none =>
      cases op <;>
        simp [Assembly.PrimOp.continuingStep?] at hCont
      case stop | «return» | revert | selfdestruct =>
        simp [Assembly.PrimOp.stackArity?] at hArity
      case pc =>
        change
          Except.ok
              (state.replaceStackAndIncrPC
                (state.stack.push state.pc)) =
            Except.ok final at hRun
        cases hRun
        rfl
      case gas =>
        change
          Except.ok
              (state.replaceStackAndIncrPC
                (state.stack.push state.gasAvailable)) =
            Except.ok final at hRun
        cases hRun
        rfl
      case create | call | callcode | delegatecall | create2 | staticcall =>
        change
          (Except.error EvmYul.EVM.ExecutionException.InvalidInstruction :
            Except EvmYul.EVM.ExecutionException EvmYul.EVM.State) =
            Except.ok final at hRun
        cases hRun

theorem pop_step_pc {state final : EVMState}
    (hStep : Assembly.PrimOp.pop.step state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
  cases state with
  | mk shared pc stack execLength =>
      cases stack with
      | nil =>
          simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
            Assembly.PrimStep.run, EvmYul.Stack.pop] at hStep
      | cons top rest =>
          simp [Assembly.PrimOp.step, Assembly.PrimOp.continuingStep?,
            Assembly.PrimStep.run, EvmYul.Stack.pop,
            EvmYul.EVM.State.replaceStackAndIncrPC,
            EvmYul.EVM.State.incrPC] at hStep
          cases hStep
          rfl

theorem runPops_pc
    (count : Nat) {state final : EVMState}
    (hRun : Instr.runPops count state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat count := by
  induction count generalizing state with
  | zero =>
      simp [Instr.runPops] at hRun
      cases hRun
      exact uint256_add_zero final.pc |>.symm
  | succ count ih =>
      unfold Instr.runPops at hRun
      cases hStep : Assembly.PrimOp.pop.step state with
      | error err =>
          simp only [hStep, Bind.bind, Except.bind] at hRun
          cases hRun
      | ok mid =>
          simp only [hStep, Bind.bind, Except.bind] at hRun
          calc
            final.pc =
                mid.pc + EvmYul.UInt256.ofNat count :=
              ih hRun
            _ =
                (state.pc + EvmYul.UInt256.ofNat 1) +
                  EvmYul.UInt256.ofNat count := by
              rw [pop_step_pc hStep]
            _ =
                state.pc +
                  (EvmYul.UInt256.ofNat 1 +
                    EvmYul.UInt256.ofNat count) := by
              exact uint256_add_assoc _ _ _
            _ =
                state.pc + EvmYul.UInt256.ofNat (count + 1) := by
              rw [Assembly.UInt256_ofNat_add]
              congr 2
              omega

theorem runPops_source_runN
    (count : Nat) {pre post : Assembly.Program} {state : EVMState}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (List.replicate count (.prim .pop)))
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runN
        (pre ++ List.replicate count (.prim .pop) ++ post)
        count state =
      Instr.runPops count state := by
  induction count generalizing pre state with
  | zero =>
      rfl
  | succ count ih =>
      rcases hFits with ⟨hFitsHere, hFitsRest⟩
      rw [List.replicate_succ]
      simp only [List.append_assoc]
      change
        Assembly.Source.runN
            (pre ++ Assembly.Instr.prim Assembly.PrimOp.pop ::
              (List.replicate count
                (Assembly.Instr.prim Assembly.PrimOp.pop) ++ post))
            (count + 1) state =
          Instr.runPops (count + 1) state
      unfold Assembly.Source.runN Instr.runPops
      rw [source_step_at_boundary hFitsHere hPc]
      change
        (do
          let state' ← Assembly.PrimOp.pop.step state
          Assembly.Source.runN
            (pre ++ .prim .pop ::
              (List.replicate count (.prim .pop) ++ post))
            count state') =
          (do
            let state' ← Assembly.PrimOp.pop.step state
            Instr.runPops count state')
      cases hStep : Assembly.PrimOp.pop.step state with
      | error err =>
          simp only [Bind.bind, Except.bind]
      | ok state' =>
          simp only [Bind.bind, Except.bind]
          have hPc' :
              state'.pc =
                (pre ++ [Assembly.Instr.prim Assembly.PrimOp.pop]).pcAfter := by
            calc
              state'.pc =
                  state.pc + EvmYul.UInt256.ofNat 1 :=
                    pop_step_pc hStep
              _ = pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
                    rw [hPc]
              _ =
                  (pre ++
                    [Assembly.Instr.prim Assembly.PrimOp.pop]).pcAfter := by
                    simpa [Assembly.Instr.byteSize] using
                      (Assembly.Program.pcAfter_snoc pre
                        (Assembly.Instr.prim Assembly.PrimOp.pop)).symm
          have hTail :=
            ih (pre := pre ++ [Assembly.Instr.prim .pop]) (state := state')
              hFitsRest hPc'
          simpa [List.append_assoc] using hTail

namespace Instr

theorem byteLength_replicate_pop (count : Nat) :
    Assembly.Program.byteLength
        (List.replicate count (.prim .pop)) =
      count := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      rw [List.replicate_succ]
      simp [Assembly.Program.byteLength, Assembly.Instr.byteSize, ih]
      omega

theorem type?_eq_some_of_lowerAt?
    {instr : Instr} {shape output : Shape}
    {code : Assembly.Program}
    (hLower : instr.lowerAt? shape = some (code, output)) :
    instr.type? shape = some output := by
  unfold TypedCfg.Instr.lowerAt? at hLower
  cases hType : instr.type? shape with
  | none =>
      simp [hType] at hLower
  | some typedOutput =>
      rw [hType] at hLower
      cases instr <;>
        simp [TypedCfg.Instr.lower?] at hLower
      all_goals
        repeat' split at hLower
        all_goals simp_all

theorem runState_pc_of_lowerAt
    {instr : Instr} {shape output : Shape}
    {code : Assembly.Program} {state final : EVMState}
    (hLower : instr.lowerAt? shape = some (code, output))
    (hRun : instr.runState shape state = .ok final) :
    final.pc =
      state.pc + EvmYul.UInt256.ofNat code.byteLength := by
  cases hType : instr.type? shape with
  | none =>
      simp [TypedCfg.Instr.lowerAt?, hType] at hLower
  | some typedOutput =>
      cases instr with
      | push value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [TypedCfg.Instr.runState] at hRun
          cases hRun
          rfl
      | returnToken value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [TypedCfg.Instr.runState] at hRun
          cases hRun
          rfl
      | prim op =>
          cases hArity : op.stackArity? with
          | none =>
              simp [TypedCfg.Instr.type?, hArity] at hType
          | some arity =>
              rcases arity with ⟨input, outputArity⟩
              simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
                at hLower
              rcases hLower with ⟨rfl, rfl⟩
              simpa [TypedCfg.Instr.runState,
                Assembly.Program.byteLength, Assembly.Instr.byteSize] using
                  primOp_step_pc_of_stackArity hArity hRun
      | pop =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simpa [TypedCfg.Instr.runState,
            Assembly.Program.byteLength, Assembly.Instr.byteSize] using
              pop_step_pc hRun
      | dup depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower
          all_goals
            rcases hLower with ⟨rfl, rfl⟩
            simp [TypedCfg.Instr.runState] at hRun
            simpa [TypedCfg.Instr.runState,
              Assembly.Program.byteLength, Assembly.Instr.byteSize] using
                primOp_step_pc_of_stackArity (by rfl) hRun
      | swap depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower
          all_goals
            rcases hLower with ⟨rfl, rfl⟩
            simp [TypedCfg.Instr.runState] at hRun
            simpa [TypedCfg.Instr.runState,
              Assembly.Program.byteLength, Assembly.Instr.byteSize] using
                primOp_step_pc_of_stackArity (by rfl) hRun
      | unwind target =>
          simp [TypedCfg.Instr.lowerAt?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simpa [TypedCfg.Instr.runState,
            byteLength_replicate_pop] using
              runPops_pc (shape.length - target.length) hRun

theorem runAt_map_fst
    {instr : TypedCfg.Instr} {shape output : Shape}
    {state : EVMState}
    (hType : instr.type? shape = some output) :
    (instr.runAt shape state).map Prod.fst =
      instr.runState shape state := by
  unfold TypedCfg.Instr.runAt
  rw [hType]
  cases hRun : instr.runState shape state with
  | error err =>
      simp only [hRun, Bind.bind, Except.bind]
      change Except.error err = Except.error err
      rfl
  | ok final =>
      simp only [hRun, Bind.bind, Except.bind]
      change Except.ok final = Except.ok final
      rfl

theorem lowerAt_source_runN
    {instr : Instr} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower : instr.lowerAt? shape = some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runN (pre ++ code ++ post) code.length state =
      (instr.runAt shape state).map Prod.fst := by
  cases hType : instr.type? shape with
  | none =>
      simp [TypedCfg.Instr.lowerAt?, hType] at hLower
  | some typedOutput =>
      rw [runAt_map_fst hType]
      cases instr with
      | push value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          change
            Assembly.Source.runN
                (pre ++ Assembly.Instr.push value :: post) 1 state =
              _
          rw [source_runN_one_at_boundary hFits.1 hPc]
          simp [TypedCfg.Instr.runState, Assembly.Source.stepAt,
            Assembly.Target.stepInstr]
      | returnToken value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          change
            Assembly.Source.runN
                (pre ++ Assembly.Instr.push value :: post) 1 state =
              _
          rw [source_runN_one_at_boundary hFits.1 hPc]
          simp [TypedCfg.Instr.runState, Assembly.Source.stepAt,
            Assembly.Target.stepInstr]
      | prim op =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          change
            Assembly.Source.runN
                (pre ++ Assembly.Instr.prim op :: post) 1 state =
              _
          rw [source_runN_one_at_boundary hFits.1 hPc]
          simp [TypedCfg.Instr.runState, Assembly.Source.stepAt,
            Assembly.Target.stepInstr]
      | pop =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          change
            Assembly.Source.runN
                (pre ++ Assembly.Instr.prim .pop :: post) 1 state =
              _
          rw [source_runN_one_at_boundary hFits.1 hPc]
          simp [TypedCfg.Instr.runState, Assembly.Source.stepAt,
            Assembly.Target.stepInstr]
      | dup depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower
          all_goals
            rcases hLower with ⟨rfl, rfl⟩
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc]
            change
              Assembly.Source.runN
                  (pre ++ Assembly.Instr.prim _ :: post) 1 state =
                _
            rw [source_runN_one_at_boundary hFits.1 hPc]
            simp [TypedCfg.Instr.runState, Assembly.Source.stepAt,
              Assembly.Target.stepInstr]
      | swap depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower
          all_goals
            rcases hLower with ⟨rfl, rfl⟩
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc]
            change
              Assembly.Source.runN
                  (pre ++ Assembly.Instr.prim _ :: post) 1 state =
                _
            rw [source_runN_one_at_boundary hFits.1 hPc]
            simp [TypedCfg.Instr.runState, Assembly.Source.stepAt,
              Assembly.Target.stepInstr]
      | unwind target =>
          simp [TypedCfg.Instr.lowerAt?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simpa [TypedCfg.Instr.runState, List.append_assoc] using
            runPops_source_runN (shape.length - target.length)
              (post := post) hFits hPc

end Instr

namespace Terminator

theorem lowerAt?_eventually_of_direct
    {shape : Shape} {term : TypedCfg.Terminator}
    {code pre post : Assembly.Program} {state : EVMState}
    (hDirect : Preservation.Terminator.Direct term)
    (hLower : term.lowerAt? shape = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedTargets
        (pre ++ code ++ post) term) :
    Assembly.Source.Eventually (pre ++ code ++ post) state
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape term state)) := by
  cases term with
  | fallthrough next =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved next (by simp [TypedCfg.Terminator.targets]) with
        ⟨dest, hDest⟩
      have hDest' :
          (pre ++ Assembly.Instr.jump next :: post).labelPc next =
            some dest := by
        simpa using hDest
      refine
        ⟨1, .ok (.running (Assembly.Source.jumpPc dest state)), ?_, ?_⟩
      · rw [show
          pre ++ [Assembly.Instr.jump next] ++ post =
            pre ++ Assembly.Instr.jump next :: post by
          simp]
        rw [source_runNResult_one_at_boundary hFits.1 hPc]
        simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
          Assembly.Instr.haltKind?, hDest', Assembly.Source.invalid]
      · exact ⟨dest, hDest, rfl⟩
  | jump target =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved target (by simp [TypedCfg.Terminator.targets]) with
        ⟨dest, hDest⟩
      have hDest' :
          (pre ++ Assembly.Instr.jump target :: post).labelPc target =
            some dest := by
        simpa using hDest
      refine
        ⟨1, .ok (.running (Assembly.Source.jumpPc dest state)), ?_, ?_⟩
      · rw [show
          pre ++ [Assembly.Instr.jump target] ++ post =
            pre ++ Assembly.Instr.jump target :: post by
          simp]
        rw [source_runNResult_one_at_boundary hFits.1 hPc]
        simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
          Assembly.Instr.haltKind?, hDest', Assembly.Source.invalid]
      · exact ⟨dest, hDest, rfl⟩
  | jumpi target next =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved target (by simp [TypedCfg.Terminator.targets]) with
        ⟨targetDest, hTargetDest⟩
      rcases hResolved next (by simp [TypedCfg.Terminator.targets]) with
        ⟨nextDest, hNextDest⟩
      have hTargetDest' :
          (pre ++ Assembly.Instr.jumpi target ::
              Assembly.Instr.jump next :: post).labelPc target =
            some targetDest := by
        simpa using hTargetDest
      have hNextDest' :
          (pre ++ Assembly.Instr.jumpi target ::
              Assembly.Instr.jump next :: post).labelPc next =
            some nextDest := by
        simpa using hNextDest
      cases hPop : state.stack.pop with
      | none =>
          refine ⟨1, .error .StackUnderflow, ?_, ?_⟩
          · rw [show
              pre ++
                    [Assembly.Instr.jumpi target,
                      Assembly.Instr.jump next] ++
                    post =
                  pre ++ Assembly.Instr.jumpi target ::
                    Assembly.Instr.jump next :: post by
                simp]
            rw [source_runNResult_one_at_boundary hFits.1 hPc]
            simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
              Assembly.Instr.haltKind?, hTargetDest', hPop,
              Assembly.Source.invalid]
            rfl
          · simp [Block.runTerm, hPop, Outcome.Simulates]
      | some popResult =>
          rcases popResult with ⟨stack, cond⟩
          let popped : EVMState := { state with stack := stack }
          by_cases hZero : cond = EvmYul.UInt256.ofNat 0
          · subst cond
            let mid : EVMState :=
              { popped with
                pc := Assembly.Source.jumpiFallthroughPc state }
            have hMidPc :
                mid.pc =
                  (pre ++ [Assembly.Instr.jumpi target]).pcAfter := by
              calc
                mid.pc =
                    (state.pc +
                      EvmYul.UInt256.ofNat Assembly.Instr.push32Size) +
                        EvmYul.UInt256.ofNat 1 := rfl
                _ =
                    (pre.pcAfter +
                      EvmYul.UInt256.ofNat Assembly.Instr.push32Size) +
                        EvmYul.UInt256.ofNat 1 := by
                      rw [hPc]
                _ =
                    pre.pcAfter +
                      (EvmYul.UInt256.ofNat Assembly.Instr.push32Size +
                        EvmYul.UInt256.ofNat 1) := by
                      exact uint256_add_assoc _ _ _
                _ =
                    pre.pcAfter +
                      EvmYul.UInt256.ofNat
                        (Assembly.Instr.push32Size + 1) := by
                      rw [Assembly.UInt256_ofNat_add]
                _ =
                    (pre ++ [Assembly.Instr.jumpi target]).pcAfter := by
                      simpa [Assembly.Instr.byteSize,
                        Assembly.Instr.jumpSize] using
                          (Assembly.Program.pcAfter_snoc pre
                            (Assembly.Instr.jumpi target)).symm
            have hFirst :
                Assembly.Source.runNResult
                    (pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++
                      post)
                    1 state =
                  .ok (.running mid) := by
              rw [show
                  pre ++
                        [Assembly.Instr.jumpi target,
                          Assembly.Instr.jump next] ++
                        post =
                      pre ++ Assembly.Instr.jumpi target ::
                        Assembly.Instr.jump next :: post by
                    simp]
              rw [source_runNResult_one_at_boundary hFits.1 hPc]
              simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
                Assembly.Instr.haltKind?, hTargetDest', hPop,
                Assembly.Source.invalid, mid, popped,
                uint256_bne_zero_self]
            have hSecond :
                Assembly.Source.runNResult
                    (pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++
                      post)
                    1 mid =
                  .ok
                    (.running
                      (Assembly.Source.jumpPc nextDest popped)) := by
              rw [show
                  pre ++
                        [Assembly.Instr.jumpi target,
                          Assembly.Instr.jump next] ++
                        post =
                      (pre ++ [Assembly.Instr.jumpi target]) ++
                        Assembly.Instr.jump next :: post by
                    simp]
              rw [source_runNResult_one_at_boundary hFits.2.1 hMidPc]
              simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
                Assembly.Instr.haltKind?, hNextDest',
                Assembly.Source.invalid, mid, popped,
                Assembly.Source.jumpPc]
            refine
              ⟨2,
                .ok
                  (.running
                    (Assembly.Source.jumpPc nextDest popped)),
                ?_, ?_⟩
            · calc
                Assembly.Source.runNResult
                    (pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++
                      post)
                    2 state =
                    Assembly.Source.runNResult
                      (pre ++
                        [Assembly.Instr.jumpi target,
                          Assembly.Instr.jump next] ++
                        post)
                      (1 + 1) state := by rfl
                _ =
                    Assembly.Source.runNResult
                      (pre ++
                        [Assembly.Instr.jumpi target,
                          Assembly.Instr.jump next] ++
                        post)
                      1 mid :=
                    Assembly.Source.runNResult_add_of_running
                      _ 1 1 hFirst
                _ =
                    .ok
                      (.running
                        (Assembly.Source.jumpPc nextDest popped)) :=
                    hSecond
            · simp [Block.runTerm, hPop, popped, Outcome.Simulates]
              exact ⟨nextDest, hNextDest', rfl⟩
          · have hBne :
                (cond != EvmYul.UInt256.ofNat 0) = true :=
              uint256_bne_zero_of_ne cond hZero
            refine
              ⟨1,
                .ok
                  (.running
                    (Assembly.Source.jumpPc targetDest popped)),
                ?_, ?_⟩
            · rw [show
                pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++
                      post =
                    pre ++ Assembly.Instr.jumpi target ::
                      Assembly.Instr.jump next :: post by
                  simp]
              rw [source_runNResult_one_at_boundary hFits.1 hPc]
              simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
                Assembly.Instr.haltKind?, hTargetDest', hPop, hBne,
                Assembly.Source.invalid, popped,
                Assembly.Source.jumpPc]
            · simp [Block.runTerm, hPop, hZero, popped,
                Outcome.Simulates]
              exact ⟨targetDest, hTargetDest', rfl⟩
  | returnDispatch _returnCount _sites =>
      simp [Preservation.Terminator.Direct] at hDirect
  | halt kind =>
      cases kind with
      | stop =>
        simp [TypedCfg.Terminator.lowerAt?] at hLower
        subst code
        refine
          ⟨1,
            Assembly.Target.stepInstrResult
              (.prim .stop) state,
            ?_, rfl⟩
        rw [show
          pre ++ [Assembly.Instr.prim .stop] ++ post =
            pre ++ Assembly.Instr.prim .stop :: post by
          simp]
        rw [source_runNResult_one_at_boundary hFits.1 hPc]
        rfl
      | «return» =>
        simp [TypedCfg.Terminator.lowerAt?] at hLower
        subst code
        refine
          ⟨1,
            Assembly.Target.stepInstrResult
              (.prim .return) state,
            ?_, rfl⟩
        rw [show
          pre ++ [Assembly.Instr.prim .return] ++ post =
            pre ++ Assembly.Instr.prim .return :: post by
          simp]
        rw [source_runNResult_one_at_boundary hFits.1 hPc]
        rfl
      | revert =>
        simp [TypedCfg.Terminator.lowerAt?] at hLower
        subst code
        refine
          ⟨1,
            Assembly.Target.stepInstrResult
              (.prim .revert) state,
            ?_, rfl⟩
        rw [show
          pre ++ [Assembly.Instr.prim .revert] ++ post =
            pre ++ Assembly.Instr.prim .revert :: post by
          simp]
        rw [source_runNResult_one_at_boundary hFits.1 hPc]
        rfl
      | selfdestruct =>
        simp [TypedCfg.Terminator.lowerAt?] at hLower
        subst code
        refine
          ⟨1,
            Assembly.Target.stepInstrResult
              (.prim .selfdestruct) state,
            ?_, rfl⟩
        rw [show
          pre ++ [Assembly.Instr.prim .selfdestruct] ++ post =
            pre ++ Assembly.Instr.prim .selfdestruct :: post by
          simp]
        rw [source_runNResult_one_at_boundary hFits.1 hPc]
        rfl
  | invalid =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      refine ⟨1, .error .InvalidInstruction, ?_, ?_⟩
      · rw [show
          pre ++ [Assembly.Instr.prim .invalid] ++ post =
            pre ++ Assembly.Instr.prim .invalid :: post by
          simp]
        rw [source_runNResult_one_at_boundary hFits.1 hPc]
        simp only [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
          Assembly.Target.stepInstr]
        rw [Assembly.PrimOp.step_eq_continuingStep_run (by rfl)]
        rfl
      · exact ⟨.InvalidInstruction, rfl⟩

end Terminator

namespace Block

theorem lowerBodyFrom?_source_runN
    {body : List Instr} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower : TypedCfg.Block.lowerBodyFrom? body shape = some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runN (pre ++ code ++ post) code.length state =
      (TypedCfg.Block.runBody body shape state).map Prod.fst := by
  induction body generalizing shape code output pre state with
  | nil =>
      simp [TypedCfg.Block.lowerBodyFrom?] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      rfl
  | cons instr rest ih =>
      unfold TypedCfg.Block.lowerBodyFrom? at hLower
      cases hHead : instr.lowerAt? shape with
      | none =>
          simp [hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, headOutput⟩
          cases hTail :
              TypedCfg.Block.lowerBodyFrom? rest headOutput with
          | none =>
              simp [hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailOutput⟩
              simp [hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hType :
                  instr.type? shape = some headOutput :=
                Instr.type?_eq_some_of_lowerAt? hHead
              have hHeadFits :
                  Assembly.Program.PCFitsFrom pre head :=
                Assembly.Program.PCFitsFrom.left hFits
              have hTailFits :
                  Assembly.Program.PCFitsFrom (pre ++ head) tail :=
                Assembly.Program.PCFitsFrom.right hFits
              have hHeadRun :=
                Instr.lowerAt_source_runN
                  (post := tail ++ post) hHead hHeadFits hPc
              rw [Instr.runAt_map_fst hType] at hHeadRun
              rw [List.length_append, Assembly.Source.runN_add]
              cases hRunState : instr.runState shape state with
              | error err =>
                  rw [show
                    Assembly.Source.runN
                        (pre ++ (head ++ tail) ++ post)
                        head.length state =
                      instr.runState shape state by
                    simpa [List.append_assoc] using hHeadRun]
                  rw [hRunState]
                  simp only [Bind.bind, Except.bind]
                  unfold TypedCfg.Block.runBody TypedCfg.Instr.runAt
                  rw [hType, hRunState]
                  rfl
              | ok mid =>
                  have hMidPc :
                      mid.pc = (pre ++ head).pcAfter := by
                    calc
                      mid.pc =
                          state.pc +
                            EvmYul.UInt256.ofNat head.byteLength :=
                        Instr.runState_pc_of_lowerAt hHead hRunState
                      _ =
                          pre.pcAfter +
                            EvmYul.UInt256.ofNat head.byteLength := by
                        rw [hPc]
                      _ = (pre ++ head).pcAfter := by
                        exact
                          (Assembly.Program.pcAfter_append pre head).symm
                  have hTailRun :=
                    ih (shape := headOutput) (pre := pre ++ head)
                      (state := mid) hTail hTailFits hMidPc
                  rw [show
                    Assembly.Source.runN
                        (pre ++ (head ++ tail) ++ post)
                        head.length state =
                      instr.runState shape state by
                    simpa [List.append_assoc] using hHeadRun]
                  simp only [hRunState, Bind.bind, Except.bind]
                  simpa [List.append_assoc, TypedCfg.Block.runBody,
                    TypedCfg.Instr.runAt, hType, hRunState] using hTailRun

end Block

end Preservation
end TypedCfg
end EvmCompiler
