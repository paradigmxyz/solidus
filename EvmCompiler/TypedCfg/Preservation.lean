import EvmCompiler.TypedCfg.Lower
import EvmCompiler.Assembly.StackShufflePreservation
import EvmCompiler.Assembly.Accepted
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
  unfold Assembly.Source.step Assembly.Source.stepWith
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
  unfold Assembly.Source.runN Assembly.Control.runNWith
  rw [source_step_at_boundary hFits hPc]
  cases hStep :
      Assembly.Source.stepAt (pre ++ instr :: post)
        pre.byteLength instr state <;>
    simp only [Bind.bind, Except.bind, Assembly.Source.runN,
      Assembly.Control.runNWith, Assembly.pure_except]

theorem source_stepResult_at_boundary
    {pre post : Assembly.Program} {instr : Assembly.Instr}
    {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.stepResult (pre ++ instr :: post) state =
      Assembly.Source.stepAtResult (pre ++ instr :: post)
        pre.byteLength instr state := by
  unfold Assembly.Source.stepResult Assembly.Source.stepResultWith
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
  unfold Assembly.Source.runNResult Assembly.Control.runNResultWith
  rw [source_stepResult_at_boundary hFits hPc]
  cases hStep :
      Assembly.Source.stepAtResult (pre ++ instr :: post)
        pre.byteLength instr state with
  | error err =>
      simp only [Bind.bind, Except.bind]
  | ok result =>
      cases result <;>
        simp only [Bind.bind, Except.bind, Assembly.Source.runNResult,
          Assembly.Control.runNResultWith, Assembly.pure_except]

theorem source_runNResult_one_eq_map_running
    {pre post : Assembly.Program} {instr : Assembly.Instr}
    {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hNoHalt : instr.haltKind? = none) :
    Assembly.Source.runNResult (pre ++ instr :: post) 1 state =
      (Assembly.Source.runN (pre ++ instr :: post) 1 state).map
        Assembly.StepResult.running := by
  rw [source_runNResult_one_at_boundary hFits hPc]
  rw [source_runN_one_at_boundary hFits hPc]
  unfold Assembly.Source.stepAtResult
  cases hStep :
      Assembly.Source.stepAt (pre ++ instr :: post)
        pre.byteLength instr state with
  | error err =>
      simp only [Bind.bind, Except.bind, Except.map]
  | ok final =>
      simp only [Bind.bind, Except.bind, Except.map, hNoHalt]

theorem source_runNResult_one_eq_map_running_append
    {pre post : Assembly.Program} {instr : Assembly.Instr}
    {state : EVMState}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hNoHalt : instr.haltKind? = none) :
    Assembly.Source.runNResult (pre ++ ([instr] ++ post)) 1 state =
      (Assembly.Source.runN (pre ++ ([instr] ++ post)) 1 state).map
        Assembly.StepResult.running := by
  simpa [List.append_assoc] using
    source_runNResult_one_eq_map_running
      (pre := pre) (post := post) hFits hPc hNoHalt

namespace Outcome

/-- A running Assembly result with the same observable EVM data. -/
def RunningData (source : EVMState) :
    Assembly.Source.ExecutionOutcome → Prop
  | .ok (.running target) => Assembly.SameRuntimeData target source
  | _ => False

/--
A running Assembly result at the resolved target PC with the same observable
EVM data. Internal lowering instructions may have changed control counters.
-/
def RunningAt (pc : Nat) (source : EVMState) :
    Assembly.Source.ExecutionOutcome → Prop
  | .ok (.running target) =>
      target.pc = EvmYul.UInt256.ofNat pc ∧
        Assembly.SameRuntimeData target source
  | _ => False

/--
Relates a TypedCfg control outcome to an Assembly execution outcome.

TypedCfg deliberately records only that an invalid path was reached, so every
concrete Assembly exception refines that source outcome. Jump outcomes retain
the symbolic target and are related through the assembled program's label map.
-/
def Simulates (program : Assembly.Program) :
    TypedCfg.Outcome → Assembly.Source.ExecutionOutcome → Prop
  | .fallthrough state, outcome =>
      RunningData state outcome
  | .jump target state, outcome =>
      ∃ dest,
        program.labelPc target = some dest ∧
          RunningAt dest state outcome
  | .returnDispatch state, outcome =>
      RunningData state outcome
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

def ResolvedCaseLabels
    (program : Assembly.Program) (sites : List ReturnSite) : Prop :=
  ∀ site, site ∈ sites →
    ∃ dest, program.labelPc site.caseLabel = some dest

def ResolvedControl
    (program : Assembly.Program) (term : Terminator) : Prop :=
  ResolvedTargets program term ∧
    ∀ label, label ∈ term.definedLabels →
      ∃ dest, program.labelPc label = some dest

end Terminator

theorem ReturnSite.findTarget?_eq_some_split
    {sites : List ReturnSite} {token : Word} {target : Label}
    (hFind : Block.ReturnSite.findTarget? token sites = some target) :
    ∃ before site after,
      sites = before ++ site :: after ∧
        (∀ prior, prior ∈ before → prior.token ≠ token) ∧
        site.token = token ∧ site.target = target := by
  induction sites with
  | nil =>
      simp [Block.ReturnSite.findTarget?] at hFind
  | cons head rest ih =>
      by_cases hHead : head.token = token
      · simp [Block.ReturnSite.findTarget?, hHead] at hFind
        exact ⟨[], head, rest, by simp, by simp, hHead, hFind⟩
      · simp [Block.ReturnSite.findTarget?, hHead] at hFind
        rcases ih hFind with
          ⟨before, site, after, hSites, hBefore, hToken, hTarget⟩
        refine
          ⟨head :: before, site, after, ?_, ?_, hToken, hTarget⟩
        · simp [hSites]
        · intro prior hPrior
          simp only [List.mem_cons] at hPrior
          cases hPrior with
          | inl hEq =>
              subst prior
              exact hHead
          | inr hMem =>
              exact hBefore prior hMem

theorem ReturnSite.findTarget?_eq_none_all_ne
    {sites : List ReturnSite} {token : Word}
    (hFind : Block.ReturnSite.findTarget? token sites = none) :
    ∀ site, site ∈ sites → site.token ≠ token := by
  induction sites with
  | nil =>
      simp
  | cons head rest ih =>
      by_cases hHead : head.token = token
      · simp [Block.ReturnSite.findTarget?, hHead] at hFind
      · simp [Block.ReturnSite.findTarget?, hHead] at hFind
        intro site hMem
        simp only [List.mem_cons] at hMem
        cases hMem with
        | inl hEq =>
            subst site
            exact hHead
        | inr hRest =>
            exact ih hFind site hRest

theorem List.getElem?_eq_some_split
    {α : Type} {xs : List α} {index : Nat} {value : α}
    (hGet : xs[index]? = some value) :
    ∃ front suffix,
      xs = front ++ value :: suffix ∧ front.length = index := by
  induction xs generalizing index with
  | nil =>
      simp at hGet
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at hGet
          subst head
          exact ⟨[], tail, by simp⟩
      | succ index =>
          simp at hGet
          rcases ih hGet with ⟨front, suffix, hEq, hLen⟩
          exact ⟨head :: front, suffix, by simp [hEq], by simp [hLen]⟩

theorem List.eraseIdx_append_at_length
    {α : Type} (front suffix : List α) (value : α) :
    (front ++ value :: suffix).eraseIdx front.length =
      front ++ suffix := by
  rw [List.eraseIdx_eq_take_drop_succ]
  simp

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
    (left + middle) + right = left + (middle + right) :=
  Assembly.UInt256_add_assoc left middle right

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
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 :=
  Assembly.PrimStep.run_pc hRun

theorem primOp_step_pc_of_stackArity
    {op : Assembly.PrimOp} {input output : Nat}
    {state final : EVMState}
    (hArity : op.stackArity? = some (input, output))
    (hRun : op.step state = .ok final) :
    final.pc = state.pc + EvmYul.UInt256.ofNat 1 :=
  Assembly.PrimOp.step_pc_of_stackArity hArity hRun

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

/--
Successful repeated popping consumes exactly the requested concrete stack
prefix.
-/
theorem runPops_stack_length
    (count : Nat) {state final : EVMState}
    (hRun : Instr.runPops count state = .ok final) :
    count ≤ state.stack.length ∧
      final.stack.length = state.stack.length - count := by
  induction count generalizing state with
  | zero =>
      simp [Instr.runPops] at hRun
      cases hRun
      simp
  | succ count ih =>
      unfold Instr.runPops at hRun
      cases hStep : Assembly.PrimOp.pop.step state with
      | error err =>
          simp [hStep, Bind.bind, Except.bind] at hRun
      | ok middle =>
          simp [hStep, Bind.bind, Except.bind] at hRun
          rcases ih hRun with ⟨hTailBound, hTailLength⟩
          have hHeadLength :
              middle.stack.length = state.stack.length - 1 :=
            Assembly.PrimOp.step_stack_length_of_stackArity
              (op := .pop) (by rfl) hStep
          have hHeadBound : 1 ≤ state.stack.length := by
            have hPrim :
                (Assembly.PrimStep.pop).run state = .ok middle := by
              simpa [Assembly.PrimOp.step,
                Assembly.PrimOp.continuingStep?] using hStep
            simpa [Assembly.PrimStep.inputArity] using
              Assembly.PrimStep.run_inputArity_le hPrim
          constructor <;> omega

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
      unfold Assembly.Source.runN Assembly.Control.runNWith Instr.runPops
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

theorem runPops_source_runNResult
    (count : Nat) {pre post : Assembly.Program} {state : EVMState}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (List.replicate count (.prim .pop)))
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runNResult
        (pre ++ List.replicate count (.prim .pop) ++ post)
        count state =
      (Instr.runPops count state).map Assembly.StepResult.running := by
  induction count generalizing pre state with
  | zero =>
      rfl
  | succ count ih =>
      rcases hFits with ⟨hFitsHere, hFitsRest⟩
      rw [List.replicate_succ]
      simp only [List.append_assoc]
      change
        Assembly.Source.runNResult
            (pre ++ Assembly.Instr.prim Assembly.PrimOp.pop ::
              (List.replicate count
                (Assembly.Instr.prim Assembly.PrimOp.pop) ++ post))
            (count + 1) state =
          (Instr.runPops (count + 1) state).map
            Assembly.StepResult.running
      unfold Assembly.Source.runNResult Assembly.Control.runNResultWith
        Instr.runPops
      rw [source_stepResult_at_boundary hFitsHere hPc]
      cases hStep : Assembly.PrimOp.pop.step state with
      | error err =>
          simp only [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Target.stepInstr, hStep, Bind.bind, Except.bind,
            Except.map]
      | ok state' =>
          simp only [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Target.stepInstr, hStep, Bind.bind, Except.bind,
            Assembly.Instr.haltKind?, Assembly.PrimOp.haltKind?,
            Except.map]
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
      simp [Assembly.Program.byteLength_cons, Assembly.Instr.byteSize, ih,
        Nat.add_comm]

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
      | bindLocals offset names =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [TypedCfg.Instr.runState] at hRun
          cases hRun
          exact (uint256_add_zero state.pc).symm
      | bindScratch baseDepth name slot =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [TypedCfg.Instr.runState] at hRun
          cases hRun
          exact (uint256_add_zero state.pc).symm
      | relabel target =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [TypedCfg.Instr.runState] at hRun
          cases hRun
          exact (uint256_add_zero state.pc).symm
      | dup depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            simp [TypedCfg.Instr.runState] at hRun <;>
            simpa [TypedCfg.Instr.runState,
              Assembly.Program.byteLength, Assembly.Instr.byteSize] using
                primOp_step_pc_of_stackArity (by rfl) hRun
      | swap depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            simp [TypedCfg.Instr.runState] at hRun <;>
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

theorem map_map_fst_running
    (result : Except EVMException (EVMState × Shape)) :
    (result.map Prod.fst).map Assembly.StepResult.running =
      result.map (fun pair => Assembly.StepResult.running pair.1) := by
  cases result <;> rfl

theorem runAt_map_running_fst
    {instr : TypedCfg.Instr} {shape output : Shape}
    {state : EVMState}
    (hType : instr.type? shape = some output) :
    (instr.runAt shape state).map
        (fun pair => Assembly.StepResult.running pair.1) =
      (instr.runState shape state).map Assembly.StepResult.running := by
  unfold TypedCfg.Instr.runAt
  rw [hType]
  cases instr.runState shape state <;> rfl

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
      | bindLocals offset names =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [Assembly.Source.runN, Assembly.Control.runNWith,
            TypedCfg.Instr.runState]
      | bindScratch baseDepth name slot =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [Assembly.Source.runN, Assembly.Control.runNWith,
            TypedCfg.Instr.runState]
      | relabel target =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [Assembly.Source.runN, Assembly.Control.runNWith,
            TypedCfg.Instr.runState]
      | dup depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc] <;>
            change
              Assembly.Source.runN
                  (pre ++ Assembly.Instr.prim _ :: post) 1 state =
                _ <;>
            rw [source_runN_one_at_boundary hFits.1 hPc] <;>
            simp [TypedCfg.Instr.runState, Assembly.Source.stepAt,
              Assembly.Target.stepInstr]
      | swap depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc] <;>
            change
              Assembly.Source.runN
                  (pre ++ Assembly.Instr.prim _ :: post) 1 state =
                _ <;>
            rw [source_runN_one_at_boundary hFits.1 hPc] <;>
            simp [TypedCfg.Instr.runState, Assembly.Source.stepAt,
              Assembly.Target.stepInstr]
      | unwind target =>
          simp [TypedCfg.Instr.lowerAt?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simpa [TypedCfg.Instr.runState, List.append_assoc] using
            runPops_source_runN (shape.length - target.length)
              (post := post) hFits hPc

theorem lowerAt_source_runNResult
    {instr : Instr} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower : instr.lowerAt? shape = some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runNResult (pre ++ code ++ post) code.length state =
      (instr.runAt shape state).map
        (fun result => Assembly.StepResult.running result.1) := by
  have hRun :=
    lowerAt_source_runN (post := post) hLower hFits hPc
  cases hType : instr.type? shape with
  | none =>
      simp [TypedCfg.Instr.lowerAt?, hType] at hLower
  | some typedOutput =>
      cases instr with
      | push value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          rw [source_runNResult_one_eq_map_running_append
            (instr := Assembly.Instr.push value) hFits.1 hPc rfl]
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc] at hRun
          rw [hRun]
          exact map_map_fst_running _
      | returnToken value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          rw [source_runNResult_one_eq_map_running_append
            (instr := Assembly.Instr.push value) hFits.1 hPc rfl]
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc] at hRun
          rw [hRun]
          exact map_map_fst_running _
      | prim op =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          have hNoHalt : op.haltKind? = none := by
            cases hArity : op.stackArity? with
            | none =>
                simp [TypedCfg.Instr.type?, hArity] at hType
            | some arity =>
                cases op <;>
                  simp [Assembly.PrimOp.stackArity?,
                    Assembly.PrimOp.haltKind?] at hArity ⊢
          rw [source_runNResult_one_eq_map_running_append
            (instr := Assembly.Instr.prim op) hFits.1 hPc hNoHalt]
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc] at hRun
          rw [hRun]
          exact map_map_fst_running _
      | pop =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          rw [source_runNResult_one_eq_map_running_append
            (instr := Assembly.Instr.prim .pop) hFits.1 hPc rfl]
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc] at hRun
          rw [hRun]
          exact map_map_fst_running _
      | bindLocals offset names =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          rw [runAt_map_running_fst hType]
          simp [Assembly.Source.runNResult, Assembly.Control.runNResultWith,
            TypedCfg.Instr.runState]
          rfl
      | bindScratch baseDepth name slot =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          rw [runAt_map_running_fst hType]
          simp [Assembly.Source.runNResult, Assembly.Control.runNResultWith,
            TypedCfg.Instr.runState]
          rfl
      | relabel target =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          rw [runAt_map_running_fst hType]
          simp [Assembly.Source.runNResult, Assembly.Control.runNResultWith,
            TypedCfg.Instr.runState]
          rfl
      | dup depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc] <;>
            rw [source_runNResult_one_eq_map_running_append hFits.1 hPc rfl] <;>
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc] at hRun <;>
            rw [hRun] <;>
            exact map_map_fst_running _
      | swap depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc] <;>
            rw [source_runNResult_one_eq_map_running_append hFits.1 hPc rfl] <;>
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc] at hRun <;>
            rw [hRun] <;>
            exact map_map_fst_running _
      | unwind target =>
          simp [TypedCfg.Instr.lowerAt?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          rw [runAt_map_running_fst hType]
          simpa [TypedCfg.Instr.runState, byteLength_replicate_pop] using
            runPops_source_runNResult (shape.length - target.length)
              (post := post) hFits hPc

end Instr

namespace Terminator

theorem returnDispatchTestCases_eventually_of_all_ne
    {depth : Nat} {sites : List ReturnSite}
    {front suffix : List Word} {token : Word}
    {code pre post : Assembly.Program} {state : EVMState}
    (hCode :
      code = TypedCfg.Terminator.returnDispatchTestCases depth sites)
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hStack : state.stack = front ++ token :: suffix)
    (hNe : ∀ site, site ∈ sites → site.token ≠ token)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ code ++ post) sites) :
    Assembly.Source.Eventually (pre ++ code ++ post) state
      (fun outcome =>
        match outcome with
        | .ok (.running final) =>
            final.stack = front ++ token :: suffix ∧
              Assembly.SameRuntimeData final state ∧
              final.pc = (pre ++ code).pcAfter
        | _ => False) := by
  subst code
  induction sites generalizing pre state with
  | nil =>
      exact Assembly.Source.Eventually.pure
        (by
          simp [TypedCfg.Terminator.returnDispatchTestCases,
            Assembly.SameRuntimeData.refl, hStack, hPc])
  | cons site rest ih =>
      let headCode := TypedCfg.Terminator.returnDispatchTest depth site
      let tailCode :=
        TypedCfg.Terminator.returnDispatchTestCases depth rest
      have hCodeEq :
          TypedCfg.Terminator.returnDispatchTestCases depth (site :: rest) =
            headCode ++ tailCode := by
        simp [TypedCfg.Terminator.returnDispatchTestCases, headCode, tailCode]
      have hFitsAppend :
          Assembly.Program.PCFitsFrom pre (headCode ++ tailCode) := by
        simpa [hCodeEq] using hFits
      have hHeadFits :
          Assembly.Program.PCFitsFrom pre headCode :=
        Assembly.Program.PCFitsFrom.left hFitsAppend
      have hTailFits :
          Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode :=
        Assembly.Program.PCFitsFrom.right hFitsAppend
      have hSiteNe : site.token ≠ token :=
        hNe site (by simp)
      rcases hResolved site (by simp) with ⟨dest, hDest⟩
      have hDest' :
          (pre ++ headCode ++ (tailCode ++ post)).labelPc site.caseLabel =
            some dest := by
        simpa [hCodeEq, List.append_assoc] using hDest
      have hRecord :
          { state with stack := front ++ token :: suffix } = state := by
        rw [← hStack]
      have hHead :=
        Assembly.StackShuffle.dispatchTest_source_exists
          (state := state) (front := front) (suffix := suffix)
          (token := token) (probe := site.token)
          (label := site.caseLabel) (dest := dest)
          (pre := pre) (post := tailCode ++ post)
          (by
            simpa [headCode, TypedCfg.Terminator.returnDispatchTest,
              hFront] using hHeadFits)
          (by simpa [hRecord] using hPc)
          (by omega)
          (by
            simpa [headCode, TypedCfg.Terminator.returnDispatchTest,
              hFront, List.append_assoc] using hDest')
      rw [hRecord] at hHead
      refine
        Assembly.Source.Eventually.bind_running
          (program :=
            pre ++
              TypedCfg.Terminator.returnDispatchTestCases depth
                (site :: rest) ++ post)
          (middle := fun mid =>
            mid.stack = front ++ token :: suffix ∧
              Assembly.SameRuntimeData mid state ∧
              mid.pc = (pre ++ headCode).pcAfter)
          ?_ ?_
      · exact Assembly.Source.Eventually.mono
          (by
            rw [hCodeEq]
            simpa [headCode, TypedCfg.Terminator.returnDispatchTest,
              hFront, List.append_assoc] using hHead)
          (by
            intro outcome hOutcome
            cases outcome with
            | error err => cases hOutcome
            | ok result =>
                cases result with
                | halted halt => cases hOutcome
                | running mid =>
                    rcases hOutcome with ⟨hStackMid, hData, hPcMid⟩
                    refine ⟨hStackMid, ?_, ?_⟩
                    · simpa [Assembly.SameRuntimeData, hRecord] using hData
                    · simpa [hSiteNe] using hPcMid)
      · intro mid hMid
        have hRestNe :
            ∀ restSite, restSite ∈ rest → restSite.token ≠ token := by
          intro restSite hMem
          exact hNe restSite (by simp [hMem])
        have hRestResolved :
            Preservation.Terminator.ResolvedCaseLabels
              ((pre ++ headCode) ++ tailCode ++ post) rest := by
          intro restSite hMem
          rcases hResolved restSite (by simp [hMem]) with ⟨restDest, hRestDest⟩
          exact
            ⟨restDest,
              by
                simpa [hCodeEq, List.append_assoc] using hRestDest⟩
        have hRest :=
          ih (pre := pre ++ headCode) (state := mid)
            (hStack := hMid.1) (hNe := hRestNe)
            (hFits := hTailFits) (hPc := hMid.2.2)
            (hResolved := hRestResolved)
        exact Assembly.Source.Eventually.mono
          (by
            rw [hCodeEq]
            simpa [List.append_assoc] using hRest)
          (by
            intro outcome hOutcome
            cases outcome with
            | error err => cases hOutcome
            | ok result =>
                cases result with
                | halted halt => cases hOutcome
                | running final =>
                    rcases hOutcome with ⟨hStackFinal, hData, hPcFinal⟩
                    exact
                      ⟨hStackFinal,
                        Assembly.SameRuntimeData.trans hData hMid.2.1,
                        by
                          simpa [hCodeEq, List.append_assoc] using hPcFinal⟩)

theorem returnDispatchTestCases_eventually_of_selected
    {depth : Nat} {before after : List ReturnSite} {site : ReturnSite}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {state : EVMState}
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hStack : state.stack = front ++ token :: suffix)
    (hBefore :
      ∀ prior, prior ∈ before → prior.token ≠ token)
    (hToken : site.token = token)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchTestCases depth
          (before ++ site :: after)))
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++
          TypedCfg.Terminator.returnDispatchTestCases depth
            (before ++ site :: after) ++ post)
        (before ++ site :: after)) :
    ∃ caseDest,
      (pre ++
        TypedCfg.Terminator.returnDispatchTestCases depth
          (before ++ site :: after) ++ post).labelPc site.caseLabel =
        some caseDest ∧
      Assembly.Source.Eventually
        (pre ++
          TypedCfg.Terminator.returnDispatchTestCases depth
            (before ++ site :: after) ++ post)
        state
        (fun outcome =>
          match outcome with
          | .ok (.running final) =>
              final.stack = front ++ token :: suffix ∧
                Assembly.SameRuntimeData final state ∧
                final.pc = EvmYul.UInt256.ofNat caseDest
          | _ => False) := by
  let prefixCode :=
    TypedCfg.Terminator.returnDispatchTestCases depth before
  let siteCode := TypedCfg.Terminator.returnDispatchTest depth site
  let tailCode :=
    TypedCfg.Terminator.returnDispatchTestCases depth after
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchTestCases depth
          (before ++ site :: after) =
        prefixCode ++ siteCode ++ tailCode := by
    simp [TypedCfg.Terminator.returnDispatchTestCases, prefixCode,
      siteCode, tailCode, List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ siteCode ++ tailCode) := by
    simpa [hCodeEq] using hFits
  have hFitsAssoc :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ (siteCode ++ tailCode)) := by
    simpa [List.append_assoc] using hFitsAll
  have hPrefixFits :
      Assembly.Program.PCFitsFrom pre prefixCode :=
    Assembly.Program.PCFitsFrom.left hFitsAssoc
  have hAfterPrefixFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        (siteCode ++ tailCode) :=
    Assembly.Program.PCFitsFrom.right hFitsAssoc
  have hSiteFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode) siteCode :=
    Assembly.Program.PCFitsFrom.left hAfterPrefixFits
  rcases hResolved site (by simp) with ⟨caseDest, hCaseDest⟩
  have hPrefixResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ prefixCode ++ (siteCode ++ tailCode ++ post)) before := by
    intro prior hMem
    rcases hResolved prior (by simp [hMem]) with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hPrefix :=
    returnDispatchTestCases_eventually_of_all_ne
      (depth := depth) (sites := before)
      (front := front) (suffix := suffix) (token := token)
      (code := prefixCode) (pre := pre)
      (post := siteCode ++ tailCode ++ post) (state := state)
      rfl hBound hFront hStack hBefore hPrefixFits hPc hPrefixResolved
  refine ⟨caseDest, hCaseDest, ?_⟩
  refine
    Assembly.Source.Eventually.bind_running
      (program :=
        pre ++
          TypedCfg.Terminator.returnDispatchTestCases depth
            (before ++ site :: after) ++ post)
      (middle := fun mid =>
        mid.stack = front ++ token :: suffix ∧
          Assembly.SameRuntimeData mid state ∧
          mid.pc = (pre ++ prefixCode).pcAfter)
      ?_ ?_
  · exact Assembly.Source.Eventually.mono
      (by simpa [hCodeEq, List.append_assoc] using hPrefix)
      (by
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok result =>
            cases result with
            | halted halt => cases hOutcome
            | running mid => exact hOutcome)
  · intro mid hMid
    have hMidRecord :
        { mid with stack := front ++ token :: suffix } = mid := by
      rw [← hMid.1]
    have hCaseDest' :
        ((pre ++ prefixCode) ++ siteCode ++ (tailCode ++ post)).labelPc
            site.caseLabel =
          some caseDest := by
      simpa [hCodeEq, List.append_assoc] using hCaseDest
    have hSelected :=
      Assembly.StackShuffle.dispatchTest_source_exists
        (state := mid) (front := front) (suffix := suffix)
        (token := token) (probe := site.token)
        (label := site.caseLabel) (dest := caseDest)
        (pre := pre ++ prefixCode) (post := tailCode ++ post)
        (by
          simpa [siteCode, TypedCfg.Terminator.returnDispatchTest,
            hFront] using hSiteFits)
        (by simpa [hMidRecord] using hMid.2.2)
        (by omega)
        (by
          simpa [siteCode, TypedCfg.Terminator.returnDispatchTest,
            hFront, List.append_assoc] using hCaseDest')
    rw [hMidRecord] at hSelected
    exact Assembly.Source.Eventually.mono
      (by simpa [hCodeEq, siteCode,
        TypedCfg.Terminator.returnDispatchTest, hFront,
        List.append_assoc] using hSelected)
      (by
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok result =>
            cases result with
            | halted halt => cases hOutcome
            | running final =>
                rcases hOutcome with ⟨hStackFinal, hData, hPcFinal⟩
                exact
                  ⟨hStackFinal,
                    Assembly.SameRuntimeData.trans
                      (by
                        simpa [Assembly.SameRuntimeData, hMidRecord] using
                          hData)
                      hMid.2.1,
                    by simpa [hToken] using hPcFinal⟩)

theorem returnDispatchCase_eventually
    {depth : Nat} {before after : List ReturnSite} {site : ReturnSite}
    {front suffix : List Word}
    {pre post : Assembly.Program} {state : EVMState}
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hStack : state.stack = front ++ site.token :: suffix)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after)))
    (hPc :
      state.pc =
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth before).pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedTargets
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        (.returnDispatch depth (before ++ site :: after))) :
    ∃ targetDest,
      (pre ++
        TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after) ++ post).labelPc site.target =
        some targetDest ∧
      Assembly.Source.Eventually
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        state
        (Outcome.RunningAt targetDest
          { state with stack := front ++ suffix }) := by
  let prefixCode :=
    TypedCfg.Terminator.returnDispatchCases depth before
  let siteCode := TypedCfg.Terminator.returnDispatchCase depth site
  let tailCode :=
    TypedCfg.Terminator.returnDispatchCases depth after
  let cleanup := Assembly.StackShuffle.removeBuriedUnder depth
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after) =
        prefixCode ++ siteCode ++ tailCode := by
    simp [TypedCfg.Terminator.returnDispatchCases, prefixCode,
      siteCode, tailCode, List.append_assoc]
  have hSiteCodeEq :
      siteCode =
        [Assembly.Instr.label site.caseLabel] ++ cleanup ++
          [Assembly.Instr.jump site.target] := by
    simp [siteCode, cleanup, TypedCfg.Terminator.returnDispatchCase,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ (siteCode ++ tailCode)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hAfterPrefixFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        (siteCode ++ tailCode) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hSiteFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode) siteCode :=
    Assembly.Program.PCFitsFrom.left hAfterPrefixFits
  have hSiteFits' :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        ([Assembly.Instr.label site.caseLabel] ++ cleanup ++
          [Assembly.Instr.jump site.target]) := by
    simpa [hSiteCodeEq] using hSiteFits
  have hLabelFit : (pre ++ prefixCode).PCFits :=
    Assembly.Program.PCFitsFrom.start hSiteFits'
  have hAfterLabelFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        (cleanup ++ [Assembly.Instr.jump site.target]) := by
    simpa [List.append_assoc] using hSiteFits'.2
  have hCleanupFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        cleanup :=
    Assembly.Program.PCFitsFrom.left hAfterLabelFits
  have hJumpFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel] ++ cleanup)
        [Assembly.Instr.jump site.target] := by
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right hAfterLabelFits)
  rcases hResolved site.target
      (by
        simp [TypedCfg.Terminator.targets]) with
    ⟨targetDest, hTargetDest⟩
  have hTargetDest' :
      (pre ++ prefixCode ++ siteCode ++ tailCode ++ post).labelPc site.target =
        some targetDest := by
    simpa [hCodeEq, List.append_assoc] using hTargetDest
  let afterLabel : EVMState := state.incrPC
  have hAfterLabelPc :
      afterLabel.pc =
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel]).pcAfter := by
    calc
      afterLabel.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
        simp [afterLabel, EvmYul.EVM.State.incrPC]
      _ = (pre ++ prefixCode).pcAfter + EvmYul.UInt256.ofNat 1 := by
        rw [hPc]
      _ =
          EvmYul.UInt256.ofNat ((pre ++ prefixCode).byteLength + 1) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ =
          (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel]).pcAfter := by
        simp [Assembly.Program.pcAfter, Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, Assembly.Instr.byteSize, Nat.add_assoc]
  have hLabelRun :
      Assembly.Source.runNResult
          (pre ++ prefixCode ++ siteCode ++ tailCode ++ post)
          1 state =
        .ok (.running afterLabel) := by
    rw [show
      pre ++ prefixCode ++ siteCode ++ tailCode ++ post =
        (pre ++ prefixCode) ++
          Assembly.Instr.label site.caseLabel ::
            (cleanup ++ Assembly.Instr.jump site.target :: tailCode ++ post) by
      simp [hSiteCodeEq, List.append_assoc]]
    rw [source_runNResult_one_at_boundary hLabelFit hPc]
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      Assembly.Instr.haltKind?, Assembly.Target.stepInstr, afterLabel]
  have hAfterLabelStack :
      afterLabel.stack = front ++ site.token :: suffix := by
    simpa [afterLabel] using hStack
  refine ⟨targetDest, hTargetDest, ?_⟩
  refine
    Assembly.Source.Eventually.bind_running
      (program :=
        pre ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
      (middle := fun mid =>
        mid = afterLabel)
      ?_ ?_
  · refine ⟨1, .ok (.running afterLabel), ?_, rfl⟩
    simpa [hCodeEq, List.append_assoc] using hLabelRun
  · intro labelState hLabelState
    subst labelState
    have hAfterLabelRecord :
        { afterLabel with stack := front ++ site.token :: suffix } =
          afterLabel := by
      rw [← hAfterLabelStack]
    have hCleanup :=
      Assembly.StackShuffle.removeBuriedUnder_source_exists
        (state := afterLabel) (front := front) (suffix := suffix)
        (token := site.token)
        (pre :=
          pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        (post := [Assembly.Instr.jump site.target] ++ tailCode ++ post)
        (by simpa [hFront] using hCleanupFits)
        (by simpa [hAfterLabelRecord] using hAfterLabelPc)
        (by omega)
    rw [hAfterLabelRecord] at hCleanup
    refine
      Assembly.Source.Eventually.bind_running
        (program :=
          pre ++
            TypedCfg.Terminator.returnDispatchCases depth
              (before ++ site :: after) ++ post)
        (middle := fun cleaned =>
          cleaned.stack = front ++ suffix ∧
            Assembly.SameRuntimeData cleaned
              { state with stack := front ++ suffix } ∧
            cleaned.pc =
              (pre ++ prefixCode ++
                [Assembly.Instr.label site.caseLabel] ++ cleanup).pcAfter)
        ?_ ?_
    · exact Assembly.Source.Eventually.mono
        (by
          simpa [hCodeEq, hSiteCodeEq, cleanup, hFront,
            List.append_assoc] using hCleanup)
        (by
          intro outcome hOutcome
          cases outcome with
          | error err => cases hOutcome
          | ok result =>
              cases result with
              | halted halt => cases hOutcome
              | running cleaned =>
                  rcases hOutcome with ⟨hStackClean, hData, hPcClean⟩
                  refine ⟨hStackClean, ?_, ?_⟩
                  calc
                    Assembly.eraseRuntimeControl cleaned =
                        Assembly.eraseRuntimeControl
                          { afterLabel with stack := front ++ suffix } :=
                      hData
                    _ =
                        Assembly.eraseRuntimeControl
                          { state with stack := front ++ suffix } := by
                      simp [afterLabel, Assembly.eraseRuntimeControl,
                        EvmYul.EVM.State.incrPC]
                  · simpa [cleanup, hFront, List.append_assoc] using hPcClean)
    · intro cleaned hCleaned
      have hTargetDest'' :
          ((pre ++ prefixCode ++
              [Assembly.Instr.label site.caseLabel] ++ cleanup) ++
            [Assembly.Instr.jump site.target] ++ tailCode ++ post).labelPc
              site.target =
            some targetDest := by
        simpa [hSiteCodeEq, List.append_assoc] using hTargetDest'
      have hTargetDest''' :
          ((pre ++ prefixCode ++
              [Assembly.Instr.label site.caseLabel] ++ cleanup) ++
            Assembly.Instr.jump site.target :: tailCode ++ post).labelPc
              site.target =
            some targetDest := by
        simpa [List.append_assoc] using hTargetDest''
      refine
        ⟨1,
          .ok (.running (Assembly.Source.jumpPc targetDest cleaned)),
          ?_, ?_⟩
      · let jumpPre :=
          pre ++ prefixCode ++
            [Assembly.Instr.label site.caseLabel] ++ cleanup
        have hTargetDestBase :
            (jumpPre ++
              Assembly.Instr.jump site.target :: (tailCode ++ post)).labelPc
                site.target =
              some targetDest := by
          simpa [jumpPre, List.append_assoc] using hTargetDest'''
        have hTargetDestActual :
            (pre ++
              (prefixCode ++
                Assembly.Instr.label site.caseLabel ::
                  (cleanup ++
                    Assembly.Instr.jump site.target ::
                      (tailCode ++ post)))).labelPc site.target =
              some targetDest := by
          simpa [jumpPre, List.append_assoc] using hTargetDestBase
        have hJumpRunBase :
            Assembly.Source.runNResult
                (jumpPre ++
                  Assembly.Instr.jump site.target :: (tailCode ++ post))
                1 cleaned =
              .ok
                (.running
                  (Assembly.Source.jumpPc targetDest cleaned)) := by
          rw [source_runNResult_one_at_boundary
            (pre := jumpPre) (post := tailCode ++ post)
            (instr := Assembly.Instr.jump site.target)
            (by
              simpa [jumpPre, List.append_assoc] using
                Assembly.Program.PCFitsFrom.start hJumpFits)
            (by simpa [jumpPre, List.append_assoc] using hCleaned.2.2)]
          simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Instr.haltKind?, hTargetDestActual,
            Assembly.Source.invalid, jumpPre, List.append_assoc]
        simpa [jumpPre, hCodeEq, hSiteCodeEq, List.append_assoc] using
          hJumpRunBase
      · exact
          ⟨rfl,
            Assembly.SameRuntimeData.trans
              (Assembly.SameRuntimeData.jumpPc targetDest cleaned)
              hCleaned.2.1⟩

theorem returnDispatch_selected_eventually
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word} {target : Label}
    {code pre post : Assembly.Program} {state : EVMState}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = some token)
    (hFind : Block.ReturnSite.findTarget? token sites = some target)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolvedTargets :
      Preservation.Terminator.ResolvedTargets
        (pre ++ code ++ post)
        (.returnDispatch returnCount sites))
    (hResolvedCases :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ code ++ post) sites)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Assembly.Source.Eventually (pre ++ code ++ post) state
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape
          (.returnDispatch returnCount sites) state)) := by
  subst code
  subst returnCount
  rcases List.getElem?_eq_some_split hGet with
    ⟨front, suffix, hStack, hFront⟩
  rcases ReturnSite.findTarget?_eq_some_split hFind with
    ⟨before, site, after, hSites, hBefore, hToken, hTarget⟩
  subst sites
  let testCases :=
    TypedCfg.Terminator.returnDispatchTestCases depth
      (before ++ site :: after)
  let tests :=
    TypedCfg.Terminator.returnDispatchTests depth
      (before ++ site :: after)
  let cases :=
    TypedCfg.Terminator.returnDispatchCases depth
      (before ++ site :: after)
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCode depth
          (before ++ site :: after) =
        testCases ++ [Assembly.Instr.prim .invalid] ++ cases := by
    simp [TypedCfg.Terminator.returnDispatchCode,
      TypedCfg.Terminator.returnDispatchTests, testCases, tests, cases,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (testCases ++ ([Assembly.Instr.prim .invalid] ++ cases)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hTestCasesFits :
      Assembly.Program.PCFitsFrom pre testCases :=
    Assembly.Program.PCFitsFrom.left hFitsAll
  have hAfterTestCasesFits :
      Assembly.Program.PCFitsFrom (pre ++ testCases)
        ([Assembly.Instr.prim .invalid] ++ cases) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hCasesFits :
      Assembly.Program.PCFitsFrom
        (pre ++ testCases ++ [Assembly.Instr.prim .invalid]) cases := by
    simpa [List.append_assoc] using hAfterTestCasesFits.2
  have hResolvedCases' :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ testCases ++
          ([Assembly.Instr.prim .invalid] ++ cases ++ post))
        (before ++ site :: after) := by
    intro resolvedSite hMem
    rcases hResolvedCases resolvedSite hMem with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hSelected :=
    returnDispatchTestCases_eventually_of_selected
      (depth := depth) (before := before) (after := after) (site := site)
      (front := front) (suffix := suffix) (token := token)
      (pre := pre)
      (post := [Assembly.Instr.prim .invalid] ++ cases ++ post)
      (state := state)
      hBound hFront
      (by simpa [hStack, List.append_assoc])
      hBefore hToken
      (by simpa [testCases] using hTestCasesFits)
      hPc
      (by simpa [testCases, List.append_assoc] using hResolvedCases')
  rcases hSelected with ⟨caseDest, hCaseDest, hSelectedRun⟩
  let caseBase := pre ++ testCases ++ [Assembly.Instr.prim .invalid]
  let casePrefix :=
    TypedCfg.Terminator.returnDispatchCases depth before
  let caseTail :=
    Assembly.StackShuffle.removeBuriedUnder depth ++
      [Assembly.Instr.jump site.target] ++
      TypedCfg.Terminator.returnDispatchCases depth after ++ post
  have hProgramAtCase :
      pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post =
        (caseBase ++ casePrefix) ++
          Assembly.Instr.label site.caseLabel :: caseTail := by
    simp [hCodeEq, testCases, cases, caseBase, casePrefix, caseTail,
      TypedCfg.Terminator.returnDispatchCases,
      TypedCfg.Terminator.returnDispatchCase, List.append_assoc]
  have hInternalLabel :
      (pre ++
        TypedCfg.Terminator.returnDispatchCode depth
          (before ++ site :: after) ++ post).labelPc site.caseLabel =
        some (caseBase ++ casePrefix).byteLength := by
    rw [hProgramAtCase]
    exact
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        (caseBase ++ casePrefix) caseTail
        (by simpa [hProgramAtCase] using hLabels)
  have hCaseDestEq :
      caseDest = (caseBase ++ casePrefix).byteLength := by
    have hCaseDest' :
        (pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post).labelPc site.caseLabel =
          some caseDest := by
      simpa [hCodeEq, testCases, cases, List.append_assoc] using hCaseDest
    rw [hInternalLabel] at hCaseDest'
    exact (Option.some.inj hCaseDest').symm
  have hResolvedTargets' :
      Preservation.Terminator.ResolvedTargets
        (caseBase ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        (.returnDispatch depth (before ++ site :: after)) := by
    intro resolvedTarget hMem
    rcases hResolvedTargets resolvedTarget
        (by
          simpa [TypedCfg.Terminator.targets] using hMem) with
      ⟨dest, hDest⟩
    exact
      ⟨dest,
        by
          simpa [hCodeEq, testCases, cases, caseBase,
            List.append_assoc] using hDest⟩
  refine
    Assembly.Source.Eventually.bind_running
      (program :=
        pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post)
      (middle := fun selected =>
        selected.stack = front ++ token :: suffix ∧
          Assembly.SameRuntimeData selected state ∧
          selected.pc = EvmYul.UInt256.ofNat caseDest)
      ?_ ?_
  · exact Assembly.Source.Eventually.mono
      (by
        simpa [hCodeEq, testCases, cases, List.append_assoc] using hSelectedRun)
      (by
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok result =>
            cases result with
            | halted halt => cases hOutcome
            | running selected => exact hOutcome)
  · intro selected hSelectedState
    have hCasePc :
        selected.pc = (caseBase ++ casePrefix).pcAfter := by
      rw [hSelectedState.2.2, hCaseDestEq]
      rfl
    have hCaseRun :=
      returnDispatchCase_eventually
        (depth := depth) (before := before) (after := after) (site := site)
        (front := front) (suffix := suffix)
        (pre := caseBase) (post := post) (state := selected)
        hBound hFront
        (by simpa [hToken] using hSelectedState.1)
        hCasesFits
        (by simpa [casePrefix] using hCasePc)
        hResolvedTargets'
    rcases hCaseRun with ⟨targetDest, hTargetDest, hRun⟩
    have hTargetDest' :
        (pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post).labelPc target =
          some targetDest := by
      simpa [hTarget, hCodeEq, testCases, cases, caseBase,
        List.append_assoc] using hTargetDest
    exact Assembly.Source.Eventually.mono
      (by
        simpa [hCodeEq, testCases, cases, caseBase,
          List.append_assoc] using hRun)
      (by
        intro outcome hOutcome
        have hErase :
            state.stack.eraseIdx depth = front ++ suffix := by
          rw [hStack, ← hFront]
          exact List.eraseIdx_append_at_length front suffix token
        simp [Block.runTerm, hDepth, hGet, hFind,
          Outcome.Simulates]
        have hTargetDestActual :
            (pre ++
              (TypedCfg.Terminator.returnDispatchCode depth
                (before ++ site :: after) ++ post)).labelPc target =
              some targetDest := by
          simpa [List.append_assoc] using hTargetDest'
        refine ⟨targetDest, hTargetDestActual, ?_⟩
        cases outcome with
        | error err => cases hOutcome
        | ok result =>
            cases result with
            | halted halt => cases hOutcome
            | running final =>
                rcases hOutcome with ⟨hPcFinal, hData⟩
                have hSelectedCleanData :
                    Assembly.SameRuntimeData
                      { selected with stack := front ++ suffix }
                      { state with stack := front ++ suffix } :=
                  Assembly.eraseRuntimeControl_with_stack_congr
                    hSelectedState.2.1
                exact
                  ⟨hPcFinal,
                    by
                      simpa [hErase] using
                        Assembly.SameRuntimeData.trans
                          hData hSelectedCleanData⟩)

theorem returnDispatch_unknown_token_eventually
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word}
    {code pre post : Assembly.Program} {state : EVMState}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = some token)
    (hFind : Block.ReturnSite.findTarget? token sites = none)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolvedCases :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ code ++ post) sites) :
    Assembly.Source.Eventually (pre ++ code ++ post) state
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape
          (.returnDispatch returnCount sites) state)) := by
  subst code
  subst returnCount
  rcases List.getElem?_eq_some_split hGet with
    ⟨front, suffix, hStack, hFront⟩
  let testCases :=
    TypedCfg.Terminator.returnDispatchTestCases depth sites
  let cases :=
    TypedCfg.Terminator.returnDispatchCases depth sites
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCode depth sites =
        testCases ++ [Assembly.Instr.prim .invalid] ++ cases := by
    simp [TypedCfg.Terminator.returnDispatchCode,
      TypedCfg.Terminator.returnDispatchTests, testCases, cases,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (testCases ++ ([Assembly.Instr.prim .invalid] ++ cases)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hTestCasesFits :
      Assembly.Program.PCFitsFrom pre testCases :=
    Assembly.Program.PCFitsFrom.left hFitsAll
  have hAfterTestsFits :
      Assembly.Program.PCFitsFrom (pre ++ testCases)
        ([Assembly.Instr.prim .invalid] ++ cases) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hResolvedCases' :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ testCases ++
          ([Assembly.Instr.prim .invalid] ++ cases ++ post)) sites := by
    intro site hMem
    rcases hResolvedCases site hMem with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hTests :=
    returnDispatchTestCases_eventually_of_all_ne
      (depth := depth) (sites := sites)
      (front := front) (suffix := suffix) (token := token)
      (code := testCases) (pre := pre)
      (post := [Assembly.Instr.prim .invalid] ++ cases ++ post)
      (state := state)
      rfl hBound hFront
      (by simpa [hStack, List.append_assoc])
      (ReturnSite.findTarget?_eq_none_all_ne hFind)
      hTestCasesFits hPc hResolvedCases'
  refine
    Assembly.Source.Eventually.bind_running
      (program :=
        pre ++ TypedCfg.Terminator.returnDispatchCode depth sites ++ post)
      (middle := fun tested =>
        tested.stack = front ++ token :: suffix ∧
          Assembly.SameRuntimeData tested state ∧
          tested.pc = (pre ++ testCases).pcAfter)
      ?_ ?_
  · exact Assembly.Source.Eventually.mono
      (by simpa [hCodeEq, List.append_assoc] using hTests)
      (by
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok result =>
            cases result with
            | halted halt => cases hOutcome
            | running tested => exact hOutcome)
  · intro tested hTested
    refine ⟨1, .error .InvalidInstruction, ?_, ?_⟩
    · have hInvalid :
          Assembly.Source.runNResult
              ((pre ++ testCases) ++
                Assembly.Instr.prim .invalid :: (cases ++ post))
              1 tested =
            .error .InvalidInstruction := by
        rw [source_runNResult_one_at_boundary
          (Assembly.Program.PCFitsFrom.start hAfterTestsFits)
          hTested.2.2]
        simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
          Assembly.Target.stepInstr, Assembly.PrimOp.step,
          Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run]
      simpa [hCodeEq, List.append_assoc] using hInvalid
    · simp [Block.runTerm, hDepth, hGet, hFind, Outcome.Simulates]

theorem returnDispatch_missing_token_eventually
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite}
    {code pre post : Assembly.Program} {state : EVMState}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hSites : sites ≠ [])
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = none)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.Eventually (pre ++ code ++ post) state
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape
          (.returnDispatch returnCount sites) state)) := by
  subst code
  subst returnCount
  cases sites with
  | nil =>
      exact (hSites rfl).elim
  | cons site rest =>
      have hLen : state.stack.length ≤ depth := by
        rw [List.getElem?_eq_none_iff] at hGet
        exact hGet
      have hDupError :
          Assembly.Target.stepInstr
              (Assembly.StackShuffle.targetInstr
                (Assembly.StackShuffle.dupInstr (depth + 1)))
              state =
            .error .StackUnderflow := by
        rw [Assembly.StackShuffle.dupInstr_step_eq_dup
          (by omega) (by omega)]
        simp [EvmYul.dup, show ¬depth + 1 ≤ state.stack.length by omega]
      have hCodeHead :
          TypedCfg.Terminator.returnDispatchCode depth (site :: rest) =
            Assembly.StackShuffle.dupInstr (depth + 1) ::
              ( [ Assembly.Instr.push site.token
                , Assembly.Instr.prim .eq
                , Assembly.Instr.jumpi site.caseLabel
                ] ++
                TypedCfg.Terminator.returnDispatchTestCases depth rest ++
                [Assembly.Instr.prim .invalid] ++
                TypedCfg.Terminator.returnDispatchCases depth (site :: rest)) := by
        simp [TypedCfg.Terminator.returnDispatchCode,
          TypedCfg.Terminator.returnDispatchTests,
          TypedCfg.Terminator.returnDispatchTestCases,
          TypedCfg.Terminator.returnDispatchTest,
          List.append_assoc]
      refine ⟨1, .error .StackUnderflow, ?_, ?_⟩
      · rw [show
          pre ++
              TypedCfg.Terminator.returnDispatchCode depth (site :: rest) ++
              post =
            pre ++
              Assembly.StackShuffle.dupInstr (depth + 1) ::
                ( [ Assembly.Instr.push site.token
                  , Assembly.Instr.prim .eq
                  , Assembly.Instr.jumpi site.caseLabel
                  ] ++
                  TypedCfg.Terminator.returnDispatchTestCases depth rest ++
                  [Assembly.Instr.prim .invalid] ++
                  TypedCfg.Terminator.returnDispatchCases depth
                    (site :: rest) ++ post) by
            rw [hCodeHead]
            simp [List.append_assoc]]
        rw [source_runNResult_one_at_boundary hFits.1 hPc]
        simp [Assembly.Source.stepAtResult,
          Assembly.StackShuffle.source_stepAt_eq_targetInstr
            (Assembly.StackShuffle.dupInstr_sourceLocal
              (n := depth + 1) (by omega) (by omega)),
          hDupError]
      · simp [Block.runTerm, hDepth, hGet, Outcome.Simulates]

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
      · exact
          ⟨dest, hDest, rfl,
            Assembly.SameRuntimeData.jumpPc dest state⟩
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
      · exact
          ⟨dest, hDest, rfl,
            Assembly.SameRuntimeData.jumpPc dest state⟩
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
              exact
                ⟨nextDest, hNextDest', rfl,
                  Assembly.SameRuntimeData.jumpPc nextDest popped⟩
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
              exact
                ⟨targetDest, hTargetDest', rfl,
                  Assembly.SameRuntimeData.jumpPc targetDest popped⟩
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
          Assembly.Target.stepInstr_prim]
        rw [Assembly.PrimOp.step_eq_continuingStep_run (by rfl)]
        rfl
      · exact ⟨.InvalidInstruction, rfl⟩

theorem lowerAt?_eventually
    {shape : Shape} {term : TypedCfg.Terminator}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower : term.lowerAt? shape = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedControl
        (pre ++ code ++ post) term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Assembly.Source.Eventually (pre ++ code ++ post) state
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape term state)) := by
  cases term with
  | fallthrough next =>
      exact lowerAt?_eventually_of_direct
        (term := .fallthrough next) (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | jump target =>
      exact lowerAt?_eventually_of_direct
        (term := .jump target) (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | jumpi target next =>
      exact lowerAt?_eventually_of_direct
        (term := .jumpi target next) (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | halt kind =>
      exact lowerAt?_eventually_of_direct
        (term := .halt kind) (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | invalid =>
      exact lowerAt?_eventually_of_direct
        (term := .invalid) (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | returnDispatch returnCount sites =>
      cases hDepth : shape.returnTokenDepth? with
      | none =>
          simp [TypedCfg.Terminator.lowerAt?, hDepth] at hLower
      | some depth =>
          by_cases hBound : depth < 16
          · have hFacts :
                (sites ≠ [] ∧ depth = returnCount) ∧
                  TypedCfg.Terminator.returnDispatchCode depth sites = code := by
              simpa [TypedCfg.Terminator.lowerAt?, hDepth,
                TypedCfg.Terminator.returnDispatchCode?, hBound] using hLower
            have hGood : sites ≠ [] ∧ depth = returnCount := hFacts.1
            have hCodeEq :
                code =
                  TypedCfg.Terminator.returnDispatchCode depth sites :=
              hFacts.2.symm
            have hResolvedCases :
                Preservation.Terminator.ResolvedCaseLabels
                  (pre ++ code ++ post) sites := by
              intro site hMem
              exact hResolved.2 site.caseLabel
                (by
                  simp only [TypedCfg.Terminator.definedLabels]
                  exact List.mem_map.mpr ⟨site, hMem, rfl⟩)
            cases hGet : state.stack[depth]? with
            | none =>
                exact returnDispatch_missing_token_eventually
                  hDepth hGood.2 hGood.1 hCodeEq hBound hGet
                  hFits hPc
            | some token =>
                cases hFind :
                    Block.ReturnSite.findTarget? token sites with
                | none =>
                    exact returnDispatch_unknown_token_eventually
                      hDepth hGood.2 hCodeEq hBound hGet hFind
                      hFits hPc hResolvedCases
                | some target =>
                    exact returnDispatch_selected_eventually
                      hDepth hGood.2 hCodeEq hBound hGet hFind
                      hFits hPc hResolved.1 hResolvedCases hLabels
          · simp [TypedCfg.Terminator.lowerAt?, hDepth,
              TypedCfg.Terminator.returnDispatchCode?, hBound] at hLower

end Terminator

namespace Block

def RunSimulates (program : Assembly.Program) :
    Except EVMException Outcome →
      Assembly.Source.ExecutionOutcome → Prop
  | .error error, outcome => outcome = .error error
  | .ok sourceOutcome, outcome =>
      Outcome.Simulates program sourceOutcome outcome

theorem runBody_output_of_lowerBodyFrom?
    {body : List Instr} {shape output runOutput : Shape}
    {code : Assembly.Program} {state final : EVMState}
    (hLower :
      TypedCfg.Block.lowerBodyFrom? body shape = some (code, output))
    (hRun :
      TypedCfg.Block.runBody body shape state = .ok (final, runOutput)) :
    runOutput = output := by
  induction body generalizing shape output runOutput code state final with
  | nil =>
      simp [TypedCfg.Block.lowerBodyFrom?, TypedCfg.Block.runBody] at hLower hRun
      exact hRun.2.symm.trans hLower.2
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
              unfold TypedCfg.Block.runBody TypedCfg.Instr.runAt at hRun
              rw [hType] at hRun
              cases hHeadRun : instr.runState shape state with
              | error err =>
                  simp only [
                    hHeadRun, Bind.bind, Except.bind, Option.elim] at hRun
                  contradiction
              | ok mid =>
                  simp only [hHeadRun, Bind.bind, Except.bind, Option.elim] at hRun
                  exact ih hTail hRun

theorem runBody_pc_of_lowerBodyFrom?
    {body : List Instr} {shape output : Shape}
    {code : Assembly.Program} {state final : EVMState}
    (hLower :
      TypedCfg.Block.lowerBodyFrom? body shape = some (code, output))
    (hRun :
      TypedCfg.Block.runBody body shape state = .ok (final, output)) :
    final.pc =
      state.pc + EvmYul.UInt256.ofNat code.byteLength := by
  induction body generalizing shape code output state final with
  | nil =>
      simp [TypedCfg.Block.lowerBodyFrom?, TypedCfg.Block.runBody] at hLower hRun
      rcases hLower with ⟨rfl, rfl⟩
      obtain ⟨hState, _⟩ := hRun
      subst final
      exact (uint256_add_zero state.pc).symm
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
              unfold TypedCfg.Block.runBody TypedCfg.Instr.runAt at hRun
              rw [hType] at hRun
              cases hHeadRun : instr.runState shape state with
              | error err =>
                  simp only [
                    hHeadRun, Bind.bind, Except.bind, Option.elim] at hRun
                  contradiction
              | ok mid =>
                  simp only [hHeadRun, Bind.bind, Except.bind] at hRun
                  have hTailPc :=
                    ih (shape := headOutput) (code := tail)
                      (output := tailOutput) (state := mid) (final := final)
                      hTail hRun
                  calc
                    final.pc =
                        mid.pc +
                          EvmYul.UInt256.ofNat tail.byteLength :=
                      hTailPc
                    _ =
                        (state.pc +
                          EvmYul.UInt256.ofNat head.byteLength) +
                            EvmYul.UInt256.ofNat tail.byteLength := by
                      rw [Instr.runState_pc_of_lowerAt hHead hHeadRun]
                    _ =
                        state.pc +
                          (EvmYul.UInt256.ofNat head.byteLength +
                            EvmYul.UInt256.ofNat tail.byteLength) := by
                      exact uint256_add_assoc _ _ _
                    _ =
                        state.pc +
                          EvmYul.UInt256.ofNat
                            (head.byteLength + tail.byteLength) := by
                      rw [Assembly.UInt256_ofNat_add]
                    _ =
                        state.pc +
                          EvmYul.UInt256.ofNat
                            (head ++ tail).byteLength := by
                      simp [Assembly.Program.byteLength_append]

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

theorem lowerBodyFrom?_source_runNResult
    {body : List Instr} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    (hLower : TypedCfg.Block.lowerBodyFrom? body shape = some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runNResult (pre ++ code ++ post) code.length state =
      (TypedCfg.Block.runBody body shape state).map
        (fun result => Assembly.StepResult.running result.1) := by
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
                Instr.lowerAt_source_runNResult
                  (post := tail ++ post) hHead hHeadFits hPc
              rw [List.length_append, Assembly.Source.runNResult_add]
              rw [show
                Assembly.Source.runNResult
                    (pre ++ (head ++ tail) ++ post)
                    head.length state =
                  (instr.runAt shape state).map
                    (fun result => Assembly.StepResult.running result.1) by
                simpa [List.append_assoc] using hHeadRun]
              cases hRunState : instr.runState shape state with
              | error err =>
                  simp [TypedCfg.Block.runBody, TypedCfg.Instr.runAt,
                    hType, hRunState, Except.map, Bind.bind, Except.bind]
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
                  simpa [List.append_assoc, TypedCfg.Block.runBody,
                    TypedCfg.Instr.runAt, hType, hRunState] using hTailRun

theorem lower?_eventually
    {block : TypedCfg.Block} {code pre post : Assembly.Program}
    {state : EVMState}
    (hLower : block.lower? = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Terminator.ResolvedControl
        (pre ++ code ++ post) block.term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Assembly.Source.Eventually (pre ++ code ++ post) state
      (RunSimulates (pre ++ code ++ post)
        (block.run state.incrPC)) := by
  unfold TypedCfg.Block.lower? at hLower
  cases hBody :
      TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm : block.term.lowerAt? block.output with
        | none =>
            simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst code
            let program :=
              pre ++
                (Assembly.Instr.label block.label :: body ++ term) ++
                  post
            let entry := state.incrPC
            have hLabelRun :
                Assembly.Source.runNResult program 1 state =
                  .ok (.running entry) := by
              have hRun :=
                source_runNResult_one_at_boundary
                  (pre := pre)
                  (post := (body ++ term) ++ post)
                  (instr := Assembly.Instr.label block.label)
                  hFits.1 hPc
              simpa [program, entry, List.append_assoc,
                Assembly.Source.stepAtResult, Assembly.Source.stepAt,
                Assembly.Target.stepInstr] using hRun
            have hEntryPc :
                entry.pc =
                  (pre ++ [Assembly.Instr.label block.label]).pcAfter := by
              calc
                entry.pc =
                    state.pc + EvmYul.UInt256.ofNat 1 := rfl
                _ =
                    pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
                  rw [hPc]
                _ =
                    (pre ++ [Assembly.Instr.label block.label]).pcAfter := by
                  simp [Assembly.Program.pcAfter,
                    Assembly.Program.byteLength_append,
                    Assembly.Program.byteLength,
                    Assembly.Instr.byteSize,
                    Assembly.UInt256_ofNat_add]
            have hBodyFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label]) body :=
              Assembly.Program.PCFitsFrom.left hFits.2
            have hTermFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label] ++ body)
                  term := by
              simpa [List.append_assoc] using
                Assembly.Program.PCFitsFrom.right hFits.2
            have hBodyRun :=
              lowerBodyFrom?_source_runNResult
                (pre := pre ++ [Assembly.Instr.label block.label])
                (post := term ++ post) hBody hBodyFits hEntryPc
            have hBodyRun' :
                Assembly.Source.runNResult program body.length entry =
                  (TypedCfg.Block.runBody
                    block.body block.input entry).map
                      (fun result =>
                        Assembly.StepResult.running result.1) := by
              simpa [program, List.append_assoc] using hBodyRun
            have hAfterLabel :
                Assembly.Source.Eventually program entry
                  (RunSimulates program (block.run entry)) := by
              cases hRunBody :
                  TypedCfg.Block.runBody
                    block.body block.input entry with
              | error err =>
                  refine ⟨body.length, .error err, ?_, ?_⟩
                  · simpa [hRunBody, Except.map] using hBodyRun'
                  · simp [RunSimulates, TypedCfg.Block.run, hRunBody,
                      Bind.bind, Except.bind]
              | ok result =>
                  rcases result with ⟨mid, bodyOutput⟩
                  have hBodyOutput : bodyOutput = block.output := by
                    exact runBody_output_of_lowerBodyFrom? hBody hRunBody
                  subst bodyOutput
                  have hBodyRunning :
                      Assembly.Source.runNResult program body.length entry =
                        .ok (.running mid) := by
                    simpa [hRunBody] using hBodyRun'
                  have hMidPc :
                      mid.pc =
                        (pre ++ [Assembly.Instr.label block.label] ++
                          body).pcAfter := by
                    calc
                      mid.pc =
                          entry.pc +
                            EvmYul.UInt256.ofNat body.byteLength :=
                        runBody_pc_of_lowerBodyFrom? hBody hRunBody
                      _ =
                          (pre ++ [Assembly.Instr.label block.label]).pcAfter +
                            EvmYul.UInt256.ofNat body.byteLength := by
                        rw [hEntryPc]
                      _ =
                          (pre ++ [Assembly.Instr.label block.label] ++
                            body).pcAfter := by
                        exact
                          (Assembly.Program.pcAfter_append
                            (pre ++ [Assembly.Instr.label block.label])
                            body).symm
                  have hTermRun :
                      Assembly.Source.Eventually program mid
                        (Outcome.Simulates program
                          (TypedCfg.Block.runTerm
                            block.output block.term mid)) := by
                    have hRun :=
                      Terminator.lowerAt?_eventually
                        (pre :=
                          pre ++ [Assembly.Instr.label block.label] ++ body)
                        (post := post) hTerm hTermFits hMidPc
                        (by
                          simpa [program, List.append_assoc] using hResolved)
                        (by
                          simpa [program, List.append_assoc] using hLabels)
                    simpa [program, List.append_assoc] using hRun
                  have hBodyThenTerm :
                      Assembly.Source.Eventually program entry
                        (Outcome.Simulates program
                          (TypedCfg.Block.runTerm
                            block.output block.term mid)) :=
                    Assembly.Source.Eventually.bind_running
                      (middle := fun current => current = mid)
                      ⟨body.length, .ok (.running mid), hBodyRunning, rfl⟩
                      (by
                        intro current hCurrent
                        subst current
                        exact hTermRun)
                  simpa [RunSimulates, TypedCfg.Block.run, hRunBody,
                    Bind.bind, Except.bind] using hBodyThenTerm
            have hFromLabel :
                Assembly.Source.Eventually program state
                  (RunSimulates program (block.run entry)) :=
              Assembly.Source.Eventually.bind_running
                (middle := fun current => current = entry)
                ⟨1, .ok (.running entry), hLabelRun, rfl⟩
                (by
                  intro current hCurrent
                  subst current
                  exact hAfterLabel)
            simpa [program, entry] using hFromLabel
      · simp [hBody, hOutput] at hLower

end Block

namespace Program

theorem lower?_step_eventually
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : EVMState} {entryPc : Nat}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    Assembly.Source.Eventually target state
      (Block.RunSimulates target
        (program.step label state.incrPC)) := by
  rcases
      TypedCfg.Program.lower?_fragment_of_findBlock?
        hLower hFind with
    ⟨fragment⟩
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
    Assembly.Program.labels_nodup_of_accepted hAccepted
  have hCodeFits :
      Assembly.Program.PCFitsFrom fragment.pre fragment.code := by
    apply Assembly.Program.PCFitsFrom.of_append
    rw [← fragment.target_eq]
    exact hFits
  have hResolved :
      Terminator.ResolvedControl target block.term := by
    constructor
    · intro symbolic hSymbolic
      rcases
          TypedCfg.Block.target_instr_mem_of_lower?
            fragment.lower hSymbolic with
        ⟨instr, hInstr, hInstrTarget⟩
      have hInstrGlobal : instr ∈ target := by
        rw [fragment.target_eq]
        simp [hInstr]
      exact
        Assembly.Program.target_resolves_of_accepted
          hAccepted hInstrGlobal hInstrTarget
    · intro internal hInternal
      have hInstr :
          Assembly.Instr.label internal ∈ fragment.code :=
        TypedCfg.Block.definedLabel_instr_mem_of_lower?
          fragment.lower hInternal
      have hInstrGlobal :
          Assembly.Instr.label internal ∈ target := by
        rw [fragment.target_eq]
        simp [hInstr]
      exact
        Assembly.Program.labelPc_exists_of_mem_labels target
          (Assembly.Program.mem_labels_of_label_mem hInstrGlobal)
  rcases
      TypedCfg.Block.lower?_starts_with_label fragment.lower with
    ⟨tail, hCode⟩
  have hEntryLabel :
      target.labelPc block.label = some fragment.pre.byteLength := by
    have hNodup :
        (fragment.pre ++
          Assembly.Instr.label block.label ::
            (tail ++ fragment.post)).labels.Nodup := by
      simpa [fragment.target_eq, hCode, List.append_assoc] using hLabels
    have hAt :=
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        fragment.pre (tail ++ fragment.post) hNodup
    simpa [fragment.target_eq, hCode, List.append_assoc] using hAt
  have hEntryPcEq : entryPc = fragment.pre.byteLength := by
    rw [hEntryLabel] at hLabelPc
    exact (Option.some.inj hLabelPc).symm
  have hStatePc : state.pc = fragment.pre.pcAfter := by
    calc
      state.pc = EvmYul.UInt256.ofNat entryPc := hPc
      _ = EvmYul.UInt256.ofNat fragment.pre.byteLength := by
        rw [hEntryPcEq]
      _ = fragment.pre.pcAfter := rfl
  have hResolvedFragment :
      Terminator.ResolvedControl
        (fragment.pre ++ fragment.code ++ fragment.post)
        block.term := by
    rw [← fragment.target_eq]
    exact hResolved
  have hLabelsFragment :
      ((fragment.pre ++ fragment.code ++ fragment.post).labels).Nodup := by
    rw [← fragment.target_eq]
    exact hLabels
  have hRun :=
    Block.lower?_eventually
      (block := block) (code := fragment.code)
      (pre := fragment.pre) (post := fragment.post)
      (state := state) fragment.lower hCodeFits hStatePc
      hResolvedFragment hLabelsFragment
  rw [fragment.target_eq]
  simpa [TypedCfg.Program.step, hFind] using hRun

end Program

end Preservation
end TypedCfg
end EvmCompiler
