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

end Preservation
end TypedCfg
end EvmCompiler
