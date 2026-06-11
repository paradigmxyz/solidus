import EvmCompiler.Assembly.Observer
import EvmCompiler.TypedCfg.Preservation

namespace EvmCompiler
namespace TypedCfg
namespace ObserverSemantics

abbrev Trace := Assembly.ResourceTrace

namespace Instr

def runState (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (trace : Trace) :
    Except EVMException (EVMState × Trace) :=
  match TypedCfg.Instr.runState instr shape state with
  | .error err => .error err
  | .ok final =>
      match instr with
      | .prim op =>
          match Assembly.ResourceObserver.ofPrimOp? op with
          | some kind =>
              Assembly.ResourceObserver.applyOracleFromPostState
                kind final trace
          | none => .ok (final, trace)
      | _ => .ok (final, trace)

def runAt (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (trace : Trace) :
    Except EVMException ((EVMState × Shape) × Trace) := do
  let output ←
    (instr.type? shape).elim (.error .InvalidInstruction) .ok
  let (state', trace') ← runState instr shape state trace
  .ok ((state', output), trace')

theorem runAt_map_running
    {instr : TypedCfg.Instr} {shape output : Shape}
    {state : EVMState} {trace : Trace}
    (hType : instr.type? shape = some output) :
    (runAt instr shape state trace).map
        (fun result =>
          (Assembly.StepResult.running result.1.1, result.2)) =
      (runState instr shape state trace).map
        (fun result =>
          (Assembly.StepResult.running result.1, result.2)) := by
  unfold runAt
  rw [hType]
  cases runState instr shape state trace <;> rfl

theorem runState_plain_pc
    {instr : TypedCfg.Instr} {shape : Shape}
    {state final : EVMState} {trace trace' : Trace}
    (hRun : runState instr shape state trace = .ok (final, trace')) :
    ∃ plain,
      TypedCfg.Instr.runState instr shape state = .ok plain ∧
        final.pc = plain.pc := by
  unfold runState at hRun
  cases hPlain : TypedCfg.Instr.runState instr shape state with
  | error err =>
      simp [hPlain] at hRun
  | ok plain =>
      simp only [hPlain] at hRun
      cases instr with
      | prim op =>
        cases hObserver : Assembly.ResourceObserver.ofPrimOp? op with
        | none =>
            simp [hObserver] at hRun
            rcases hRun with ⟨hFinal, _hTrace⟩
            subst final
            refine ⟨plain, ?_, rfl⟩
            simpa only [hPlain]
        | some kind =>
            simp [hObserver] at hRun
            cases hApply :
                Assembly.ResourceObserver.applyOracleFromPostState
                  kind plain trace with
            | error err =>
                rw [hApply] at hRun
                cases hRun
            | ok pair =>
                rcases pair with ⟨oracleState, oracleTrace⟩
                rw [hApply] at hRun
                cases hRun
                exact
                  ⟨plain, by simpa only [hPlain],
                    Assembly.ResourceObserver.applyOracleFromPostState_pc
                      hApply⟩
      | push value =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩
      | returnToken value =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩
      | pop =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩
      | dup depth =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩
      | swap depth =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩
      | bindLocals offset names =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩
      | bindScratch baseDepth name slot =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩
      | relabel target =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩
      | unwind target =>
          change Except.ok (plain, trace) = .ok (final, trace') at hRun
          cases hRun
          exact ⟨final, rfl, rfl⟩

theorem runState_pc_of_lowerAt
    {instr : TypedCfg.Instr} {shape output : Shape}
    {code : Assembly.Program} {state final : EVMState}
    {trace trace' : Trace}
    (hLower : instr.lowerAt? shape = some (code, output))
    (hRun : runState instr shape state trace = .ok (final, trace')) :
    final.pc =
      state.pc + EvmYul.UInt256.ofNat code.byteLength := by
  rcases runState_plain_pc hRun with ⟨plain, hPlain, hPc⟩
  rw [hPc]
  exact Preservation.Instr.runState_pc_of_lowerAt hLower hPlain

end Instr

namespace Block

def runBody : List TypedCfg.Instr → Shape → EVMState → Trace →
    Except EVMException ((EVMState × Shape) × Trace)
  | [], shape, state, trace => .ok ((state, shape), trace)
  | instr :: rest, shape, state, trace => do
      let ((state', shape'), trace') ←
        Instr.runAt instr shape state trace
      runBody rest shape' state' trace'

def run (block : TypedCfg.Block) (state : EVMState) (trace : Trace) :
    Except EVMException (TypedCfg.Outcome × Trace) := do
  let ((state', output), trace') ←
    runBody block.body block.input state trace
  if output = block.output then
    .ok (TypedCfg.Block.runTerm block.output block.term state', trace')
  else
    .error .InvalidInstruction

end Block

namespace Program

def step (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (trace : Trace) :
    Except EVMException (TypedCfg.Outcome × Trace) :=
  match program.findBlock? label with
  | none => .ok (.invalid state, trace)
  | some block => Block.run block state trace

def runN (program : TypedCfg.Program) :
    Nat → Label → EVMState → Trace →
      Except EVMException (TypedCfg.Outcome × Trace)
  | 0, label, state, trace => .ok (.jump label state, trace)
  | fuel + 1, label, state, trace =>
      match step program label state trace with
      | .error err => .error err
      | .ok (outcome, trace') =>
          match outcome with
          | .jump next state' => runN program fuel next state' trace'
          | .fallthrough state' => .ok (.fallthrough state', trace')
          | .returnDispatch state' => .ok (.returnDispatch state', trace')
          | .halt kind state' => .ok (.halt kind state', trace')
          | .invalid state' => .ok (.invalid state', trace')

end Program

end ObserverSemantics
end TypedCfg
end EvmCompiler
