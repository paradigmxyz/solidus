import EvmCompiler.Assembly.Observer
import EvmCompiler.TypedCfg.EffectSemantics

namespace EvmCompiler
namespace TypedCfg
namespace ObserverSemantics

abbrev Trace := Assembly.ResourceTrace

namespace Instr

@[simp] def handler : EffectSemantics.Handler Trace where
  afterInstr instr final trace :=
    match instr with
    | .prim op =>
        match Assembly.ResourceObserver.ofPrimOp? op with
        | some kind =>
            Assembly.ResourceObserver.applyOracleFromPostState
              kind final trace
        | none => .ok (final, trace)
    | _ => .ok (final, trace)

def runState (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (trace : Trace) :
    Except EVMException (EVMState × Trace) :=
  match TypedCfg.Instr.runState instr shape state with
  | .error err => .error err
  | .ok final => handler.afterInstr instr final trace

def runAt (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (trace : Trace) :
    Except EVMException ((EVMState × Shape) × Trace) := do
  let output ←
    (instr.type? shape).elim (.error .InvalidInstruction) .ok
  let (state', trace') ← runState instr shape state trace
  .ok ((state', output), trace')

theorem runState_eq_effectSemantics
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (trace : Trace) :
    runState instr shape state trace =
      EffectSemantics.Instr.runState handler instr shape state trace := by
  unfold runState EffectSemantics.Instr.runState
  cases TypedCfg.Instr.runState instr shape state <;> rfl

theorem runAt_eq_effectSemantics
    (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (trace : Trace) :
    runAt instr shape state trace =
      EffectSemantics.Instr.runAt handler instr shape state trace := by
  unfold runAt EffectSemantics.Instr.runAt
  rw [runState_eq_effectSemantics]

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
      simp [hPlain, Bind.bind, Except.bind] at hRun
  | ok plain =>
      simp only [hPlain, handler, Bind.bind, Except.bind] at hRun
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

end Instr

namespace Block

def runBody : List TypedCfg.Instr → Shape → EVMState → Trace →
    Except EVMException ((EVMState × Shape) × Trace) :=
  EffectSemantics.Block.runBody Instr.handler

theorem runBody_eq_effectSemantics
    (body : List TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (trace : Trace) :
    runBody body shape state trace =
      EffectSemantics.Block.runBody
        Instr.handler body shape state trace := by
  rfl

@[simp] theorem runBody_nil (shape : Shape) (state : EVMState)
    (trace : Trace) :
    runBody [] shape state trace = .ok ((state, shape), trace) := rfl

@[simp] theorem runBody_cons (instr : TypedCfg.Instr)
    (rest : List TypedCfg.Instr) (shape : Shape)
    (state : EVMState) (trace : Trace) :
    runBody (instr :: rest) shape state trace =
      (do
        let ((state', shape'), trace') ←
          Instr.runAt instr shape state trace
        runBody rest shape' state' trace') := by
  change
    (do
      let ((state', shape'), trace') ←
        EffectSemantics.Instr.runAt
          Instr.handler instr shape state trace
      EffectSemantics.Block.runBody
        Instr.handler rest shape' state' trace') = _
  rw [← Instr.runAt_eq_effectSemantics]
  simp only [runBody_eq_effectSemantics]

def run (block : TypedCfg.Block) (state : EVMState) (trace : Trace) :
    Except EVMException (TypedCfg.Outcome × Trace) := do
  let ((state', output), trace') ←
    runBody block.body block.input state trace
  if output = block.output then
    .ok (TypedCfg.Block.runTerm block.output block.term state', trace')
  else
    .error .InvalidInstruction

theorem run_eq_effectSemantics
    (block : TypedCfg.Block) (state : EVMState) (trace : Trace) :
    run block state trace =
      EffectSemantics.Block.run Instr.handler block state trace := by
  rfl

end Block

namespace Program

def step (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (trace : Trace) :
    Except EVMException (TypedCfg.Outcome × Trace) :=
  match program.findBlock? label with
  | none => .ok (.invalid state, trace)
  | some block => Block.run block state trace

theorem step_eq_effectSemantics
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (trace : Trace) :
    step program label state trace =
      EffectSemantics.Program.step Instr.handler
        program label state trace := by
  rfl

def runN (program : TypedCfg.Program) :
    Nat → Label → EVMState → Trace →
      Except EVMException (TypedCfg.Outcome × Trace) :=
  EffectSemantics.Program.runN Instr.handler program

end Program

end ObserverSemantics
end TypedCfg
end EvmCompiler
