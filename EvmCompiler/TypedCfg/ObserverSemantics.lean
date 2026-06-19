import EvmCompiler.Assembly.Observer
import EvmCompiler.TypedCfg.EffectSemantics

namespace EvmCompiler
namespace TypedCfg
namespace ObserverSemantics

abbrev Trace := Assembly.ResourceTrace

namespace Instr

@[simp] def observer? : TypedCfg.Instr → Option Assembly.ResourceObserver
  | .prim op => Assembly.ResourceObserver.ofPrimOp? op
  | _ => none

@[simp] def handler : EffectSemantics.Handler Trace where
  afterInstr instr final trace :=
    match observer? instr with
    | some kind =>
        Assembly.ResourceObserver.applyOracleFromPostState
          kind final trace
    | none => .ok (final, trace)

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

theorem runAt_of_observer?_eq_none
    {instr : TypedCfg.Instr} {shape : Shape}
    {state : EVMState} {trace : Trace}
    (hObserver : observer? instr = none) :
    runAt instr shape state trace =
      (TypedCfg.Instr.runAt instr shape state).map
        (fun result => (result, trace)) := by
  unfold runAt TypedCfg.Instr.runAt
  cases hType : instr.type? shape with
  | none =>
      simp [hType, Except.map, Bind.bind, Except.bind]
  | some output =>
      cases hRun : TypedCfg.Instr.runState instr shape state with
      | error err =>
          simp [hType, runState, hRun, Except.map,
            Bind.bind, Except.bind]
      | ok final =>
          have hHandler :
              handler.afterInstr instr final trace =
                .ok (final, trace) := by
            change
              (match observer? instr with
              | some kind =>
                  Assembly.ResourceObserver.applyOracleFromPostState
                    kind final trace
              | none => .ok (final, trace)) =
                .ok (final, trace)
            rw [hObserver]
          have hObservedRun :
              runState instr shape state trace =
                .ok (final, trace) := by
            unfold runState
            rw [hRun]
            exact hHandler
          simp [hType, hRun, hObservedRun, Except.map,
            Bind.bind, Except.bind]

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
            simp [observer?, hObserver] at hRun
            rcases hRun with ⟨hFinal, _hTrace⟩
            subst final
            refine ⟨plain, ?_, rfl⟩
            simpa only [hPlain]
        | some kind =>
            simp [observer?, hObserver] at hRun
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
  unfold runBody
  rw [EffectSemantics.Block.runBody_cons]
  rw [← Instr.runAt_eq_effectSemantics]

theorem runBody_of_forall_observer?_eq_none
    {body : List TypedCfg.Instr} {shape : Shape}
    {state : EVMState} {trace : Trace}
    (hSilent :
      ∀ instr, instr ∈ body → Instr.observer? instr = none) :
    runBody body shape state trace =
      (TypedCfg.Block.runBody body shape state).map
        (fun result => (result, trace)) := by
  induction body generalizing shape state trace with
  | nil =>
      rfl
  | cons instr rest ih =>
      rw [runBody_cons,
        Instr.runAt_of_observer?_eq_none
          (hSilent instr (by simp))]
      unfold TypedCfg.Block.runBody
      cases hRun : TypedCfg.Instr.runAt instr shape state with
      | error err =>
          simp [hRun, Except.map, Bind.bind, Except.bind]
      | ok result =>
          rcases result with ⟨state', shape'⟩
          simp only [hRun, Except.map, Bind.bind, Except.bind]
          rw [ih]
          · cases hRest :
                TypedCfg.Block.runBody rest shape' state' <;>
              simp [hRest, Except.map, Bind.bind, Except.bind]
          · intro restInstr hMem
            exact hSilent restInstr (by simp [hMem])

def run (block : TypedCfg.Block) (state : EVMState) (trace : Trace) :
    Except EVMException (TypedCfg.Outcome × Trace) := do
  let ((state', output), trace') ←
    runBody block.body block.input state trace
  if output = block.output then
    let outcome ←
      TypedCfg.Block.runTermChecked block.output block.term state'
    .ok (outcome, trace')
  else
    .error .InvalidInstruction

theorem run_eq_effectSemantics
    (block : TypedCfg.Block) (state : EVMState) (trace : Trace) :
    run block state trace =
      EffectSemantics.Block.run Instr.handler block state trace := by
  simp only [run, EffectSemantics.Block.run, Control.Block.run,
    runBody, EffectSemantics.Block.runBody]
  simp only [StateT.run, StateT.instMonad, StateT.bind,
    StateT.instMonadExceptOf]
  cases hRun :
      Control.Block.runBody
        (EffectSemantics.Instr.runStateM Instr.handler)
        block.body block.input state trace with
  | error err =>
      rfl
  | ok result =>
      rcases result with ⟨pair, trace'⟩
      rcases pair with ⟨state', output⟩
      by_cases hOutput : output = block.output
      · cases hTerm : TypedCfg.Block.runTermChecked
            block.output block.term state' <;>
          simp [hOutput, hTerm, Bind.bind, Except.bind,
            StateT.bind, StateT.pure, MonadExcept.throw,
            MonadExceptOf.throw, StateT.instMonadExceptOf,
            instMonadExceptOfExcept, throwThe, StateT.lift]
      · simp [hOutput]
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
  unfold step EffectSemantics.Program.step Control.Program.step
  cases hFind : program.findBlock? label with
  | none =>
      simp [hFind]
  | some block =>
      simp only [hFind]
      exact Block.run_eq_effectSemantics block state trace

def runN (program : TypedCfg.Program) :
    Nat → Label → EVMState → Trace →
      Except EVMException (TypedCfg.Outcome × Trace) :=
  EffectSemantics.Program.runN Instr.handler program

abbrev Eventually (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (trace : Trace)
    (outcome : TypedCfg.Outcome) (trace' : Trace) : Prop :=
  EffectSemantics.Program.Eventually
    Instr.handler program label state trace outcome trace'

@[simp] theorem runN_zero (program : TypedCfg.Program)
    (label : Label) (state : EVMState) (trace : Trace) :
    runN program 0 label state trace =
      .ok (.jump label state, trace) := rfl

theorem runN_succ (program : TypedCfg.Program)
    (fuel : Nat) (label : Label) (state : EVMState) (trace : Trace) :
    runN program (fuel + 1) label state trace =
      match step program label state trace with
      | .error err => .error err
      | .ok (outcome, trace') =>
          match outcome with
          | .jump next state' =>
              runN program fuel next state' trace'
          | .fallthrough state' =>
              .ok (.fallthrough state', trace')
          | .returnDispatch state' =>
              .ok (.returnDispatch state', trace')
          | .halt kind state' =>
              .ok (.halt kind state', trace')
          | .invalid state' =>
              .ok (.invalid state', trace') := by
  unfold runN
  rw [EffectSemantics.Program.runN_succ]
  rw [step_eq_effectSemantics]
  cases hStep :
      EffectSemantics.Program.step
        Instr.handler program label state trace with
  | error err =>
      simp [hStep]
  | ok result =>
      rcases result with ⟨outcome, trace'⟩
      cases outcome <;> simp [hStep]

/--
Decompose one successful positive-fuel execution into the existing program
step and the remaining execution. This is an inversion theorem for `runN`,
not a second control semantics.
-/
theorem runN_succ_elim
    {program : TypedCfg.Program} {fuel : Nat} {label : Label}
    {state : EVMState} {trace traceFinal : Trace}
    {outcome : TypedCfg.Outcome}
    (hRun :
      runN program (fuel + 1) label state trace =
        .ok (outcome, traceFinal)) :
    ∃ firstOutcome firstTrace,
      step program label state trace =
          .ok (firstOutcome, firstTrace) ∧
        match firstOutcome with
        | .jump next state' =>
            runN program fuel next state' firstTrace =
              .ok (outcome, traceFinal)
        | .fallthrough state' =>
            outcome = .fallthrough state' ∧
              traceFinal = firstTrace
        | .returnDispatch state' =>
            outcome = .returnDispatch state' ∧
              traceFinal = firstTrace
        | .halt kind state' =>
            outcome = .halt kind state' ∧
              traceFinal = firstTrace
        | .invalid state' =>
            outcome = .invalid state' ∧
              traceFinal = firstTrace := by
  rw [runN_succ] at hRun
  cases hStep : step program label state trace with
  | error err =>
      rw [hStep] at hRun
      contradiction
  | ok result =>
      rcases result with ⟨firstOutcome, firstTrace⟩
      rw [hStep] at hRun
      refine ⟨firstOutcome, firstTrace, rfl, ?_⟩
      cases firstOutcome with
      | jump next state' =>
          exact hRun
      | fallthrough state'
      | returnDispatch state'
      | halt kind state'
      | invalid state' =>
          cases hRun
          exact ⟨rfl, rfl⟩

theorem runN_one_of_step
    {program : TypedCfg.Program} {label : Label}
    {state : EVMState} {trace trace' : Trace}
    {outcome : TypedCfg.Outcome}
    (hStep :
      step program label state trace =
        .ok (outcome, trace')) :
    runN program 1 label state trace =
      .ok (outcome, trace') := by
  rw [show 1 = 0 + 1 by rfl, runN_succ, hStep]
  cases outcome <;> rfl

/--
Execution that is residual at a jump composes with any additional target fuel.
-/
theorem runN_add_of_jump
    {program : TypedCfg.Program}
    {firstFuel restFuel : Nat} {entry next : Label}
    {initial middle : EVMState}
    {initialTrace middleTrace : Trace}
    (hFirst :
      runN program firstFuel entry initial initialTrace =
        .ok (.jump next middle, middleTrace)) :
    runN program (firstFuel + restFuel)
        entry initial initialTrace =
      runN program restFuel next middle middleTrace := by
  induction firstFuel generalizing entry initial initialTrace with
  | zero =>
      simp only [runN_zero] at hFirst
      cases hFirst
      simp
  | succ firstFuel ih =>
      have hFirst' := hFirst
      rw [runN_succ] at hFirst'
      cases hStep : step program entry initial initialTrace with
      | error err =>
          rw [hStep] at hFirst'
          contradiction
      | ok result =>
          rcases result with ⟨firstOutcome, firstTrace⟩
          rw [hStep] at hFirst'
          cases firstOutcome with
          | jump afterLabel afterState =>
              rw [show
                Nat.succ firstFuel + restFuel =
                  (firstFuel + restFuel) + 1 by omega,
                runN_succ, hStep]
              exact ih hFirst'
          | fallthrough afterState
          | returnDispatch afterState
          | halt kind afterState
          | invalid afterState =>
              simp at hFirst'

/--
Once a fuel-indexed CFG run has halted, granting additional fuel does not
change its outcome or observer trace.
-/
theorem runN_add_of_halt
    {program : TypedCfg.Program}
    {firstFuel restFuel : Nat} {entry : Label}
    {initial final : EVMState}
    {initialTrace finalTrace : Trace} {kind : Assembly.HaltKind}
    (hFirst :
      runN program firstFuel entry initial initialTrace =
        .ok (.halt kind final, finalTrace)) :
    runN program (firstFuel + restFuel)
        entry initial initialTrace =
      .ok (.halt kind final, finalTrace) := by
  induction firstFuel generalizing entry initial initialTrace with
  | zero =>
      simp only [runN_zero] at hFirst
      cases hFirst
  | succ firstFuel ih =>
      have hFirst' := hFirst
      rw [runN_succ] at hFirst'
      cases hStep : step program entry initial initialTrace with
      | error err =>
          rw [hStep] at hFirst'
          contradiction
      | ok result =>
          rcases result with ⟨firstOutcome, firstTrace⟩
          rw [hStep] at hFirst'
          rw [show
            Nat.succ firstFuel + restFuel =
              (firstFuel + restFuel) + 1 by omega,
            runN_succ, hStep]
          cases firstOutcome with
          | jump next state' =>
              exact ih hFirst'
          | halt firstKind state' =>
              cases hFirst'
              rfl
          | fallthrough state'
          | returnDispatch state'
          | invalid state' =>
              simp at hFirst'

namespace Eventually

theorem residual (program : TypedCfg.Program) (label : Label)
    (state : EVMState) (trace : Trace) :
    Eventually program label state trace (.jump label state) trace :=
  EffectSemantics.Program.Eventually.residual
    Instr.handler program label state trace

theorem of_runN
    {program : TypedCfg.Program} {fuel : Nat} {label : Label}
    {state : EVMState} {trace trace' : Trace}
    {outcome : TypedCfg.Outcome}
    (hRun :
      runN program fuel label state trace =
        .ok (outcome, trace')) :
    Eventually program label state trace outcome trace' :=
  EffectSemantics.Program.Eventually.of_runN hRun

theorem bind_jump
    {program : TypedCfg.Program} {entry next : Label}
    {initial middle : EVMState}
    {initialTrace middleTrace finalTrace : Trace}
    {outcome : TypedCfg.Outcome}
    (hFirst :
      Eventually program entry initial initialTrace
        (.jump next middle) middleTrace)
    (hNext :
      Eventually program next middle middleTrace
        outcome finalTrace) :
    Eventually program entry initial initialTrace
      outcome finalTrace :=
  EffectSemantics.Program.Eventually.bind_jump hFirst hNext

end Eventually

end Program

end ObserverSemantics
end TypedCfg
end EvmCompiler
