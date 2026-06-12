import EvmCompiler.Simulation.ResourceReplay
import EvmCompiler.Structured.EffectSemantics

namespace EvmCompiler
namespace Structured
namespace ObserverSemantics

abbrev Trace := Assembly.ResourceTrace
abbrev Observer := Assembly.ResourceObserver
abbrev State :=
  Simulation.ResourceReplay.State Structured.RunState
abbrev Outcome {transcript : Trace} :=
  Structured.OutcomeT (State transcript)

def basicOpObserver? (op : Structured.BasicOp) : Option Observer :=
  Assembly.ResourceObserver.ofPrimOp? op.toPrimOp

def applyObserver {transcript : Trace} (kind : Observer)
    (state : State transcript) :
    Except EVMException (State transcript) :=
  match Simulation.ResourceReplay.consume? kind state with
  | none => Structured.invalid
  | some (value, consumed) =>
      match
          Assembly.ResourceObserver.overwriteTop
            value consumed.source.evm
      with
      | .error err => .error err
      | .ok evm =>
          .ok
            (consumed.withSource
              (consumed.source.withEVM evm))

def stateModel (transcript : Trace) :
    Structured.EffectSemantics.StateModel (State transcript) where
  source state := state.source
  withSource := Simulation.ResourceReplay.State.withSource
  pushReturn state callerStack retc :=
    state.withSource (state.source.pushReturn callerStack retc)
  popReturn? state :=
    match state.source.popReturn? with
    | none => none
    | some (frame, source) => some (frame, state.withSource source)

@[simp] theorem stateModel_source
    {transcript : Trace} (state : State transcript) :
    (stateModel transcript).source state = state.source := rfl

@[simp] theorem stateModel_evm
    {transcript : Trace} (state : State transcript) :
    (stateModel transcript).evm state = state.source.evm := rfl

@[simp] theorem stateModel_returns
    {transcript : Trace} (state : State transcript) :
    (stateModel transcript).returns state = state.source.returns := rfl

@[simp] theorem stateModel_withEVM
    {transcript : Trace} (state : State transcript) (evm : EVMState) :
    (stateModel transcript).withEVM state evm =
      state.withSource (state.source.withEVM evm) := rfl

theorem stateModel_popReturn?_eq_some
    {transcript : Trace} {state returned : State transcript}
    {frame : Structured.ReturnDest}
    (hPop :
      (stateModel transcript).popReturn? state =
        some (frame, returned)) :
    state.source.popReturn? = some (frame, returned.source) ∧
      returned.cursor = state.cursor := by
  unfold stateModel at hPop
  cases hSource : state.source.popReturn? with
  | none =>
      simp [hSource] at hPop
  | some result =>
      rcases result with ⟨sourceFrame, sourceReturned⟩
      simp [hSource] at hPop
      rcases hPop with ⟨rfl, rfl⟩
      exact
        ⟨by simpa using hSource,
          by simp⟩

def handler (transcript : Trace) :
    Structured.EffectSemantics.Handler (State transcript) where
  afterInstr instr state :=
    match instr with
    | .op op =>
        match basicOpObserver? op with
        | none => .ok state
        | some kind => applyObserver kind state
    | .push _ | .bindLocals _ _ | .bindScratch _ _ _ =>
        .ok state

theorem applyObserver_stack_length
    {transcript : Trace} {kind : Observer}
    {state final : State transcript}
    (hApply : applyObserver kind state = .ok final) :
    final.source.evm.stack.length =
      state.source.evm.stack.length := by
  unfold applyObserver at hApply
  cases hConsume :
      Simulation.ResourceReplay.consume? kind state with
  | none =>
      simp [hConsume, Structured.invalid] at hApply
  | some consumed =>
      rcases consumed with ⟨value, consumedState⟩
      simp [hConsume] at hApply
      cases hOverwrite :
          Assembly.ResourceObserver.overwriteTop
            value consumedState.source.evm with
      | error err =>
          simp [hOverwrite] at hApply
      | ok evm =>
          simp [hOverwrite] at hApply
          cases hApply
          change
            evm.stack.length = state.source.evm.stack.length
          rw [
            Assembly.ResourceObserver.overwriteTop_stack_length
              hOverwrite,
            Simulation.ResourceReplay.consume?_source hConsume]

theorem handler_stack_length
    {transcript : Trace} {instr : Structured.BasicInstr}
    {state final : State transcript}
    (hAfter :
      (handler transcript).afterInstr instr state = .ok final) :
    final.source.evm.stack.length =
      state.source.evm.stack.length := by
  cases instr with
  | push value | bindLocals value names
  | bindScratch value name slot =>
      simp [handler] at hAfter
      cases hAfter
      rfl
  | op op =>
      cases hObserver : basicOpObserver? op with
      | none =>
          simp [handler, hObserver] at hAfter
          cases hAfter
          rfl
      | some kind =>
          simp only [handler, hObserver] at hAfter
          exact applyObserver_stack_length hAfter

namespace Outcome

def ConsumedExactly {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Prop :=
  outcome.state.ConsumedExactly

def observed {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Trace :=
  outcome.state.observed

def remaining {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Trace :=
  outcome.state.remaining

def Nonhalting {transcript : Trace}
    (outcome : Outcome (transcript := transcript)) : Prop :=
  match outcome.mode with
  | .halt _ => False
  | _ => True

@[simp] theorem regular_state {transcript : Trace}
    (state : State transcript) :
    (Structured.EffectSemantics.Outcome.regular state).state = state := rfl

@[simp] theorem regular_mode {transcript : Trace}
    (state : State transcript) :
    (Structured.EffectSemantics.Outcome.regular state).mode =
      Structured.Mode.regular := rfl

@[simp] theorem brk_state {transcript : Trace}
    (state : State transcript) :
    (Structured.EffectSemantics.Outcome.brk state).state = state := rfl

@[simp] theorem brk_mode {transcript : Trace}
    (state : State transcript) :
    (Structured.EffectSemantics.Outcome.brk state).mode =
      Structured.Mode.brk := rfl

@[simp] theorem cont_state {transcript : Trace}
    (state : State transcript) :
    (Structured.EffectSemantics.Outcome.cont state).state = state := rfl

@[simp] theorem cont_mode {transcript : Trace}
    (state : State transcript) :
    (Structured.EffectSemantics.Outcome.cont state).mode =
      Structured.Mode.cont := rfl

@[simp] theorem leave_state {transcript : Trace}
    (state : State transcript) :
    (Structured.EffectSemantics.Outcome.leave state).state = state := rfl

@[simp] theorem leave_mode {transcript : Trace}
    (state : State transcript) :
    (Structured.EffectSemantics.Outcome.leave state).mode =
      Structured.Mode.leave := rfl

@[simp] theorem halt_state {transcript : Trace}
    (kind : Assembly.HaltKind) (state : State transcript) :
    (Structured.EffectSemantics.Outcome.halt kind state).state = state := rfl

@[simp] theorem halt_mode {transcript : Trace}
    (kind : Assembly.HaltKind) (state : State transcript) :
    (Structured.EffectSemantics.Outcome.halt kind state).mode =
      Structured.Mode.halt kind := rfl

theorem observed_eq_transcript_of_consumedExactly
    {transcript : Trace} {outcome : Outcome (transcript := transcript)}
    (hConsumed : outcome.ConsumedExactly) :
    outcome.observed = transcript :=
  Simulation.ResourceReplay.State.observed_eq_transcript_of_consumedExactly
    hConsumed

theorem remaining_eq_nil_of_consumedExactly
    {transcript : Trace} {outcome : Outcome (transcript := transcript)}
    (hConsumed : outcome.ConsumedExactly) :
    outcome.remaining = [] :=
  Simulation.ResourceReplay.State.remaining_eq_nil_of_consumedExactly
    hConsumed

end Outcome

namespace Code

def run {transcript : Trace} (code : Structured.Code)
    (state : State transcript) :
    Except EVMException (State transcript) :=
  Structured.EffectSemantics.Code.run
    (stateModel transcript) (handler transcript) code state

def withHidden {transcript : Trace} (state : State transcript)
    (hidden : EvmYul.Stack Word) : State transcript :=
  state.withSource
    (state.source.withEVM
      { state.source.evm with
        stack := state.source.evm.stack ++ hidden })

def FrameSafe (code : Structured.Code) : Prop :=
  ∀ (transcript : Trace) (state final : State transcript)
      (hidden : EvmYul.Stack Word),
    run code state = .ok final →
      run code (withHidden state hidden) =
        .ok (withHidden final hidden)

/--
Semantic converse to `FrameSafe`.

If code succeeds with a compiler-owned hidden stack suffix, the same source
code succeeds without that suffix and the hidden execution is exactly the
framed source result. Backward compiler adequacy requires this source-facing
property at procedure boundaries.
-/
def FrameReflecting (code : Structured.Code) : Prop :=
  ∀ (transcript : Trace) (state framedFinal : State transcript)
      (hidden : EvmYul.Stack Word),
    run code (withHidden state hidden) = .ok framedFinal →
      ∃ final,
        run code state = .ok final ∧
          framedFinal = withHidden final hidden

@[simp] theorem withHidden_source
    {transcript : Trace} (state : State transcript)
    (hidden : EvmYul.Stack Word) :
    (withHidden state hidden).source =
      state.source.withEVM
        { state.source.evm with
          stack := state.source.evm.stack ++ hidden } := rfl

@[simp] theorem withHidden_cursor
    {transcript : Trace} (state : State transcript)
    (hidden : EvmYul.Stack Word) :
    (withHidden state hidden).cursor = state.cursor := rfl

@[simp] theorem withHidden_remaining
    {transcript : Trace} (state : State transcript)
    (hidden : EvmYul.Stack Word) :
    (withHidden state hidden).remaining = state.remaining := rfl

def runCondition {transcript : Trace} (code : Structured.Code)
    (state : State transcript) :
    Except EVMException (State transcript × Bool) :=
  Structured.EffectSemantics.Code.runCondition
    (stateModel transcript) (handler transcript) code state

theorem run_cons_eq_run_single_bind
    {transcript : Trace} (instr : Structured.BasicInstr)
    (rest : Structured.Code) (state : State transcript) :
    run (instr :: rest) state =
      (run [instr] state).bind (run rest) :=
  Structured.EffectSemantics.Code.run_cons_eq_run_single_bind
    (stateModel transcript) (handler transcript) instr rest state

theorem run_returns_eq
    {transcript : Trace} {code : Structured.Code}
    {state final : State transcript}
    (hRun : run code state = .ok final) :
    final.source.returns = state.source.returns := by
  induction code generalizing state final with
  | nil =>
      simp [run, Structured.EffectSemantics.Code.run] at hRun
      cases hRun
      rfl
  | cons instr rest ih =>
      unfold run Structured.EffectSemantics.Code.run at hRun
      simp only [stateModel_evm, stateModel_withEVM] at hRun
      cases hStep : instr.step state.source.evm with
      | error err =>
          simp [hStep, Bind.bind, Except.bind] at hRun
      | ok evm =>
          simp only [hStep, Bind.bind, Except.bind] at hRun
          cases hAfter :
              (handler transcript).afterInstr instr
                (state.withSource (state.source.withEVM evm)) with
          | error err =>
              rw [hAfter] at hRun
              contradiction
          | ok middle =>
              rw [hAfter] at hRun
              have hMiddle :
                  middle.source.returns = state.source.returns := by
                cases instr with
                | push value | bindLocals value names
                | bindScratch value name slot =>
                    simp [handler] at hAfter
                    cases hAfter
                    rfl
                | op op =>
                    cases hObserver : basicOpObserver? op with
                    | none =>
                        simp [handler, hObserver] at hAfter
                        cases hAfter
                        rfl
                    | some kind =>
                        simp only [handler, hObserver] at hAfter
                        unfold applyObserver at hAfter
                        cases hConsume :
                            Simulation.ResourceReplay.consume? kind
                              (state.withSource
                                (state.source.withEVM evm)) with
                        | none =>
                            simp [hConsume, Structured.invalid] at hAfter
                        | some consumed =>
                            rcases consumed with ⟨value, consumed⟩
                            simp [hConsume] at hAfter
                            cases hOverwrite :
                                Assembly.ResourceObserver.overwriteTop
                                  value consumed.source.evm with
                            | error err =>
                                simp [hOverwrite] at hAfter
                            | ok observed =>
                                simp [hOverwrite] at hAfter
                                cases hAfter
                                rw [
                                  Simulation.ResourceReplay.consume?_source
                                    hConsume]
                                rfl
              exact (ih hRun).trans hMiddle

theorem runCondition_returns_eq
    {transcript : Trace} {code : Structured.Code}
    {state final : State transcript} {cond : Bool}
    (hRun : runCondition code state = .ok (final, cond)) :
    final.source.returns = state.source.returns := by
  unfold runCondition Structured.EffectSemantics.Code.runCondition at hRun
  cases hCode :
      Structured.EffectSemantics.Code.run
        (stateModel transcript) (handler transcript) code state with
  | error err =>
      simp [hCode, Bind.bind, Except.bind] at hRun
  | ok middle =>
      simp only [hCode, Bind.bind, Except.bind] at hRun
      unfold Structured.EffectSemantics.Code.popCondition at hRun
      cases hPop : middle.source.evm.stack.pop with
      | none =>
          simp [hPop] at hRun
      | some result =>
          rcases result with ⟨stack, value⟩
          simp [hPop] at hRun
          have hReturns :
              middle.source.returns = state.source.returns :=
            run_returns_eq (by simpa [run] using hCode)
          rcases hRun with ⟨rfl, rfl⟩
          exact hReturns

end Code

namespace Block

abbrev Eval {transcript : Trace} :=
  Structured.EffectSemantics.Block.Eval
    (stateModel transcript) (handler transcript)

end Block

namespace Stmt

abbrev Eval {transcript : Trace} :=
  Structured.EffectSemantics.Stmt.Eval
    (stateModel transcript) (handler transcript)

end Stmt

mutual

  inductive Block.FrameSafe : Structured.Block → Prop where
    | nil : Block.FrameSafe { stmts := [] }
    | cons {stmt : Structured.Stmt} {rest : List Structured.Stmt}
        (hStmt : Stmt.FrameSafe stmt)
        (hRest : Block.FrameSafe { stmts := rest }) :
        Block.FrameSafe { stmts := stmt :: rest }

  inductive Stmt.FrameSafe : Structured.Stmt → Prop where
    | code {code : Structured.Code} (hCode : Code.FrameSafe code) :
        Stmt.FrameSafe (.code code)
    | if_ {cond : Structured.Code} {body : Structured.Block}
        (hCond : Code.FrameSafe cond)
        (hBody : Block.FrameSafe body) :
        Stmt.FrameSafe (.if_ cond body)
    | switch {scrutinee : Structured.Code}
        {cases : List (Word × Structured.Block)}
        {defaultBody : Option Structured.Block}
        (hScrutinee : Code.FrameSafe scrutinee)
        (hCases :
          ∀ value body, (value, body) ∈ cases →
            Block.FrameSafe body)
        (hDefault :
          ∀ body, defaultBody = some body →
            Block.FrameSafe body) :
        Stmt.FrameSafe (.switch scrutinee cases defaultBody)
    | for_ {init post body : Structured.Block}
        {cond : Structured.Code}
        (hInit : Block.FrameSafe init)
        (hCond : Code.FrameSafe cond)
        (hPost : Block.FrameSafe post)
        (hBody : Block.FrameSafe body) :
        Stmt.FrameSafe (.for_ init cond post body)
    | brk : Stmt.FrameSafe .brk
    | cont : Stmt.FrameSafe .cont
    | leave : Stmt.FrameSafe .leave
    | call {name : Structured.Name} : Stmt.FrameSafe (.call name)
    | terminal {kind : Assembly.HaltKind} :
        Stmt.FrameSafe (.terminal kind)

end

mutual

  /--
  Structural source contract collecting backward frame reflection for every
  straight-line fragment nested in a block.
  -/
  inductive Block.FrameReflecting : Structured.Block → Prop where
    | nil : Block.FrameReflecting { stmts := [] }
    | cons {stmt : Structured.Stmt} {rest : List Structured.Stmt}
        (hStmt : Stmt.FrameReflecting stmt)
        (hRest : Block.FrameReflecting { stmts := rest }) :
        Block.FrameReflecting { stmts := stmt :: rest }

  inductive Stmt.FrameReflecting : Structured.Stmt → Prop where
    | code {code : Structured.Code}
        (hCode : Code.FrameReflecting code) :
        Stmt.FrameReflecting (.code code)
    | if_ {cond : Structured.Code} {body : Structured.Block}
        (hCond : Code.FrameReflecting cond)
        (hBody : Block.FrameReflecting body) :
        Stmt.FrameReflecting (.if_ cond body)
    | switch {scrutinee : Structured.Code}
        {cases : List (Word × Structured.Block)}
        {defaultBody : Option Structured.Block}
        (hScrutinee : Code.FrameReflecting scrutinee)
        (hCases :
          ∀ value body, (value, body) ∈ cases →
            Block.FrameReflecting body)
        (hDefault :
          ∀ body, defaultBody = some body →
            Block.FrameReflecting body) :
        Stmt.FrameReflecting (.switch scrutinee cases defaultBody)
    | for_ {init post body : Structured.Block}
        {cond : Structured.Code}
        (hInit : Block.FrameReflecting init)
        (hCond : Code.FrameReflecting cond)
        (hPost : Block.FrameReflecting post)
        (hBody : Block.FrameReflecting body) :
        Stmt.FrameReflecting (.for_ init cond post body)
    | brk : Stmt.FrameReflecting .brk
    | cont : Stmt.FrameReflecting .cont
    | leave : Stmt.FrameReflecting .leave
    | call {name : Structured.Name} :
        Stmt.FrameReflecting (.call name)
    | terminal {kind : Assembly.HaltKind} :
        Stmt.FrameReflecting (.terminal kind)

end

namespace For

abbrev Eval {transcript : Trace} :=
  Structured.EffectSemantics.For.Eval
    (stateModel transcript) (handler transcript)

end For

mutual

  theorem Block.Eval.returns_eq_of_nonhalting
      {transcript : Trace} {program : Structured.Program}
      {fuel : Nat} {block : Structured.Block}
      {state : State transcript}
      {outcome : Outcome (transcript := transcript)}
      (hEval : Block.Eval program fuel block state outcome)
      (hNonhalting : outcome.Nonhalting) :
      outcome.state.source.returns = state.source.returns := by
    cases hEval with
    | nil =>
        rfl
    | cons_regular hStmt hRest =>
        exact
          (Block.Eval.returns_eq_of_nonhalting
            hRest hNonhalting).trans
            (Stmt.Eval.returns_eq_of_nonhalting hStmt (by
              simp [Outcome.Nonhalting]))
    | cons_brk hStmt =>
        exact
          Stmt.Eval.returns_eq_of_nonhalting hStmt (by
            simp [Outcome.Nonhalting])
    | cons_cont hStmt =>
        exact
          Stmt.Eval.returns_eq_of_nonhalting hStmt (by
            simp [Outcome.Nonhalting])
    | cons_leave hStmt =>
        exact
          Stmt.Eval.returns_eq_of_nonhalting hStmt (by
            simp [Outcome.Nonhalting])
    | cons_halt hStmt =>
        simp [Outcome.Nonhalting] at hNonhalting
  termination_by fuel

  theorem Stmt.Eval.returns_eq_of_nonhalting
      {transcript : Trace} {program : Structured.Program}
      {fuel : Nat} {stmt : Structured.Stmt}
      {state : State transcript}
      {outcome : Outcome (transcript := transcript)}
      (hEval : Stmt.Eval program fuel stmt state outcome)
      (hNonhalting : outcome.Nonhalting) :
      outcome.state.source.returns = state.source.returns := by
    cases hEval with
    | code hCode =>
        exact Code.run_returns_eq hCode
    | if_false hCond =>
        exact Code.runCondition_returns_eq hCond
    | if_true hCond hBody =>
        exact
          (Block.Eval.returns_eq_of_nonhalting
            hBody hNonhalting).trans
            (Code.runCondition_returns_eq hCond)
    | switch_none hScrutinee hPop hSelect =>
        simpa using Code.run_returns_eq hScrutinee
    | switch_some hScrutinee hPop hStateAfterPop hSelect hBody =>
        have hBodyReturns :=
          Block.Eval.returns_eq_of_nonhalting hBody hNonhalting
        exact
          hBodyReturns.trans
            (by
              subst hStateAfterPop
              simpa using Code.run_returns_eq hScrutinee)
    | for_init_regular hInit hLoop =>
        exact
          (For.Eval.returns_eq_of_nonhalting
            hLoop hNonhalting).trans
            (Block.Eval.returns_eq_of_nonhalting hInit (by
              simp [Outcome.Nonhalting]))
    | for_init_leave hInit =>
        exact
          Block.Eval.returns_eq_of_nonhalting hInit (by
            simp [Outcome.Nonhalting])
    | for_init_halt hInit =>
        simp [Outcome.Nonhalting] at hNonhalting
    | brk =>
        rfl
    | cont =>
        rfl
    | leave hReturns =>
        rfl
    | call_regular hLookup hSplit hBody hPop hAttach =>
        have hBodyReturns :=
          Block.Eval.returns_eq_of_nonhalting hBody (by
            simp [Outcome.Nonhalting])
        simp [stateModel] at hBodyReturns
        obtain ⟨hSourcePop, hCursor⟩ :=
          stateModel_popReturn?_eq_some hPop
        unfold Structured.RunState.popReturn? at hSourcePop
        rw [hBodyReturns] at hSourcePop
        simp at hSourcePop
        simpa using
          (congrArg Structured.RunState.returns hSourcePop.2).symm
    | call_leave hLookup hSplit hBody hPop hAttach =>
        have hBodyReturns :=
          Block.Eval.returns_eq_of_nonhalting hBody (by
            simp [Outcome.Nonhalting])
        simp [stateModel] at hBodyReturns
        obtain ⟨hSourcePop, hCursor⟩ :=
          stateModel_popReturn?_eq_some hPop
        unfold Structured.RunState.popReturn? at hSourcePop
        rw [hBodyReturns] at hSourcePop
        simp at hSourcePop
        simpa using
          (congrArg Structured.RunState.returns hSourcePop.2).symm
    | call_halt hLookup hSplit hBody =>
        simp [Outcome.Nonhalting] at hNonhalting
    | terminal hStep =>
        simp [Outcome.Nonhalting] at hNonhalting
  termination_by fuel

  theorem For.Eval.returns_eq_of_nonhalting
      {transcript : Trace} {program : Structured.Program}
      {fuel : Nat} {cond : Structured.Code}
      {post body : Structured.Block}
      {state : State transcript}
      {outcome : Outcome (transcript := transcript)}
      (hEval : For.Eval program fuel cond post body state outcome)
      (hNonhalting : outcome.Nonhalting) :
      outcome.state.source.returns = state.source.returns := by
    cases hEval with
    | false hCond =>
        exact Code.runCondition_returns_eq hCond
    | body_brk hCond hBody =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hBody (by
            simp [Outcome.Nonhalting])).trans
            (Code.runCondition_returns_eq hCond)
    | body_leave hCond hBody =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hBody (by
            simp [Outcome.Nonhalting])).trans
            (Code.runCondition_returns_eq hCond)
    | body_halt hCond hBody =>
        simp [Outcome.Nonhalting] at hNonhalting
    | regular_post_regular hCond hBody hPost hLoop =>
        exact
          (For.Eval.returns_eq_of_nonhalting
            hLoop hNonhalting).trans
            ((Block.Eval.returns_eq_of_nonhalting hPost (by
              simp [Outcome.Nonhalting])).trans
              ((Block.Eval.returns_eq_of_nonhalting hBody (by
                simp [Outcome.Nonhalting])).trans
                (Code.runCondition_returns_eq hCond)))
    | cont_post_regular hCond hBody hPost hLoop =>
        exact
          (For.Eval.returns_eq_of_nonhalting
            hLoop hNonhalting).trans
            ((Block.Eval.returns_eq_of_nonhalting hPost (by
              simp [Outcome.Nonhalting])).trans
              ((Block.Eval.returns_eq_of_nonhalting hBody (by
                simp [Outcome.Nonhalting])).trans
                (Code.runCondition_returns_eq hCond)))
    | regular_post_leave hCond hBody hPost =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hPost (by
            simp [Outcome.Nonhalting])).trans
            ((Block.Eval.returns_eq_of_nonhalting hBody (by
              simp [Outcome.Nonhalting])).trans
              (Code.runCondition_returns_eq hCond))
    | cont_post_leave hCond hBody hPost =>
        exact
          (Block.Eval.returns_eq_of_nonhalting hPost (by
            simp [Outcome.Nonhalting])).trans
            ((Block.Eval.returns_eq_of_nonhalting hBody (by
              simp [Outcome.Nonhalting])).trans
              (Code.runCondition_returns_eq hCond))
    | regular_post_halt hCond hBody hPost =>
        simp [Outcome.Nonhalting] at hNonhalting
    | cont_post_halt hCond hBody hPost =>
        simp [Outcome.Nonhalting] at hNonhalting
  termination_by fuel

end

namespace CallStack

/--
An observer-replayed procedure body that returns regularly pops exactly the
source frame introduced at its call boundary.
-/
theorem poppedFrame_eq_of_regular_eval
    {transcript : Trace} {program : Structured.Program}
    {fuel retc : Nat} {body : Structured.Block}
    {source bodyState returned : State transcript}
    {args callerStack : EvmYul.Stack Word}
    {frame : Structured.ReturnDest}
    (hBody :
      Block.Eval program fuel body
        ((stateModel transcript).pushReturn
          ((stateModel transcript).withEVM source
            { source.source.evm with stack := args })
          callerStack retc)
        (Structured.EffectSemantics.Outcome.regular bodyState))
    (hPop :
      (stateModel transcript).popReturn? bodyState =
        some (frame, returned)) :
    frame = { callerStack := callerStack, retc := retc } := by
  have hReturns :=
    Block.Eval.returns_eq_of_nonhalting hBody (by
      simp [Outcome.Nonhalting])
  simp only [Outcome.regular_state, stateModel,
    Simulation.ResourceReplay.State.withSource_source,
    Structured.RunState.pushReturn_returns,
    Structured.RunState.withEVM_returns] at hReturns
  obtain ⟨hSourcePop, _hCursor⟩ :=
    stateModel_popReturn?_eq_some hPop
  unfold Structured.RunState.popReturn? at hSourcePop
  rw [hReturns] at hSourcePop
  simp at hSourcePop
  exact hSourcePop.1.symm

/--
An observer-replayed procedure body that exits with `leave` pops the same
source call frame as ordinary fallthrough.
-/
theorem poppedFrame_eq_of_leave_eval
    {transcript : Trace} {program : Structured.Program}
    {fuel retc : Nat} {body : Structured.Block}
    {source bodyState returned : State transcript}
    {args callerStack : EvmYul.Stack Word}
    {frame : Structured.ReturnDest}
    (hBody :
      Block.Eval program fuel body
        ((stateModel transcript).pushReturn
          ((stateModel transcript).withEVM source
            { source.source.evm with stack := args })
          callerStack retc)
        (Structured.EffectSemantics.Outcome.leave bodyState))
    (hPop :
      (stateModel transcript).popReturn? bodyState =
        some (frame, returned)) :
    frame = { callerStack := callerStack, retc := retc } := by
  have hReturns :=
    Block.Eval.returns_eq_of_nonhalting hBody (by
      simp [Outcome.Nonhalting])
  simp only [Outcome.leave_state, stateModel,
    Simulation.ResourceReplay.State.withSource_source,
    Structured.RunState.pushReturn_returns,
    Structured.RunState.withEVM_returns] at hReturns
  obtain ⟨hSourcePop, _hCursor⟩ :=
    stateModel_popReturn?_eq_some hPop
  unfold Structured.RunState.popReturn? at hSourcePop
  rw [hReturns] at hSourcePop
  simp at hSourcePop
  exact hSourcePop.1.symm

end CallStack

namespace Proc

def FrameSafe (proc : Structured.Proc) : Prop :=
  ObserverSemantics.Block.FrameSafe proc.body

def FrameReflecting (proc : Structured.Proc) : Prop :=
  ObserverSemantics.Block.FrameReflecting proc.body

end Proc

namespace ProcList

def FrameSafe : List Structured.Proc → Prop
  | [] => True
  | proc :: rest =>
      ObserverSemantics.Proc.FrameSafe proc ∧ FrameSafe rest

theorem FrameSafe_of_lookup?
    {procs : List Structured.Proc} {name : Structured.Name}
    {proc : Structured.Proc}
    (hFrameSafe : FrameSafe procs)
    (hLookup : Structured.ProcList.lookup? name procs = some proc) :
    ObserverSemantics.Proc.FrameSafe proc := by
  induction procs with
  | nil =>
      simp [Structured.ProcList.lookup?] at hLookup
  | cons head rest ih =>
      unfold Structured.ProcList.lookup? at hLookup
      by_cases hName : head.name = name
      · simp [hName] at hLookup
        cases hLookup
        exact hFrameSafe.1
      · simp [hName] at hLookup
        exact ih hFrameSafe.2 hLookup

def FrameReflecting : List Structured.Proc → Prop
  | [] => True
  | proc :: rest =>
      ObserverSemantics.Proc.FrameReflecting proc ∧
        FrameReflecting rest

theorem FrameReflecting_of_lookup?
    {procs : List Structured.Proc} {name : Structured.Name}
    {proc : Structured.Proc}
    (hFrameReflecting : FrameReflecting procs)
    (hLookup : Structured.ProcList.lookup? name procs = some proc) :
    ObserverSemantics.Proc.FrameReflecting proc := by
  induction procs with
  | nil =>
      simp [Structured.ProcList.lookup?] at hLookup
  | cons head rest ih =>
      unfold Structured.ProcList.lookup? at hLookup
      by_cases hName : head.name = name
      · simp [hName] at hLookup
        cases hLookup
        exact hFrameReflecting.1
      · simp [hName] at hLookup
        exact ih hFrameReflecting.2 hLookup

end ProcList

namespace Program

def FrameSafe (program : Structured.Program) : Prop :=
  ProcList.FrameSafe program.procs ∧
    ObserverSemantics.Block.FrameSafe program.body

def FrameReflecting (program : Structured.Program) : Prop :=
  ProcList.FrameReflecting program.procs ∧
    ObserverSemantics.Block.FrameReflecting program.body

theorem procFrameSafe_of_lookup?
    {program : Structured.Program} {name : Structured.Name}
    {proc : Structured.Proc}
    (hFrameSafe : FrameSafe program)
    (hLookup :
      Structured.ProcList.lookup? name program.procs = some proc) :
    ObserverSemantics.Proc.FrameSafe proc :=
  ProcList.FrameSafe_of_lookup? hFrameSafe.1 hLookup

theorem procFrameReflecting_of_lookup?
    {program : Structured.Program} {name : Structured.Name}
    {proc : Structured.Proc}
    (hFrameReflecting : FrameReflecting program)
    (hLookup :
      Structured.ProcList.lookup? name program.procs = some proc) :
    ObserverSemantics.Proc.FrameReflecting proc :=
  ProcList.FrameReflecting_of_lookup? hFrameReflecting.1 hLookup

def initialState (initial : Structured.RunState) (transcript : Trace) :
    State transcript :=
  { source := initial }

def runState (fuel : Nat) (program : Structured.Program)
    {transcript : Trace} (state : State transcript) :
    Except EVMException (Outcome (transcript := transcript)) :=
  Structured.EffectSemantics.Program.runState
    (stateModel transcript) (handler transcript)
    fuel program state

def run (fuel : Nat) (program : Structured.Program)
    (initial : Structured.RunState) (transcript : Trace) :
    Except EVMException (Outcome (transcript := transcript)) :=
  runState fuel program (initialState initial transcript)

def ExactReplay (fuel : Nat) (program : Structured.Program)
    (initial : Structured.RunState) (transcript : Trace)
    (outcome : Outcome (transcript := transcript)) : Prop :=
  run fuel program initial transcript = .ok outcome ∧
    outcome.ConsumedExactly

theorem eval_of_runState
    {fuel : Nat} {program : Structured.Program}
    {transcript : Trace} {state : State transcript}
    {outcome : Outcome (transcript := transcript)}
    (hRun : runState fuel program state = .ok outcome) :
    Block.Eval program fuel program.body state outcome :=
  Structured.EffectSemantics.Program.eval_of_runState hRun

theorem eval_of_run
    {fuel : Nat} {program : Structured.Program}
    {initial : Structured.RunState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hRun : run fuel program initial transcript = .ok outcome) :
    Block.Eval program fuel program.body
      (initialState initial transcript) outcome :=
  eval_of_runState hRun

theorem ExactReplay.eval
    {fuel : Nat} {program : Structured.Program}
    {initial : Structured.RunState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hReplay : ExactReplay fuel program initial transcript outcome) :
    Block.Eval program fuel program.body
      (initialState initial transcript) outcome :=
  eval_of_run hReplay.1

theorem ExactReplay.observed_eq_transcript
    {fuel : Nat} {program : Structured.Program}
    {initial : Structured.RunState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hReplay : ExactReplay fuel program initial transcript outcome) :
    outcome.observed = transcript :=
  Outcome.observed_eq_transcript_of_consumedExactly hReplay.2

theorem ExactReplay.remaining_eq_nil
    {fuel : Nat} {program : Structured.Program}
    {initial : Structured.RunState} {transcript : Trace}
    {outcome : Outcome (transcript := transcript)}
    (hReplay : ExactReplay fuel program initial transcript outcome) :
    outcome.remaining = [] :=
  Outcome.remaining_eq_nil_of_consumedExactly hReplay.2

end Program

@[simp] theorem basicOpObserver?_gas :
    basicOpObserver? .gas = some .gas := rfl

@[simp] theorem basicOpObserver?_msize :
    basicOpObserver? .msize = some .msize := rfl

end ObserverSemantics
end Structured
end EvmCompiler
