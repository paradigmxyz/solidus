import EvmCompiler.TypedCfg.Typing
import EvmCompiler.Assembly.Semantics

namespace EvmCompiler
namespace TypedCfg

abbrev EVMState := Assembly.EVMState
abbrev EVMException := Assembly.EVMException

inductive Outcome where
  | fallthrough (state : EVMState)
  | jump (target : Label) (state : EVMState)
  | returnDispatch (state : EVMState)
  | halt (kind : Assembly.HaltKind) (state : EVMState)
  | invalid (state : EVMState)

namespace Instr

def runPops : Nat → EVMState → Except EVMException EVMState
  | 0, state => .ok state
  | count + 1, state => do
      let state' ← Assembly.PrimOp.pop.step state
      runPops count state'

def runState (instr : Instr) (shape : Shape) (state : EVMState) :
    Except EVMException EVMState :=
  match instr with
  | .push value =>
      .ok
        (state.replaceStackAndIncrPC
          (state.stack.push value)
          (pcΔ := Assembly.pushPcDelta value))
  | .returnToken value =>
      .ok
        (state.replaceStackAndIncrPC
          (state.stack.push value) (pcΔ := 33))
  | .prim op =>
      op.step state
  | .pop =>
      Assembly.PrimOp.pop.step state
  | .dup depth =>
      match depth with
      | 0 => Assembly.PrimOp.dup1.step state
      | 1 => Assembly.PrimOp.dup2.step state
      | 2 => Assembly.PrimOp.dup3.step state
      | 3 => Assembly.PrimOp.dup4.step state
      | 4 => Assembly.PrimOp.dup5.step state
      | 5 => Assembly.PrimOp.dup6.step state
      | 6 => Assembly.PrimOp.dup7.step state
      | 7 => Assembly.PrimOp.dup8.step state
      | 8 => Assembly.PrimOp.dup9.step state
      | 9 => Assembly.PrimOp.dup10.step state
      | 10 => Assembly.PrimOp.dup11.step state
      | 11 => Assembly.PrimOp.dup12.step state
      | 12 => Assembly.PrimOp.dup13.step state
      | 13 => Assembly.PrimOp.dup14.step state
      | 14 => Assembly.PrimOp.dup15.step state
      | 15 => Assembly.PrimOp.dup16.step state
      | _ => .error .InvalidInstruction
  | .swap depth =>
      match depth with
      | 0 => Assembly.PrimOp.swap1.step state
      | 1 => Assembly.PrimOp.swap2.step state
      | 2 => Assembly.PrimOp.swap3.step state
      | 3 => Assembly.PrimOp.swap4.step state
      | 4 => Assembly.PrimOp.swap5.step state
      | 5 => Assembly.PrimOp.swap6.step state
      | 6 => Assembly.PrimOp.swap7.step state
      | 7 => Assembly.PrimOp.swap8.step state
      | 8 => Assembly.PrimOp.swap9.step state
      | 9 => Assembly.PrimOp.swap10.step state
      | 10 => Assembly.PrimOp.swap11.step state
      | 11 => Assembly.PrimOp.swap12.step state
      | 12 => Assembly.PrimOp.swap13.step state
      | 13 => Assembly.PrimOp.swap14.step state
      | 14 => Assembly.PrimOp.swap15.step state
      | 15 => Assembly.PrimOp.swap16.step state
      | _ => .error .InvalidInstruction
  | .bindLocals _offset _names =>
      .ok state
  | .bindScratch _baseDepth _name _slot =>
      .ok state
  | .relabel _target =>
      .ok state
  | .unwind target =>
      runPops (shape.length - target.length) state

def runAt (instr : Instr) (shape : Shape) (state : EVMState) :
    Except EVMException (EVMState × Shape) := do
  let output ←
    (instr.type? shape).elim (.error .InvalidInstruction) .ok
  let state' ← instr.runState shape state
  .ok (state', output)

end Instr

namespace Block

def runBody : List Instr → Shape → EVMState →
    Except EVMException (EVMState × Shape)
  | [], shape, state => .ok (state, shape)
  | instr :: rest, shape, state => do
      let (state', shape') ← instr.runAt shape state
      runBody rest shape' state'

def ReturnSite.findTarget? (token : Word) :
    List ReturnSite → Option Label
  | [] => none
  | site :: rest =>
      if site.token = token then some site.target
      else findTarget? token rest

def runTerm (shape : Shape) (term : Terminator) (state : EVMState) : Outcome :=
  match term with
  | .fallthrough next => .jump next state
  | .jump target => .jump target state
  | .jumpi target fallthrough =>
      match state.stack.pop with
      | none => .invalid state
      | some (stack, cond) =>
          let state' := { state with stack := stack }
          if cond = EvmYul.UInt256.ofNat 0 then
            .jump fallthrough state'
          else
            .jump target state'
  | .returnDispatch returnCount sites =>
      match shape.returnTokenDepth? with
      | none => .invalid state
      | some depth =>
          if depth ≠ returnCount then
            .invalid state
          else match state.stack[depth]? with
          | none => .invalid state
          | some token =>
              match ReturnSite.findTarget? token sites with
              | none => .invalid state
              | some target =>
                  .jump target { state with stack := state.stack.eraseIdx depth }
  | .halt kind => .halt kind state
  | .invalid => .invalid state

def runTermChecked (shape : Shape) (term : Terminator)
    (state : EVMState) : Except EVMException Outcome :=
  match term with
  | .halt .selfdestruct =>
      if state.executionEnv.perm then
        .ok (.halt .selfdestruct state)
      else
        .error .StaticModeViolation
  | _ => .ok (runTerm shape term state)

theorem runTermChecked_halt_of_allowed
    (shape : Shape) (kind : Assembly.HaltKind) (state : EVMState)
    (hAllowed : kind = .selfdestruct →
      state.executionEnv.perm = true) :
    runTermChecked shape (.halt kind) state =
      .ok (.halt kind state) := by
  cases kind <;> simp [runTermChecked, runTerm, hAllowed]

theorem runTermChecked_selfdestruct_of_static
    (shape : Shape) (state : EVMState)
    (hPermission : state.executionEnv.perm = false) :
    runTermChecked shape (.halt .selfdestruct) state =
      .error .StaticModeViolation := by
  simp [runTermChecked, hPermission]

@[simp] theorem runTermChecked_fallthrough
    (shape : Shape) (target : Label) (state : EVMState) :
    runTermChecked shape (.fallthrough target) state =
      .ok (runTerm shape (.fallthrough target) state) := rfl

@[simp] theorem runTermChecked_jump
    (shape : Shape) (target : Label) (state : EVMState) :
    runTermChecked shape (.jump target) state =
      .ok (runTerm shape (.jump target) state) := rfl

@[simp] theorem runTermChecked_jumpi
    (shape : Shape) (target fallthrough : Label) (state : EVMState) :
    runTermChecked shape (.jumpi target fallthrough) state =
      .ok (runTerm shape (.jumpi target fallthrough) state) := rfl

@[simp] theorem runTermChecked_returnDispatch
    (shape : Shape) (returnCount : Nat) (sites : List ReturnSite)
    (state : EVMState) :
    runTermChecked shape (.returnDispatch returnCount sites) state =
      .ok (runTerm shape (.returnDispatch returnCount sites) state) := rfl

@[simp] theorem runTermChecked_invalid
    (shape : Shape) (state : EVMState) :
    runTermChecked shape .invalid state =
      .ok (runTerm shape .invalid state) := rfl

@[simp] theorem runTermChecked_stop
    (shape : Shape) (state : EVMState) :
    runTermChecked shape (.halt .stop) state =
      .ok (.halt .stop state) := rfl

@[simp] theorem runTermChecked_return
    (shape : Shape) (state : EVMState) :
    runTermChecked shape (.halt .return) state =
      .ok (.halt .return state) := rfl

@[simp] theorem runTermChecked_revert
    (shape : Shape) (state : EVMState) :
    runTermChecked shape (.halt .revert) state =
      .ok (.halt .revert state) := rfl

theorem runTerm_eq_of_runTermChecked_eq_ok
    {shape : Shape} {term : Terminator} {state : EVMState}
    {outcome : Outcome}
    (hRun : runTermChecked shape term state = .ok outcome) :
    runTerm shape term state = outcome := by
  cases term with
  | halt kind =>
      cases kind with
      | stop | «return» | revert =>
          exact Except.ok.inj hRun
      | selfdestruct =>
          simp only [runTerm]
          cases hPermission : state.executionEnv.perm with
          | false =>
              simp [runTermChecked, hPermission] at hRun
          | true =>
              simpa [runTermChecked, hPermission] using hRun
  | fallthrough _ | jump _ | jumpi _ _
  | returnDispatch _ _ | invalid =>
      exact Except.ok.inj hRun

theorem ReturnSite.mem_of_findTarget?_eq_some
    {token : Word} {sites : List ReturnSite} {target : Label}
    (hFind : ReturnSite.findTarget? token sites = some target) :
    ∃ site ∈ sites, site.target = target := by
  induction sites with
  | nil =>
      simp [ReturnSite.findTarget?] at hFind
  | cons site rest ih =>
      by_cases hToken : site.token = token
      · simp [ReturnSite.findTarget?, hToken] at hFind
        exact ⟨site, by simp, hFind⟩
      · simp [ReturnSite.findTarget?, hToken] at hFind
        rcases ih hFind with ⟨found, hMem, hTarget⟩
        exact ⟨found, by simp [hMem], hTarget⟩

theorem ReturnSite.mem_token_of_findTarget?_eq_some
    {token : Word} {sites : List ReturnSite} {target : Label}
    (hFind : ReturnSite.findTarget? token sites = some target) :
    ∃ site ∈ sites, site.token = token ∧ site.target = target := by
  induction sites with
  | nil =>
      simp [ReturnSite.findTarget?] at hFind
  | cons site rest ih =>
      by_cases hToken : site.token = token
      · simp [ReturnSite.findTarget?, hToken] at hFind
        exact ⟨site, by simp, hToken, hFind⟩
      · simp [ReturnSite.findTarget?, hToken] at hFind
        rcases ih hFind with ⟨found, hMem, hFoundToken, hTarget⟩
        exact ⟨found, by simp [hMem], hFoundToken, hTarget⟩

theorem findBlock?_exists_of_targetsHaveShape?_eq_true
    {program : Program} {shape : Shape} {sites : List ReturnSite}
    (hShapes : Terminator.targetsHaveShape? program shape sites = true)
    {site : ReturnSite} (hMem : site ∈ sites) :
    ∃ block, program.findBlock? site.target = some block := by
  induction sites with
  | nil =>
      simp at hMem
  | cons head rest ih =>
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl hHead =>
          subst head
          cases hFind : program.findBlock? site.target with
          | none =>
              simp [Terminator.targetsHaveShape?,
                Program.labelShape?, hFind] at hShapes
          | some block =>
              exact ⟨block, rfl⟩
      | inr hRest =>
          cases hHeadFind : program.findBlock? head.target with
          | none =>
              simp [Terminator.targetsHaveShape?,
                Program.labelShape?, hHeadFind] at hShapes
          | some headBlock =>
              have hTail :
                  Terminator.targetsHaveShape?
                      program shape rest = true := by
                have hCombined :
                    shape.compatible headBlock.input = true ∧
                      Terminator.targetsHaveShape?
                        program shape rest = true := by
                  simpa [Terminator.targetsHaveShape?,
                    Program.labelShape?, hHeadFind] using hShapes
                exact hCombined.2
              exact ih hTail hRest

/--
An ordinary well-typed terminator can jump only to a block owned by the same
TypedCfg program, including a target selected by return dispatch.
-/
theorem findBlock?_exists_of_type?_runTerm_jump
    {program : Program} {shape : Shape} {term : Terminator}
    {state final : EVMState} {next : Label}
    (hType : term.type? program shape = some ())
    (hRun : runTerm shape term state = .jump next final) :
    ∃ block, program.findBlock? next = some block := by
  cases term with
  | fallthrough target =>
      cases hFind : program.findBlock? target with
      | none =>
          simp [Terminator.type?, Program.labelShape?, hFind] at hType
      | some block =>
          simp [runTerm] at hRun
          rcases hRun with ⟨rfl, _⟩
          exact ⟨block, hFind⟩
  | jump target =>
      cases hFind : program.findBlock? target with
      | none =>
          simp [Terminator.type?, Program.labelShape?, hFind] at hType
      | some block =>
          simp [runTerm] at hRun
          rcases hRun with ⟨rfl, _⟩
          exact ⟨block, hFind⟩
  | jumpi target fallthrough =>
      cases hTarget : program.findBlock? target with
      | none =>
          simp [Terminator.type?, Program.labelShape?, hTarget] at hType
      | some targetBlock =>
          cases hFallthrough : program.findBlock? fallthrough with
          | none =>
              simp [Terminator.type?, Program.labelShape?,
                hTarget, hFallthrough] at hType
          | some fallthroughBlock =>
              cases hPop : state.stack.pop with
              | none =>
                  simp [runTerm, hPop] at hRun
              | some pair =>
                  rcases pair with ⟨stack, cond⟩
                  by_cases hZero : cond = EvmYul.UInt256.ofNat 0
                  · simp [runTerm, hPop, hZero] at hRun
                    rcases hRun with ⟨rfl, _⟩
                    exact ⟨fallthroughBlock, hFallthrough⟩
                  · simp [runTerm, hPop, hZero] at hRun
                    rcases hRun with ⟨rfl, _⟩
                    exact ⟨targetBlock, hTarget⟩
  | returnDispatch returnCount sites =>
      cases hDepth : shape.returnTokenDepth? with
      | none =>
          simp [Terminator.type?, hDepth] at hType
      | some depth =>
          by_cases hCount : depth = returnCount
          · subst depth
            have hShapes :
                Terminator.targetsHaveShape?
                    program (shape.erase returnCount) sites = true := by
              have hChecked :
                  sites ≠ [] ∧
                    Terminator.targetsHaveShape?
                      program (shape.erase returnCount) sites = true := by
                simpa [Terminator.type?, hDepth] using hType
              exact hChecked.2
            cases hToken : state.stack[returnCount]? with
            | none =>
                simp [runTerm, hDepth, hToken] at hRun
            | some token =>
                cases hFind :
                    ReturnSite.findTarget? token sites with
                | none =>
                    simp [runTerm, hDepth, hToken, hFind] at hRun
                | some target =>
                    simp [runTerm, hDepth, hToken, hFind] at hRun
                    rcases hRun with ⟨rfl, _⟩
                    rcases
                        ReturnSite.mem_of_findTarget?_eq_some hFind with
                      ⟨site, hMem, hSiteTarget⟩
                    subst target
                    exact
                      findBlock?_exists_of_targetsHaveShape?_eq_true
                        hShapes hMem
          · simp [Terminator.type?, hDepth, hCount] at hType
  | halt kind =>
      simp [runTerm] at hRun
  | invalid =>
      simp [runTerm] at hRun

theorem runTerm_ne_fallthrough
    (shape : Shape) (term : Terminator)
    (state final : EVMState) :
    runTerm shape term state ≠ .fallthrough final := by
  cases term <;> simp [runTerm] <;> aesop

theorem runTerm_ne_returnDispatch
    (shape : Shape) (term : Terminator)
    (state final : EVMState) :
    runTerm shape term state ≠ .returnDispatch final := by
  cases term <;> simp [runTerm] <;> aesop

def run (block : Block) (state : EVMState) :
    Except EVMException Outcome := do
  let (state', output) ← runBody block.body block.input state
  if output = block.output then
    runTermChecked block.output block.term state'
  else
    .error .InvalidInstruction

end Block

namespace Program

def step (program : Program) (label : Label) (state : EVMState) :
    Except EVMException Outcome :=
  match program.findBlock? label with
  | none => .ok (.invalid state)
  | some block => block.run state

/--
Fuel-indexed multi-block execution.

Fuel exhaustion leaves the current control point as a residual jump. This is
the compositional boundary used by source proofs: a compiled source fragment
may establish that execution reaches its continuation label without executing
the continuation's sentinel block. The input state is already at the semantic
entry to the block; consuming the emitted Assembly label byte belongs to the
TypedCfg-to-Assembly preservation theorem, not this IR interpreter.
-/
def runN (program : Program) : Nat → Label → EVMState →
    Except EVMException Outcome
  | 0, label, state => .ok (.jump label state)
  | fuel + 1, label, state => do
      let outcome ← program.step label state
      match outcome with
      | .jump next state' => runN program fuel next state'
      | .fallthrough state' => .ok (.fallthrough state')
      | .returnDispatch state' => .ok (.returnDispatch state')
      | .halt kind state' => .ok (.halt kind state')
      | .invalid state' => .ok (.invalid state')

@[simp] theorem runN_zero (program : Program) (label : Label)
    (state : EVMState) :
    program.runN 0 label state = .ok (.jump label state) := rfl

theorem runN_succ (program : Program) (fuel : Nat) (label : Label)
    (state : EVMState) :
    program.runN (fuel + 1) label state =
      (do
        let outcome ← program.step label state
        match outcome with
        | .jump next state' => program.runN fuel next state'
        | .fallthrough state' => .ok (.fallthrough state')
        | .returnDispatch state' => .ok (.returnDispatch state')
        | .halt kind state' => .ok (.halt kind state')
        | .invalid state' => .ok (.invalid state')) := rfl

theorem runN_succ_of_step_jump
    {program : Program} {fuel : Nat} {label next : Label}
    {state state' : EVMState} {outcome : Outcome}
    (hStep :
      program.step label state = .ok (.jump next state'))
    (hRun : program.runN fuel next state' = .ok outcome) :
    program.runN (fuel + 1) label state = .ok outcome := by
  rw [runN_succ, hStep]
  exact hRun

theorem runN_succ_of_step_terminal
    {program : Program} {fuel : Nat} {label : Label}
    {state : EVMState} {outcome : Outcome}
    (hStep : program.step label state = .ok outcome)
    (hTerminal : ∀ next state', outcome ≠ .jump next state') :
    program.runN (fuel + 1) label state = .ok outcome := by
  rw [runN_succ, hStep]
  cases outcome with
  | jump next state' =>
      exact False.elim (hTerminal next state' rfl)
  | fallthrough state' | returnDispatch state' | halt _ state' | invalid state' =>
      rfl

/--
Successful finite execution from a semantic block entry.

This relation deliberately permits residual jumps. It is the CFG-level
composition interface: one generated fragment can establish that it reaches a
continuation, and another can continue execution from that label.
-/
def Eventually (program : Program) (label : Label) (state : EVMState)
    (outcome : Outcome) : Prop :=
  ∃ fuel, program.runN fuel label state = .ok outcome

namespace Eventually

theorem residual (program : Program) (label : Label) (state : EVMState) :
    program.Eventually label state (.jump label state) :=
  ⟨0, rfl⟩

theorem of_runN
    {program : Program} {fuel : Nat} {label : Label}
    {state : EVMState} {outcome : Outcome}
    (hRun : program.runN fuel label state = .ok outcome) :
    program.Eventually label state outcome :=
  ⟨fuel, hRun⟩

theorem bind_jump
    {program : Program} {entry next : Label}
    {initial middle : EVMState} {outcome : Outcome}
    (hFirst : program.Eventually entry initial (.jump next middle))
    (hNext : program.Eventually next middle outcome) :
    program.Eventually entry initial outcome := by
  rcases hFirst with ⟨firstFuel, hFirst⟩
  rcases hNext with ⟨nextFuel, hNext⟩
  refine ⟨firstFuel + nextFuel, ?_⟩
  induction firstFuel generalizing entry initial with
  | zero =>
      simp only [runN_zero] at hFirst
      cases hFirst
      simpa using hNext
  | succ firstFuel ih =>
      rw [Nat.succ_add, runN_succ]
      rw [runN_succ] at hFirst
      cases hStep : program.step entry initial with
      | error err =>
          simp [hStep, Bind.bind, Except.bind] at hFirst
      | ok stepOutcome =>
          rw [hStep] at hFirst
          simp only [Bind.bind, Except.bind] at hFirst ⊢
          cases stepOutcome with
          | jump target stepped =>
              exact ih hFirst
          | fallthrough stepped =>
              cases hFirst
          | returnDispatch stepped =>
              cases hFirst
          | halt kind stepped =>
              cases hFirst
          | invalid stepped =>
              cases hFirst

end Eventually

end Program

end TypedCfg
end EvmCompiler
