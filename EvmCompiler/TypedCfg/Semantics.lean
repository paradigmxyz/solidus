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
          (state.stack.push value) (pcΔ := 33))
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

def run (block : Block) (state : EVMState) :
    Except EVMException Outcome := do
  let (state', output) ← runBody block.body block.input state
  if output = block.output then
    .ok (runTerm block.output block.term state')
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
