import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.Locals.EffectSemantics

namespace EvmCompiler
namespace Locals
namespace InteractionSemantics

abbrev Open (α : Type) :=
  Simulation.Interaction EVMException α

abbrev State := Locals.Source.State
abbrev Outcome := Locals.Source.Effectful.Outcome State

def stateModel : Locals.Source.Effectful.StateModel State :=
  Locals.Source.Effectful.Ordinary.stateModel

namespace Primitive

def isolated (state : State) (values : List Word) : Assembly.EVMState :=
  { toSharedState := state.shared
    pc := EvmYul.UInt256.ofNat 0
    stack := values.reverse
    execLength := 0 }

def supportsOpen (op : Structured.BasicOp) : Bool :=
  match op with
  | .dup1 | .dup2 | .dup3 | .dup4
  | .dup5 | .dup6 | .dup7 | .dup8
  | .dup9 | .dup10 | .dup11 | .dup12
  | .dup13 | .dup14 | .dup15 | .dup16
  | .swap1 | .swap2 | .swap3 | .swap4
  | .swap5 | .swap6 | .swap7 | .swap8
  | .swap9 | .swap10 | .swap11 | .swap12
  | .swap13 | .swap14 | .swap15 | .swap16
  | .invalid => false
  | .gas | .msize
  | .call | .callcode | .delegatecall | .staticcall
  | .create | .create2 => true
  | op =>
      (Locals.Source.PrimitiveSemantics.sourceContinuingStep? op).isSome

theorem stackArity_of_supportsOpen
    {op : Structured.BasicOp}
    (hSupports : supportsOpen op = true) :
    op.toPrimOp.stackArity? =
      some
        (Expressions.Structured.BasicOp.inputs op,
          Expressions.Structured.BasicOp.outputs op) := by
  cases op <;> simp [supportsOpen] at hSupports
  all_goals rfl

def finish (source : State) (target : Assembly.EVMState) :
    State × List Word :=
  (source.withShared target.toSharedState, target.stack.reverse)

def openEval (op : Structured.BasicOp) (state : State)
    (values : List Word) : Open (State × List Word) :=
  if values.length = Expressions.Structured.BasicOp.inputs op then
    if supportsOpen op then
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.openStep
          op.toPrimOp (isolated state values))
    else
      throw .InvalidInstruction
  else
    throw .StackUnderflow

/-- Primitive interactions may change shared state but never the source local
store, for every possible open-world response. -/
theorem openEval_vars_eq (op : Structured.BasicOp) (state : State)
    (values : List Word) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEval op state values) := by
  unfold openEval
  by_cases hLength :
      values.length = Expressions.Structured.BasicOp.inputs op
  · simp only [hLength, if_pos]
    by_cases hSupports : supportsOpen op = true
    · simp only [hSupports, if_pos]
      apply Simulation.Interaction.AllDone.map (finish state)
        (Simulation.Interaction.AllDone.trivial
          (Assembly.InteractionSemantics.PrimOp.openStep
            op.toPrimOp (isolated state values)))
      · intro _ _
        trivial
      · intro _ _
        rfl
    · simp only [hSupports, if_neg]
      exact .done True.intro
  · simp only [hLength, if_neg]
    exact .done True.intro

/--
A primitive admitted by the canonical ordinary source semantics is a closed
interaction. This is the semantic bridge used by upper pass proofs; it does
not classify or reinterpret the primitive.
-/
theorem openEval_closedStep
    {op : Structured.BasicOp} {step : Assembly.PrimStep}
    {state : State} {values : List Word}
    (hLength : values.length = Expressions.Structured.BasicOp.inputs op)
    (hSupports : supportsOpen op = true)
    (hSourceStep :
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op = some step)
    (hGas : op.toPrimOp ≠ .gas)
    (hMsize : op.toPrimOp ≠ .msize) :
    openEval op state values =
      Simulation.Interaction.map (finish state)
        (.done (step.run (isolated state values))) := by
  simp only [openEval, hLength, hSupports, ↓reduceIte]
  rw [Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
    (Locals.Source.PrimitiveSemantics.sourceContinuingStep?_toPrimOp
      hSourceStep)
    hGas hMsize]

@[simp] theorem openEval_iszero (state : State) (value : Word) :
    openEval .iszero state [value] =
      Simulation.Interaction.pure
        (state, [EvmYul.UInt256.isZero value]) := by
  rw [openEval_closedStep
    (step := .un EvmYul.UInt256.isZero)
    (by simp [Expressions.Structured.BasicOp.inputs])
    (by simp [supportsOpen,
      Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
      Structured.BasicOp.toPrimOp, Assembly.PrimOp.continuingStep?])
    (by rfl) (by simp [Structured.BasicOp.toPrimOp])
    (by simp [Structured.BasicOp.toPrimOp])]
  unfold Simulation.Interaction.map
  simp only [Assembly.PrimStep.run, isolated,
    EvmYul.EVM.execUnOp, EvmYul.Stack.pop,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, Simulation.Interaction.bind_done_ok]
  rfl

def openTerminal (kind : Assembly.HaltKind) (state : State)
    (values : List Word) : Open State :=
  let isolatedState : Assembly.EVMState := isolated state values
  Simulation.Interaction.map
    (fun final => state.withShared final.toSharedState)
    (.done (Structured.Terminal.step kind isolatedState))

@[simp] theorem openEval_gas (state : State) :
    openEval .gas state [] =
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.resourceStep
          .gas (isolated state [])) := by
  simp [openEval, supportsOpen,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Structured.BasicOp.toPrimOp]

@[simp] theorem openEval_msize (state : State) :
    openEval .msize state [] =
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.resourceStep
          .msize (isolated state [])) := by
  simp [openEval, supportsOpen,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Structured.BasicOp.toPrimOp]

@[simp] theorem openEval_call (state : State)
    (values : List Word) (hLength : values.length = 7) :
    openEval .call state values =
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.callStep
          .call (isolated state values)) := by
  simp [openEval, supportsOpen, hLength,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Structured.BasicOp.toPrimOp]

@[simp] theorem openEval_callcode (state : State)
    (values : List Word) (hLength : values.length = 7) :
    openEval .callcode state values =
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.callStep
          .callcode (isolated state values)) := by
  simp [openEval, supportsOpen, hLength,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Structured.BasicOp.toPrimOp]

@[simp] theorem openEval_delegatecall (state : State)
    (values : List Word) (hLength : values.length = 6) :
    openEval .delegatecall state values =
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.callStep
          .delegatecall (isolated state values)) := by
  simp [openEval, supportsOpen, hLength,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Structured.BasicOp.toPrimOp]

@[simp] theorem openEval_staticcall (state : State)
    (values : List Word) (hLength : values.length = 6) :
    openEval .staticcall state values =
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.callStep
          .staticcall (isolated state values)) := by
  simp [openEval, supportsOpen, hLength,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Structured.BasicOp.toPrimOp]

@[simp] theorem openEval_create (state : State)
    (values : List Word) (hLength : values.length = 3) :
    openEval .create state values =
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.createStep
          .create (isolated state values)) := by
  simp [openEval, supportsOpen, hLength,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Structured.BasicOp.toPrimOp]

@[simp] theorem openEval_create2 (state : State)
    (values : List Word) (hLength : values.length = 4) :
    openEval .create2 state values =
      Simulation.Interaction.map (finish state)
        (Assembly.InteractionSemantics.PrimOp.createStep
          .create2 (isolated state values)) := by
  simp [openEval, supportsOpen, hLength,
    Locals.Source.PrimitiveSemantics.sourceContinuingStep?,
    Expressions.Structured.BasicOp.inputs,
    Structured.BasicOp.toPrimOp]

end Primitive

mutual
  def Expr.OpenSupported {results : Nat} :
      Locals.Expr results → Prop
    | .lit _value => True
    | .var _name => True
    | .code _code => False
    | .prim op args =>
        Primitive.supportsOpen op = true ∧
          ExprSeq.OpenSupported args

  def ExprSeq.OpenSupported {results : Nat} :
      Locals.ExprSeq results → Prop
    | .nil => True
    | .cons head tail =>
        Expr.OpenSupported head ∧
          ExprSeq.OpenSupported tail
end

mutual
  def Block.OpenSupported : Locals.Block → Prop
    | ⟨stmts⟩ => StmtList.OpenSupported stmts

  def Stmt.OpenSupported : Locals.Stmt → Prop
    | .expr expr => Expr.OpenSupported expr
    | .exprs exprs => ExprSeq.OpenSupported exprs
    | .let_ _name value => Expr.OpenSupported value
    | .assign _name value => Expr.OpenSupported value
    | .assignTop _name
    | .assignTopWithOffset _offset _name
    | .promoteName _name
    | .cleanupTo _targetLayout => True
    | .block body => Block.OpenSupported body
    | .if_ cond body =>
        Expr.OpenSupported cond ∧ Block.OpenSupported body
    | .switch scrutinee cases defaultBody =>
        Expr.OpenSupported scrutinee ∧
          CaseList.OpenSupported cases ∧
          Default.OpenSupported defaultBody
    | .for_ init cond post body =>
        Block.OpenSupported init ∧ Expr.OpenSupported cond ∧
          Block.OpenSupported post ∧ Block.OpenSupported body
    | .brk | .cont | .leave | .call _name | .terminal _kind => True
    | .terminalArgs _kind args => ExprSeq.OpenSupported args

  def StmtList.OpenSupported : List Locals.Stmt → Prop
    | [] => True
    | stmt :: rest =>
        Stmt.OpenSupported stmt ∧ StmtList.OpenSupported rest

  def CaseList.OpenSupported : List (Word × Locals.Block) → Prop
    | [] => True
    | (_value, body) :: rest =>
        Block.OpenSupported body ∧ CaseList.OpenSupported rest

  def Default.OpenSupported : Option Locals.Block → Prop
    | none => True
    | some body => Block.OpenSupported body
end

namespace CaseList

theorem openSupported_of_mem
    {cases : List (Word × Locals.Block)}
    {value : Word} {body : Locals.Block}
    (hSupported : OpenSupported cases)
    (hMem : (value, body) ∈ cases) :
    Block.OpenSupported body := by
  induction cases with
  | nil => simp at hMem
  | cons head rest ih =>
      rcases head with ⟨headValue, headBody⟩
      rcases hSupported with ⟨hHead, hRest⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with hEq | hMem
      · rcases hEq with ⟨rfl, rfl⟩
        exact hHead
      · exact ih hRest hMem

end CaseList

def primitiveSemantics :
    Locals.Source.Effectful.Control.PrimitiveSemantics
      (Simulation.Interaction EVMException) State where
  eval := Primitive.openEval
  terminal := Primitive.openTerminal

namespace Expr

def openEval {results : Nat} (expr : Locals.Expr results)
    (state : State) : Open (State × List Word) :=
  Locals.Source.Effectful.Expr.Control.eval
    stateModel primitiveSemantics expr state

def openEvalOne {results : Nat} (expr : Locals.Expr results)
    (state : State) : Open (State × Word) :=
  Locals.Source.Effectful.Expr.Control.evalOne
    stateModel primitiveSemantics expr state

theorem openEvalOne_eq_bind {results : Nat}
    (expr : Locals.Expr results) (state : State) :
    openEvalOne expr state =
      Simulation.Interaction.bind (openEval expr state) fun result =>
        match result.2 with
        | [value] => pure (result.1, value)
        | _ => throw .InvalidInstruction := by
  unfold openEvalOne Locals.Source.Effectful.Expr.Control.evalOne
  change
    Simulation.Interaction.bind (openEval expr state) (fun result =>
      match result.2 with
      | [value] => pure (result.1, value)
      | _ => throw .InvalidInstruction) = _
  rfl

def openEvalCondition (expr : Locals.Expr 1)
    (state : State) : Open (State × Bool) :=
  Locals.Source.Effectful.Expr.Control.evalCondition
    stateModel primitiveSemantics expr state

theorem openEvalCondition_eq_map_openEvalOne
    (expr : Locals.Expr 1) (state : State) :
    openEvalCondition expr state =
      Simulation.Interaction.map
        (fun result => (result.1,
          result.2 != EvmYul.UInt256.ofNat 0))
        (openEvalOne expr state) := by
  unfold openEvalCondition
    Locals.Source.Effectful.Expr.Control.evalCondition
    Simulation.Interaction.map
  rfl

theorem openEvalCondition_eq_bind (expr : Locals.Expr 1) (state : State) :
    openEvalCondition expr state =
      Simulation.Interaction.bind (openEval expr state) fun result =>
        match result.2 with
        | [value] =>
            pure (result.1, value != EvmYul.UInt256.ofNat 0)
        | _ => throw .InvalidInstruction := by
  unfold openEvalCondition
    Locals.Source.Effectful.Expr.Control.evalCondition
  change
    Simulation.Interaction.bind (openEvalOne expr state) (fun result =>
      pure (result.1, result.2 != EvmYul.UInt256.ofNat 0)) = _
  rw [openEvalOne_eq_bind, Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial (openEval expr state))
  intro result _hResult
  cases result.2 with
  | nil => rfl
  | cons value rest =>
      cases rest <;> rfl

mutual
  /-- Expression evaluation preserves local bindings on every open branch. -/
  theorem openEval_vars_eq {results : Nat}
      (expr : Locals.Expr results) (state : State) :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result => result.1.vars = state.vars)
        (openEval expr state) := by
    cases expr with
    | lit value =>
        exact .done rfl
    | var name =>
        cases hLookup : state.vars name with
        | none =>
            change Simulation.Interaction.AllDone _
              (match state.vars name with
              | some value => Simulation.Interaction.pure (state, [value])
              | none => throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            rw [hLookup]
            exact .done True.intro
        | some value =>
            change Simulation.Interaction.AllDone _
              (match state.vars name with
              | some value => Simulation.Interaction.pure (state, [value])
              | none => throw EvmYul.EVM.ExecutionException.InvalidInstruction)
            rw [hLookup]
            exact .done rfl
    | code code =>
        exact .done True.intro
    | prim op args =>
        unfold openEval Locals.Source.Effectful.Expr.Control.eval
        apply Simulation.Interaction.AllDone.bind (openEvalSeq_vars_eq args state)
        · intro _ _
          trivial
        · intro result hArgs
          rcases result with ⟨afterArgs, values⟩
          apply Simulation.Interaction.AllDone.mono
            (Primitive.openEval_vars_eq op afterArgs values)
          intro outcome hOutcome
          cases outcome with
          | error _ => trivial
          | ok result => exact hOutcome.trans hArgs

  /-- Expression-sequence evaluation preserves local bindings on every branch. -/
  theorem openEvalSeq_vars_eq {results : Nat}
      (exprs : Locals.ExprSeq results) (state : State) :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result => result.1.vars = state.vars)
        (Locals.Source.Effectful.Expr.Control.ExprSeq.eval
          stateModel primitiveSemantics exprs state) := by
    cases exprs with
    | nil =>
        exact .done rfl
    | cons head tail =>
        unfold Locals.Source.Effectful.Expr.Control.ExprSeq.eval
        apply Simulation.Interaction.AllDone.bind (openEval_vars_eq head state)
        · intro _ _
          trivial
        · intro headResult hHead
          rcases headResult with ⟨afterHead, headValues⟩
          apply Simulation.Interaction.AllDone.bind
            (openEvalSeq_vars_eq tail afterHead)
          · intro _ _
            trivial
          · intro tailResult hTail
            rcases tailResult with ⟨afterTail, tailValues⟩
            exact .done (hTail.trans hHead)
end

/-- One-result evaluation inherits local-store preservation. -/
theorem openEvalOne_vars_eq {results : Nat}
    (expr : Locals.Expr results) (state : State) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEvalOne expr state) := by
  unfold openEvalOne Locals.Source.Effectful.Expr.Control.evalOne
  apply Simulation.Interaction.AllDone.bind (openEval_vars_eq expr state)
  · intro _ _
    trivial
  · intro result hVars
    rcases result with ⟨final, values⟩
    cases values with
    | nil => exact .done True.intro
    | cons value rest =>
        cases rest with
        | nil => exact .done hVars
        | cons next tail => exact .done True.intro

end Expr

namespace ExprSeq

def openEval {results : Nat} (exprs : Locals.ExprSeq results)
    (state : State) : Open (State × List Word) :=
  Locals.Source.Effectful.Expr.Control.ExprSeq.eval
    stateModel primitiveSemantics exprs state

theorem openEval_vars_eq {results : Nat}
    (exprs : Locals.ExprSeq results) (state : State) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .error _ => True
        | .ok result => result.1.vars = state.vars)
      (openEval exprs state) :=
  Expr.openEvalSeq_vars_eq exprs state

end ExprSeq

namespace Block

def openRun (program : Locals.Program) (ctx : Locals.Source.Ctx)
    (fuel : Nat) (block : Locals.Block) (state : State) :
    Open (Outcome × Locals.Source.Ctx) :=
  Locals.Source.Effectful.Control.Block.runOpen
    stateModel primitiveSemantics program ctx fuel block state

def openRunScoped (program : Locals.Program)
    (ctx : Locals.Source.Ctx) (block : Locals.Block)
    (fuel : Nat) (state : State) : Open Outcome :=
  Locals.Source.Effectful.Control.Block.runScoped
    stateModel primitiveSemantics program ctx block fuel state

end Block

namespace Stmt

def openRunForLoop (program : Locals.Program)
    (loopCtx : Locals.Source.Ctx) (cond : Locals.Expr 1)
    (postBase : Locals.Source.Ctx) (post : Locals.Block)
    (bodyBase : Locals.Source.Ctx) (body : Locals.Block)
    (fuel : Nat) (state : State) : Open Outcome :=
  Locals.Source.Effectful.Control.Stmt.runForLoop
    stateModel primitiveSemantics program loopCtx cond
    postBase post bodyBase body fuel state

def openRun (program : Locals.Program) (ctx : Locals.Source.Ctx)
    (fuel : Nat) (stmt : Locals.Stmt) (state : State) :
    Open (Outcome × Locals.Source.Ctx) :=
  Locals.Source.Effectful.Control.Stmt.run
    stateModel primitiveSemantics program ctx fuel stmt state

end Stmt

namespace Program

def openRunState (fuel : Nat) (program : Locals.Program)
    (state : State) : Open Outcome :=
  Locals.Source.Effectful.Control.Program.runState
    stateModel primitiveSemantics fuel program state

end Program

end InteractionSemantics
end Locals
end EvmCompiler
