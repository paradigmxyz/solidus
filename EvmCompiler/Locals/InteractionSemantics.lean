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

def openEvalCondition (expr : Locals.Expr 1)
    (state : State) : Open (State × Bool) :=
  Locals.Source.Effectful.Expr.Control.evalCondition
    stateModel primitiveSemantics expr state

end Expr

namespace ExprSeq

def openEval {results : Nat} (exprs : Locals.ExprSeq results)
    (state : State) : Open (State × List Word) :=
  Locals.Source.Effectful.Expr.Control.ExprSeq.eval
    stateModel primitiveSemantics exprs state

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
