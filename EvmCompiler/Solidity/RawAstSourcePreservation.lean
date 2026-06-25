import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Solidity.RawAstSourceSemantics
import EvmCompiler.Yul.EndToEnd
import EvmCompiler.Yul.FunctionsInteractionPrimitive

/-!
Semantic interface for preserving accepted raw solc Yul to ordered Yul.

This file intentionally contains the relation shape, not the final source
theorem.  The remaining proof work should discharge `ObjectPreserved` from
`decodeAndElaborateSolcIr?` success and the checked frontend validation facts,
then compose it with `RawAstEndToEnd`.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst
namespace Raw
namespace SourcePreservation

abbrev State := Yul.InteractionSemantics.State
abbrev Failure := Yul.InteractionSemantics.Failure
abbrev Open (α : Type) := Yul.InteractionSemantics.Open α

def SameDoneRel {α : Type} :
    Except Failure α → Except Failure α → Prop :=
  Eq

/-- At the dispatcher-sequence boundary the ordered side has already executed
the dispatcher lexical block, while the raw side is still immediately before
its enclosing block restriction. Errors agree exactly; successful ordered
states are the raw state restricted to the common block-entry store. -/
def PendingBlockDoneRel (entryStore : EvmYul.Yul.VarStore) :
    Except Failure State → Except Failure State → Prop :=
  Simulation.Interaction.ExceptRel Eq
    (fun raw ordered => ordered = raw.restrictStoreTo entryStore)

theorem forward_refl {α : Type}
    (truncated : Failure → Prop)
    (run : Open α) :
    Simulation.Interaction.ForwardRel truncated SameDoneRel run run := by
  induction run with
  | done result =>
      exact .done rfl
  | request query resume ih =>
      exact .request ih

def rawObjectRun (fuel : Nat) (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (state : State) : Open State :=
  Raw.SourceSemantics.execObjectCode fuel
    (Raw.SourceSemantics.contextForObject context) object state

def orderedRun (fuel : Nat) (ordered : Yul.OrderedProgram)
    (state : State) : Open State :=
  Yul.InteractionSemantics.exec fuel
    (.Block [ordered.program.contract.dispatcher])
    (some ordered.program.contract) state

def BlockRunForward (rawFuel orderedFuel : Nat)
    (context : Frontend.ObjectBuiltinContext)
    (code : List Raw.Stmt) (ordered : Yul.OrderedProgram)
    (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.execBlock rawFuel
      (Raw.SourceSemantics.contextForObject context) code state)
    (orderedRun orderedFuel ordered state)

/-- Exact preservation for raw multi-value expression evaluation before any
enclosing statement applies declaration/assignment writeback. -/
def ExprValuesRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawExpr : Raw.Expr) (orderedExpr : Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.evalValues rawFuel context rawExpr state)
    (Yul.InteractionSemantics.evalValues orderedFuel orderedExpr
      (some contract) state)

/-- Exact preservation for scalar expression evaluation. -/
def ExprRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawExpr : Raw.Expr) (orderedExpr : Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.eval rawFuel context rawExpr state)
    (Yul.InteractionSemantics.eval orderedFuel orderedExpr
      (some contract) state)

/-- Exact preservation for left-to-right argument-list evaluation. Call sites
pass reversed source lists on both sides, matching canonical Yul semantics. -/
def ArgsRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawArgs : List Raw.Expr) (orderedArgs : List Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.evalArgs rawFuel context rawArgs state)
    (Yul.InteractionSemantics.evalArgs orderedFuel orderedArgs
      (some contract) state)

theorem exprValuesRunForward_zero
    {orderedFuel : Nat} {context : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State} :
    ExprValuesRunForward 0 orderedFuel
      context rawExpr orderedExpr contract state := by
  unfold ExprValuesRunForward Raw.SourceSemantics.evalValues
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem argsRunForward_zero
    {orderedFuel : Nat} {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State} :
    ArgsRunForward 0 orderedFuel
      context rawArgs orderedArgs contract state := by
  unfold ArgsRunForward
  rw [Raw.SourceSemantics.evalArgs_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem argsRunForward_nil_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    ArgsRunForward (rawFuel + 1) (orderedFuel + 1)
      context [] [] contract state := by
  unfold ArgsRunForward
  rw [Raw.SourceSemantics.EvalArgs.nil_succ]
  rw [Yul.InteractionSemantics.EvalArgs.nil_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_literal_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {literal : Raw.Literal} {value : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hLiteral : Raw.SourceSemantics.literalWord? literal = some value) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.literal literal) (.Lit value) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.literal_succ
    rawFuel context literal state value hLiteral]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_identifier_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {value : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hLookup : state.lookup? name = some value) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.identifier name) (.Var name) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.identifier_succ
    rawFuel context name state value hLookup]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues,
    Yul.InteractionSemantics.stateModel, id_eq, hLookup]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprRunForward_of_values
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hValues :
      ExprValuesRunForward rawFuel orderedFuel
        context rawExpr orderedExpr contract state) :
    ExprRunForward rawFuel orderedFuel
      context rawExpr orderedExpr contract state := by
  unfold ExprRunForward ExprValuesRunForward at *
  rw [Raw.SourceSemantics.Eval.eval_eq_bind]
  rw [Yul.InteractionSemantics.eval_eq_bind]
  refine Simulation.Interaction.ForwardRel.bind_custom hValues ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok result => exact Simulation.Interaction.ForwardRel.done rfl

theorem argsRunForward_cons
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {rawRest : List Raw.Expr}
    {orderedArg : Frontend.AstExpr}
    {orderedRest : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hHead :
      ExprRunForward (rawFuel + 1) (orderedFuel + 1)
        context rawArg orderedArg contract state)
    (hTail :
      ∀ (stateAfterArg : State),
        ArgsRunForward rawFuel orderedFuel
          context rawRest orderedRest contract stateAfterArg) :
    ArgsRunForward (rawFuel + 2) (orderedFuel + 2)
      context (rawArg :: rawRest) (orderedArg :: orderedRest)
      contract state := by
  unfold ArgsRunForward ExprRunForward at *
  simp only [Raw.SourceSemantics.evalArgs, Raw.SourceSemantics.evalTail,
    Yul.InteractionSemantics.evalArgs, Yul.Source.Canonical.evalArgs,
    Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.evalTail]
  refine Simulation.Interaction.ForwardRel.bind_custom hHead ?_
  intro rawHeadDone orderedHeadDone hHeadDone
  unfold SameDoneRel at hHeadDone
  subst orderedHeadDone
  cases rawHeadDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok headResult =>
      rcases headResult with ⟨stateAfterArg, value⟩
      refine
        Simulation.Interaction.ForwardRel.bind_custom
          (hTail stateAfterArg) ?_
      intro rawTailDone orderedTailDone hTailDone
      unfold SameDoneRel at hTailDone
      subst orderedTailDone
      cases rawTailDone with
      | error error =>
          exact Simulation.Interaction.ForwardRel.done rfl
      | ok tailResult =>
          exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_primitiveCall_succ
    {fuel : Nat} {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {orderedArgs : List Frontend.AstExpr}
    {op : EvmYul.Operation .Yul}
    {contract : Frontend.AstContract} {state : State}
    (hClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .primitive)
    (hOp : Frontend.Primitive.ofName? name = some op)
    (hArgs :
      ArgsRunForward fuel fuel context rawArgs.reverse orderedArgs.reverse
        contract state) :
    ExprValuesRunForward (fuel + 1) (fuel + 1)
      context (.functionCall name rawArgs) (.Call (.inl op) orderedArgs)
      contract state := by
  unfold ExprValuesRunForward ArgsRunForward at *
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    fuel context name rawArgs state hClz]
  simp only [hClass, hOp]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  refine Simulation.Interaction.ForwardRel.bind_custom hArgs ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      exact
        forward_refl Yul.FunctionsInteractionPrimitive.Truncated
          (Yul.InteractionSemantics.primitiveSemantics.eval
            fuel result.1 op result.2.reverse)

theorem exprValuesRunForward_datasize_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {nameArg : Raw.Expr} {dataName : Name} {size : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hName : Raw.SourceSemantics.objectBuiltinNameArg? nameArg = some dataName)
    (hSize : context.objectBuiltins.size? dataName = some size) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "datasize" [nameArg]) (.Lit size)
      contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "datasize" [nameArg] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "datasize" [nameArg] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit size) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.datasize_succ
    rawFuel context nameArg state dataName size hName hSize]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_dataoffset_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {nameArg : Raw.Expr} {dataName : Name} {offset : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hName : Raw.SourceSemantics.objectBuiltinNameArg? nameArg = some dataName)
    (hOffset : context.objectBuiltins.offset? dataName = some offset) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "dataoffset" [nameArg]) (.Lit offset)
      contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "dataoffset" [nameArg] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "dataoffset" [nameArg] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit offset) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.dataoffset_succ
    rawFuel context nameArg state dataName offset hName hOffset]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_linkersymbol_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {nameArg : Raw.Expr} {linkerName : Name} {value : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hName : Raw.SourceSemantics.objectBuiltinNameArg? nameArg = some linkerName)
    (hValue :
      context.objectBuiltins.findLinkerSymbol? linkerName = some value) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "linkersymbol" [nameArg]) (.Lit value)
      contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "linkersymbol" [nameArg] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "linkersymbol" [nameArg] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit value) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.linkersymbol_succ
    rawFuel context nameArg state linkerName value hName hValue]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_loadimmutable_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {nameArg : Raw.Expr} {immutableName : Name} {value : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hName :
      Raw.SourceSemantics.objectBuiltinNameArg? nameArg = some immutableName)
    (hValue :
      context.objectBuiltins.findImmutableValue? immutableName = some value) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "loadimmutable" [nameArg]) (.Lit value)
      contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "loadimmutable" [nameArg] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "loadimmutable" [nameArg] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit value) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.loadimmutable_succ
    rawFuel context nameArg state immutableName value hName hValue]
  simp only [Yul.InteractionSemantics.evalValues,
    Yul.Source.Canonical.evalValues, Yul.Source.Effectful.evalValues]
  exact Simulation.Interaction.ForwardRel.done rfl

/-- Exact pre-block statement preservation used by the recursive frontend
proof. Lexical-store restriction is handled only by block constructors. -/
def StmtRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawStmt : Raw.Stmt) (orderedStmt : Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.exec rawFuel context rawStmt state)
    (Yul.InteractionSemantics.exec orderedFuel orderedStmt
      (some contract) state)

theorem stmtRunForward_variableDeclaration_none_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {names : List Name}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.variableDeclaration names none) (.Let names none)
      contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.variableDeclaration_none_succ]
  cases hCheck : EvmYul.Yul.checkDeclaration state names with
  | error error =>
      unfold Yul.InteractionSemantics.exec Yul.Source.Canonical.exec
        Yul.Source.Effectful.exec
      simp only [Yul.InteractionSemantics.stateModel, id_eq, hCheck]
      unfold Raw.SourceSemantics.fail
        Yul.Source.Effectful.Control.fail
        Yul.InteractionSemantics.Primitive.fail
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      cases result
      rw [Yul.InteractionSemantics.Exec.let_none_succ
        orderedFuel names (some contract) state hCheck]
      exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_variableDeclaration_some_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {names : List Name} {rawExpr : Raw.Expr}
    {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hValues :
      ExprValuesRunForward rawFuel orderedFuel
        context rawExpr orderedExpr contract state) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.variableDeclaration names (some rawExpr))
      (.Let names (some orderedExpr)) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.variableDeclaration_some_succ]
  cases hCheck : EvmYul.Yul.checkDeclaration state names with
  | error error =>
      unfold Yul.InteractionSemantics.exec Yul.Source.Canonical.exec
        Yul.Source.Effectful.exec
      simp only [Yul.InteractionSemantics.stateModel, id_eq, hCheck]
      unfold Raw.SourceSemantics.fail
        Yul.Source.Effectful.Control.fail
        Yul.InteractionSemantics.Primitive.fail
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      cases result
      rw [Yul.InteractionSemantics.Exec.let_some_succ
        orderedFuel names orderedExpr (some contract) state hCheck]
      unfold ExprValuesRunForward at hValues
      refine Simulation.Interaction.ForwardRel.bind_custom hValues ?_
      intro rawDone orderedDone hDone
      unfold SameDoneRel at hDone
      subst orderedDone
      cases rawDone with
      | error error => exact Simulation.Interaction.ForwardRel.done rfl
      | ok result => exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_assignment_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {names : List Name} {rawExpr : Raw.Expr}
    {orderedExpr : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hValues :
      ExprValuesRunForward rawFuel orderedFuel
        context rawExpr orderedExpr contract state) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.assignment names rawExpr)
      (.Assign names orderedExpr) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.assignment_succ]
  cases hCheck : EvmYul.Yul.checkAssignment state names with
  | error error =>
      unfold Yul.InteractionSemantics.exec Yul.Source.Canonical.exec
        Yul.Source.Effectful.exec
      simp only [Yul.InteractionSemantics.stateModel, id_eq, hCheck]
      unfold Raw.SourceSemantics.fail
        Yul.Source.Effectful.Control.fail
        Yul.InteractionSemantics.Primitive.fail
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      cases result
      rw [Yul.InteractionSemantics.Exec.assign_succ
        orderedFuel names orderedExpr (some contract) state hCheck]
      unfold ExprValuesRunForward at hValues
      refine Simulation.Interaction.ForwardRel.bind_custom hValues ?_
      intro rawDone orderedDone hDone
      unfold SameDoneRel at hDone
      subst orderedDone
      cases rawDone with
      | error error => exact Simulation.Interaction.ForwardRel.done rfl
      | ok result => exact Simulation.Interaction.ForwardRel.done rfl

/-- Exact pre-block statement-list preservation. Both sides still carry the
same lexical store; the dispatcher adapter below accounts for the ordered
dispatcher's additional block boundary. -/
def SeqRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCode : List Raw.Stmt) (orderedCode : List Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.execSeq rawFuel context rawCode state)
    (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
      (some contract) state)

theorem seqRunForward_zero
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    SeqRunForward 0 orderedFuel context rawCode orderedCode contract state := by
  unfold SeqRunForward
  rw [Raw.SourceSemantics.execSeq_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem seqRunForward_nil_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    SeqRunForward (rawFuel + 1) (orderedFuel + 1)
      context [] [] contract state := by
  unfold SeqRunForward
  rw [Raw.SourceSemantics.ExecSeq.nil_succ]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

/-- Generic list constructor for the recursive frontend proof. The head and
tail share one residual fuel on each side; only regular states enter the tail. -/
theorem seqRunForward_cons
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {rawRest : List Raw.Stmt}
    {orderedStmt : Frontend.AstStmt}
    {orderedRest : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hHead :
      StmtRunForward rawFuel orderedFuel
        context rawStmt orderedStmt contract state)
    (hTail :
      ∀ shared vars,
        SeqRunForward rawFuel orderedFuel context rawRest orderedRest contract
          (.Ok shared vars)) :
    SeqRunForward (rawFuel + 1) (orderedFuel + 1)
      context (rawStmt :: rawRest) (orderedStmt :: orderedRest)
      contract state := by
  unfold SeqRunForward StmtRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  refine Simulation.Interaction.ForwardRel.bind_custom hHead ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok stateAfterStmt =>
      cases stateAfterStmt with
      | Ok shared vars => exact hTail shared vars
      | OutOfFuel => exact Simulation.Interaction.ForwardRel.done rfl
      | Checkpoint jump => exact Simulation.Interaction.ForwardRel.done rfl

theorem seqRunForward_cons_functionDefinition_omitted_ok
    {fuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {params returns : List Name} {body rest : List Raw.Stmt}
    {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract}
    {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore}
    (hRest :
      SeqRunForward (fuel + 1) orderedFuel
        context rest orderedCode contract (.Ok shared vars)) :
    SeqRunForward (fuel + 2) orderedFuel
      context
      (.functionDefinition name params returns body :: rest)
      orderedCode contract (.Ok shared vars) := by
  unfold SeqRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
  simpa [Simulation.Interaction.bind_pure]

/-- Raw block-body sequence preservation against the ordered dispatcher
sequence, before both sides apply their lexical block store restriction. -/
def DispatcherSeqRunForward (rawFuel orderedFuel : Nat)
    (context : Frontend.ObjectBuiltinContext)
    (scope : Raw.SourceSemantics.FunctionScope)
    (code : List Raw.Stmt) (ordered : Yul.OrderedProgram)
    (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    (PendingBlockDoneRel state.store)
    (Raw.SourceSemantics.execSeq rawFuel
      ((Raw.SourceSemantics.contextForObject context).withFunctionScope scope)
      code state)
    (Yul.InteractionSemantics.execSeq orderedFuel
      [ordered.program.contract.dispatcher]
      (some ordered.program.contract) state)

/-- Close the ordered dispatcher's lexical block around an exact raw/Yul
statement-list simulation. This is the only place where the internal sequence
relation changes from exact states to the pending block-restriction relation. -/
theorem dispatcherSeqRunForward_of_seq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {ordered : Yul.OrderedProgram} {state : State}
    (hDispatcher :
      ordered.program.contract.dispatcher = .Block orderedCode)
    (hSeq :
      SeqRunForward rawFuel orderedFuel
        ((Raw.SourceSemantics.contextForObject context).withFunctionScope scope)
        rawCode orderedCode ordered.program.contract state) :
    DispatcherSeqRunForward rawFuel (orderedFuel + 2)
      context scope rawCode ordered state := by
  unfold DispatcherSeqRunForward SeqRunForward at *
  have hRestricted :=
    Simulation.Interaction.ForwardRel.bind_right
      (rightNext := fun orderedState : State =>
        pure (orderedState.restrictStoreTo state.store))
      (targetDoneRel := PendingBlockDoneRel state.store)
      hSeq (by
      intro rawDone orderedDone hDone
      unfold SameDoneRel at hDone
      subst orderedDone
      cases rawDone with
      | error error =>
          exact
            Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.error rfl)
      | ok rawState =>
          exact
            Simulation.Interaction.ForwardRel.done
              (Simulation.Interaction.ExceptRel.ok rfl))
  rw [hDispatcher]
  rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [Yul.InteractionSemantics.ExecSeq.nil_succ]
  have hContinue :
      (fun stateAfterStmt : State =>
        match stateAfterStmt with
        | .Ok _ _ =>
            (Simulation.Interaction.pure stateAfterStmt : Open State)
        | .OutOfFuel | .Checkpoint _ =>
            (Simulation.Interaction.pure stateAfterStmt : Open State)) =
      (fun stateAfterStmt =>
        (Simulation.Interaction.pure stateAfterStmt : Open State)) := by
    funext stateAfterStmt
    cases stateAfterStmt <;> rfl
  have hRight :
      Simulation.Interaction.bind
          (Simulation.Interaction.bind
            (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
              (some ordered.program.contract) state)
            (fun stateAfterBody =>
              pure (stateAfterBody.restrictStoreTo state.store)))
          (fun stateAfterStmt : State =>
            match stateAfterStmt with
            | .Ok _ _ =>
                (Simulation.Interaction.pure stateAfterStmt : Open State)
            | .OutOfFuel | .Checkpoint _ =>
                (Simulation.Interaction.pure stateAfterStmt : Open State)) =
        Simulation.Interaction.bind
          (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
            (some ordered.program.contract) state)
          (fun stateAfterBody =>
            pure (stateAfterBody.restrictStoreTo state.store)) := by
    rw [hContinue]
    exact Simulation.Interaction.bind_pure _
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated
      (PendingBlockDoneRel state.store)
      (Raw.SourceSemantics.execSeq rawFuel
        ((Raw.SourceSemantics.contextForObject context).withFunctionScope scope)
        rawCode state)
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
            (some ordered.program.contract) state)
          (fun stateAfterBody =>
            pure (stateAfterBody.restrictStoreTo state.store)))
        (fun stateAfterStmt : State =>
          match stateAfterStmt with
          | .Ok _ _ =>
              (Simulation.Interaction.pure stateAfterStmt : Open State)
          | .OutOfFuel | .Checkpoint _ =>
              (Simulation.Interaction.pure stateAfterStmt : Open State)))
  rw [hRight]
  exact hRestricted

theorem dispatcherSeqRunForward_zero
    {orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    {state : State} :
    DispatcherSeqRunForward 0 orderedFuel context scope code ordered state := by
  unfold DispatcherSeqRunForward
  rw [Raw.SourceSemantics.execSeq_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by
        simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem dispatcherSeqRunForward_cons_functionDefinition_ok
    {fuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {name : Name} {params returns : List Name} {body rest : List Raw.Stmt}
    {ordered : Yul.OrderedProgram}
    {shared : EvmYul.SharedState .Yul} {vars : EvmYul.Yul.VarStore}
    (hRest :
      DispatcherSeqRunForward (fuel + 1) orderedFuel
        context scope rest ordered (.Ok shared vars)) :
    DispatcherSeqRunForward (fuel + 2) orderedFuel
      context scope
      (.functionDefinition name params returns body :: rest)
      ordered (.Ok shared vars) := by
  unfold DispatcherSeqRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
  simpa [Simulation.Interaction.bind_pure]

theorem blockRunForward_of_scope_seq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    {state : State}
    (hScope : Raw.SourceSemantics.functionScope? code = some scope)
    (hSeq :
      DispatcherSeqRunForward rawFuel orderedFuel
        context scope code ordered state) :
    BlockRunForward (rawFuel + 1) (orderedFuel + 1)
      context code ordered state := by
  unfold BlockRunForward DispatcherSeqRunForward orderedRun at *
  rw [Raw.SourceSemantics.ExecBlock.succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [hScope]
  refine Simulation.Interaction.ForwardRel.bind_custom hSeq ?_
  intro leftDone rightDone hDone
  cases hDone with
  | error hError =>
      subst_vars
      exact Simulation.Interaction.ForwardRel.done rfl
  | @ok rawState orderedState hRestricted =>
      subst orderedState
      apply Simulation.Interaction.ForwardRel.done
      unfold SameDoneRel
      congr 1
      exact (Yul.InteractionSemantics.State.restrictStoreTo_idem
        rawState state.store).symm

theorem rawObjectRun_none_code
    {fuel : Nat} {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {state : State}
    (hCode : object.code? = none) :
    rawObjectRun fuel context object state = pure state := by
  unfold rawObjectRun
  exact Raw.SourceSemantics.ExecObjectCode.code_none
    fuel (Raw.SourceSemantics.contextForObject context) object state hCode

theorem rawObjectRun_some_code
    {fuel : Nat} {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {state : State}
    {code : List Raw.Stmt}
    (hCode : object.code? = some code) :
    rawObjectRun fuel context object state =
      Raw.SourceSemantics.execCode fuel
        (Raw.SourceSemantics.contextForObject context) code state := by
  unfold rawObjectRun
  exact Raw.SourceSemantics.ExecObjectCode.code_some
    fuel (Raw.SourceSemantics.contextForObject context) object state hCode

theorem rawObjectRun_some_code_succ
    {fuel : Nat} {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {state : State}
    {code : List Raw.Stmt}
    (hCode : object.code? = some code) :
    rawObjectRun (fuel + 1) context object state =
      Raw.SourceSemantics.execBlock (fuel + 1)
        (Raw.SourceSemantics.contextForObject context) code state := by
  unfold rawObjectRun
  exact Raw.SourceSemantics.ExecObjectCode.code_some_succ
    fuel (Raw.SourceSemantics.contextForObject context) object state hCode

/-- Finite-prefix preservation from raw solc Yul execution to ordered Yul
execution for one selected object/context/fuel pair. -/
def RunForward (rawFuel orderedFuel : Nat)
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram)
    (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (rawObjectRun rawFuel context object state)
    (orderedRun orderedFuel ordered state)

/-- Whole-object raw-to-ordered preservation surface.

The proof should be private to the Solidity frontend: callers get it by
successful raw decoding/elaboration/compilation, not by providing generated
names, replay traces, layouts, or certificates.
-/
structure ObjectPreserved
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  forward :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel, RunForward rawFuel orderedFuel context object ordered state

theorem runForward_of_eq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    {state : State}
    (hRun :
      rawObjectRun rawFuel context object state =
        orderedRun orderedFuel ordered state) :
    RunForward rawFuel orderedFuel context object ordered state := by
  unfold RunForward
  rw [hRun]
  exact
    forward_refl Yul.FunctionsInteractionPrimitive.Truncated
      (orderedRun orderedFuel ordered state)

theorem blockRunForward_of_eq
    {rawFuel orderedFuel : Nat}
    {context : Frontend.ObjectBuiltinContext}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    {state : State}
    (hRun :
      Raw.SourceSemantics.execBlock rawFuel
          (Raw.SourceSemantics.contextForObject context) code state =
        orderedRun orderedFuel ordered state) :
    BlockRunForward rawFuel orderedFuel context code ordered state := by
  unfold BlockRunForward
  rw [hRun]
  exact
    forward_refl Yul.FunctionsInteractionPrimitive.Truncated
      (orderedRun orderedFuel ordered state)

structure ObjectRunEquivalent
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  run_eq :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        rawObjectRun rawFuel context object state =
          orderedRun orderedFuel ordered state

namespace ObjectRunEquivalent

theorem preserved
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    (hEq : ObjectRunEquivalent context object ordered) :
    ObjectPreserved context object ordered where
  forward := by
    intro rawFuel state
    rcases hEq.run_eq rawFuel state with ⟨orderedFuel, hRun⟩
    exact ⟨orderedFuel, runForward_of_eq hRun⟩

end ObjectRunEquivalent

structure ObjectPositiveRunEquivalent
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  run_eq :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        rawObjectRun (rawFuel + 1) context object state =
          orderedRun (orderedFuel + 1) ordered state

structure ObjectPositivePreserved
    (context : Frontend.ObjectBuiltinContext)
    (object : Raw.Object) (ordered : Yul.OrderedProgram) : Prop where
  forward :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        RunForward (rawFuel + 1) (orderedFuel + 1)
          context object ordered state

structure CodePositiveRunEquivalent
    (context : Frontend.ObjectBuiltinContext)
    (code : List Raw.Stmt) (ordered : Yul.OrderedProgram) : Prop where
  run_eq :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        Raw.SourceSemantics.execBlock (rawFuel + 1)
            (Raw.SourceSemantics.contextForObject context) code state =
          orderedRun (orderedFuel + 1) ordered state

structure CodePositivePreserved
    (context : Frontend.ObjectBuiltinContext)
    (code : List Raw.Stmt) (ordered : Yul.OrderedProgram) : Prop where
  forward :
    ∀ (rawFuel : Nat) (state : State),
      ∃ orderedFuel,
        BlockRunForward (rawFuel + 1) (orderedFuel + 1)
          context code ordered state

namespace ObjectPositiveRunEquivalent

theorem preserved
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    (hEq : ObjectPositiveRunEquivalent context object ordered) :
    ObjectPositivePreserved context object ordered where
  forward := by
    intro rawFuel state
    rcases hEq.run_eq rawFuel state with ⟨orderedFuel, hRun⟩
    exact ⟨orderedFuel, runForward_of_eq hRun⟩

end ObjectPositiveRunEquivalent

namespace CodePositiveRunEquivalent

theorem preserved
    {context : Frontend.ObjectBuiltinContext}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    (hEq : CodePositiveRunEquivalent context code ordered) :
    CodePositivePreserved context code ordered where
  forward := by
    intro rawFuel state
    rcases hEq.run_eq rawFuel state with ⟨orderedFuel, hRun⟩
    exact ⟨orderedFuel, blockRunForward_of_eq hRun⟩

end CodePositiveRunEquivalent

namespace CodePositivePreserved

theorem of_scope_dispatcher_seq
    {context : Frontend.ObjectBuiltinContext}
    {scope : Raw.SourceSemantics.FunctionScope}
    {code : List Raw.Stmt} {ordered : Yul.OrderedProgram}
    (hScope : Raw.SourceSemantics.functionScope? code = some scope)
    (hSeq :
      ∀ (rawFuel : Nat) (state : State),
        ∃ orderedFuel,
          DispatcherSeqRunForward rawFuel orderedFuel
            context scope code ordered state) :
    CodePositivePreserved context code ordered where
  forward := by
    intro rawFuel state
    rcases hSeq rawFuel state with ⟨orderedFuel, hForward⟩
    exact
      ⟨orderedFuel,
        blockRunForward_of_scope_seq hScope hForward⟩

theorem toObjectPositive
    {context : Frontend.ObjectBuiltinContext}
    {object : Raw.Object} {ordered : Yul.OrderedProgram}
    {code : List Raw.Stmt}
    (hCodeRun : CodePositivePreserved context code ordered)
    (hCode : object.code? = some code) :
    ObjectPositivePreserved context object ordered where
  forward := by
    intro rawFuel state
    rcases hCodeRun.forward rawFuel state with ⟨orderedFuel, hForward⟩
    refine ⟨orderedFuel, ?_⟩
    unfold RunForward BlockRunForward at *
    rw [rawObjectRun_some_code_succ hCode]
    exact hForward

end CodePositivePreserved

/-- The raw source scope and the elaborator's top-function scope may carry
different payloads, but they must expose the same function names. -/
def FunctionScopeNameRel
    (rawScope : Raw.SourceSemantics.FunctionScope)
    (topScope : List (Name × Name)) : Prop :=
  ∀ name,
    rawScope.any (fun entry => entry.fst == name) =
      topScope.any (fun entry => entry.fst == name)

theorem collectTopFunctions_rawFunctionScope
    {stmts : List Raw.Stmt}
    {state finalState : Elab.State}
    {topScope : List (Name × Name)}
    (hCollect :
      (Elab.collectTopFunctions stmts).run state =
        .ok (topScope, finalState)) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? stmts = some rawScope ∧
        FunctionScopeNameRel rawScope topScope := by
  induction stmts generalizing state finalState topScope with
  | nil =>
      unfold Elab.collectTopFunctions at hCollect
      simp [StateT.run_pure] at hCollect
      cases hCollect
      refine ⟨[], rfl, ?_⟩
      intro name
      simp
  | cons stmt rest ih =>
      cases stmt with
      | functionDefinition name params returns body =>
          unfold Elab.collectTopFunctions at hCollect
          simp [StateT.run_bind] at hCollect
          cases hTail : (Elab.collectTopFunctions rest).run state with
          | error err =>
              simp [hTail] at hCollect
          | ok tailResult =>
              rcases tailResult with ⟨topTail, tailState⟩
              simp [hTail] at hCollect
              cases hDuplicate :
                  topTail.any (fun entry => entry.fst == name) with
              | true =>
                  rw [hDuplicate] at hCollect
                  unfold Elab.throw at hCollect
                  dsimp at hCollect
                  change
                    (Except.bind
                        ((fun _ : Elab.State =>
                            Except.error
                              (toString "duplicate top-level Yul function " ++
                                toString name)) tailState)
                        ?cont) =
                      Except.ok (topScope, finalState) at hCollect
                  change
                    (Except.error
                      (toString "duplicate top-level Yul function " ++
                        toString name) :
                      Except String (List (Name × Name) × Elab.State)) =
                      Except.ok (topScope, finalState) at hCollect
                  cases hCollect
              | false =>
                  cases hDeclare :
                      (Elab.declareIdentifiers [name] "function").run
                        tailState with
                  | error err =>
                      simp [hDuplicate, hDeclare] at hCollect
                  | ok declareResult =>
                      rcases declareResult with ⟨_, declaredState⟩
                      simp [hDuplicate, hDeclare, StateT.run_bind] at hCollect
                      rcases hCollect with ⟨hTopScope, _hFinalState⟩
                      cases hTopScope
                      rcases ih hTail with
                        ⟨rawTail, hRawTail, hNameRel⟩
                      have hRawDuplicate :
                          rawTail.any (fun entry => entry.fst == name) =
                            false := by
                        rw [hNameRel name, hDuplicate]
                      refine
                        ⟨(name, { params, returns, body }) :: rawTail,
                          ?_, ?_⟩
                      · simp [Raw.SourceSemantics.functionScope?,
                          hRawTail, hRawDuplicate]
                      · intro query
                        simp [hNameRel query]
      | block stmts =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | variableDeclaration names value? =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | assignment names value =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | expressionStatement expr =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | switch scrutinee cases default =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | forLoop pre condition post body =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | ifThen condition body =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | «break» =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | «continue» =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]
      | «leave» =>
          have hTail :
              (Elab.collectTopFunctions rest).run state =
                .ok (topScope, finalState) := by
            simpa [Elab.collectTopFunctions] using hCollect
          rcases ih hTail with ⟨rawTail, hRawTail, hNameRel⟩
          refine ⟨rawTail, ?_, hNameRel⟩
          simp [Raw.SourceSemantics.functionScope?, hRawTail]

theorem elaborateCodeCore_rawFunctionScope
    {stmts : List Raw.Stmt}
    {dispatcher : List Frontend.Stmt} {state : Elab.State}
    (hCore :
      Elab.elaborateCodeCore stmts = .ok (dispatcher, state)) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? stmts = some rawScope := by
  unfold Elab.elaborateCodeCore Elab.elaborateCodeAction at hCore
  simp [StateT.run_bind] at hCore
  cases hPush : Elab.pushIdentifierScope.run {} with
  | error err =>
      simp [hPush] at hCore
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      simp [hPush] at hCore
      cases hCollect :
          (Elab.collectTopFunctions stmts).run pushedState with
      | error err =>
          simp [hCollect] at hCore
      | ok collectResult =>
          rcases collectResult with ⟨topScope, collectState⟩
          rcases collectTopFunctions_rawFunctionScope hCollect with
            ⟨rawScope, hRawScope, _hNameRel⟩
          exact ⟨rawScope, hRawScope⟩

theorem elaborateCode_rawFunctionScope
    {stmts : List Raw.Stmt}
    {dispatcher : List Frontend.Stmt}
    {functions : List (Name × Frontend.FunctionDef)}
    {helper? arg? ret? : Option Name}
    (hElab :
      Elab.elaborateCode stmts =
        .ok (dispatcher, functions, helper?, arg?, ret?)) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? stmts = some rawScope := by
  rcases Elab.elaborateCode_parts hElab with
    ⟨state, hCore, _hFunctions, _hHelper, _hArg, _hRet⟩
  exact elaborateCodeCore_rawFunctionScope hCore

structure ArtifactRawSourceContext
    (rawJson : String) (selection : Selection)
    (artifact : Frontend.Program.Artifact) where
  json : Lean.Json
  selected : SelectedIr
  program : Frontend.Program
  linkerSymbols : List (Frontend.Name × Frontend.Word)
  context : Frontend.ObjectBuiltinContext
  parse :
    Lean.Json.parse rawJson = .ok json
  selected_ok :
    decodeSelectedIr json selection = .ok selected
  decode :
    decodeAndElaborateSolcIr? rawJson selection = some program
  raw_elaborates :
    selected.root.elaborate? selected.evmVersion = .ok program.object
  linker :
    decodeLinkerSymbols? rawJson selection = some linkerSymbols
  compile :
    program.compileArtifactWithLinkerSymbols? linkerSymbols = some artifact
  codeArtifact :
    program.object.compileVerifiedStackCodeArtifactIn? context =
      some artifact.codeArtifact
  resolved :
    program.object.resolveObjectBuiltinsIn? context =
      some artifact.codeArtifact.resolved
  ordered :
    artifact.codeArtifact.resolved.toSolcYulOrderedProgram? =
      some artifact.codeArtifact.ordered
  sourceContext :
    Raw.SourceSemantics.contextForObject context =
      { objectBuiltins := context }

namespace ArtifactRawSourceContext

theorem nonempty_of_compile
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    Nonempty (ArtifactRawSourceContext rawJson selection artifact) := by
  rcases compileArtifactFromRawSolcIr?_raw_source_ordered_context hCompile with
    ⟨json, selected, program, linkerSymbols, context,
      hParse, hSelected, hDecode, hRawElab, hLinker, hProgramCompile,
      hCodeArtifact, hResolved, hOrdered, hSourceContext⟩
  exact ⟨
    { json := json
      selected := selected
      program := program
      linkerSymbols := linkerSymbols
      context := context
      parse := hParse
      selected_ok := hSelected
      decode := hDecode
      raw_elaborates := hRawElab
      linker := hLinker
      compile := hProgramCompile
      codeArtifact := hCodeArtifact
      resolved := hResolved
      ordered := hOrdered
      sourceContext := hSourceContext }⟩

theorem code_elaborates
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ helper? arg? ret?,
      Elab.elaborateCode code =
        .ok (ctx.program.object.dispatcher, ctx.program.object.functions,
          helper?, arg?, ret?) := by
  rcases Raw.Object.elaborate?_parts ctx.raw_elaborates with
    ⟨_itemFuel, dispatcher, functions, helper?, arg?, ret?,
      _data, _objects, _items, _hFuel, hCodeElab, _hItems, hFrontend⟩
  have hElab :
      Elab.elaborateCode code =
        .ok (dispatcher, functions, helper?, arg?, ret?) := by
    simpa [hCode] using hCodeElab
  refine ⟨helper?, arg?, ret?, ?_⟩
  have hDispatcher :
      ctx.program.object.dispatcher = dispatcher := by
    rw [hFrontend]
  have hFunctions :
      ctx.program.object.functions = functions := by
    rw [hFrontend]
  rw [hDispatcher, hFunctions]
  exact hElab

/-- Recover the exact frontend and canonical dispatcher lists executed by the
artifact from successful raw-code elaboration, object-builtin resolution, and
ordered-Yul conversion. All generated memoryguard context remains internal. -/
theorem dispatcher_parts
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ helper? arg? ret? memoryContract resolvedDispatcher orderedDispatcher,
      Elab.elaborateCode code =
          .ok (ctx.program.object.dispatcher, ctx.program.object.functions,
            helper?, arg?, ret?) ∧
        Frontend.MemoryGuard.Object.inferredContract? ctx.program.object =
          some memoryContract ∧
        Frontend.Stmt.List.resolveObjectBuiltinsIn?
            ctx.program.object.dispatcher
            { ctx.context with memoryContract := memoryContract } =
          some resolvedDispatcher ∧
        artifact.codeArtifact.resolved.dispatcher = resolvedDispatcher ∧
        Frontend.Stmt.List.toYul? resolvedDispatcher =
          some orderedDispatcher ∧
        artifact.codeArtifact.ordered.program.contract.dispatcher =
          .Block orderedDispatcher := by
  rcases ctx.code_elaborates hCode with
    ⟨helper?, arg?, ret?, hElab⟩
  rcases
      Frontend.Object.resolveObjectBuiltinsIn?_dispatcher ctx.resolved with
    ⟨memoryContract, resolvedDispatcher,
      hMemory, hResolveDispatcher, hResolvedDispatcher⟩
  rcases
      Frontend.Object.toSolcYulOrderedProgram?_dispatcher ctx.ordered with
    ⟨orderedDispatcher, hToYul, hOrderedDispatcher⟩
  have hResolvedToYul :
      Frontend.Stmt.List.toYul? resolvedDispatcher =
        some orderedDispatcher := by
    rw [← hResolvedDispatcher]
    exact hToYul
  exact
    ⟨helper?, arg?, ret?, memoryContract, resolvedDispatcher,
      orderedDispatcher, hElab, hMemory, hResolveDispatcher,
      hResolvedDispatcher, hResolvedToYul, hOrderedDispatcher⟩

theorem code_functionScope
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ rawScope,
      Raw.SourceSemantics.functionScope? code = some rawScope := by
  rcases ctx.code_elaborates hCode with
    ⟨helper?, arg?, ret?, hElab⟩
  exact elaborateCode_rawFunctionScope hElab

end ArtifactRawSourceContext

def RawSourceBytecodePrefixDoneRel
    (artifact : Frontend.Program.Artifact) :
    Except Failure State →
      Except Assembly.EVMException Assembly.StepResult →
        Prop :=
  fun rawDone bytecodeDone =>
    ∃ orderedDone,
      SameDoneRel rawDone orderedDone ∧
        Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
          artifact orderedDone bytecodeDone

structure ArtifactRawSourceEquivalent
    (rawJson : String) (selection : Selection)
    (artifact : Frontend.Program.Artifact)
    extends ArtifactRawSourceContext rawJson selection artifact where
  sourceRun :
    ObjectPositiveRunEquivalent context selected.root
      artifact.codeArtifact.ordered

structure ArtifactRawSourcePreserved
    (rawJson : String) (selection : Selection)
    (artifact : Frontend.Program.Artifact)
    extends ArtifactRawSourceContext rawJson selection artifact where
  sourceRun :
    ObjectPositivePreserved context selected.root
      artifact.codeArtifact.ordered

namespace ArtifactRawSourceContext

def withSourceRun
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    (sourceRun :
      ObjectPositiveRunEquivalent ctx.context ctx.selected.root
        artifact.codeArtifact.ordered) :
    ArtifactRawSourceEquivalent rawJson selection artifact :=
  { ctx with
    sourceRun := sourceRun }

def withSourcePreserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    (sourceRun :
      ObjectPositivePreserved ctx.context ctx.selected.root
        artifact.codeArtifact.ordered) :
    ArtifactRawSourcePreserved rawJson selection artifact :=
  { ctx with
    sourceRun := sourceRun }

def withSourceCodePreserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (sourceRun :
      CodePositivePreserved ctx.context code
        artifact.codeArtifact.ordered) :
    ArtifactRawSourcePreserved rawJson selection artifact :=
  ctx.withSourcePreserved (sourceRun.toObjectPositive hCode)

theorem sourcePreserved_of_dispatcherSeq
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (hSeq :
      ∀ rawScope,
        Raw.SourceSemantics.functionScope? code = some rawScope →
          ∀ (rawFuel : Nat) (state : State),
            ∃ orderedFuel,
              DispatcherSeqRunForward rawFuel orderedFuel
                ctx.context rawScope code artifact.codeArtifact.ordered state) :
    Nonempty (ArtifactRawSourcePreserved rawJson selection artifact) := by
  rcases ctx.code_functionScope hCode with ⟨rawScope, hScope⟩
  exact ⟨
    ctx.withSourceCodePreserved hCode
      (CodePositivePreserved.of_scope_dispatcher_seq
        hScope (hSeq rawScope hScope))⟩

end ArtifactRawSourceContext

namespace ArtifactRawSourceEquivalent

def preserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hSource :
      ArtifactRawSourceEquivalent rawJson selection artifact) :
    ArtifactRawSourcePreserved rawJson selection artifact :=
  { hSource.toArtifactRawSourceContext with
    sourceRun := hSource.sourceRun.preserved }

end ArtifactRawSourceEquivalent

theorem rawSourceEquivalentToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hSource :
      ArtifactRawSourceEquivalent rawJson selection artifact) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) hSource.context hSource.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases hSource.sourceRun.run_eq rawFuel
      (Yul.EndToEnd.installedSourceState artifact baseSource) with
    ⟨orderedFuel, hRawOrdered⟩
  rcases
      Yul.EndToEnd.optimizedSolcYulToRawBytecode
        (object := hSource.program.object)
        (linkerSymbols := hSource.linkerSymbols)
        (artifact := artifact)
        (sourceFuel := orderedFuel)
        (baseSource := baseSource)
        hSource.compile with
    ⟨structuredFuel, hAccepted, hOrderedBytecode⟩
  have hRawOrderedForward :
      Simulation.Interaction.ForwardRel
        Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
        (rawObjectRun (rawFuel + 1) hSource.context hSource.selected.root
          (Yul.EndToEnd.installedSourceState artifact baseSource))
        (orderedRun (orderedFuel + 1) artifact.codeArtifact.ordered
          (Yul.EndToEnd.installedSourceState artifact baseSource)) :=
    runForward_of_eq hRawOrdered
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact
    Simulation.Interaction.ForwardRel.trans
      hRawOrderedForward hOrderedBytecode
      (by
        intro rawDone orderedError hSame hTruncated
        subst rawDone
        exact ⟨orderedError, rfl, hTruncated⟩)

theorem rawSourcePreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hSource :
      ArtifactRawSourcePreserved rawJson selection artifact) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) hSource.context hSource.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases hSource.sourceRun.forward rawFuel
      (Yul.EndToEnd.installedSourceState artifact baseSource) with
    ⟨orderedFuel, hRawOrderedForward⟩
  rcases
      Yul.EndToEnd.optimizedSolcYulToRawBytecode
        (object := hSource.program.object)
        (linkerSymbols := hSource.linkerSymbols)
        (artifact := artifact)
        (sourceFuel := orderedFuel)
        (baseSource := baseSource)
        hSource.compile with
    ⟨structuredFuel, hAccepted, hOrderedBytecode⟩
  refine ⟨structuredFuel, hAccepted, ?_⟩
  exact
    Simulation.Interaction.ForwardRel.trans
      hRawOrderedForward hOrderedBytecode
      (by
        intro rawDone orderedError hSame hTruncated
        subst rawDone
        exact ⟨orderedError, rfl, hTruncated⟩)

theorem rawSourceCodePreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (hCodeRun :
      CodePositivePreserved ctx.context code
        artifact.codeArtifact.ordered) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) :=
  rawSourcePreservedToRawBytecode
    (ctx.withSourceCodePreserved hCode hCodeRun)

theorem rawSourceDispatcherSeqPreservedToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (hSeq :
      ∀ rawScope,
        Raw.SourceSemantics.functionScope? code = some rawScope →
          ∀ (rawFuel : Nat) (state : State),
            ∃ orderedFuel,
              DispatcherSeqRunForward rawFuel orderedFuel
                ctx.context rawScope code artifact.codeArtifact.ordered state) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases ctx.code_functionScope hCode with ⟨rawScope, hScope⟩
  exact
    rawSourceCodePreservedToRawBytecode
      (rawFuel := rawFuel) (baseSource := baseSource)
      ctx hCode
      (CodePositivePreserved.of_scope_dispatcher_seq
        hScope (hSeq rawScope hScope))

theorem rawSourceCodeEquivalentToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {rawFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code)
    (hCodeRun :
      CodePositiveRunEquivalent ctx.context code
        artifact.codeArtifact.ordered) :
    ∃ structuredFuel : Nat,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (RawSourceBytecodePrefixDoneRel artifact)
          (rawObjectRun (rawFuel + 1) ctx.context ctx.selected.root
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) :=
  rawSourceCodePreservedToRawBytecode
    ctx hCode hCodeRun.preserved

end SourcePreservation
end Raw
end RawAst
end Solidity
end EvmCompiler
