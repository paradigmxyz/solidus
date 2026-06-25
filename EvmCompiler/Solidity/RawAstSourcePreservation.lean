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

/-- Intermediate statement-list outcomes inside one lexical block. Most
statements preserve exact state; administrative empty-block stubs may apply the
block-entry restriction early on abrupt states. The enclosing block erases
that distinction. -/
def BlockSeqDoneRel (entryStore : EvmYul.Yul.VarStore) :
    Except Failure State → Except Failure State → Prop :=
  Simulation.Interaction.ExceptRel Eq
    (fun raw ordered =>
      ordered = raw ∨ ordered = raw.restrictStoreTo entryStore)

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

/-- Primitive evaluation at potentially different source/target meta-fuels.
The recursive frontend proof derives this locally; equal fuels use
`forward_refl`, while widened target fuel needs a primitive-family lemma. -/
def PrimitiveRunForward (rawFuel orderedFuel : Nat)
    (state : State) (op : EvmYul.Operation .Yul)
    (args : List Frontend.Word) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
    (Yul.InteractionSemantics.primitiveSemantics.eval
      rawFuel state op args)
    (Yul.InteractionSemantics.primitiveSemantics.eval
      orderedFuel state op args)

/-- Generic lexical-block preservation under an explicit raw function context
and active ordered contract. -/
def BlockCodeRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCode : List Raw.Stmt) (orderedCode : List Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    SameDoneRel
    (Raw.SourceSemantics.execBlock rawFuel context rawCode state)
    (Yul.InteractionSemantics.exec orderedFuel (.Block orderedCode)
      (some contract) state)

/-- Selection and recursive body preservation for a lowered switch. Successful
frontend elaboration will construct this relation from the raw/ordered case
lists, so statement simulation never receives a case-specific replay premise. -/
def SwitchCasesRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt))
    (rawDefault : List Raw.Stmt)
    (orderedCases : List (Frontend.Word × List Frontend.AstStmt))
    (orderedDefault : List Frontend.AstStmt)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (stateAfterCondition : State) (value : Frontend.Word),
    ∃ rawBody orderedBody,
      Raw.SourceSemantics.selectSwitchCase value rawDefault rawCases =
          some rawBody ∧
        EvmYul.Yul.selectSwitchCase value orderedDefault orderedCases =
          orderedBody ∧
        BlockCodeRunForward rawFuel orderedFuel
          context rawBody orderedBody contract stateAfterCondition

/-- Compiler-owned evidence that one elaborated expression survives object
builtin resolution and converts to the exact canonical ordered expression. -/
structure ExprNormalized (context : Frontend.ObjectBuiltinContext)
    (front : Frontend.Expr) (ordered : Frontend.AstExpr) where
  resolved : Frontend.Expr
  resolve : front.resolveObjectBuiltinsIn? context = some resolved
  toYul : resolved.toYul? = some ordered

structure ExprListNormalized (context : Frontend.ObjectBuiltinContext)
    (front : List Frontend.Expr) (ordered : List Frontend.AstExpr) where
  resolved : List Frontend.Expr
  resolve : Frontend.Expr.List.resolveObjectBuiltinsIn? front context =
    some resolved
  toYul : Frontend.Expr.List.toYul? resolved = some ordered

structure StmtNormalized (context : Frontend.ObjectBuiltinContext)
    (front : Frontend.Stmt) (ordered : Frontend.AstStmt) where
  resolved : Frontend.Stmt
  resolve : front.resolveObjectBuiltinsIn? context = some resolved
  toYul : resolved.toYul? = some ordered

structure StmtListNormalized (context : Frontend.ObjectBuiltinContext)
    (front : List Frontend.Stmt) (ordered : List Frontend.AstStmt) where
  resolved : List Frontend.Stmt
  resolve : Frontend.Stmt.List.resolveObjectBuiltinsIn? front context =
    some resolved
  toYul : Frontend.Stmt.List.toYul? resolved = some ordered

namespace ExprListNormalized

def nil (context : Frontend.ObjectBuiltinContext) :
    ExprListNormalized context [] [] where
  resolved := []
  resolve := by simp [Frontend.Expr.List.resolveObjectBuiltinsIn?]
  toYul := rfl

theorem nil_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : List Frontend.AstExpr}
    (hNormalized : ExprListNormalized context [] ordered) :
    ordered = [] := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Expr.List.toYul?] using hToYul.symm

theorem cons_parts
    {context : Frontend.ObjectBuiltinContext}
    {frontHead : Frontend.Expr} {frontTail : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    (hNormalized :
      ExprListNormalized context (frontHead :: frontTail)
        ordered) :
    ∃ orderedHead orderedTail,
      ordered = orderedHead :: orderedTail ∧
        Nonempty (ExprNormalized context frontHead orderedHead) ∧
        Nonempty (ExprListNormalized context frontTail orderedTail) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.List.resolveObjectBuiltinsIn? at hResolve
  cases hHeadResolve :
      Frontend.Expr.resolveObjectBuiltinsIn? frontHead context with
  | none => simp [hHeadResolve] at hResolve
  | some resolvedHead =>
      cases hTailResolve :
          Frontend.Expr.List.resolveObjectBuiltinsIn? frontTail context with
      | none => simp [hHeadResolve, hTailResolve] at hResolve
      | some resolvedTail =>
          simp [hHeadResolve, hTailResolve] at hResolve
          subst resolved
          unfold Frontend.Expr.List.toYul? at hToYul
          cases hHeadToYul : Frontend.Expr.toYul? resolvedHead with
          | none => simp [hHeadToYul] at hToYul
          | some headYul =>
              cases hTailToYul :
                  Frontend.Expr.List.toYul? resolvedTail with
              | none => simp [hHeadToYul, hTailToYul] at hToYul
              | some tailYul =>
                  simp [hHeadToYul, hTailToYul] at hToYul
                  exact
                    ⟨headYul, tailYul, hToYul.symm,
                      ⟨{
                        resolved := resolvedHead
                        resolve := hHeadResolve
                        toYul := hHeadToYul }⟩,
                      ⟨{
                        resolved := resolvedTail
                        resolve := hTailResolve
                        toYul := hTailToYul }⟩⟩

end ExprListNormalized

namespace StmtListNormalized

def nil (context : Frontend.ObjectBuiltinContext) :
    StmtListNormalized context [] [] where
  resolved := []
  resolve := by simp [Frontend.Stmt.List.resolveObjectBuiltinsIn?]
  toYul := rfl

theorem nil_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : List Frontend.AstStmt}
    (hNormalized : StmtListNormalized context [] ordered) :
    ordered = [] := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.List.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.List.toYul?] using hToYul.symm

theorem cons_parts
    {context : Frontend.ObjectBuiltinContext}
    {frontHead : Frontend.Stmt} {frontTail : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    (hNormalized :
      StmtListNormalized context (frontHead :: frontTail)
        ordered) :
    ∃ orderedHead orderedTail,
      ordered = orderedHead :: orderedTail ∧
        Nonempty (StmtNormalized context frontHead orderedHead) ∧
        Nonempty (StmtListNormalized context frontTail orderedTail) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.List.resolveObjectBuiltinsIn? at hResolve
  cases hHeadResolve :
      Frontend.Stmt.resolveObjectBuiltinsIn? frontHead context with
  | none => simp [hHeadResolve] at hResolve
  | some resolvedHead =>
      cases hTailResolve :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? frontTail context with
      | none => simp [hHeadResolve, hTailResolve] at hResolve
      | some resolvedTail =>
          simp [hHeadResolve, hTailResolve] at hResolve
          subst resolved
          unfold Frontend.Stmt.List.toYul? at hToYul
          cases hHeadToYul : Frontend.Stmt.toYul? resolvedHead with
          | none => simp [hHeadToYul] at hToYul
          | some headYul =>
              cases hTailToYul :
                  Frontend.Stmt.List.toYul? resolvedTail with
              | none => simp [hHeadToYul, hTailToYul] at hToYul
              | some tailYul =>
                  simp [hHeadToYul, hTailToYul] at hToYul
                  exact
                    ⟨headYul, tailYul, hToYul.symm,
                      ⟨{
                        resolved := resolvedHead
                        resolve := hHeadResolve
                        toYul := hHeadToYul }⟩,
                      ⟨{
                        resolved := resolvedTail
                        resolve := hTailResolve
                        toYul := hTailToYul }⟩⟩

end StmtListNormalized

namespace ExprNormalized

theorem literal_parts
    {context : Frontend.ObjectBuiltinContext}
    {literal : Raw.Literal}
    {state finalState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    (hElab :
      (Elab.Expr.elaborate (.literal literal)).run state =
        .ok (front, finalState))
    (hNormalized : ExprNormalized context front ordered) :
    ∃ value,
      Raw.SourceSemantics.literalWord? literal = some value ∧
        ordered = .Lit value := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  cases literal with
  | number value =>
      simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
      rcases hElab with ⟨hFront, hState⟩
      simp [Frontend.Expr.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
      subst ordered
      exact ⟨value, rfl, rfl⟩
  | bool value =>
      simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
      rcases hElab with ⟨hFront, hState⟩
      simp [Frontend.Expr.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
      subst ordered
      exact ⟨EvmYul.UInt256.ofNat (if value then 1 else 0), rfl, rfl⟩
  | stringLit value =>
      simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
      rcases hElab with ⟨hFront, hState⟩
      simp [Frontend.Expr.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      cases hWord : Frontend.StringLiteral.word? value with
      | none => simp [Frontend.Expr.toYul?, hWord] at hToYul
      | some word =>
          simp [Frontend.Expr.toYul?, hWord] at hToYul
          subst ordered
          exact ⟨word, by simp [Raw.SourceSemantics.literalWord?, hWord], rfl⟩
  | bytesLit bytes =>
      simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
      rcases hElab with ⟨hFront, hState⟩
      simp [Frontend.Expr.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      cases hWord : Frontend.StringLiteral.wordBytes? bytes with
      | none => simp [Frontend.Expr.toYul?, hWord] at hToYul
      | some word =>
          simp [Frontend.Expr.toYul?, hWord] at hToYul
          subst ordered
          exact ⟨word, by simp [Raw.SourceSemantics.literalWord?, hWord], rfl⟩

theorem identifier_ordered
    {context : Frontend.ObjectBuiltinContext}
    {name : Name} {state finalState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    (hElab :
      (Elab.Expr.elaborate (.identifier name)).run state =
        .ok (front, finalState))
    (hNormalized : ExprNormalized context front ordered) :
    ordered = .Var name := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Elab.Expr.elaborate at hElab
  simp at hElab
  cases hVisible :
      (Elab.requireIdentifierVisible name "expression").run state with
  | error err => simp [hVisible] at hElab
  | ok result =>
      rcases result with ⟨_, visibleState⟩
      simp [hVisible] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hResolved : resolved = .var name := by
        unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
        exact Option.some.inj hResolve.symm
      subst resolved
      simpa [Frontend.Expr.toYul?] using hToYul.symm

theorem primitive_call_parts
    {context : Frontend.ObjectBuiltinContext}
    {callee : Name} {args : List Frontend.Expr}
    {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context (.call .primitive callee args) ordered) :
    ∃ op orderedArgs,
      Frontend.Primitive.ofName? callee = some op ∧
        ordered = .Call (.inl op) orderedArgs ∧
        Nonempty (ExprListNormalized context args orderedArgs) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgsResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none => simp [hArgsResolve] at hResolve
  | some resolvedArgs =>
      simp [hArgsResolve] at hResolve
      subst resolved
      unfold Frontend.Expr.toYul? at hToYul
      cases hOp : Frontend.Primitive.ofName? callee with
      | none => simp [hOp] at hToYul
      | some op =>
          cases hArgsToYul : Frontend.Expr.List.toYul? resolvedArgs with
          | none => simp [hOp, hArgsToYul] at hToYul
          | some orderedArgs =>
              simp [hOp, hArgsToYul] at hToYul
              exact
                ⟨op, orderedArgs, rfl, hToYul.symm,
                  ⟨{
                    resolved := resolvedArgs
                    resolve := hArgsResolve
                    toYul := hArgsToYul }⟩⟩

theorem user_call_parts
    {context : Frontend.ObjectBuiltinContext}
    {callee : Name} {args : List Frontend.Expr}
    {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context (.call .user callee args) ordered) :
    ∃ orderedArgs,
      ordered = .Call (.inr callee) orderedArgs ∧
        Nonempty (ExprListNormalized context args orderedArgs) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgsResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none => simp [hArgsResolve] at hResolve
  | some resolvedArgs =>
      simp [hArgsResolve] at hResolve
      subst resolved
      unfold Frontend.Expr.toYul? at hToYul
      cases hArgsToYul : Frontend.Expr.List.toYul? resolvedArgs with
      | none => simp [hArgsToYul] at hToYul
      | some orderedArgs =>
          simp [hArgsToYul] at hToYul
          exact
            ⟨orderedArgs, hToYul.symm,
              ⟨{
                resolved := resolvedArgs
                resolve := hArgsResolve
                toYul := hArgsToYul }⟩⟩

end ExprNormalized

namespace StmtNormalized

theorem let_none_ordered
    {context : Frontend.ObjectBuiltinContext}
    {names : List Name} {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.letDecl names none) ordered) :
    ordered = .Let names none := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.toYul?] using hToYul.symm

theorem let_some_parts
    {context : Frontend.ObjectBuiltinContext}
    {names : List Name} {value : Frontend.Expr}
    {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.letDecl names (some value)) ordered) :
    ∃ orderedValue,
      ordered = .Let names (some orderedValue) ∧
        Nonempty (ExprNormalized context value orderedValue) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hValueResolve : value.resolveObjectBuiltinsIn? context with
  | none => simp [hValueResolve] at hResolve
  | some resolvedValue =>
      simp [hValueResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hValueToYul : resolvedValue.toYul? with
      | none => simp [hValueToYul] at hToYul
      | some orderedValue =>
          simp [hValueToYul] at hToYul
          exact
            ⟨orderedValue, hToYul.symm,
              ⟨{
                resolved := resolvedValue
                resolve := hValueResolve
                toYul := hValueToYul }⟩⟩

theorem assign_parts
    {context : Frontend.ObjectBuiltinContext}
    {names : List Name} {value : Frontend.Expr}
    {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.assign names value) ordered) :
    ∃ orderedValue,
      ordered = .Assign names orderedValue ∧
        Nonempty (ExprNormalized context value orderedValue) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hValueResolve : value.resolveObjectBuiltinsIn? context with
  | none => simp [hValueResolve] at hResolve
  | some resolvedValue =>
      simp [hValueResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hValueToYul : resolvedValue.toYul? with
      | none => simp [hValueToYul] at hToYul
      | some orderedValue =>
          simp [hValueToYul] at hToYul
          exact
            ⟨orderedValue, hToYul.symm,
              ⟨{
                resolved := resolvedValue
                resolve := hValueResolve
                toYul := hValueToYul }⟩⟩

theorem block_parts
    {context : Frontend.ObjectBuiltinContext}
    {body : List Frontend.Stmt} {ordered : Frontend.AstStmt}
    (hNormalized : StmtNormalized context (.block body) ordered) :
    ∃ orderedBody,
      ordered = .Block orderedBody ∧
        Nonempty (StmtListNormalized context body orderedBody) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hBodyResolve :
      Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
  | none => simp [hBodyResolve] at hResolve
  | some resolvedBody =>
      simp [hBodyResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hBodyToYul : Frontend.Stmt.List.toYul? resolvedBody with
      | none => simp [hBodyToYul] at hToYul
      | some orderedBody =>
          simp [hBodyToYul] at hToYul
          exact
            ⟨orderedBody, hToYul.symm,
              ⟨{
                resolved := resolvedBody
                resolve := hBodyResolve
                toYul := hBodyToYul }⟩⟩

theorem if_parts
    {context : Frontend.ObjectBuiltinContext}
    {condition : Frontend.Expr} {body : List Frontend.Stmt}
    {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.ifThen condition body) ordered) :
    ∃ orderedCondition orderedBody,
      ordered = .If orderedCondition orderedBody ∧
        Nonempty (ExprNormalized context condition orderedCondition) ∧
        Nonempty (StmtListNormalized context body orderedBody) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hConditionResolve : condition.resolveObjectBuiltinsIn? context with
  | none => simp [hConditionResolve] at hResolve
  | some resolvedCondition =>
      cases hBodyResolve :
          Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
      | none => simp [hConditionResolve, hBodyResolve] at hResolve
      | some resolvedBody =>
          simp [hConditionResolve, hBodyResolve] at hResolve
          subst resolved
          unfold Frontend.Stmt.toYul? at hToYul
          cases hConditionToYul : resolvedCondition.toYul? with
          | none => simp [hConditionToYul] at hToYul
          | some orderedCondition =>
              cases hBodyToYul : Frontend.Stmt.List.toYul? resolvedBody with
              | none => simp [hConditionToYul, hBodyToYul] at hToYul
              | some orderedBody =>
                  simp [hConditionToYul, hBodyToYul] at hToYul
                  exact
                    ⟨orderedCondition, orderedBody, hToYul.symm,
                      ⟨{
                        resolved := resolvedCondition
                        resolve := hConditionResolve
                        toYul := hConditionToYul }⟩,
                      ⟨{
                        resolved := resolvedBody
                        resolve := hBodyResolve
                        toYul := hBodyToYul }⟩⟩

theorem break_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : Frontend.AstStmt}
    (hNormalized : StmtNormalized context .break ordered) :
    ordered = .Break := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.toYul?] using hToYul.symm

theorem continue_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : Frontend.AstStmt}
    (hNormalized : StmtNormalized context .continue ordered) :
    ordered = .Continue := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.toYul?] using hToYul.symm

theorem leave_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : Frontend.AstStmt}
    (hNormalized : StmtNormalized context .leave ordered) :
    ordered = .Leave := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.toYul?] using hToYul.symm

end StmtNormalized

/-- Static compiler evidence for one raw function binding. It records the
checked function elaboration and its canonical ordered target, but no semantic
preservation premise. `generatedScopes` is the definition-site lexical suffix
under which the function body was elaborated. -/
structure CompiledFunctionBinding
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (generated : Name)
    (rawFn : Raw.SourceSemantics.FunctionDef)
    (generatedScopes : List (List (Name × Name))) where
  frontFn : Frontend.FunctionDef
  functionState : Elab.State
  finalFunctionState : Elab.State
  orderedBody : List Frontend.AstStmt
  functionScopes : functionState.functionScopes = generatedScopes
  elaborates :
    (Elab.FunctionDef.elaborate rawFn.params rawFn.returns rawFn.body).run
        functionState = .ok (frontFn, finalFunctionState)
  bodyNormalized :
    StmtListNormalized builtinContext frontFn.body orderedBody
  orderedLookup :
    contract.functions.lookup generated =
      some (.Def rawFn.params rawFn.returns orderedBody)

/-- One raw function scope and the generated-name scope produced for the same
block. Generated lookup is complete with respect to raw lookup; each resolved
binding carries its checked canonical target. -/
structure CompiledFunctionScope
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (rawScope : Raw.SourceSemantics.FunctionScope)
    (generatedScope : List (Name × Name))
    (generatedScopes : List (List (Name × Name))) : Prop where
  binding :
    ∀ {rawName generated},
      Elab.lookupFunctionInScope rawName generatedScope = some generated →
        ∃ rawFn,
          Raw.SourceSemantics.lookupFunctionInScope rawName rawScope =
              some rawFn ∧
            Nonempty
              (CompiledFunctionBinding builtinContext contract
                generated rawFn generatedScopes)
  rawLookupNone :
    ∀ {rawName},
      Elab.lookupFunctionInScope rawName generatedScope = none →
        Raw.SourceSemantics.lookupFunctionInScope rawName rawScope = none

/-- Lexically aligned raw and generated function-scope stacks. The head scope
stores definition-site evidence against the entire generated suffix. -/
inductive CompiledFunctionScopes
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) :
    List Raw.SourceSemantics.FunctionScope →
      List (List (Name × Name)) → Prop where
  | nil : CompiledFunctionScopes builtinContext contract [] []
  | cons
      {rawScope : Raw.SourceSemantics.FunctionScope}
      {rawRest : List Raw.SourceSemantics.FunctionScope}
      {generatedScope : List (Name × Name)}
      {generatedRest : List (List (Name × Name))}
      (head :
        CompiledFunctionScope builtinContext contract rawScope generatedScope
          (generatedScope :: generatedRest))
      (tail :
        CompiledFunctionScopes builtinContext contract rawRest generatedRest) :
      CompiledFunctionScopes builtinContext contract
        (rawScope :: rawRest) (generatedScope :: generatedRest)

namespace CompiledFunctionScopes

/-- Resolve an elaborator user-function lookup to the corresponding raw
definition-site lexical suffix and checked ordered function binding. -/
theorem resolve
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawScopes : List Raw.SourceSemantics.FunctionScope}
    {generatedScopes : List (List (Name × Name))}
    (hScopes :
      CompiledFunctionScopes builtinContext contract rawScopes generatedScopes)
    {rawName generated : Name}
    (hResolve :
      Elab.resolveFunctionIn rawName generatedScopes = some generated) :
    ∃ rawFn rawLexical generatedLexical,
      Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn
          rawName rawScopes = some (rawFn, rawLexical) ∧
        Nonempty
          (CompiledFunctionBinding builtinContext contract
            generated rawFn generatedLexical) ∧
        CompiledFunctionScopes builtinContext contract
          rawLexical generatedLexical := by
  induction hScopes with
  | nil =>
      simp [Elab.resolveFunctionIn] at hResolve
  | @cons rawScope rawRest generatedScope generatedRest hHead hTail ih =>
      cases hLookup : Elab.lookupFunctionInScope rawName generatedScope with
      | none =>
          have hRawNone := hHead.rawLookupNone hLookup
          have hOuter :
              Elab.resolveFunctionIn rawName generatedRest = some generated := by
            simpa [Elab.resolveFunctionIn, hLookup] using hResolve
          rcases ih hOuter with
            ⟨rawFn, rawLexical, generatedLexical,
              hRawResolve, hBinding, hLexical⟩
          refine
            ⟨rawFn, rawLexical, generatedLexical, ?_, hBinding, hLexical⟩
          simp [Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn,
            hRawNone, hRawResolve]
      | some resolved =>
          have hGenerated : resolved = generated := by
            simpa [Elab.resolveFunctionIn, hLookup] using hResolve
          subst resolved
          rcases hHead.binding hLookup with
            ⟨rawFn, hRawLookup, hBinding⟩
          refine
            ⟨rawFn, rawScope :: rawRest, generatedScope :: generatedRest,
              ?_, hBinding, .cons hHead hTail⟩
          simp [Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn,
            hRawLookup]

end CompiledFunctionScopes

namespace CompiledFunctionBinding

/-- Peel the checked function elaboration down to the lexical block run used
by recursive semantic preservation. Identifier-scope setup is erased, while
the definition-site generated function scopes are retained exactly. -/
theorem block_parts
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generated : Name}
    {rawFn : Raw.SourceSemantics.FunctionDef}
    {generatedScopes : List (List (Name × Name))}
    (hBinding :
      CompiledFunctionBinding builtinContext contract
        generated rawFn generatedScopes) :
    ∃ bodyState finalBodyState frontBody orderedBody,
      bodyState.functionScopes = generatedScopes ∧
        (Elab.Stmt.List.elaborateBlock rawFn.body true).run bodyState =
          .ok (frontBody, finalBodyState) ∧
        Nonempty (StmtListNormalized builtinContext frontBody orderedBody) ∧
        contract.functions.lookup generated =
          some (.Def rawFn.params rawFn.returns orderedBody) := by
  rcases hBinding with
    ⟨frontFn, functionState, finalFunctionState, orderedBody,
      hFunctionScopes, hFunction, hNormalized, hOrderedLookup⟩
  unfold Elab.FunctionDef.elaborate at hFunction
  simp [StateT.run_bind] at hFunction
  cases hPush : Elab.pushIdentifierScope.run functionState with
  | error err => simp [hPush] at hFunction
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      have hPushScopes :
          pushedState.functionScopes = functionState.functionScopes :=
        Elab.pushIdentifierScope_preserves_functionScopes hPush
      simp [hPush] at hFunction
      cases hDeclare :
          (Elab.declareIdentifiers (rawFn.params ++ rawFn.returns)
            "function parameter/result").run pushedState with
      | error err => simp [hDeclare] at hFunction
      | ok declareResult =>
          rcases declareResult with ⟨_, declaredState⟩
          have hDeclareScopes :
              declaredState.functionScopes = pushedState.functionScopes :=
            Elab.declareIdentifiers_preserves_functionScopes
              (rawFn.params ++ rawFn.returns)
              "function parameter/result" hDeclare
          simp [hDeclare] at hFunction
          cases hBody :
              (Elab.Stmt.List.elaborateBlock rawFn.body true).run
                declaredState with
          | error err => simp [hBody] at hFunction
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              simp [hBody] at hFunction
              cases hPop : Elab.popIdentifierScope.run bodyState with
              | error err => simp [hPop] at hFunction
              | ok popResult =>
                  rcases popResult with ⟨_, poppedState⟩
                  simp [hPop] at hFunction
                  rcases hFunction with ⟨hFrontFn, _hFinalState⟩
                  have hFrontBody : frontFn.body = frontBody := by
                    rw [← hFrontFn]
                  rw [hFrontBody] at hNormalized
                  refine
                    ⟨declaredState, bodyState, frontBody, orderedBody,
                      ?_, hBody, ⟨hNormalized⟩, hOrderedLookup⟩
                  rw [hDeclareScopes, hPushScopes, hFunctionScopes]

end CompiledFunctionBinding

/-- Bundled semantic evidence for one elaborated raw user call. The frontend
derivation supplies the generated callee lookup; recursive preservation
supplies the callee body for every argument result. -/
structure GeneratedUserCallRun (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawName : Name) (rawArgs : List Raw.Expr)
    (generated : Name) (orderedArgs : List Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) where
  fn : Raw.SourceSemantics.FunctionDef
  lexicalScopes : List Raw.SourceSemantics.FunctionScope
  orderedBody : List Frontend.AstStmt
  notClz : rawName ≠ "clz"
  callClass : CallClass.classifyCall rawName = .user
  rawLookup :
    Raw.SourceSemantics.lookupFunctionWithLexicalScopes context rawName =
      some (fn, lexicalScopes)
  orderedLookup :
    contract.functions.lookup generated =
      some (.Def fn.params fn.returns orderedBody)
  argsForward :
    ArgsRunForward (rawFuel + 1) (orderedFuel + 1)
      context rawArgs.reverse orderedArgs.reverse contract state
  bodyForward :
    ∀ (stateAfterArgs : State) (values : List Frontend.Word),
      BlockCodeRunForward rawFuel orderedFuel
        { context with functionScopes := lexicalScopes }
        fn.body orderedBody contract
        (Yul.InteractionSemantics.stateModel.withSource stateAfterArgs
          (EvmYul.Yul.State.mkOk
            (stateAfterArgs.initcall fn.params fn.returns values.reverse)))

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

theorem exprValuesRunForward_identifier_succ_any
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name}
    {contract : Frontend.AstContract} {state : State} :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.identifier name) (.Var name) contract state := by
  cases hLookup : state.lookup? name with
  | some value =>
      exact exprValuesRunForward_identifier_succ hLookup
  | none =>
      unfold ExprValuesRunForward
      unfold Raw.SourceSemantics.evalValues
        Yul.InteractionSemantics.evalValues Yul.Source.Canonical.evalValues
        Yul.Source.Effectful.evalValues
      simp only [hLookup, Yul.InteractionSemantics.stateModel, id_eq]
      unfold Raw.SourceSemantics.fail
        Yul.Source.Effectful.Control.fail
        Yul.InteractionSemantics.Primitive.fail
      exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_of_elaborated_literal
    {rawFuel orderedFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {literal : Raw.Literal}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hElab :
      (Elab.Expr.elaborate (.literal literal)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.literal literal) ordered contract state := by
  rcases ExprNormalized.literal_parts hElab hNormalized with
    ⟨value, hLiteral, hOrdered⟩
  subst ordered
  exact exprValuesRunForward_literal_succ hLiteral

theorem exprValuesRunForward_of_elaborated_identifier
    {rawFuel orderedFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {name : Name}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hElab :
      (Elab.Expr.elaborate (.identifier name)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.identifier name) ordered contract state := by
  have hOrdered := ExprNormalized.identifier_ordered hElab hNormalized
  subst ordered
  exact exprValuesRunForward_identifier_succ_any

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

/-- Semantic compiler interface for one expression under a constant target
fuel slack. The successor shape is stable under recursive argument traversal,
while the slack absorbs fixed frontend expansion depth. -/
def ExprElaborationRunForward
    (slack : Nat)
    (rawContext : Raw.SourceSemantics.Context)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawFuel : Nat)
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    (Elab.Expr.elaborate rawExpr).run elabState =
        .ok (front, finalElabState) →
      ExprNormalized builtinContext front ordered →
        ExprValuesRunForward rawFuel (rawFuel + slack)
          rawContext rawExpr ordered contract state

/-- Source-facing recursive expression interface. Unlike the older local
scaffold above, this interface only accepts elaborator states whose generated
function scopes are checked against the active raw lexical context. -/
def ScopedExprElaborationRunForward
    (slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawFuel : Nat)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    CompiledFunctionScopes builtinContext contract
        rawContext.functionScopes elabState.functionScopes →
      (Elab.Expr.elaborate rawExpr).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext rawExpr ordered contract state

/-- Recursive lexical-block interface paired with
`ScopedExprElaborationRunForward`. Child blocks construct a fresh head scope;
function calls reuse the definition-site suffix returned by
`CompiledFunctionScopes.resolve`. -/
def ScopedBlockElaborationRunForward
    (slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawFuel : Nat)
    {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    CompiledFunctionScopes builtinContext contract
        rawContext.functionScopes elabState.functionScopes →
      (Elab.Stmt.List.elaborateBlock rawCode true).run elabState =
          .ok (front, finalElabState) →
        StmtListNormalized builtinContext front ordered →
          BlockCodeRunForward rawFuel (rawFuel + slack)
            rawContext rawCode ordered contract state

/-- Pointwise checked expression compilation, independent of the order in
which runtime argument evaluation visits the list. -/
inductive ExprListCompiled (builtinContext : Frontend.ObjectBuiltinContext) :
    List Raw.Expr → List Frontend.AstExpr → Prop where
  | nil : ExprListCompiled builtinContext [] []
  | cons
      {rawHead : Raw.Expr} {orderedHead : Frontend.AstExpr}
      {rawTail : List Raw.Expr} {orderedTail : List Frontend.AstExpr}
      {frontHead : Frontend.Expr}
      {elabState finalElabState : Elab.State}
      (headElaborates :
        (Elab.Expr.elaborate rawHead).run elabState =
          .ok (frontHead, finalElabState))
      (headNormalized :
        ExprNormalized builtinContext frontHead orderedHead)
      (tail : ExprListCompiled builtinContext rawTail orderedTail) :
      ExprListCompiled builtinContext
        (rawHead :: rawTail) (orderedHead :: orderedTail)

namespace ExprListCompiled

theorem of_elaboration
    {builtinContext : Frontend.ObjectBuiltinContext} :
    ∀ {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
      {ordered : List Frontend.AstExpr}
      {elabState finalElabState : Elab.State},
      (Elab.Expr.List.elaborate rawExprs).run elabState =
          .ok (fronts, finalElabState) →
        ExprListNormalized builtinContext fronts ordered →
          ExprListCompiled builtinContext rawExprs ordered := by
  intro rawExprs
  induction rawExprs with
  | nil =>
      intro fronts ordered elabState finalElabState hElab hNormalized
      simp [Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := ExprListNormalized.nil_ordered hNormalized
      subst ordered
      exact .nil
  | cons rawHead rawTail ih =>
      intro fronts ordered elabState finalElabState hElab hNormalized
      unfold Elab.Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Expr.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headElabState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Expr.List.elaborate rawTail).run headElabState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailElabState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases ExprListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              exact
                .cons hHead hHeadNormalized
                  (ih hTail hTailNormalized)

theorem append
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawLeft rawRight : List Raw.Expr}
    {orderedLeft orderedRight : List Frontend.AstExpr}
    (hLeft : ExprListCompiled builtinContext rawLeft orderedLeft)
    (hRight : ExprListCompiled builtinContext rawRight orderedRight) :
    ExprListCompiled builtinContext
      (rawLeft ++ rawRight) (orderedLeft ++ orderedRight) := by
  induction hLeft with
  | nil => exact hRight
  | cons hElab hNormalized hTail ih =>
      exact .cons hElab hNormalized ih

theorem reverse
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hCompiled : ExprListCompiled builtinContext rawExprs ordered) :
    ExprListCompiled builtinContext rawExprs.reverse ordered.reverse := by
  induction hCompiled with
  | nil => exact .nil
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hNormalized hTail ih =>
      simpa using
        append ih
          (.cons hElab hNormalized
            (.nil : ExprListCompiled builtinContext [] []))

end ExprListCompiled

/-- Pointwise expression compilation with one fixed generated lexical scope
stack. This retains precisely the state relation that ordinary user calls need
after runtime reverses the argument list. -/
inductive ScopedExprListCompiled
    (builtinContext : Frontend.ObjectBuiltinContext)
    (generatedScopes : List (List (Name × Name))) :
    List Raw.Expr → List Frontend.AstExpr → Prop where
  | nil : ScopedExprListCompiled builtinContext generatedScopes [] []
  | cons
      {rawHead : Raw.Expr} {orderedHead : Frontend.AstExpr}
      {rawTail : List Raw.Expr} {orderedTail : List Frontend.AstExpr}
      {frontHead : Frontend.Expr}
      {elabState finalElabState : Elab.State}
      (headElaborates :
        (Elab.Expr.elaborate rawHead).run elabState =
          .ok (frontHead, finalElabState))
      (headScopes : elabState.functionScopes = generatedScopes)
      (headNormalized :
        ExprNormalized builtinContext frontHead orderedHead)
      (tail :
        ScopedExprListCompiled builtinContext generatedScopes
          rawTail orderedTail) :
      ScopedExprListCompiled builtinContext generatedScopes
        (rawHead :: rawTail) (orderedHead :: orderedTail)

namespace ScopedExprListCompiled

theorem of_elaboration
    {builtinContext : Frontend.ObjectBuiltinContext} :
    ∀ {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
      {ordered : List Frontend.AstExpr}
      {elabState finalElabState : Elab.State},
      (Elab.Expr.List.elaborate rawExprs).run elabState =
          .ok (fronts, finalElabState) →
        ExprListNormalized builtinContext fronts ordered →
          ScopedExprListCompiled builtinContext elabState.functionScopes
            rawExprs ordered := by
  intro rawExprs
  induction rawExprs with
  | nil =>
      intro fronts ordered elabState finalElabState hElab hNormalized
      simp [Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := ExprListNormalized.nil_ordered hNormalized
      subst ordered
      exact .nil
  | cons rawHead rawTail ih =>
      intro fronts ordered elabState finalElabState hElab hNormalized
      unfold Elab.Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Expr.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headElabState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Expr.List.elaborate rawTail).run headElabState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailElabState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases ExprListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              have hHeadScopes :
                  headElabState.functionScopes =
                    elabState.functionScopes :=
                Elab.Expr.elaborate_preserves_functionScopes
                  rawHead hHead
              have hTailCompiled := ih hTail hTailNormalized
              rw [hHeadScopes] at hTailCompiled
              exact
                .cons hHead rfl hHeadNormalized hTailCompiled

theorem append
    {builtinContext : Frontend.ObjectBuiltinContext}
    {generatedScopes : List (List (Name × Name))}
    {rawLeft rawRight : List Raw.Expr}
    {orderedLeft orderedRight : List Frontend.AstExpr}
    (hLeft :
      ScopedExprListCompiled builtinContext generatedScopes
        rawLeft orderedLeft)
    (hRight :
      ScopedExprListCompiled builtinContext generatedScopes
        rawRight orderedRight) :
    ScopedExprListCompiled builtinContext generatedScopes
      (rawLeft ++ rawRight) (orderedLeft ++ orderedRight) := by
  induction hLeft with
  | nil => exact hRight
  | cons hElab hScopes hNormalized hTail ih =>
      exact .cons hElab hScopes hNormalized ih

theorem reverse
    {builtinContext : Frontend.ObjectBuiltinContext}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hCompiled :
      ScopedExprListCompiled builtinContext generatedScopes
        rawExprs ordered) :
    ScopedExprListCompiled builtinContext generatedScopes
      rawExprs.reverse ordered.reverse := by
  induction hCompiled with
  | nil => exact .nil
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hScopes hNormalized hTail ih =>
      simpa using
        append ih
          (.cons hElab hScopes hNormalized
            (.nil :
              ScopedExprListCompiled builtinContext generatedScopes [] []))

end ScopedExprListCompiled

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

theorem argsRunForward_of_scoped_compiled
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract) :
    ∀ {rawContext : Raw.SourceSemantics.Context}
      {generatedScopes : List (List (Name × Name))}
      {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr},
      CompiledFunctionScopes builtinContext contract
          rawContext.functionScopes generatedScopes →
        ScopedExprListCompiled builtinContext generatedScopes
          rawExprs ordered →
          ∀ (rawBase : Nat) (state : State),
            ArgsRunForward
              (rawBase + 2 * rawExprs.length + 1)
              ((rawBase + slack) + 2 * rawExprs.length + 1)
              rawContext rawExprs ordered contract state := by
  intro rawContext generatedScopes rawExprs ordered hFunctionScopes hCompiled
  induction hCompiled with
  | nil =>
      intro rawBase state
      simpa using
        (argsRunForward_nil_succ
          (rawFuel := rawBase) (orderedFuel := rawBase + slack)
          (context := rawContext) (contract := contract) (state := state))
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hScopes hNormalized hTail ih =>
      intro rawBase state
      let rawTailFuel := rawBase + 2 * rawTail.length + 1
      let orderedTailFuel := rawTailFuel + slack
      have hHeadFunctionScopes :
          CompiledFunctionScopes builtinContext contract
            rawContext.functionScopes elabState.functionScopes := by
        simpa [hScopes] using hFunctionScopes
      have hHeadValues :=
        hExpr (rawTailFuel + 1) hHeadFunctionScopes
          (state := state) hElab hNormalized
      have hHeadRun := exprRunForward_of_values hHeadValues
      have hHeadRun' :
          ExprRunForward (rawTailFuel + 1) (orderedTailFuel + 1)
            rawContext rawHead orderedHead contract state := by
        simpa [orderedTailFuel, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hHeadRun
      have hCons :=
        argsRunForward_cons
          (rawFuel := rawTailFuel) (orderedFuel := orderedTailFuel)
          (context := rawContext) (rawArg := rawHead)
          (rawRest := rawTail) (orderedArg := orderedHead)
          (orderedRest := orderedTail) (contract := contract)
          (state := state) hHeadRun'
          (fun stateAfterHead =>
            by
              simpa [rawTailFuel, orderedTailFuel, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                (ih rawBase stateAfterHead))
      simpa [rawTailFuel, orderedTailFuel, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCons

theorem argsRunForward_reverse_of_scoped_elaboration
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hFunctionScopes :
      CompiledFunctionScopes builtinContext contract
        rawContext.functionScopes elabState.functionScopes)
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (rawBase : Nat) (state : State) :
    ArgsRunForward
      (rawBase + 2 * rawExprs.length + 1)
      ((rawBase + slack) + 2 * rawExprs.length + 1)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    ScopedExprListCompiled.of_elaboration hElab hNormalized
  have hReversed := ScopedExprListCompiled.reverse hCompiled
  simpa using
    argsRunForward_of_scoped_compiled hExpr hFunctionScopes hReversed
      rawBase state

theorem argsRunForward_of_compiled
    {slack : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract) :
    ∀ {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr},
      ExprListCompiled builtinContext rawExprs ordered →
        ∀ (rawBase : Nat) (state : State),
          ArgsRunForward
            (rawBase + 2 * rawExprs.length + 1)
            ((rawBase + slack) + 2 * rawExprs.length + 1)
            rawContext rawExprs ordered contract state := by
  intro rawExprs ordered hCompiled
  induction hCompiled with
  | nil =>
      intro rawBase state
      simpa using
        (argsRunForward_nil_succ
          (rawFuel := rawBase) (orderedFuel := rawBase + slack)
          (context := rawContext) (contract := contract) (state := state))
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hNormalized hTail ih =>
      intro rawBase state
      let rawTailFuel := rawBase + 2 * rawTail.length + 1
      let orderedTailFuel := rawTailFuel + slack
      have hHeadValues :=
        hExpr (rawTailFuel + 1)
          (state := state) hElab hNormalized
      have hHeadRun := exprRunForward_of_values hHeadValues
      have hHeadRun' :
          ExprRunForward (rawTailFuel + 1) (orderedTailFuel + 1)
            rawContext rawHead orderedHead contract state := by
        simpa [orderedTailFuel, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hHeadRun
      have hCons :=
        argsRunForward_cons
          (rawFuel := rawTailFuel) (orderedFuel := orderedTailFuel)
          (context := rawContext) (rawArg := rawHead)
          (rawRest := rawTail) (orderedArg := orderedHead)
          (orderedRest := orderedTail) (contract := contract)
          (state := state) hHeadRun'
          (fun stateAfterHead =>
            by
              simpa [rawTailFuel, orderedTailFuel, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                (ih rawBase stateAfterHead))
      simpa [rawTailFuel, orderedTailFuel, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCons

theorem argsRunForward_reverse_of_elaboration
    {slack : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (rawBase : Nat) (state : State) :
    ArgsRunForward
      (rawBase + 2 * rawExprs.length + 1)
      ((rawBase + slack) + 2 * rawExprs.length + 1)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    ExprListCompiled.of_elaboration hElab hNormalized
  have hReversed := ExprListCompiled.reverse hCompiled
  simpa using
    (argsRunForward_of_compiled hExpr hReversed
      rawBase state)

theorem argsRunForward_of_elaboration
    {slack : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (rawBase : Nat) (state : State) :
    ArgsRunForward
      (rawBase + 2 * rawExprs.length + 1)
      ((rawBase + slack) + 2 * rawExprs.length + 1)
      rawContext rawExprs ordered contract state :=
  argsRunForward_of_compiled hExpr
    (ExprListCompiled.of_elaboration hElab hNormalized) rawBase state

theorem exprValuesRunForward_primitiveCall_of_runs
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {orderedArgs : List Frontend.AstExpr}
    {op : EvmYul.Operation .Yul}
    {contract : Frontend.AstContract} {state : State}
    (hClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .primitive)
    (hOp : Frontend.Primitive.ofName? name = some op)
    (hArgs :
      ArgsRunForward rawFuel orderedFuel context
        rawArgs.reverse orderedArgs.reverse contract state)
    (hPrimitive :
      ∀ (stateAfterArgs : State) (values : List Frontend.Word),
        PrimitiveRunForward rawFuel orderedFuel
          stateAfterArgs op values.reverse) :
    ExprValuesRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.functionCall name rawArgs) (.Call (.inl op) orderedArgs)
      contract state := by
  unfold ExprValuesRunForward ArgsRunForward at *
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    rawFuel context name rawArgs state hClz]
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
      exact hPrimitive result.1 result.2

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
      contract state :=
  exprValuesRunForward_primitiveCall_of_runs
    hClz hClass hOp hArgs
    (fun stateAfterArgs values =>
      forward_refl Yul.FunctionsInteractionPrimitive.Truncated
        (Yul.InteractionSemantics.primitiveSemantics.eval
          fuel stateAfterArgs op values.reverse))

theorem exprValuesRunForward_of_elaborated_primitiveCall
    {slack rawBase : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .primitive)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hPrimitive :
      ∀ (op : EvmYul.Operation .Yul),
        Frontend.Primitive.ofName? name = some op →
          ∀ (stateAfterArgs : State) (values : List Frontend.Word),
            PrimitiveRunForward
              (rawBase + 2 * rawArgs.length + 1)
              ((rawBase + slack) + 2 * rawArgs.length + 1)
              stateAfterArgs op values.reverse) :
    ExprValuesRunForward
      (rawBase + 2 * rawArgs.length + 2)
      ((rawBase + slack) + 2 * rawArgs.length + 2)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  unfold Elab.Expr.elaborate at hElab
  simp at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      simp [hArgs, hClass] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rcases ExprNormalized.primitive_call_parts hNormalized with
        ⟨op, orderedArgs, hOp, rfl, ⟨hArgsNormalized⟩⟩
      let rawArgsFuel := rawBase + 2 * rawArgs.length + 1
      let orderedArgsFuel :=
        (rawBase + slack) + 2 * rawArgs.length + 1
      have hArgsRun :=
        argsRunForward_reverse_of_elaboration hExpr hArgs hArgsNormalized
          rawBase state
      have hCall :=
        exprValuesRunForward_primitiveCall_of_runs
          hNotClz hClass hOp hArgsRun (hPrimitive op hOp)
      have hRawFuel :
          rawBase + 2 * rawArgs.length + 2 =
            (rawBase + 2 * rawArgs.length + 1) + 1 := by
        omega
      have hOrderedFuel :
          (rawBase + slack) + 2 * rawArgs.length + 2 =
            ((rawBase + slack) + 2 * rawArgs.length + 1) + 1 := by
        omega
      rw [hRawFuel, hOrderedFuel]
      exact hCall

theorem exprValuesRunForward_userCall_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawName : Name} {rawArgs : List Raw.Expr}
    {generated : Name} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun : GeneratedUserCallRun rawFuel orderedFuel context
      rawName rawArgs generated orderedArgs contract state) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 2)
      context (.functionCall rawName rawArgs)
      (.Call (.inr generated) orderedArgs) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context rawName rawArgs state hRun.notClz]
  simp only [hRun.callClass]
  rw [Yul.InteractionSemantics.EvalValues.internal_succ]
  have hArgsForward := hRun.argsForward
  unfold ArgsRunForward at hArgsForward
  refine
    Simulation.Interaction.ForwardRel.bind_custom hArgsForward ?_
  intro rawArgsDone orderedArgsDone hArgsDone
  unfold SameDoneRel at hArgsDone
  subst orderedArgsDone
  cases rawArgsDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok argsResult =>
      rcases argsResult with ⟨stateAfterArgs, reversedValues⟩
      change
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
          (Raw.SourceSemantics.call (rawFuel + 1) context
            reversedValues.reverse rawName stateAfterArgs)
          (Yul.InteractionSemantics.call (orderedFuel + 1)
            reversedValues.reverse (some generated) (some contract)
            stateAfterArgs)
      rw [Raw.SourceSemantics.Call.explicit_succ
        rawFuel context reversedValues.reverse rawName stateAfterArgs
        hRun.fn hRun.lexicalScopes hRun.rawLookup]
      rw [Yul.InteractionSemantics.Call.explicit_succ
        orderedFuel reversedValues.reverse generated contract
        hRun.fn.params hRun.fn.returns hRun.orderedBody stateAfterArgs
        hRun.orderedLookup]
      have hBodyForward :=
        hRun.bodyForward stateAfterArgs reversedValues
      unfold BlockCodeRunForward at hBodyForward
      refine
        Simulation.Interaction.ForwardRel.bind_custom
          hBodyForward ?_
      intro rawBodyDone orderedBodyDone hBodyDone
      unfold SameDoneRel at hBodyDone
      subst orderedBodyDone
      cases rawBodyDone with
      | error error =>
          exact Simulation.Interaction.ForwardRel.done rfl
      | ok stateAfterBody =>
          exact Simulation.Interaction.ForwardRel.done rfl

/-- Frontend-owned provider for a direct elaborated user call. The recursive
source-fuel proof will construct it from lexical compilation evidence; callers
see neither generated names nor callee layouts. -/
def UserCallElaborationRunForward
    (slack : Nat)
    (rawContext : Raw.SourceSemantics.Context)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawBase : Nat)
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {state : State},
    (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState) →
      ExprNormalized builtinContext front ordered →
        ∃ generated orderedArgs,
          ordered = .Call (.inr generated) orderedArgs ∧
            Nonempty
              (GeneratedUserCallRun
                (rawBase + 2 * rawArgs.length)
                ((rawBase + slack) + 2 * rawArgs.length)
                rawContext name rawArgs generated orderedArgs contract state)

theorem exprValuesRunForward_of_elaborated_userCall
    {slack rawBase : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hUser :
      UserCallElaborationRunForward
        slack rawContext builtinContext contract)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward
      (rawBase + 2 * rawArgs.length + 2)
      ((rawBase + slack) + 2 * rawArgs.length + 2)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  rcases hUser rawBase hElab hNormalized with
    ⟨generated, orderedArgs, rfl, ⟨hRun⟩⟩
  have hCall := exprValuesRunForward_userCall_succ hRun
  have hRawFuel :
      rawBase + 2 * rawArgs.length + 2 =
        (rawBase + 2 * rawArgs.length) + 2 := by
    omega
  have hOrderedFuel :
      (rawBase + slack) + 2 * rawArgs.length + 2 =
        ((rawBase + slack) + 2 * rawArgs.length) + 2 := by
    omega
  rw [hRawFuel, hOrderedFuel]
  exact hCall

/-- Ordinary generated user calls are preserved from compiler-derived lexical
scope evidence and the lower-fuel recursive expression/block hypotheses. No
callee-preservation or generated-layout premise is exposed. -/
theorem exprValuesRunForward_of_scoped_elaborated_userCall
    {slack rawBase : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract)
    (hBlock :
      ScopedBlockElaborationRunForward slack builtinContext contract)
    (hFunctionScopes :
      CompiledFunctionScopes builtinContext contract
        rawContext.functionScopes elabState.functionScopes)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward
      (rawBase + 2 * rawArgs.length + 2)
      ((rawBase + slack) + 2 * rawArgs.length + 2)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  unfold Elab.Expr.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      have hArgsScopes :
          argsState.functionScopes = elabState.functionScopes :=
        Elab.Expr.List.elaborate_preserves_functionScopes rawArgs hArgs
      have hArgsFunctionScopes :
          CompiledFunctionScopes builtinContext contract
            rawContext.functionScopes argsState.functionScopes := by
        simpa [hArgsScopes] using hFunctionScopes
      simp [hArgs, hClass] at hElab
      cases hResolve :
          Elab.resolveFunctionIn name argsState.functionScopes with
      | none =>
          simp [Elab.resolveFunction, StateT.run_bind,
            StateT.run_get, hResolve] at hElab
          unfold Elab.throw at hElab
          change
            (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
              .ok (front, finalElabState) at hElab
          cases hElab
      | some generated =>
          simp [Elab.resolveFunction, hResolve] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases ExprNormalized.user_call_parts hNormalized with
            ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
          rcases CompiledFunctionScopes.resolve
              hArgsFunctionScopes hResolve with
            ⟨rawFn, rawLexical, generatedLexical,
              hRawResolve, ⟨hBinding⟩, hLexicalScopes⟩
          rcases CompiledFunctionBinding.block_parts hBinding with
            ⟨bodyElabState, finalBodyElabState, frontBody, orderedBody,
              hBodyScopes, hBodyElab, ⟨hBodyNormalized⟩,
              hOrderedLookup⟩
          have hBodyFunctionScopes :
              CompiledFunctionScopes builtinContext contract
                rawLexical bodyElabState.functionScopes := by
            simpa [hBodyScopes] using hLexicalScopes
          have hArgsRun :=
            argsRunForward_reverse_of_scoped_elaboration
              hExpr hFunctionScopes hArgs hArgsNormalized
              rawBase state
          have hRawLookup :
              Raw.SourceSemantics.lookupFunctionWithLexicalScopes
                  rawContext name = some (rawFn, rawLexical) := by
            simpa [Raw.SourceSemantics.lookupFunctionWithLexicalScopes]
              using hRawResolve
          let callRawFuel := rawBase + 2 * rawArgs.length
          let callOrderedFuel :=
            (rawBase + slack) + 2 * rawArgs.length
          have hRun :
              GeneratedUserCallRun callRawFuel callOrderedFuel
                rawContext name rawArgs generated orderedArgs contract state :=
            { fn := rawFn
              lexicalScopes := rawLexical
              orderedBody := orderedBody
              notClz := hNotClz
              callClass := hClass
              rawLookup := hRawLookup
              orderedLookup := hOrderedLookup
              argsForward := by
                simpa [callRawFuel, callOrderedFuel] using hArgsRun
              bodyForward := by
                intro stateAfterArgs values
                have hBody :=
                  hBlock callRawFuel
                    (rawContext :=
                      { rawContext with functionScopes := rawLexical })
                    hBodyFunctionScopes
                    (state :=
                      Yul.InteractionSemantics.stateModel.withSource
                        stateAfterArgs
                        (EvmYul.Yul.State.mkOk
                          (stateAfterArgs.initcall rawFn.params
                            rawFn.returns values.reverse)))
                    hBodyElab hBodyNormalized
                simpa [callOrderedFuel, callRawFuel, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using hBody }
          have hCall := exprValuesRunForward_userCall_succ hRun
          simpa [callRawFuel, callOrderedFuel, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hCall

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

theorem exprValuesRunForward_datacopy_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {orderedArgs : List Frontend.AstExpr}
    {op : EvmYul.Operation .Yul}
    {contract : Frontend.AstContract} {state : State}
    (hOp : Frontend.Primitive.ofName? "codecopy" = some op)
    (hArgs :
      ArgsRunForward rawFuel orderedFuel context
        rawArgs.reverse orderedArgs.reverse contract state)
    (hPrimitive :
      ∀ (stateAfterArgs : State) (values : List Frontend.Word),
        PrimitiveRunForward rawFuel orderedFuel
          stateAfterArgs op values.reverse) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "datacopy" rawArgs)
      (.Call (.inl op) orderedArgs) contract state := by
  unfold ExprValuesRunForward ArgsRunForward at *
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "datacopy" rawArgs state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "datacopy" rawArgs state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Call (.inl op) orderedArgs) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.datacopy_succ
    rawFuel context rawArgs state op hOp]
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
      exact hPrimitive result.1 result.2

theorem exprValuesRunForward_memoryguard_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawValue : Raw.Expr} {size : Frontend.Word}
    {contract : Frontend.AstContract} {state : State}
    (hValue :
      ExprRunForward rawFuel (orderedFuel + 1)
        context rawValue (.Lit size) contract state) :
    ExprValuesRunForward (rawFuel + 2) (orderedFuel + 1)
      context (.functionCall "memoryguard" [rawValue])
      (.Lit size) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context "memoryguard" [rawValue] state (by decide)]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.evalObjectBuiltin
        (rawFuel + 1) context "memoryguard" [rawValue] state)
      (Yul.InteractionSemantics.evalValues (orderedFuel + 1)
        (.Lit size) (some contract) state)
  rw [Raw.SourceSemantics.EvalObjectBuiltin.memoryguard_succ]
  have hTarget :
      Simulation.Interaction.bind
          (Yul.InteractionSemantics.eval (orderedFuel + 1)
            (.Lit size) (some contract) state)
          (fun result => pure (result.1, [result.2])) =
        Yul.InteractionSemantics.evalValues (orderedFuel + 1)
          (.Lit size) (some contract) state := by
    unfold Yul.InteractionSemantics.eval Yul.Source.Canonical.eval
      Yul.Source.Effectful.eval Yul.InteractionSemantics.evalValues
      Yul.Source.Canonical.evalValues Yul.Source.Effectful.evalValues
    rfl
  rw [← hTarget]
  unfold ExprRunForward at hValue
  refine Simulation.Interaction.ForwardRel.bind_custom hValue ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok result => exact Simulation.Interaction.ForwardRel.done rfl

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

theorem stmtRunForward_block_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hBlock :
      BlockCodeRunForward rawFuel orderedFuel
        context rawCode orderedCode contract state) :
    StmtRunForward (rawFuel + 1) orderedFuel
      context (.block rawCode) (.Block orderedCode) contract state := by
  unfold StmtRunForward BlockCodeRunForward at *
  rw [Raw.SourceSemantics.Exec.block_succ]
  exact hBlock

theorem stmtRunForward_ifThen_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {orderedCondition : Frontend.AstExpr}
    {rawBody : List Raw.Stmt} {orderedBody : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hCondition :
      ExprRunForward rawFuel orderedFuel
        context rawCondition orderedCondition contract state)
    (hBody :
      ∀ (stateAfterCondition : State) (value : Frontend.Word),
        value ≠ EvmYul.UInt256.ofNat 0 →
          BlockCodeRunForward rawFuel orderedFuel
            context rawBody orderedBody contract stateAfterCondition) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.ifThen rawCondition rawBody)
      (.If orderedCondition orderedBody) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.ifThen_succ]
  rw [Yul.InteractionSemantics.Exec.if_succ]
  unfold ExprRunForward at hCondition
  refine Simulation.Interaction.ForwardRel.bind_custom hCondition ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok conditionResult =>
      rcases conditionResult with ⟨stateAfterCondition, value⟩
      change
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
          (if value ≠ EvmYul.UInt256.ofNat 0 then
            Raw.SourceSemantics.execBlock rawFuel context rawBody
              stateAfterCondition
          else
            pure stateAfterCondition)
          (if value ≠ EvmYul.UInt256.ofNat 0 then
            Yul.InteractionSemantics.exec orderedFuel (.Block orderedBody)
              (some contract) stateAfterCondition
          else
            pure stateAfterCondition)
      split
      case isTrue hRawTruthy =>
        exact hBody stateAfterCondition value hRawTruthy
      case isFalse hRawFalse =>
        exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_switch_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr} {orderedCondition : Frontend.AstExpr}
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {rawDefault : List Raw.Stmt}
    {orderedCases : List (Frontend.Word × List Frontend.AstStmt)}
    {orderedDefault : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hCondition :
      ExprRunForward rawFuel orderedFuel
        context rawCondition orderedCondition contract state)
    (hCases :
      SwitchCasesRunForward rawFuel orderedFuel context
        rawCases rawDefault orderedCases orderedDefault contract) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context (.switch rawCondition rawCases rawDefault)
      (.Switch orderedCondition orderedCases orderedDefault)
      contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.switch_succ]
  rw [Yul.InteractionSemantics.Exec.switch_succ]
  unfold ExprRunForward at hCondition
  refine Simulation.Interaction.ForwardRel.bind_custom hCondition ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok conditionResult =>
      rcases conditionResult with ⟨stateAfterCondition, value⟩
      rcases hCases stateAfterCondition value with
        ⟨rawBody, orderedBody, hRawSelected, hOrderedSelected, hBody⟩
      simp only [hRawSelected, hOrderedSelected]
      exact hBody

theorem stmtRunForward_break_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context .break .Break contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.break_succ]
  rw [Yul.InteractionSemantics.Exec.brk_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_continue_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context .continue .Continue contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.continue_succ]
  rw [Yul.InteractionSemantics.Exec.cont_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_leave_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      context .leave .Leave contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.leave_succ]
  rw [Yul.InteractionSemantics.Exec.leave_succ]
  exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_functionDefinition_stub_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {contract : Frontend.AstContract}
    {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore} :
    StmtRunForward (rawFuel + 1) (orderedFuel + 2)
      context (.functionDefinition name params returns body)
      (.Block []) contract (.Ok shared store) := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
  rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (pure (EvmYul.Yul.State.Ok shared store))
      (pure (EvmYul.Yul.State.Ok shared
        (EvmYul.Yul.State.restrictVarStore store store)))
  rw [Yul.VarStoreRestriction.restrict_self]
  exact Simulation.Interaction.ForwardRel.done rfl

def BlockElaborationRunForward
    (slack : Nat)
    (rawContext : Raw.SourceSemantics.Context)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawFuel : Nat)
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    (Elab.Stmt.List.elaborateBlock rawCode true).run elabState =
        .ok (front, finalElabState) →
      StmtListNormalized builtinContext front ordered →
        BlockCodeRunForward rawFuel (rawFuel + slack)
          rawContext rawCode ordered contract state

theorem stmtRunForward_of_elaborated_variableDeclaration_none
    {rawFuel orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {names : List Name}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hElab :
      (Elab.Stmt.elaborate (.variableDeclaration names none)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      rawContext (.variableDeclaration names none)
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp at hElab
  cases hDeclare :
      (Elab.declareIdentifiers names "variable").run elabState with
  | error err => simp [hDeclare] at hElab
  | ok result =>
      rcases result with ⟨_, declaredState⟩
      simp [hDeclare] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := StmtNormalized.let_none_ordered hNormalized
      subst ordered
      exact stmtRunForward_variableDeclaration_none_succ

theorem stmtRunForward_of_elaborated_variableDeclaration_some
    {slack rawFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {names : List Name} {rawValue : Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    (hElab :
      (Elab.Stmt.elaborate
        (.variableDeclaration names (some rawValue))).run elabState =
          .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) ((rawFuel + slack) + 1)
      rawContext (.variableDeclaration names (some rawValue))
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp at hElab
  cases hValue : (Elab.Expr.elaborate rawValue).run elabState with
  | error err => simp [hValue] at hElab
  | ok valueResult =>
      rcases valueResult with ⟨frontValue, valueState⟩
      simp [hValue] at hElab
      cases hDeclare :
          (Elab.declareIdentifiers names "variable").run valueState with
      | error err => simp [hDeclare] at hElab
      | ok result =>
          rcases result with ⟨_, declaredState⟩
          simp [hDeclare] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases StmtNormalized.let_some_parts hNormalized with
            ⟨orderedValue, rfl, ⟨hValueNormalized⟩⟩
          exact
            stmtRunForward_variableDeclaration_some_succ
              (hExpr rawFuel (state := state)
                hValue hValueNormalized)

theorem stmtRunForward_of_elaborated_assignment
    {slack rawFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {names : List Name} {rawValue : Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    (hElab :
      (Elab.Stmt.elaborate (.assignment names rawValue)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) ((rawFuel + slack) + 1)
      rawContext (.assignment names rawValue) ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hVisible :
      (Elab.requireIdentifiersVisible names "assignment").run elabState with
  | error err => simp [hVisible] at hElab
  | ok visibleResult =>
      rcases visibleResult with ⟨_, visibleState⟩
      simp [hVisible] at hElab
      cases hValue : (Elab.Expr.elaborate rawValue).run visibleState with
      | error err => simp [hValue] at hElab
      | ok valueResult =>
          rcases valueResult with ⟨frontValue, valueState⟩
          simp [hValue] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases StmtNormalized.assign_parts hNormalized with
            ⟨orderedValue, rfl, ⟨hValueNormalized⟩⟩
          exact
            stmtRunForward_assignment_succ
              (hExpr rawFuel (state := state)
                hValue hValueNormalized)

theorem stmtRunForward_of_elaborated_break
    {rawFuel orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hElab : (Elab.Stmt.elaborate .break).run elabState =
      .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      rawContext .break ordered contract state := by
  simp [Elab.Stmt.elaborate] at hElab
  rcases hElab with ⟨rfl, rfl⟩
  have hOrdered := StmtNormalized.break_ordered hNormalized
  subst ordered
  exact stmtRunForward_break_succ

theorem stmtRunForward_of_elaborated_continue
    {rawFuel orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hElab : (Elab.Stmt.elaborate .continue).run elabState =
      .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      rawContext .continue ordered contract state := by
  simp [Elab.Stmt.elaborate] at hElab
  rcases hElab with ⟨rfl, rfl⟩
  have hOrdered := StmtNormalized.continue_ordered hNormalized
  subst ordered
  exact stmtRunForward_continue_succ

theorem stmtRunForward_of_elaborated_leave
    {rawFuel orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hElab : (Elab.Stmt.elaborate .leave).run elabState =
      .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (orderedFuel + 1)
      rawContext .leave ordered contract state := by
  simp [Elab.Stmt.elaborate] at hElab
  rcases hElab with ⟨rfl, rfl⟩
  have hOrdered := StmtNormalized.leave_ordered hNormalized
  subst ordered
  exact stmtRunForward_leave_succ

theorem stmtRunForward_of_elaborated_block
    {slack rawFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawBody : List Raw.Stmt}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hBlock :
      BlockElaborationRunForward slack rawContext builtinContext contract)
    (hElab :
      (Elab.Stmt.elaborate (.block rawBody)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) (rawFuel + slack)
      rawContext (.block rawBody) ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp at hElab
  cases hBody :
      (Elab.Stmt.List.elaborateBlock rawBody true).run elabState with
  | error err => simp [hBody] at hElab
  | ok bodyResult =>
      rcases bodyResult with ⟨frontBody, bodyState⟩
      simp [hBody] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rcases StmtNormalized.block_parts hNormalized with
        ⟨orderedBody, rfl, ⟨hBodyNormalized⟩⟩
      exact
        stmtRunForward_block_succ
          (hBlock rawFuel (state := state)
            hBody hBodyNormalized)

theorem stmtRunForward_of_elaborated_ifThen
    {slack rawFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawCondition : Raw.Expr} {rawBody : List Raw.Stmt}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ExprElaborationRunForward slack rawContext builtinContext contract)
    (hBlock :
      BlockElaborationRunForward slack rawContext builtinContext contract)
    (hElab :
      (Elab.Stmt.elaborate (.ifThen rawCondition rawBody)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    StmtRunForward (rawFuel + 1) ((rawFuel + slack) + 1)
      rawContext (.ifThen rawCondition rawBody) ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hCondition : (Elab.Expr.elaborate rawCondition).run elabState with
  | error err => simp [hCondition] at hElab
  | ok conditionResult =>
      rcases conditionResult with ⟨frontCondition, conditionState⟩
      simp [hCondition] at hElab
      cases hBody :
          (Elab.Stmt.List.elaborateBlock rawBody true).run
            conditionState with
      | error err => simp [hBody] at hElab
      | ok bodyResult =>
          rcases bodyResult with ⟨frontBody, bodyState⟩
          simp [hBody] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          rcases StmtNormalized.if_parts hNormalized with
            ⟨orderedCondition, orderedBody, rfl,
              ⟨hConditionNormalized⟩, ⟨hBodyNormalized⟩⟩
          apply stmtRunForward_ifThen_succ
          · exact
              exprRunForward_of_values
                (hExpr rawFuel (state := state)
                  hCondition hConditionNormalized)
          · intro stateAfterCondition value _hTruthy
            exact
              hBlock rawFuel
                (state := stateAfterCondition) hBody hBodyNormalized

/-- Semantic compiler interface for one statement under arbitrary residual
fuel. The full frontend proof constructs this from expression, block, switch,
loop, and generated-call preservation; list traversal is generic below. -/
def StmtElaborationRunForward
    (rawContext : Raw.SourceSemantics.Context)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ (rawFuel orderedFuel : Nat)
    {rawStmt : Raw.Stmt} {front : Frontend.Stmt}
    {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    (Elab.Stmt.elaborate rawStmt).run elabState =
        .ok (front, finalElabState) →
      StmtNormalized builtinContext front ordered →
        StmtRunForward rawFuel orderedFuel
          rawContext rawStmt ordered contract state

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

def ScopedSeqRunForward (entryStore : EvmYul.Yul.VarStore)
    (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawCode : List Raw.Stmt) (orderedCode : List Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    (BlockSeqDoneRel entryStore)
    (Raw.SourceSemantics.execSeq rawFuel context rawCode state)
    (Yul.InteractionSemantics.execSeq orderedFuel orderedCode
      (some contract) state)

theorem scopedSeqRunForward_of_exact
    {entryStore : EvmYul.Yul.VarStore}
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExact :
      SeqRunForward rawFuel orderedFuel
        context rawCode orderedCode contract state) :
    ScopedSeqRunForward entryStore rawFuel orderedFuel
      context rawCode orderedCode contract state := by
  unfold SeqRunForward ScopedSeqRunForward at *
  apply Simulation.Interaction.ForwardRel.mono hExact
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ExceptRel.error rfl
  | ok rawState =>
      exact Simulation.Interaction.ExceptRel.ok (.inl rfl)

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

theorem seqRunForward_of_elaboration
    {rawContext : Raw.SourceSemantics.Context}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hStmt :
      StmtElaborationRunForward rawContext builtinContext contract) :
    ∀ {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
      {ordered : List Frontend.AstStmt}
      {elabState finalElabState : Elab.State},
      (Elab.Stmt.List.elaborate rawCode).run elabState =
          .ok (front, finalElabState) →
        StmtListNormalized builtinContext front ordered →
          ∀ (rawBase orderedBase : Nat) (state : State),
            SeqRunForward
              (rawBase + rawCode.length + 1)
              (orderedBase + rawCode.length + 1)
              rawContext rawCode ordered contract state := by
  intro rawCode
  induction rawCode with
  | nil =>
      intro front ordered elabState finalElabState hElab hNormalized
        rawBase orderedBase state
      simp [Elab.Stmt.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := StmtListNormalized.nil_ordered hNormalized
      subst ordered
      simpa using
        (seqRunForward_nil_succ
          (rawFuel := rawBase) (orderedFuel := orderedBase)
          (context := rawContext) (contract := contract) (state := state))
  | cons rawHead rawTail ih =>
      intro front ordered elabState finalElabState hElab hNormalized
        rawBase orderedBase state
      unfold Elab.Stmt.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Stmt.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headElabState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Stmt.List.elaborate rawTail).run headElabState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailElabState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases StmtListNormalized.cons_parts hNormalized with
                ⟨orderedHead, orderedTail, rfl,
                  ⟨hHeadNormalized⟩, ⟨hTailNormalized⟩⟩
              let rawTailFuel := rawBase + rawTail.length + 1
              let orderedTailFuel := orderedBase + rawTail.length + 1
              have hHeadRun :=
                hStmt rawTailFuel orderedTailFuel
                  (state := state) hHead hHeadNormalized
              have hCons :=
                seqRunForward_cons
                  (rawFuel := rawTailFuel)
                  (orderedFuel := orderedTailFuel)
                  (context := rawContext) (rawStmt := rawHead)
                  (rawRest := rawTail) (orderedStmt := orderedHead)
                  (orderedRest := orderedTail) (contract := contract)
                  (state := state) hHeadRun
                  (fun shared vars =>
                    ih hTail hTailNormalized rawBase orderedBase
                      (.Ok shared vars))
              simpa [rawTailFuel, orderedTailFuel, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hCons

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

/-- Generic lexical-block constructor. A recursively preserved statement list
under the block's raw function scope yields exact block outcomes because both
semantics apply the same entry-store restriction. -/
theorem blockCodeRunForward_of_scope_seq
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {scope : Raw.SourceSemantics.FunctionScope}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hScope : Raw.SourceSemantics.functionScope? rawCode = some scope)
    (hSeq :
      SeqRunForward rawFuel orderedFuel
        (context.withFunctionScope scope)
        rawCode orderedCode contract state) :
    BlockCodeRunForward (rawFuel + 1) (orderedFuel + 1)
      context rawCode orderedCode contract state := by
  unfold BlockCodeRunForward SeqRunForward at *
  rw [Raw.SourceSemantics.ExecBlock.succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [hScope]
  refine Simulation.Interaction.ForwardRel.bind_custom hSeq ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok stateAfterBody =>
      exact Simulation.Interaction.ForwardRel.done rfl

theorem blockCodeRunForward_of_scope_scopedSeq
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {scope : Raw.SourceSemantics.FunctionScope}
    {rawCode : List Raw.Stmt} {orderedCode : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hScope : Raw.SourceSemantics.functionScope? rawCode = some scope)
    (hSeq :
      ScopedSeqRunForward state.store rawFuel orderedFuel
        (context.withFunctionScope scope)
        rawCode orderedCode contract state) :
    BlockCodeRunForward (rawFuel + 1) (orderedFuel + 1)
      context rawCode orderedCode contract state := by
  unfold BlockCodeRunForward ScopedSeqRunForward at *
  rw [Raw.SourceSemantics.ExecBlock.succ]
  rw [Yul.InteractionSemantics.Exec.block_succ]
  simp only [hScope]
  refine Simulation.Interaction.ForwardRel.bind_custom hSeq ?_
  intro rawDone orderedDone hDone
  cases hDone with
  | error hError =>
      subst_vars
      exact Simulation.Interaction.ForwardRel.done rfl
  | @ok rawState orderedState hState =>
      cases hState with
      | inl hExact =>
          subst orderedState
          exact Simulation.Interaction.ForwardRel.done rfl
      | inr hRestricted =>
          subst orderedState
          apply Simulation.Interaction.ForwardRel.done
          unfold SameDoneRel
          congr 1
          exact
            (Yul.InteractionSemantics.State.restrictStoreTo_idem
              rawState state.store).symm

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

theorem dispatcher_normalized
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ helper? arg? ret? memoryContract orderedDispatcher,
      Elab.elaborateCode code =
          .ok (ctx.program.object.dispatcher, ctx.program.object.functions,
            helper?, arg?, ret?) ∧
        Frontend.MemoryGuard.Object.inferredContract? ctx.program.object =
          some memoryContract ∧
        Nonempty
          (StmtListNormalized
            { ctx.context with memoryContract := memoryContract }
            ctx.program.object.dispatcher orderedDispatcher) ∧
        artifact.codeArtifact.ordered.program.contract.dispatcher =
          .Block orderedDispatcher := by
  rcases ctx.dispatcher_parts hCode with
    ⟨helper?, arg?, ret?, memoryContract, resolvedDispatcher,
      orderedDispatcher, hElab, hMemory, hResolve, _hResolved,
      hToYul, hOrdered⟩
  exact
    ⟨helper?, arg?, ret?, memoryContract, orderedDispatcher,
      hElab, hMemory,
      ⟨{
        resolved := resolvedDispatcher
        resolve := hResolve
        toYul := hToYul }⟩,
      hOrdered⟩

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
