import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Solidity.RawAstClzPreservation
import EvmCompiler.Solidity.RawAstClzAllocation
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

theorem classifyCall_objectBuiltin_mem
    {name : Name}
    (hClass : CallClass.classifyCall name = .objectBuiltin) :
    name ∈ CallClass.objectBuiltins := by
  unfold CallClass.classifyCall at hClass
  cases hPrimitive : Frontend.Primitive.ofName? name with
  | some op => simp [hPrimitive] at hClass
  | none =>
      simp [hPrimitive] at hClass
      by_cases hObject : name ∈ CallClass.objectBuiltins
      · exact hObject
      · cases hDialect : CallClass.unsupportedDialectBuiltin? name <;>
          simp [hObject, hDialect] at hClass

theorem rawObjectBuiltinNameArg_of_elaboration
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {elabState finalElabState : Elab.State} {name : Name}
    (hElab :
      (Elab.Expr.elaborate rawExpr).run elabState =
        .ok (front, finalElabState))
    (hName : Frontend.Expr.objectBuiltinNameArg? front = some name) :
    Raw.SourceSemantics.objectBuiltinNameArg? rawExpr = some name := by
  cases rawExpr with
  | literal literal =>
      cases literal with
      | number value =>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
      | bool value =>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
      | stringLit value =>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
          subst name
          rfl
      | bytesLit bytes =>
          simp [Elab.Expr.elaborate, Elab.Literal.elaborate] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
          subst name
          rfl
  | identifier ident =>
      unfold Elab.Expr.elaborate at hElab
      cases hVisible :
          (Elab.requireIdentifierVisible ident "expression").run elabState with
      | error err => simp [hVisible] at hElab
      | ok visibleResult =>
          rcases visibleResult with ⟨_, visibleState⟩
          simp [hVisible] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
  | functionCall callee args =>
      by_cases hMemoryguard : callee = "memoryguard"
      · subst callee
        cases args with
        | nil =>
            simp [Elab.Expr.elaborate] at hElab
            unfold Elab.throw at hElab
            change
              (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
                .ok (front, finalElabState) at hElab
            cases hElab
        | cons arg rest =>
            cases rest with
            | nil =>
                unfold Elab.Expr.elaborate at hElab
                cases hArg : (Elab.Expr.elaborate arg).run elabState with
                | error err => simp [hArg] at hElab
                | ok argResult =>
                    rcases argResult with ⟨frontArg, argState⟩
                    simp [hArg] at hElab
                    rcases hElab with ⟨rfl, rfl⟩
                    simp [Frontend.Expr.objectBuiltinNameArg?] at hName
            | cons extra tail =>
                simp [Elab.Expr.elaborate] at hElab
                unfold Elab.throw at hElab
                change
                  (Except.error _ :
                    Except String (Frontend.Expr × Elab.State)) =
                    .ok (front, finalElabState) at hElab
                cases hElab
      · by_cases hClz : callee = "clz"
        · subst callee
          cases args with
          | nil =>
              simp [Elab.Expr.elaborate] at hElab
              unfold Elab.throw at hElab
              change
                (Except.error _ :
                  Except String (Frontend.Expr × Elab.State)) =
                  .ok (front, finalElabState) at hElab
              cases hElab
          | cons arg rest =>
              cases rest with
              | nil =>
                  unfold Elab.Expr.elaborate at hElab
                  cases hArg : (Elab.Expr.elaborate arg).run elabState with
                  | error err => simp [hArg] at hElab
                  | ok argResult =>
                      rcases argResult with ⟨frontArg, argState⟩
                      simp [hArg] at hElab
                      cases hHelper : Elab.ensureClzHelper.run argState with
                      | error err => simp [hHelper] at hElab
                      | ok helperResult =>
                          rcases helperResult with ⟨helper, helperState⟩
                          simp [hHelper] at hElab
                          rcases hElab with ⟨rfl, rfl⟩
                          simp [Frontend.Expr.objectBuiltinNameArg?] at hName
              | cons extra tail =>
                  simp [Elab.Expr.elaborate] at hElab
                  unfold Elab.throw at hElab
                  change
                    (Except.error _ :
                      Except String (Frontend.Expr × Elab.State)) =
                      .ok (front, finalElabState) at hElab
                  cases hElab
        · unfold Elab.Expr.elaborate at hElab
          simp [StateT.run_bind] at hElab
          cases hArgs : (Elab.Expr.List.elaborate args).run elabState with
          | error err => simp [hArgs] at hElab
          | ok argsResult =>
              rcases argsResult with ⟨frontArgs, argsState⟩
              simp [hArgs] at hElab
              cases hKind : CallClass.classifyCall callee with
              | primitive =>
                  simp [hKind] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  simp [Frontend.Expr.objectBuiltinNameArg?] at hName
              | objectBuiltin =>
                  simp [hKind] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  simp [Frontend.Expr.objectBuiltinNameArg?] at hName
              | dialectBuiltin =>
                  simp [hKind] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  simp [Frontend.Expr.objectBuiltinNameArg?] at hName
              | user =>
                  simp [hKind] at hElab
                  cases hResolve :
                      Elab.resolveFunctionIn callee argsState.functionScopes with
                  | none =>
                      simp [Elab.resolveFunction, hResolve] at hElab
                      unfold Elab.throw at hElab
                      change
                        (Except.error _ :
                          Except String (Frontend.Expr × Elab.State)) =
                          .ok (front, finalElabState) at hElab
                      cases hElab
                  | some generated =>
                      simp [Elab.resolveFunction, hResolve] at hElab
                      rcases hElab with ⟨rfl, rfl⟩
                      simp [Frontend.Expr.objectBuiltinNameArg?] at hName

theorem exprList_elaborate_length
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState)) :
    fronts.length = rawExprs.length := by
  induction rawExprs generalizing elabState finalElabState fronts with
  | nil =>
      simp [Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      rfl
  | cons rawHead rawTail ih =>
      unfold Elab.Expr.List.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hHead : (Elab.Expr.elaborate rawHead).run elabState with
      | error err => simp [hHead] at hElab
      | ok headResult =>
          rcases headResult with ⟨frontHead, headState⟩
          simp [hHead] at hElab
          cases hTail :
              (Elab.Expr.List.elaborate rawTail).run headState with
          | error err => simp [hTail] at hElab
          | ok tailResult =>
              rcases tailResult with ⟨frontTail, tailState⟩
              simp [hTail] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              simp [ih hTail]

theorem exprList_elaborate_single_head
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {elabState finalElabState : Elab.State}
    (hElab :
      (Elab.Expr.List.elaborate [rawExpr]).run elabState =
        .ok ([front], finalElabState)) :
    ∃ headState,
      (Elab.Expr.elaborate rawExpr).run elabState =
        .ok (front, headState) := by
  unfold Elab.Expr.List.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hHead : (Elab.Expr.elaborate rawExpr).run elabState with
  | error err => simp [hHead] at hElab
  | ok headResult =>
      rcases headResult with ⟨frontHead, headState⟩
      simp [hHead, Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨hFront, _hFinal⟩
      subst frontHead
      refine ⟨headState, ?_⟩
      rfl

theorem rawSingleObjectBuiltinNameArg_of_list_elaboration
    {rawArgs : List Raw.Expr} {frontArgs : List Frontend.Expr}
    {elabState finalElabState : Elab.State}
    {frontNameArg : Frontend.Expr} {dataName : Name}
    (hElab :
      (Elab.Expr.List.elaborate rawArgs).run elabState =
        .ok (frontArgs, finalElabState))
    (hFrontArgs : frontArgs = [frontNameArg])
    (hFrontName :
      Frontend.Expr.objectBuiltinNameArg? frontNameArg = some dataName) :
    ∃ rawNameArg,
      rawArgs = [rawNameArg] ∧
        Raw.SourceSemantics.objectBuiltinNameArg? rawNameArg = some dataName := by
  have hLengths := exprList_elaborate_length hElab
  rw [hFrontArgs] at hLengths hElab
  have hRawLength : rawArgs.length = 1 := by simpa using hLengths.symm
  rw [List.length_eq_one_iff] at hRawLength
  rcases hRawLength with ⟨rawNameArg, rfl⟩
  rcases exprList_elaborate_single_head hElab with
    ⟨nameState, hNameElab⟩
  exact
    ⟨rawNameArg, rfl,
      rawObjectBuiltinNameArg_of_elaboration hNameElab hFrontName⟩

theorem objectBuiltinCall_elaboration_parts
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr}
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .objectBuiltin)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState)) :
    ∃ frontArgs argsState,
      (Elab.Expr.List.elaborate rawArgs).run elabState =
          .ok (frontArgs, argsState) ∧
        front = .call .objectBuiltin name frontArgs ∧
        finalElabState = argsState := by
  unfold Elab.Expr.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      simp [hArgs, hClass] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      exact ⟨frontArgs, argsState, by rfl, rfl, rfl⟩

theorem functionCall_elaboration_kind_parts
    {name : Name} {rawArgs : List Raw.Expr}
    {kind : Frontend.CallKind}
    {state finalState : Elab.State}
    {front : Frontend.Expr}
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = kind)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run state =
        .ok (front, finalState)) :
    ∃ callee frontArgs,
      front = .call kind callee frontArgs := by
  unfold Elab.Expr.elaborate at hElab
  simp [hNotMemoryguard, hNotClz, StateT.run_bind] at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run state with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      simp [hArgs, hClass] at hElab
      cases kind with
      | primitive =>
          rcases hElab with ⟨rfl, rfl⟩
          exact ⟨name, frontArgs, rfl⟩
      | objectBuiltin =>
          rcases hElab with ⟨rfl, rfl⟩
          exact ⟨name, frontArgs, rfl⟩
      | dialectBuiltin =>
          rcases hElab with ⟨rfl, rfl⟩
          exact ⟨name, frontArgs, rfl⟩
      | user =>
          cases hResolve :
              Elab.resolveFunctionIn name argsState.functionScopes with
          | none =>
              simp [Elab.resolveFunction, StateT.run_bind,
                StateT.run_get, hResolve] at hElab
              unfold Elab.throw at hElab
              change
                (Except.error _ :
                  Except String (Frontend.Expr × Elab.State)) =
                    .ok (front, finalState) at hElab
              cases hElab
          | some generated =>
              simp [Elab.resolveFunction, hResolve] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              exact ⟨generated, frontArgs, rfl⟩

theorem switchCaseValue_elaboration_word
    {rawValue : Raw.SwitchCaseValue}
    {frontValue : Frontend.SwitchCaseValue}
    {word : Frontend.Word}
    (hElab :
      Elab.SwitchCaseValue.elaborate rawValue = .ok frontValue)
    (hWord : frontValue.toWord? = some word) :
    Raw.SourceSemantics.switchCaseValueWord? rawValue = some word := by
  cases rawValue with
  | literal literal =>
      cases literal with
      | number value =>
          simp [Elab.SwitchCaseValue.elaborate] at hElab
          subst frontValue
          simpa [Raw.SourceSemantics.switchCaseValueWord?,
            Raw.SourceSemantics.literalWord?,
            Frontend.SwitchCaseValue.toWord?] using hWord
      | bool value =>
          simp [Elab.SwitchCaseValue.elaborate] at hElab
          subst frontValue
          simpa [Raw.SourceSemantics.switchCaseValueWord?,
            Raw.SourceSemantics.literalWord?,
            Frontend.SwitchCaseValue.toWord?] using hWord
      | stringLit value =>
          simp [Elab.SwitchCaseValue.elaborate] at hElab
          subst frontValue
          simpa [Raw.SourceSemantics.switchCaseValueWord?,
            Raw.SourceSemantics.literalWord?,
            Frontend.SwitchCaseValue.toWord?] using hWord
      | bytesLit bytes =>
          simp [Elab.SwitchCaseValue.elaborate] at hElab
          subst frontValue
          simpa [Raw.SourceSemantics.switchCaseValueWord?,
            Raw.SourceSemantics.literalWord?,
            Frontend.SwitchCaseValue.toWord?] using hWord

theorem memoryguard_elaboration_parts
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr}
    (hElab :
      (Elab.Expr.elaborate (.functionCall "memoryguard" rawArgs)).run
        elabState = .ok (front, finalElabState)) :
    ∃ rawValue frontValue valueState,
      rawArgs = [rawValue] ∧
        front = .call .objectBuiltin "memoryguard" [frontValue] ∧
        (Elab.Expr.elaborate rawValue).run elabState =
          .ok (frontValue, valueState) ∧
        finalElabState = valueState := by
  cases rawArgs with
  | nil =>
      simp [Elab.Expr.elaborate] at hElab
      unfold Elab.throw at hElab
      change
        (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
          .ok (front, finalElabState) at hElab
      cases hElab
  | cons rawValue rest =>
      cases rest with
      | nil =>
          unfold Elab.Expr.elaborate at hElab
          cases hValue : (Elab.Expr.elaborate rawValue).run elabState with
          | error err => simp [hValue] at hElab
          | ok valueResult =>
              rcases valueResult with ⟨frontValue, valueState⟩
              simp [hValue] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              exact ⟨rawValue, frontValue, valueState, rfl, rfl, hValue, rfl⟩
      | cons extra tail =>
          simp [Elab.Expr.elaborate] at hElab
          unfold Elab.throw at hElab
          change
            (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
              .ok (front, finalElabState) at hElab
          cases hElab

theorem clz_elaboration_parts
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr}
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run
        elabState = .ok (front, finalElabState)) :
    ∃ rawArg frontArg argState helper helperState,
      rawArgs = [rawArg] ∧
        (Elab.Expr.elaborate rawArg).run elabState =
          .ok (frontArg, argState) ∧
        Elab.ensureClzHelper.run argState = .ok (helper, helperState) ∧
        front = .call .user helper [frontArg] ∧
        finalElabState = helperState := by
  cases rawArgs with
  | nil =>
      simp [Elab.Expr.elaborate] at hElab
      unfold Elab.throw at hElab
      change
        (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
          .ok (front, finalElabState) at hElab
      cases hElab
  | cons rawArg rest =>
      cases rest with
      | nil =>
          unfold Elab.Expr.elaborate at hElab
          cases hArg : (Elab.Expr.elaborate rawArg).run elabState with
          | error err => simp [hArg] at hElab
          | ok argResult =>
              rcases argResult with ⟨frontArg, argState⟩
              simp [hArg] at hElab
              cases hHelper : Elab.ensureClzHelper.run argState with
              | error err => simp [hHelper] at hElab
              | ok helperResult =>
                  rcases helperResult with ⟨helper, helperState⟩
                  simp [hHelper] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  exact
                    ⟨rawArg, frontArg, argState, helper, helperState,
                      rfl, hArg, hHelper, rfl, rfl⟩
      | cons extra tail =>
          simp [Elab.Expr.elaborate] at hElab
          unfold Elab.throw at hElab
          change
            (Except.error _ : Except String (Frontend.Expr × Elab.State)) =
              .ok (front, finalElabState) at hElab
          cases hElab

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
      match raw with
      | .Ok _ _ => ordered = raw
      | .OutOfFuel | .Checkpoint _ =>
          ordered = raw ∨ ordered = raw.restrictStoreTo entryStore)

/-- A recursive sequence may reuse its enclosing block entry store after a
regular prefix. On an abrupt initial state, that store must be the state's own
entry store so an administrative empty block is related correctly. -/
def BlockEntryCompatible (entryStore : EvmYul.Yul.VarStore) : State → Prop
  | .Ok _ _ => True
  | state => state.store = entryStore

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

theorem primitiveOpenEval_succ_succ_eq
    (left right : Nat) (state : State)
    (op : EvmYul.Operation .Yul) (args : List Frontend.Word) :
    Yul.InteractionSemantics.Primitive.openEval (left + 2) state op args =
      Yul.InteractionSemantics.Primitive.openEval (right + 2) state op args := by
  cases op <;> rename_i inner <;> cases inner <;>
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?,
      EvmYul.Yul.primCall]

theorem primitiveOpenEval_one_eq_or_truncated
    (right : Nat) (state : State)
    (op : EvmYul.Operation .Yul) (args : List Frontend.Word) :
    Yul.InteractionSemantics.Primitive.openEval 1 state op args =
        Yul.InteractionSemantics.Primitive.openEval (right + 2) state op args ∨
      ∃ failure,
        Yul.InteractionSemantics.Primitive.openEval 1 state op args =
            .done (.error failure) ∧
          Yul.FunctionsInteractionPrimitive.Truncated failure := by
  cases op <;> rename_i inner <;> cases inner <;>
    simp [Yul.InteractionSemantics.Primitive.openEval,
      Yul.InteractionSemantics.Primitive.closedEval,
      Yul.InteractionSemantics.Primitive.fail,
      Yul.FunctionsInteractionPrimitive.Truncated,
      Simulation.ExternalKind.ofYulOperation?,
      Simulation.CallKind.ofYulOperation?,
      Simulation.CreateKind.ofYulOperation?,
      EvmYul.Yul.primCall]

/-- Widening only the target primitive fuel preserves every source run. At
fuel zero, and at the one-fuel `EXTCODEHASH` edge, source exhaustion is the
declared truncation relation; all other positive runs are definitionally
fuel-insensitive after the primitive dispatcher is classified. -/
theorem primitiveRunForward_slack
    (rawFuel slack : Nat) (state : State)
    (op : EvmYul.Operation .Yul) (args : List Frontend.Word) :
    PrimitiveRunForward rawFuel (rawFuel + slack) state op args := by
  unfold PrimitiveRunForward
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Yul.InteractionSemantics.Primitive.openEval rawFuel state op args)
      (Yul.InteractionSemantics.Primitive.openEval
        (rawFuel + slack) state op args)
  cases rawFuel with
  | zero =>
      simp only [Yul.InteractionSemantics.Primitive.openEval]
      exact
        Simulation.Interaction.ForwardRel.truncated
          (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
  | succ predecessor =>
      cases predecessor with
      | zero =>
          cases slack with
          | zero =>
              simpa using
                (forward_refl Yul.FunctionsInteractionPrimitive.Truncated
                  (Yul.InteractionSemantics.Primitive.openEval
                    1 state op args))
          | succ extra =>
              rcases primitiveOpenEval_one_eq_or_truncated
                  extra state op args with hEq | hTruncated
              · rw [show 1 + (extra + 1) = extra + 2 by omega]
                rw [hEq]
                exact
                  forward_refl Yul.FunctionsInteractionPrimitive.Truncated _
              · rcases hTruncated with ⟨failure, hRun, hFailure⟩
                rw [show 1 + (extra + 1) = extra + 2 by omega]
                rw [hRun]
                exact
                  Simulation.Interaction.ForwardRel.truncated hFailure
      | succ residual =>
          have hEq :=
            primitiveOpenEval_succ_succ_eq
              residual (residual + slack) state op args
          rw [show residual + 1 + 1 = residual + 2 by omega]
          rw [show residual + 1 + 1 + slack =
            (residual + slack) + 2 by omega]
          rw [hEq]
          exact
            forward_refl Yul.FunctionsInteractionPrimitive.Truncated _

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

/-- Pointwise semantic correspondence for switch cases. Literal conversion and
body preservation are stored once per case; selection is proved generically
from this relation rather than replayed by each switch statement. -/
inductive SwitchCaseListRunForward (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (contract : Frontend.AstContract) :
    List (Raw.SwitchCaseValue × List Raw.Stmt) →
      List (Frontend.Word × List Frontend.AstStmt) → Prop where
  | nil : SwitchCaseListRunForward rawFuel orderedFuel context contract [] []
  | cons
      {rawValue : Raw.SwitchCaseValue} {rawBody : List Raw.Stmt}
      {rawRest : List (Raw.SwitchCaseValue × List Raw.Stmt)}
      {word : Frontend.Word} {orderedBody : List Frontend.AstStmt}
      {orderedRest : List (Frontend.Word × List Frontend.AstStmt)}
      (value :
        Raw.SourceSemantics.switchCaseValueWord? rawValue = some word)
      (body :
        ∀ state,
          BlockCodeRunForward rawFuel orderedFuel
            context rawBody orderedBody contract state)
      (rest :
        SwitchCaseListRunForward rawFuel orderedFuel context contract
          rawRest orderedRest) :
      SwitchCaseListRunForward rawFuel orderedFuel context contract
        ((rawValue, rawBody) :: rawRest)
        ((word, orderedBody) :: orderedRest)

theorem word_beq_eq_true_iff_eq (left right : Frontend.Word) :
    (left == right) = true ↔ left = right := by
  cases left with
  | mk leftValue =>
      cases right with
      | mk rightValue =>
          constructor
          · intro hEq
            have hValue : leftValue = rightValue := eq_of_beq hEq
            cases hValue
            rfl
          · intro hEq
            cases hEq
            change (leftValue == leftValue) = true
            exact BEq.rfl

theorem SwitchCaseListRunForward.select
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {orderedCases : List (Frontend.Word × List Frontend.AstStmt)}
    {rawDefault : List Raw.Stmt}
    {orderedDefault : List Frontend.AstStmt}
    {contract : Frontend.AstContract}
    (hCases :
      SwitchCaseListRunForward rawFuel orderedFuel context contract
        rawCases orderedCases)
    (hDefault :
      ∀ state,
        BlockCodeRunForward rawFuel orderedFuel
          context rawDefault orderedDefault contract state) :
    SwitchCasesRunForward rawFuel orderedFuel context
      rawCases rawDefault orderedCases orderedDefault contract := by
  intro stateAfterCondition selectedValue
  induction hCases with
  | nil =>
      exact
        ⟨rawDefault, orderedDefault,
          by simp [Raw.SourceSemantics.selectSwitchCase],
          by simp [EvmYul.Yul.selectSwitchCase],
          hDefault stateAfterCondition⟩
  | @cons rawValue rawBody rawRest word orderedBody orderedRest
      hValue hBody hRest ih =>
      by_cases hSelected : selectedValue = word
      · have hBeq : (selectedValue == word) = true :=
          (word_beq_eq_true_iff_eq selectedValue word).mpr hSelected
        exact
          ⟨rawBody, orderedBody,
            by simp only [Raw.SourceSemantics.selectSwitchCase, hValue,
              hBeq, ↓reduceIte],
            by simp [EvmYul.Yul.selectSwitchCase, hSelected],
            hBody stateAfterCondition⟩
      · have hBeq : (selectedValue == word) = false :=
          Bool.eq_false_iff.mpr (fun h =>
            hSelected
              ((word_beq_eq_true_iff_eq selectedValue word).mp h))
        have hWordNe : word ≠ selectedValue := Ne.symm hSelected
        rcases ih with
          ⟨rawSelected, orderedSelected, hRaw, hOrdered, hRun⟩
        exact
          ⟨rawSelected, orderedSelected,
            by simpa [Raw.SourceSemantics.selectSwitchCase, hValue,
              hBeq] using hRaw,
            by simpa [EvmYul.Yul.selectSwitchCase, hWordNe] using hOrdered,
            hRun⟩

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

/-- Checked object-builtin resolution and canonical conversion for a switch
case list. Keeping this relation separate lets switch selection consume the
same recursively preserved block interface as ordinary lexical blocks. -/
structure CaseListNormalized (context : Frontend.ObjectBuiltinContext)
    (front : List (Frontend.SwitchCaseValue × List Frontend.Stmt))
    (ordered : List (Frontend.Word × List Frontend.AstStmt)) where
  resolved : List (Frontend.SwitchCaseValue × List Frontend.Stmt)
  resolve :
    Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? front context =
      some resolved
  toYul : Frontend.Stmt.CaseList.toYul? resolved = some ordered

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

namespace CaseListNormalized

theorem nil_ordered
    {context : Frontend.ObjectBuiltinContext}
    {ordered : List (Frontend.Word × List Frontend.AstStmt)}
    (hNormalized : CaseListNormalized context [] ordered) :
    ordered = [] := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  simp [Frontend.Stmt.CaseList.resolveObjectBuiltinsIn?] at hResolve
  subst resolved
  simpa [Frontend.Stmt.CaseList.toYul?] using hToYul.symm

theorem cons_parts
    {context : Frontend.ObjectBuiltinContext}
    {frontValue : Frontend.SwitchCaseValue}
    {frontBody : List Frontend.Stmt}
    {frontRest : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {ordered : List (Frontend.Word × List Frontend.AstStmt)}
    (hNormalized :
      CaseListNormalized context
        ((frontValue, frontBody) :: frontRest) ordered) :
    ∃ orderedValue orderedBody orderedRest,
      ordered = (orderedValue, orderedBody) :: orderedRest ∧
        frontValue.toWord? = some orderedValue ∧
        Nonempty (StmtListNormalized context frontBody orderedBody) ∧
        Nonempty (CaseListNormalized context frontRest orderedRest) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? at hResolve
  cases hBodyResolve :
      Frontend.Stmt.List.resolveObjectBuiltinsIn? frontBody context with
  | none => simp [hBodyResolve] at hResolve
  | some resolvedBody =>
      cases hRestResolve :
          Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? frontRest context with
      | none => simp [hBodyResolve, hRestResolve] at hResolve
      | some resolvedRest =>
          simp [hBodyResolve, hRestResolve] at hResolve
          subst resolved
          unfold Frontend.Stmt.CaseList.toYul? at hToYul
          cases hValue : frontValue.toWord? with
          | none => simp [hValue] at hToYul
          | some orderedValue =>
              cases hBodyToYul : Frontend.Stmt.List.toYul? resolvedBody with
              | none => simp [hValue, hBodyToYul] at hToYul
              | some orderedBody =>
                  cases hRestToYul :
                      Frontend.Stmt.CaseList.toYul? resolvedRest with
                  | none =>
                      simp [hValue, hBodyToYul, hRestToYul] at hToYul
                  | some orderedRest =>
                      simp [hValue, hBodyToYul, hRestToYul] at hToYul
                      exact
                        ⟨orderedValue, orderedBody, orderedRest,
                          hToYul.symm, by simpa using hValue,
                          ⟨{
                            resolved := resolvedBody
                            resolve := hBodyResolve
                            toYul := hBodyToYul }⟩,
                          ⟨{
                            resolved := resolvedRest
                            resolve := hRestResolve
                            toYul := hRestToYul }⟩⟩

end CaseListNormalized

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

theorem dialect_call_false
    {context : Frontend.ObjectBuiltinContext}
    {callee : Name} {args : List Frontend.Expr}
    {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context (.call .dialectBuiltin callee args) ordered) :
    False := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgsResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none => simp [hArgsResolve] at hResolve
  | some resolvedArgs =>
      simp [hArgsResolve] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul

theorem setimmutable_call_false
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "setimmutable" args) ordered) :
    False := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases hArgsResolve :
      Frontend.Expr.List.resolveObjectBuiltinsIn? args context with
  | none => simp [hArgsResolve] at hResolve
  | some resolvedArgs =>
      simp [hArgsResolve] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul

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

/-- Generic expression-statement normalization outside the dedicated
`setimmutable` expansion. The caller proves that the frontend resolver takes
its ordinary expression route; successful normalization then supplies the
exact canonical call expression. -/
theorem exprStmt_parts_of_generic_resolve
    {context : Frontend.ObjectBuiltinContext}
    {expr : Frontend.Expr} {ordered : Frontend.AstStmt}
    (hGeneric :
      Frontend.Stmt.resolveObjectBuiltinsIn? (.exprStmt expr) context =
        (do
          let resolvedExpr ← expr.resolveObjectBuiltinsIn? context
          some (.exprStmt resolvedExpr)))
    (hNormalized : StmtNormalized context (.exprStmt expr) ordered) :
    ∃ orderedExpr,
      ordered = .ExprStmtCall orderedExpr ∧
        Nonempty (ExprNormalized context expr orderedExpr) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  rw [hGeneric] at hResolve
  cases hExprResolve : expr.resolveObjectBuiltinsIn? context with
  | none => simp [hExprResolve] at hResolve
  | some resolvedExpr =>
      simp [hExprResolve] at hResolve
      subst resolved
      unfold Frontend.Stmt.toYul? at hToYul
      cases hExprToYul : resolvedExpr.toYul? with
      | none => simp [hExprToYul] at hToYul
      | some orderedExpr =>
          simp [hExprToYul] at hToYul
          exact
            ⟨orderedExpr, hToYul.symm,
              ⟨{
                resolved := resolvedExpr
                resolve := hExprResolve
                toYul := hExprToYul }⟩⟩

theorem exprStmt_call_parts_of_not_setimmutable
    {context : Frontend.ObjectBuiltinContext}
    {kind : Frontend.CallKind} {callee : Name}
    {args : List Frontend.Expr} {ordered : Frontend.AstStmt}
    (hNotSetimmutable :
      kind ≠ .objectBuiltin ∨ callee ≠ "setimmutable")
    (hNormalized :
      StmtNormalized context (.exprStmt (.call kind callee args)) ordered) :
    ∃ orderedExpr,
      ordered = .ExprStmtCall orderedExpr ∧
        Nonempty
          (ExprNormalized context (.call kind callee args) orderedExpr) := by
  apply exprStmt_parts_of_generic_resolve _ hNormalized
  cases kind with
  | primitive => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
  | user => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
  | dialectBuiltin => simp [Frontend.Stmt.resolveObjectBuiltinsIn?]
  | objectBuiltin =>
      have hCallee : callee ≠ "setimmutable" := by
        rcases hNotSetimmutable with hKind | hCallee
        · exact False.elim (hKind rfl)
        · exact hCallee
      simp [Frontend.Stmt.resolveObjectBuiltinsIn?, hCallee]

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

theorem switch_parts
    {context : Frontend.ObjectBuiltinContext}
    {condition : Frontend.Expr}
    {cases : List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
    {default : List Frontend.Stmt} {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context (.switch condition cases default) ordered) :
    ∃ orderedCondition orderedCases orderedDefault,
      ordered = .Switch orderedCondition orderedCases orderedDefault ∧
        Nonempty (ExprNormalized context condition orderedCondition) ∧
        Nonempty (CaseListNormalized context cases orderedCases) ∧
        Nonempty (StmtListNormalized context default orderedDefault) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hConditionResolve : condition.resolveObjectBuiltinsIn? context with
  | none => simp [hConditionResolve] at hResolve
  | some resolvedCondition =>
      cases hCasesResolve :
          Frontend.Stmt.CaseList.resolveObjectBuiltinsIn? cases context with
      | none => simp [hConditionResolve, hCasesResolve] at hResolve
      | some resolvedCases =>
          cases hDefaultResolve :
              Frontend.Stmt.List.resolveObjectBuiltinsIn? default context with
          | none =>
              simp [hConditionResolve, hCasesResolve, hDefaultResolve]
                at hResolve
          | some resolvedDefault =>
              simp [hConditionResolve, hCasesResolve, hDefaultResolve]
                at hResolve
              subst resolved
              unfold Frontend.Stmt.toYul? at hToYul
              cases hConditionToYul : resolvedCondition.toYul? with
              | none => simp [hConditionToYul] at hToYul
              | some orderedCondition =>
                  cases hCasesToYul :
                      Frontend.Stmt.CaseList.toYul? resolvedCases with
                  | none => simp [hConditionToYul, hCasesToYul] at hToYul
                  | some orderedCases =>
                      cases hDefaultToYul :
                          Frontend.Stmt.List.toYul? resolvedDefault with
                      | none =>
                          simp [hConditionToYul, hCasesToYul,
                            hDefaultToYul] at hToYul
                      | some orderedDefault =>
                          simp [hConditionToYul, hCasesToYul,
                            hDefaultToYul] at hToYul
                          exact
                            ⟨orderedCondition, orderedCases, orderedDefault,
                              hToYul.symm,
                              ⟨{
                                resolved := resolvedCondition
                                resolve := hConditionResolve
                                toYul := hConditionToYul }⟩,
                              ⟨{
                                resolved := resolvedCases
                                resolve := hCasesResolve
                                toYul := hCasesToYul }⟩,
                              ⟨{
                                resolved := resolvedDefault
                                resolve := hDefaultResolve
                                toYul := hDefaultToYul }⟩⟩

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

theorem functionDef_ordered
    {context : Frontend.ObjectBuiltinContext}
    {name : Name} {params returns : List Name}
    {body : List Frontend.Stmt} {ordered : Frontend.AstStmt}
    (hNormalized :
      StmtNormalized context
        (.functionDef name params returns body) ordered) :
    ordered = .Block [] := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Stmt.resolveObjectBuiltinsIn? at hResolve
  cases hBodyResolve :
      Frontend.Stmt.List.resolveObjectBuiltinsIn? body context with
  | none => simp [hBodyResolve] at hResolve
  | some resolvedBody =>
      simp [hBodyResolve] at hResolve
      subst resolved
      simpa [Frontend.Stmt.toYul?] using hToYul.symm

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

/-- Raw object-builtin execution and frontend normalization share every
metadata field. The frontend may replace only `memoryContract`, which raw
source execution never inspects. -/
def ObjectBuiltinContextsAgree
    (source target : Frontend.ObjectBuiltinContext) : Prop :=
  { source with memoryContract := target.memoryContract } = target

namespace ObjectBuiltinContextsAgree

theorem withMemoryContract
    (source : Frontend.ObjectBuiltinContext)
    (memoryContract : MemoryContract.Contract) :
    ObjectBuiltinContextsAgree source
      { source with memoryContract := memoryContract } := by
  rfl

theorem size?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.size? name = target.size? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

theorem offset?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.offset? name = target.offset? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

theorem findLinkerSymbol?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.findLinkerSymbol? name = target.findLinkerSymbol? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

theorem findImmutableValue?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.findImmutableValue? name = target.findImmutableValue? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

theorem findImmutableReferences?_eq
    {source target : Frontend.ObjectBuiltinContext}
    (hAgree : ObjectBuiltinContextsAgree source target)
    (name : Name) :
    source.findImmutableReferences? name =
      target.findImmutableReferences? name := by
  unfold ObjectBuiltinContextsAgree at hAgree
  rw [← hAgree]

end ObjectBuiltinContextsAgree

/-- All frontend context needed to simulate one raw expression or block. The
object metadata is shared exactly, while lexical function names are related to
their generated frontend names by checked elaboration evidence. -/
structure CompiledContext
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (rawContext : Raw.SourceSemantics.Context)
    (generatedScopes : List (List (Name × Name))) : Prop where
  objectBuiltins :
    ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext
  functionScopes :
    CompiledFunctionScopes builtinContext contract
      rawContext.functionScopes generatedScopes

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
structure GeneratedUserCallRun
    (rawFuel orderedArgsFuel orderedBodyFuel : Nat)
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
    ArgsRunForward (rawFuel + 1) (orderedArgsFuel + 1)
      context rawArgs.reverse orderedArgs.reverse contract state
  bodyForward :
    ∀ (stateAfterArgs : State) (values : List Frontend.Word),
      BlockCodeRunForward rawFuel orderedBodyFuel
        { context with functionScopes := lexicalScopes }
        fn.body orderedBody contract
        (Yul.InteractionSemantics.stateModel.withSource stateAfterArgs
          (EvmYul.Yul.State.mkOk
            (stateAfterArgs.initcall fn.params fn.returns values.reverse)))

/-- Compiler-owned ordered binding for the one generated `clz` helper. -/
structure CompiledClzBinding
    (contract : Frontend.AstContract) (generated : Name) where
  argName : Name
  returnName : Name
  yulBody : List Frontend.AstStmt
  namesDistinct : argName ≠ returnName
  orderedLookup :
    contract.functions.lookup generated =
      some (.Def [argName] [returnName] yulBody)
  bodyToYul :
    Frontend.Stmt.List.toYul?
        (Elab.clzHelperBody argName returnName) = some yulBody

/-- State-scoped resolver from exact generated names retained by one successful
elaboration path to the checked ordered helper binding in the active contract.
The enclosing code proof constructs this from its final elaborator state; it
does not quantify over unrelated states or arbitrary helper allocations. -/
def ClzBindingResolverAt (contract : Frontend.AstContract)
    (elabState : Elab.State) : Prop :=
  ∀ {generated arg ret : Name},
    Elab.ClzAllocatedAs elabState generated arg ret →
      Nonempty (CompiledClzBinding contract generated)

namespace ClzBindingResolverAt

/-- Pull a final-state resolver backward along one checked monotone elaborator
transition. This is the recursive continuation rule used by expression,
statement, and block preservation. -/
theorem of_extends
    {contract : Frontend.AstContract}
    {before after : Elab.State}
    (hExtends : Elab.ClzAllocationExtends before after)
    (hAfter : ClzBindingResolverAt contract after) :
    ClzBindingResolverAt contract before := by
  intro generated arg ret hAllocated
  exact hAfter (hExtends.allocated hAllocated)

end ClzBindingResolverAt

/-- Bundled generated-helper evidence for one actual elaborator action. Entry
allocation is reachable, and every exact allocation retained at the action's
final state resolves to the checked canonical helper in the active contract. -/
structure ClzCompilationPath
    (contract : Frontend.AstContract)
    (entry final : Elab.State) : Prop where
  entryValid : Elab.ClzAllocationValid entry
  finalResolver : ClzBindingResolverAt contract final

namespace ClzCompilationPath

/-- Restrict a path to its prefix. The suffix's monotone allocation transition
pulls final helper resolution back to the prefix endpoint. -/
theorem prefixPath
    {contract : Frontend.AstContract}
    {entry mid final : Elab.State}
    (path : ClzCompilationPath contract entry final)
    (hSuffix : Elab.ClzAllocationExtends mid final) :
    ClzCompilationPath contract entry mid where
  entryValid := path.entryValid
  finalResolver :=
    ClzBindingResolverAt.of_extends hSuffix path.finalResolver

/-- Restrict a path to its suffix. The prefix transition supplies reachable
allocation validity at the suffix entry. -/
theorem suffixPath
    {contract : Frontend.AstContract}
    {entry mid final : Elab.State}
    (path : ClzCompilationPath contract entry final)
    (hPrefix : Elab.ClzAllocationExtends entry mid) :
    ClzCompilationPath contract mid final where
  entryValid := hPrefix.after_valid
  finalResolver := path.finalResolver

end ClzCompilationPath

/-- Checked raw-function binding augmented with the exact generated-helper path
through that function's elaboration. No semantic call premise is stored. -/
structure PathCompiledFunctionBinding
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
  clzPath :
    ClzCompilationPath contract functionState finalFunctionState

namespace PathCompiledFunctionBinding

def toCompiled
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generated : Name}
    {rawFn : Raw.SourceSemantics.FunctionDef}
    {generatedScopes : List (List (Name × Name))}
    (binding :
      PathCompiledFunctionBinding builtinContext contract
        generated rawFn generatedScopes) :
    CompiledFunctionBinding builtinContext contract
      generated rawFn generatedScopes where
  frontFn := binding.frontFn
  functionState := binding.functionState
  finalFunctionState := binding.finalFunctionState
  orderedBody := binding.orderedBody
  functionScopes := binding.functionScopes
  elaborates := binding.elaborates
  bodyNormalized := binding.bodyNormalized
  orderedLookup := binding.orderedLookup

theorem block_parts
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generated : Name}
    {rawFn : Raw.SourceSemantics.FunctionDef}
    {generatedScopes : List (List (Name × Name))}
    (binding :
      PathCompiledFunctionBinding builtinContext contract
        generated rawFn generatedScopes) :
    ∃ bodyState finalBodyState frontBody orderedBody,
      bodyState.functionScopes = generatedScopes ∧
        (Elab.Stmt.List.elaborateBlock rawFn.body true).run bodyState =
          .ok (frontBody, finalBodyState) ∧
        Nonempty (StmtListNormalized builtinContext frontBody orderedBody) ∧
        contract.functions.lookup generated =
          some (.Def rawFn.params rawFn.returns orderedBody) ∧
        Nonempty
          (ClzCompilationPath contract bodyState finalBodyState) := by
  have hFunction := binding.elaborates
  unfold Elab.FunctionDef.elaborate at hFunction
  simp [StateT.run_bind] at hFunction
  cases hPush : Elab.pushIdentifierScope.run binding.functionState with
  | error err => simp [hPush] at hFunction
  | ok pushResult =>
      rcases pushResult with ⟨_, pushedState⟩
      have hPushExt :=
        Elab.pushIdentifierScope_preserves_clzAllocation
          hPush binding.clzPath.entryValid
      have hPushScopes :
          pushedState.functionScopes =
            binding.functionState.functionScopes :=
        Elab.pushIdentifierScope_preserves_functionScopes hPush
      simp [hPush] at hFunction
      cases hDeclare :
          (Elab.declareIdentifiers (rawFn.params ++ rawFn.returns)
            "function parameter/result").run pushedState with
      | error err => simp [hDeclare] at hFunction
      | ok declareResult =>
          rcases declareResult with ⟨_, declaredState⟩
          have hDeclareExt :=
            Elab.declareIdentifiers_preserves_clzAllocation
              (rawFn.params ++ rawFn.returns)
              "function parameter/result" hDeclare hPushExt.after_valid
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
              have hBodyExt :=
                Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                  rawFn.body true hBody hDeclareExt.after_valid
              simp [hBody] at hFunction
              cases hPop : Elab.popIdentifierScope.run bodyState with
              | error err => simp [hPop] at hFunction
              | ok popResult =>
                  rcases popResult with ⟨_, poppedState⟩
                  have hPopExt :=
                    Elab.popIdentifierScope_preserves_clzAllocation
                      hPop hBodyExt.after_valid
                  simp [hPop] at hFunction
                  rcases hFunction with ⟨hFrontFn, hFinalState⟩
                  have hFinalResolver :
                      ClzBindingResolverAt contract poppedState := by
                    rw [hFinalState]
                    exact binding.clzPath.finalResolver
                  have hBodyPath :
                      ClzCompilationPath contract declaredState bodyState :=
                    { entryValid := hDeclareExt.after_valid
                      finalResolver :=
                        ClzBindingResolverAt.of_extends
                          hPopExt hFinalResolver }
                  have hFrontBody : binding.frontFn.body = frontBody := by
                    rw [← hFrontFn]
                  have hNormalized := binding.bodyNormalized
                  rw [hFrontBody] at hNormalized
                  refine
                    ⟨declaredState, bodyState, frontBody,
                      binding.orderedBody, ?_, hBody, ⟨hNormalized⟩,
                      binding.orderedLookup, ⟨hBodyPath⟩⟩
                  rw [hDeclareScopes, hPushScopes, binding.functionScopes]

end PathCompiledFunctionBinding

structure PathCompiledFunctionScope
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
              (PathCompiledFunctionBinding builtinContext contract
                generated rawFn generatedScopes)
  rawLookupNone :
    ∀ {rawName},
      Elab.lookupFunctionInScope rawName generatedScope = none →
        Raw.SourceSemantics.lookupFunctionInScope rawName rawScope = none

inductive PathCompiledFunctionScopes
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) :
    List Raw.SourceSemantics.FunctionScope →
      List (List (Name × Name)) → Prop where
  | nil : PathCompiledFunctionScopes builtinContext contract [] []
  | cons
      {rawScope : Raw.SourceSemantics.FunctionScope}
      {rawRest : List Raw.SourceSemantics.FunctionScope}
      {generatedScope : List (Name × Name)}
      {generatedRest : List (List (Name × Name))}
      (head :
        PathCompiledFunctionScope builtinContext contract rawScope
          generatedScope (generatedScope :: generatedRest))
      (tail :
        PathCompiledFunctionScopes builtinContext contract
          rawRest generatedRest) :
      PathCompiledFunctionScopes builtinContext contract
        (rawScope :: rawRest) (generatedScope :: generatedRest)

namespace PathCompiledFunctionScopes

theorem resolve
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawScopes : List Raw.SourceSemantics.FunctionScope}
    {generatedScopes : List (List (Name × Name))}
    (hScopes :
      PathCompiledFunctionScopes builtinContext contract
        rawScopes generatedScopes)
    {rawName generated : Name}
    (hResolve :
      Elab.resolveFunctionIn rawName generatedScopes = some generated) :
    ∃ rawFn rawLexical generatedLexical,
      Raw.SourceSemantics.lookupFunctionWithLexicalScopesIn
          rawName rawScopes = some (rawFn, rawLexical) ∧
        Nonempty
          (PathCompiledFunctionBinding builtinContext contract
            generated rawFn generatedLexical) ∧
        PathCompiledFunctionScopes builtinContext contract
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

theorem toCompiled
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawScopes : List Raw.SourceSemantics.FunctionScope}
    {generatedScopes : List (List (Name × Name))}
    (hScopes :
      PathCompiledFunctionScopes builtinContext contract
        rawScopes generatedScopes) :
    CompiledFunctionScopes builtinContext contract
      rawScopes generatedScopes := by
  induction hScopes with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons
        { binding := by
            intro rawName generated hLookup
            rcases head.binding hLookup with
              ⟨rawFn, hRaw, ⟨binding⟩⟩
            exact ⟨rawFn, hRaw, ⟨binding.toCompiled⟩⟩
          rawLookupNone := head.rawLookupNone }
        ih

end PathCompiledFunctionScopes

/-- Object metadata plus lexical function bindings, each carrying its actual
function-elaboration helper path. This is the context used only by the new
path-scoped semantic recursion. -/
structure PathCompiledContext
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (rawContext : Raw.SourceSemantics.Context)
    (generatedScopes : List (List (Name × Name))) : Prop where
  objectBuiltins :
    ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext
  functionScopes :
    PathCompiledFunctionScopes builtinContext contract
      rawContext.functionScopes generatedScopes

namespace PathCompiledContext

def toCompiled
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    (context :
      PathCompiledContext builtinContext contract rawContext generatedScopes) :
    CompiledContext builtinContext contract rawContext generatedScopes where
  objectBuiltins := context.objectBuiltins
  functionScopes := context.functionScopes.toCompiled

end PathCompiledContext

/-- Temporary recursive callback used by the generic expression classifier.
It remains private scaffolding until statement continuation preservation
constructs `ClzBindingResolverAt` for each reachable final state. -/
def ClzBindingResolver (contract : Frontend.AstContract) : Prop :=
  ∀ {argState : Elab.State} {generated : Name}
    {helperState : Elab.State},
    Elab.ensureClzHelper.run argState = .ok (generated, helperState) →
      Nonempty (CompiledClzBinding contract generated)

/-- Bundled semantic evidence for one generated `clz` call. The argument is
preserved recursively; helper lookup, conversion, execution fuel, and the
result equation are owned by the frontend-generated binding. -/
structure GeneratedClzCallRun
    (rawArgFuel orderedArgFuel orderedCallFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawArg : Raw.Expr) (generated : Name)
    (orderedArg : Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) where
  binding : CompiledClzBinding contract generated
  bodyFuel :
    Raw.ClzPreservation.stmtListFuel
        (Elab.clzHelperBody binding.argName binding.returnName) + 2 ≤
      orderedCallFuel
  argForward :
    ExprRunForward rawArgFuel orderedArgFuel
      context rawArg orderedArg contract state

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

/-- With one unit of source fuel, a nonempty argument list reaches expression
fuel zero and truncates before any source effect. -/
theorem argsRunForward_cons_one
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawHead : Raw.Expr} {rawTail : List Raw.Expr}
    {orderedHead : Frontend.AstExpr}
    {orderedTail : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State} :
    ArgsRunForward 1 (orderedFuel + 1)
      context (rawHead :: rawTail) (orderedHead :: orderedTail)
      contract state := by
  unfold ArgsRunForward
  rw [show
    Raw.SourceSemantics.evalArgs 1 context (rawHead :: rawTail) state =
      Raw.SourceSemantics.fail state .OutOfFuel by
        unfold Raw.SourceSemantics.evalArgs
          Raw.SourceSemantics.evalTail Raw.SourceSemantics.eval
          Raw.SourceSemantics.evalValues Raw.SourceSemantics.fail
        simp only
        change
          Simulation.Interaction.bind
              (Simulation.Interaction.bind
                (Yul.InteractionSemantics.Primitive.fail state .OutOfFuel :
                  Open (State × List Frontend.Word))
                (fun result => pure (result.1, result.2.head!)))
              (fun result =>
                Yul.InteractionSemantics.Primitive.fail
                  result.1 .OutOfFuel) =
            Yul.InteractionSemantics.Primitive.fail state .OutOfFuel
        rw [Yul.InteractionSemantics.Primitive.bind_fail]
        rw [Yul.InteractionSemantics.Primitive.bind_fail]]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

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

/-- Source-facing expression preservation at one source fuel. The checked
context relates both object metadata and generated lexical function scopes. -/
def ScopedExprElaborationRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    CompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      (Elab.Expr.elaborate rawExpr).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext rawExpr ordered contract state

/-- Source-facing recursive expression interface at every source fuel. -/
def ScopedExprElaborationRunForward
    (slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel,
    ScopedExprElaborationRunForwardAt rawFuel slack builtinContext contract

/-- The well-founded recursive hypothesis available strictly below one source
fuel. Call and argument constructors consume this form. -/
def ScopedExprElaborationRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedExprElaborationRunForwardAt rawFuel slack builtinContext contract

/-- Path-scoped expression preservation. Unlike the older private callback
interface, this carries only evidence computed for the actual successful
elaborator action. -/
def ScopedExprPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawExpr : Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      ClzCompilationPath contract elabState finalElabState →
      (Elab.Expr.elaborate rawExpr).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext rawExpr ordered contract state

def ScopedExprPathRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedExprPathRunForwardAt rawFuel slack builtinContext contract

theorem ScopedExprElaborationRunForward.below
    {slack bound : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract) :
    ScopedExprElaborationRunForwardBelow
      bound slack builtinContext contract := by
  intro rawFuel _hFuel
  exact hExpr rawFuel

/-- Recursive lexical-block interface paired with
`ScopedExprElaborationRunForward`. Child blocks construct a fresh head scope;
function calls reuse the definition-site suffix returned by
`CompiledFunctionScopes.resolve`. -/
def ScopedBlockElaborationRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    CompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      (Elab.Stmt.List.elaborateBlock rawCode true).run elabState =
          .ok (front, finalElabState) →
        StmtListNormalized builtinContext front ordered →
          BlockCodeRunForward rawFuel (rawFuel + slack)
            rawContext rawCode ordered contract state

def ScopedBlockElaborationRunForward
    (slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel,
    ScopedBlockElaborationRunForwardAt rawFuel slack builtinContext contract

def ScopedBlockElaborationRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedBlockElaborationRunForwardAt rawFuel slack builtinContext contract

/-- Path-scoped lexical-block preservation, paired with
`ScopedExprPathRunForwardAt` for the final mutual source-fuel induction. -/
def ScopedBlockPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State} {state : State},
    PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      ClzCompilationPath contract elabState finalElabState →
      (Elab.Stmt.List.elaborateBlock rawCode true).run elabState =
          .ok (front, finalElabState) →
        StmtListNormalized builtinContext front ordered →
          BlockCodeRunForward rawFuel (rawFuel + slack)
            rawContext rawCode ordered contract state

def ScopedBlockPathRunForwardBelow
    (bound slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ rawFuel, rawFuel < bound →
    ScopedBlockPathRunForwardAt rawFuel slack builtinContext contract

theorem scopedExprPathRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedExprPathRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawExpr front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  exact exprValuesRunForward_zero

theorem ScopedBlockElaborationRunForward.below
    {slack bound : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hBlock :
      ScopedBlockElaborationRunForward slack builtinContext contract) :
    ScopedBlockElaborationRunForwardBelow
      bound slack builtinContext contract := by
  intro rawFuel _hFuel
  exact hBlock rawFuel

theorem scopedExprElaborationRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedExprElaborationRunForwardAt
      0 slack builtinContext contract := by
  intro rawContext rawExpr front ordered elabState finalElabState state
    hContext hElab hNormalized
  exact exprValuesRunForward_zero

theorem blockCodeRunForward_zero
    {orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {ordered : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    BlockCodeRunForward 0 orderedFuel
      rawContext rawCode ordered contract state := by
  unfold BlockCodeRunForward
  rw [Raw.SourceSemantics.execBlock_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem scopedBlockElaborationRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedBlockElaborationRunForwardAt
      0 slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState state
    hContext hElab hNormalized
  exact blockCodeRunForward_zero

theorem scopedBlockPathRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedBlockPathRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  exact blockCodeRunForward_zero

/-- Private semantic interface for compiler-generated `clz` replacement at one
fuel. The final frontend theorem discharges this from helper generation,
ordered lookup, and the helper-body execution theorem. -/
def ClzElaborationRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    CompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext (.functionCall "clz" rawArgs)
            ordered contract state

/-- Path-scoped generated-`clz` interface used by the final recursive frontend
theorem. It exposes no resolver over unrelated elaborator states. -/
def ClzPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State} {state : State},
    PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      ClzCompilationPath contract elabState finalElabState →
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
          .ok (front, finalElabState) →
        ExprNormalized builtinContext front ordered →
          ExprValuesRunForward rawFuel (rawFuel + slack)
            rawContext (.functionCall "clz" rawArgs)
            ordered contract state

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

/-- Pointwise expression compilation carrying the exact generated-helper path
for each occurrence. Because paths are stored per node, the evidence survives
the runtime reversal of call arguments without pretending elaboration itself
ran in reverse. -/
inductive PathScopedExprListCompiled
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract)
    (generatedScopes : List (List (Name × Name))) :
    List Raw.Expr → List Frontend.AstExpr → Prop where
  | nil :
      PathScopedExprListCompiled builtinContext contract generatedScopes [] []
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
      (headPath :
        ClzCompilationPath contract elabState finalElabState)
      (tail :
        PathScopedExprListCompiled builtinContext contract generatedScopes
          rawTail orderedTail) :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        (rawHead :: rawTail) (orderedHead :: orderedTail)

namespace PathScopedExprListCompiled

theorem of_elaboration
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ∀ {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
      {ordered : List Frontend.AstExpr}
      {elabState finalElabState : Elab.State},
      (Elab.Expr.List.elaborate rawExprs).run elabState =
          .ok (fronts, finalElabState) →
        ExprListNormalized builtinContext fronts ordered →
          ClzCompilationPath contract elabState finalElabState →
            PathScopedExprListCompiled builtinContext contract
              elabState.functionScopes rawExprs ordered := by
  intro rawExprs
  induction rawExprs with
  | nil =>
      intro fronts ordered elabState finalElabState hElab hNormalized hPath
      simp [Elab.Expr.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := ExprListNormalized.nil_ordered hNormalized
      subst ordered
      exact .nil
  | cons rawHead rawTail ih =>
      intro fronts ordered elabState finalElabState hElab hNormalized hPath
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
              have hHeadExt :=
                Elab.Expr.elaborate_preserves_clzAllocation rawHead
                  hHead hPath.entryValid
              have hTailExt :=
                Elab.Expr.List.elaborate_preserves_clzAllocation rawTail
                  hTail hHeadExt.after_valid
              have hHeadScopes :
                  headElabState.functionScopes =
                    elabState.functionScopes :=
                Elab.Expr.elaborate_preserves_functionScopes rawHead hHead
              have hHeadPath :
                  ClzCompilationPath contract elabState headElabState :=
                hPath.prefixPath hTailExt
              have hTailPath :
                  ClzCompilationPath contract
                    headElabState tailElabState :=
                hPath.suffixPath hHeadExt
              have hTailCompiled :=
                ih hTail hTailNormalized hTailPath
              rw [hHeadScopes] at hTailCompiled
              exact
                .cons hHead rfl hHeadNormalized hHeadPath hTailCompiled

theorem append
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generatedScopes : List (List (Name × Name))}
    {rawLeft rawRight : List Raw.Expr}
    {orderedLeft orderedRight : List Frontend.AstExpr}
    (hLeft :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        rawLeft orderedLeft)
    (hRight :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        rawRight orderedRight) :
    PathScopedExprListCompiled builtinContext contract generatedScopes
      (rawLeft ++ rawRight) (orderedLeft ++ orderedRight) := by
  induction hLeft with
  | nil => exact hRight
  | cons hElab hScopes hNormalized hPath hTail ih =>
      exact .cons hElab hScopes hNormalized hPath ih

theorem reverse
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hCompiled :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        rawExprs ordered) :
    PathScopedExprListCompiled builtinContext contract generatedScopes
      rawExprs.reverse ordered.reverse := by
  induction hCompiled with
  | nil => exact .nil
  | @cons rawHead orderedHead rawTail orderedTail frontHead
      elabState finalElabState hElab hScopes hNormalized hPath hTail ih =>
      simpa using
        append ih
          (.cons hElab hScopes hNormalized hPath
            (.nil :
              PathScopedExprListCompiled builtinContext contract
                generatedScopes [] []))

end PathScopedExprListCompiled

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

theorem orderedEvalArgs_single
    (fuel : Nat) (arg : Frontend.AstExpr)
    (contract : Frontend.AstContract) (state : State) :
    Yul.InteractionSemantics.evalArgs (fuel + 3) [arg]
        (some contract) state =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.eval (fuel + 2) arg
          (some contract) state)
        (fun result => Simulation.Interaction.pure (result.1, [result.2])) := by
  rw [show fuel + 3 = (fuel + 1) + 2 by omega,
    Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
  simp only [Yul.InteractionSemantics.evalArgs,
    Yul.Source.Canonical.evalArgs, Yul.Source.Effectful.evalArgs]
  rw [Yul.InteractionSemantics.eval_eq_bind]
  rw [show fuel + 1 + 1 = fuel + 2 by omega]
  rw [Simulation.Interaction.bind_assoc]
  apply congrArg (fun next =>
    Simulation.Interaction.bind
      (Yul.InteractionSemantics.evalValues
        (fuel + 2) arg (some contract) state) next)
  funext result
  rfl

theorem argsRunForward_of_scoped_compiled
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract) :
    ∀ {rawContext : Raw.SourceSemantics.Context}
      {generatedScopes : List (List (Name × Name))}
      {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr},
      CompiledContext builtinContext contract rawContext generatedScopes →
        ScopedExprListCompiled builtinContext generatedScopes
          rawExprs ordered →
          ∀ (rawBase : Nat) (state : State),
            ArgsRunForward
              (rawBase + 2 * rawExprs.length + 1)
              ((rawBase + slack) + 2 * rawExprs.length + 1)
              rawContext rawExprs ordered contract state := by
  intro rawContext generatedScopes rawExprs ordered hContext hCompiled
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
      have hHeadContext :
          CompiledContext builtinContext contract rawContext
            elabState.functionScopes :=
        { objectBuiltins := hContext.objectBuiltins
          functionScopes := by
            simpa [hScopes] using hContext.functionScopes }
      have hHeadValues :=
        hExpr (rawTailFuel + 1) hHeadContext
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
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
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
    argsRunForward_of_scoped_compiled hExpr hContext hReversed
      rawBase state

/-- Argument-list preservation at every source fuel. The two-step source
schedule mirrors `evalArgs`/`evalTail`: fuel zero truncates immediately, fuel
one truncates on a nonempty head, and fuel `n + 2` recursively evaluates the
head at `n + 1` and the tail at `n`. -/
theorem argsRunForward_of_scoped_compiled_fuel
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hContext :
      CompiledContext builtinContext contract rawContext generatedScopes)
    (hCompiled :
      ScopedExprListCompiled builtinContext generatedScopes
        rawExprs ordered) :
  ∀ (rawFuel : Nat) (state : State),
      ArgsRunForward rawFuel (rawFuel + slack)
        rawContext rawExprs ordered contract state := by
  intro rawFuel
  induction rawFuel using Nat.strong_induction_on generalizing
      rawExprs ordered with
  | h rawFuel ih =>
      intro state
      cases rawFuel with
      | zero =>
          exact argsRunForward_zero
      | succ predecessor =>
          cases predecessor with
          | zero =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := 0) (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | cons hElab hScopes hNormalized hTail =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_cons_one
                      (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
          | succ residual =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := residual + 1)
                      (orderedFuel := (residual + 1) + slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | @cons rawHead orderedHead rawTail orderedTail frontHead
                  elabState finalElabState hElab hScopes hNormalized hTail =>
                  have hHeadContext :
                      CompiledContext builtinContext contract rawContext
                        elabState.functionScopes :=
                    { objectBuiltins := hContext.objectBuiltins
                      functionScopes := by
                        simpa [hScopes] using hContext.functionScopes }
                  have hHeadValues :=
                    hExpr (residual + 1) hHeadContext
                      (state := state) hElab hNormalized
                  have hHead := exprRunForward_of_values hHeadValues
                  have hTailRun :
                      ∀ stateAfterHead,
                        ArgsRunForward residual (residual + slack)
                          rawContext rawTail orderedTail contract
                          stateAfterHead := by
                    intro stateAfterHead
                    exact
                      ih residual (by omega) hTail stateAfterHead
                  have hCons :=
                    argsRunForward_cons
                      (rawFuel := residual)
                      (orderedFuel := residual + slack)
                      (context := rawContext) (rawArg := rawHead)
                      (rawRest := rawTail) (orderedArg := orderedHead)
                      (orderedRest := orderedTail) (contract := contract)
                      (state := state) (by
                        simpa [Nat.add_comm, Nat.add_left_comm,
                          Nat.add_assoc] using hHead)
                      hTailRun
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using hCons

/-- Argument preservation from only the strictly-lower expression hypotheses
needed by the source evaluator. This is the form used by the final source-fuel
induction. -/
theorem argsRunForward_of_scoped_compiled_fuel_below
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        rawFuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hContext :
      CompiledContext builtinContext contract rawContext generatedScopes)
    (hCompiled :
      ScopedExprListCompiled builtinContext generatedScopes
        rawExprs ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs ordered contract state := by
  induction rawFuel using Nat.strong_induction_on generalizing
      rawExprs ordered state with
  | h rawFuel ih =>
      cases rawFuel with
      | zero =>
          exact argsRunForward_zero
      | succ predecessor =>
          cases predecessor with
          | zero =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := 0) (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | cons hElab hScopes hNormalized hTail =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_cons_one
                      (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
          | succ residual =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := residual + 1)
                      (orderedFuel := (residual + 1) + slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | @cons rawHead orderedHead rawTail orderedTail frontHead
                  elabState finalElabState hElab hScopes hNormalized hTail =>
                  have hHeadContext :
                      CompiledContext builtinContext contract rawContext
                        elabState.functionScopes :=
                    { objectBuiltins := hContext.objectBuiltins
                      functionScopes := by
                        simpa [hScopes] using hContext.functionScopes }
                  have hHeadValues :=
                    hExpr (residual + 1) (by omega)
                      hHeadContext (state := state) hElab hNormalized
                  have hHead := exprRunForward_of_values hHeadValues
                  have hTailBelow :
                      ScopedExprElaborationRunForwardBelow
                        residual slack builtinContext contract := by
                    intro fuel hFuel
                    exact hExpr fuel (by omega)
                  have hTailRun :
                      ∀ stateAfterHead,
                        ArgsRunForward residual (residual + slack)
                          rawContext rawTail orderedTail contract
                          stateAfterHead := by
                    intro stateAfterHead
                    exact
                      ih residual (by omega) hTailBelow hTail
                        stateAfterHead
                  have hCons :=
                    argsRunForward_cons
                      (rawFuel := residual)
                      (orderedFuel := residual + slack)
                      (context := rawContext) (rawArg := rawHead)
                      (rawRest := rawTail) (orderedArg := orderedHead)
                      (orderedRest := orderedTail) (contract := contract)
                      (state := state) (by
                        simpa [Nat.add_comm, Nat.add_left_comm,
                          Nat.add_assoc] using hHead)
                      hTailRun
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using hCons

theorem argsRunForward_reverse_of_scoped_elaboration_fuel
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForward slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    ScopedExprListCompiled.of_elaboration hElab hNormalized
  have hReversed := ScopedExprListCompiled.reverse hCompiled
  exact
    argsRunForward_of_scoped_compiled_fuel
      hExpr hContext hReversed rawFuel state

theorem argsRunForward_reverse_of_scoped_elaboration_fuel_below
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        rawFuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    ScopedExprListCompiled.of_elaboration hElab hNormalized
  have hReversed := ScopedExprListCompiled.reverse hCompiled
  exact
    argsRunForward_of_scoped_compiled_fuel_below
      hExpr hContext hReversed state

/-- Arbitrary-fuel argument preservation over occurrence-local compilation
paths. This is stable under argument reversal because each node retains its
own exact elaborator path to the final artifact binding. -/
theorem argsRunForward_of_path_scoped_compiled_fuel_below
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprPathRunForwardBelow
        rawFuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {generatedScopes : List (List (Name × Name))}
    {rawExprs : List Raw.Expr} {ordered : List Frontend.AstExpr}
    (hContext :
      PathCompiledContext builtinContext contract rawContext generatedScopes)
    (hCompiled :
      PathScopedExprListCompiled builtinContext contract generatedScopes
        rawExprs ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs ordered contract state := by
  induction rawFuel using Nat.strong_induction_on generalizing
      rawExprs ordered state with
  | h rawFuel ih =>
      cases rawFuel with
      | zero =>
          exact argsRunForward_zero
      | succ predecessor =>
          cases predecessor with
          | zero =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := 0) (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | cons hElab hScopes hNormalized hPath hTail =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_cons_one
                      (orderedFuel := slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
          | succ residual =>
              cases hCompiled with
              | nil =>
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using
                    (argsRunForward_nil_succ
                      (rawFuel := residual + 1)
                      (orderedFuel := (residual + 1) + slack)
                      (context := rawContext) (contract := contract)
                      (state := state))
              | @cons rawHead orderedHead rawTail orderedTail frontHead
                  elabState finalElabState hElab hScopes hNormalized
                  hHeadPath hTail =>
                  have hHeadContext :
                      PathCompiledContext builtinContext contract rawContext
                        elabState.functionScopes :=
                    { objectBuiltins := hContext.objectBuiltins
                      functionScopes := by
                        simpa [hScopes] using hContext.functionScopes }
                  have hHeadValues :=
                    hExpr (residual + 1) (by omega)
                      hHeadContext hHeadPath (state := state)
                        hElab hNormalized
                  have hHead := exprRunForward_of_values hHeadValues
                  have hTailBelow :
                      ScopedExprPathRunForwardBelow
                        residual slack builtinContext contract := by
                    intro fuel hFuel
                    exact hExpr fuel (by omega)
                  have hTailRun :
                      ∀ stateAfterHead,
                        ArgsRunForward residual (residual + slack)
                          rawContext rawTail orderedTail contract
                          stateAfterHead := by
                    intro stateAfterHead
                    exact
                      ih residual (by omega) hTailBelow hTail
                        stateAfterHead
                  have hCons :=
                    argsRunForward_cons
                      (rawFuel := residual)
                      (orderedFuel := residual + slack)
                      (context := rawContext) (rawArg := rawHead)
                      (rawRest := rawTail) (orderedArg := orderedHead)
                      (orderedRest := orderedTail) (contract := contract)
                      (state := state) (by
                        simpa [Nat.add_comm, Nat.add_left_comm,
                          Nat.add_assoc] using hHead)
                      hTailRun
                  simpa [Nat.add_comm, Nat.add_left_comm,
                    Nat.add_assoc] using hCons

theorem argsRunForward_reverse_of_path_elaboration_fuel_below
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprPathRunForwardBelow
        rawFuel slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawExprs : List Raw.Expr} {fronts : List Frontend.Expr}
    {ordered : List Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.List.elaborate rawExprs).run elabState =
        .ok (fronts, finalElabState))
    (hNormalized : ExprListNormalized builtinContext fronts ordered)
    (state : State) :
    ArgsRunForward rawFuel (rawFuel + slack)
      rawContext rawExprs.reverse ordered.reverse contract state := by
  have hCompiled :=
    PathScopedExprListCompiled.of_elaboration hElab hNormalized hPath
  have hReversed := PathScopedExprListCompiled.reverse hCompiled
  exact
    argsRunForward_of_path_scoped_compiled_fuel_below
      hExpr hContext hReversed state

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

theorem exprValuesRunForward_of_scoped_elaborated_primitiveCall_below
    {slack argsFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        argsFuel slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
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
              argsFuel (argsFuel + slack)
              stateAfterArgs op values.reverse) :
    ExprValuesRunForward
      (argsFuel + 1)
      ((argsFuel + slack) + 1)
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
      have hArgsRun :=
        argsRunForward_reverse_of_scoped_elaboration_fuel_below
          hExpr hContext hArgs hArgsNormalized
          state
      have hCall :=
        exprValuesRunForward_primitiveCall_of_runs
          hNotClz hClass hOp hArgsRun (hPrimitive op hOp)
      exact hCall

theorem exprValuesRunForward_of_path_elaborated_primitiveCall_below
    {slack argsFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        argsFuel slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
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
              argsFuel (argsFuel + slack)
              stateAfterArgs op values.reverse) :
    ExprValuesRunForward
      (argsFuel + 1)
      ((argsFuel + slack) + 1)
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
      have hArgsRun :=
        argsRunForward_reverse_of_path_elaboration_fuel_below
          hExpr hContext hPath hArgs hArgsNormalized state
      exact
        exprValuesRunForward_primitiveCall_of_runs
          hNotClz hClass hOp hArgsRun (hPrimitive op hOp)

theorem exprValuesRunForward_userCall_one
    {orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user) :
    ExprValuesRunForward 1 orderedFuel rawContext
      (.functionCall name rawArgs) ordered contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    0 rawContext name rawArgs state hNotClz]
  simp only [hClass]
  rw [Raw.SourceSemantics.evalArgs_zero]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem exprValuesRunForward_objectBuiltinCall_one
    {orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .objectBuiltin) :
    ExprValuesRunForward 1 orderedFuel rawContext
      (.functionCall name rawArgs) ordered contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    0 rawContext name rawArgs state hNotClz]
  simp only [hClass]
  unfold Raw.SourceSemantics.evalObjectBuiltin
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem exprValuesRunForward_clz_one
    {orderedFuel : Nat}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State} :
    ExprValuesRunForward 1 orderedFuel rawContext
      (.functionCall "clz" [rawArg]) ordered contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.clz_succ 0 rawContext rawArg state]
  unfold Raw.SourceSemantics.eval
  simp only [Raw.SourceSemantics.evalValues]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem exprValuesRunForward_generatedClz
    {rawArgFuel orderedBase : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {generated : Name}
    {orderedArg : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun : GeneratedClzCallRun rawArgFuel (orderedBase + 2)
      (orderedBase + 3)
      context rawArg generated orderedArg contract state) :
    ExprValuesRunForward (rawArgFuel + 1) (orderedBase + 4)
      context (.functionCall "clz" [rawArg])
      (.Call (.inr generated) [orderedArg]) contract state := by
  unfold ExprValuesRunForward
  rw [Raw.SourceSemantics.EvalValues.clz_succ]
  rw [show orderedBase + 4 = (orderedBase + 3) + 1 by omega,
    Yul.InteractionSemantics.EvalValues.internal_succ]
  simp only [List.reverse_singleton]
  rw [orderedEvalArgs_single]
  rw [Simulation.Interaction.bind_assoc]
  have hArg := hRun.argForward
  unfold ExprRunForward at hArg
  refine Simulation.Interaction.ForwardRel.bind_custom hArg ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error =>
      exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      rcases result with ⟨stateAfterArg, value⟩
      cases stateAfterArg with
      | OutOfFuel =>
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [
                Yul.FunctionsInteractionPrimitive.Truncated])
      | Checkpoint jump =>
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [
                Yul.FunctionsInteractionPrimitive.Truncated])
      | Ok shared store =>
          simp only [Simulation.Interaction.instMonad,
            Simulation.Interaction.pure, Simulation.Interaction.bind,
            List.reverse_singleton]
          rw [Raw.ClzPreservation.clzHelperCall
            hRun.binding.namesDistinct hRun.binding.orderedLookup
            hRun.binding.bodyToYul
            shared store value (orderedBase + 3) hRun.bodyFuel]
          apply Simulation.Interaction.ForwardRel.done
          unfold SameDoneRel
          rw [Elab.ClzHelperModel.run_eq_reference]

theorem exprValuesRunForward_of_scoped_clz_parts
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {frontArg : Frontend.Expr}
    {orderedArg : Frontend.AstExpr} {generated : Name}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        context elabState.functionScopes)
    (hArgElab :
      (Elab.Expr.elaborate rawArg).run elabState =
        .ok (frontArg, finalElabState))
    (hArgNormalized :
      ExprNormalized builtinContext frontArg orderedArg)
    (binding : CompiledClzBinding contract generated)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack + 1) :
    ExprValuesRunForward (rawArgFuel + 1) ((rawArgFuel + slack) + 2)
      context (.functionCall "clz" [rawArg])
      (.Call (.inr generated) [orderedArg]) contract state := by
  have hArgValues :=
    hExpr (state := state) hContext hArgElab hArgNormalized
  have hArgRun := exprRunForward_of_values hArgValues
  let orderedBase := rawArgFuel + slack - 2
  have hBase : orderedBase + 2 = rawArgFuel + slack := by
    dsimp [orderedBase]
    omega
  have hBodyFuel :
      Raw.ClzPreservation.stmtListFuel
          (Elab.clzHelperBody binding.argName binding.returnName) + 2 ≤
        orderedBase + 3 := by
    rw [Raw.ClzPreservation.helperBodyFuel_eq]
    dsimp [orderedBase]
    omega
  have hRun :
      GeneratedClzCallRun rawArgFuel (orderedBase + 2) (orderedBase + 3)
        context rawArg generated
        orderedArg contract state :=
    { binding := binding
      bodyFuel := hBodyFuel
      argForward := by simpa [hBase] using hArgRun }
  have hCall := exprValuesRunForward_generatedClz hRun
  have hTargetEq : orderedBase + 4 = rawArgFuel + slack + 2 := by
    dsimp [orderedBase]
    omega
  rw [hTargetEq] at hCall
  exact hCall

theorem exprValuesRunForward_of_scoped_elaborated_clz_at
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        context elabState.functionScopes)
    (hValid : Elab.ClzAllocationValid elabState)
    (hBindings : ClzBindingResolverAt contract finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack + 1) :
    ExprValuesRunForward (rawArgFuel + 1) ((rawArgFuel + slack) + 2)
      context (.functionCall "clz" rawArgs) ordered contract state := by
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  rcases ExprNormalized.user_call_parts hNormalized with
    ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
  rcases ExprListNormalized.cons_parts hArgsNormalized with
    ⟨orderedArg, orderedTail, hOrderedArgs,
      ⟨hArgNormalized⟩, ⟨hTailNormalized⟩⟩
  have hTail : orderedTail = [] :=
    ExprListNormalized.nil_ordered hTailNormalized
  subst orderedTail
  subst orderedArgs
  have hArgExt :=
    Elab.Expr.elaborate_preserves_clzAllocation rawArg hArgElab hValid
  rcases Elab.ensureClzHelper_allocated hEnsure hArgExt.after_valid with
    ⟨argName, returnName, hAllocated⟩
  rcases hBindings hAllocated with ⟨binding⟩
  exact
    exprValuesRunForward_of_scoped_clz_parts
      hExpr hContext hArgElab hArgNormalized binding
      hArgTarget hHelperFuel

/-- Path-native generated-`clz` preservation. The argument prefix receives a
resolver transported backward through `ensureClzHelper`; the exact helper
binding is then read from the actual expression-final state. -/
theorem exprValuesRunForward_of_scoped_elaborated_clz_path
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        context elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack + 1) :
    ExprValuesRunForward (rawArgFuel + 1) ((rawArgFuel + slack) + 2)
      context (.functionCall "clz" rawArgs) ordered contract state := by
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  rcases ExprNormalized.user_call_parts hNormalized with
    ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
  rcases ExprListNormalized.cons_parts hArgsNormalized with
    ⟨orderedArg, orderedTail, hOrderedArgs,
      ⟨hArgNormalized⟩, ⟨hTailNormalized⟩⟩
  have hTail : orderedTail = [] :=
    ExprListNormalized.nil_ordered hTailNormalized
  subst orderedTail
  subst orderedArgs
  have hArgExt :=
    Elab.Expr.elaborate_preserves_clzAllocation rawArg
      hArgElab hPath.entryValid
  have hEnsureExt :=
    Elab.ensureClzHelper_preserves_clzAllocation
      hEnsure hArgExt.after_valid
  have hArgPath :
      ClzCompilationPath contract elabState argState :=
    hPath.prefixPath hEnsureExt
  have hArgValues :=
    hExpr (state := state) hContext hArgPath hArgElab hArgNormalized
  have hArgRun := exprRunForward_of_values hArgValues
  rcases Elab.ensureClzHelper_allocated hEnsure hArgExt.after_valid with
    ⟨argName, returnName, hAllocated⟩
  rcases hPath.finalResolver hAllocated with ⟨binding⟩
  let orderedBase := rawArgFuel + slack - 2
  have hBase : orderedBase + 2 = rawArgFuel + slack := by
    dsimp [orderedBase]
    omega
  have hBodyFuel :
      Raw.ClzPreservation.stmtListFuel
          (Elab.clzHelperBody binding.argName binding.returnName) + 2 ≤
        orderedBase + 3 := by
    rw [Raw.ClzPreservation.helperBodyFuel_eq]
    dsimp [orderedBase]
    omega
  have hRun :
      GeneratedClzCallRun rawArgFuel (orderedBase + 2) (orderedBase + 3)
        context rawArg generated
        orderedArg contract state :=
    { binding := binding
      bodyFuel := hBodyFuel
      argForward := by simpa [hBase] using hArgRun }
  have hCall := exprValuesRunForward_generatedClz hRun
  have hTargetEq : orderedBase + 4 = rawArgFuel + slack + 2 := by
    dsimp [orderedBase]
    omega
  rw [hTargetEq] at hCall
  exact hCall

theorem exprValuesRunForward_of_scoped_elaborated_clz
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        context elabState.functionScopes)
    (hBindings : ClzBindingResolver contract)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack + 1) :
    ExprValuesRunForward (rawArgFuel + 1) ((rawArgFuel + slack) + 2)
      context (.functionCall "clz" rawArgs) ordered contract state := by
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  rcases ExprNormalized.user_call_parts hNormalized with
    ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
  rcases ExprListNormalized.cons_parts hArgsNormalized with
    ⟨orderedArg, orderedTail, hOrderedArgs,
      ⟨hArgNormalized⟩, ⟨hTailNormalized⟩⟩
  have hTail : orderedTail = [] :=
    ExprListNormalized.nil_ordered hTailNormalized
  subst orderedTail
  subst orderedArgs
  rcases hBindings hEnsure with ⟨binding⟩
  exact
    exprValuesRunForward_of_scoped_clz_parts
      hExpr hContext hArgElab hArgNormalized binding
      hArgTarget hHelperFuel

def clzFrontendSlack : Nat :=
  Raw.ClzPreservation.helperBodyFuel + 1

theorem clzElaborationRunForwardAt_zero
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ClzElaborationRunForwardAt
      0 clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hElab hNormalized
  exact exprValuesRunForward_zero

theorem clzElaborationRunForwardAt_one
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ClzElaborationRunForwardAt
      1 clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hElab hNormalized
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  exact exprValuesRunForward_clz_one

theorem clzElaborationRunForwardAt_succ_succ
    {argFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprElaborationRunForwardAt
        (argFuel + 1) Raw.ClzPreservation.helperBodyFuel
        builtinContext contract)
    (hBindings : ClzBindingResolver contract) :
    ClzElaborationRunForwardAt
      (argFuel + 2) clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hElab hNormalized
  have hArgTarget :
      2 ≤ (argFuel + 1) + Raw.ClzPreservation.helperBodyFuel := by
    rw [Raw.ClzPreservation.helperBodyFuel_value]
    omega
  have hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        (argFuel + 1) + Raw.ClzPreservation.helperBodyFuel + 1 := by
    omega
  have hCall := exprValuesRunForward_of_scoped_elaborated_clz
    (state := state) hExpr hContext hBindings hElab hNormalized
      hArgTarget hHelperFuel
  simpa [clzFrontendSlack, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hCall

theorem clzPathRunForwardAt_zero
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ClzPathRunForwardAt
      0 clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  exact exprValuesRunForward_zero

theorem clzPathRunForwardAt_one
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ClzPathRunForwardAt
      1 clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  exact exprValuesRunForward_clz_one

theorem clzPathRunForwardAt_succ_succ
    {argFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprPathRunForwardAt
        (argFuel + 1) Raw.ClzPreservation.helperBodyFuel
        builtinContext contract) :
    ClzPathRunForwardAt
      (argFuel + 2) clzFrontendSlack builtinContext contract := by
  intro rawContext rawArgs front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  have hArgTarget :
      2 ≤ (argFuel + 1) + Raw.ClzPreservation.helperBodyFuel := by
    rw [Raw.ClzPreservation.helperBodyFuel_value]
    omega
  have hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        (argFuel + 1) + Raw.ClzPreservation.helperBodyFuel + 1 := by
    omega
  have hCall := exprValuesRunForward_of_scoped_elaborated_clz_path
    (state := state) hExpr hContext hPath hElab hNormalized
      hArgTarget hHelperFuel
  simpa [clzFrontendSlack, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hCall

/-- Call-body execution and caller restoration supplied by one bundled
generated-call occurrence, independently of its argument-fuel schedule. -/
theorem generatedUserCallRun_call_succ
    {rawFuel orderedArgsFuel orderedBodyFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawName : Name} {rawArgs : List Raw.Expr}
    {generated : Name} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {entryState stateAfterArgs : State}
    {reversedValues : List Frontend.Word}
    (hRun :
      GeneratedUserCallRun rawFuel orderedArgsFuel orderedBodyFuel
        context rawName rawArgs generated orderedArgs contract entryState) :
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Raw.SourceSemantics.call (rawFuel + 1) context
        reversedValues.reverse rawName stateAfterArgs)
      (Yul.InteractionSemantics.call (orderedBodyFuel + 1)
        reversedValues.reverse (some generated) (some contract)
        stateAfterArgs) := by
  rw [Raw.SourceSemantics.Call.explicit_succ
    rawFuel context reversedValues.reverse rawName stateAfterArgs
    hRun.fn hRun.lexicalScopes hRun.rawLookup]
  rw [Yul.InteractionSemantics.Call.explicit_succ
    orderedBodyFuel reversedValues.reverse generated contract
    hRun.fn.params hRun.fn.returns hRun.orderedBody stateAfterArgs
    hRun.orderedLookup]
  have hBodyForward := hRun.bodyForward stateAfterArgs reversedValues
  unfold BlockCodeRunForward at hBodyForward
  refine
    Simulation.Interaction.ForwardRel.bind_custom hBodyForward ?_
  intro rawBodyDone orderedBodyDone hBodyDone
  unfold SameDoneRel at hBodyDone
  subst orderedBodyDone
  cases rawBodyDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok stateAfterBody => exact Simulation.Interaction.ForwardRel.done rfl

theorem exprValuesRunForward_userCall_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawName : Name} {rawArgs : List Raw.Expr}
    {generated : Name} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun : GeneratedUserCallRun rawFuel orderedFuel orderedFuel context
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
      exact generatedUserCallRun_call_succ hRun

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
theorem exprValuesRunForward_of_scoped_elaborated_userCall_below
    {slack callFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        (callFuel + 2) slack builtinContext contract)
    (hBlock :
      ScopedBlockElaborationRunForwardBelow
        (callFuel + 2) slack builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward
      (callFuel + 2)
      ((callFuel + slack) + 2)
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
      have hArgsContext :
          CompiledContext builtinContext contract rawContext
            argsState.functionScopes :=
        { objectBuiltins := hContext.objectBuiltins
          functionScopes := by
            simpa [hArgsScopes] using hContext.functionScopes }
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
              hArgsContext.functionScopes hResolve with
            ⟨rawFn, rawLexical, generatedLexical,
              hRawResolve, ⟨hBinding⟩, hLexicalScopes⟩
          rcases CompiledFunctionBinding.block_parts hBinding with
            ⟨bodyElabState, finalBodyElabState, frontBody, orderedBody,
              hBodyScopes, hBodyElab, ⟨hBodyNormalized⟩,
              hOrderedLookup⟩
          have hBodyContext :
              CompiledContext builtinContext contract
                { rawContext with functionScopes := rawLexical }
                bodyElabState.functionScopes :=
            { objectBuiltins := by
                simpa using hContext.objectBuiltins
              functionScopes := by
                simpa [hBodyScopes] using hLexicalScopes }
          have hArgsRun :=
            argsRunForward_reverse_of_scoped_elaboration_fuel_below
              (rawFuel := callFuel + 1)
              (fun fuel hFuel => hExpr fuel (by omega))
              hContext hArgs hArgsNormalized state
          have hRawLookup :
              Raw.SourceSemantics.lookupFunctionWithLexicalScopes
                  rawContext name = some (rawFn, rawLexical) := by
            simpa [Raw.SourceSemantics.lookupFunctionWithLexicalScopes]
              using hRawResolve
          have hRun :
              GeneratedUserCallRun callFuel (callFuel + slack)
                (callFuel + slack)
                rawContext name rawArgs generated orderedArgs contract state :=
            { fn := rawFn
              lexicalScopes := rawLexical
              orderedBody := orderedBody
              notClz := hNotClz
              callClass := hClass
              rawLookup := hRawLookup
              orderedLookup := hOrderedLookup
              argsForward := by
                simpa [Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hArgsRun
              bodyForward := by
                intro stateAfterArgs values
                have hBody :=
                  hBlock callFuel (by omega)
                    (rawContext :=
                      { rawContext with functionScopes := rawLexical })
                    hBodyContext
                    (state :=
                      Yul.InteractionSemantics.stateModel.withSource
                        stateAfterArgs
                        (EvmYul.Yul.State.mkOk
                          (stateAfterArgs.initcall rawFn.params
                            rawFn.returns values.reverse)))
                    hBodyElab hBodyNormalized
                simpa [Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using hBody }
          have hCall := exprValuesRunForward_userCall_succ hRun
          exact hCall

/-- Construct the bundled generated-call execution evidence from one actual
checked path. Both value-position calls and expression statements consume this
same interface; generated names and callee layouts remain existential. -/
theorem generatedUserCallRun_of_path_elaboration_below
    {argsSlack bodySlack callFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        (callFuel + 2) argsSlack builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (callFuel + 2) bodySlack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ∃ generated orderedArgs,
      ordered = .Call (.inr generated) orderedArgs ∧
        Nonempty
          (GeneratedUserCallRun callFuel (callFuel + argsSlack)
            (callFuel + bodySlack)
            rawContext name rawArgs generated orderedArgs contract state) := by
  unfold Elab.Expr.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hArgs : (Elab.Expr.List.elaborate rawArgs).run elabState with
  | error err => simp [hArgs] at hElab
  | ok argsResult =>
      rcases argsResult with ⟨frontArgs, argsState⟩
      have hArgsScopes :
          argsState.functionScopes = elabState.functionScopes :=
        Elab.Expr.List.elaborate_preserves_functionScopes rawArgs hArgs
      have hArgsContext :
          PathCompiledContext builtinContext contract rawContext
            argsState.functionScopes :=
        { objectBuiltins := hContext.objectBuiltins
          functionScopes := by
            simpa [hArgsScopes] using hContext.functionScopes }
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
          rcases PathCompiledFunctionScopes.resolve
              hArgsContext.functionScopes hResolve with
            ⟨rawFn, rawLexical, generatedLexical,
              hRawResolve, ⟨hBinding⟩, hLexicalScopes⟩
          rcases PathCompiledFunctionBinding.block_parts hBinding with
            ⟨bodyElabState, finalBodyElabState, frontBody, orderedBody,
              hBodyScopes, hBodyElab, ⟨hBodyNormalized⟩,
              hOrderedLookup, ⟨hBodyPath⟩⟩
          have hBodyContext :
              PathCompiledContext builtinContext contract
                { rawContext with functionScopes := rawLexical }
                bodyElabState.functionScopes :=
            { objectBuiltins := by
                simpa using hContext.objectBuiltins
              functionScopes := by
                simpa [hBodyScopes] using hLexicalScopes }
          have hArgsRun :=
            argsRunForward_reverse_of_path_elaboration_fuel_below
              (rawFuel := callFuel + 1)
              (fun fuel hFuel => hExpr fuel (by omega))
              hContext hPath hArgs hArgsNormalized state
          have hRawLookup :
              Raw.SourceSemantics.lookupFunctionWithLexicalScopes
                  rawContext name = some (rawFn, rawLexical) := by
            simpa [Raw.SourceSemantics.lookupFunctionWithLexicalScopes]
              using hRawResolve
          have hRun :
              GeneratedUserCallRun callFuel (callFuel + argsSlack)
                (callFuel + bodySlack)
                rawContext name rawArgs generated orderedArgs contract state :=
            { fn := rawFn
              lexicalScopes := rawLexical
              orderedBody := orderedBody
              notClz := hNotClz
              callClass := hClass
              rawLookup := hRawLookup
              orderedLookup := hOrderedLookup
              argsForward := by
                simpa [Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hArgsRun
              bodyForward := by
                intro stateAfterArgs values
                have hBody :=
                  hBlock callFuel (by omega)
                    (rawContext :=
                      { rawContext with functionScopes := rawLexical })
                    hBodyContext hBodyPath
                    (state :=
                      Yul.InteractionSemantics.stateModel.withSource
                        stateAfterArgs
                        (EvmYul.Yul.State.mkOk
                          (stateAfterArgs.initcall rawFn.params
                            rawFn.returns values.reverse)))
                    hBodyElab hBodyNormalized
                simpa [Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using hBody }
          exact ⟨generated, orderedArgs, rfl, ⟨hRun⟩⟩

/-- Path-scoped ordinary user calls. The lexical lookup returns a checked
callee binding carrying its own function-body elaboration path, so recursive
calls and generated `clz` inside nested functions require no semantic oracle. -/
theorem exprValuesRunForward_of_path_elaborated_userCall_below
    {slack callFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        (callFuel + 2) slack builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (callFuel + 2) slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hNotMemoryguard : name ≠ "memoryguard")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user)
    (hElab :
      (Elab.Expr.elaborate (.functionCall name rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward
      (callFuel + 2)
      ((callFuel + slack) + 2)
      rawContext (.functionCall name rawArgs) ordered contract state := by
  rcases generatedUserCallRun_of_path_elaboration_below
      hExpr hBlock hContext hPath hNotMemoryguard hNotClz hClass
      hElab hNormalized with
    ⟨generated, orderedArgs, rfl, ⟨hRun⟩⟩
  exact exprValuesRunForward_userCall_succ hRun

namespace ExprNormalized

theorem datasize_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "datasize" args) ordered) :
    ∃ nameArg dataName size,
      args = [nameArg] ∧
        Frontend.Expr.objectBuiltinNameArg? nameArg = some dataName ∧
        context.size? dataName = some size ∧
        ordered = .Lit size := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons nameArg rest =>
      cases rest with
      | nil =>
          cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
          | none => simp [hName] at hResolve
          | some dataName =>
              cases hSize : context.size? dataName with
              | none => simp [hName, hSize] at hResolve
              | some size =>
                  simp [hName, hSize] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  exact ⟨nameArg, dataName, size, rfl, hName, hSize,
                    hToYul.symm⟩
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (nameArg :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

theorem dataoffset_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "dataoffset" args) ordered) :
    ∃ nameArg dataName offset,
      args = [nameArg] ∧
        Frontend.Expr.objectBuiltinNameArg? nameArg = some dataName ∧
        context.offset? dataName = some offset ∧
        ordered = .Lit offset := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons nameArg rest =>
      cases rest with
      | nil =>
          cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
          | none => simp [hName] at hResolve
          | some dataName =>
              cases hOffset : context.offset? dataName with
              | none => simp [hName, hOffset] at hResolve
              | some offset =>
                  simp [hName, hOffset] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  exact ⟨nameArg, dataName, offset, rfl, hName, hOffset,
                    hToYul.symm⟩
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (nameArg :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

theorem linkersymbol_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "linkersymbol" args) ordered) :
    ∃ nameArg linkerName value,
      args = [nameArg] ∧
        Frontend.Expr.objectBuiltinNameArg? nameArg = some linkerName ∧
        context.findLinkerSymbol? linkerName = some value ∧
        ordered = .Lit value := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons nameArg rest =>
      cases rest with
      | nil =>
          cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
          | none => simp [hName] at hResolve
          | some linkerName =>
              cases hValue : context.findLinkerSymbol? linkerName with
              | none => simp [hName, hValue] at hResolve
              | some value =>
                  simp [hName, hValue] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  exact ⟨nameArg, linkerName, value, rfl, hName, hValue,
                    hToYul.symm⟩
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (nameArg :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

theorem loadimmutable_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "loadimmutable" args) ordered) :
    ∃ nameArg immutableName value,
      args = [nameArg] ∧
        Frontend.Expr.objectBuiltinNameArg? nameArg = some immutableName ∧
        context.findImmutableValue? immutableName = some value ∧
        ordered = .Lit value := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons nameArg rest =>
      cases rest with
      | nil =>
          cases hName : Frontend.Expr.objectBuiltinNameArg? nameArg with
          | none => simp [hName] at hResolve
          | some immutableName =>
              cases hValue : context.findImmutableValue? immutableName with
              | none => simp [hName, hValue] at hResolve
              | some value =>
                  simp [hName, hValue] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  exact ⟨nameArg, immutableName, value, rfl, hName, hValue,
                    hToYul.symm⟩
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (nameArg :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

theorem datacopy_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "datacopy" args) ordered) :
    ∃ target offset size orderedArgs op,
      args = [target, offset, size] ∧
        Frontend.Primitive.ofName? "codecopy" = some op ∧
        ordered = .Call (.inl op) orderedArgs ∧
        Nonempty
          (ExprListNormalized context [target, offset, size] orderedArgs) := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons target rest =>
      cases rest with
      | nil =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn? [target] context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul
      | cons offset rest =>
          cases rest with
          | nil =>
              cases hArgsResolve :
                  Frontend.Expr.List.resolveObjectBuiltinsIn?
                    [target, offset] context with
              | none => simp [hArgsResolve] at hResolve
              | some resolvedArgs =>
                  simp [hArgsResolve] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
          | cons size rest =>
              cases rest with
              | nil =>
                  cases hTarget :
                      target.resolveObjectBuiltinsIn? context with
                  | none => simp [hTarget] at hResolve
                  | some resolvedTarget =>
                      cases hOffset :
                          offset.resolveObjectBuiltinsIn? context with
                      | none => simp [hTarget, hOffset] at hResolve
                      | some resolvedOffset =>
                          cases hSize :
                              size.resolveObjectBuiltinsIn? context with
                          | none =>
                              simp [hTarget, hOffset, hSize] at hResolve
                          | some resolvedSize =>
                              simp [hTarget, hOffset, hSize] at hResolve
                              subst resolved
                              unfold Frontend.Expr.toYul? at hToYul
                              cases hOp :
                                  Frontend.Primitive.ofName? "codecopy" with
                              | none => simp [hOp] at hToYul
                              | some op =>
                                  cases hArgsYul :
                                      Frontend.Expr.List.toYul?
                                        [resolvedTarget, resolvedOffset,
                                          resolvedSize] with
                                  | none => simp [hOp, hArgsYul] at hToYul
                                  | some orderedArgs =>
                                      simp [hOp, hArgsYul] at hToYul
                                      refine
                                        ⟨target, offset, size, orderedArgs,
                                          op, rfl, by rfl, hToYul.symm, ⟨{
                                            resolved :=
                                              [resolvedTarget,
                                                resolvedOffset, resolvedSize]
                                            resolve := by
                                              simp [Frontend.Expr.List.resolveObjectBuiltinsIn?,
                                                hTarget, hOffset, hSize]
                                            toYul := hArgsYul }⟩⟩
              | cons extra tail =>
                  cases hArgsResolve :
                      Frontend.Expr.List.resolveObjectBuiltinsIn?
                        (target :: offset :: size :: extra :: tail) context with
                  | none => simp [hArgsResolve] at hResolve
                  | some resolvedArgs =>
                      simp [hArgsResolve] at hResolve
                      subst resolved
                      simp [Frontend.Expr.toYul?] at hToYul

theorem memoryguard_parts
    {context : Frontend.ObjectBuiltinContext}
    {args : List Frontend.Expr} {ordered : Frontend.AstExpr}
    (hNormalized :
      ExprNormalized context
        (.call .objectBuiltin "memoryguard" args) ordered) :
    ∃ value size,
      args = [value] ∧
        Nonempty (ExprNormalized context value (.Lit size)) ∧
        ordered = .Lit size := by
  rcases hNormalized with ⟨resolved, hResolve, hToYul⟩
  unfold Frontend.Expr.resolveObjectBuiltinsIn? at hResolve
  cases args with
  | nil =>
      simp [Frontend.Expr.List.resolveObjectBuiltinsIn?] at hResolve
      subst resolved
      simp [Frontend.Expr.toYul?] at hToYul
  | cons value rest =>
      cases rest with
      | nil =>
          cases hValue : value.resolveObjectBuiltinsIn? context with
          | none => simp [hValue] at hResolve
          | some resolvedValue =>
              cases resolvedValue with
              | lit size =>
                  simp [hValue] at hResolve
                  subst resolved
                  simp [Frontend.Expr.toYul?] at hToYul
                  have hValueNormalized :
                      ExprNormalized context value (.Lit size) :=
                    { resolved := .lit size
                      resolve := hValue
                      toYul := rfl }
                  exact
                    ⟨value, size, rfl,
                      ⟨hValueNormalized⟩,
                      hToYul.symm⟩
              | stringLit literal => simp [hValue] at hResolve
              | bytesLit bytes => simp [hValue] at hResolve
              | var name => simp [hValue] at hResolve
              | call kind callee callArgs => simp [hValue] at hResolve
      | cons extra tail =>
          cases hArgsResolve :
              Frontend.Expr.List.resolveObjectBuiltinsIn?
                (value :: extra :: tail) context with
          | none => simp [hArgsResolve] at hResolve
          | some resolvedArgs =>
              simp [hArgsResolve] at hResolve
              subst resolved
              simp [Frontend.Expr.toYul?] at hToYul

end ExprNormalized

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

theorem exprValuesRunForward_of_scoped_elaborated_datasize
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hBuiltins :
      ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "datasize" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 2) ((rawFuel + 2) + slack)
      rawContext (.functionCall "datasize" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "datasize") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.datasize_parts hNormalized with
    ⟨frontNameArg, dataName, size, hFrontArgs,
      hFrontName, hSize, rfl⟩
  rcases rawSingleObjectBuiltinNameArg_of_list_elaboration
      hArgs hFrontArgs hFrontName with
    ⟨rawNameArg, rfl, hRawName⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exprValuesRunForward_datasize_succ
      (rawFuel := rawFuel) (orderedFuel := rawFuel + slack + 1)
      hRawName (by
        rw [ObjectBuiltinContextsAgree.size?_eq hBuiltins]
        exact hSize))

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

theorem exprValuesRunForward_of_scoped_elaborated_dataoffset
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hBuiltins :
      ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "dataoffset" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 2) ((rawFuel + 2) + slack)
      rawContext (.functionCall "dataoffset" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "dataoffset") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.dataoffset_parts hNormalized with
    ⟨frontNameArg, dataName, offset, hFrontArgs,
      hFrontName, hOffset, rfl⟩
  rcases rawSingleObjectBuiltinNameArg_of_list_elaboration
      hArgs hFrontArgs hFrontName with
    ⟨rawNameArg, rfl, hRawName⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exprValuesRunForward_dataoffset_succ
      (rawFuel := rawFuel) (orderedFuel := rawFuel + slack + 1)
      hRawName (by
        rw [ObjectBuiltinContextsAgree.offset?_eq hBuiltins]
        exact hOffset))

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

theorem exprValuesRunForward_of_scoped_elaborated_linkersymbol
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hBuiltins :
      ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "linkersymbol" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 2) ((rawFuel + 2) + slack)
      rawContext (.functionCall "linkersymbol" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "linkersymbol") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.linkersymbol_parts hNormalized with
    ⟨frontNameArg, linkerName, value, hFrontArgs,
      hFrontName, hValue, rfl⟩
  rcases rawSingleObjectBuiltinNameArg_of_list_elaboration
      hArgs hFrontArgs hFrontName with
    ⟨rawNameArg, rfl, hRawName⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exprValuesRunForward_linkersymbol_succ
      (rawFuel := rawFuel) (orderedFuel := rawFuel + slack + 1)
      hRawName (by
        rw [ObjectBuiltinContextsAgree.findLinkerSymbol?_eq hBuiltins]
        exact hValue))

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

theorem exprValuesRunForward_of_scoped_elaborated_loadimmutable
    {slack rawFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hBuiltins :
      ObjectBuiltinContextsAgree rawContext.objectBuiltins builtinContext)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "loadimmutable" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (rawFuel + 2) ((rawFuel + 2) + slack)
      rawContext (.functionCall "loadimmutable" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "loadimmutable") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.loadimmutable_parts hNormalized with
    ⟨frontNameArg, immutableName, value, hFrontArgs,
      hFrontName, hValue, rfl⟩
  rcases rawSingleObjectBuiltinNameArg_of_list_elaboration
      hArgs hFrontArgs hFrontName with
    ⟨rawNameArg, rfl, hRawName⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exprValuesRunForward_loadimmutable_succ
      (rawFuel := rawFuel) (orderedFuel := rawFuel + slack + 1)
      hRawName (by
        rw [ObjectBuiltinContextsAgree.findImmutableValue?_eq hBuiltins]
        exact hValue))

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

theorem exprValuesRunForward_of_scoped_elaborated_datacopy_below
    {slack argsFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        argsFuel (slack + 1) builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "datacopy" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (argsFuel + 2) ((argsFuel + 2) + slack)
      rawContext (.functionCall "datacopy" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "datacopy") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.datacopy_parts hNormalized with
    ⟨target, offset, size, orderedArgs, op,
      hFrontArgs, hOp, rfl, ⟨hArgsNormalized⟩⟩
  rw [hFrontArgs] at hArgs
  have hArgsRun :=
    argsRunForward_reverse_of_scoped_elaboration_fuel_below
      hExpr hContext hArgs hArgsNormalized
      state
  have hRun :=
    exprValuesRunForward_datacopy_succ
      (rawFuel := argsFuel)
      (orderedFuel := argsFuel + (slack + 1))
      hOp hArgsRun
      (fun stateAfterArgs values =>
        primitiveRunForward_slack argsFuel (slack + 1)
          stateAfterArgs op values.reverse)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

theorem exprValuesRunForward_of_path_elaborated_datacopy_below
    {slack argsFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        argsFuel (slack + 1) builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "datacopy" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (argsFuel + 2) ((argsFuel + 2) + slack)
      rawContext (.functionCall "datacopy" rawArgs)
      ordered contract state := by
  rcases objectBuiltinCall_elaboration_parts
      (name := "datacopy") (by decide) (by decide) rfl hElab with
    ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
  rcases ExprNormalized.datacopy_parts hNormalized with
    ⟨target, offset, size, orderedArgs, op,
      hFrontArgs, hOp, rfl, ⟨hArgsNormalized⟩⟩
  rw [hFrontArgs] at hArgs
  have hArgsRun :=
    argsRunForward_reverse_of_path_elaboration_fuel_below
      hExpr hContext hPath hArgs hArgsNormalized state
  have hRun :=
    exprValuesRunForward_datacopy_succ
      (rawFuel := argsFuel)
      (orderedFuel := argsFuel + (slack + 1))
      hOp hArgsRun
      (fun stateAfterArgs values =>
        primitiveRunForward_slack argsFuel (slack + 1)
          stateAfterArgs op values.reverse)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

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

theorem exprValuesRunForward_of_scoped_elaborated_memoryguard_below
    {slack valueFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprElaborationRunForwardBelow
        (valueFuel + 1) (slack + 2) builtinContext contract)
    (hContext :
      CompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "memoryguard" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (valueFuel + 2) ((valueFuel + 2) + slack)
      rawContext (.functionCall "memoryguard" rawArgs)
      ordered contract state := by
  rcases memoryguard_elaboration_parts hElab with
    ⟨rawValue, frontValue, valueState, rfl, rfl, hValueElab, rfl⟩
  rcases ExprNormalized.memoryguard_parts hNormalized with
    ⟨normalizedValue, size, hFrontArgs, ⟨hValueNormalized⟩, rfl⟩
  rcases List.cons.inj hFrontArgs with ⟨hFrontValue, _⟩
  subst normalizedValue
  have hValueValues :=
    hExpr valueFuel (by omega) hContext (state := state)
      hValueElab hValueNormalized
  have hValueRun := exprRunForward_of_values hValueValues
  have hRun :=
    exprValuesRunForward_memoryguard_succ
      (rawFuel := valueFuel)
      (orderedFuel := valueFuel + slack + 1)
      hValueRun
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

theorem exprValuesRunForward_of_path_elaborated_memoryguard_below
    {slack valueFuel : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Expr} {ordered : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardBelow
        (valueFuel + 1) (slack + 2) builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "memoryguard" rawArgs)).run
        elabState = .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered) :
    ExprValuesRunForward (valueFuel + 2) ((valueFuel + 2) + slack)
      rawContext (.functionCall "memoryguard" rawArgs)
      ordered contract state := by
  rcases memoryguard_elaboration_parts hElab with
    ⟨rawValue, frontValue, valueState, rfl, rfl, hValueElab, rfl⟩
  rcases ExprNormalized.memoryguard_parts hNormalized with
    ⟨normalizedValue, size, hFrontArgs, ⟨hValueNormalized⟩, rfl⟩
  rcases List.cons.inj hFrontArgs with ⟨hFrontValue, _⟩
  subst normalizedValue
  have hValueValues :=
    hExpr valueFuel (by omega) hContext hPath (state := state)
      hValueElab hValueNormalized
  have hValueRun := exprRunForward_of_values hValueValues
  have hRun :=
    exprValuesRunForward_memoryguard_succ
      (rawFuel := valueFuel)
      (orderedFuel := valueFuel + slack + 1)
      hValueRun
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRun

/-- Generic successor expression constructor. Primitive, ordinary user-call,
and object-builtin cases are selected from the canonical Lean classifier;
unsupported dialect calls and expression-position `setimmutable` are rejected
by successful normalization. `clz` remains the one private generated-helper
interface to discharge. -/
theorem scopedExprElaborationRunForwardAt_succ
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprElaborationRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ScopedBlockElaborationRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    (hClz :
      ClzElaborationRunForwardAt
        (fuel + 1) slack builtinContext contract) :
    ScopedExprElaborationRunForwardAt
      (fuel + 1) slack builtinContext contract := by
  intro rawContext rawExpr front ordered elabState finalElabState state
    hContext hElab hNormalized
  cases rawExpr with
  | literal literal =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_of_elaborated_literal
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state)
          hElab hNormalized)
  | identifier name =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_of_elaborated_identifier
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state)
          hElab hNormalized)
  | functionCall name rawArgs =>
      by_cases hMemoryguard : name = "memoryguard"
      · subst name
        cases fuel with
        | zero =>
            exact
              exprValuesRunForward_objectBuiltinCall_one
                (orderedFuel := 1 + slack) (by decide) rfl
        | succ residual =>
            have hValueExpr :
                ScopedExprElaborationRunForwardBelow
                  (residual + 1) (slack + 2)
                  builtinContext contract := by
              intro childFuel hChild
              exact hExpr 2 childFuel (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (exprValuesRunForward_of_scoped_elaborated_memoryguard_below
                (slack := slack) (valueFuel := residual)
                hValueExpr hContext hElab hNormalized)
      · by_cases hClzName : name = "clz"
        · subst name
          exact hClz hContext hElab hNormalized
        · cases hClass : CallClass.classifyCall name with
          | primitive =>
              have hArgExpr :
                  ScopedExprElaborationRunForwardBelow
                    fuel slack builtinContext contract := by
                intro childFuel hChild
                exact hExpr 0 childFuel (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (exprValuesRunForward_of_scoped_elaborated_primitiveCall_below
                  (slack := slack) (argsFuel := fuel)
                  hArgExpr hContext hMemoryguard hClzName hClass
                  hElab hNormalized
                  (fun op _hOp stateAfterArgs values =>
                    primitiveRunForward_slack fuel slack
                      stateAfterArgs op values.reverse))
          | user =>
              cases fuel with
              | zero =>
                  exact
                    exprValuesRunForward_userCall_one
                      (orderedFuel := 1 + slack)
                      hClzName hClass
              | succ residual =>
                  have hRecursiveExpr :
                      ScopedExprElaborationRunForwardBelow
                        (residual + 2) slack builtinContext contract := by
                    simpa using hExpr 0
                  have hRecursiveBlock :
                      ScopedBlockElaborationRunForwardBelow
                        (residual + 2) slack builtinContext contract := by
                    simpa using hBlock
                  simpa [Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                    (exprValuesRunForward_of_scoped_elaborated_userCall_below
                      (slack := slack) (callFuel := residual)
                      hRecursiveExpr hRecursiveBlock hContext
                      hMemoryguard hClzName hClass hElab hNormalized)
          | objectBuiltin =>
              cases fuel with
              | zero =>
                  exact
                    exprValuesRunForward_objectBuiltinCall_one
                      (orderedFuel := 1 + slack)
                      hClzName hClass
              | succ residual =>
                  have hObjectName := classifyCall_objectBuiltin_mem hClass
                  simp [CallClass.objectBuiltins] at hObjectName
                  rcases hObjectName with
                    (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_datasize
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_dataoffset
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · have hArgExpr :
                        ScopedExprElaborationRunForwardBelow
                          residual (slack + 1)
                          builtinContext contract := by
                      intro childFuel hChild
                      exact hExpr 1 childFuel (by omega)
                    exact
                      exprValuesRunForward_of_scoped_elaborated_datacopy_below
                        (slack := slack) (argsFuel := residual)
                        hArgExpr hContext hElab hNormalized
                  · rcases objectBuiltinCall_elaboration_parts
                        hMemoryguard hClzName hClass hElab with
                      ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
                    exact False.elim
                      (ExprNormalized.setimmutable_call_false hNormalized)
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_loadimmutable
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_linkersymbol
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact False.elim (hMemoryguard rfl)
          | dialectBuiltin =>
              unfold Elab.Expr.elaborate at hElab
              simp [StateT.run_bind] at hElab
              cases hArgs :
                  (Elab.Expr.List.elaborate rawArgs).run elabState with
              | error err => simp [hArgs] at hElab
              | ok argsResult =>
                  rcases argsResult with ⟨frontArgs, argsState⟩
                  simp [hArgs, hClass] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  exact False.elim
                    (ExprNormalized.dialect_call_false hNormalized)

/-- Generic path-scoped successor expression constructor. Every accepted raw
expression class is covered using only lower source fuel, occurrence-local
elaboration paths, and path-aware lexical function bindings. -/
theorem scopedExprPathRunForwardAt_succ
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    (hClz :
      ClzPathRunForwardAt
        (fuel + 1) slack builtinContext contract) :
    ScopedExprPathRunForwardAt
      (fuel + 1) slack builtinContext contract := by
  intro rawContext rawExpr front ordered elabState finalElabState state
    hContext hPath hElab hNormalized
  cases rawExpr with
  | literal literal =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_of_elaborated_literal
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state)
          hElab hNormalized)
  | identifier name =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exprValuesRunForward_of_elaborated_identifier
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state)
          hElab hNormalized)
  | functionCall name rawArgs =>
      by_cases hMemoryguard : name = "memoryguard"
      · subst name
        cases fuel with
        | zero =>
            exact
              exprValuesRunForward_objectBuiltinCall_one
                (orderedFuel := 1 + slack) (by decide) rfl
        | succ residual =>
            have hValueExpr :
                ScopedExprPathRunForwardBelow
                  (residual + 1) (slack + 2)
                  builtinContext contract := by
              intro childFuel hChild
              exact hExpr 2 childFuel (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (exprValuesRunForward_of_path_elaborated_memoryguard_below
                (slack := slack) (valueFuel := residual)
                hValueExpr hContext hPath hElab hNormalized)
      · by_cases hClzName : name = "clz"
        · subst name
          exact hClz hContext hPath hElab hNormalized
        · cases hClass : CallClass.classifyCall name with
          | primitive =>
              have hArgExpr :
                  ScopedExprPathRunForwardBelow
                    fuel slack builtinContext contract := by
                intro childFuel hChild
                exact hExpr 0 childFuel (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (exprValuesRunForward_of_path_elaborated_primitiveCall_below
                  (slack := slack) (argsFuel := fuel)
                  hArgExpr hContext hPath hMemoryguard hClzName hClass
                  hElab hNormalized
                  (fun op _hOp stateAfterArgs values =>
                    primitiveRunForward_slack fuel slack
                      stateAfterArgs op values.reverse))
          | user =>
              cases fuel with
              | zero =>
                  exact
                    exprValuesRunForward_userCall_one
                      (orderedFuel := 1 + slack)
                      hClzName hClass
              | succ residual =>
                  have hRecursiveExpr :
                      ScopedExprPathRunForwardBelow
                        (residual + 2) slack builtinContext contract := by
                    simpa using hExpr 0
                  have hRecursiveBlock :
                      ScopedBlockPathRunForwardBelow
                        (residual + 2) slack builtinContext contract := by
                    simpa using hBlock
                  simpa [Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                    (exprValuesRunForward_of_path_elaborated_userCall_below
                      (slack := slack) (callFuel := residual)
                      hRecursiveExpr hRecursiveBlock hContext hPath
                      hMemoryguard hClzName hClass hElab hNormalized)
          | objectBuiltin =>
              cases fuel with
              | zero =>
                  exact
                    exprValuesRunForward_objectBuiltinCall_one
                      (orderedFuel := 1 + slack)
                      hClzName hClass
              | succ residual =>
                  have hObjectName := classifyCall_objectBuiltin_mem hClass
                  simp [CallClass.objectBuiltins] at hObjectName
                  rcases hObjectName with
                    (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_datasize
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_dataoffset
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · have hArgExpr :
                        ScopedExprPathRunForwardBelow
                          residual (slack + 1)
                          builtinContext contract := by
                      intro childFuel hChild
                      exact hExpr 1 childFuel (by omega)
                    exact
                      exprValuesRunForward_of_path_elaborated_datacopy_below
                        (slack := slack) (argsFuel := residual)
                        hArgExpr hContext hPath hElab hNormalized
                  · rcases objectBuiltinCall_elaboration_parts
                        hMemoryguard hClzName hClass hElab with
                      ⟨frontArgs, argsState, hArgs, rfl, rfl⟩
                    exact False.elim
                      (ExprNormalized.setimmutable_call_false hNormalized)
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_loadimmutable
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact
                      exprValuesRunForward_of_scoped_elaborated_linkersymbol
                        (slack := slack) (rawFuel := residual)
                        hContext.objectBuiltins hElab hNormalized
                  · exact False.elim (hMemoryguard rfl)
          | dialectBuiltin =>
              unfold Elab.Expr.elaborate at hElab
              simp [StateT.run_bind] at hElab
              cases hArgs :
                  (Elab.Expr.List.elaborate rawArgs).run elabState with
              | error err => simp [hArgs] at hElab
              | ok argsResult =>
                  rcases argsResult with ⟨frontArgs, argsState⟩
                  simp [hArgs, hClass] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  exact False.elim
                    (ExprNormalized.dialect_call_false hNormalized)

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

/-- Statement preservation inside one lexical block. Regular outcomes remain
exact; only abrupt outcomes may expose the administrative store restriction
introduced by an erased nested function declaration. -/
def ScopedStmtRunForward (entryStore : EvmYul.Yul.VarStore)
    (rawFuel orderedFuel : Nat)
    (context : Raw.SourceSemantics.Context)
    (rawStmt : Raw.Stmt) (orderedStmt : Frontend.AstStmt)
    (contract : Frontend.AstContract) (state : State) : Prop :=
  Simulation.Interaction.ForwardRel
    Yul.FunctionsInteractionPrimitive.Truncated
    (BlockSeqDoneRel entryStore)
    (Raw.SourceSemantics.exec rawFuel context rawStmt state)
    (Yul.InteractionSemantics.exec orderedFuel orderedStmt
      (some contract) state)

theorem scopedStmtRunForward_of_exact
    {entryStore : EvmYul.Yul.VarStore}
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {orderedStmt : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hExact :
      StmtRunForward rawFuel orderedFuel
        context rawStmt orderedStmt contract state) :
    ScopedStmtRunForward entryStore rawFuel orderedFuel
      context rawStmt orderedStmt contract state := by
  unfold StmtRunForward ScopedStmtRunForward at *
  apply Simulation.Interaction.ForwardRel.mono hExact
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ExceptRel.error rfl
  | ok rawState =>
      cases rawState with
      | Ok => exact Simulation.Interaction.ExceptRel.ok rfl
      | OutOfFuel => exact Simulation.Interaction.ExceptRel.ok (.inl rfl)
      | Checkpoint => exact Simulation.Interaction.ExceptRel.ok (.inl rfl)

theorem stmtRunForward_zero
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {orderedStmt : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State} :
    StmtRunForward 0 orderedFuel
      context rawStmt orderedStmt contract state := by
  unfold StmtRunForward
  rw [show Raw.SourceSemantics.exec 0 context rawStmt state =
      Raw.SourceSemantics.fail state .OutOfFuel by
    simp [Raw.SourceSemantics.exec]]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

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

/-- Primitive expression statements consume the shared expression simulation
and discard its values through the canonical empty destination list. -/
theorem stmtRunForward_expressionStatement_primitive_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {op : EvmYul.Operation .Yul}
    {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hNotSetimmutable : name ≠ "setimmutable")
    (hValues :
      ExprValuesRunForward rawFuel orderedFuel context
        (.functionCall name rawArgs) (.Call (.inl op) orderedArgs)
        contract state) :
    StmtRunForward (rawFuel + 1) orderedFuel context
      (.expressionStatement (.functionCall name rawArgs))
      (.ExprStmtCall (.Call (.inl op) orderedArgs)) contract state := by
  unfold StmtRunForward
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hNotSetimmutable]
  rw [Yul.InteractionSemantics.Exec.expr_primitive]
  unfold ExprValuesRunForward at hValues
  refine Simulation.Interaction.ForwardRel.bind_custom hValues ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      rcases result with ⟨stateAfterExpr, values⟩
      cases stateAfterExpr <;>
        exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_expressionStatement_call_one
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hNotSetimmutable : name ≠ "setimmutable") :
    StmtRunForward 1 orderedFuel context
      (.expressionStatement (.functionCall name rawArgs))
      ordered contract state := by
  unfold StmtRunForward
  rw [show 1 = 0 + 1 by omega]
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hNotSetimmutable, Raw.SourceSemantics.evalValues,
    Raw.SourceSemantics.fail]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

theorem stmtRunForward_expressionStatement_userCall_two
    {orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hNotSetimmutable : name ≠ "setimmutable")
    (hNotClz : name ≠ "clz")
    (hClass : CallClass.classifyCall name = .user) :
    StmtRunForward 2 orderedFuel context
      (.expressionStatement (.functionCall name rawArgs))
      ordered contract state := by
  unfold StmtRunForward
  rw [show 2 = 1 + 1 by omega]
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hNotSetimmutable]
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    0 context name rawArgs state hNotClz]
  simp only [hClass]
  rw [Raw.SourceSemantics.evalArgs_zero]
  unfold Raw.SourceSemantics.fail
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Yul.InteractionSemantics.Primitive.fail state .OutOfFuel :
            Open (State × List Frontend.Word))
          (fun result =>
            Raw.SourceSemantics.call 0 context result.2.reverse
              name result.1))
        (fun result => pure result.1))
      _
  rw [Simulation.Interaction.bind_assoc]
  rw [Yul.InteractionSemantics.Primitive.bind_fail]
  exact
    Simulation.Interaction.ForwardRel.truncated
      (by simp [Yul.FunctionsInteractionPrimitive.Truncated])

/-- The expression-statement constructor consumes the same generated-call
evidence with one additional unit of target argument fuel. Callee-body fuel,
lookup, return restoration, and value discard remain shared with value-position
calls. -/
theorem stmtRunForward_expressionStatement_userCall_succ
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawName : Name} {rawArgs : List Raw.Expr}
    {generated : Name} {orderedArgs : List Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun :
      GeneratedUserCallRun rawFuel (orderedFuel + 1) orderedFuel
        context rawName rawArgs generated orderedArgs contract state) :
    StmtRunForward (rawFuel + 3) (orderedFuel + 3)
      context (.expressionStatement (.functionCall rawName rawArgs))
      (.ExprStmtCall (.Call (.inr generated) orderedArgs))
      contract state := by
  have hNotSetimmutable : rawName ≠ "setimmutable" := by
    intro hName
    subst rawName
    have hClass := hRun.callClass
    simp [CallClass.classifyCall, CallClass.objectBuiltins,
      Frontend.Primitive.ofName?] at hClass
  unfold StmtRunForward
  rw [show rawFuel + 3 = (rawFuel + 2) + 1 by omega]
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp [hNotSetimmutable, hRun.notClz]
  rw [Raw.SourceSemantics.EvalValues.functionCall_succ_of_ne_clz
    (rawFuel + 1) context rawName rawArgs state hRun.notClz]
  simp only [hRun.callClass]
  rw [show orderedFuel + 3 = (orderedFuel + 1) + 2 by omega]
  rw [Yul.InteractionSemantics.Exec.expr_internal_succ]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Raw.SourceSemantics.evalArgs (rawFuel + 1) context
            rawArgs.reverse state)
          (fun argsResult =>
            Raw.SourceSemantics.call (rawFuel + 1) context
              argsResult.2.reverse rawName argsResult.1))
        (fun callResult => pure callResult.1))
      _
  rw [Simulation.Interaction.bind_assoc]
  have hArgsForward := hRun.argsForward
  unfold ArgsRunForward at hArgsForward
  refine
    Simulation.Interaction.ForwardRel.bind_custom hArgsForward ?_
  intro rawArgsDone orderedArgsDone hArgsDone
  unfold SameDoneRel at hArgsDone
  subst orderedArgsDone
  cases rawArgsDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok argsResult =>
      rcases argsResult with ⟨stateAfterArgs, reversedValues⟩
      have hCallForward :=
        generatedUserCallRun_call_succ
          (stateAfterArgs := stateAfterArgs)
          (reversedValues := reversedValues) hRun
      refine
        Simulation.Interaction.ForwardRel.bind_custom hCallForward ?_
      intro rawCallDone orderedCallDone hCallDone
      unfold SameDoneRel at hCallDone
      subst orderedCallDone
      cases rawCallDone with
      | error error => exact Simulation.Interaction.ForwardRel.done rfl
      | ok callResult =>
          rcases callResult with ⟨stateAfterCall, values⟩
          cases stateAfterCall <;>
            exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_expressionStatement_generatedClz
    {rawArgFuel orderedBase : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawArg : Raw.Expr} {generated : Name}
    {orderedArg : Frontend.AstExpr}
    {contract : Frontend.AstContract} {state : State}
    (hRun :
      GeneratedClzCallRun rawArgFuel (orderedBase + 2)
        (orderedBase + 2) context rawArg generated orderedArg
        contract state) :
    StmtRunForward (rawArgFuel + 2) (orderedBase + 4)
      context (.expressionStatement (.functionCall "clz" [rawArg]))
      (.ExprStmtCall (.Call (.inr generated) [orderedArg]))
      contract state := by
  unfold StmtRunForward
  rw [show rawArgFuel + 2 = (rawArgFuel + 1) + 1 by omega]
  rw [Raw.SourceSemantics.Exec.expressionStatement_succ]
  simp
  rw [Raw.SourceSemantics.EvalValues.clz_succ]
  change
    Simulation.Interaction.ForwardRel
      Yul.FunctionsInteractionPrimitive.Truncated SameDoneRel
      (Simulation.Interaction.bind
        (Simulation.Interaction.bind
          (Raw.SourceSemantics.eval rawArgFuel context rawArg state)
          (fun result =>
            match result.1 with
            | .Ok _ _ =>
                pure
                  (result.1,
                    [Elab.ClzHelperModel.reference result.2])
            | .OutOfFuel | .Checkpoint _ =>
                Raw.SourceSemantics.fail result.1 .OutOfFuel))
        (fun result => pure result.1))
      _
  rw [Simulation.Interaction.bind_assoc]
  rw [show orderedBase + 4 = (orderedBase + 2) + 2 by omega]
  rw [Yul.InteractionSemantics.Exec.expr_internal_succ]
  simp only [List.reverse_singleton]
  rw [orderedEvalArgs_single]
  simp only [Simulation.Interaction.bind_assoc]
  have hArg := hRun.argForward
  unfold ExprRunForward at hArg
  refine Simulation.Interaction.ForwardRel.bind_custom hArg ?_
  intro rawDone orderedDone hDone
  unfold SameDoneRel at hDone
  subst orderedDone
  cases rawDone with
  | error error => exact Simulation.Interaction.ForwardRel.done rfl
  | ok result =>
      rcases result with ⟨stateAfterArg, value⟩
      cases stateAfterArg with
      | OutOfFuel =>
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
      | Checkpoint jump =>
          exact
            Simulation.Interaction.ForwardRel.truncated
              (by simp [Yul.FunctionsInteractionPrimitive.Truncated])
      | Ok shared store =>
          simp only [Simulation.Interaction.instMonad,
            Simulation.Interaction.pure, Simulation.Interaction.bind,
            List.reverse_singleton]
          rw [Raw.ClzPreservation.clzHelperCall
            hRun.binding.namesDistinct hRun.binding.orderedLookup
            hRun.binding.bodyToYul shared store value
            (orderedBase + 2) hRun.bodyFuel]
          exact Simulation.Interaction.ForwardRel.done rfl

theorem stmtRunForward_of_path_elaborated_clz
    {rawArgFuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {context : Raw.SourceSemantics.Context}
    {rawArgs : List Raw.Expr} {front : Frontend.Expr}
    {ordered : Frontend.AstExpr}
    {elabState finalElabState : Elab.State}
    {contract : Frontend.AstContract} {state : State}
    (hExpr :
      ScopedExprPathRunForwardAt
        rawArgFuel slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        context elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Expr.elaborate (.functionCall "clz" rawArgs)).run elabState =
        .ok (front, finalElabState))
    (hNormalized : ExprNormalized builtinContext front ordered)
    (hArgTarget : 2 ≤ rawArgFuel + slack)
    (hHelperFuel :
      Raw.ClzPreservation.helperBodyFuel + 2 ≤
        rawArgFuel + slack) :
    StmtRunForward (rawArgFuel + 2) ((rawArgFuel + 2) + slack)
      context (.expressionStatement (.functionCall "clz" rawArgs))
      (.ExprStmtCall ordered) contract state := by
  rcases clz_elaboration_parts hElab with
    ⟨rawArg, frontArg, argState, generated, helperState,
      rfl, hArgElab, hEnsure, rfl, rfl⟩
  rcases ExprNormalized.user_call_parts hNormalized with
    ⟨orderedArgs, rfl, ⟨hArgsNormalized⟩⟩
  rcases ExprListNormalized.cons_parts hArgsNormalized with
    ⟨orderedArg, orderedTail, hOrderedArgs,
      ⟨hArgNormalized⟩, ⟨hTailNormalized⟩⟩
  have hTail : orderedTail = [] :=
    ExprListNormalized.nil_ordered hTailNormalized
  subst orderedTail
  subst orderedArgs
  have hArgExt :=
    Elab.Expr.elaborate_preserves_clzAllocation rawArg
      hArgElab hPath.entryValid
  have hEnsureExt :=
    Elab.ensureClzHelper_preserves_clzAllocation
      hEnsure hArgExt.after_valid
  have hArgPath :
      ClzCompilationPath contract elabState argState :=
    hPath.prefixPath hEnsureExt
  have hArgValues :=
    hExpr (state := state) hContext hArgPath hArgElab hArgNormalized
  have hArgRun := exprRunForward_of_values hArgValues
  rcases Elab.ensureClzHelper_allocated hEnsure hArgExt.after_valid with
    ⟨argName, returnName, hAllocated⟩
  rcases hPath.finalResolver hAllocated with ⟨binding⟩
  let orderedBase := rawArgFuel + slack - 2
  have hBase : orderedBase + 2 = rawArgFuel + slack := by
    dsimp [orderedBase]
    omega
  have hBodyFuel :
      Raw.ClzPreservation.stmtListFuel
          (Elab.clzHelperBody binding.argName binding.returnName) + 2 ≤
        orderedBase + 2 := by
    rw [Raw.ClzPreservation.helperBodyFuel_eq]
    dsimp [orderedBase]
    omega
  have hRun :
      GeneratedClzCallRun rawArgFuel (orderedBase + 2)
        (orderedBase + 2) context rawArg generated orderedArg
        contract state :=
    { binding := binding
      bodyFuel := hBodyFuel
      argForward := by simpa [hBase] using hArgRun }
  have hCall := stmtRunForward_expressionStatement_generatedClz hRun
  have hTargetEq :
      orderedBase + 4 = rawArgFuel + 2 + slack := by
    dsimp [orderedBase]
    omega
  rw [hTargetEq] at hCall
  exact hCall

/-- Every accepted ordinary call statement is derived from checked
elaboration and normalization. Generated user calls use the bundled occurrence
interface; primitive and `datacopy` statements consume the generic expression
simulation. Only `clz` and `setimmutable` remain separate frontend-owned
normalizations. -/
theorem scopedStmtRunForward_of_path_elaborated_callStatement_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {rawContext : Raw.SourceSemantics.Context}
    {name : Name} {rawArgs : List Raw.Expr}
    {elabState finalElabState : Elab.State}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {contract : Frontend.AstContract}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath :
      ClzCompilationPath contract elabState finalElabState)
    (hNotClz : name ≠ "clz")
    (hNotSetimmutable : name ≠ "setimmutable")
    (hElab :
      (Elab.Stmt.elaborate
        (.expressionStatement (.functionCall name rawArgs))).run
          elabState = .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 1) ((fuel + 1) + slack)
      rawContext (.expressionStatement (.functionCall name rawArgs))
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  cases hSupported :
      CallClass.supportedExpressionStatementCall? name with
  | false =>
      simp [hSupported] at hElab
      change
        (Except.error "unsupported Yul expression statement call" :
          Except String (Frontend.Stmt × Elab.State)) =
            .ok (front, finalElabState) at hElab
      cases hElab
  | true =>
      simp [hSupported, StateT.run_bind] at hElab
      cases hExprElab :
          (Elab.Expr.elaborate (.functionCall name rawArgs)).run
            elabState with
      | error err => simp [hExprElab] at hElab
      | ok exprResult =>
          rcases exprResult with ⟨frontExpr, exprState⟩
          simp [hExprElab] at hElab
          rcases hElab with ⟨rfl, rfl⟩
          have hNotMemoryguard : name ≠ "memoryguard" := by
            intro hName
            subst name
            have hRejected :
                CallClass.supportedExpressionStatementCall?
                    "memoryguard" = false := by
              rfl
            rw [hRejected] at hSupported
            cases hSupported
          cases hClass : CallClass.classifyCall name with
          | primitive =>
              rcases functionCall_elaboration_kind_parts
                  hNotMemoryguard hNotClz hClass hExprElab with
                ⟨callee, frontArgs, rfl⟩
              rcases StmtNormalized.exprStmt_call_parts_of_not_setimmutable
                  (Or.inl (by intro hKind; cases hKind)) hNormalized with
                ⟨orderedExpr, rfl, ⟨hExprNormalized⟩⟩
              rcases ExprNormalized.primitive_call_parts hExprNormalized with
                ⟨op, orderedArgs, hOp, rfl, hArgsNormalized⟩
              have hValues :=
                hExpr 1 fuel (by omega) (state := state)
                  hContext hPath hExprElab hExprNormalized
              apply scopedStmtRunForward_of_exact
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using
                  (stmtRunForward_expressionStatement_primitive_succ
                    hNotSetimmutable hValues)
          | user =>
              rcases functionCall_elaboration_kind_parts
                  hNotMemoryguard hNotClz hClass hExprElab with
                ⟨generated, frontArgs, rfl⟩
              rcases StmtNormalized.exprStmt_call_parts_of_not_setimmutable
                  (Or.inl (by intro hKind; cases hKind)) hNormalized with
                ⟨orderedExpr, rfl, ⟨hExprNormalized⟩⟩
              cases fuel with
              | zero =>
                  exact scopedStmtRunForward_of_exact
                    (stmtRunForward_expressionStatement_call_one
                      (orderedFuel := 1 + slack)
                      hNotSetimmutable)
              | succ predecessor =>
                  cases predecessor with
                  | zero =>
                      exact scopedStmtRunForward_of_exact
                        (stmtRunForward_expressionStatement_userCall_two
                          (orderedFuel := 2 + slack)
                          hNotSetimmutable hNotClz hClass)
                  | succ callFuel =>
                      have hArgsExpr :
                          ScopedExprPathRunForwardBelow
                            (callFuel + 2) (slack + 1)
                            builtinContext contract := by
                        intro childFuel hChild
                        exact hExpr 1 childFuel (by omega)
                      have hBodyBlock :
                          ScopedBlockPathRunForwardBelow
                            (callFuel + 2) slack
                            builtinContext contract := by
                        intro childFuel hChild
                        exact hBlock childFuel (by omega)
                      rcases generatedUserCallRun_of_path_elaboration_below
                          hArgsExpr hBodyBlock hContext hPath
                          hNotMemoryguard hNotClz hClass
                          hExprElab hExprNormalized with
                        ⟨resolved, orderedArgs, hOrdered, ⟨hRun⟩⟩
                      cases hOrdered
                      apply scopedStmtRunForward_of_exact
                      simpa [Nat.add_assoc, Nat.add_comm,
                        Nat.add_left_comm] using
                          (stmtRunForward_expressionStatement_userCall_succ
                            hRun)
          | objectBuiltin =>
              have hObject :
                  name = "datacopy" ∨ name = "setimmutable" := by
                unfold CallClass.supportedExpressionStatementCall?
                  at hSupported
                simp [hClass] at hSupported
                exact hSupported
              rcases hObject with hDatacopy | hSetimmutable
              · subst name
                rcases objectBuiltinCall_elaboration_parts
                    hNotMemoryguard hNotClz hClass hExprElab with
                  ⟨frontArgs, argsState, hArgsElab, hFront, hFinal⟩
                subst frontExpr
                subst exprState
                rcases
                    StmtNormalized.exprStmt_call_parts_of_not_setimmutable
                      (Or.inr (by decide)) hNormalized with
                  ⟨orderedExpr, rfl, ⟨hExprNormalized⟩⟩
                rcases ExprNormalized.datacopy_parts hExprNormalized with
                  ⟨target, offset, size, orderedArgs, op,
                    hArgs, hOp, rfl, hArgsNormalized⟩
                have hValues :=
                  hExpr 1 fuel (by omega) (state := state)
                    hContext hPath hExprElab hExprNormalized
                apply scopedStmtRunForward_of_exact
                simpa [Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using
                    (stmtRunForward_expressionStatement_primitive_succ
                      (by decide) hValues)
              · exact False.elim (hNotSetimmutable hSetimmutable)
          | dialectBuiltin =>
              unfold CallClass.supportedExpressionStatementCall?
                at hSupported
              simp [hClass] at hSupported

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

/-- Erased nested function declarations are exact on regular states. On an
abrupt block entry, their administrative empty block may apply the enclosing
entry-store restriction early. -/
theorem scopedStmtRunForward_functionDefinition_stub_succ
    {rawFuel orderedFuel : Nat}
    {entryStore : EvmYul.Yul.VarStore}
    {context : Raw.SourceSemantics.Context}
    {name : Name} {params returns : List Name} {body : List Raw.Stmt}
    {contract : Frontend.AstContract} {state : State}
    (hCompatible : BlockEntryCompatible entryStore state) :
    ScopedStmtRunForward entryStore (rawFuel + 1) (orderedFuel + 2)
      context (.functionDefinition name params returns body)
      (.Block []) contract state := by
  cases state with
  | Ok shared store =>
      exact scopedStmtRunForward_of_exact
        stmtRunForward_functionDefinition_stub_succ
  | OutOfFuel =>
      unfold ScopedStmtRunForward
      rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
      rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
      rw [Yul.InteractionSemantics.Exec.block_succ]
      rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
      exact
        Simulation.Interaction.ForwardRel.done
          (Simulation.Interaction.ExceptRel.ok (Or.inl rfl))
  | Checkpoint jump =>
      unfold ScopedStmtRunForward
      rw [Raw.SourceSemantics.Exec.functionDefinition_succ]
      rw [show orderedFuel + 2 = (orderedFuel + 1) + 1 by omega]
      rw [Yul.InteractionSemantics.Exec.block_succ]
      rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
      rw [← hCompatible]
      cases jump <;>
        exact
          Simulation.Interaction.ForwardRel.done
            (Simulation.Interaction.ExceptRel.ok (Or.inr rfl))

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

/-- One checked statement occurrence under its exact frontend state path. This
is the statement component consumed by the generic recursive list theorem. -/
def ScopedStmtPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {front : Frontend.Stmt}
    {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State},
    BlockEntryCompatible entryStore state →
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      ClzCompilationPath contract elabState finalElabState →
      (Elab.Stmt.elaborate rawStmt).run elabState =
          .ok (front, finalElabState) →
      StmtNormalized builtinContext front ordered →
      ScopedStmtRunForward entryStore rawFuel (rawFuel + slack)
        rawContext rawStmt ordered contract state

/-- The four statement families with genuinely distinct control/call
semantics. The generic statement classifier handles all remaining constructors
directly and consumes one bundled provider for these cases. -/
inductive StmtNeedsSpecialPreservation : Raw.Stmt → Prop where
  | expressionStatement (expr : Raw.Expr) :
      StmtNeedsSpecialPreservation (.expressionStatement expr)
  | functionDefinition (name : Name) (params returns : List Name)
      (body : List Raw.Stmt) :
      StmtNeedsSpecialPreservation
        (.functionDefinition name params returns body)
  | switch (scrutinee : Raw.Expr)
      (cases : List (Raw.SwitchCaseValue × List Raw.Stmt))
      (default : List Raw.Stmt) :
      StmtNeedsSpecialPreservation (.switch scrutinee cases default)
  | forLoop (pre : List Raw.Stmt) (condition : Raw.Expr)
      (post body : List Raw.Stmt) :
      StmtNeedsSpecialPreservation (.forLoop pre condition post body)

def ScopedStmtSpecialRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {front : Frontend.Stmt}
    {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State},
    StmtNeedsSpecialPreservation rawStmt →
      BlockEntryCompatible entryStore state →
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      ClzCompilationPath contract elabState finalElabState →
      (Elab.Stmt.elaborate rawStmt).run elabState =
          .ok (front, finalElabState) →
      StmtNormalized builtinContext front ordered →
      ScopedStmtRunForward entryStore rawFuel (rawFuel + slack)
        rawContext rawStmt ordered contract state

/-- Whole statement-list preservation under one enclosing lexical-block entry
store. Recursive tails start in regular states, so the same entry store remains
compatible without weakening regular outcome equality. -/
def ScopedSeqPathRunForwardAt
    (rawFuel slack : Nat)
    (builtinContext : Frontend.ObjectBuiltinContext)
    (contract : Frontend.AstContract) : Prop :=
  ∀ {rawContext : Raw.SourceSemantics.Context}
    {rawCode : List Raw.Stmt} {front : List Frontend.Stmt}
    {ordered : List Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State},
    BlockEntryCompatible entryStore state →
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes →
      ClzCompilationPath contract elabState finalElabState →
      (Elab.Stmt.List.elaborate rawCode).run elabState =
          .ok (front, finalElabState) →
      StmtListNormalized builtinContext front ordered →
      ScopedSeqRunForward entryStore rawFuel (rawFuel + slack)
        rawContext rawCode ordered contract state

/-- Build the pointwise switch-case interface from the actual checked case-list
elaboration path. Each case body is discharged by the generic recursive block
theorem at the same source fuel. -/
theorem switchCaseListRunForward_of_path_elaboration_below
    {bound fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hFuel : fuel < bound)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        bound slack builtinContext contract) :
    ∀ {rawContext : Raw.SourceSemantics.Context}
      {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
      {frontCases :
        List (Frontend.SwitchCaseValue × List Frontend.Stmt)}
      {orderedCases : List (Frontend.Word × List Frontend.AstStmt)}
      {elabState finalElabState : Elab.State},
      PathCompiledContext builtinContext contract
          rawContext elabState.functionScopes →
        ClzCompilationPath contract elabState finalElabState →
        (Elab.Stmt.CaseList.elaborate rawCases).run elabState =
          .ok (frontCases, finalElabState) →
        CaseListNormalized builtinContext frontCases orderedCases →
        SwitchCaseListRunForward fuel (fuel + slack)
          rawContext contract rawCases orderedCases := by
  intro rawContext rawCases
  induction rawCases with
  | nil =>
      intro frontCases orderedCases elabState finalElabState
        hContext hPath hElab hNormalized
      simp [Elab.Stmt.CaseList.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := CaseListNormalized.nil_ordered hNormalized
      subst orderedCases
      exact .nil
  | cons rawCase rawRest ih =>
      rcases rawCase with ⟨rawValue, rawBody⟩
      intro frontCases orderedCases elabState finalElabState
        hContext hPath hElab hNormalized
      unfold Elab.Stmt.CaseList.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hValue : Elab.SwitchCaseValue.elaborate rawValue with
      | error err =>
          simp [hValue] at hElab
          unfold Elab.throw at hElab
          cases hElab
      | ok frontValue =>
          simp [hValue] at hElab
          cases hBody :
              (Elab.Stmt.List.elaborateBlock rawBody true).run elabState with
          | error err => simp [hBody] at hElab
          | ok bodyResult =>
              rcases bodyResult with ⟨frontBody, bodyState⟩
              simp [hBody] at hElab
              cases hRest :
                  (Elab.Stmt.CaseList.elaborate rawRest).run bodyState with
              | error err => simp [hRest] at hElab
              | ok restResult =>
                  rcases restResult with ⟨frontRest, restState⟩
                  simp [hRest] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  rcases CaseListNormalized.cons_parts hNormalized with
                    ⟨orderedValue, orderedBody, orderedRest, rfl,
                      hOrderedValue, ⟨hBodyNormalized⟩,
                      ⟨hRestNormalized⟩⟩
                  have hBodyExt :=
                    Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                      rawBody true hBody hPath.entryValid
                  have hRestExt :=
                    Elab.Stmt.CaseList.elaborate_preserves_clzAllocation
                      rawRest hRest hBodyExt.after_valid
                  have hBodyPath :
                      ClzCompilationPath contract elabState bodyState :=
                    hPath.prefixPath hRestExt
                  have hRestPath :
                      ClzCompilationPath contract bodyState restState :=
                    hPath.suffixPath hBodyExt
                  have hBodyScopes :
                      bodyState.functionScopes =
                        elabState.functionScopes :=
                    Elab.Stmt.List.elaborateBlock_preserves_functionScopes
                      rawBody true hBody
                  have hRestContext :
                      PathCompiledContext builtinContext contract
                        rawContext bodyState.functionScopes := by
                    simpa [hBodyScopes] using hContext
                  have hBodyRun :
                      ∀ state,
                        BlockCodeRunForward fuel (fuel + slack)
                          rawContext rawBody orderedBody contract state := by
                    intro state
                    exact
                      hBlock fuel hFuel (state := state)
                        hContext hBodyPath hBody hBodyNormalized
                  exact
                    .cons
                      (switchCaseValue_elaboration_word hValue hOrderedValue)
                      hBodyRun
                      (ih hRestContext hRestPath hRest hRestNormalized)

theorem scopedStmtRunForward_switch_of_path_below
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ScopedExprPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    (hBlock :
      ScopedBlockPathRunForwardBelow
        (fuel + 1) slack builtinContext contract)
    {rawContext : Raw.SourceSemantics.Context}
    {rawCondition : Raw.Expr}
    {rawCases : List (Raw.SwitchCaseValue × List Raw.Stmt)}
    {rawDefault : List Raw.Stmt}
    {front : Frontend.Stmt} {ordered : Frontend.AstStmt}
    {elabState finalElabState : Elab.State}
    {entryStore : EvmYul.Yul.VarStore} {state : State}
    (hContext :
      PathCompiledContext builtinContext contract
        rawContext elabState.functionScopes)
    (hPath : ClzCompilationPath contract elabState finalElabState)
    (hElab :
      (Elab.Stmt.elaborate
        (.switch rawCondition rawCases rawDefault)).run elabState =
          .ok (front, finalElabState))
    (hNormalized : StmtNormalized builtinContext front ordered) :
    ScopedStmtRunForward entryStore (fuel + 1) (fuel + 1 + slack)
      rawContext (.switch rawCondition rawCases rawDefault)
      ordered contract state := by
  unfold Elab.Stmt.elaborate at hElab
  simp [StateT.run_bind] at hElab
  cases hCondition :
      (Elab.Expr.elaborate rawCondition).run elabState with
  | error err => simp [hCondition] at hElab
  | ok conditionResult =>
      rcases conditionResult with ⟨frontCondition, conditionState⟩
      simp [hCondition] at hElab
      cases hCases :
          (Elab.Stmt.CaseList.elaborate rawCases).run conditionState with
      | error err => simp [hCases] at hElab
      | ok casesResult =>
          rcases casesResult with ⟨frontCases, casesState⟩
          simp [hCases] at hElab
          cases hDefault :
              (Elab.Stmt.List.elaborateBlock rawDefault true).run
                casesState with
          | error err => simp [hDefault] at hElab
          | ok defaultResult =>
              rcases defaultResult with ⟨frontDefault, defaultState⟩
              simp [hDefault] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases StmtNormalized.switch_parts hNormalized with
                ⟨orderedCondition, orderedCases, orderedDefault, rfl,
                  ⟨hConditionNormalized⟩, ⟨hCasesNormalized⟩,
                  ⟨hDefaultNormalized⟩⟩
              have hConditionExt :=
                Elab.Expr.elaborate_preserves_clzAllocation rawCondition
                  hCondition hPath.entryValid
              have hCasesExt :=
                Elab.Stmt.CaseList.elaborate_preserves_clzAllocation
                  rawCases hCases hConditionExt.after_valid
              have hDefaultExt :=
                Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                  rawDefault true hDefault hCasesExt.after_valid
              have hConditionPath :
                  ClzCompilationPath contract elabState conditionState :=
                hPath.prefixPath
                  (Elab.ClzAllocationExtends.trans hCasesExt hDefaultExt)
              have hCasesPath :
                  ClzCompilationPath contract conditionState casesState :=
                (hPath.suffixPath hConditionExt).prefixPath hDefaultExt
              have hDefaultPath :
                  ClzCompilationPath contract casesState defaultState :=
                hPath.suffixPath
                  (Elab.ClzAllocationExtends.trans hConditionExt hCasesExt)
              have hConditionScopes :
                  conditionState.functionScopes =
                    elabState.functionScopes :=
                Elab.Expr.elaborate_preserves_functionScopes
                  rawCondition hCondition
              have hCasesScopes :
                  casesState.functionScopes =
                    conditionState.functionScopes :=
                Elab.Stmt.CaseList.elaborate_preserves_functionScopes
                  rawCases hCases
              have hCasesContext :
                  PathCompiledContext builtinContext contract
                    rawContext conditionState.functionScopes := by
                simpa [hConditionScopes] using hContext
              have hDefaultContext :
                  PathCompiledContext builtinContext contract
                    rawContext casesState.functionScopes := by
                simpa [hCasesScopes] using hCasesContext
              have hConditionRun :=
                hExpr fuel (by omega) (state := state)
                  hContext hConditionPath hCondition hConditionNormalized
              have hCasesRun :=
                switchCaseListRunForward_of_path_elaboration_below
                  (fuel := fuel) (slack := slack) (by omega) hBlock
                  hCasesContext hCasesPath hCases hCasesNormalized
              have hDefaultRun :
                  ∀ stateAfterCondition,
                    BlockCodeRunForward fuel (fuel + slack)
                      rawContext rawDefault orderedDefault contract
                      stateAfterCondition := by
                intro stateAfterCondition
                exact
                  hBlock fuel (by omega) (state := stateAfterCondition)
                    hDefaultContext hDefaultPath hDefault hDefaultNormalized
              apply scopedStmtRunForward_of_exact
              have hSwitch :=
                stmtRunForward_switch_succ
                  (rawFuel := fuel) (orderedFuel := fuel + slack)
                  (context := rawContext) (contract := contract)
                  (state := state)
                  (exprRunForward_of_values hConditionRun)
                  (SwitchCaseListRunForward.select hCasesRun hDefaultRun)
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hSwitch

theorem scopedStmtPathRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedStmtPathRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawStmt front ordered elabState finalElabState
    entryStore state hCompatible hContext hPath hElab hNormalized
  exact scopedStmtRunForward_of_exact stmtRunForward_zero

/-- Generic checked statement classifier. Ordinary structural statements are
proved here from occurrence-local expression/block paths; only the four
semantically distinct call/control families are delegated to one bundled
provider. -/
theorem scopedStmtPathRunForwardAt_succ_of_special
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hExpr :
      ∀ extra,
        ScopedExprPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hBlock :
      ∀ extra,
        ScopedBlockPathRunForwardBelow
          (fuel + 1) (slack + extra) builtinContext contract)
    (hSpecial :
      ScopedStmtSpecialRunForwardAt
        (fuel + 1) slack builtinContext contract) :
    ScopedStmtPathRunForwardAt
      (fuel + 1) slack builtinContext contract := by
  intro rawContext rawStmt front ordered elabState finalElabState
    entryStore state hCompatible hContext hPath hElab hNormalized
  cases rawStmt with
  | block rawBody =>
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
          have hBodyRun :=
            hBlock 1 fuel (by omega) (state := state)
              hContext hPath hBody hBodyNormalized
          apply scopedStmtRunForward_of_exact
          simpa [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
              (stmtRunForward_block_succ hBodyRun)
  | variableDeclaration names value? =>
      cases value? with
      | none =>
          have hRun :=
            stmtRunForward_of_elaborated_variableDeclaration_none
              (rawFuel := fuel) (orderedFuel := fuel + slack)
              (rawContext := rawContext) (contract := contract)
              (state := state) hElab hNormalized
          exact scopedStmtRunForward_of_exact
            (by simpa [Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hRun)
      | some rawValue =>
          unfold Elab.Stmt.elaborate at hElab
          simp at hElab
          cases hValue :
              (Elab.Expr.elaborate rawValue).run elabState with
          | error err => simp [hValue] at hElab
          | ok valueResult =>
              rcases valueResult with ⟨frontValue, valueState⟩
              simp [hValue] at hElab
              cases hDeclare :
                  (Elab.declareIdentifiers names "variable").run
                    valueState with
              | error err => simp [hDeclare] at hElab
              | ok declareResult =>
                  rcases declareResult with ⟨_, declaredState⟩
                  simp [hDeclare] at hElab
                  rcases hElab with ⟨rfl, rfl⟩
                  rcases StmtNormalized.let_some_parts hNormalized with
                    ⟨orderedValue, rfl, ⟨hValueNormalized⟩⟩
                  have hValueExt :=
                    Elab.Expr.elaborate_preserves_clzAllocation rawValue
                      hValue hPath.entryValid
                  have hDeclareExt :=
                    Elab.declareIdentifiers_preserves_clzAllocation
                      names "variable" hDeclare hValueExt.after_valid
                  have hValuePath :
                      ClzCompilationPath contract elabState valueState :=
                    hPath.prefixPath hDeclareExt
                  have hValueRun :=
                    hExpr 0 fuel (by omega) (state := state)
                      hContext hValuePath hValue hValueNormalized
                  apply scopedStmtRunForward_of_exact
                  simpa [Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm] using
                      (stmtRunForward_variableDeclaration_some_succ
                        hValueRun)
  | assignment names rawValue =>
      unfold Elab.Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hVisible :
          (Elab.requireIdentifiersVisible names "assignment").run
            elabState with
      | error err => simp [hVisible] at hElab
      | ok visibleResult =>
          rcases visibleResult with ⟨_, visibleState⟩
          simp [hVisible] at hElab
          cases hValue :
              (Elab.Expr.elaborate rawValue).run visibleState with
          | error err => simp [hValue] at hElab
          | ok valueResult =>
              rcases valueResult with ⟨frontValue, valueState⟩
              simp [hValue] at hElab
              rcases hElab with ⟨rfl, rfl⟩
              rcases StmtNormalized.assign_parts hNormalized with
                ⟨orderedValue, rfl, ⟨hValueNormalized⟩⟩
              have hVisibleExt :=
                Elab.requireIdentifiersVisible_preserves_clzAllocation
                  names "assignment" hVisible hPath.entryValid
              have hValuePath :
                  ClzCompilationPath contract visibleState valueState :=
                hPath.suffixPath hVisibleExt
              have hVisibleScopes :
                  visibleState.functionScopes =
                    elabState.functionScopes :=
                Elab.requireIdentifiersVisible_preserves_functionScopes
                  names "assignment" hVisible
              have hValueContext :
                  PathCompiledContext builtinContext contract
                    rawContext visibleState.functionScopes := by
                simpa [hVisibleScopes] using hContext
              have hValueRun :=
                hExpr 0 fuel (by omega) (state := state)
                  hValueContext hValuePath hValue hValueNormalized
              apply scopedStmtRunForward_of_exact
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using
                  (stmtRunForward_assignment_succ hValueRun)
  | expressionStatement expr =>
      exact hSpecial (.expressionStatement expr) hCompatible hContext
        hPath hElab hNormalized
  | functionDefinition name params returns body =>
      exact hSpecial (.functionDefinition name params returns body)
        hCompatible hContext hPath hElab hNormalized
  | switch scrutinee cases default =>
      exact hSpecial (.switch scrutinee cases default)
        hCompatible hContext hPath hElab hNormalized
  | forLoop pre condition post body =>
      exact hSpecial (.forLoop pre condition post body)
        hCompatible hContext hPath hElab hNormalized
  | ifThen rawCondition rawBody =>
      unfold Elab.Stmt.elaborate at hElab
      simp [StateT.run_bind] at hElab
      cases hCondition :
          (Elab.Expr.elaborate rawCondition).run elabState with
      | error err => simp [hCondition] at hElab
      | ok conditionResult =>
          rcases conditionResult with
            ⟨frontCondition, conditionState⟩
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
              have hConditionExt :=
                Elab.Expr.elaborate_preserves_clzAllocation rawCondition
                  hCondition hPath.entryValid
              have hBodyExt :=
                Elab.Stmt.List.elaborateBlock_preserves_clzAllocation
                  rawBody true hBody hConditionExt.after_valid
              have hConditionPath :
                  ClzCompilationPath contract
                    elabState conditionState :=
                hPath.prefixPath hBodyExt
              have hBodyPath :
                  ClzCompilationPath contract
                    conditionState bodyState :=
                hPath.suffixPath hConditionExt
              have hConditionScopes :
                  conditionState.functionScopes =
                    elabState.functionScopes :=
                Elab.Expr.elaborate_preserves_functionScopes
                  rawCondition hCondition
              have hBodyContext :
                  PathCompiledContext builtinContext contract
                    rawContext conditionState.functionScopes := by
                simpa [hConditionScopes] using hContext
              have hConditionRun :=
                hExpr 0 fuel (by omega) (state := state)
                  hContext hConditionPath
                  hCondition hConditionNormalized
              apply scopedStmtRunForward_of_exact
              have hIf :=
                stmtRunForward_ifThen_succ
                  (rawFuel := fuel) (orderedFuel := fuel + slack)
                  (context := rawContext) (contract := contract)
                  (state := state)
                  (exprRunForward_of_values hConditionRun)
                  (fun stateAfterCondition value _hTruthy =>
                    hBlock 0 fuel (by omega)
                      (state := stateAfterCondition)
                      hBodyContext hBodyPath hBody hBodyNormalized)
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hIf
  | «break» =>
      apply scopedStmtRunForward_of_exact
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (stmtRunForward_of_elaborated_break
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (rawContext := rawContext) (contract := contract)
          (state := state) hElab hNormalized)
  | «continue» =>
      apply scopedStmtRunForward_of_exact
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (stmtRunForward_of_elaborated_continue
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (rawContext := rawContext) (contract := contract)
          (state := state) hElab hNormalized)
  | «leave» =>
      apply scopedStmtRunForward_of_exact
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (stmtRunForward_of_elaborated_leave
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (rawContext := rawContext) (contract := contract)
          (state := state) hElab hNormalized)

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
      cases rawState with
      | Ok => exact Simulation.Interaction.ExceptRel.ok rfl
      | OutOfFuel => exact Simulation.Interaction.ExceptRel.ok (.inl rfl)
      | Checkpoint => exact Simulation.Interaction.ExceptRel.ok (.inl rfl)

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

/-- Generic block-scoped list constructor. The strengthened done relation
forces exact agreement whenever the tail is entered. -/
theorem scopedSeqRunForward_cons
    {entryStore : EvmYul.Yul.VarStore}
    {rawFuel orderedFuel : Nat}
    {context : Raw.SourceSemantics.Context}
    {rawStmt : Raw.Stmt} {rawRest : List Raw.Stmt}
    {orderedStmt : Frontend.AstStmt}
    {orderedRest : List Frontend.AstStmt}
    {contract : Frontend.AstContract} {state : State}
    (hHead :
      ScopedStmtRunForward entryStore rawFuel orderedFuel
        context rawStmt orderedStmt contract state)
    (hTail :
      ∀ shared vars,
        ScopedSeqRunForward entryStore rawFuel orderedFuel
          context rawRest orderedRest contract (.Ok shared vars)) :
    ScopedSeqRunForward entryStore (rawFuel + 1) (orderedFuel + 1)
      context (rawStmt :: rawRest) (orderedStmt :: orderedRest)
      contract state := by
  unfold ScopedSeqRunForward ScopedStmtRunForward at *
  rw [Raw.SourceSemantics.ExecSeq.cons_succ]
  rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
  refine Simulation.Interaction.ForwardRel.bind_custom hHead ?_
  intro rawDone orderedDone hDone
  cases hDone with
  | error hError =>
      subst_vars
      exact
        Simulation.Interaction.ForwardRel.done
          (Simulation.Interaction.ExceptRel.error rfl)
  | @ok rawState orderedState hState =>
      cases rawState with
      | Ok shared vars =>
          subst orderedState
          exact hTail shared vars
      | OutOfFuel =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact
                Simulation.Interaction.ForwardRel.done
                  (Simulation.Interaction.ExceptRel.ok (Or.inl rfl))
          | inr hRestricted =>
              subst orderedState
              exact
                Simulation.Interaction.ForwardRel.done
                  (Simulation.Interaction.ExceptRel.ok (Or.inr rfl))
      | Checkpoint jump =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact
                Simulation.Interaction.ForwardRel.done
                  (Simulation.Interaction.ExceptRel.ok (Or.inl rfl))
          | inr hRestricted =>
              subst orderedState
              cases jump <;>
                exact
                  Simulation.Interaction.ForwardRel.done
                    (Simulation.Interaction.ExceptRel.ok (Or.inr rfl))

theorem scopedSeqPathRunForwardAt_zero
    {slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract} :
    ScopedSeqPathRunForwardAt 0 slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState
    entryStore state hCompatible hContext hPath hElab hNormalized
  exact scopedSeqRunForward_of_exact seqRunForward_zero

/-- Fuel-recursive statement-list theorem. It splits the actual checked
elaboration path at the head occurrence, carries the same lexical context into
the tail, and uses no generated-name or semantic replay premise. -/
theorem scopedSeqPathRunForwardAt_succ
    {fuel slack : Nat}
    {builtinContext : Frontend.ObjectBuiltinContext}
    {contract : Frontend.AstContract}
    (hStmt :
      ScopedStmtPathRunForwardAt fuel slack builtinContext contract)
    (hSeq :
      ScopedSeqPathRunForwardAt fuel slack builtinContext contract) :
    ScopedSeqPathRunForwardAt (fuel + 1) slack builtinContext contract := by
  intro rawContext rawCode front ordered elabState finalElabState
    entryStore state hCompatible hContext hPath hElab hNormalized
  cases rawCode with
  | nil =>
      simp [Elab.Stmt.List.elaborate] at hElab
      rcases hElab with ⟨rfl, rfl⟩
      have hOrdered := StmtListNormalized.nil_ordered hNormalized
      subst ordered
      apply scopedSeqRunForward_of_exact
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (seqRunForward_nil_succ
          (rawFuel := fuel) (orderedFuel := fuel + slack)
          (context := rawContext) (contract := contract) (state := state))
  | cons rawHead rawTail =>
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
              have hHeadExt :=
                Elab.Stmt.elaborate_preserves_clzAllocation rawHead
                  hHead hPath.entryValid
              have hTailExt :=
                Elab.Stmt.List.elaborate_preserves_clzAllocation rawTail
                  hTail hHeadExt.after_valid
              have hHeadPath :
                  ClzCompilationPath contract elabState headElabState :=
                hPath.prefixPath hTailExt
              have hTailPath :
                  ClzCompilationPath contract
                    headElabState tailElabState :=
                hPath.suffixPath hHeadExt
              have hHeadScopes :
                  headElabState.functionScopes =
                    elabState.functionScopes :=
                Elab.Stmt.elaborate_preserves_functionScopes rawHead hHead
              have hTailContext :
                  PathCompiledContext builtinContext contract
                    rawContext headElabState.functionScopes := by
                simpa [hHeadScopes] using hContext
              have hHeadRun :=
                hStmt hCompatible hContext hHeadPath hHead hHeadNormalized
              have hCons :=
                scopedSeqRunForward_cons
                  (entryStore := entryStore)
                  (rawFuel := fuel) (orderedFuel := fuel + slack)
                  (context := rawContext) (rawStmt := rawHead)
                  (rawRest := rawTail) (orderedStmt := orderedHead)
                  (orderedRest := orderedTail) (contract := contract)
                  (state := state) hHeadRun
                  (fun shared vars =>
                    hSeq (state := .Ok shared vars)
                      (by trivial) hTailContext hTailPath
                      hTail hTailNormalized)
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hCons

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
      cases rawState with
      | Ok shared vars =>
          subst orderedState
          exact Simulation.Interaction.ForwardRel.done rfl
      | OutOfFuel =>
          cases hState with
          | inl hExact =>
              subst orderedState
              exact Simulation.Interaction.ForwardRel.done rfl
          | inr hRestricted =>
              subst orderedState
              apply Simulation.Interaction.ForwardRel.done
              unfold SameDoneRel
              congr 1
      | Checkpoint jump =>
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
                  (.Checkpoint jump) state.store).symm

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

/-- Successful raw compilation constructs the exact generated-`clz` resolver
for the final code-elaboration state. Name allocation, frontend validation,
object-builtin resolution, Yul conversion, and canonical lookup are all
discharged from the compiler artifact; callers supply no helper certificate. -/
theorem clzBindingResolverAt
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (ctx : ArtifactRawSourceContext rawJson selection artifact)
    {code : List Raw.Stmt}
    (hCode : ctx.selected.root.code? = some code) :
    ∃ coreDispatcher finalState,
      Elab.elaborateCodeCore code = .ok (coreDispatcher, finalState) ∧
        ClzBindingResolverAt
          artifact.codeArtifact.ordered.program.contract finalState := by
  rcases ctx.code_elaborates hCode with
    ⟨helper?, arg?, ret?, hElab⟩
  rcases Elab.elaborateCode_parts hElab with
    ⟨finalState, hCore, hFunctions, hHelper, hArg, hRet⟩
  refine ⟨ctx.program.object.dispatcher, finalState, hCore, ?_⟩
  intro generated allocatedArg allocatedRet hAllocated
  have hHelperOption : helper? = some generated := by
    rw [hHelper]
    exact hAllocated.helper_eq
  have hArgOption : arg? = some allocatedArg := by
    rw [hArg]
    exact hAllocated.arg_eq
  have hRetOption : ret? = some allocatedRet := by
    rw [hRet]
    exact hAllocated.ret_eq
  have hExactElab :
      Elab.elaborateCode code =
        .ok (ctx.program.object.dispatcher, ctx.program.object.functions,
          some generated, some allocatedArg, some allocatedRet) := by
    simpa [hHelperOption, hArgOption, hRetOption] using hElab
  rcases decodeAndElaborateSolcIr?_frontendValidated ctx.decode with
    ⟨json, selected, object, hParse, hSelected, hObject,
      hValidated, hProgram⟩
  rw [ctx.parse] at hParse
  cases hParse
  rw [ctx.selected_ok] at hSelected
  cases hSelected
  have hValidatedProgram :
      Raw.Object.FrontendValidated
        ctx.selected.root ctx.program.object := by
    simpa [hProgram] using hValidated
  have hNamesBool :
      Raw.Object.clzHelperNamesDistinct? ctx.selected.root = true :=
    hValidatedProgram.2.1
  have hNames : allocatedArg ≠ allocatedRet :=
    Raw.Object.clzHelperNamesDistinct?_arg_ne
      hCode hExactElab hNamesBool
  have hHelperMem :
      (generated,
        Elab.clzHelperFunctionDef allocatedArg allocatedRet) ∈
          ctx.program.object.functions :=
    Elab.elaborateCode_clzHelper_mem hExactElab
  rcases Frontend.Object.compileVerifiedStackCodeArtifactIn?_function_entry
      ctx.codeArtifact hHelperMem with
    ⟨memoryContract, resolvedFn, yulBody, _hMemory, hResolve,
      _hResolvedMem, hParams, hReturns, hBodyYul, hEntry⟩
  have hResolveIdentity :=
    EvmCompiler.Solidity.RawAst.Raw.ClzPreservation.clzHelperFunctionDef_resolveObjectBuiltinsIn?
      allocatedArg allocatedRet
      { ctx.context with memoryContract := memoryContract }
  rw [hResolveIdentity] at hResolve
  have hResolvedFn :
      resolvedFn = Elab.clzHelperFunctionDef allocatedArg allocatedRet :=
    Option.some.inj hResolve.symm
  subst resolvedFn
  have hOrderedSource :=
    Frontend.Object.toSolcYulOrderedProgram?_source ctx.ordered
  have hLookup :
      artifact.codeArtifact.ordered.program.contract.functions.lookup
          generated =
        some
          (.Def
            (Elab.clzHelperFunctionDef allocatedArg allocatedRet).params
            (Elab.clzHelperFunctionDef allocatedArg allocatedRet).returns
            yulBody) := by
    rw [hOrderedSource.1]
    exact
      EvmCompiler.Yul.FunctionList.lookup_functionMap_of_mem
        hOrderedSource.2.1 hEntry
  refine ⟨{
    argName := allocatedArg
    returnName := allocatedRet
    yulBody := yulBody
    namesDistinct := hNames
    orderedLookup := ?_
    bodyToYul := ?_ }⟩
  · simpa [Elab.clzHelperFunctionDef] using hLookup
  · simpa [Elab.clzHelperFunctionDef] using hBodyYul

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
