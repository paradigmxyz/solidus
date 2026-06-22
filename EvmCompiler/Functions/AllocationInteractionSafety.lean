import EvmCompiler.Functions.AllocationInteractionPrimitive
import EvmCompiler.Functions.InteractionSemantics

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionSafety

abbrev SourceState := AllocationInteractionRelation.SourceState
abbrev Word := Assembly.Word

mutual
  /-- Source-facing safety of an expression for every open-world answer. -/
  def ExprSafe (contract : MemoryContract.Contract) {results : Nat}
      (expr : Functions.Expr results) (source : SourceState) : Prop :=
    match expr with
    | .lit _ => True
    | .var name => ∃ value, source.vars name = some value
    | .code _ => False
    | .prim op args =>
        Locals.InteractionSemantics.Primitive.supportsOpen op = true ∧
          ExprSeqSafe contract args source ∧
          Simulation.Interaction.AllDone
            (AllocationInteractionPrimitive.PrimitiveArgsSafe contract op)
            (Functions.InteractionSemantics.ExprSeq.openEval args source)

  /-- Source-facing safety of an expression sequence under ordered evaluation. -/
  def ExprSeqSafe (contract : MemoryContract.Contract) {results : Nat}
      (exprs : Locals.ExprSeq results) (source : SourceState) : Prop :=
    match exprs with
    | .nil => True
    | .cons head tail =>
        ExprSafe contract head source ∧
          Simulation.Interaction.AllDone
            (fun outcome =>
              match outcome with
              | .error _ => True
              | .ok result => ExprSeqSafe contract tail result.1)
            (Functions.InteractionSemantics.Expr.openEval head source)
end

/-- Source-facing safety for canonical left-to-right call arguments. -/
def ArgListSafe (contract : MemoryContract.Contract) :
    List (Functions.Expr 1) → SourceState → Prop
  | [], _source => True
  | arg :: rest, source =>
      ExprSafe contract arg source ∧
        Simulation.Interaction.AllDone
          (fun outcome =>
            match outcome with
            | .error _ => True
            | .ok result => ArgListSafe contract rest result.1)
          (Functions.InteractionSemantics.Expr.openEvalOne arg source)

/--
Legacy globally quantified reservation-safety interface.

Although each clause is guarded by a successful source evaluation, the
quantifiers range over every scoped expression and source state rather than one
program execution. `SourceSafety.uninhabited` below shows that no contract can
satisfy this interface. New public theorems must instead use program/run-indexed
safety; this structure remains temporarily because the legacy mixed-allocation
proof route still consumes it.
-/
structure SourceSafety (contract : MemoryContract.Contract) : Prop where
  expr :
    ∀ {results : Nat} {live : List Functions.Name}
      {expr : Functions.Expr results} {source : SourceState},
      Functions.Scope.ExprScoped live expr →
      AllocationInteractionRelation.LiveDefined live source →
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Expr.openEval expr source) →
      ExprSafe contract expr source
  terminal :
    ∀ {kind : Assembly.HaltKind} {source : SourceState}
      {values : List Word},
      Simulation.Interaction.Successful
        (Locals.InteractionSemantics.Primitive.openTerminal
          kind source values) →
      Simulation.MemorySafety.TerminalMemorySafe contract kind values

namespace SourceSafety

/-- Safe, scoped expression sequences remain safe along every reachable
left-to-right continuation. -/
theorem exprSeq
    {contract : MemoryContract.Contract}
    (hSafety : SourceSafety contract) :
    ∀ {results : Nat} {live : List Functions.Name}
      {exprs : Locals.ExprSeq results} {source : SourceState},
      Functions.Scope.ExprSeqScoped live exprs →
      AllocationInteractionRelation.LiveDefined live source →
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.ExprSeq.openEval exprs source) →
      ExprSeqSafe contract exprs source := by
  intro results live exprs
  cases exprs with
  | nil =>
      intro source _hScoped _hDefined _hSuccess
      trivial
  | @cons headResults tailResults head tail =>
      intro source hScoped hDefined hSuccess
      rcases hScoped with ⟨hHeadScoped, hTailScoped⟩
      unfold Functions.InteractionSemantics.ExprSeq.openEval at hSuccess
      unfold Locals.InteractionSemantics.ExprSeq.openEval at hSuccess
      unfold Locals.Source.Effectful.Expr.Control.ExprSeq.eval at hSuccess
      have hHeadSuccess := Simulation.Interaction.Successful.bind_left hSuccess
      refine ⟨hSafety.expr hHeadScoped hDefined hHeadSuccess, ?_⟩
      have hContinuations :=
        Simulation.Interaction.Successful.bind_inv hSuccess
      have hVars :=
        Locals.InteractionSemantics.Expr.openEval_vars_eq head source
      apply Simulation.Interaction.AllDone.mono
        (Simulation.Interaction.AllDone.inter hContinuations hVars)
      intro outcome hOutcome
      cases outcome with
      | error err => trivial
      | ok result =>
          rcases result with ⟨afterHead, values⟩
          have hTailSuccessRaw :=
            Simulation.Interaction.Successful.bind_left hOutcome.1
          have hTailSuccess :
              Simulation.Interaction.Successful
                (Functions.InteractionSemantics.ExprSeq.openEval
                  tail afterHead) := by
            simpa [Functions.InteractionSemantics.ExprSeq.openEval,
              Locals.InteractionSemantics.ExprSeq.openEval] using
              hTailSuccessRaw
          exact
            exprSeq hSafety hTailScoped
              (hDefined.congr_vars hOutcome.2) hTailSuccess
termination_by results live exprs => sizeOf exprs
decreasing_by simp_wf

/-- Canonical function arguments inherit source safety from their scoped
expressions and the successful left-to-right argument run. -/
theorem argList
    {contract : MemoryContract.Contract}
    (hSafety : SourceSafety contract) :
    ∀ {live : List Functions.Name} {args : List (Functions.Expr 1)}
      {source : SourceState},
      (∀ arg, arg ∈ args → Functions.Scope.ExprScoped live arg) →
      AllocationInteractionRelation.LiveDefined live source →
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.ArgList.openEval args source) →
      ArgListSafe contract args source := by
  intro live args
  induction args with
  | nil =>
      intro source _hScoped _hDefined _hSuccess
      trivial
  | cons arg rest ih =>
      intro source hScoped hDefined hSuccess
      unfold Functions.InteractionSemantics.ArgList.openEval at hSuccess
      unfold Functions.Source.Canonical.ArgList.eval at hSuccess
      unfold Functions.Source.Effectful.ArgList.Control.eval at hSuccess
      have hHeadSuccess := Simulation.Interaction.Successful.bind_left hSuccess
      have hArgSuccess :
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Expr.openEvalOne arg source) := by
        simpa [Functions.InteractionSemantics.Expr.openEvalOne,
          Locals.InteractionSemantics.Expr.openEvalOne] using hHeadSuccess
      have hEvalSuccess :
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Expr.openEval arg source) := by
        unfold Functions.InteractionSemantics.Expr.openEvalOne at hArgSuccess
        unfold Locals.InteractionSemantics.Expr.openEvalOne at hArgSuccess
        unfold Locals.Source.Effectful.Expr.Control.evalOne at hArgSuccess
        exact Simulation.Interaction.Successful.bind_left hArgSuccess
      refine
        ⟨hSafety.expr (hScoped arg (by simp)) hDefined hEvalSuccess, ?_⟩
      have hContinuations :=
        Simulation.Interaction.Successful.bind_inv hSuccess
      have hVars :=
        Locals.InteractionSemantics.Expr.openEvalOne_vars_eq arg source
      apply Simulation.Interaction.AllDone.mono
        (Simulation.Interaction.AllDone.inter hContinuations hVars)
      intro outcome hOutcome
      cases outcome with
      | error err => trivial
      | ok result =>
          rcases result with ⟨afterArg, value⟩
          have hRestSuccessRaw :=
            Simulation.Interaction.Successful.bind_left hOutcome.1
          have hRestSuccess :
              Simulation.Interaction.Successful
                (Functions.InteractionSemantics.ArgList.openEval
                  rest afterArg) := by
            simpa [Functions.InteractionSemantics.ArgList.openEval,
              Functions.Source.Canonical.ArgList.eval] using hRestSuccessRaw
          exact
            ih (fun expr hMem => hScoped expr (by simp [hMem]))
              (hDefined.congr_vars hOutcome.2) hRestSuccess

private def counterexampleSource : SourceState :=
  { shared := default
    vars := fun _ => none }

private def counterexampleAddress : Word :=
  EvmYul.UInt256.ofNat USize.size

private def counterexampleExpr : Functions.Expr 0 :=
  .prim .mstore
    (Locals.ExprSeq.cons (.lit (EvmYul.UInt256.ofNat 0))
      (Locals.ExprSeq.cons (.lit counterexampleAddress) .nil))

/-- The legacy global interface is inconsistent. Ordinary gasless evaluation
accepts a closed `mstore` at the host address-space limit, while `ExprSafe`
correctly rejects that write. The contradiction is independent of the scratch
reservation, so it applies to every memory contract. -/
theorem uninhabited (contract : MemoryContract.Contract) :
    ¬ SourceSafety contract := by
  intro hSafety
  have hSafe := hSafety.expr
    (expr := counterexampleExpr) (source := counterexampleSource)
    (live := [])
    (by simp [counterexampleExpr, Functions.Scope.ExprScoped,
      Functions.Scope.ExprSeqScoped])
    (by simp [AllocationInteractionRelation.LiveDefined])
    (by
      change Simulation.Interaction.AllDone _ (.done (.ok _))
      exact .done trivial)
  have hPrim := hSafe.2.2
  change Simulation.Interaction.AllDone
    (AllocationInteractionPrimitive.PrimitiveArgsSafe contract .mstore)
    (.done (.ok (counterexampleSource,
      [EvmYul.UInt256.ofNat 0, counterexampleAddress]))) at hPrim
  cases hPrim with
  | done hArgs =>
      have hHost := hArgs.2.2.2
      simp only [Simulation.MemorySafety.PrimitiveHostSafe,
        List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append] at hHost
      rw [counterexampleAddress,
        EvmYul.UInt256.toNat_ofNat_of_lt
          Compiler.MemoryRelation.usize_size_lt_uint256_size] at hHost
      omega

end SourceSafety

end AllocationInteractionSafety
end Functions
end EvmCompiler
