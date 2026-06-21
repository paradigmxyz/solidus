import EvmCompiler.Functions.StackExpressionPreservation
import EvmCompiler.Functions.StackAccessLowering
import EvmCompiler.Functions.StackLoweringCompilation
import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Functions.StackStatementPreservation
import EvmCompiler.Locals.InteractionArity

/-!
Internal-call preservation for the stack allocator.

This owner bridges the canonical Functions call protocol to the ordinary
Locals/Expressions call protocol. It does not define a call interpreter or a
call-specific compiler.
-/

namespace EvmCompiler
namespace Functions
namespace StackCallPreservation

open StackRelation

@[simp] private theorem openEvalSeq_cast
    {left right : Nat} (h : left = right)
    (exprs : Locals.ExprSeq left) (state : Locals.Source.State) :
    Locals.InteractionSemantics.ExprSeq.openEval
        (cast (congrArg Locals.ExprSeq h) exprs) state =
      Locals.InteractionSemantics.ExprSeq.openEval exprs state := by
  cases h
  rfl

private theorem exprSeqScoped_cast
    {left right : Nat} (h : left = right)
    {env : List Name} {exprs : Locals.ExprSeq left}
    (hScoped : Functions.Scope.ExprSeqScoped env exprs) :
    Functions.Scope.ExprSeqScoped env
      (cast (congrArg Locals.ExprSeq h) exprs) := by
  cases h
  exact hScoped

private theorem openSupported_cast
    {left right : Nat} (h : left = right)
    {exprs : Locals.ExprSeq left}
    (hSupported :
      Locals.InteractionSemantics.ExprSeq.OpenSupported exprs) :
    Locals.InteractionSemantics.ExprSeq.OpenSupported
      (cast (congrArg Locals.ExprSeq h) exprs) := by
  cases h
  exact hSupported

/-- `argExprs` is a shape adapter, not a new argument semantics. -/
theorem argExprs_openEval :
    ∀ (args : List (Functions.Expr 1)) (state : Locals.Source.State),
      Locals.InteractionSemantics.ExprSeq.openEval
          (Lower.argExprs args) state =
        Functions.InteractionSemantics.ArgList.openEval args state
  | [], _state => rfl
  | arg :: rest, state => by
      unfold Lower.argExprs
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons arg (Lower.argExprs rest)
      have hLen : 1 + rest.length = rest.length + 1 := by omega
      change
        Locals.InteractionSemantics.ExprSeq.openEval
            (cast (congrArg Locals.ExprSeq hLen) exprs) state = _
      rw [openEvalSeq_cast hLen]
      unfold Locals.InteractionSemantics.ExprSeq.openEval
        Functions.InteractionSemantics.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval
        Functions.Source.Effectful.ArgList.Control.eval
      simp only [exprs,
        Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
      change
        Simulation.Interaction.bind
            (Locals.InteractionSemantics.Expr.openEval arg state)
            (fun headResult =>
              Simulation.Interaction.bind
                (Locals.InteractionSemantics.ExprSeq.openEval
                  (Lower.argExprs rest) headResult.1)
                (fun tailResult =>
                  Simulation.Interaction.pure
                    (tailResult.1, headResult.2 ++ tailResult.2))) =
          Simulation.Interaction.bind
            (Locals.InteractionSemantics.Expr.openEvalOne arg state)
            (fun headResult =>
              Simulation.Interaction.bind
                (Functions.InteractionSemantics.ArgList.openEval
                  rest headResult.1)
                (fun tailResult =>
                  Simulation.Interaction.pure
                    (tailResult.1, headResult.2 :: tailResult.2)))
      rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
        Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Locals.InteractionArity.Expr.openEval_length arg state)
      intro headResult hLength
      rcases headResult with ⟨stateAfterHead, values⟩
      change values.length = 1 at hLength
      cases values with
      | nil => simp at hLength
      | cons value tail =>
          cases tail with
          | nil =>
              simp only [Simulation.Interaction.bind_done_ok]
              rw [argExprs_openEval rest stateAfterHead]
              rfl
          | cons next tail => simp at hLength

theorem argExprs_scoped :
    ∀ {env : List Name} {args : List (Functions.Expr 1)},
      (∀ arg, arg ∈ args → Functions.Scope.ExprScoped env arg) →
        Functions.Scope.ExprSeqScoped env (Lower.argExprs args)
  | _env, [], _hScoped => trivial
  | env, arg :: rest, hScoped => by
      unfold Lower.argExprs
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons arg (Lower.argExprs rest)
      have hLen : 1 + rest.length = rest.length + 1 := by omega
      apply exprSeqScoped_cast hLen
      exact
        ⟨hScoped arg (by simp),
          argExprs_scoped
            (fun candidate hCandidate =>
              hScoped candidate (by simp [hCandidate]))⟩

theorem argExprs_openSupported :
    ∀ {args : List (Functions.Expr 1)},
      Functions.InteractionSemantics.ArgList.OpenSupported args →
        Locals.InteractionSemantics.ExprSeq.OpenSupported
          (Lower.argExprs args)
  | [], _hSupported => trivial
  | arg :: rest, hSupported => by
      unfold Lower.argExprs
      let exprs : Locals.ExprSeq (1 + rest.length) :=
        Locals.ExprSeq.cons arg (Lower.argExprs rest)
      have hLen : 1 + rest.length = rest.length + 1 := by omega
      apply openSupported_cast hLen
      exact
        ⟨hSupported arg (by simp),
          argExprs_openSupported
            (fun candidate hCandidate =>
              hSupported candidate (by simp [hCandidate]))⟩

theorem argExprs_localsScoped_of_check
    {env layout : List Name} {args : List (Functions.Expr 1)}
    (hCheck : StackAccess.ExprSeq.check? layout 0 (Lower.argExprs args) =
      some ())
    (hScoped :
      ∀ arg, arg ∈ args → Functions.Scope.ExprScoped env arg) :
    Locals.Scope.ExprSeqScoped layout (Lower.argExprs args) := by
  exact
    StackAccess.ExprSeq.scoped_of_check hCheck (argExprs_scoped hScoped)

/-- Ordered source arguments compile to the exact reversed argument prefix
expected by the Expressions call splitter. -/
theorem openEvalArgs_compileCode
    (args : List (Functions.Expr 1)) (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hScoped :
      Locals.Scope.ExprSeqScoped ctx.layout (Lower.argExprs args))
    (hSupported :
      Functions.InteractionSemantics.ArgList.OpenSupported args)
    (hCompile :
      Locals.ExprSeq.compileCode ctx 0 (Lower.argExprs args) = some code)
    (hInitial : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (Locals.InteractionPreservation.Expr.OutcomeRel args.length source target)
      (Functions.InteractionSemantics.ArgList.openEval args source)
      (Structured.InteractionSemantics.Code.openRun code target) := by
  rw [← argExprs_openEval args source]
  exact
    StackExpressionPreservation.openEvalSeq_compileCode
      (Lower.argExprs args) ctx hScoped
      (argExprs_openSupported hSupported) hCompile hInitial

/-- The target call splitter recovers precisely the argument vector emitted by
the checked expression compiler and the untouched dormant caller stack. -/
theorem splitArgs_of_argResult
    {argc : Nat} {sourceInitial sourceFinal : Locals.Source.State}
    {targetInitial targetFinal : Structured.RunState}
    {args : List Word}
    (hResult :
      Locals.InteractionPreservation.Expr.ResultRel args.length
        sourceInitial targetInitial (sourceFinal, args) targetFinal)
    (hLength : args.length = argc) :
    Structured.StackFrame.splitArgs? argc targetFinal.evm.stack =
      some (args.reverse, targetInitial.evm.stack) := by
  rw [hResult.stack, ← hLength]
  simpa using
    Structured.StackFrame.splitArgs?_append args.reverse
      targetInitial.evm.stack

/-- After ordered arguments are evaluated, removing their temporary stack
prefix recovers the caller layout with the argument effects already reflected
in shared state. -/
theorem callerStateRel_of_argResult
    {ctx : Locals.Ctx} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {arity : Nat}
    {sourceInitial sourceAfterArgs : Locals.Source.State}
    {targetInitial targetAfterArgs : Structured.RunState}
    {args : List Word}
    (hInitial :
      StateRel ctx.layout suffix returns sourceInitial targetInitial)
    (hResult :
      Locals.InteractionPreservation.Expr.ResultRel arity
        sourceInitial targetInitial (sourceAfterArgs, args) targetAfterArgs) :
    StateRel ctx.layout suffix returns sourceAfterArgs
      (targetAfterArgs.withEVM
        { targetAfterArgs.evm with stack := targetInitial.evm.stack }) := by
  have hValues :
      StackRelation.values sourceAfterArgs ctx.layout =
        StackRelation.values sourceInitial ctx.layout := by
    unfold StackRelation.values
    rw [hResult.vars]
  constructor
  · simpa using hResult.shared
  · simpa using hResult.returns.trans hInitial.returns
  · simp only [Structured.RunState.withEVM]
    rw [hInitial.stack, hValues]
  · intro name hName
    obtain ⟨value, hValue⟩ := hInitial.defined hName
    exact ⟨value, by rw [hResult.vars]; exact hValue⟩

inductive ArgBlockResultRel
    (arity : Nat) (sourceInitial : Locals.Source.State)
    (targetInitial : Structured.RunState) :
    (Locals.Source.State × List Word) → Structured.Outcome → Prop
  | regular {sourceFinal : Locals.Source.State} {values : List Word}
      {targetFinal : Structured.RunState} :
      Locals.InteractionPreservation.Expr.ResultRel arity
        sourceInitial targetInitial (sourceFinal, values) targetFinal →
      ArgBlockResultRel arity sourceInitial targetInitial
        (sourceFinal, values) (.regular targetFinal)

abbrev OpenArgBlockResultRel
    (arity : Nat) (sourceInitial : Locals.Source.State)
    (targetInitial : Structured.RunState) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (ArgBlockResultRel arity sourceInitial targetInitial)

theorem openEvalArgs_compileBlock
    (targetProgram : Expressions.Program) (targetFuel : Nat)
    (args : List (Functions.Expr 1)) (ctx : Locals.Ctx)
    {code : Structured.Code} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hFuel : 2 ≤ targetFuel)
    (hScoped :
      Locals.Scope.ExprSeqScoped ctx.layout (Lower.argExprs args))
    (hSupported :
      Functions.InteractionSemantics.ArgList.OpenSupported args)
    (hCompile :
      Locals.ExprSeq.compileCode ctx 0 (Lower.argExprs args) = some code)
    (hInitial : StateRel ctx.layout suffix returns source target) :
    Simulation.Interaction.Rel
      (OpenArgBlockResultRel args.length source target)
      (Functions.InteractionSemantics.ArgList.openEval args source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        targetFuel { stmts := [.code code] } target) := by
  have hArgs :=
    openEvalArgs_compileCode args ctx hScoped hSupported hCompile hInitial
  rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_stmt_of_fuel
    targetProgram targetFuel (.code code) target hFuel]
  unfold Expressions.InteractionSemantics.Stmt.openRun
    Expressions.EffectSemantics.Control.Stmt.run
  change
    Simulation.Interaction.Rel
      (OpenArgBlockResultRel args.length source target)
      (Functions.InteractionSemantics.ArgList.openEval args source)
      (Simulation.Interaction.bind
        (Structured.InteractionSemantics.Code.openRun code target)
        (fun final =>
          Simulation.Interaction.pure (Structured.Outcome.regular final)))
  rw [← Simulation.Interaction.bind_pure
    (Functions.InteractionSemantics.ArgList.openEval args source)]
  apply Simulation.Interaction.Rel.bind hArgs
  intro sourceResult targetResult hResult
  exact Simulation.Interaction.Rel.done
    (Simulation.Interaction.ExceptRel.ok (.regular hResult))

namespace CalleeEntry

def sourceState (sourceAfterArgs : Locals.Source.State)
    (fn : Functions.FunDef) (paramStore : Functions.Source.Store) :
    Locals.Source.State :=
  Functions.InteractionSemantics.stateModel.withSource sourceAfterArgs
    { shared := sourceAfterArgs.shared
      vars := Functions.Source.Store.initReturns fn.returns paramStore }

def targetState (targetAfterArgs : Structured.RunState)
    (args callerStack : EvmYul.Stack Word) (retc : Nat) :
    Structured.RunState :=
  (targetAfterArgs.withEVM { targetAfterArgs.evm with stack := args }).pushReturn
    callerStack retc

/-- Canonical function initialization retains parameter values and installs
zeroes for all declared returns. -/
theorem initialized_lookup
    {fn : Functions.FunDef} {args : List Word}
    {paramStore : Functions.Source.Store}
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore) :
    Functions.Source.Store.lookupMany fn.params
        (Functions.Source.Store.initReturns fn.returns paramStore) =
      some args :=
  (Functions.Source.Store.initializedStore_lookupMany hSignature hInsert).1

/-- Before the return-zeroing prelude, the real target call state already
realizes the canonical parameter layout. -/
theorem stateRel
    {fn : Functions.FunDef} {args : List Word}
    {paramStore : Functions.Source.Store}
    {sourceAfterArgs : Locals.Source.State}
    {targetAfterArgs : Structured.RunState}
    {callerStack : EvmYul.Stack Word}
    {callerReturns : List Structured.ReturnDest}
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hShared : targetAfterArgs.evm.toSharedState = sourceAfterArgs.shared)
    (hReturns : targetAfterArgs.returns = callerReturns) :
    StateRel fn.params.reverse []
      ({ callerStack := callerStack, retc := fn.returns.length } ::
        callerReturns)
      (sourceState sourceAfterArgs fn paramStore)
      (targetState targetAfterArgs args.reverse callerStack
        fn.returns.length) := by
  have hParams := initialized_lookup hSignature hInsert
  have hParamsReverse :=
    Functions.Source.Store.lookupMany_reverse hParams
  apply StateRel.of_lookupMany
  · simpa [sourceState, targetState,
      Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel,
      Structured.RunState.withEVM, Structured.RunState.pushReturn] using
      hShared
  · simpa [targetState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn] using hReturns
  · simpa [sourceState, Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel] using hParamsReverse
  · simp [targetState, Structured.RunState.withEVM,
      Structured.RunState.pushReturn]

theorem runtimeCtx
    (fn : Functions.FunDef) (frame : Structured.ReturnDest)
    (callerReturns : List Structured.ReturnDest) :
    StackStatementPreservation.RuntimeCtxCovers
      (Functions.Source.Effectful.FunDef.bodyCtx fn)
      (Locals.Ctx.procEntryWithLayoutAndRetc
        (StackLowering.functionBodyLayout fn) fn.returns.length)
      {} fn.returns (frame :: callerReturns) := by
  let sourceCtx := Functions.Source.Effectful.FunDef.bodyCtx fn
  let targetCtx :=
    Locals.Ctx.procEntryWithLayoutAndRetc
      (StackLowering.functionBodyLayout fn) fn.returns.length
  have hContext :
      StackStatementPreservation.CtxCovers sourceCtx targetCtx := by
    constructor
    intro name hName
    simp [sourceCtx, targetCtx, StackLowering.functionBodyLayout,
      Functions.Source.Effectful.FunDef.bodyCtx,
      Locals.Ctx.procEntryWithLayoutAndRetc,
      Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
      Locals.Ctx.initial] at hName ⊢
    rcases hName with hReturn | hParam
    · exact Or.inl hReturn
    · exact Or.inr hParam
  refine ⟨?_, ?_, ?_⟩
  · exact
      { context := hContext
        breakTarget := by intro layout hTarget; simp at hTarget
        continueTarget := by intro layout hTarget; simp at hTarget }
  · refine
      { availability := by
          simp [sourceCtx, targetCtx,
            Functions.Source.Effectful.FunDef.bodyCtx,
            Functions.Source.Ctx.withLeaveScope,
            Functions.Source.Ctx.initial,
            Locals.Ctx.procEntryWithLayoutAndRetc,
            Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
            Locals.Ctx.initial]
        sourceScope := ?_
        targetDepth := ?_
        targetRetc := ?_ }
    · intro scope hScope name hName
      have hScopeEq : scope = fn.returns ++ fn.params := by
        simpa [sourceCtx, Functions.Source.Effectful.FunDef.bodyCtx] using
          Option.some.inj hScope.symm
      subst scope
      exact List.mem_append_left fn.params hName
    · intro _hLeave
      simp [targetCtx, Locals.Ctx.procEntryWithLayoutAndRetc,
        Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
        Locals.Ctx.initial]
    · intro _hLeave
      simp [targetCtx, Locals.Ctx.procEntryWithLayoutAndRetc,
        Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
        Locals.Ctx.initial]
  · intro _hLeave
    simp

end CalleeEntry

namespace ReturnPrelude

/-- The ordinary `initReturns` compiler prelude pushes exactly the zero-valued
source bindings, producing the canonical function-body layout. -/
theorem compileOpenRun :
    ∀ (targetProgram : Expressions.Program) (names : List Name)
      (targetCtx : Locals.Ctx)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source : Locals.Source.State} {target : Structured.RunState},
      (names.reverse ++ targetCtx.layout).Nodup →
      (∀ name, name ∈ names → source.vars name = some Lower.zero) →
      StateRel targetCtx.layout suffix returns source target →
      ∃ code finalCtx finalTarget,
        Locals.Block.compileOpen targetCtx
            { stmts := Lower.initReturns names } = some (code, finalCtx) ∧
        finalCtx.layout = names.reverse ++ targetCtx.layout ∧
        code.length = names.length ∧
        (∀ stmt, stmt ∈ code → ∃ stmtCode, stmt = .code stmtCode) ∧
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (names.length + 1) { stmts := code } target =
          Simulation.Interaction.pure
            (Structured.Outcome.regular finalTarget) ∧
        StateRel (names.reverse ++ targetCtx.layout) suffix returns
          source finalTarget
  | targetProgram, [], targetCtx, suffix, returns, source, target,
      _hNodup, _hZero, hInitial => by
      exact
        ⟨[], targetCtx, target,
          by simp [Lower.initReturns, Locals.Block.compileOpen], by simp,
          rfl,
          by intro stmt hStmt; simp at hStmt,
          by simpa using
            Expressions.InteractionSemantics.Block.openRun_nil
              targetProgram 0 target,
          by simpa using hInitial⟩
  | targetProgram, name :: rest, targetCtx, suffix, returns, source, target,
      hNodup, hZero, hInitial => by
      have hShape :
          (rest.reverse ++ name :: targetCtx.layout).Nodup := by
        simpa [List.reverse_cons, List.append_assoc] using hNodup
      have hFresh : name ∉ targetCtx.layout :=
        List.nodup_cons.mp (List.nodup_append.mp hShape).2.1 |>.1
      let targetAfter :=
        target.withEVM
          (target.evm.replaceStackAndIncrPC
            (Lower.zero :: target.evm.stack) (pcΔ := 33))
      have hAfter :
          StateRel (name :: targetCtx.layout) suffix returns source
            targetAfter := by
        exact StateRel.afterPushExisting hFresh (hZero name (by simp)) hInitial
      obtain ⟨tailCode, finalCtx, finalTarget, hTailCompile, hFinalLayout,
          hTailLength, hTailOnly, hTailRun, hFinal⟩ :=
        compileOpenRun targetProgram rest
          (targetCtx.withLayout (name :: targetCtx.layout))
          (by simpa [Locals.Ctx.withLayout] using hShape)
          (fun candidate hCandidate => hZero candidate (by simp [hCandidate]))
          (by simpa [Locals.Ctx.withLayout] using hAfter)
      let headCode : Structured.Code :=
        [.push Lower.zero] ++
          Locals.bindLocals 0 (name :: targetCtx.layout)
      have hCompile :
          Locals.Block.compileOpen targetCtx
              { stmts := Lower.initReturns (name :: rest) } =
            some (.code headCode :: tailCode, finalCtx) := by
        simp [Lower.initReturns, Locals.Block.compileOpen,
          Locals.Stmt.compile, Locals.Expr.compileCode, Locals.codeStmt,
          headCode, hTailCompile]
      have hHeadRun :
          Expressions.InteractionSemantics.Stmt.openRun targetProgram
              (rest.length + 1) (.code headCode) target =
            Simulation.Interaction.pure
              (Structured.Outcome.regular targetAfter) := by
        unfold Expressions.InteractionSemantics.Stmt.openRun
          Expressions.EffectSemantics.Control.Stmt.run
        change
          Simulation.Interaction.bind
              (Structured.InteractionSemantics.Code.openRun headCode target)
              (fun final =>
                Simulation.Interaction.pure
                  (Structured.Outcome.regular final)) = _
        unfold headCode
        rw [Structured.InteractionSemantics.Code.openRun_append,
          Locals.InteractionPreservation.Code.openRun_push,
          Simulation.Interaction.bind_done_ok]
        rw [show Locals.bindLocals 0 (name :: targetCtx.layout) =
            [.bindLocals 0 (name :: targetCtx.layout)] by rfl,
          Locals.InteractionPreservation.Code.openRun_bindLocals]
        rfl
      refine
        ⟨.code headCode :: tailCode, finalCtx, finalTarget,
          hCompile, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [Locals.Ctx.withLayout, List.reverse_cons,
          List.append_assoc] using hFinalLayout
      · simp [hTailLength]
      · intro stmt hStmt
        rcases List.mem_cons.mp hStmt with hHead | hTail
        · subst stmt
          exact ⟨headCode, rfl⟩
        · exact hTailOnly stmt hTail
      · rw [show (name :: rest).length + 1 = rest.length + 2 by simp]
        rw [Expressions.InteractionSemantics.Block.openRun_cons]
        change
          Simulation.Interaction.bind
              (Expressions.InteractionSemantics.Stmt.openRun targetProgram
                (rest.length + 1) (.code headCode) target) _ = _
        rw [hHeadRun]
        simpa [Simulation.Interaction.pure,
          Simulation.Interaction.bind] using hTailRun
      · simpa [Locals.Ctx.withLayout, List.reverse_cons,
          List.append_assoc] using hFinal

theorem compileOpenRun_of_fuel
    (targetProgram : Expressions.Program) (names : List Name)
    (targetCtx : Locals.Ctx) (targetFuel : Nat)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hFuel : names.length < targetFuel)
    (hNodup : (names.reverse ++ targetCtx.layout).Nodup)
    (hZero : ∀ name, name ∈ names → source.vars name = some Lower.zero)
    (hInitial : StateRel targetCtx.layout suffix returns source target) :
    ∃ code finalCtx finalTarget,
      Locals.Block.compileOpen targetCtx
          { stmts := Lower.initReturns names } = some (code, finalCtx) ∧
      finalCtx.layout = names.reverse ++ targetCtx.layout ∧
      code.length = names.length ∧
      (∀ stmt, stmt ∈ code → ∃ stmtCode, stmt = .code stmtCode) ∧
      Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel { stmts := code } target =
        Simulation.Interaction.pure
          (Structured.Outcome.regular finalTarget) ∧
      StateRel (names.reverse ++ targetCtx.layout) suffix returns
        source finalTarget := by
  obtain ⟨code, finalCtx, finalTarget, hCompile, hLayout, hCodeLength,
      hCodeOnly, hRun, hFinal⟩ :=
    compileOpenRun targetProgram names targetCtx hNodup hZero hInitial
  have hCanonicalFuel : code.length < names.length + 1 := by
    omega
  have hRequestedFuel : code.length < targetFuel := by
    omega
  have hFuelEq :=
    Expressions.InteractionSemantics.Block.openRun_codeOnly_fuel_eq
      targetProgram code hCodeOnly (names.length + 1) targetFuel target
      hCanonicalFuel hRequestedFuel
  exact ⟨code, finalCtx, finalTarget, hCompile, hLayout, hCodeLength, hCodeOnly,
    hFuelEq ▸ hRun, hFinal⟩

end ReturnPrelude

inductive CallResultRel
    (frame : Structured.ReturnDest)
    (callerReturns : List Structured.ReturnDest) :
    Functions.InteractionSemantics.CallResult → Structured.Outcome → Prop
  | regular {source : Locals.Source.State} {values : List Word}
      {target : Structured.RunState} :
      target.evm.toSharedState = source.shared →
      target.evm.stack = values.reverse →
      target.returns = frame :: callerReturns →
      values.length = frame.retc →
      CallResultRel frame callerReturns
        (.returned source values) (.regular target)
  | leave {source : Locals.Source.State} {values : List Word}
      {target : Structured.RunState} :
      target.evm.toSharedState = source.shared →
      target.evm.stack = values.reverse →
      target.returns = frame :: callerReturns →
      values.length = frame.retc →
      CallResultRel frame callerReturns
        (.returned source values) (.leave target)
  | halt {kind : Assembly.HaltKind} {source : Locals.Source.State}
      {target : Structured.RunState} :
      target.evm.toSharedState = source.shared →
      CallResultRel frame callerReturns
        (.halted kind source) (.halt kind target)

abbrev OpenCallResultRel
    (frame : Structured.ReturnDest)
    (callerReturns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (CallResultRel frame callerReturns)

/-- Semantic internal-call result after the ordinary Expressions call wrapper
restores the dormant caller stack. Return-frame metadata is relevant only for
the nonterminal result. -/
inductive AttachedCallResultRel
    (retc : Nat) (callerStack : List Word)
    (callerReturns : List Structured.ReturnDest) :
    Functions.InteractionSemantics.CallResult → Structured.Outcome → Prop
  | returned {source : Locals.Source.State} {values : List Word}
      {target : Structured.RunState} :
      target.evm.toSharedState = source.shared →
      target.evm.stack = values.reverse ++ callerStack →
      target.returns = callerReturns →
      values.length = retc →
      AttachedCallResultRel retc callerStack callerReturns
        (.returned source values) (.regular target)
  | halt {kind : Assembly.HaltKind} {source : Locals.Source.State}
      {target : Structured.RunState} :
      target.evm.toSharedState = source.shared →
      AttachedCallResultRel retc callerStack callerReturns
        (.halted kind source) (.halt kind target)

abbrev OpenAttachedCallResultRel
    (retc : Nat) (callerStack : List Word)
    (callerReturns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (AttachedCallResultRel retc callerStack callerReturns)

namespace CallResultRel

theorem regular_of_stateRel
    {returnNames : List Name} {source : Locals.Source.State}
    {values : List Word} {target : Structured.RunState}
    {frame : Structured.ReturnDest}
    {callerReturns : List Structured.ReturnDest}
    (hRetc : frame.retc = returnNames.length)
    (hLookup :
      Functions.Source.Store.lookupMany returnNames source.vars = some values)
    (hRel :
      StateRel returnNames.reverse [] (frame :: callerReturns)
        source target) :
    CallResultRel frame callerReturns
      (.returned source values) (.regular target) := by
  apply CallResultRel.regular hRel.shared
  · rw [hRel.stack]
    rw [StackRelation.values_eq_of_lookupMany
      (Functions.Source.Store.lookupMany_reverse hLookup)]
    simp
  · exact hRel.returns
  · rw [hRetc]
    exact Functions.Source.Store.lookupMany_length hLookup

theorem leave_of_stateRel
    {returnNames : List Name} {source : Locals.Source.State}
    {values : List Word} {target : Structured.RunState}
    {frame : Structured.ReturnDest}
    {callerReturns : List Structured.ReturnDest}
    (hRetc : frame.retc = returnNames.length)
    (hLookup :
      Functions.Source.Store.lookupMany returnNames source.vars = some values)
    (hRel :
      StateRel returnNames.reverse [] (frame :: callerReturns)
        source target) :
    CallResultRel frame callerReturns
      (.returned source values) (.leave target) := by
  apply CallResultRel.leave hRel.shared
  · rw [hRel.stack]
    rw [StackRelation.values_eq_of_lookupMany
      (Functions.Source.Store.lookupMany_reverse hLookup)]
    simp
  · exact hRel.returns
  · rw [hRetc]
    exact Functions.Source.Store.lookupMany_length hLookup

end CallResultRel

namespace CallAttachment

/-- Attach one already-related callee run through the real Expressions call
wrapper. Procedure lookup, argument splitting, return-frame removal, and return
value attachment are all the ordinary target operations. -/
theorem of_body
    {targetProgram : Expressions.Program}
    {name : Expressions.Name} {proc : Expressions.Proc}
    {sourceRun :
      Simulation.Interaction EVMException
        Functions.InteractionSemantics.CallResult}
    {targetFuel : Nat}
    {callArgs callerStack : List Word}
    {targetCaller : Structured.RunState}
    (hLookup :
      Expressions.EffectSemantics.ProcList.lookup?
          name targetProgram.procs = some proc)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc targetCaller.evm.stack =
        some (callArgs, callerStack))
    (hBody :
      Simulation.Interaction.ForwardRel
        StackStatementPreservation.FuelTruncated
        (OpenCallResultRel
          { callerStack := callerStack, retc := proc.retc }
          targetCaller.returns)
        sourceRun
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel proc.body
          (CalleeEntry.targetState targetCaller callArgs callerStack
            proc.retc))) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenAttachedCallResultRel proc.retc callerStack targetCaller.returns)
      sourceRun
      (Expressions.InteractionSemantics.Stmt.openRun targetProgram
        (targetFuel + 1) (.call name) targetCaller) := by
  rw [Expressions.InteractionSemantics.Stmt.openRun_call]
  simp only [hLookup, hSplit]
  change
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenAttachedCallResultRel proc.retc callerStack targetCaller.returns)
      sourceRun
      (Simulation.Interaction.bind
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel proc.body
          (CalleeEntry.targetState targetCaller callArgs callerStack
            proc.retc)) _)
  rw [← Simulation.Interaction.bind_pure sourceRun]
  apply Simulation.Interaction.ForwardRel.bind hBody
  intro sourceResult targetResult hResult
  cases hResult with
  | @regular source values target hShared hStack hReturns hLength =>
      have hPop :
          target.popReturn? =
            some
              ({ callerStack := callerStack, retc := proc.retc },
                { target with returns := targetCaller.returns }) := by
        unfold Structured.RunState.popReturn?
        rw [hReturns]
      have hAttach :
          Structured.StackFrame.attachReturns?
              { callerStack := callerStack, retc := proc.retc }
              target.evm.stack =
            some (values.reverse ++ callerStack) := by
        rw [hStack]
        exact Structured.StackFrame.attachReturns?_eq_some (by simpa using hLength)
      let attached : Structured.RunState :=
        ({ target with returns := targetCaller.returns }).withEVM
          { target.evm with stack := values.reverse ++ callerStack }
      simp only [Simulation.Interaction.pure,
        Structured.Outcome.regular_mode, Structured.Outcome.regular_state,
        Structured.EffectSemantics.Ordinary.runStateModel_evm,
        Structured.EffectSemantics.Ordinary.runStateModel_withEVM,
        Structured.EffectSemantics.Ordinary.runStateModel_popReturn?]
      rw [hPop]
      simp only [Structured.OutcomeT.state]
      rw [hAttach]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact AttachedCallResultRel.returned
        (by simpa [attached] using hShared)
        (by simp [attached])
        (by simp [attached])
        hLength
  | @leave source values target hShared hStack hReturns hLength =>
      have hPop :
          target.popReturn? =
            some
              ({ callerStack := callerStack, retc := proc.retc },
                { target with returns := targetCaller.returns }) := by
        unfold Structured.RunState.popReturn?
        rw [hReturns]
      have hAttach :
          Structured.StackFrame.attachReturns?
              { callerStack := callerStack, retc := proc.retc }
              target.evm.stack =
            some (values.reverse ++ callerStack) := by
        rw [hStack]
        exact Structured.StackFrame.attachReturns?_eq_some (by simpa using hLength)
      let attached : Structured.RunState :=
        ({ target with returns := targetCaller.returns }).withEVM
          { target.evm with stack := values.reverse ++ callerStack }
      simp only [Simulation.Interaction.pure,
        Structured.Outcome.leave_mode, Structured.Outcome.leave_state,
        Structured.EffectSemantics.Ordinary.runStateModel_evm,
        Structured.EffectSemantics.Ordinary.runStateModel_withEVM,
        Structured.EffectSemantics.Ordinary.runStateModel_popReturn?]
      rw [hPop]
      simp only [Structured.OutcomeT.state]
      rw [hAttach]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact AttachedCallResultRel.returned
        (by simpa [attached] using hShared)
        (by simp [attached])
        (by simp [attached])
        hLength
  | @halt kind source target hShared =>
      simp only [Simulation.Interaction.pure,
        Structured.Outcome.halt_mode, Structured.Outcome.halt_state]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact AttachedCallResultRel.halt hShared

end CallAttachment

namespace FunctionLookup

/-- Source first-match function lookup is preserved by the actual stack
function lowerer followed by ordinary Locals procedure compilation. -/
theorem of_compilers
    (allFunctions : List FunDef) (name : Name) :
    ∀ {sourceFunctions : List FunDef} {procs : List Locals.Proc}
      {lowerProcs : List Expressions.Proc} {fn : FunDef},
      StackLowering.lowerFunctions? allFunctions sourceFunctions =
          some procs →
      Locals.ProcList.toExpressions? procs = some lowerProcs →
      Functions.Source.FunList.find? name sourceFunctions = some fn →
      ∃ proc lowerProc,
        StackLowering.lowerFunction? allFunctions fn = some proc ∧
        proc.toExpressions? = some lowerProc ∧
        Expressions.EffectSemantics.ProcList.lookup? name lowerProcs =
          some lowerProc
  | [], _procs, _lowerProcs, _fn, _hLower, _hCompile, hFind => by
      simp [Functions.Source.FunList.find?] at hFind
  | head :: rest, procs, lowerProcs, fn, hLower, hCompile, hFind => by
      cases hHeadLower : StackLowering.lowerFunction? allFunctions head with
      | none =>
          simp [StackLowering.lowerFunctions?, hHeadLower] at hLower
      | some headProc =>
          cases hTailLower :
              StackLowering.lowerFunctions? allFunctions rest with
          | none =>
              simp [StackLowering.lowerFunctions?, hHeadLower, hTailLower]
                at hLower
          | some tailProcs =>
              simp [StackLowering.lowerFunctions?, hHeadLower, hTailLower]
                  at hLower
              subst procs
              cases hHeadCompile : headProc.toExpressions? with
              | none =>
                  simp [Locals.ProcList.toExpressions?, hHeadCompile]
                    at hCompile
              | some headLower =>
                  cases hTailCompile :
                      Locals.ProcList.toExpressions? tailProcs with
                  | none =>
                      simp [Locals.ProcList.toExpressions?, hHeadCompile,
                        hTailCompile] at hCompile
                  | some tailLower =>
                      simp [Locals.ProcList.toExpressions?, hHeadCompile,
                          hTailCompile] at hCompile
                      subst lowerProcs
                      have hHeadProcName : headProc.name = head.name := by
                        obtain ⟨_facts, _schedule, _body, _hFacts,
                            _hSchedule, _hBody, _hAccess, hProc⟩ :=
                          StackLowering.lowerFunction?_components hHeadLower
                        rw [hProc]
                      have hHeadLowerName : headLower.name = head.name :=
                        (Locals.Proc.toExpressions?_name hHeadCompile).trans
                          hHeadProcName
                      by_cases hName : head.name = name
                      · simp [Functions.Source.FunList.find?, hName] at hFind
                        subst fn
                        refine ⟨headProc, headLower, hHeadLower,
                          hHeadCompile, ?_⟩
                        simp [Expressions.EffectSemantics.ProcList.lookup?,
                          hHeadLowerName, hName]
                      · have hTailFind :
                            Functions.Source.FunList.find? name rest =
                              some fn := by
                          simpa [Functions.Source.FunList.find?, hName]
                            using hFind
                        obtain ⟨proc, lowerProc, hProcLower,
                            hProcCompile, hLookup⟩ :=
                          of_compilers allFunctions name hTailLower
                            hTailCompile hTailFind
                        refine ⟨proc, lowerProc, hProcLower, hProcCompile, ?_⟩
                        simp [Expressions.EffectSemantics.ProcList.lookup?,
                          hHeadLowerName, hName, hLookup]

end FunctionLookup

namespace CallerWriteback

structure PendingRel
    (layout : Locals.Layout) (suffix : List Word)
    (returns : List Structured.ReturnDest) (pending : List Word)
    (source : Locals.Source.State) (target : Structured.RunState) : Prop where
  shared : target.evm.toSharedState = source.shared
  returnsEq : target.returns = returns
  stack :
    target.evm.stack =
      pending ++ StackRelation.values source layout ++ suffix
  defined : ∀ name, name ∈ layout → ∃ value, source.vars name = some value

private theorem set_append_offset
    {α : Type} (above suffix : List α) (depth : Nat) (value : α) :
    (above ++ suffix).set (above.length + depth) value =
      above ++ suffix.set depth value := by
  induction above with
  | nil => simp
  | cons head tail ih => simp [Nat.succ_add, ih]

private theorem PendingRel.assignTopWithOffset
    (targetProgram : Expressions.Program)
    (targetFuel : Nat)
    {ctx : Locals.Ctx} {suffix : List Word}
    {returns : List Structured.ReturnDest}
    {name : Name} {value : Word} {remaining : List Word}
    {source : Locals.Source.State} {target : Structured.RunState}
    {code : List Expressions.Stmt} {finalCtx : Locals.Ctx}
    (hNodup : ctx.layout.Nodup)
    (hFuel : 2 ≤ targetFuel)
    (hCompile :
      Locals.Stmt.compile ctx
          (.assignTopWithOffset remaining.length name) =
        some (code, finalCtx))
    (hPending :
      PendingRel ctx.layout suffix returns (value :: remaining)
        source target) :
    ∃ finalTarget,
      Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
          { stmts := code } target =
        Simulation.Interaction.pure
          (Structured.Outcome.regular finalTarget) ∧
      PendingRel ctx.layout suffix returns remaining
        (source.insert name value) finalTarget ∧
      finalCtx = ctx := by
  obtain ⟨depth, op, hDepth, hSwap, hCode, hFinalCtx⟩ :=
    Locals.Stmt.compile_assignTopWithOffset_components hCompile
  subst code
  have hAt : ctx.layout[depth]? = some name :=
    Locals.Layout.getElem?_eq_some_of_lookupDepth?_eq_some hDepth
  obtain ⟨old, hOld⟩ :=
    hPending.defined name (List.mem_of_getElem? hAt)
  have hValueAt :
      (StackRelation.values source ctx.layout)[depth]? = some old := by
    simp [StackRelation.values, List.getElem?_map, hAt, hOld]
  have hDepthBound :
      depth < (StackRelation.values source ctx.layout).length :=
    List.getElem?_eq_some_iff.mp hValueAt |>.1
  have hRestGet :
      ((remaining ++ StackRelation.values source ctx.layout ++ suffix)[remaining.length + depth]?) =
        some old := by
    rw [List.append_assoc]
    rw [List.getElem?_append_right]
    · rw [show remaining.length + depth - remaining.length = depth by omega]
      rw [List.getElem?_append_left hDepthBound]
      simpa using hValueAt
    · simp
  have hSwap' :
      Locals.StackOp.swap? (remaining.length + depth + 1) = some op := by
    simpa [Nat.add_assoc] using hSwap
  obtain ⟨afterSwapPop, hSwapRun, hFinalStack,
      hFinalShared, hFinalReturns⟩ :=
    Locals.InteractionPreservation.Code.openRun_swap_pop
      hSwap' hRestGet hPending.stack
  have hCodeRun :
      Structured.InteractionSemantics.Code.openRun
          ([Structured.BasicInstr.op op, Structured.BasicInstr.op .pop] ++
            Locals.bindLocals remaining.length ctx.layout)
          target = .done (.ok afterSwapPop) := by
    rw [Structured.InteractionSemantics.Code.openRun_append, hSwapRun]
    simp only [Simulation.Interaction.bind_done_ok]
    rw [show Locals.bindLocals remaining.length ctx.layout =
        [.bindLocals remaining.length ctx.layout] by rfl,
      Locals.InteractionPreservation.Code.openRun_bindLocals]
  have hBlockRun :
      Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
          { stmts :=
              Locals.codeStmt
                ([Structured.BasicInstr.op op,
                    Structured.BasicInstr.op .pop] ++
                  Locals.bindLocals remaining.length ctx.layout) }
          target =
        Simulation.Interaction.pure
          (Structured.Outcome.regular afterSwapPop) := by
    simpa [Locals.codeStmt] using
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        targetProgram targetFuel _ target afterSwapPop hFuel hCodeRun
  refine ⟨afterSwapPop, hBlockRun, ?_, hFinalCtx⟩
  constructor
  · rw [hFinalShared]
    simpa [Locals.Source.State.insert] using hPending.shared
  · exact hFinalReturns.trans hPending.returnsEq
  · rw [hFinalStack]
    rw [show remaining ++ StackRelation.values source ctx.layout ++ suffix =
        remaining ++ (StackRelation.values source ctx.layout ++ suffix) by
      simp [List.append_assoc]]
    rw [set_append_offset,
      List.set_append_left depth value hDepthBound,
      ← StackRelation.values_insert_existing hNodup hAt]
    simp [List.append_assoc]
  · intro candidate hCandidate
    by_cases hName : candidate = name
    · subst candidate
      exact ⟨value, Locals.Source.Store.insert_self _ _ _⟩
    · obtain ⟨oldValue, hOldValue⟩ := hPending.defined candidate hCandidate
      exact
        ⟨oldValue, by
          simpa [Locals.Source.State.insert,
            Locals.Source.Store.insert, hName] using hOldValue⟩

theorem compileOpenRunRev :
    ∀ (targetProgram : Expressions.Program) (targetExtra : Nat)
      (ctx : Locals.Ctx)
      (suffix : List Word) (returns : List Structured.ReturnDest)
      (names : List Name) (values : List Word)
      (source : Locals.Source.State) (target : Structured.RunState)
      (finalStore : Functions.Source.Store)
      (code : List Expressions.Stmt),
      ctx.layout.Nodup →
      Functions.Source.Store.assignMany names values source.vars =
        some finalStore →
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTopsRev names } =
        some (code, ctx) →
      PendingRel ctx.layout suffix returns values source target →
      ∃ finalTarget,
        Expressions.InteractionSemantics.Block.openRun targetProgram
            (targetExtra + names.length + 1) { stmts := code } target =
          Simulation.Interaction.pure
            (Structured.Outcome.regular finalTarget) ∧
        StateRel ctx.layout suffix returns
          (source.withVars finalStore) finalTarget
  | targetProgram, targetExtra, ctx, suffix, returns, [], values, source, target,
      finalStore, code, _hNodup, hAssign, hCompile, hPending => by
      cases values with
      | cons value values =>
          simp [Functions.Source.Store.assignMany] at hAssign
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
          subst finalStore
          simp [Lower.assignReturnedTopsRev,
            Locals.Block.compileOpen] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          refine ⟨target, ?_, ?_⟩
          · simpa using
              Expressions.InteractionSemantics.Block.openRun_nil
                targetProgram targetExtra target
          · constructor
            · simpa [Locals.Source.State.withVars] using hPending.shared
            · exact hPending.returnsEq
            · simpa [Locals.Source.State.withVars] using hPending.stack
            · intro name hName
              simpa [Locals.Source.State.withVars] using
                hPending.defined name hName
  | targetProgram, targetExtra, ctx, suffix, returns, name :: names, values,
      source, target, finalStore, code, hNodup, hAssign, hCompile,
      hPending => by
      cases values with
      | nil =>
          simp [Functions.Source.Store.assignMany] at hAssign
      | cons value values =>
          have hLength : values.length = names.length := by
            have hWholeLength :=
              Functions.Source.Store.assignMany_length hAssign
            simpa using hWholeLength
          have hContains : source.vars.contains name := by
            by_contra hNotContains
            simp [Functions.Source.Store.assignMany, hNotContains] at hAssign
          have hTailAssign :
              Functions.Source.Store.assignMany names values
                  (source.insert name value).vars = some finalStore := by
            simpa [Functions.Source.Store.assignMany, hContains,
              Locals.Source.State.insert] using hAssign
          change
            Locals.Block.compileOpen ctx
                { stmts :=
                    .assignTopWithOffset names.length name ::
                      Lower.assignReturnedTopsRev names } =
              some (code, ctx) at hCompile
          obtain ⟨headCode, middleCtx, tailCode, hHeadCompile,
              hTailCompile, hCode⟩ :=
            Locals.Block.compileOpen_cons_components hCompile
          obtain ⟨_depth, _op, _hDepth, _hSwap,
              hHeadCode, hMiddleCtx⟩ :=
            Locals.Stmt.compile_assignTopWithOffset_components hHeadCompile
          subst middleCtx
          subst headCode
          subst code
          have hHeadCompile' :
              Locals.Stmt.compile ctx
                  (.assignTopWithOffset values.length name) =
                some
                  (Locals.codeStmt
                    ([Structured.BasicInstr.op _op,
                        Structured.BasicInstr.op .pop] ++
                      Locals.bindLocals values.length ctx.layout),
                   ctx) := by
            simpa [hLength] using hHeadCompile
          obtain ⟨targetAfterHead, hHeadRun, hAfterHead, _hCtx⟩ :=
            PendingRel.assignTopWithOffset targetProgram
              (targetExtra + names.length + 2) hNodup (by omega)
              hHeadCompile' hPending
          have hHeadRun' :
              Expressions.InteractionSemantics.Block.openRun targetProgram
                  (targetExtra + names.length + 2)
                  { stmts :=
                      Locals.codeStmt
                        ([Structured.BasicInstr.op _op,
                            Structured.BasicInstr.op .pop] ++
                          Locals.bindLocals names.length ctx.layout) }
                  target =
                Simulation.Interaction.pure
                  (Structured.Outcome.regular targetAfterHead) := by
            simpa [hLength] using hHeadRun
          obtain ⟨finalTarget, hTailRun, hFinalRel⟩ :=
            compileOpenRunRev targetProgram targetExtra ctx suffix returns
              names values (source.insert name value) targetAfterHead
              finalStore tailCode hNodup hTailAssign hTailCompile hAfterHead
          refine ⟨finalTarget, ?_, hFinalRel⟩
          rw [Expressions.InteractionSemantics.Block.openRun_append]
          simp only [List.length_cons]
          rw [show targetExtra + (names.length + 1) + 1 =
              targetExtra + names.length + 2 by omega]
          rw [hHeadRun']
          simp only [Simulation.Interaction.bind_done_ok,
            Structured.Outcome.regular_mode,
            Structured.Outcome.regular_state, Locals.codeStmt,
            List.length_cons, List.length_nil, Nat.add_zero]
          simpa using hTailRun

theorem compileOpenRev_length :
    ∀ (ctx : Locals.Ctx) (names : List Name)
      (code : List Expressions.Stmt),
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTopsRev names } =
        some (code, ctx) →
      code.length = names.length
  | _ctx, [], code, hCompile => by
      simp [Lower.assignReturnedTopsRev,
        Locals.Block.compileOpen] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      rfl
  | ctx, name :: names, code, hCompile => by
      change
        Locals.Block.compileOpen ctx
            { stmts :=
                .assignTopWithOffset names.length name ::
                  Lower.assignReturnedTopsRev names } =
          some (code, ctx) at hCompile
      obtain ⟨headCode, middleCtx, tailCode, hHead, hTail, hCode⟩ :=
        Locals.Block.compileOpen_cons_components hCompile
      obtain ⟨_depth, _op, _hDepth, _hSwap, hHeadCode, hMiddle⟩ :=
        Locals.Stmt.compile_assignTopWithOffset_components hHead
      subst middleCtx
      subst headCode
      subst code
      have hTailLength := compileOpenRev_length ctx names tailCode hTail
      simp [Locals.codeStmt, hTailLength]

/-- Execute the compiler's caller writeback order. The checked source store
assignment is reversed exactly once to match the top-first target stack. -/
theorem compileOpenRun
    (targetProgram : Expressions.Program) (targetExtra : Nat)
    (ctx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (targets : List Name) (values : List Word)
    (source : Locals.Source.State) (target : Structured.RunState)
    (finalStore : Functions.Source.Store)
    (code : List Expressions.Stmt)
    (hLayoutNodup : ctx.layout.Nodup)
    (hTargetsNodup : targets.Nodup)
    (hAssign :
      Functions.Source.Store.assignMany targets values source.vars =
        some finalStore)
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTops targets } =
        some (code, ctx))
    (hPending :
      PendingRel ctx.layout suffix returns values.reverse source target) :
    ∃ finalTarget,
      Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetExtra + targets.length + 1) { stmts := code } target =
        Simulation.Interaction.pure
          (Structured.Outcome.regular finalTarget) ∧
      StateRel ctx.layout suffix returns
        (source.withVars finalStore) finalTarget := by
  have hReverse :
      Functions.Source.Store.assignMany targets.reverse values.reverse
          source.vars = some finalStore :=
    Functions.Source.Store.assignMany_reverse_of_run hAssign hTargetsNodup
  have hRun :=
    compileOpenRunRev targetProgram targetExtra ctx suffix returns
      targets.reverse values.reverse source target finalStore code hLayoutNodup
      hReverse (by simpa [Lower.assignReturnedTops] using hCompile) hPending
  simpa using hRun

theorem compileOpen_length
    (ctx : Locals.Ctx) (targets : List Name)
    (code : List Expressions.Stmt)
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTops targets } =
        some (code, ctx)) :
    code.length = targets.length := by
  simpa [Lower.assignReturnedTops] using
    compileOpenRev_length ctx targets.reverse code
      (by simpa [Lower.assignReturnedTops] using hCompile)

/-- A returned internal call has enough checked arity and caller-layout
information to construct source `assignMany` and run the emitted target
writeback without accepting assignment evidence as a premise. -/
theorem returned
    (targetProgram : Expressions.Program)
    (targetExtra : Nat)
    (sourceCtx : Functions.Source.Ctx)
    (controlTargets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (ctx : Locals.Ctx) (suffix : List Word)
    (returns : List Structured.ReturnDest)
    (targets : List Name) (retc : Nat)
    (sourceAfterArgs sourceReturned : Locals.Source.State)
    (callerTarget targetAfterCall : Structured.RunState)
    (values : List Word) (code : List Expressions.Stmt)
    (hRuntime :
      StackStatementPreservation.RuntimeCtxCovers sourceCtx ctx
        controlTargets returnNames returns)
    (hLayoutNodup : ctx.layout.Nodup)
    (hTargetsNodup : targets.Nodup)
    (hTargetsLength : targets.length = retc)
    (hTargetsLayout : ∀ name, name ∈ targets → name ∈ ctx.layout)
    (hCaller :
      StateRel ctx.layout suffix returns sourceAfterArgs callerTarget)
    (hAttached :
      AttachedCallResultRel retc callerTarget.evm.stack returns
        (.returned sourceReturned values) (.regular targetAfterCall))
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTops targets } =
        some (code, ctx)) :
    Simulation.Interaction.Rel
      (StackStatementPreservation.ControlOpenOutcomeRel controlTargets
        returnNames ctx suffix returns)
      (Functions.InteractionSemantics.Stmt.finishCall targets sourceCtx
        sourceAfterArgs (.returned sourceReturned values))
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetExtra + targets.length + 1) { stmts := code }
        targetAfterCall) := by
  cases hAttached with
  | returned hShared hStack hReturns hValuesLength =>
      have hLength : values.length = targets.length := by
        omega
      have hContains :
          ∀ name, name ∈ targets →
            sourceAfterArgs.vars.contains name = true := by
        intro name hName
        obtain ⟨value, hValue⟩ :=
          hCaller.defined (hTargetsLayout name hName)
        simp [Locals.Source.Store.contains, hValue]
      obtain ⟨finalStore, hAssign⟩ :=
        Functions.Source.Store.assignMany_exists_of_length_of_contains
          hLength hContains
      let writeSource := sourceReturned.withVars sourceAfterArgs.vars
      have hPending :
          PendingRel ctx.layout suffix returns values.reverse
            writeSource targetAfterCall := by
        constructor
        · simpa [writeSource, Locals.Source.State.withVars] using hShared
        · exact hReturns
        · rw [hStack, hCaller.stack]
          simp [writeSource, StackRelation.values,
            Locals.Source.State.withVars]
        · intro name hName
          obtain ⟨value, hValue⟩ := hCaller.defined hName
          exact
            ⟨value, by
              simpa [writeSource, Locals.Source.State.withVars] using hValue⟩
      have hAssignWrite :
          Functions.Source.Store.assignMany targets values
              writeSource.vars = some finalStore := by
        simpa [writeSource, Locals.Source.State.withVars] using hAssign
      obtain ⟨finalTarget, hTargetRun, hFinalRel⟩ :=
        compileOpenRun targetProgram targetExtra ctx suffix returns targets
          values writeSource targetAfterCall finalStore code hLayoutNodup
          hTargetsNodup hAssignWrite hCompile hPending
      have hSourceRun :
          Functions.InteractionSemantics.Stmt.finishCall targets sourceCtx
              sourceAfterArgs (.returned sourceReturned values) =
            Simulation.Interaction.pure
              (Locals.Source.Effectful.Outcome.regular
                (sourceReturned.withVars finalStore), sourceCtx) := by
        simp [Functions.InteractionSemantics.Stmt.finishCall, hAssign,
          Functions.InteractionSemantics.stateModel,
          Locals.InteractionSemantics.stateModel,
          Locals.Source.Effectful.Ordinary.stateModel,
          Locals.Source.Effectful.StateModel.vars,
          Locals.Source.Effectful.StateModel.source,
          Locals.Source.Effectful.StateModel.withSource,
          Locals.Source.State.withVars,
          Simulation.Interaction.pure, Simulation.Interaction.bind,
          Simulation.Interaction.monad_pure_bind]
        rfl
      rw [hSourceRun, hTargetRun]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      apply StackStatementPreservation.ControlOpenResultRel.regular hRuntime
      simpa [writeSource, Locals.Source.State.withVars] using hFinalRel

theorem halted
    (sourceCtx : Functions.Source.Ctx)
    (controlTargets : StackSchedule.ControlTargets)
    (returnNames : List Name) (ctx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (targets : List Name) (retc : Nat)
    (sourceAfterArgs sourceHalted : Locals.Source.State)
    (callerStack : List Word) (targetHalted : Structured.RunState)
    (kind : Assembly.HaltKind)
    (hAttached :
      AttachedCallResultRel retc callerStack returns
        (.halted kind sourceHalted) (.halt kind targetHalted)) :
    Simulation.Interaction.Rel
      (StackStatementPreservation.ControlOpenOutcomeRel controlTargets
        returnNames ctx suffix returns)
      (Functions.InteractionSemantics.Stmt.finishCall targets sourceCtx
        sourceAfterArgs (.halted kind sourceHalted))
      (Simulation.Interaction.pure
        (Structured.Outcome.halt kind targetHalted)) := by
  cases hAttached with
  | halt hShared =>
      simp only [Functions.InteractionSemantics.Stmt.finishCall,
        Simulation.Interaction.pure]
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact StackStatementPreservation.ControlOpenResultRel.halt hShared.symm

/-- Compose any already-attached call run with canonical source `finishCall`
and the compiler-owned target writeback block. -/
theorem afterCall
    (targetProgram : Expressions.Program) (targetExtra : Nat)
    (sourceCtx : Functions.Source.Ctx)
    (controlTargets : StackSchedule.ControlTargets)
    (returnNames : List Name) (ctx : Locals.Ctx)
    (suffix : List Word) (returns : List Structured.ReturnDest)
    (targets : List Name) (retc : Nat)
    (sourceAfterArgs : Locals.Source.State)
    (callerTarget : Structured.RunState)
    (code : List Expressions.Stmt)
    {sourceRun :
      Simulation.Interaction EVMException
        Functions.InteractionSemantics.CallResult}
    {targetRun :
      Simulation.Interaction EVMException Structured.Outcome}
    (hRuntime :
      StackStatementPreservation.RuntimeCtxCovers sourceCtx ctx
        controlTargets returnNames returns)
    (hLayoutNodup : ctx.layout.Nodup)
    (hTargetsNodup : targets.Nodup)
    (hTargetsLength : targets.length = retc)
    (hTargetsLayout : ∀ name, name ∈ targets → name ∈ ctx.layout)
    (hCaller :
      StateRel ctx.layout suffix returns sourceAfterArgs callerTarget)
    (hCompile :
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTops targets } =
        some (code, ctx))
    (hCall :
      Simulation.Interaction.ForwardRel
        StackStatementPreservation.FuelTruncated
        (OpenAttachedCallResultRel retc callerTarget.evm.stack returns)
        sourceRun targetRun) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (StackStatementPreservation.ControlOpenOutcomeRel controlTargets
        returnNames ctx suffix returns)
      (Simulation.Interaction.bind sourceRun
        (Functions.InteractionSemantics.Stmt.finishCall targets sourceCtx
          sourceAfterArgs))
      (Simulation.Interaction.bind targetRun
        (fun outcome =>
          match outcome.mode with
          | .regular =>
              Expressions.InteractionSemantics.Block.openRun targetProgram
                (targetExtra + targets.length + 1) { stmts := code }
                outcome.state
          | .brk | .cont | .leave | .halt _ =>
              Simulation.Interaction.pure outcome)) := by
  apply Simulation.Interaction.ForwardRel.bind hCall
  intro sourceResult targetResult hAttached
  cases hAttached with
  | @returned sourceReturned values targetAfterCall
      hShared hStack hReturns hValuesLength =>
      apply Simulation.Interaction.ForwardRel.ofRel
      simpa only [Structured.Outcome.regular_mode,
        Structured.Outcome.regular_state] using
        returned targetProgram targetExtra sourceCtx controlTargets
          returnNames ctx suffix returns targets retc sourceAfterArgs
          sourceReturned callerTarget targetAfterCall values code hRuntime
          hLayoutNodup hTargetsNodup hTargetsLength hTargetsLayout hCaller
          (.returned hShared hStack hReturns hValuesLength) hCompile
  | @halt kind sourceHalted targetHalted hShared =>
      apply Simulation.Interaction.ForwardRel.ofRel
      simpa only [Structured.Outcome.halt_mode,
        Structured.Outcome.halt_state] using
        halted sourceCtx controlTargets returnNames ctx suffix returns targets
          retc sourceAfterArgs sourceHalted callerTarget.evm.stack
          targetHalted kind (.halt hShared)

end CallerWriteback

namespace CallPoint

/-- Preserve the complete call core before the scheduler's post-call retain
transition. The callee capability is deliberately private proof plumbing; the
program dispatcher discharges it by source fuel. -/
theorem core
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (controlTargets : StackSchedule.ControlTargets)
    (returnNames : List Name) (ctx : Locals.Ctx)
    (sourceFuel targetExtra : Nat)
    (targets : List Name) (functionName : Name)
    (args : List (Functions.Expr 1)) (fn : Functions.FunDef)
    (argCode : Structured.Code) (writebackCode : List Expressions.Stmt)
    {suffix : List Word} {returns : List Structured.ReturnDest}
    {source : Locals.Source.State} {target : Structured.RunState}
    (hFind :
      Functions.Source.FunList.find? functionName sourceProgram.functions =
        some fn)
    (hRuntime :
      StackStatementPreservation.RuntimeCtxCovers sourceCtx ctx
        controlTargets returnNames returns)
    (hLayoutNodup : ctx.layout.Nodup)
    (hTargetsNodup : targets.Nodup)
    (hTargetsLength : targets.length = fn.returns.length)
    (hTargetsLayout : ∀ name, name ∈ targets → name ∈ ctx.layout)
    (hArgScoped :
      Locals.Scope.ExprSeqScoped ctx.layout (Lower.argExprs args))
    (hArgSupported :
      Functions.InteractionSemantics.ArgList.OpenSupported args)
    (hArgCompile :
      Locals.ExprSeq.compileCode ctx 0 (Lower.argExprs args) =
        some argCode)
    (hWritebackCompile :
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTops targets } =
        some (writebackCode, ctx))
    (hInitial : StateRel ctx.layout suffix returns source target)
    (hCallee :
      ∀ {sourceAfterArgs : Locals.Source.State}
        {argValues : List Word} {targetAfterArgs : Structured.RunState},
        Locals.InteractionPreservation.Expr.ResultRel args.length
            source target (sourceAfterArgs, argValues) targetAfterArgs →
          Simulation.Interaction.ForwardRel
            StackStatementPreservation.FuelTruncated
            (OpenAttachedCallResultRel fn.returns.length
              target.evm.stack returns)
            (Functions.InteractionSemantics.FunDef.openRunBody sourceProgram
              fn argValues sourceFuel sourceAfterArgs)
            (Expressions.InteractionSemantics.Stmt.openRun targetProgram
              (targetExtra + targets.length + 1) (.call functionName)
              targetAfterArgs)) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (StackStatementPreservation.ControlOpenOutcomeRel controlTargets
        returnNames ctx suffix returns)
      (Functions.InteractionSemantics.Stmt.openRun sourceProgram sourceCtx
        (sourceFuel + 1) (.call targets functionName args) source)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetExtra + targets.length + 3)
        { stmts :=
            [.code argCode] ++ (.call functionName :: writebackCode) }
        target) := by
  rw [Functions.InteractionSemantics.Stmt.openRun_call]
  simp only [hTargetsNodup, if_pos]
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  have hArgs :=
    openEvalArgs_compileBlock targetProgram
      (targetExtra + targets.length + 3) args ctx (by omega)
      hArgScoped hArgSupported hArgCompile hInitial
  apply Simulation.Interaction.ForwardRel.bind
    (Simulation.Interaction.ForwardRel.ofRel hArgs)
  intro sourceResult targetResult hArgResult
  cases hArgResult with
  | @regular sourceAfterArgs argValues targetAfterArgs hArg =>
      simp only [hFind, Option.elim_some,
        Simulation.Interaction.bind_done_ok,
        Simulation.Interaction.monad_pure_bind]
      let callerTarget :=
        targetAfterArgs.withEVM
          { targetAfterArgs.evm with stack := target.evm.stack }
      have hCaller :
          StateRel ctx.layout suffix returns sourceAfterArgs callerTarget := by
        exact callerStateRel_of_argResult hInitial hArg
      have hAttached := hCallee hArg
      have hAttached' :
          Simulation.Interaction.ForwardRel
            StackStatementPreservation.FuelTruncated
            (OpenAttachedCallResultRel fn.returns.length
              callerTarget.evm.stack returns)
            (Functions.InteractionSemantics.FunDef.openRunBody sourceProgram
              fn argValues sourceFuel sourceAfterArgs)
            (Expressions.InteractionSemantics.Stmt.openRun targetProgram
              (targetExtra + targets.length + 1) (.call functionName)
              targetAfterArgs) := by
        simpa [callerTarget, Structured.RunState.withEVM] using hAttached
      have hAfterCall :=
        CallerWriteback.afterCall targetProgram targetExtra sourceCtx
          controlTargets returnNames ctx suffix returns targets
          fn.returns.length sourceAfterArgs callerTarget writebackCode hRuntime
          hLayoutNodup hTargetsNodup hTargetsLength hTargetsLayout hCaller
          hWritebackCompile hAttached'
      have hFuelEq :
          targetExtra + targets.length + 3 - 1 =
            targetExtra + targets.length + 2 := by
        omega
      simp only [Structured.Outcome.regular_mode,
        Structured.Outcome.regular_state, List.length_cons,
        List.length_nil, Nat.add_zero]
      rw [hFuelEq]
      rw [Expressions.InteractionSemantics.Block.openRun_cons]
      change
        Simulation.Interaction.ForwardRel
          StackStatementPreservation.FuelTruncated
          (StackStatementPreservation.ControlOpenOutcomeRel controlTargets
            returnNames ctx suffix returns)
          _
          (Simulation.Interaction.bind
            (Expressions.InteractionSemantics.Stmt.openRun targetProgram
              (targetExtra + targets.length + 1) (.call functionName)
              targetAfterArgs) _)
      simpa using hAfterCall

/-- The complete compiled call core preserves one canonical Functions call at
arbitrary sufficient target fuel. The callee capability is fuel-indexed private
plumbing for the recursive dispatcher, not a public compiler premise. -/
theorem corePreserves
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (controlTargets : StackSchedule.ControlTargets)
    (returnNames : List Name) (ctx : Locals.Ctx)
    (targets : List Name) (functionName : Name)
    (args : List (Functions.Expr 1)) (fn : Functions.FunDef)
    (argCode : Structured.Code) (writebackCode : List Expressions.Stmt)
    (hFind :
      Functions.Source.FunList.find? functionName sourceProgram.functions =
        some fn)
    (hLayoutNodup : ctx.layout.Nodup)
    (hTargetsNodup : targets.Nodup)
    (hTargetsLength : targets.length = fn.returns.length)
    (hTargetsLayout : ∀ name, name ∈ targets → name ∈ ctx.layout)
    (hArgScoped :
      Locals.Scope.ExprSeqScoped ctx.layout (Lower.argExprs args))
    (hArgSupported :
      Functions.InteractionSemantics.ArgList.OpenSupported args)
    (hArgCompile :
      Locals.ExprSeq.compileCode ctx 0 (Lower.argExprs args) = some argCode)
    (hWritebackCompile :
      Locals.Block.compileOpen ctx
          { stmts := Lower.assignReturnedTops targets } =
        some (writebackCode, ctx))
    (hCallee :
      ∀ (sourceFuel targetFuel : Nat)
        {suffix : List Word} {returns : List Structured.ReturnDest}
        {source sourceAfterArgs : Locals.Source.State}
        {target targetAfterArgs : Structured.RunState}
        {argValues : List Word},
        StateRel ctx.layout suffix returns source target →
        Locals.InteractionPreservation.Expr.ResultRel args.length
            source target (sourceAfterArgs, argValues) targetAfterArgs →
        Simulation.Interaction.ForwardRel
          StackStatementPreservation.FuelTruncated
          (OpenAttachedCallResultRel fn.returns.length
            target.evm.stack returns)
          (Functions.InteractionSemantics.FunDef.openRunBody sourceProgram
            fn argValues sourceFuel sourceAfterArgs)
          (Expressions.InteractionSemantics.Stmt.openRun targetProgram
            targetFuel (.call functionName) targetAfterArgs)) :
    StackStatementPreservation.ControlPointPreserves sourceProgram
      targetProgram controlTargets returnNames ctx ctx
      (.call targets functionName args)
      ([.code argCode] ++ (.call functionName :: writebackCode)) := by
  unfold StackStatementPreservation.ControlPointPreserves
  intro sourceCtx sourceFuel targetFuel suffix returns source target hFuel
    hRuntime hInitial
  cases sourceFuel with
  | zero =>
      unfold Functions.InteractionSemantics.Stmt.openRun
        Functions.Source.Canonical.Stmt.run
        Functions.Source.Effectful.Control.Stmt.run
      exact Simulation.Interaction.ForwardRel.truncated rfl
  | succ sourceFuel =>
      have hWritebackLength :=
        CallerWriteback.compileOpen_length ctx targets writebackCode
          hWritebackCompile
      have hCodeLength :
          ([Expressions.Stmt.code argCode] ++
            (Expressions.Stmt.call functionName :: writebackCode)).length =
            targets.length + 2 := by
        simp [hWritebackLength]
      have hLength := Expressions.TargetFuel.Covers.length_lt hFuel
      rw [hCodeLength] at hLength
      let targetExtra := targetFuel - targets.length - 3
      have hTargetEq :
          targetExtra + targets.length + 3 = targetFuel := by
        dsimp [targetExtra]
        omega
      have hCore :=
        core sourceProgram targetProgram sourceCtx controlTargets returnNames
          ctx sourceFuel targetExtra targets functionName args fn argCode
          writebackCode hFind hRuntime hLayoutNodup hTargetsNodup
          hTargetsLength hTargetsLayout hArgScoped hArgSupported hArgCompile
          hWritebackCompile hInitial (fun hArgResult =>
            hCallee sourceFuel
              (targetExtra + targets.length + 1) hInitial hArgResult)
      simpa [hTargetEq] using hCore

/-- Build a complete retained call point from the actual scheduler/lowerer and
ordinary Locals compiler equations. The returned retain artifact is computed by
the compiler and remains an existential conclusion. -/
theorem compiledOfCompilers
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (controlTargets : StackSchedule.ControlTargets)
    (returnNames : List Name)
    (targets : List Name) (functionName : Name)
    (args : List (Functions.Expr 1))
    (point : StackSchedule.Point)
    (lowered : List Locals.Stmt)
    (targetCtx finalCtx : Locals.Ctx)
    (code : List Expressions.Stmt)
    (lowerFuel : Nat)
    (hFunctions : lowerCtx.functions = sourceProgram.functions)
    (hLayoutNodup : targetCtx.layout.Nodup)
    (hTargetsLayout : ∀ name, name ∈ targets → name ∈ targetCtx.layout)
    (hArgScoped :
      Locals.Scope.ExprSeqScoped targetCtx.layout (Lower.argExprs args))
    (hArgSupported :
      Functions.InteractionSemantics.ArgList.OpenSupported args)
    (hRetainSource :
      ∀ {retain : AllocationLayout.Transition},
        point.retain? = some retain →
        targetCtx.layout = retain.source)
    (hLower :
      StackLowering.lowerPointFuel lowerFuel lowerCtx
          (.call targets functionName args) point = some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hCallee :
      ∀ (fn : Functions.FunDef),
        Functions.Source.FunList.find? functionName sourceProgram.functions =
            some fn →
        ∀ (sourceFuel targetFuel : Nat)
          {suffix : List Word} {returns : List Structured.ReturnDest}
          {source sourceAfterArgs : Locals.Source.State}
          {target targetAfterArgs : Structured.RunState}
          {argValues : List Word},
          StateRel targetCtx.layout suffix returns source target →
          Locals.InteractionPreservation.Expr.ResultRel args.length
              source target (sourceAfterArgs, argValues) targetAfterArgs →
          Simulation.Interaction.ForwardRel
            StackStatementPreservation.FuelTruncated
            (OpenAttachedCallResultRel fn.returns.length
              target.evm.stack returns)
            (Functions.InteractionSemantics.FunDef.openRunBody sourceProgram
              fn argValues sourceFuel sourceAfterArgs)
            (Expressions.InteractionSemantics.Stmt.openRun targetProgram
              targetFuel (.call functionName) targetAfterArgs)) :
    ∃ retain,
      point.retain? = some retain ∧
      StackStatementPreservation.CompiledControlPoint sourceProgram
        targetProgram controlTargets returnNames targetCtx finalCtx
        (.call targets functionName args) code retain.schedule.target := by
  obtain ⟨fn, retain, argCode, writebackCode, transitionCode, hFind,
      _hArgsLength, hTargetsLength, hTargetsNodup, _hAccess, _hFalls,
      _hRegions, hRetain, hArgCompile, hWritebackCompile,
      hTransitionCompile, hCode⟩ :=
    StackLoweringCompilation.callPoint_components hLower hCompile
  have hFind' :
      Functions.Source.FunList.find? functionName sourceProgram.functions =
        some fn := by
    rw [← hFunctions]
    exact hFind
  have hCore :=
    corePreserves sourceProgram targetProgram controlTargets returnNames
      targetCtx targets functionName args fn argCode writebackCode hFind'
      hLayoutNodup hTargetsNodup hTargetsLength hTargetsLayout hArgScoped
      hArgSupported hArgCompile hWritebackCompile (hCallee fn hFind')
  have hSource := hRetainSource hRetain
  have hCode' :
      code =
        ([.code argCode] ++ (.call functionName :: writebackCode)) ++
          transitionCode := by
    simpa [List.append_assoc] using hCode
  refine ⟨retain, hRetain, ?_⟩
  exact
    StackStatementPreservation.compiledControlThenTransition
      sourceProgram targetProgram controlTargets returnNames targetCtx
      finalCtx (.call targets functionName args) retain
      ([.code argCode] ++ (.call functionName :: writebackCode))
      transitionCode code hSource hTransitionCompile hCode' hCore

end CallPoint

namespace EntryMarker

theorem openRun
    (targetProgram : Expressions.Program) (targetFuel : Nat)
    (layout : Locals.Layout) (target : Structured.RunState)
    (hFuel : 2 ≤ targetFuel) :
    Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := [.code [.bindLocals 0 layout]] } target =
      Simulation.Interaction.pure (Structured.Outcome.regular target) := by
  have hCode :
      Structured.InteractionSemantics.Code.openRun
          [.bindLocals 0 layout] target = .done (.ok target) := by
    exact Locals.InteractionPreservation.Code.openRun_bindLocals 0 layout target
  simpa using
    Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
      targetProgram targetFuel _ target target hFuel hCode

end EntryMarker

namespace ReturnEpilogue

/-- Regular function fallthrough evaluates declared returns once and removes
the active frame while preserving exactly those values for call attachment. -/
theorem openRun
    (targetProgram : Expressions.Program) (targetExtra : Nat)
    (targetCtx : Locals.Ctx) (returnNames : List Name)
    (returnCode cleanup : Structured.Code)
    {source : Locals.Source.State} {target : Structured.RunState}
    {frame : Structured.ReturnDest}
    {callerReturns : List Structured.ReturnDest}
    (hFrameRetc : frame.retc = returnNames.length)
    (hAccess :
      StackAccess.ExprSeq.check? targetCtx.layout 0
          (StackLowering.returnWords returnNames) = some ())
    (hReturnCompile :
      Locals.ExprSeq.compileCode targetCtx 0
          (StackLowering.returnWords returnNames) = some returnCode)
    (hCleanup :
      targetCtx.cleanupToPreserving? returnNames.length 0 = some cleanup)
    (hInitial :
      StateRel targetCtx.layout [] (frame :: callerReturns) source target) :
    ∃ values finalTarget,
      Functions.Source.Store.lookupMany returnNames source.vars = some values ∧
      Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetExtra + 3) { stmts := [.code returnCode, .code cleanup] }
          target =
        Simulation.Interaction.pure
          (Structured.Outcome.regular finalTarget) ∧
      CallResultRel frame callerReturns
        (.returned source values) (.regular finalTarget) := by
  have hNamesLayout :
      ∀ name : Name, name ∈ returnNames → name ∈ targetCtx.layout := by
    intro name hName
    exact StackLowering.returnWords_names_mem_of_check hAccess hName
  obtain ⟨values, hLookup⟩ :=
    hInitial.lookupMany_of_subset hNamesLayout
  have hReturnRel :=
    StackExpressionPreservation.openEvalSeq_compileCode
      (StackLowering.returnWords returnNames) targetCtx
      (StackLowering.returnWords_localsScoped hNamesLayout)
      (StackStatementPreservation.returnWords_openSupported returnNames)
      hReturnCompile hInitial
  have hReturnEval :=
    StackStatementPreservation.returnWords_openEval
      returnNames source values hLookup
  rw [hReturnEval] at hReturnRel
  obtain ⟨targetAfterReturns, hReturnRun, hReturnDone⟩ :=
    Simulation.Interaction.Rel.done_left hReturnRel
  cases hReturnDone with
  | @ok sourceResult targetAfterReturns hReturnResult =>
      have hCleanupMany :
          Locals.Ctx.cleanupManyPreserving? targetCtx.layout.length
              returnNames.length = some cleanup := by
        unfold Locals.Ctx.cleanupToPreserving? at hCleanup
        simpa using hCleanup
      have hValuesLength : values.reverse.length = returnNames.length := by
        simpa using Functions.Source.Store.lookupMany_length hLookup
      have hDiscardedLength :
          (StackRelation.values source targetCtx.layout).length =
            targetCtx.layout.length := by
        simp [StackRelation.values]
      have hAfterStack :
          targetAfterReturns.evm.stack =
            values.reverse ++ StackRelation.values source targetCtx.layout := by
        rw [hReturnResult.stack, hInitial.stack]
        simp [List.append_assoc]
      obtain ⟨finalTarget, hCleanupRun, hFinalStack,
          hCleanupShared, hCleanupReturns⟩ :=
        Locals.InteractionCleanupPreservation.openRun_cleanupManyPreserving?
          (values := values.reverse)
          (discarded := StackRelation.values source targetCtx.layout)
          (suffix := []) (target := targetAfterReturns)
          hCleanupMany hValuesLength hDiscardedLength
          (by simpa using hAfterStack)
      have hFinalRel :
          StateRel returnNames.reverse [] (frame :: callerReturns)
            source finalTarget := by
        apply StateRel.of_lookupMany
        · rw [hCleanupShared, hReturnResult.shared]
        · exact hCleanupReturns.trans
            (hReturnResult.returns.trans hInitial.returns)
        · exact Functions.Source.Store.lookupMany_reverse hLookup
        · simpa using hFinalStack
      have hTargetRun :
          Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetExtra + 3)
              { stmts := [.code returnCode, .code cleanup] } target =
            Simulation.Interaction.pure
              (Structured.Outcome.regular finalTarget) := by
        have hReturnBlock :=
          Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
            targetProgram (targetExtra + 3) returnCode target
              targetAfterReturns (by omega) hReturnRun
        have hCleanupBlock :=
          Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
            targetProgram (targetExtra + 2) cleanup targetAfterReturns
              finalTarget (by omega) hCleanupRun
        change
          Expressions.InteractionSemantics.Block.openRun targetProgram
              (targetExtra + 3)
              { stmts :=
                  [Expressions.Stmt.code returnCode] ++
                    [Expressions.Stmt.code cleanup] } target = _
        rw [Expressions.InteractionSemantics.Block.openRun_append,
          hReturnBlock]
        simp only [Simulation.Interaction.bind_done_ok,
          Structured.Outcome.regular_mode,
          Structured.Outcome.regular_state, List.length_cons,
          List.length_nil, Nat.add_zero]
        simpa using hCleanupBlock
      exact
        ⟨values, finalTarget, hLookup, hTargetRun,
          CallResultRel.regular_of_stateRel hFrameRetc hLookup hFinalRel⟩

/-- A zero-return fallthrough emits no empty return-vector statement. The
ordinary preserving cleanup alone removes the active frame and returns `[]`. -/
theorem openRun_noReturns
    (targetProgram : Expressions.Program) (targetExtra : Nat)
    (targetCtx : Locals.Ctx) (cleanup : Structured.Code)
    {source : Locals.Source.State} {target : Structured.RunState}
    {frame : Structured.ReturnDest}
    {callerReturns : List Structured.ReturnDest}
    (hFrameRetc : frame.retc = 0)
    (hCleanup : targetCtx.cleanupToPreserving? 0 0 = some cleanup)
    (hInitial :
      StateRel targetCtx.layout [] (frame :: callerReturns) source target) :
    ∃ finalTarget,
      Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetExtra + 2) { stmts := [.code cleanup] } target =
        Simulation.Interaction.pure
          (Structured.Outcome.regular finalTarget) ∧
      CallResultRel frame callerReturns
        (.returned source []) (.regular finalTarget) := by
  have hCleanupMany :
      Locals.Ctx.cleanupManyPreserving? targetCtx.layout.length 0 =
        some cleanup := by
    unfold Locals.Ctx.cleanupToPreserving? at hCleanup
    simpa using hCleanup
  have hDiscardedLength :
      (StackRelation.values source targetCtx.layout).length =
        targetCtx.layout.length := by
    simp [StackRelation.values]
  obtain ⟨finalTarget, hCleanupRun, hFinalStack,
      hCleanupShared, hCleanupReturns⟩ :=
    Locals.InteractionCleanupPreservation.openRun_cleanupManyPreserving?
      (values := [])
      (discarded := StackRelation.values source targetCtx.layout)
      (suffix := []) (target := target) hCleanupMany (by simp)
      hDiscardedLength (by simpa using hInitial.stack)
  have hLookup :
      Functions.Source.Store.lookupMany [] source.vars = some [] := rfl
  have hFinalRel :
      StateRel [] [] (frame :: callerReturns) source finalTarget := by
    apply StateRel.of_lookupMany
    · exact hCleanupShared.trans hInitial.shared
    · exact hCleanupReturns.trans hInitial.returns
    · exact hLookup
    · simpa using hFinalStack
  have hTargetRun :
      Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetExtra + 2) { stmts := [.code cleanup] } target =
        Simulation.Interaction.pure
          (Structured.Outcome.regular finalTarget) := by
    exact
      Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code_done
        targetProgram (targetExtra + 2) cleanup target finalTarget
          (by omega) hCleanupRun
  exact
    ⟨finalTarget, hTargetRun,
      CallResultRel.regular_of_stateRel (returnNames := []) (values := [])
        hFrameRetc hLookup hFinalRel⟩

end ReturnEpilogue

namespace Function

/-- One initialized function body is preserved through its scheduled body and
ordinary fallthrough return epilogue. The recursive body theorem is an
adjacent private input; the public program theorem discharges it by fuel. -/
theorem openRunBody_afterPrelude_of_run
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (args : List Word)
    (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (targetCtx finalCtx : Locals.Ctx)
    (targetBody : Expressions.Block)
    (returnCode cleanup : Structured.Code)
    {frame : Structured.ReturnDest}
    {callerReturns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (hFrameRetc : frame.retc = fn.returns.length)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hBodyRun :
      Simulation.Interaction.ForwardRel
        StackStatementPreservation.FuelTruncated
        (StackStatementPreservation.ControlOpenOutcomeRel {}
          fn.returns finalCtx [] (frame :: callerReturns))
        (Functions.InteractionSemantics.Block.openRun sourceProgram
          (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
          (CalleeEntry.sourceState sourceAfterArgs fn paramStore))
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel targetBody target))
    (hReturnAccess :
      StackAccess.ExprSeq.check? finalCtx.layout 0
          (StackLowering.returnWords fn.returns) = some ())
    (hReturnCompile :
      Locals.ExprSeq.compileCode finalCtx 0
          (StackLowering.returnWords fn.returns) = some returnCode)
    (hCleanup :
      finalCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code returnCode, .code cleanup])) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel frame callerReturns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            targetBody.stmts ++ [.code returnCode, .code cleanup] } target) := by
  rcases targetBody with ⟨targetStmts⟩
  unfold Functions.InteractionSemantics.FunDef.openRunBody
    Functions.Source.Canonical.FunDef.runBody
    Functions.Source.Effectful.Control.FunDef.runBody
  rw [hInsert]
  simp only [Option.elim_some, Simulation.Interaction.pure,
    Simulation.Interaction.bind_done_ok]
  change
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel frame callerReturns)
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun sourceProgram
          (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
          (CalleeEntry.sourceState sourceAfterArgs fn paramStore)) _)
      _
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind hBodyRun
  intro sourceResult targetResult hResult
  cases hResult with
  | @regular source _sourceCtx targetAfter _hFinalRuntime hState =>
      simp only [Locals.Source.Effectful.Outcome.regular,
        Structured.Outcome.regular_mode,
        Structured.Outcome.regular_state,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.vars, id_eq]
      have hTailFuel :=
        Expressions.TargetFuel.Covers.tail_after_append hFuel
      have hTailLength := Expressions.TargetFuel.Covers.length_lt hTailFuel
      have hResidual : 3 ≤ targetFuel - targetStmts.length := by
        simpa using hTailLength
      let extra := targetFuel - targetStmts.length - 3
      have hResidualEq :
          targetFuel - targetStmts.length = extra + 3 := by
        dsimp [extra]
        omega
      obtain ⟨values, finalTarget, hLookup, hTargetRun, hCallRel⟩ :=
        ReturnEpilogue.openRun targetProgram extra finalCtx fn.returns
          returnCode cleanup hFrameRetc hReturnAccess hReturnCompile hCleanup
          hState
      rw [hResidualEq, hTargetRun]
      simp only [Simulation.Interaction.pure]
      rw [hLookup]
      exact Simulation.Interaction.ForwardRel.done
        (Simulation.Interaction.ExceptRel.ok hCallRel)
  | brk hTarget _hState => simp at hTarget
  | cont hTarget _hState => simp at hTarget
  | @leave source _sourceCtx targetAfter hState =>
      simp only [Locals.Source.Effectful.Outcome.leave,
        Structured.Outcome.leave_mode,
        Structured.Outcome.leave_state,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.vars, id_eq]
      have hNames :
          ∀ name, name ∈ fn.returns → name ∈ fn.returns.reverse := by
        intro name hName
        simpa using hName
      obtain ⟨values, hLookup⟩ := hState.lookupMany_of_subset hNames
      rw [hLookup]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact CallResultRel.leave_of_stateRel hFrameRetc hLookup hState
  | @halt kind source _sourceCtx targetAfter hShared =>
      simp only [Locals.Source.Effectful.Outcome.halt,
        Structured.Outcome.halt_mode,
        Structured.Outcome.halt_state]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact CallResultRel.halt hShared.symm

theorem openRunBody_afterPrelude
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (args : List Word)
    (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (targetCtx finalCtx : Locals.Ctx)
    (targetBody : Expressions.Block)
    (returnCode cleanup : Structured.Code)
    {frame : Structured.ReturnDest}
    {callerReturns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (hFrameRetc : frame.retc = fn.returns.length)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hBody :
      StackStatementPreservation.ControlBlockPreserves
        sourceProgram targetProgram {} fn.returns targetCtx finalCtx
        fn.body targetBody)
    (hRuntime :
      StackStatementPreservation.RuntimeCtxCovers
        (Functions.Source.Effectful.FunDef.bodyCtx fn) targetCtx {}
        fn.returns (frame :: callerReturns))
    (hReturnAccess :
      StackAccess.ExprSeq.check? finalCtx.layout 0
          (StackLowering.returnWords fn.returns) = some ())
    (hReturnCompile :
      Locals.ExprSeq.compileCode finalCtx 0
          (StackLowering.returnWords fn.returns) = some returnCode)
    (hCleanup :
      finalCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code returnCode, .code cleanup]))
    (hInitial :
      StateRel targetCtx.layout [] (frame :: callerReturns)
        (CalleeEntry.sourceState sourceAfterArgs fn paramStore) target) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel frame callerReturns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts :=
            targetBody.stmts ++ [.code returnCode, .code cleanup] } target) := by
  have hBodyFuel :=
    Expressions.TargetFuel.Covers.head_of_append hFuel
  have hBodyRun :=
    hBody (Functions.Source.Effectful.FunDef.bodyCtx fn)
      sourceFuel targetFuel hBodyFuel hRuntime hInitial
  exact
    openRunBody_afterPrelude_of_run sourceProgram targetProgram fn args
      paramStore sourceAfterArgs sourceFuel targetFuel targetCtx finalCtx
      targetBody returnCode cleanup hFrameRetc hInsert hBodyRun hReturnAccess
      hReturnCompile hCleanup hFuel

/-- Zero-return specialization of `openRunBody_afterPrelude` matching the
instruction-free return-vector phase emitted by `StackLowering`. -/
theorem openRunBody_afterPrelude_noReturns_of_run
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (args : List Word)
    (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (targetCtx finalCtx : Locals.Ctx)
    (targetBody : Expressions.Block)
    (cleanup : Structured.Code)
    {frame : Structured.ReturnDest}
    {callerReturns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (hReturns : fn.returns = [])
    (hFrameRetc : frame.retc = 0)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hBodyRun :
      Simulation.Interaction.ForwardRel
        StackStatementPreservation.FuelTruncated
        (StackStatementPreservation.ControlOpenOutcomeRel {}
          fn.returns finalCtx [] (frame :: callerReturns))
        (Functions.InteractionSemantics.Block.openRun sourceProgram
          (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
          (CalleeEntry.sourceState sourceAfterArgs fn paramStore))
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          targetFuel targetBody target))
    (hCleanup : finalCtx.cleanupToPreserving? 0 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code cleanup])) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel frame callerReturns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := targetBody.stmts ++ [.code cleanup] } target) := by
  rcases targetBody with ⟨targetStmts⟩
  unfold Functions.InteractionSemantics.FunDef.openRunBody
    Functions.Source.Canonical.FunDef.runBody
    Functions.Source.Effectful.Control.FunDef.runBody
  rw [hInsert]
  simp only [Option.elim_some, Simulation.Interaction.pure,
    Simulation.Interaction.bind_done_ok]
  change
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel frame callerReturns)
      (Simulation.Interaction.bind
        (Functions.InteractionSemantics.Block.openRun sourceProgram
          (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
          (CalleeEntry.sourceState sourceAfterArgs fn paramStore)) _)
      _
  rw [Expressions.InteractionSemantics.Block.openRun_append]
  apply Simulation.Interaction.ForwardRel.bind hBodyRun
  intro sourceResult targetResult hResult
  cases hResult with
  | @regular source _sourceCtx targetAfter _hFinalRuntime hState =>
      simp only [Locals.Source.Effectful.Outcome.regular,
        Structured.Outcome.regular_mode,
        Structured.Outcome.regular_state,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.vars, id_eq]
      have hTailFuel :=
        Expressions.TargetFuel.Covers.tail_after_append hFuel
      have hTailLength := Expressions.TargetFuel.Covers.length_lt hTailFuel
      have hResidual : 2 ≤ targetFuel - targetStmts.length := by
        simpa using hTailLength
      let extra := targetFuel - targetStmts.length - 2
      have hResidualEq :
          targetFuel - targetStmts.length = extra + 2 := by
        dsimp [extra]
        omega
      obtain ⟨finalTarget, hTargetRun, hCallRel⟩ :=
        ReturnEpilogue.openRun_noReturns targetProgram extra finalCtx cleanup
          hFrameRetc hCleanup hState
      rw [hResidualEq, hTargetRun]
      simp only [Simulation.Interaction.pure]
      have hLookup :
          Functions.Source.Store.lookupMany fn.returns source.vars =
            some [] := by
        rw [hReturns]
        rfl
      rw [hLookup]
      exact Simulation.Interaction.ForwardRel.done
        (Simulation.Interaction.ExceptRel.ok hCallRel)
  | brk hTarget _hState => simp at hTarget
  | cont hTarget _hState => simp at hTarget
  | @leave source _sourceCtx targetAfter hState =>
      simp only [Locals.Source.Effectful.Outcome.leave,
        Structured.Outcome.leave_mode,
        Structured.Outcome.leave_state,
        Functions.InteractionSemantics.stateModel,
        Locals.InteractionSemantics.stateModel,
        Locals.Source.Effectful.Ordinary.stateModel,
        Locals.Source.Effectful.StateModel.vars, id_eq]
      have hLookup :
          Functions.Source.Store.lookupMany fn.returns source.vars =
            some [] := by
        rw [hReturns]
        rfl
      rw [hLookup]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact CallResultRel.leave_of_stateRel
        (by simpa [hReturns] using hFrameRetc) hLookup hState
  | @halt kind source _sourceCtx targetAfter hShared =>
      simp only [Locals.Source.Effectful.Outcome.halt,
        Structured.Outcome.halt_mode,
        Structured.Outcome.halt_state]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact CallResultRel.halt hShared.symm

theorem openRunBody_afterPrelude_noReturns
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (args : List Word)
    (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (targetCtx finalCtx : Locals.Ctx)
    (targetBody : Expressions.Block)
    (cleanup : Structured.Code)
    {frame : Structured.ReturnDest}
    {callerReturns : List Structured.ReturnDest}
    {target : Structured.RunState}
    (hReturns : fn.returns = [])
    (hFrameRetc : frame.retc = 0)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hBody :
      StackStatementPreservation.ControlBlockPreserves
        sourceProgram targetProgram {} fn.returns targetCtx finalCtx
        fn.body targetBody)
    (hRuntime :
      StackStatementPreservation.RuntimeCtxCovers
        (Functions.Source.Effectful.FunDef.bodyCtx fn) targetCtx {}
        fn.returns (frame :: callerReturns))
    (hCleanup : finalCtx.cleanupToPreserving? 0 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code cleanup]))
    (hInitial :
      StateRel targetCtx.layout [] (frame :: callerReturns)
        (CalleeEntry.sourceState sourceAfterArgs fn paramStore) target) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel frame callerReturns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Block.openRun targetProgram targetFuel
        { stmts := targetBody.stmts ++ [.code cleanup] } target) := by
  have hBodyFuel :=
    Expressions.TargetFuel.Covers.head_of_append hFuel
  have hBodyRun :=
    hBody (Functions.Source.Effectful.FunDef.bodyCtx fn)
      sourceFuel targetFuel hBodyFuel hRuntime hInitial
  exact
    openRunBody_afterPrelude_noReturns_of_run sourceProgram targetProgram fn
      args paramStore sourceAfterArgs sourceFuel targetFuel targetCtx finalCtx
      targetBody cleanup hReturns hFrameRetc hInsert hBodyRun hCleanup hFuel

/-- Preserve a whole function body from the real call-created entry state,
including the metadata marker and compiler-generated zero-return prelude. -/
theorem openRunBody_fromEntry_of_bodyRun
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (args : List Word)
    (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (finalCtx : Locals.Ctx)
    (returnPreludeCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (returnCode cleanup : Structured.Code)
    {callerTarget : Structured.RunState}
    {callerStack : List Word}
    (hTargetFuel : 0 < targetFuel)
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hShared :
      callerTarget.evm.toSharedState = sourceAfterArgs.shared)
    (hReturnPreludeCompile :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length))
    (hBodyRun :
      ∀ {targetAfterPrelude : Structured.RunState},
        StateRel (StackLowering.functionBodyLayout fn) []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns)
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore)
            targetAfterPrelude →
        Simulation.Interaction.ForwardRel
          StackStatementPreservation.FuelTruncated
          (StackStatementPreservation.ControlOpenOutcomeRel {}
            fn.returns finalCtx []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns))
          (Functions.InteractionSemantics.Block.openRun sourceProgram
            (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore))
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel targetBody targetAfterPrelude))
    (hReturnAccess :
      StackAccess.ExprSeq.check? finalCtx.layout 0
          (StackLowering.returnWords fn.returns) = some ())
    (hReturnCompile :
      Locals.ExprSeq.compileCode finalCtx 0
          (StackLowering.returnWords fn.returns) = some returnCode)
    (hCleanup :
      finalCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code returnCode, .code cleanup])) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel
        { callerStack := callerStack, retc := fn.returns.length }
        callerTarget.returns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetFuel + fn.returns.length + 1)
        { stmts :=
            [.code [.bindLocals 0 fn.params.reverse]] ++
              (returnPreludeCode ++
                (targetBody.stmts ++ [.code returnCode, .code cleanup])) }
        (CalleeEntry.targetState callerTarget args.reverse callerStack
          fn.returns.length)) := by
  let entryCtx :=
    Locals.Ctx.procEntryWithLayoutAndRetc
      fn.params.reverse fn.returns.length
  let bodyCtx :=
    Locals.Ctx.procEntryWithLayoutAndRetc
      (StackLowering.functionBodyLayout fn) fn.returns.length
  let sourceEntry := CalleeEntry.sourceState sourceAfterArgs fn paramStore
  let targetEntry :=
    CalleeEntry.targetState callerTarget args.reverse callerStack
      fn.returns.length
  have hEntryRel :
      StateRel fn.params.reverse []
        ({ callerStack := callerStack, retc := fn.returns.length } ::
          callerTarget.returns)
        sourceEntry targetEntry := by
    exact CalleeEntry.stateRel hSignature hInsert hShared rfl
  have hNodup :
      (fn.returns.reverse ++ entryCtx.layout).Nodup := by
    have hParts := List.nodup_append.mp hSignature
    change (fn.returns.reverse ++ fn.params.reverse).Nodup
    have hReturnsReverse : fn.returns.reverse.Nodup := by
      simpa using hParts.1
    have hParamsReverse : fn.params.reverse.Nodup := by
      simpa using hParts.2.1
    apply List.nodup_append.mpr
    refine ⟨hReturnsReverse, hParamsReverse, ?_⟩
    intro left hLeft right hRight hEq
    exact hParts.2.2 left (by simpa using hLeft)
      right (by simpa using hRight) hEq
  have hZero :
      ∀ name, name ∈ fn.returns → sourceEntry.vars name = some Lower.zero := by
    intro name hName
    simpa [sourceEntry, CalleeEntry.sourceState,
      Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel] using
      Functions.Source.Store.initReturns_apply_of_mem
        (List.nodup_append.mp hSignature).1 hName
  obtain ⟨preludeCode, preludeFinalCtx, targetAfterPrelude,
      hPreludeCompile, hPreludeLayout, hPreludeLength, _hPreludeOnly,
      hPreludeRun, hPreludeRel⟩ :=
    ReturnPrelude.compileOpenRun_of_fuel targetProgram fn.returns entryCtx
      (targetFuel + fn.returns.length) (by omega) hNodup hZero hEntryRel
  have hPreludeEq : preludeCode = returnPreludeCode := by
    rw [hReturnPreludeCompile] at hPreludeCompile
    exact (congrArg Prod.fst (Option.some.inj hPreludeCompile)).symm
  have hPreludeCtxEq : preludeFinalCtx = bodyCtx := by
    rw [hReturnPreludeCompile] at hPreludeCompile
    exact (congrArg Prod.snd (Option.some.inj hPreludeCompile)).symm
  subst preludeCode
  subst preludeFinalCtx
  have hExactBodyRun := hBodyRun (by
    simpa [bodyCtx, StackLowering.functionBodyLayout] using hPreludeRel)
  have hAfter :=
    openRunBody_afterPrelude_of_run sourceProgram targetProgram fn args paramStore
      sourceAfterArgs sourceFuel targetFuel bodyCtx finalCtx targetBody
      returnCode cleanup rfl hInsert hExactBodyRun hReturnAccess
      hReturnCompile hCleanup hFuel
  have hEntryRun :=
    EntryMarker.openRun targetProgram
      (targetFuel + fn.returns.length + 1) fn.params.reverse targetEntry
      (by omega)
  change Simulation.Interaction.ForwardRel _ _ _ _
  rw [Expressions.InteractionSemantics.Block.openRun_append, hEntryRun]
  simp only [Simulation.Interaction.pure,
    Simulation.Interaction.bind_done_ok,
    Structured.Outcome.regular_mode, Structured.Outcome.regular_state,
    List.length_cons, List.length_nil, Nat.add_zero]
  rw [show targetFuel + fn.returns.length + 1 - 1 =
      targetFuel + fn.returns.length by omega]
  rw [Expressions.InteractionSemantics.Block.openRun_append, hPreludeRun]
  simp only [Simulation.Interaction.pure,
    Simulation.Interaction.bind_done_ok,
    Structured.Outcome.regular_mode, Structured.Outcome.regular_state]
  have hResidual :
      targetFuel + fn.returns.length - returnPreludeCode.length =
        targetFuel := by
    omega
  rw [hResidual]
  exact hAfter

theorem openRunBody_fromEntry
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (args : List Word)
    (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (finalCtx : Locals.Ctx)
    (returnPreludeCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (returnCode cleanup : Structured.Code)
    {callerTarget : Structured.RunState}
    {callerStack : List Word}
    (hTargetFuel : 0 < targetFuel)
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hShared :
      callerTarget.evm.toSharedState = sourceAfterArgs.shared)
    (hReturnPreludeCompile :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length))
    (hBody :
      StackStatementPreservation.ControlBlockPreserves
        sourceProgram targetProgram {} fn.returns
        (Locals.Ctx.procEntryWithLayoutAndRetc
          (StackLowering.functionBodyLayout fn) fn.returns.length)
        finalCtx fn.body targetBody)
    (hReturnAccess :
      StackAccess.ExprSeq.check? finalCtx.layout 0
          (StackLowering.returnWords fn.returns) = some ())
    (hReturnCompile :
      Locals.ExprSeq.compileCode finalCtx 0
          (StackLowering.returnWords fn.returns) = some returnCode)
    (hCleanup :
      finalCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code returnCode, .code cleanup])) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel
        { callerStack := callerStack, retc := fn.returns.length }
        callerTarget.returns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetFuel + fn.returns.length + 1)
        { stmts :=
            [.code [.bindLocals 0 fn.params.reverse]] ++
              (returnPreludeCode ++
                (targetBody.stmts ++ [.code returnCode, .code cleanup])) }
        (CalleeEntry.targetState callerTarget args.reverse callerStack
          fn.returns.length)) := by
  have hBodyFuel := Expressions.TargetFuel.Covers.head_of_append hFuel
  have hRuntime :=
    CalleeEntry.runtimeCtx fn
      { callerStack := callerStack, retc := fn.returns.length }
      callerTarget.returns
  apply openRunBody_fromEntry_of_bodyRun sourceProgram targetProgram fn args
    paramStore sourceAfterArgs sourceFuel targetFuel finalCtx
    returnPreludeCode targetBody returnCode cleanup hTargetFuel hSignature
    hInsert hShared hReturnPreludeCompile
  · intro targetAfter hInitial
    exact hBody (Functions.Source.Effectful.FunDef.bodyCtx fn)
      sourceFuel targetFuel hBodyFuel hRuntime hInitial
  · exact hReturnAccess
  · exact hReturnCompile
  · exact hCleanup
  · exact hFuel

theorem openRunBody_fromEntry_noReturns_of_bodyRun
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (args : List Word)
    (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (finalCtx : Locals.Ctx)
    (returnPreludeCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (cleanup : Structured.Code)
    {callerTarget : Structured.RunState}
    {callerStack : List Word}
    (hTargetFuel : 0 < targetFuel)
    (hReturns : fn.returns = [])
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hShared :
      callerTarget.evm.toSharedState = sourceAfterArgs.shared)
    (hReturnPreludeCompile :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length))
    (hBodyRun :
      ∀ {targetAfterPrelude : Structured.RunState},
        StateRel (StackLowering.functionBodyLayout fn) []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns)
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore)
            targetAfterPrelude →
        Simulation.Interaction.ForwardRel
          StackStatementPreservation.FuelTruncated
          (StackStatementPreservation.ControlOpenOutcomeRel {}
            fn.returns finalCtx []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns))
          (Functions.InteractionSemantics.Block.openRun sourceProgram
            (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore))
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel targetBody targetAfterPrelude))
    (hCleanup : finalCtx.cleanupToPreserving? 0 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code cleanup])) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel
        { callerStack := callerStack, retc := fn.returns.length }
        callerTarget.returns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetFuel + fn.returns.length + 1)
        { stmts :=
            [.code [.bindLocals 0 fn.params.reverse]] ++
              (returnPreludeCode ++
                (targetBody.stmts ++ [.code cleanup])) }
        (CalleeEntry.targetState callerTarget args.reverse callerStack
          fn.returns.length)) := by
  let entryCtx :=
    Locals.Ctx.procEntryWithLayoutAndRetc
      fn.params.reverse fn.returns.length
  let bodyCtx :=
    Locals.Ctx.procEntryWithLayoutAndRetc
      (StackLowering.functionBodyLayout fn) fn.returns.length
  let sourceEntry := CalleeEntry.sourceState sourceAfterArgs fn paramStore
  let targetEntry :=
    CalleeEntry.targetState callerTarget args.reverse callerStack
      fn.returns.length
  have hEntryRel :
      StateRel fn.params.reverse []
        ({ callerStack := callerStack, retc := fn.returns.length } ::
          callerTarget.returns)
        sourceEntry targetEntry := by
    exact CalleeEntry.stateRel hSignature hInsert hShared rfl
  have hNodup :
      (fn.returns.reverse ++ entryCtx.layout).Nodup := by
    have hParts := List.nodup_append.mp hSignature
    change (fn.returns.reverse ++ fn.params.reverse).Nodup
    have hReturnsReverse : fn.returns.reverse.Nodup := by
      simpa using hParts.1
    have hParamsReverse : fn.params.reverse.Nodup := by
      simpa using hParts.2.1
    apply List.nodup_append.mpr
    refine ⟨hReturnsReverse, hParamsReverse, ?_⟩
    intro left hLeft right hRight hEq
    exact hParts.2.2 left (by simpa using hLeft)
      right (by simpa using hRight) hEq
  have hZero :
      ∀ name, name ∈ fn.returns → sourceEntry.vars name = some Lower.zero := by
    intro name hName
    simpa [sourceEntry, CalleeEntry.sourceState,
      Functions.InteractionSemantics.stateModel,
      Locals.InteractionSemantics.stateModel,
      Locals.Source.Effectful.Ordinary.stateModel] using
      Functions.Source.Store.initReturns_apply_of_mem
        (List.nodup_append.mp hSignature).1 hName
  obtain ⟨preludeCode, preludeFinalCtx, targetAfterPrelude,
      hPreludeCompile, hPreludeLayout, hPreludeLength, _hPreludeOnly,
      hPreludeRun, hPreludeRel⟩ :=
    ReturnPrelude.compileOpenRun_of_fuel targetProgram fn.returns entryCtx
      (targetFuel + fn.returns.length) (by omega) hNodup hZero hEntryRel
  have hPreludeEq : preludeCode = returnPreludeCode := by
    rw [hReturnPreludeCompile] at hPreludeCompile
    exact (congrArg Prod.fst (Option.some.inj hPreludeCompile)).symm
  have hPreludeCtxEq : preludeFinalCtx = bodyCtx := by
    rw [hReturnPreludeCompile] at hPreludeCompile
    exact (congrArg Prod.snd (Option.some.inj hPreludeCompile)).symm
  subst preludeCode
  subst preludeFinalCtx
  have hExactBodyRun := hBodyRun (by
    simpa [bodyCtx, StackLowering.functionBodyLayout] using hPreludeRel)
  have hAfter :=
    openRunBody_afterPrelude_noReturns_of_run sourceProgram targetProgram fn args
      paramStore sourceAfterArgs sourceFuel targetFuel bodyCtx finalCtx
      targetBody cleanup hReturns (by simp [hReturns]) hInsert hExactBodyRun
      hCleanup hFuel
  have hEntryRun :=
    EntryMarker.openRun targetProgram
      (targetFuel + fn.returns.length + 1) fn.params.reverse targetEntry
      (by omega)
  change Simulation.Interaction.ForwardRel _ _ _ _
  rw [Expressions.InteractionSemantics.Block.openRun_append, hEntryRun]
  simp only [Simulation.Interaction.pure,
    Simulation.Interaction.bind_done_ok,
    Structured.Outcome.regular_mode, Structured.Outcome.regular_state,
    List.length_cons, List.length_nil, Nat.add_zero]
  rw [show targetFuel + fn.returns.length + 1 - 1 =
      targetFuel + fn.returns.length by omega]
  rw [Expressions.InteractionSemantics.Block.openRun_append, hPreludeRun]
  simp only [Simulation.Interaction.pure,
    Simulation.Interaction.bind_done_ok,
    Structured.Outcome.regular_mode, Structured.Outcome.regular_state]
  have hResidual :
      targetFuel + fn.returns.length - returnPreludeCode.length =
        targetFuel := by
    omega
  rw [hResidual]
  exact hAfter

theorem openRunBody_fromEntry_noReturns
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (args : List Word)
    (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (finalCtx : Locals.Ctx)
    (returnPreludeCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (cleanup : Structured.Code)
    {callerTarget : Structured.RunState}
    {callerStack : List Word}
    (hTargetFuel : 0 < targetFuel)
    (hReturns : fn.returns = [])
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hShared :
      callerTarget.evm.toSharedState = sourceAfterArgs.shared)
    (hReturnPreludeCompile :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length))
    (hBody :
      StackStatementPreservation.ControlBlockPreserves
        sourceProgram targetProgram {} fn.returns
        (Locals.Ctx.procEntryWithLayoutAndRetc
          (StackLowering.functionBodyLayout fn) fn.returns.length)
        finalCtx fn.body targetBody)
    (hCleanup : finalCtx.cleanupToPreserving? 0 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code cleanup])) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenCallResultRel
        { callerStack := callerStack, retc := fn.returns.length }
        callerTarget.returns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Block.openRun targetProgram
        (targetFuel + fn.returns.length + 1)
        { stmts :=
            [.code [.bindLocals 0 fn.params.reverse]] ++
              (returnPreludeCode ++
                (targetBody.stmts ++ [.code cleanup])) }
        (CalleeEntry.targetState callerTarget args.reverse callerStack
          fn.returns.length)) := by
  have hBodyFuel := Expressions.TargetFuel.Covers.head_of_append hFuel
  have hRuntime :=
    CalleeEntry.runtimeCtx fn
      { callerStack := callerStack, retc := fn.returns.length }
      callerTarget.returns
  apply openRunBody_fromEntry_noReturns_of_bodyRun sourceProgram targetProgram
    fn args paramStore sourceAfterArgs sourceFuel targetFuel finalCtx
    returnPreludeCode targetBody cleanup hTargetFuel hReturns hSignature
    hInsert hShared hReturnPreludeCompile
  · intro targetAfter hInitial
    exact hBody (Functions.Source.Effectful.FunDef.bodyCtx fn)
      sourceFuel targetFuel hBodyFuel hRuntime hInitial
  · exact hCleanup
  · exact hFuel

theorem openRunBody_attached_of_bodyRun
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (proc : Expressions.Proc)
    (args : List Word) (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (finalCtx : Locals.Ctx)
    (returnPreludeCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (returnCode cleanup : Structured.Code)
    {callerTarget : Structured.RunState}
    {callerStack : List Word}
    (hTargetFuel : 0 < targetFuel)
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hLookup :
      Expressions.EffectSemantics.ProcList.lookup?
          proc.name targetProgram.procs = some proc)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc callerTarget.evm.stack =
        some (args.reverse, callerStack))
    (hRetc : proc.retc = fn.returns.length)
    (hShared :
      callerTarget.evm.toSharedState = sourceAfterArgs.shared)
    (hProcBody :
      proc.body =
        { stmts :=
            [.code [.bindLocals 0 fn.params.reverse]] ++
              (returnPreludeCode ++
                (targetBody.stmts ++ [.code returnCode, .code cleanup])) })
    (hReturnPreludeCompile :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length))
    (hBodyRun :
      ∀ {targetAfterPrelude : Structured.RunState},
        StateRel (StackLowering.functionBodyLayout fn) []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns)
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore)
            targetAfterPrelude →
        Simulation.Interaction.ForwardRel
          StackStatementPreservation.FuelTruncated
          (StackStatementPreservation.ControlOpenOutcomeRel {}
            fn.returns finalCtx []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns))
          (Functions.InteractionSemantics.Block.openRun sourceProgram
            (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore))
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel targetBody targetAfterPrelude))
    (hReturnAccess :
      StackAccess.ExprSeq.check? finalCtx.layout 0
          (StackLowering.returnWords fn.returns) = some ())
    (hReturnCompile :
      Locals.ExprSeq.compileCode finalCtx 0
          (StackLowering.returnWords fn.returns) = some returnCode)
    (hCleanup :
      finalCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code returnCode, .code cleanup])) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenAttachedCallResultRel proc.retc callerStack callerTarget.returns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Stmt.openRun targetProgram
        (targetFuel + fn.returns.length + 2) (.call proc.name)
        callerTarget) := by
  have hBodyRun :=
    openRunBody_fromEntry_of_bodyRun sourceProgram targetProgram fn args paramStore
      sourceAfterArgs sourceFuel targetFuel finalCtx returnPreludeCode
      targetBody returnCode cleanup (callerTarget := callerTarget)
      (callerStack := callerStack) hTargetFuel hSignature hInsert hShared
      hReturnPreludeCompile hBodyRun hReturnAccess hReturnCompile hCleanup hFuel
  rw [← hProcBody] at hBodyRun
  have hBodyRun' :
      Simulation.Interaction.ForwardRel
        StackStatementPreservation.FuelTruncated
        (OpenCallResultRel
          { callerStack := callerStack, retc := proc.retc }
          callerTarget.returns)
        (Functions.InteractionSemantics.FunDef.openRunBody
          sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetFuel + fn.returns.length + 1) proc.body
          (CalleeEntry.targetState callerTarget args.reverse callerStack
            proc.retc)) := by
    simpa [hRetc] using hBodyRun
  have hAttached :=
    CallAttachment.of_body hLookup hSplit hBodyRun'
  simpa [hRetc, Nat.add_assoc] using hAttached

theorem openRunBody_attached_noReturns_of_bodyRun
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (proc : Expressions.Proc)
    (args : List Word) (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (finalCtx : Locals.Ctx)
    (returnPreludeCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (cleanup : Structured.Code)
    {callerTarget : Structured.RunState}
    {callerStack : List Word}
    (hTargetFuel : 0 < targetFuel)
    (hReturns : fn.returns = [])
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hLookup :
      Expressions.EffectSemantics.ProcList.lookup?
          proc.name targetProgram.procs = some proc)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc callerTarget.evm.stack =
        some (args.reverse, callerStack))
    (hRetc : proc.retc = fn.returns.length)
    (hShared :
      callerTarget.evm.toSharedState = sourceAfterArgs.shared)
    (hProcBody :
      proc.body =
        { stmts :=
            [.code [.bindLocals 0 fn.params.reverse]] ++
              (returnPreludeCode ++
                (targetBody.stmts ++ [.code cleanup])) })
    (hReturnPreludeCompile :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length))
    (hBodyRun :
      ∀ {targetAfterPrelude : Structured.RunState},
        StateRel (StackLowering.functionBodyLayout fn) []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns)
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore)
            targetAfterPrelude →
        Simulation.Interaction.ForwardRel
          StackStatementPreservation.FuelTruncated
          (StackStatementPreservation.ControlOpenOutcomeRel {}
            fn.returns finalCtx []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns))
          (Functions.InteractionSemantics.Block.openRun sourceProgram
            (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore))
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel targetBody targetAfterPrelude))
    (hCleanup : finalCtx.cleanupToPreserving? 0 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++ [.code cleanup])) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenAttachedCallResultRel proc.retc callerStack callerTarget.returns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Stmt.openRun targetProgram
        (targetFuel + fn.returns.length + 2) (.call proc.name)
        callerTarget) := by
  have hBodyRun :=
    openRunBody_fromEntry_noReturns_of_bodyRun sourceProgram targetProgram fn args
      paramStore sourceAfterArgs sourceFuel targetFuel finalCtx
      returnPreludeCode targetBody cleanup (callerTarget := callerTarget)
      (callerStack := callerStack) hTargetFuel hReturns hSignature hInsert
      hShared hReturnPreludeCompile hBodyRun hCleanup hFuel
  rw [← hProcBody] at hBodyRun
  have hBodyRun' :
      Simulation.Interaction.ForwardRel
        StackStatementPreservation.FuelTruncated
        (OpenCallResultRel
          { callerStack := callerStack, retc := proc.retc }
          callerTarget.returns)
        (Functions.InteractionSemantics.FunDef.openRunBody
          sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
        (Expressions.InteractionSemantics.Block.openRun targetProgram
          (targetFuel + fn.returns.length + 1) proc.body
          (CalleeEntry.targetState callerTarget args.reverse callerStack
            proc.retc)) := by
    simpa [hRetc] using hBodyRun
  have hAttached := CallAttachment.of_body hLookup hSplit hBodyRun'
  simpa [hRetc, Nat.add_assoc] using hAttached

/-- Uniform semantic interface for the compiler-owned optional return-code
phase. `none` is permitted exactly for zero-return procedures and emits no
target statement. -/
theorem openRunBody_attached_of_optionalReturn_of_bodyRun
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (proc : Expressions.Proc)
    (args : List Word) (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (finalCtx : Locals.Ctx)
    (returnPreludeCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (returnCode? : Option Structured.Code)
    (cleanup : Structured.Code)
    {callerTarget : Structured.RunState}
    {callerStack : List Word}
    (hTargetFuel : 0 < targetFuel)
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hLookup :
      Expressions.EffectSemantics.ProcList.lookup?
          proc.name targetProgram.procs = some proc)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc callerTarget.evm.stack =
        some (args.reverse, callerStack))
    (hRetc : proc.retc = fn.returns.length)
    (hShared :
      callerTarget.evm.toSharedState = sourceAfterArgs.shared)
    (hProcBody :
      proc.body =
        { stmts :=
            [.code [.bindLocals 0 fn.params.reverse]] ++
              (returnPreludeCode ++
                (targetBody.stmts ++
                  (StackLoweringCompilation.returnCodeStmts returnCode? ++
                    [.code cleanup]))) })
    (hReturnPreludeCompile :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length))
    (hExactBodyRun :
      ∀ {targetAfterPrelude : Structured.RunState},
        StateRel (StackLowering.functionBodyLayout fn) []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns)
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore)
            targetAfterPrelude →
        Simulation.Interaction.ForwardRel
          StackStatementPreservation.FuelTruncated
          (StackStatementPreservation.ControlOpenOutcomeRel {}
            fn.returns finalCtx []
            ({ callerStack := callerStack, retc := fn.returns.length } ::
              callerTarget.returns))
          (Functions.InteractionSemantics.Block.openRun sourceProgram
            (Functions.Source.Effectful.FunDef.bodyCtx fn) sourceFuel fn.body
            (CalleeEntry.sourceState sourceAfterArgs fn paramStore))
          (Expressions.InteractionSemantics.Block.openRun targetProgram
            targetFuel targetBody targetAfterPrelude))
    (hReturnPhase :
      match returnCode? with
      | none => fn.returns = []
      | some returnCode =>
          Locals.ExprSeq.compileCode finalCtx 0
              (StackLowering.returnWords fn.returns) = some returnCode)
    (hReturnAccess :
      StackAccess.ExprSeq.check? finalCtx.layout 0
          (StackLowering.returnWords fn.returns) = some ())
    (hCleanup :
      finalCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++
          (StackLoweringCompilation.returnCodeStmts returnCode? ++
            [.code cleanup]))) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenAttachedCallResultRel proc.retc callerStack callerTarget.returns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Stmt.openRun targetProgram
        (targetFuel + fn.returns.length + 2) (.call proc.name)
        callerTarget) := by
  cases returnCode? with
  | none =>
      have hCleanup' :
          finalCtx.cleanupToPreserving? 0 0 = some cleanup := by
        have hLength : fn.returns.length = 0 := by simp [hReturnPhase]
        simpa only [hLength] using hCleanup
      apply openRunBody_attached_noReturns_of_bodyRun sourceProgram
        targetProgram fn proc
        args paramStore sourceAfterArgs sourceFuel targetFuel finalCtx
        returnPreludeCode targetBody cleanup hTargetFuel hReturnPhase
        hSignature hInsert hLookup hSplit hRetc hShared
      · simpa [StackLoweringCompilation.returnCodeStmts,
          List.append_assoc] using hProcBody
      · exact hReturnPreludeCompile
      · exact hExactBodyRun
      · exact hCleanup'
      · simpa [StackLoweringCompilation.returnCodeStmts,
          List.append_assoc] using hFuel
  | some returnCode =>
      apply openRunBody_attached_of_bodyRun sourceProgram targetProgram fn proc args
        paramStore sourceAfterArgs sourceFuel targetFuel finalCtx
        returnPreludeCode targetBody returnCode cleanup hTargetFuel hSignature
        hInsert hLookup hSplit hRetc hShared
      · simpa [StackLoweringCompilation.returnCodeStmts,
          List.append_assoc] using hProcBody
      · exact hReturnPreludeCompile
      · exact hExactBodyRun
      · exact hReturnAccess
      · exact hReturnPhase
      · exact hCleanup
      · simpa [StackLoweringCompilation.returnCodeStmts,
          List.append_assoc] using hFuel

theorem openRunBody_attached_of_optionalReturn
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (fn : Functions.FunDef) (proc : Expressions.Proc)
    (args : List Word) (paramStore : Functions.Source.Store)
    (sourceAfterArgs : Locals.Source.State)
    (sourceFuel targetFuel : Nat)
    (finalCtx : Locals.Ctx)
    (returnPreludeCode : List Expressions.Stmt)
    (targetBody : Expressions.Block)
    (returnCode? : Option Structured.Code)
    (cleanup : Structured.Code)
    {callerTarget : Structured.RunState}
    {callerStack : List Word}
    (hTargetFuel : 0 < targetFuel)
    (hSignature : (fn.returns ++ fn.params).Nodup)
    (hInsert :
      Functions.Source.Store.insertMany fn.params args
          Locals.Source.Store.empty = some paramStore)
    (hLookup :
      Expressions.EffectSemantics.ProcList.lookup?
          proc.name targetProgram.procs = some proc)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc callerTarget.evm.stack =
        some (args.reverse, callerStack))
    (hRetc : proc.retc = fn.returns.length)
    (hShared :
      callerTarget.evm.toSharedState = sourceAfterArgs.shared)
    (hProcBody :
      proc.body =
        { stmts :=
            [.code [.bindLocals 0 fn.params.reverse]] ++
              (returnPreludeCode ++
                (targetBody.stmts ++
                  (StackLoweringCompilation.returnCodeStmts returnCode? ++
                    [.code cleanup]))) })
    (hReturnPreludeCompile :
      Locals.Block.compileOpen
          (Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length)
          { stmts := Lower.initReturns fn.returns } =
        some
          (returnPreludeCode,
            Locals.Ctx.procEntryWithLayoutAndRetc
              (StackLowering.functionBodyLayout fn) fn.returns.length))
    (hBody :
      StackStatementPreservation.ControlBlockPreserves
        sourceProgram targetProgram {} fn.returns
        (Locals.Ctx.procEntryWithLayoutAndRetc
          (StackLowering.functionBodyLayout fn) fn.returns.length)
        finalCtx fn.body targetBody)
    (hReturnPhase :
      match returnCode? with
      | none => fn.returns = []
      | some returnCode =>
          Locals.ExprSeq.compileCode finalCtx 0
              (StackLowering.returnWords fn.returns) = some returnCode)
    (hReturnAccess :
      StackAccess.ExprSeq.check? finalCtx.layout 0
          (StackLowering.returnWords fn.returns) = some ())
    (hCleanup :
      finalCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup)
    (hFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        (targetBody.stmts ++
          (StackLoweringCompilation.returnCodeStmts returnCode? ++
            [.code cleanup]))) :
    Simulation.Interaction.ForwardRel
      StackStatementPreservation.FuelTruncated
      (OpenAttachedCallResultRel proc.retc callerStack callerTarget.returns)
      (Functions.InteractionSemantics.FunDef.openRunBody
        sourceProgram fn args (sourceFuel + 1) sourceAfterArgs)
      (Expressions.InteractionSemantics.Stmt.openRun targetProgram
        (targetFuel + fn.returns.length + 2) (.call proc.name)
        callerTarget) := by
  have hBodyFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        targetBody.stmts :=
    Expressions.TargetFuel.Covers.head_of_append hFuel
  have hRuntime :=
    CalleeEntry.runtimeCtx fn
      { callerStack := callerStack, retc := fn.returns.length }
      callerTarget.returns
  apply openRunBody_attached_of_optionalReturn_of_bodyRun sourceProgram
    targetProgram fn proc args paramStore sourceAfterArgs sourceFuel targetFuel
    finalCtx returnPreludeCode targetBody returnCode? cleanup hTargetFuel
    hSignature hInsert hLookup hSplit hRetc hShared hProcBody
    hReturnPreludeCompile
  · intro targetAfterPrelude hInitial
    exact hBody (Functions.Source.Effectful.FunDef.bodyCtx fn)
      sourceFuel targetFuel hBodyFuel hRuntime (by
        simpa [Locals.Ctx.procEntryWithLayoutAndRetc,
          Locals.Ctx.procEntryWithLayout,
          StackLowering.functionBodyLayout] using hInitial)
  · exact hReturnPhase
  · exact hReturnAccess
  · exact hCleanup
  · exact hFuel

end Function

end StackCallPreservation
end Functions
end EvmCompiler
