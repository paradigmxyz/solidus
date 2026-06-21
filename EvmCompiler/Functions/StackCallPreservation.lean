import EvmCompiler.Functions.StackExpressionPreservation
import EvmCompiler.Functions.StackAccessLowering
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
      target.returns = frame :: callerReturns →
      CallResultRel frame callerReturns
        (.halted kind source) (.halt kind target)

abbrev OpenCallResultRel
    (frame : Structured.ReturnDest)
    (callerReturns : List Structured.ReturnDest) :=
  Simulation.Interaction.ExceptRel
    (fun (_ : EVMException) (_ : EVMException) => True)
    (CallResultRel frame callerReturns)

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

end ReturnEpilogue

namespace Function

/-- One initialized function body is preserved through its scheduled body and
ordinary fallthrough return epilogue. The recursive body theorem is an
adjacent private input; the public program theorem discharges it by fuel. -/
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
  rcases targetBody with ⟨targetStmts⟩
  have hBodyFuel :
      Expressions.TargetFuel.Covers targetProgram sourceFuel targetFuel
        targetStmts :=
    Expressions.TargetFuel.Covers.head_of_append hFuel
  have hBodyRun :=
    hBody (Functions.Source.Effectful.FunDef.bodyCtx fn)
      sourceFuel targetFuel hBodyFuel hRuntime hInitial
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
  | regular _hFinalRuntime hState =>
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
  | @halt kind source _sourceCtx targetAfter hShared hReturns =>
      simp only [Locals.Source.Effectful.Outcome.halt,
        Structured.Outcome.halt_mode,
        Structured.Outcome.halt_state]
      apply Simulation.Interaction.ForwardRel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact CallResultRel.halt hShared.symm hReturns

end Function

end StackCallPreservation
end Functions
end EvmCompiler
