import EvmCompiler.Yul.FunctionsObserverTerminalCompoundFuel

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverTerminalFuel

/-!
Program-indexed terminal preservation for the canonical Yul `for` lowering.

The qualitative relation proof remains in `FunctionsObserverTerminalForward`.
This module reconstructs only a bounded canonical Functions loop run and uses
determinism to transfer that bound to the qualitative result.
-/

def RecursiveTerminalLoopForwardProgramBounded
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (sourceProgram : Yul.Program)
    (targetProgram : Objects.Program)
    (profile : SolcValidation.DialectProfile)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel compilerFuel : Nat}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {before after afterCond afterPost : Fresh.State}
    {layout : List Name}
    {cond : AstExpr}
    {post body : List AstStmt}
    {preCond : List Functions.Stmt}
    {lowerCond : Locals.Expr 1}
    {lowerPost lowerBody : Functions.Block}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool},
    sourceFuel < bound →
      FunctionsObserverStaticCost.expr cond ≤
        FunctionsObserverStaticCost.program sourceProgram →
      FunctionsObserverStaticCost.stmtList post ≤
        FunctionsObserverStaticCost.program sourceProgram →
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram →
      SolcValidation.ExprOk? profile sourceProgram.contract
          layout 1 cond =
        true →
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout false false canLeave post =
        true →
      SolcValidation.StmtsOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout true true canLeave body =
        true →
      StateRelation.Vars.NamesWithin before.used
          (Expr.names cond) →
      StateRelation.Vars.NamesWithin before.used
          (Stmt.List.names post) →
      StateRelation.Vars.NamesWithin before.used
          (Stmt.List.names body) →
      Expr.lower1Unchecked? before cond =
        some (preCond, lowerCond, afterCond) →
      Stmt.List.toBlockUncheckedFuel?
          compilerFuel afterCond post =
        some (lowerPost, afterPost) →
      Stmt.List.toBlockUncheckedFuel?
          compilerFuel afterPost body =
        some (lowerBody, after) →
      StateRelation.Replay.ScopedExactRel codeRel layout source target →
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars →
      StateRelation.Vars.NamesWithin before.used ctx.scope →
      StateRelation.Vars.NamesWithin before.used layout →
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx →
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.For cond post body)
          (some sourceProgram.contract) source =
        .error failure →
      Yul.Source.Effectful.Exception.Observable failure.exception →
      Nonempty
        { result :
            FunctionsObserverTerminal.ForLoopResult
              contract codeRel targetProgram.toFunctions lowerPost
              { stmts :=
                  preCond ++
                    .if_
                      (.prim .iszero
                        (Locals.ExprSeq.cons lowerCond .nil))
                      { stmts := [.brk] } ::
                    lowerBody.stmts }
              failure target ctx //
          ForLoopResult.ProgramBounded
            (FunctionsObserverStaticCost.program sourceProgram)
            sourceFuel result }

namespace RecursiveTerminalLoopForwardProgramBounded

theorem ofComponents
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hOrdinary :
      FunctionsObserverTerminalForward.RecursiveTerminalLoopForward
        contract transcript codeRel sourceProgram targetProgram profile
        (bound + 1))
    (hValue :
      FunctionsObserverCallFuel.RecursiveScopedValueForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hRegularList :
      FunctionsObserverForwardFuel.RecursiveOpenListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalList :
      RecursiveTerminalListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound) :
    RecursiveTerminalLoopForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile
      (bound + 1) := by
  intro sourceFuel
  induction sourceFuel using Nat.strong_induction_on with
  | h sourceFuel ih =>
      intro compilerFuel sourceControl before after afterCond afterPost
        layout cond post body preCond lowerCond lowerPost lowerBody
        source failure target ctx canBreak canContinue canLeave
        hFuel hCondCost hPostCost hBodyCost
        hCondOk hPostOk hBodyOk hCondNames hPostNames hBodyNames
        hLowerCond hLowerPost hLowerBody hRel hDomain hScope hLayout
        hControl hRun hObservable
      obtain ⟨ordinary⟩ :=
        hOrdinary
          (sourceFuel := sourceFuel) (compilerFuel := compilerFuel)
          (sourceControl := sourceControl)
          (before := before) (after := after)
          (afterCond := afterCond) (afterPost := afterPost)
          (layout := layout) (cond := cond) (post := post) (body := body)
          (preCond := preCond) (lowerCond := lowerCond)
          (lowerPost := lowerPost) (lowerBody := lowerBody)
          (source := source) (failure := failure)
          (target := target) (ctx := ctx)
          (canBreak := canBreak) (canContinue := canContinue)
          (canLeave := canLeave)
          hFuel hCondOk hPostOk hBodyOk hCondNames hPostNames hBodyNames
          hLowerCond hLowerPost hLowerBody hRel hDomain hScope hLayout
          hControl hRun hObservable
      obtain ⟨loopFuel, hSourceFuel, hLoopRun⟩ :=
        Yul.Source.Effectful.exec_for_observable_error_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun hObservable
      obtain ⟨iterationFuel, hLoopFuel, hFailureCase⟩ :=
        Yul.Source.Effectful.loop_observable_error_parts
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hLoopRun hObservable
      obtain
          ⟨sourceShared, sourceVars, hSource,
            _hShared, _hScoped, _hSourceDomain⟩ :=
        hRel.2
      have hConditionInput :
          source.withSource
              (EvmYul.Yul.State.mkOk source.source) =
            source := by
        rw [hSource]
        change source.withSource (.Ok sourceShared sourceVars) = source
        rw [← hSource]
        exact Simulation.ResourceReplay.State.withSource_self source
      have hCondFresh : Fresh.Extends before afterCond :=
        Expr.lower1Unchecked?_stateExtends hLowerCond
      have hPostFresh : Fresh.Extends afterCond afterPost :=
        Stmt.List.toBlockUncheckedFuel?_stateExtends hLowerPost
      have hBodyFresh : Fresh.Extends afterPost after :=
        Stmt.List.toBlockUncheckedFuel?_stateExtends hLowerBody
      have hFresh : Fresh.Extends before after :=
        Fresh.Extends.trans hCondFresh
          (Fresh.Extends.trans hPostFresh hBodyFresh)
      have hLayoutAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used layout :=
        hLayout.mono hCondFresh
      have hLayoutAfterPost :
          StateRelation.Vars.NamesWithin afterPost.used layout :=
        hLayout.mono (Fresh.Extends.trans hCondFresh hPostFresh)
      have hPostNamesAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used
            (Stmt.List.names post) :=
        hPostNames.mono hCondFresh
      have hBodyNamesAfterPost :
          StateRelation.Vars.NamesWithin afterPost.used
            (Stmt.List.names body) :=
        hBodyNames.mono (Fresh.Extends.trans hCondFresh hPostFresh)
      have hScopeAfterCond :
          StateRelation.Vars.NamesWithin afterCond.used ctx.scope :=
        hScope.mono hCondFresh
      have hBodyBaseScope :
          StateRelation.Vars.NamesWithin before.used
            (ctx.withLoopControl ctx.scope ctx.scope).scope := by
        simpa [Functions.Source.Ctx.withLoopControl] using hScope
      have hBodyControl :
          FunctionsObserverOutcome.ControlContextRel
            (FunctionsObserverOutcome.ControlContextRel.forBodySourceControl
              layout sourceControl)
            layout true true canLeave
            (ctx.withLoopControl ctx.scope ctx.scope) :=
        FunctionsObserverOutcome.ControlContextRel.forBody hControl
      have hPostControl :
          FunctionsObserverOutcome.ControlContextRel
            (FunctionsObserverOutcome.ControlContextRel.forPostSourceControl
              sourceControl)
            layout false false canLeave ctx.withoutLoopControl :=
        FunctionsObserverOutcome.ControlContextRel.forPost hControl
      have hAbsorb :
          8 *
                FunctionsObserverFuel.executionBudgetFor
                  (FunctionsObserverStaticCost.program sourceProgram)
                  (FunctionsObserverStaticCost.program sourceProgram)
                  iterationFuel +
              8 ≤
            FunctionsObserverFuel.targetBudgetFor
              (FunctionsObserverStaticCost.program sourceProgram)
              sourceFuel :=
        FunctionsObserverFuel.eight_executionBudgetsFor_add_eight_le_target_of_lt
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.program sourceProgram)
          (by rfl) (by omega)
      rcases hFailureCase with hCondFailure | hAfterCond
      · have hCondFailure' :
            Yul.Source.Effectful.eval
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                iterationFuel cond (some sourceProgram.contract) source =
              .error failure := by
          simpa [ObserverSemantics.SourceReplay.stateModel,
            hConditionInput] using hCondFailure
        obtain ⟨condBounded⟩ :=
          hTerminalExpr (by omega) hCondCost hCondOk hLowerCond hRel
            hDomain hBodyBaseScope hCondFailure' hObservable
        let guardedBody :=
          FunctionsObserverTerminal.StatementResult.appendUnreachable
            condBounded.1
            (.if_
                (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                { stmts := [.brk] } ::
              lowerBody.stmts)
        obtain ⟨candidateBounded⟩ :=
          ForLoopResult.ofBody_runBounded
            (ctx := ctx) (post := lowerPost)
            (body :=
              { stmts :=
                  preCond ++
                    .if_
                      (.prim .iszero
                        (Locals.ExprSeq.cons lowerCond .nil))
                      { stmts := [.brk] } ::
                    lowerBody.stmts })
            guardedBody
        let candidate := candidateBounded.1
        have hCandidateRun :=
          FunctionsObserverTerminal.ForLoopResult.run_requiredFuel candidate
        obtain ⟨ordinaryFuel, hOrdinaryRun⟩ := ordinary.run
        have hOutcome :=
          Functions.Source.Effectful.Stmt.runForLoop_success_unique
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            targetProgram.toFunctions hCandidateRun hOrdinaryRun
        have hOrdinaryAt :
            Functions.Source.Effectful.Stmt.runForLoop
                (Functions.ObserverSemantics.stateModel transcript)
                (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                targetProgram.toFunctions ctx.withoutLoopControl
                (.lit (EvmYul.UInt256.ofNat 1))
                ctx.withoutLoopControl lowerPost
                (ctx.withLoopControl ctx.scope ctx.scope)
                { stmts :=
                    preCond ++
                      .if_
                        (.prim .iszero
                          (Locals.ExprSeq.cons lowerCond .nil))
                        { stmts := [.brk] } ::
                      lowerBody.stmts }
                candidate.requiredFuel target =
              .ok
                (Functions.Source.Effectful.Outcome.halt
                  ordinary.kind ordinary.finalTarget) := by
          simpa [hOutcome] using hCandidateRun
        have hRequired :=
          FunctionsObserverTerminal.ForLoopResult.requiredFuel_le_of_run
            ordinary hOrdinaryAt
        have hGuarded :=
          StatementResult.appendUnreachable_runBounded
            condBounded.1
            (.if_
                (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                { stmts := [.brk] } ::
              lowerBody.stmts)
        have hCondGlobal :=
          FunctionsObserverFuel.executionBudgetFor_le_global_at
            (FunctionsObserverStaticCost.program sourceProgram)
            hCondCost (show iterationFuel ≤ iterationFuel by rfl)
        have hCondBound := condBounded.2
        have hGuardedBound :
            guardedBody.requiredFuel ≤ condBounded.1.requiredFuel := by
          simpa [guardedBody, StatementResult.RunBounded] using hGuarded
        have hCandidateBound :
            candidate.requiredFuel ≤ guardedBody.requiredFuel + 1 := by
          simpa [candidate, ForLoopResult.RunBounded] using
            candidateBounded.2
        refine ⟨⟨ordinary, ?_⟩⟩
        dsimp [ForLoopResult.ProgramBounded, ForLoopResult.RunBounded]
        omega
      · rcases hAfterCond with
          ⟨sourceAfterCond, condValue, hCondRun, hLoopCase⟩
        have hCondRun' :
            Yul.Source.Effectful.eval
                (ObserverSemantics.SourceReplay.stateModel transcript)
                (ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript)
                iterationFuel cond (some sourceProgram.contract) source =
              .ok (sourceAfterCond, condValue) := by
          simpa [ObserverSemantics.SourceReplay.stateModel,
            hConditionInput] using hCondRun
        obtain ⟨values, hCondValues, hCondHead⟩ :=
          Yul.Source.Effectful.eval_ok_parts
            (ObserverSemantics.SourceReplay.stateModel transcript)
            (ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            hCondRun'
        obtain ⟨value, hValues, preparedNonempty⟩ :=
          hValue (exprFuel := iterationFuel)
            (before := before) (after := afterCond)
            (layout := layout) (expr := cond)
            (pre := preCond) (lower := lowerCond)
            (source := source) (source' := sourceAfterCond)
            (target := target)
            (ctx := ctx.withLoopControl ctx.scope ctx.scope)
            (values := values)
            (by omega) hCondCost hCondOk hLowerCond hRel hDomain
            hBodyBaseScope hCondValues
        obtain ⟨preparedBounded⟩ := preparedNonempty
        let prepared := preparedBounded.1
        have hCondValue : condValue = value := by
          rw [hValues] at hCondHead
          simpa using hCondHead
        subst value
        have hPreparedLayoutScope :
            FunctionsObserverOutcome.LayoutWithinScope
              layout prepared.prepared.finalCtx := by
          have hExtends :=
            Functions.Source.Effectful.Block.runOpen_scopeExtends
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              targetProgram.toFunctions
              (FunctionsObserverExpression.PreparedValue.run_requiredFuel
                prepared.prepared)
          exact fun name hMem =>
            hExtends name (hBodyControl.scope name hMem)
        have hPreparedControl :
            FunctionsObserverOutcome.ControlContextRel
              (FunctionsObserverOutcome.ControlContextRel.forBodySourceControl
                layout sourceControl)
              layout true true canLeave prepared.prepared.finalCtx :=
          FunctionsObserverOutcome.ControlContextRel.transport hBodyControl
            (fun _name hMem => hMem)
            prepared.prepared.control hPreparedLayoutScope
        cases hLoopCase with
        | body hNonzero hBodyFailure =>
            obtain ⟨listCompilerFuel, lowerBodyStmts, _hBlockFuel,
                hLowerBodyList, hLowerBodyEq⟩ :=
              Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
            subst lowerBody
            rcases
                Yul.Source.Effectful.exec_block_error_parts
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  hBodyFailure with hOuter | hBodyParts
            · rcases hOuter with ⟨rfl, hFailure⟩
              rw [← hFailure] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable]
                at hObservable
            · rcases hBodyParts with
                ⟨bodyFuel, hBodyFuel, hBodyListRun⟩
              obtain ⟨bodyBounded⟩ :=
                hTerminalList
                  (sourceFuel := bodyFuel)
                  (compilerFuel := listCompilerFuel)
                  (sourceControl :=
                    FunctionsObserverOutcome.ControlContextRel.forBodySourceControl
                      layout sourceControl)
                  (before := afterPost) (after := after)
                  (layout := layout) (stmts := body)
                  (lower := lowerBodyStmts)
                  (source := sourceAfterCond) (failure := failure)
                  (target := prepared.prepared.evalTarget)
                  (ctx := prepared.prepared.finalCtx)
                  (canBreak := true) (canContinue := true)
                  (canLeave := canLeave)
                  (by omega) hBodyCost hBodyOk hBodyNamesAfterPost
                  hLowerBodyList prepared.relation
                  (prepared.prepared.domain.mono hPostFresh)
                  (prepared.prepared.scope.mono hPostFresh)
                  hLayoutAfterPost hPreparedControl
                  hBodyListRun hObservable
              have hGuardRun :=
                Functions.Source.Effectful.Block.runOpen_forGuard_body_at_add_three
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (FunctionsObserverExpression.PreparedValue.run_requiredFuel
                    prepared.prepared)
                  prepared.prepared.eval
                  (Functions.ObserverSafety.SafeSemantics.eval_iszero
                    prepared.prepared.evalTarget condValue)
                  hNonzero
                  (FunctionsObserverTerminal.StatementResult.run_requiredFuel
                    bodyBounded.1)
              let guardedBody :
                  FunctionsObserverTerminal.StatementResult
                    contract codeRel targetProgram.toFunctions
                    (preCond ++
                      .if_
                          (.prim .iszero
                            (Locals.ExprSeq.cons lowerCond .nil))
                          { stmts := [.brk] } ::
                        lowerBodyStmts)
                    failure target
                    (ctx.withLoopControl ctx.scope ctx.scope) :=
                { kind := bodyBounded.1.kind
                  finalTarget := bodyBounded.1.finalTarget
                  finalCtx := bodyBounded.1.finalCtx
                  run :=
                    ⟨prepared.prepared.requiredFuel +
                        bodyBounded.1.requiredFuel + 3,
                      hGuardRun⟩
                  relation := bodyBounded.1.relation }
              obtain ⟨candidateBounded⟩ :=
                ForLoopResult.ofBody_runBounded
                  (ctx := ctx) (post := lowerPost)
                  (body :=
                    { stmts :=
                        preCond ++
                          .if_
                            (.prim .iszero
                              (Locals.ExprSeq.cons lowerCond .nil))
                            { stmts := [.brk] } ::
                          lowerBodyStmts })
                  guardedBody
              let candidate := candidateBounded.1
              have hCandidateRun :=
                FunctionsObserverTerminal.ForLoopResult.run_requiredFuel
                  candidate
              obtain ⟨ordinaryFuel, hOrdinaryRun⟩ := ordinary.run
              have hOutcome :=
                Functions.Source.Effectful.Stmt.runForLoop_success_unique
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions hCandidateRun hOrdinaryRun
              have hOrdinaryAt :
                  Functions.Source.Effectful.Stmt.runForLoop
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      (.lit (EvmYul.UInt256.ofNat 1))
                      ctx.withoutLoopControl lowerPost
                      (ctx.withLoopControl ctx.scope ctx.scope)
                      { stmts :=
                          preCond ++
                            .if_
                              (.prim .iszero
                                (Locals.ExprSeq.cons lowerCond .nil))
                              { stmts := [.brk] } ::
                            lowerBodyStmts }
                      candidate.requiredFuel target =
                    .ok
                      (Functions.Source.Effectful.Outcome.halt
                        ordinary.kind ordinary.finalTarget) := by
                simpa [hOutcome] using hCandidateRun
              have hRequired :=
                FunctionsObserverTerminal.ForLoopResult.requiredFuel_le_of_run
                  ordinary hOrdinaryAt
              have hGuardRequired :
                  guardedBody.requiredFuel ≤
                    prepared.prepared.requiredFuel +
                      bodyBounded.1.requiredFuel + 3 :=
                FunctionsObserverTerminal.StatementResult.requiredFuel_le_of_run
                  guardedBody hGuardRun
              have hPreparedBound :
                  prepared.prepared.requiredFuel ≤
                    FunctionsObserverFuel.executionBudgetFor
                      (FunctionsObserverStaticCost.program sourceProgram)
                      (FunctionsObserverStaticCost.expr cond)
                      iterationFuel := by
                simpa [prepared,
                  FunctionsObserverFuel.PreparedValue.ProgramBounded] using
                  preparedBounded.2
              have hBodyBound := bodyBounded.2
              have hPreparedGlobal :=
                FunctionsObserverFuel.executionBudgetFor_le_global_at
                  (FunctionsObserverStaticCost.program sourceProgram)
                  hCondCost (show iterationFuel ≤ iterationFuel by rfl)
              have hBodyGlobal :=
                FunctionsObserverFuel.executionBudgetFor_le_global_at
                  (FunctionsObserverStaticCost.program sourceProgram)
                  hBodyCost (show bodyFuel ≤ iterationFuel by omega)
              have hCandidateBound :
                  candidate.requiredFuel ≤ guardedBody.requiredFuel + 1 := by
                simpa [candidate, ForLoopResult.RunBounded] using
                  candidateBounded.2
              refine ⟨⟨ordinary, ?_⟩⟩
              dsimp [ForLoopResult.ProgramBounded,
                ForLoopResult.RunBounded]
              omega
        | post hNonzero hBody hBodyContinues hPostFailure =>
            rename_i sourceAfterBody
            obtain ⟨closedBodyBounded⟩ :=
              FunctionsObserverForwardFuel.RecursiveOpenCompoundForwardProgramBounded.closeGuardedBody
                (sourceControl :=
                  FunctionsObserverOutcome.ControlContextRel.forBodySourceControl
                    layout sourceControl)
                hRegularList prepared
                (FunctionsObserverStaticCost.expr cond)
                preparedBounded.2 (by omega) hBodyCost hBodyOk
                hBodyNamesAfterPost hLowerBody hPostFresh hFresh
                hLayout hLayoutAfterPost hBodyControl hNonzero hBody
            let closedBody := closedBodyBounded.1
            obtain ⟨bodyResult⟩ :=
              FunctionsObserverForward.ClosedListResult.continuingBody
                closedBody hBodyContinues rfl
            obtain ⟨listCompilerFuel, lowerPostStmts, _hBlockFuel,
                hLowerPostList, hLowerPostEq⟩ :=
              Stmt.List.toBlockUncheckedFuel?_parts hLowerPost
            subst lowerPost
            rcases
                Yul.Source.Effectful.exec_block_error_parts
                  (ObserverSemantics.SourceReplay.stateModel transcript)
                  (ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  hPostFailure with hOuter | hPostParts
            · rcases hOuter with ⟨rfl, hFailure⟩
              rw [← hFailure] at hObservable
              simp [Yul.Source.Effectful.Exception.Observable]
                at hObservable
            · rcases hPostParts with
                ⟨postFuel, hPostFuel, hPostListRun⟩
              obtain ⟨postBounded⟩ :=
                hTerminalList
                  (sourceFuel := postFuel)
                  (compilerFuel := listCompilerFuel)
                  (sourceControl :=
                    FunctionsObserverOutcome.ControlContextRel.forPostSourceControl
                      sourceControl)
                  (before := afterCond) (after := afterPost)
                  (layout := layout) (stmts := post)
                  (lower := lowerPostStmts)
                  (source :=
                    sourceAfterBody.withSource
                      sourceAfterBody.source.reviveJump)
                  (failure := failure)
                  (target := bodyResult.outcome.state)
                  (ctx := ctx.withoutLoopControl)
                  (canBreak := false) (canContinue := false)
                  (canLeave := canLeave)
                  (by omega) hPostCost hPostOk hPostNamesAfterCond
                  hLowerPostList bodyResult.relation
                  (bodyResult.targetDomain
                    (by
                      simpa [Functions.Source.Ctx.withLoopControl] using
                        hScopeAfterCond))
                  (by
                    simpa [Functions.Source.Ctx.withoutLoopControl] using
                      hScopeAfterCond)
                  hLayoutAfterCond hPostControl
                  hPostListRun hObservable
              obtain ⟨bodyTargetFuel, hBodyTargetFuel, hBodyTarget⟩ :=
                closedBodyBounded.2
              obtain ⟨bodyWitnessFuel, hBodyWitness⟩ := bodyResult.run
              have hBodyOutcome :=
                Functions.Source.Effectful.Block.runScoped_success_unique
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions hBodyTarget hBodyWitness
              have hBodyTargetResult :
                  Functions.Source.Effectful.Block.runScoped
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions
                      (ctx.withLoopControl ctx.scope ctx.scope)
                      { stmts :=
                          preCond ++
                            .if_
                              (.prim .iszero
                                (Locals.ExprSeq.cons lowerCond .nil))
                              { stmts := [.brk] } ::
                            lowerBody.stmts }
                      bodyTargetFuel target =
                    .ok bodyResult.outcome := by
                simpa [hBodyOutcome] using hBodyTarget
              have hPostScoped :
                  Functions.Source.Effectful.Block.runScoped
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      { stmts := lowerPostStmts }
                      postBounded.1.requiredFuel
                      bodyResult.outcome.state =
                    .ok
                      (Functions.Source.Effectful.Outcome.halt
                        postBounded.1.kind postBounded.1.finalTarget) :=
                Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (FunctionsObserverTerminal.StatementResult.run_requiredFuel
                    postBounded.1)
                  (by simp)
              let commonFuel :=
                max bodyTargetFuel postBounded.1.requiredFuel
              have hBodyTarget' :=
                Functions.Source.Effectful.Block.runScoped_mono
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (fuel' := commonFuel)
                  (by simp [commonFuel])
                  hBodyTargetResult
              have hPostScoped' :=
                Functions.Source.Effectful.Block.runScoped_mono
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions
                  (fuel' := commonFuel)
                  (by simp [commonFuel])
                  hPostScoped
              have hLoopTarget :
                  Functions.Source.Effectful.Stmt.runForLoop
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      (.lit (EvmYul.UInt256.ofNat 1))
                      ctx.withoutLoopControl
                      { stmts := lowerPostStmts }
                      (ctx.withLoopControl ctx.scope ctx.scope)
                      { stmts :=
                          preCond ++
                            .if_
                              (.prim .iszero
                                (Locals.ExprSeq.cons lowerCond .nil))
                              { stmts := [.brk] } ::
                            lowerBody.stmts }
                      (commonFuel + 1) target =
                    .ok
                      (Functions.Source.Effectful.Outcome.halt
                        postBounded.1.kind
                        postBounded.1.finalTarget) := by
                rcases bodyResult.mode with hRegular | hContinue
                · have hBodyEq :
                      bodyResult.outcome =
                        Functions.Source.Effectful.Outcome.regular
                          bodyResult.outcome.state :=
                    Functions.Source.Effectful.Outcome.eq_regular_of_mode
                      hRegular
                  rw [hBodyEq] at hBodyTarget'
                  exact
                    Functions.Source.Effectful.Stmt.runForLoop_regular_post_halt_of_runs
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions
                      (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                        target)
                      hBodyTarget' hPostScoped'
                · have hBodyEq :
                      bodyResult.outcome =
                        Functions.Source.Effectful.Outcome.cont
                          bodyResult.outcome.state :=
                    Functions.Source.Effectful.Outcome.eq_cont_of_mode
                      hContinue
                  rw [hBodyEq] at hBodyTarget'
                  exact
                    Functions.Source.Effectful.Stmt.runForLoop_cont_post_halt_of_runs
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions
                      (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                        target)
                      hBodyTarget' hPostScoped'
              have hOutcome :=
                Functions.Source.Effectful.Stmt.runForLoop_success_unique
                  (Functions.ObserverSemantics.stateModel transcript)
                  (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                    contract transcript)
                  targetProgram.toFunctions hLoopTarget ordinary.run.choose_spec
              have hOrdinaryAt :
                  Functions.Source.Effectful.Stmt.runForLoop
                      (Functions.ObserverSemantics.stateModel transcript)
                      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                        contract transcript)
                      targetProgram.toFunctions ctx.withoutLoopControl
                      (.lit (EvmYul.UInt256.ofNat 1))
                      ctx.withoutLoopControl
                      { stmts := lowerPostStmts }
                      (ctx.withLoopControl ctx.scope ctx.scope)
                      { stmts :=
                          preCond ++
                            .if_
                              (.prim .iszero
                                (Locals.ExprSeq.cons lowerCond .nil))
                              { stmts := [.brk] } ::
                            lowerBody.stmts }
                      (commonFuel + 1) target =
                    .ok
                      (Functions.Source.Effectful.Outcome.halt
                        ordinary.kind ordinary.finalTarget) := by
                simpa [hOutcome] using hLoopTarget
              have hRequired :=
                FunctionsObserverTerminal.ForLoopResult.requiredFuel_le_of_run
                  ordinary hOrdinaryAt
              have hPostBound := postBounded.2
              have hBodyGlobal :=
                FunctionsObserverFuel.executionBudgetFor_le_global_at
                  (FunctionsObserverStaticCost.program sourceProgram)
                  hBodyCost (show iterationFuel ≤ iterationFuel by rfl)
              have hCondGlobal :=
                FunctionsObserverFuel.executionBudgetFor_le_global_at
                  (FunctionsObserverStaticCost.program sourceProgram)
                  hCondCost (show iterationFuel ≤ iterationFuel by rfl)
              have hPostGlobal :=
                FunctionsObserverFuel.executionBudgetFor_le_global_at
                  (FunctionsObserverStaticCost.program sourceProgram)
                  hPostCost (show postFuel ≤ iterationFuel by omega)
              refine ⟨⟨ordinary, ?_⟩⟩
              dsimp [ForLoopResult.ProgramBounded,
                ForLoopResult.RunBounded]
              omega
        | recurse hNonzero hBody hBodyContinues hPost hPostRecurs
            hRecursive =>
            rename_i sourceAfterBody sourceAfterPost
            obtain ⟨closedBodyBounded⟩ :=
              FunctionsObserverForwardFuel.RecursiveOpenCompoundForwardProgramBounded.closeGuardedBody
                (sourceControl :=
                  FunctionsObserverOutcome.ControlContextRel.forBodySourceControl
                    layout sourceControl)
                hRegularList prepared
                (FunctionsObserverStaticCost.expr cond)
                preparedBounded.2 (by omega) hBodyCost hBodyOk
                hBodyNamesAfterPost hLowerBody hPostFresh hFresh
                hLayout hLayoutAfterPost hBodyControl hNonzero hBody
            let closedBody := closedBodyBounded.1
            obtain ⟨bodyResult⟩ :=
              FunctionsObserverForward.ClosedListResult.continuingBody
                closedBody hBodyContinues rfl
            obtain ⟨closedPostBounded⟩ :=
              FunctionsObserverForwardFuel.RecursiveOpenCompoundForwardProgramBounded.closeLoopPost
                (sourceControl :=
                  FunctionsObserverOutcome.ControlContextRel.forPostSourceControl
                    sourceControl)
                hRegularList bodyResult (by omega) hPostCost hPostOk
                hPostNamesAfterCond hLowerPost hBodyFresh
                (by
                  simpa [Functions.Source.Ctx.withLoopControl] using
                    hScopeAfterCond)
                (by
                  simpa [Functions.Source.Ctx.withoutLoopControl] using
                    hScopeAfterCond)
                hLayoutAfterCond hPostControl hPost
            let closedPost := closedPostBounded.1
            cases hSourcePost : sourceAfterPost.source with
            | OutOfFuel =>
                change
                  Yul.Source.Effectful.LoopPostRecurs
                    sourceAfterPost.source at hPostRecurs
                rw [hSourcePost] at hPostRecurs
                simp [Yul.Source.Effectful.LoopPostRecurs] at hPostRecurs
            | Checkpoint jump =>
                cases jump with
                | Leave shared store =>
                    change
                      Yul.Source.Effectful.LoopPostRecurs
                        sourceAfterPost.source at hPostRecurs
                    rw [hSourcePost] at hPostRecurs
                    simp [Yul.Source.Effectful.LoopPostRecurs]
                      at hPostRecurs
                | Break shared store =>
                    have hMode :
                        closedPost.outcome.mode = .brk := by
                      have hModeRel := closedPost.relation.mode
                      rw [hSourcePost] at hModeRel
                      exact
                        FunctionsObserverOutcome.ModeRel.source_break_target_brk
                          hModeRel
                    have hExit := closedPost.exitScope
                    simp [FunctionsObserverOutcome.ExitScopeRel,
                      FunctionsObserverOutcome.ControlContextRel.forPostSourceControl,
                      hMode] at hExit
                | Continue shared store =>
                    have hMode :
                        closedPost.outcome.mode = .cont := by
                      have hModeRel := closedPost.relation.mode
                      rw [hSourcePost] at hModeRel
                      exact
                        FunctionsObserverOutcome.ModeRel.source_continue_target_cont
                          hModeRel
                    have hExit := closedPost.exitScope
                    simp [FunctionsObserverOutcome.ExitScopeRel,
                      FunctionsObserverOutcome.ControlContextRel.forPostSourceControl,
                      hMode] at hExit
            | Ok postShared postStore =>
                rcases lowerPost with ⟨lowerPostStmts⟩
                have hPostMode :
                    closedPost.outcome.mode = .regular := by
                  have hModeRel := closedPost.relation.mode
                  rw [hSourcePost] at hModeRel
                  exact
                    FunctionsObserverOutcome.ModeRel.source_ok_target_regular
                      hModeRel
                have hPostRel :
                    StateRelation.Replay.ScopedExactRel codeRel layout
                      sourceAfterPost closedPost.outcome.state := by
                  have hExact := closedPost.relation.exact hPostMode
                  have hLayoutEq := closedPost.regularLayout hPostMode
                  have hRevived :
                      sourceAfterPost.withSource
                          sourceAfterPost.source.reviveJump =
                        sourceAfterPost := by
                    rw [hSourcePost]
                    change
                      sourceAfterPost.withSource
                          (.Ok postShared postStore) =
                        sourceAfterPost
                    rw [← hSourcePost]
                    exact
                      Simulation.ResourceReplay.State.withSource_self
                        sourceAfterPost
                  rw [hRevived] at hExact
                  simpa [hLayoutEq] using hExact
                have hPostDomain :
                    StateRelation.Vars.TargetDomainWithin before.used
                      closedPost.outcome.state.source.vars := by
                  have hRestricted := closedPost.targetRestriction
                  simp [FunctionsObserverOutcome.ScopedTargetRestriction,
                    hPostMode] at hRestricted
                  exact
                    hRestricted.domain
                      (by
                        simpa [Functions.Source.Ctx.withoutLoopControl] using
                          hScope)
                have hRecursiveInput :
                    sourceAfterPost.withSource
                        (sourceAfterPost.source.overwrite? source.source) =
                      sourceAfterPost := by
                  rw [hSourcePost, hSource]
                  change
                    sourceAfterPost.withSource
                        (.Ok postShared postStore) =
                      sourceAfterPost
                  rw [← hSourcePost]
                  exact
                    Simulation.ResourceReplay.State.withSource_self
                      sourceAfterPost
                have hRecursive' :
                    Yul.Source.Effectful.exec
                        (ObserverSemantics.SourceReplay.stateModel transcript)
                        (ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        iterationFuel (.For cond post body)
                        (some sourceProgram.contract) sourceAfterPost =
                      .error failure := by
                  simpa [ObserverSemantics.SourceReplay.stateModel,
                    hRecursiveInput] using hRecursive
                obtain ⟨recursiveBounded⟩ :=
                  ih iterationFuel (by omega)
                    (compilerFuel := compilerFuel)
                    (sourceControl := sourceControl)
                    (before := before) (after := after)
                    (afterCond := afterCond) (afterPost := afterPost)
                    (layout := layout) (cond := cond)
                    (post := post) (body := body)
                    (preCond := preCond) (lowerCond := lowerCond)
                    (lowerPost := { stmts := lowerPostStmts })
                    (lowerBody := lowerBody)
                    (source := sourceAfterPost) (failure := failure)
                    (target := closedPost.outcome.state) (ctx := ctx)
                    (canBreak := canBreak)
                    (canContinue := canContinue) (canLeave := canLeave)
                    (by omega) hCondCost hPostCost hBodyCost
                    hCondOk hPostOk hBodyOk hCondNames hPostNames hBodyNames
                    hLowerCond hLowerPost hLowerBody hPostRel hPostDomain
                    hScope hLayout hControl hRecursive' hObservable
                obtain ⟨bodyTargetFuel, hBodyTargetFuel, hBodyTarget⟩ :=
                  closedBodyBounded.2
                obtain ⟨postTargetFuel, hPostTargetFuel, hPostTarget⟩ :=
                  closedPostBounded.2
                let recursive := recursiveBounded.1
                obtain ⟨bodyWitnessFuel, hBodyWitness⟩ := bodyResult.run
                have hBodyOutcome :=
                  Functions.Source.Effectful.Block.runScoped_success_unique
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions hBodyTarget hBodyWitness
                have hBodyTargetResult :
                    Functions.Source.Effectful.Block.runScoped
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (ctx.withLoopControl ctx.scope ctx.scope)
                        { stmts :=
                            preCond ++
                              .if_
                                (.prim .iszero
                                  (Locals.ExprSeq.cons lowerCond .nil))
                                { stmts := [.brk] } ::
                              lowerBody.stmts }
                        bodyTargetFuel target =
                      .ok bodyResult.outcome := by
                  simpa [hBodyOutcome] using hBodyTarget
                have hPostEq :
                    closedPost.outcome =
                      Functions.Source.Effectful.Outcome.regular
                        closedPost.outcome.state :=
                  Functions.Source.Effectful.Outcome.eq_regular_of_mode
                    hPostMode
                rw [hPostEq] at hPostTarget
                let commonFuel :=
                  max bodyTargetFuel
                    (max postTargetFuel recursive.requiredFuel)
                have hBodyTarget' :=
                  Functions.Source.Effectful.Block.runScoped_mono
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions
                    (fuel' := commonFuel)
                    (by simp [commonFuel])
                    hBodyTargetResult
                have hPostTarget' :=
                  Functions.Source.Effectful.Block.runScoped_mono
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions
                    (fuel' := commonFuel)
                    (by simp [commonFuel])
                    hPostTarget
                have hRecursiveTarget' :=
                  Functions.Source.Effectful.Stmt.runForLoop_mono
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions
                    (fuel' := commonFuel)
                    (by simp [commonFuel])
                    (FunctionsObserverTerminal.ForLoopResult.run_requiredFuel
                      recursive)
                have hLoopTarget :
                    Functions.Source.Effectful.Stmt.runForLoop
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions ctx.withoutLoopControl
                        (.lit (EvmYul.UInt256.ofNat 1))
                        ctx.withoutLoopControl
                        { stmts := lowerPostStmts }
                        (ctx.withLoopControl ctx.scope ctx.scope)
                        { stmts :=
                            preCond ++
                              .if_
                                (.prim .iszero
                                  (Locals.ExprSeq.cons lowerCond .nil))
                                { stmts := [.brk] } ::
                              lowerBody.stmts }
                        (commonFuel + 1) target =
                      .ok
                        (Functions.Source.Effectful.Outcome.halt
                          recursive.kind recursive.finalTarget) := by
                  rcases bodyResult.mode with hRegular | hContinue
                  · have hBodyEq :
                        bodyResult.outcome =
                          Functions.Source.Effectful.Outcome.regular
                            bodyResult.outcome.state :=
                      Functions.Source.Effectful.Outcome.eq_regular_of_mode
                        hRegular
                    rw [hBodyEq] at hBodyTarget'
                    exact
                      Functions.Source.Effectful.Stmt.runForLoop_regular_post_recurse_of_runs
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (loopCtx := ctx.withoutLoopControl)
                        (postBase := ctx.withoutLoopControl)
                        (post := { stmts := lowerPostStmts })
                        (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                          target)
                        hBodyTarget' hPostTarget' hRecursiveTarget'
                  · have hBodyEq :
                        bodyResult.outcome =
                          Functions.Source.Effectful.Outcome.cont
                            bodyResult.outcome.state :=
                      Functions.Source.Effectful.Outcome.eq_cont_of_mode
                        hContinue
                    rw [hBodyEq] at hBodyTarget'
                    exact
                      Functions.Source.Effectful.Stmt.runForLoop_cont_post_recurse_of_runs
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions
                        (loopCtx := ctx.withoutLoopControl)
                        (postBase := ctx.withoutLoopControl)
                        (post := { stmts := lowerPostStmts })
                        (Functions.ObserverSafety.SafeSemantics.evalCondition_one
                          target)
                        hBodyTarget' hPostTarget' hRecursiveTarget'
                obtain ⟨ordinaryFuel, hOrdinaryRun⟩ := ordinary.run
                have hOutcome :=
                  Functions.Source.Effectful.Stmt.runForLoop_success_unique
                    (Functions.ObserverSemantics.stateModel transcript)
                    (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                      contract transcript)
                    targetProgram.toFunctions hLoopTarget hOrdinaryRun
                have hOrdinaryAt :
                    Functions.Source.Effectful.Stmt.runForLoop
                        (Functions.ObserverSemantics.stateModel transcript)
                        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                          contract transcript)
                        targetProgram.toFunctions ctx.withoutLoopControl
                        (.lit (EvmYul.UInt256.ofNat 1))
                        ctx.withoutLoopControl
                        { stmts := lowerPostStmts }
                        (ctx.withLoopControl ctx.scope ctx.scope)
                        { stmts :=
                            preCond ++
                              .if_
                                (.prim .iszero
                                  (Locals.ExprSeq.cons lowerCond .nil))
                                { stmts := [.brk] } ::
                              lowerBody.stmts }
                        (commonFuel + 1) target =
                      .ok
                        (Functions.Source.Effectful.Outcome.halt
                          ordinary.kind ordinary.finalTarget) := by
                  simpa [hOutcome] using hLoopTarget
                have hRequired :=
                  FunctionsObserverTerminal.ForLoopResult.requiredFuel_le_of_run
                    ordinary hOrdinaryAt
                have hBodyGlobal :=
                  FunctionsObserverFuel.executionBudgetFor_le_global_at
                    (FunctionsObserverStaticCost.program sourceProgram)
                    hBodyCost (show iterationFuel ≤ iterationFuel by rfl)
                have hCondGlobal :=
                  FunctionsObserverFuel.executionBudgetFor_le_global_at
                    (FunctionsObserverStaticCost.program sourceProgram)
                    hCondCost (show iterationFuel ≤ iterationFuel by rfl)
                have hPostGlobal :=
                  FunctionsObserverFuel.executionBudgetFor_le_global_at
                    (FunctionsObserverStaticCost.program sourceProgram)
                    hPostCost (show iterationFuel ≤ iterationFuel by rfl)
                have hRecursiveGlobal :
                    recursive.requiredFuel ≤
                      FunctionsObserverFuel.executionBudgetFor
                        (FunctionsObserverStaticCost.program sourceProgram)
                        (FunctionsObserverStaticCost.program sourceProgram)
                        iterationFuel := by
                  exact recursiveBounded.2.trans
                    (FunctionsObserverFuel.targetBudgetFor_le_executionBudgetFor
                      (FunctionsObserverStaticCost.program sourceProgram)
                      (FunctionsObserverStaticCost.program sourceProgram)
                      iterationFuel)
                refine ⟨⟨ordinary, ?_⟩⟩
                dsimp [ForLoopResult.ProgramBounded,
                  ForLoopResult.RunBounded]
                omega

end RecursiveTerminalLoopForwardProgramBounded

namespace RecursiveTerminalStmtForwardProgramBounded

theorem forLoop
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound sourceFuel compilerFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {cond : AstExpr}
    {post body : List AstStmt}
    {lower : List Functions.Stmt}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {canBreak canContinue canLeave : Bool}
    (hLoop :
      RecursiveTerminalLoopForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile
        (bound + 1))
    (hFuel : sourceFuel < bound + 1)
    (hStmtCost :
      FunctionsObserverStaticCost.stmt (.For cond post body) ≤
        FunctionsObserverStaticCost.program sourceProgram)
    (hOk :
      SolcValidation.StmtOk? profile sourceProgram.contract
          ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
          layout canBreak canContinue canLeave (.For cond post body) =
        true)
    (hNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.names (.For cond post body)))
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.For cond post body) =
        some (lower, after))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hLayout :
      StateRelation.Vars.NamesWithin before.used layout)
    (hControl :
      FunctionsObserverOutcome.ControlContextRel sourceControl layout
        canBreak canContinue canLeave ctx)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel (.For cond post body)
          (some sourceProgram.contract) source =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      { result :
          FunctionsObserverTerminal.StatementResult
            contract codeRel targetProgram.toFunctions lower
            failure target ctx //
        StatementResult.ProgramBounded
          (FunctionsObserverStaticCost.program sourceProgram)
          (FunctionsObserverStaticCost.stmt (.For cond post body))
          sourceFuel result } := by
  obtain
      ⟨compilerPrevious, preCond, lowerCond, afterCond,
        lowerPost, afterPost, lowerBody, _hCompilerFuel,
        hLowerCond, hLowerPost, hLowerBody, hLowerStmt⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_for_parts hLower
  subst lower
  have hOkParts := hOk
  simp [SolcValidation.StmtOk?] at hOkParts
  have hCondNames :
      StateRelation.Vars.NamesWithin before.used
        (Expr.names cond) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hPostNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names post) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hBodyNames :
      StateRelation.Vars.NamesWithin before.used
        (Stmt.List.names body) := by
    intro name hMem
    exact hNames name (by simp [Stmt.names, hMem])
  have hCostParts := hStmtCost
  simp only [FunctionsObserverStaticCost.stmt] at hCostParts
  have hCondCost :
      FunctionsObserverStaticCost.expr cond ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    omega
  have hMaxCost :
      max (FunctionsObserverStaticCost.stmtList post)
          (FunctionsObserverStaticCost.stmtList body) ≤
        FunctionsObserverStaticCost.program sourceProgram := by
    exact
      (Nat.le_add_left
        (max (FunctionsObserverStaticCost.stmtList post)
          (FunctionsObserverStaticCost.stmtList body))
        (FunctionsObserverStaticCost.expr cond)).trans
        ((Nat.le_add_right
          (FunctionsObserverStaticCost.expr cond +
            max (FunctionsObserverStaticCost.stmtList post)
              (FunctionsObserverStaticCost.stmtList body))
          6).trans hCostParts)
  have hPostCost :
      FunctionsObserverStaticCost.stmtList post ≤
        FunctionsObserverStaticCost.program sourceProgram :=
    (Nat.le_max_left _ _).trans hMaxCost
  have hBodyCost :
      FunctionsObserverStaticCost.stmtList body ≤
        FunctionsObserverStaticCost.program sourceProgram :=
    (Nat.le_max_right _ _).trans hMaxCost
  obtain ⟨loopBounded⟩ :=
    hLoop
      (sourceFuel := sourceFuel) (compilerFuel := compilerPrevious)
      (sourceControl := sourceControl)
      (before := before) (after := after)
      (afterCond := afterCond) (afterPost := afterPost)
      (layout := layout) (cond := cond) (post := post) (body := body)
      (preCond := preCond) (lowerCond := lowerCond)
      (lowerPost := lowerPost) (lowerBody := lowerBody)
      (source := source) (failure := failure)
      (target := target) (ctx := ctx)
      (canBreak := canBreak) (canContinue := canContinue)
      (canLeave := canLeave)
      hFuel hCondCost hPostCost hBodyCost
      hOkParts.1 hOkParts.2.1 hOkParts.2.2
      hCondNames hPostNames hBodyNames hLowerCond hLowerPost hLowerBody
      hRel hDomain hScope hLayout hControl hRun hObservable
  obtain ⟨resultBounded⟩ :=
    StatementResult.ofForLoop_runBounded loopBounded.1
  have hLoopBound := loopBounded.2
  have hResultBound := resultBounded.2
  have hTargetPositive :=
    FunctionsObserverFuel.targetBudgetFor_ge_sixteen
      (FunctionsObserverStaticCost.program sourceProgram) sourceFuel
  have hParent :=
    FunctionsObserverFuel.targetBudgetFor_add_localCost_le_executionBudgetFor
      (FunctionsObserverStaticCost.program sourceProgram)
      (FunctionsObserverStaticCost.stmt (.For cond post body))
      sourceFuel
  have hWrapper :
      4 ≤ FunctionsObserverStaticCost.stmt (.For cond post body) := by
    simp [FunctionsObserverStaticCost.stmt]
  refine ⟨⟨resultBounded.1, ?_⟩⟩
  dsimp [StatementResult.ProgramBounded, StatementResult.RunBounded]
  dsimp [ForLoopResult.ProgramBounded, ForLoopResult.RunBounded]
    at hLoopBound
  dsimp [StatementResult.RunBounded] at hResultBound
  omega

theorem ofComponents
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {sourceProgram : Yul.Program}
    {targetProgram : Objects.Program}
    {profile : SolcValidation.DialectProfile}
    {bound : Nat}
    (hDecomposition :
      FunctionsObserverCompiler.Decomposition sourceProgram targetProgram)
    (hProgramOk :
      SolcValidation.ProgramOkWith? profile sourceProgram = true)
    (hRegularExpr :
      FunctionsObserverCallFuel.RecursiveScopedExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalExpr :
      RecursiveTerminalExpressionForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalBody :
      RecursiveTerminalBodyForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hTerminalList :
      RecursiveTerminalListForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile bound)
    (hLoop :
      RecursiveTerminalLoopForwardProgramBounded
        contract transcript codeRel sourceProgram targetProgram profile
        (bound + 1)) :
    RecursiveTerminalStmtForwardProgramBounded
      contract transcript codeRel sourceProgram targetProgram profile
      (bound + 1) := by
  intro sourceFuel compilerFuel sourceControl before after layout stmt lower
    source failure target ctx canBreak canContinue canLeave
    hFuel hStmtCost hOk hNames hLower hRel hDomain hScope hLayout
    hControl hRun hObservable
  cases stmt with
  | Block body =>
      exact
        block hTerminalList hFuel hStmtCost hOk hNames hLower hRel
          hDomain hScope hLayout hControl hRun hObservable
  | Switch scrutinee cases defaultBody =>
      exact
        switch hRegularExpr hTerminalExpr hTerminalList
          hFuel hStmtCost hOk hNames hLower hRel hDomain hScope hLayout
          hControl hRun hObservable
  | For cond post body =>
      exact
        forLoop hLoop hFuel hStmtCost hOk hNames hLower hRel hDomain
          hScope hLayout hControl hRun hObservable
  | If cond body =>
      exact
        ifThen hRegularExpr hTerminalExpr hTerminalList
          hFuel hStmtCost hOk hNames hLower hRel hDomain hScope hLayout
          hControl hRun hObservable
  | Let names value? =>
      cases value? with
      | none =>
          have hOkParts := hOk
          simp [SolcValidation.StmtOk?, SolcValidation.bindableList?,
            SolcValidation.nonemptyNames?,
            SolcValidation.bindingNames?,
            SolcValidation.namesNodup?,
            SolcValidation.namesFresh?] at hOkParts
          obtain
              ⟨sourceShared, sourceVars, hSource,
                _hShared, _hScoped, hSourceDomain⟩ :=
            hRel.2
          have hCheck :
              EvmYul.Yul.checkDeclaration source.source names =
                .ok () := by
            rw [hSource]
            apply StateRelation.Vars.checkDeclaration_ok hSourceDomain
            · simpa [identNames_eq_self] using hOkParts.2.2.1
            · intro candidate hMem
              exact
                (hOkParts.2.2.2 candidate
                  (by simpa [identNames_eq_self] using hMem)).2
          exact
            (Yul.Source.Effectful.exec_let_none_observable_error_false
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              hCheck hRun hObservable).elim
      | some value =>
          by_cases hFunctionCall :
              ∃ functionName functionArgs,
                value = .Call (.inr functionName) functionArgs
          · obtain ⟨functionName, functionArgs, rfl⟩ := hFunctionCall
            have hNamesUsed :
                StateRelation.Vars.NamesWithin before.used
                  (identNames names) := by
              intro candidate hMem
              apply hNames candidate
              exact List.mem_append_left _ hMem
            exact
              letCall hDecomposition hProgramOk hRegularExpr
                hTerminalExpr hTerminalBody
                hFuel hStmtCost hOk hNamesUsed hLower hRel hDomain
                hScope hRun hObservable
          · have hNotFunctionCall :
                ∀ functionName functionArgs,
                  value ≠ .Call (.inr functionName) functionArgs := by
              intro functionName functionArgs hEq
              exact hFunctionCall ⟨functionName, functionArgs, hEq⟩
            obtain ⟨name, hNamesEq⟩ :=
              Stmt.toFunctionsListUncheckedFuel?_let_noncall_singleton
                hNotFunctionCall hLower
            subst names
            exact
              letOne hTerminalExpr hFuel hStmtCost hNotFunctionCall hOk
                hLower hRel hDomain hScope hRun hObservable
  | Assign names value =>
      by_cases hFunctionCall :
          ∃ functionName functionArgs,
            value = .Call (.inr functionName) functionArgs
      · obtain ⟨functionName, functionArgs, rfl⟩ := hFunctionCall
        exact
          assignCall hDecomposition hProgramOk hRegularExpr
            hTerminalExpr hTerminalBody hFuel hStmtCost hOk hLower hRel
            hDomain hScope hRun hObservable
      · have hNotFunctionCall :
            ∀ functionName functionArgs,
              value ≠ .Call (.inr functionName) functionArgs := by
          intro functionName functionArgs hEq
          exact hFunctionCall ⟨functionName, functionArgs, hEq⟩
        obtain ⟨name, hNamesEq⟩ :=
          Stmt.toFunctionsListUncheckedFuel?_assign_noncall_singleton
            hNotFunctionCall hLower
        subst names
        exact
          assignOne hTerminalExpr hFuel hStmtCost hNotFunctionCall hOk
            hLower hRel hDomain hScope hRun hObservable
  | ExprStmtCall value =>
      cases value with
      | Lit literal =>
          simp [SolcValidation.StmtOk?, SolcValidation.ExprOk?] at hOk
      | Var name =>
          simp [SolcValidation.StmtOk?, SolcValidation.ExprOk?] at hOk
      | Call callee args =>
          cases callee with
          | inl prim =>
              have hLeafOk :
                  SolcValidation.StmtOk? profile sourceProgram.contract
                      ((Contract.functionEntries
                        sourceProgram.contract).map Prod.fst)
                      layout false false false
                      (.ExprStmtCall (.Call (.inl prim) args)) =
                    true := by
                simpa [SolcValidation.StmtOk?] using hOk
              cases hTerminal : Prim.terminal? prim with
              | none =>
                  exact
                    primitive hRegularExpr hTerminalExpr
                      hFuel hStmtCost hTerminal hLeafOk hLower hRel
                      hDomain hScope hRun hObservable
              | some kind =>
                  exact
                    terminalPrimitive hRegularExpr hTerminalExpr
                      hFuel hStmtCost hTerminal hLeafOk hLower hRel
                      hDomain hScope hRun hObservable
          | inr functionName =>
              have hLeafOk :
                  SolcValidation.StmtOk? profile sourceProgram.contract
                      ((Contract.functionEntries
                        sourceProgram.contract).map Prod.fst)
                      layout false false false
                      (.ExprStmtCall
                        (.Call (.inr functionName) args)) =
                    true := by
                simpa [SolcValidation.StmtOk?] using hOk
              exact
                functionCall hDecomposition hProgramOk hRegularExpr
                  hTerminalExpr hTerminalBody hFuel hStmtCost hLeafOk
                  hLower hRel hDomain hScope hRun hObservable
  | Break =>
      exact
        (Yul.Source.Effectful.exec_break_observable_error_false
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun hObservable).elim
  | Continue =>
      exact
        (Yul.Source.Effectful.exec_continue_observable_error_false
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun hObservable).elim
  | Leave =>
      exact
        (Yul.Source.Effectful.exec_leave_observable_error_false
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          hRun hObservable).elim

end RecursiveTerminalStmtForwardProgramBounded
end FunctionsObserverTerminalFuel
end Yul
end EvmCompiler
