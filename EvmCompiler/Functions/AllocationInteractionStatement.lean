import EvmCompiler.Functions.AllocationInteractionExpressionRecursive
import EvmCompiler.Locals.InteractionStatePreservation

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionStatement

open AllocationInteractionRelation

/-- Source-visible live names selected by a statement outcome. -/
def outcomeLive
    (returns regularLive : List Functions.Name)
    (ctx : Functions.Source.Ctx) :
    Locals.Source.Mode → List Functions.Name
  | .regular => regularLive
  | .brk => ctx.breakScope?.getD []
  | .cont => ctx.continueScope?.getD []
  | .leave => returns
  | .halt _ => regularLive

/-- Every source control destination is contained in the current live scope. -/
structure ControlScopesWithin
    (returns live : List Functions.Name)
    (ctx : Functions.Source.Ctx) : Prop where
  breakScope :
    ∀ scope, ctx.breakScope? = some scope →
      ∀ name, name ∈ scope → name ∈ live
  continueScope :
    ∀ scope, ctx.continueScope? = some scope →
      ∀ name, name ∈ scope → name ∈ live
  returnsLive : ∀ name, name ∈ returns → name ∈ live
  leaveScope :
    ∀ scope, ctx.leaveScope? = some scope →
      ∀ name, name ∈ returns → name ∈ scope

namespace ControlScopesWithin

theorem mono
    {returns beforeLive afterLive : List Functions.Name}
    {ctx : Functions.Source.Ctx}
    (hControl : ControlScopesWithin returns beforeLive ctx)
    (hSubset : ∀ name, name ∈ beforeLive → name ∈ afterLive) :
    ControlScopesWithin returns afterLive ctx :=
  { breakScope := fun scope hScope name hName =>
      hSubset name (hControl.breakScope scope hScope name hName)
    continueScope := fun scope hScope name hName =>
      hSubset name (hControl.continueScope scope hScope name hName)
    returnsLive := fun name hName =>
      hSubset name (hControl.returnsLive name hName)
    leaveScope := hControl.leaveScope }

theorem outcomeLive_subset
    {returns live : List Functions.Name}
    {ctx : Functions.Source.Ctx}
    (hControl : ControlScopesWithin returns live ctx)
    (mode : Locals.Source.Mode) :
    ∀ name, name ∈ outcomeLive returns live ctx mode → name ∈ live := by
  intro name hName
  cases mode with
  | regular => exact hName
  | brk =>
      cases hBreak : ctx.breakScope? with
      | none => simp [outcomeLive, hBreak] at hName
      | some scope =>
          exact hControl.breakScope scope hBreak name
            (by simpa [outcomeLive, hBreak] using hName)
  | cont =>
      cases hContinue : ctx.continueScope? with
      | none => simp [outcomeLive, hContinue] at hName
      | some scope =>
          exact hControl.continueScope scope hContinue name
            (by simpa [outcomeLive, hContinue] using hName)
  | leave => exact hControl.returnsLive name hName
  | halt kind => exact hName

theorem push
    {returns live : List Functions.Name}
    {ctx : Functions.Source.Ctx}
    (hControl : ControlScopesWithin returns live ctx)
    (name : Functions.Name) :
    ControlScopesWithin returns (name :: live)
      { ctx with scope := name :: ctx.scope } :=
  { breakScope := fun scope hScope localName hLocal =>
      List.mem_cons_of_mem name
        (hControl.breakScope scope hScope localName hLocal)
    continueScope := fun scope hScope localName hLocal =>
      List.mem_cons_of_mem name
        (hControl.continueScope scope hScope localName hLocal)
    returnsLive := fun returnName hReturn =>
      List.mem_cons_of_mem name
        (hControl.returnsLive returnName hReturn)
    leaveScope := hControl.leaveScope }

end ControlScopesWithin

/--
Statement outcomes retain the full compiler/runtime invariant on regular
continuation and the activation-owned relation on abrupt or terminal exits.
-/
inductive BoundaryOutcomeRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Plan) (returns regularLive : List Locals.Name)
    (frameBase : Nat) (mode : ActivationMode)
    (controlCtx : Functions.Source.Ctx) :
    Functions.InteractionSemantics.Outcome →
      Expressions.InteractionSemantics.Outcome → Prop where
  | regular {source : SourceState} {target : TargetState}
      (invariant :
        AllocationContext.ActivationInvariant contract lowerCtx lowerState
          localsCtx plan regularLive frameBase mode source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase mode controlCtx
        (Functions.Source.Effectful.Outcome.regular source)
        (Structured.EffectSemantics.Outcome.regular target)
  | brk {source : SourceState} {target : TargetState}
      (defined : LiveDefined (controlCtx.breakScope?.getD []) source)
      (stackLength :
        target.evm.stack.length =
          mode.stackLength plan (controlCtx.breakScope?.getD []))
      (modeMatches : mode.Matches plan (controlCtx.breakScope?.getD []))
      (state :
        ActivationStateRel contract plan (controlCtx.breakScope?.getD []) 0
          frameBase mode source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase mode controlCtx
        (Functions.Source.Effectful.Outcome.brk source)
        (Structured.EffectSemantics.Outcome.brk target)
  | cont {source : SourceState} {target : TargetState}
      (defined : LiveDefined (controlCtx.continueScope?.getD []) source)
      (stackLength :
        target.evm.stack.length =
          mode.stackLength plan (controlCtx.continueScope?.getD []))
      (modeMatches : mode.Matches plan (controlCtx.continueScope?.getD []))
      (state :
        ActivationStateRel contract plan (controlCtx.continueScope?.getD []) 0
          frameBase mode source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase mode controlCtx
        (Functions.Source.Effectful.Outcome.cont source)
        (Structured.EffectSemantics.Outcome.cont target)
  | leave {source : SourceState} {target : TargetState}
      (state : LeaveStateRel contract returns source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase mode controlCtx
        (Functions.Source.Effectful.Outcome.leave source)
        (Structured.EffectSemantics.Outcome.leave target)
  | halt (kind : Assembly.HaltKind)
      {source : SourceState} {target : TargetState}
      (state : HaltStateRel contract plan source target) :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase mode controlCtx
        (Functions.Source.Effectful.Outcome.halt kind source)
        (Structured.EffectSemantics.Outcome.halt kind target)

/-- Result relation for one allocated Functions statement. -/
def StmtResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns regularLive : List Locals.Name) (frameBase : Nat)
    (mode : ActivationMode)
    (controlCtx : Functions.Source.Ctx)
    (expectedCtx : Functions.Source.Ctx) :
    (Functions.InteractionSemantics.Outcome × Functions.Source.Ctx) →
      Expressions.InteractionSemantics.Outcome → Prop
  | (sourceOutcome, sourceCtx), targetOutcome =>
      sourceCtx = expectedCtx ∧
        BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan returns
          regularLive frameBase mode controlCtx sourceOutcome targetOutcome

abbrev OpenStmtResultRel
    (contract : MemoryContract.Contract)
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx) (plan : Plan)
    (returns regularLive : List Locals.Name) (frameBase : Nat)
    (mode : ActivationMode)
    (controlCtx : Functions.Source.Ctx)
    (expectedCtx : Functions.Source.Ctx) :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (StmtResultRel contract lowerCtx lowerState localsCtx plan returns
      regularLive frameBase mode controlCtx expectedCtx)

namespace BoundaryOutcomeRel

/-- Forget regular compiler context while retaining the outcome-indexed state. -/
theorem toActivationOutcomeRel
    {contract : MemoryContract.Contract}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx} {plan : Plan}
    {returns regularLive : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {controlCtx : Functions.Source.Ctx}
    {sourceOutcome : Functions.InteractionSemantics.Outcome}
    {targetOutcome : Expressions.InteractionSemantics.Outcome}
    (hRel :
      BoundaryOutcomeRel contract lowerCtx lowerState localsCtx plan returns
        regularLive frameBase mode controlCtx sourceOutcome targetOutcome) :
    ActivationOutcomeRel contract plan
      (outcomeLive returns regularLive controlCtx sourceOutcome.mode)
      0 frameBase mode sourceOutcome targetOutcome := by
  cases hRel with
  | regular invariant => exact .regular invariant.state
  | brk defined stackLength modeMatches state =>
      exact .brk defined stackLength modeMatches state
  | cont defined stackLength modeMatches state =>
      exact .cont defined stackLength modeMatches state
  | leave state => exact .leave state
  | halt kind state => exact .halt kind state

/--
An abrupt result may cross compiler contexts belonging to a dynamically
unreachable tail. Its destination live set is selected by the outcome itself.
-/
theorem reindex_nonregular
    {contract : MemoryContract.Contract}
    {beforeLowerCtx afterLowerCtx : AllocationLowering.Ctx}
    {beforeLowerState afterLowerState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx} {plan : Plan}
    {returns beforeRegularLive afterRegularLive : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {controlCtx : Functions.Source.Ctx}
    {sourceOutcome : Functions.InteractionSemantics.Outcome}
    {targetOutcome : Expressions.InteractionSemantics.Outcome}
    (hRel :
      BoundaryOutcomeRel contract beforeLowerCtx beforeLowerState
        beforeLocals plan returns beforeRegularLive frameBase mode controlCtx
        sourceOutcome targetOutcome)
    (hNonregular : sourceOutcome.mode ≠ .regular) :
    BoundaryOutcomeRel contract afterLowerCtx afterLowerState afterLocals plan
      returns afterRegularLive frameBase mode controlCtx sourceOutcome
      targetOutcome := by
  cases hRel with
  | regular invariant => exact False.elim (hNonregular rfl)
  | brk defined stackLength modeMatches state =>
      exact .brk defined stackLength modeMatches state
  | cont defined stackLength modeMatches state =>
      exact .cont defined stackLength modeMatches state
  | leave state => exact .leave state
  | halt kind state => exact .halt kind state

end BoundaryOutcomeRel

/--
An expression statement is preserved by the ordinary allocation lowerer and
Locals compiler. The statement layer merely packages the recursively proved
expression result as a regular control outcome.
-/
theorem expr_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {sourceFuel targetExtra frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : AllocationInteractionRelation.SourceState}
    {target : AllocationInteractionRelation.TargetState}
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx lowerState
        localsCtx plan live frameBase mode source target) :
    Simulation.Interaction.Rel
      (OpenStmtResultRel contract lowerCtx lowerFinal localsFinal plan returns
        live frameBase mode sourceCtx sourceCtx)
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.expr expr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases hLowerExpr :
      AllocationLowering.lowerExpr lowerCtx lowerState expr with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
  | some lowered =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      cases hCode : Locals.Expr.compileCode localsCtx 0 lowered with
      | none =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode]
            at hCompile
      | some code =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode]
            at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          have hExpr :=
            AllocationInteractionExpressionRecursive.forwardExpr
              hSafe hInvariant.compiler hScoped hLowerExpr hCode
              hInvariant.state
          have hVars :=
            Locals.InteractionStatePreservation.expr_openEval_vars expr source
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          simp only [Locals.codeStmt]
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run]
          apply Simulation.Interaction.Rel.bind_custom hExprStrong
          intro sourceDone targetDone hDone
          rcases hDone with ⟨hRelated, hVarsDone⟩
          cases hRelated with
          | error hError =>
              exact .done (.error hError)
          | @ok sourceResult targetFinal hResult =>
              apply Simulation.Interaction.Rel.done
              apply Simulation.Interaction.ExceptRel.ok
              refine ⟨rfl, .regular ?_⟩
              exact
                { compiler := hInvariant.compiler
                  planWF := hInvariant.planWF
                  defined := hInvariant.defined.congr_vars hVarsDone
                  state := by simpa using hResult.state
                  stackLength := by
                    have hValues : sourceResult.2 = [] :=
                      List.eq_nil_of_length_eq_zero hResult.valuesLength
                    rw [hResult.stack, hValues]
                    simpa using hInvariant.stackLength }

/-- Exact ordinary compiler shape for a stack-resident declaration. -/
theorem stack_let_compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Plan} {beforeLive afterLive : List Locals.Name}
    {name : Locals.Name} {value : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hBefore :
      AllocationContext.StackExprContext lowerCtx beforeState beforeLocals
        plan beforeLive)
    (hAfter :
      AllocationContext.StackExprContext lowerCtx afterState afterLocals
        plan afterLive)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name value) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals)) :
    ∃ (loweredValue : Locals.Expr 1) (valueCode : Structured.Code),
      AllocationLowering.lowerExpr lowerCtx beforeState value =
          some loweredValue ∧
        Locals.Expr.compileCode beforeLocals 0 loweredValue =
          some valueCode ∧
        currentStackOrder plan afterLive =
          name :: currentStackOrder plan beforeLive ∧
        loweredStmts = [.let_ name loweredValue] ∧
        afterState =
          { allocation :=
              (AllocationSupport.allocateName
                name beforeState.allocation).2
            layout := name :: beforeState.layout } ∧
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              Locals.bindLocals 0 (name :: beforeLocals.layout))] ∧
        afterLocals =
          beforeLocals.withLayout (name :: beforeLocals.layout) := by
  cases hLowerValue :
      AllocationLowering.lowerExpr lowerCtx beforeState value with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
  | some loweredValue =>
      let slot := beforeState.allocation.nextSlot
      cases hStack : AllocationLowering.isStackSlot lowerCtx slot with
      | false =>
          change
            AllocationLowering.isStackSlot lowerCtx
                beforeState.allocation.nextSlot = false at hStack
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack,
            hBefore.frameAbsent] at hLower
      | true =>
          change
            AllocationLowering.isStackSlot lowerCtx
                beforeState.allocation.nextSlot = true at hStack
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack] at hLower
          rcases hLower with ⟨hLowered, hAfterState⟩
          subst loweredStmts
          subst afterState
          have hStackOrder :
              currentStackOrder plan afterLive =
                name :: currentStackOrder plan beforeLive := by
            rw [hAfter.stackOrder, hBefore.stackOrder]
          cases hValueCode :
              Locals.Expr.compileCode beforeLocals 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hValueCode] at hCompile
          | some valueCode =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.codeStmt, hValueCode] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              exact
                ⟨loweredValue, valueCode, rfl, hValueCode,
                  hStackOrder, rfl, rfl, rfl, rfl⟩

/-- Preservation of one stack-resident declaration through ordinary passes. -/
theorem stack_let_of_lower_compile
    {contract : MemoryContract.Contract}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Expressions.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Plan} {live : List Locals.Name}
    {sourceFuel targetExtra frameBase : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source : SourceState} {target : TargetState}
    (hSafe : AllocationInteractionSafety.ExprSafe contract valueExpr source)
    (hAfter :
      AllocationContext.StackExprContext lowerCtx afterState afterLocals
        plan (name :: live))
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hInvariant :
      AllocationContext.ActivationInvariant contract lowerCtx beforeState
        beforeLocals plan live frameBase .stack source target) :
    Simulation.Interaction.Rel
      (OpenStmtResultRel contract lowerCtx afterState afterLocals plan returns
        (name :: live) frameBase .stack sourceCtx
        { sourceCtx with scope := name :: sourceCtx.scope })
      (Functions.InteractionSemantics.Stmt.openRun
        sourceProgram sourceCtx sourceFuel (.let_ name valueExpr) source)
      (Expressions.InteractionSemantics.Block.openRun
        targetProgram (targetExtra + 2) { stmts := compiledStmts } target) := by
  cases hInvariant.compiler with
  | stack hBefore =>
      obtain
          ⟨loweredValue, valueCode, hLowerValue, hCompileValue,
            hStackOrder, rfl, rfl, rfl, rfl⟩ :=
        stack_let_compiler_shape hBefore hAfter hLower hCompile
      obtain ⟨location, hLocation⟩ :=
        hAfter.location name (by simp)
      cases location with
      | scratch slot =>
          exact False.elim
            (hAfter.liveStackOnly name slot (by simp) hLocation)
      | stack planDepth =>
          have hExpr :=
            AllocationInteractionExpressionRecursive.forwardExpr
              hSafe (.stack hBefore) hScoped hLowerValue hCompileValue
              hInvariant.state
          have hVars :=
            Locals.InteractionStatePreservation.expr_openEval_vars
              valueExpr source
          have hExprStrong :=
            Simulation.Interaction.Rel.strengthen_left hExpr hVars
          have hCore :
              Simulation.Interaction.Rel
                (OpenStmtResultRel contract lowerCtx
                  { allocation :=
                      (AllocationSupport.allocateName
                        name beforeState.allocation).2
                    layout := name :: beforeState.layout }
                  (beforeLocals.withLayout
                    (name :: beforeLocals.layout))
                  plan returns (name :: live) frameBase .stack sourceCtx
                  { sourceCtx with scope := name :: sourceCtx.scope })
                (Simulation.Interaction.bind
                  (Functions.InteractionSemantics.Expr.openEval
                    valueExpr source)
                  (fun result =>
                    Simulation.Interaction.bind
                      (match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error
                            .InvalidInstruction)
                      (fun valueResult =>
                        Simulation.Interaction.pure
                          (Functions.Source.Effectful.Outcome.regular
                            (valueResult.1.insert name valueResult.2),
                            { sourceCtx with
                              scope := name :: sourceCtx.scope }))))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.pure
                      (Structured.Outcome.regular targetAfterValue))) := by
            apply Simulation.Interaction.Rel.bind_custom hExprStrong
            intro sourceDone targetDone hDone
            rcases hDone with ⟨hRelated, hVarsDone⟩
            cases hRelated with
            | error hError =>
                exact .done (.error hError)
            | @ok sourceResult targetAfterValue hResult =>
                rcases sourceResult with ⟨sourceAfterValue, values⟩
                cases values with
                | nil =>
                    have hLength := hResult.valuesLength
                    simp at hLength
                | cons value tail =>
                    cases tail with
                    | cons other rest =>
                        have hLength := hResult.valuesLength
                        simp at hLength
                    | nil =>
                        have hValueStack :
                            targetAfterValue.evm.stack =
                              value :: target.evm.stack := by
                          simpa using hResult.stack
                        have hFinalState :
                            ActivationStateRel contract plan (name :: live)
                              0 frameBase .stack
                              (sourceAfterValue.insert name value)
                              targetAfterValue := by
                          exact hResult.state.declare_stack_live hValueStack
                            (by
                              intro other hOther
                              rcases List.mem_cons.mp hOther with hName | hLive
                              · exact .inl hName
                              · exact .inr hLive)
                            hLocation hStackOrder
                        apply Simulation.Interaction.Rel.done
                        apply Simulation.Interaction.ExceptRel.ok
                        refine ⟨rfl, .regular ?_⟩
                        exact
                          { compiler := .stack hAfter
                            planWF := hInvariant.planWF
                            defined :=
                              (hInvariant.defined.congr_vars
                                hVarsDone).insert_cons
                            state := hFinalState
                            stackLength := by
                              simp [hValueStack, Locals.Ctx.withLayout,
                                hInvariant.stackLength] }
          have hCoreNested :
              Simulation.Interaction.Rel
                (OpenStmtResultRel contract lowerCtx
                  { allocation :=
                      (AllocationSupport.allocateName
                        name beforeState.allocation).2
                    layout := name :: beforeState.layout }
                  (beforeLocals.withLayout
                    (name :: beforeLocals.layout))
                  plan returns (name :: live) frameBase .stack sourceCtx
                  { sourceCtx with scope := name :: sourceCtx.scope })
                (Simulation.Interaction.bind
                  (Simulation.Interaction.bind
                    (Functions.InteractionSemantics.Expr.openEval
                      valueExpr source)
                    (fun result =>
                      match result.2 with
                      | [value] =>
                          Simulation.Interaction.pure (result.1, value)
                      | _ =>
                          Simulation.Interaction.error
                            .InvalidInstruction))
                  (fun valueResult =>
                    Simulation.Interaction.pure
                      (Functions.Source.Effectful.Outcome.regular
                        (valueResult.1.insert name valueResult.2),
                        { sourceCtx with
                          scope := name :: sourceCtx.scope })))
                (Simulation.Interaction.bind
                  (Structured.InteractionSemantics.Code.openRun
                    valueCode target)
                  (fun targetAfterValue =>
                    Simulation.Interaction.pure
                      (Structured.Outcome.regular targetAfterValue))) := by
            rw [Simulation.Interaction.bind_assoc]
            exact hCore
          rw [Locals.InteractionPreservation.Stmt.TargetBlock.openRun_single_code]
          unfold Functions.InteractionSemantics.Stmt.openRun
            Functions.Source.Canonical.Stmt.run
            Expressions.InteractionSemantics.Stmt.openRun
          simp only [Functions.Source.Effectful.Control.Stmt.run,
            Expressions.EffectSemantics.Control.Stmt.run]
          unfold Locals.Source.Effectful.Expr.Control.evalOne
          change
            Simulation.Interaction.Rel _ _
              (Simulation.Interaction.bind
                (Structured.InteractionSemantics.Code.openRun
                  (valueCode ++
                    Locals.bindLocals 0 (name :: beforeLocals.layout))
                  target)
                (fun final =>
                  Simulation.Interaction.pure
                    (Structured.Outcome.regular final)))
          rw [Structured.InteractionSemantics.Code.openRun_append,
            show Locals.bindLocals 0 (name :: beforeLocals.layout) =
              [.bindLocals 0 (name :: beforeLocals.layout)] by rfl]
          have hBindRun :
              Structured.InteractionSemantics.Code.openRun
                  [.bindLocals 0 (name :: beforeLocals.layout)] =
                fun state => Simulation.Interaction.pure state := by
            funext state
            exact
              Locals.InteractionPreservation.Code.openRun_bindLocals
                0 (name :: beforeLocals.layout) state
          rw [hBindRun]
          simpa [Simulation.Interaction.bind,
            Functions.InteractionSemantics.Expr.openEval,
            Locals.InteractionSemantics.Expr.openEval,
            Functions.InteractionSemantics.primitiveSemantics,
            Functions.InteractionSemantics.stateModel,
            Locals.InteractionSemantics.stateModel,
            Locals.Source.Effectful.Ordinary.stateModel,
            Locals.Source.Effectful.StateModel.insert] using hCoreNested

end AllocationInteractionStatement
end Functions
end EvmCompiler
