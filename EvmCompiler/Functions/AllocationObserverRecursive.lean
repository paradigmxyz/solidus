import EvmCompiler.Functions.AllocationObserverDispatcher

namespace EvmCompiler
namespace Functions
namespace AllocationObserverRecursive

open AllocationObserverRelation
open AllocationObserverForward
open AllocationObserverDispatcher

abbrev Trace := Assembly.ResourceTrace

namespace BodyCursor

/--
Fuel-bounded recursive preservation for every compiler-owned source root in
one lowered program.

Calls may change the root, allocator depth, and frame base. Every main or
selected-function root enters through the same pass-owned artifact.
-/
def RecursiveProgramForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {transcript : Trace}
    (maxDepth : Nat)
    (fuelBound : Nat) : Prop :=
  ∀ {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {config : Frame.Config}
    {allocatorDepth frameBase : Nat},
    program.Scoped →
    Frame.FuelSafe config maxDepth →
    allocatorDepth + fuelBound ≤ maxDepth →
    AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config →
    AllocationObserverDispatcher.BodyCursor.RecursiveBlockForward
      (root := root) (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (fuelBound := fuelBound) (transcript := transcript)

/--
Fuel-bounded recursive preservation for compiler-selected stack-only roots.

The ordinary compiler proves that no function requires a scratch frame. The
recursive proof then uses the shared resource-indexed dispatcher and carries no
allocator configuration or synthetic frame state.
-/
def StackRecursiveProgramForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {transcript : Trace}
    (fuelBound : Nat) : Prop :=
  ∀ {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {allocatorDepth frameBase : Nat},
    program.Scoped →
    AllocationLowering.frameFunctions
        compilation.recipe compilation.stackSlots =
      [] →
    AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward
      (root := root) (resource := .stackOnly)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (fuelBound := fuelBound) (transcript := transcript)

/--
Dispatch one successful source statement in compiler-selected stack-only mode.

Every case delegates to the theorem owned by its adjacent pass. This theorem
owns only source syntax dispatch, strict fuel descent, and selected-root
construction for recursive calls.
-/
theorem controlledHeadResultStack
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {allocatorDepth frameBase sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hFrameFunctions :
      AllocationLowering.frameFunctions
          compilation.recipe compilation.stackSlots =
        [])
    (hProgramScoped : program.Scoped)
    (hRecursive :
      ∀ smallerBound,
        smallerBound ≤ sourceFuel + 1 →
          StackRecursiveProgramForward (allocation := allocation)
            (program := program) (expressions := expressions)
            (transcript := transcript) smallerBound)
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Control.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel stmt source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      AllocationObserverDispatcher.BodyCursor.ResourceBoundary cursor
        (resource := .stackOnly) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope
          (Functions.Scope.Stmt.outEnv live stmt)
          { stmts := rest } afterState afterLocals,
        AllocationObserverDispatcher.BodyCursor.ResourceControlledHeadResult
          cursor hBoundary afterState afterLocals headCode tail
          (resource := .stackOnly) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  cases stmt with
  | expr expr =>
      have hSourceCopy := hSource
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSourceCopy
      cases hEval :
          Locals.Source.Effectful.Expr.Control.eval
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            expr source with
      | error err =>
          simp [hEval] at hSourceCopy
      | ok result =>
          rcases result with ⟨sourceFinal, values⟩
          simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
          have hEq :
              (Functions.Source.Effectful.Outcome.regular sourceFinal,
                sourceCtx) =
              (sourceOutcome, finalCtx) :=
            Except.ok.inj hSourceCopy
          cases hEq
          obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.ResourceHeadResult.exprOfSafeRunStack
              cursor hSource hBoundary.sourceScope hBoundary.invariant
          exact
            ⟨afterState, afterLocals, headCode, tail,
              AllocationObserverDispatcher.BodyCursor.ResourceControlledHeadResult.of_no_control
                cursor hBoundary tail hHead
                (by
                  intro sourceFinal hOutcome
                  have hMode :=
                    congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                  contradiction)
                (by
                  intro sourceFinal hOutcome
                  have hMode :=
                    congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                  contradiction)⟩
  | let_ name valueExpr =>
      have hSourceCopy := hSource
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSourceCopy
      cases hEval :
          Locals.Source.Effectful.Expr.Control.evalOne
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            valueExpr source with
      | error err =>
          simp [hEval] at hSourceCopy
      | ok result =>
          rcases result with ⟨evalFinal, value⟩
          simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
          have hEq :
              (Functions.Source.Effectful.Outcome.regular
                  ((Functions.ObserverSemantics.stateModel transcript).insert
                    evalFinal name value),
                { sourceCtx with scope := name :: sourceCtx.scope }) =
              (sourceOutcome, finalCtx) :=
            Except.ok.inj hSourceCopy
          cases hEq
          obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.ResourceHeadResult.letOfSafeRunStack
              cursor hSource hBoundary.sourceScope hBoundary.invariant
          exact
            ⟨afterState, afterLocals, headCode, tail,
              AllocationObserverDispatcher.BodyCursor.ResourceControlledHeadResult.of_no_control
                cursor hBoundary tail hHead
                (by
                  intro sourceFinal hOutcome
                  have hMode :=
                    congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                  contradiction)
                (by
                  intro sourceFinal hOutcome
                  have hMode :=
                    congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                  contradiction)⟩
  | assign name valueExpr =>
      have hSourceCopy := hSource
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSourceCopy
      cases hContains :
          (Functions.ObserverSemantics.stateModel transcript).vars source
            |>.contains name with
      | false =>
          simp [hContains, Functions.Source.invalid, Structured.invalid]
            at hSourceCopy
      | true =>
          simp only [hContains, ↓reduceIte] at hSourceCopy
          cases hEval :
              Locals.Source.Effectful.Expr.Control.evalOne
                (Functions.ObserverSemantics.stateModel transcript)
                (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                  program.memoryContract transcript)
                valueExpr source with
          | error err =>
              simp [hEval] at hSourceCopy
          | ok result =>
              rcases result with ⟨evalFinal, value⟩
              simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
              have hEq :
                  (Functions.Source.Effectful.Outcome.regular
                      ((Functions.ObserverSemantics.stateModel transcript).withVars
                        evalFinal
                        (Locals.Source.Store.insert
                          ((Functions.ObserverSemantics.stateModel transcript).vars
                            evalFinal)
                          name value)),
                    sourceCtx) =
                  (sourceOutcome, finalCtx) :=
                Except.ok.inj hSourceCopy
              cases hEq
              obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                AllocationObserverDispatcher.BodyCursor.ResourceHeadResult.assignOfSafeRunStack
                  cursor hSource hBoundary.sourceScope hBoundary.invariant
              exact
                ⟨afterState, afterLocals, headCode, tail,
                  AllocationObserverDispatcher.BodyCursor.ResourceControlledHeadResult.of_no_control
                    cursor hBoundary tail hHead
                    (by
                      intro sourceFinal hOutcome
                      have hMode :=
                        congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                      contradiction)
                    (by
                      intro sourceFinal hOutcome
                      have hMode :=
                        congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                      contradiction)⟩
  | block body =>
      obtain ⟨afterState, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.ResourceBoundary.blockControlledHeadResultStack
          cursor hSource hBoundary
          (by
            intro bodyOutcome bodyCtx bodyCursor hOpen bodyBoundary
            exact
              hRecursive (sourceFuel + 1) (by omega)
                hProgramScoped hFrameFunctions
                bodyCursor (by omega) bodyBoundary hOpen)
      exact ⟨afterState, localsCtx, headCode, tail, hHead⟩
  | if_ cond body =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Control.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ fuel =>
          have hFinalCtx : finalCtx = sourceCtx := by
            rcases
                Functions.Source.Effectful.Stmt.run_if_cases
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource with hFalse | hTrue
            · rcases hFalse with
                ⟨afterCond, hCond, hOutcome, hFinal⟩
              exact hFinal
            · rcases hTrue with
                ⟨afterCond, bodyOutcome, hCond, hBody, hOutcome, hFinal⟩
              exact hFinal
          subst finalCtx
          obtain ⟨afterState, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.ResourceBoundary.ifControlledHeadResultStack
              cursor hSource hBoundary
              (by
                intro sourceAfterCond bodyOutcome bodyCtx bodyCursor hOpen
                  targetBodyStart bodyBoundary
                exact
                  hRecursive (fuel + 1) (by omega)
                    hProgramScoped hFrameFunctions
                    bodyCursor (by omega) bodyBoundary hOpen)
          exact ⟨afterState, localsCtx, headCode, tail, hHead⟩
  | switch scrutinee cases defaultBody =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Control.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ fuel =>
          have hFinalCtx : finalCtx = sourceCtx := by
            rcases
                Functions.Source.Effectful.Stmt.run_switch_cases
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource with hNone | hSome
            · rcases hNone with
                ⟨afterScrutinee, value, hEval, hSelect, hOutcome, hFinal⟩
              exact hFinal
            · rcases hSome with
                ⟨afterScrutinee, value, selected, bodyOutcome, hEval,
                  hSelect, hBody, hOutcome, hFinal⟩
              exact hFinal
          subst finalCtx
          obtain ⟨afterState, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.ResourceBoundary.switchControlledHeadResultStack
              cursor hSource hBoundary
              (by
                intro selected sourceAfterScrutinee bodyOutcome bodyCtx
                  selectedStart selectedPlanning bodyCursor hState hOpen
                  targetBodyStart bodyBoundary
                exact
                  hRecursive (fuel + 1) (by omega)
                    hProgramScoped hFrameFunctions
                    bodyCursor (by omega) bodyBoundary hOpen)
          exact ⟨afterState, localsCtx, headCode, tail, hHead⟩
  | for_ init cond post body =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Control.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ fuel =>
          let hLoopRecursive :
              AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward
                (root := root) (resource := .stackOnly)
                (allocatorDepth := allocatorDepth)
                (frameBase := frameBase) (fuelBound := fuel + 1)
                (transcript := transcript) :=
            hRecursive (fuel + 1) (by omega)
              hProgramScoped hFrameFunctions
          obtain ⟨afterState, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.ResourceBoundary.forControlledHeadResultStack
              cursor hSource hBoundary hLoopRecursive
          exact ⟨afterState, localsCtx, headCode, tail, hHead⟩
  | brk =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.ResourceBoundary.brkControlledHeadResultStack
          cursor hSource hBoundary
      exact ⟨afterState, afterLocals, headCode, tail, hHead⟩
  | cont =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.ResourceBoundary.contControlledHeadResultStack
          cursor hSource hBoundary
      exact ⟨afterState, afterLocals, headCode, tail, hHead⟩
  | leave =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.ResourceBoundary.leaveControlledHeadResultStack
          cursor hSource hBoundary
      exact ⟨afterState, afterLocals, headCode, tail, hHead⟩
  | call targets functionName args =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Control.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ callFuel =>
          rcases
              Functions.Source.Effectful.Stmt.run_call_cases
                (Functions.ObserverSemantics.stateModel transcript)
                (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                  program.memoryContract transcript)
                program hSource with hRegular | hHalt
          · rcases hRegular with ⟨sourceFinal, rfl, rfl⟩
            cases callFuel with
            | zero =>
                obtain
                    ⟨stateAfterArgs, argValues, selectedFn,
                      stateAfterCall, returnValues, returnStore,
                      hTargets, hArgs, hFind, hBody, hAssign, hFinal⟩ :=
                  Functions.Source.Effectful.Stmt.call_regular_parts
                    (Functions.ObserverSemantics.stateModel transcript)
                    (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                      program.memoryContract transcript)
                    program hSource
                simp [Functions.Source.Effectful.Control.FunDef.runBody,
                  Functions.Source.invalid, Structured.invalid] at hBody
            | succ fuel =>
                obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                  AllocationObserverDispatcher.BodyCursor.ResourceBoundary.callRegularControlledHeadResultStack
                    cursor hFrameFunctions hSource hBoundary
                    (by
                      intro selectedFn selected selectedPrepared hNoFrame
                        sourceBodyStart bodyOutcome bodyCtx' targetBodyStart
                        hOpen hInvariant hReturnFrame
                      have hSelectedFrameFunctions :
                          AllocationLowering.frameFunctions
                              selected.recipe selected.stackSlots =
                            [] := by
                        obtain ⟨hRecipe, hSlots, _hFrameName⟩ :=
                          compilation.selected_agrees selected
                        simpa [hRecipe, hSlots] using hFrameFunctions
                      let selectedRoot :=
                        AllocationObserverForward.BodyCursor.RootArtifact.ofSelected
                          selected selectedPrepared
                          (selected.bodyScoped hProgramScoped)
                      let selectedCursor := selectedRoot.cursor
                      have hPreparedMode :
                          selectedPrepared.mode = .stack :=
                        selectedPrepared.mode_eq_stack_of_noFrame hNoFrame
                      have hSelectedInvariant :
                          AllocationObserverContext.ActivationResourceInvariant
                            .stackOnly program.memoryContract allocatorDepth
                            selected.lowerCtx selected.bodyStart
                            selectedPrepared.returnCtx selectedPrepared.plan
                            ((selected.slots.returns.map Prod.fst).reverse ++
                              (selected.slots.params.map Prod.fst).reverse)
                            0
                            (selectedPrepared.mode.atStackDepth
                              (currentStackOrder selectedPrepared.plan
                                ((selected.slots.returns.map Prod.fst).reverse ++
                                  (selected.slots.params.map
                                    Prod.fst).reverse)).length)
                            sourceBodyStart targetBodyStart := by
                        simpa [hPreparedMode, ActivationMode.atStackDepth] using
                          hInvariant
                      let selectedBoundary :
                          AllocationObserverDispatcher.BodyCursor.ResourceBoundary
                            selectedCursor (resource := .stackOnly)
                            (allocatorDepth := allocatorDepth)
                            (frameBase := 0)
                            (mode :=
                              selectedPrepared.mode.atStackDepth
                                (currentStackOrder selectedPrepared.plan
                                  ((selected.slots.returns.map
                                      Prod.fst).reverse ++
                                    (selected.slots.params.map
                                      Prod.fst).reverse)).length)
                            (sourceCtx :=
                              Functions.Source.Effectful.FunDef.bodyCtx
                                selectedFn)
                            (source := sourceBodyStart)
                            (target := targetBodyStart) :=
                        AllocationObserverDispatcher.BodyCursor.ResourceBoundary.functionBody
                          selectedPrepared hProgramScoped hReturnFrame trivial
                          hSelectedInvariant
                      have hSelectedRecursive :
                          AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward
                            (root := selectedRoot)
                            (resource := .stackOnly)
                            (allocatorDepth := allocatorDepth)
                            (frameBase := 0) (fuelBound := fuel + 1)
                            (transcript := transcript) :=
                        hRecursive (fuel + 1) (by omega)
                          (root := selectedRoot)
                          (allocatorDepth := allocatorDepth)
                          (frameBase := 0)
                          hProgramScoped hSelectedFrameFunctions
                      have hBodyResult :=
                        hSelectedRecursive selectedCursor
                          (sourceFuel := fuel) (by omega)
                          selectedBoundary hOpen
                      obtain ⟨targetOutcome, hRuntime, hControl⟩ :=
                        hBodyResult.runtime
                      exact
                        ⟨targetOutcome, by
                          simpa [selectedRoot, selectedCursor,
                            AllocationObserverForward.BodyCursor.RootArtifact.ofSelected,
                            hPreparedMode, ActivationMode.atStackDepth] using
                            hRuntime⟩)
                exact
                  ⟨afterState, afterLocals, headCode, tail, hHead⟩
          · rcases hHalt with ⟨kind, sourceFinal, rfl, rfl⟩
            cases callFuel with
            | zero =>
                obtain
                    ⟨stateAfterArgs, argValues, selectedFn, hTargets,
                      hArgs, hFind, hBody⟩ :=
                  Functions.Source.Effectful.Stmt.call_halted_parts
                    (Functions.ObserverSemantics.stateModel transcript)
                    (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                      program.memoryContract transcript)
                    program hSource
                simp [Functions.Source.Effectful.Control.FunDef.runBody,
                  Functions.Source.invalid, Structured.invalid] at hBody
            | succ fuel =>
                obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                  AllocationObserverDispatcher.BodyCursor.ResourceBoundary.callHaltControlledHeadResultStack
                    cursor hFrameFunctions hSource hBoundary
                    (by
                      intro selectedFn selected selectedPrepared hNoFrame
                        sourceBodyStart bodyCtx' targetBodyStart
                        hOpen hInvariant hReturnFrame
                      have hSelectedFrameFunctions :
                          AllocationLowering.frameFunctions
                              selected.recipe selected.stackSlots =
                            [] := by
                        obtain ⟨hRecipe, hSlots, _hFrameName⟩ :=
                          compilation.selected_agrees selected
                        simpa [hRecipe, hSlots] using hFrameFunctions
                      let selectedRoot :=
                        AllocationObserverForward.BodyCursor.RootArtifact.ofSelected
                          selected selectedPrepared
                          (selected.bodyScoped hProgramScoped)
                      let selectedCursor := selectedRoot.cursor
                      have hPreparedMode :
                          selectedPrepared.mode = .stack :=
                        selectedPrepared.mode_eq_stack_of_noFrame hNoFrame
                      have hSelectedInvariant :
                          AllocationObserverContext.ActivationResourceInvariant
                            .stackOnly program.memoryContract allocatorDepth
                            selected.lowerCtx selected.bodyStart
                            selectedPrepared.returnCtx selectedPrepared.plan
                            ((selected.slots.returns.map Prod.fst).reverse ++
                              (selected.slots.params.map Prod.fst).reverse)
                            0
                            (selectedPrepared.mode.atStackDepth
                              (currentStackOrder selectedPrepared.plan
                                ((selected.slots.returns.map Prod.fst).reverse ++
                                  (selected.slots.params.map
                                    Prod.fst).reverse)).length)
                            sourceBodyStart targetBodyStart := by
                        simpa [hPreparedMode, ActivationMode.atStackDepth] using
                          hInvariant
                      let selectedBoundary :
                          AllocationObserverDispatcher.BodyCursor.ResourceBoundary
                            selectedCursor (resource := .stackOnly)
                            (allocatorDepth := allocatorDepth)
                            (frameBase := 0)
                            (mode :=
                              selectedPrepared.mode.atStackDepth
                                (currentStackOrder selectedPrepared.plan
                                  ((selected.slots.returns.map
                                      Prod.fst).reverse ++
                                    (selected.slots.params.map
                                      Prod.fst).reverse)).length)
                            (sourceCtx :=
                              Functions.Source.Effectful.FunDef.bodyCtx
                                selectedFn)
                            (source := sourceBodyStart)
                            (target := targetBodyStart) :=
                        AllocationObserverDispatcher.BodyCursor.ResourceBoundary.functionBody
                          selectedPrepared hProgramScoped hReturnFrame trivial
                          hSelectedInvariant
                      have hSelectedRecursive :
                          AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward
                            (root := selectedRoot)
                            (resource := .stackOnly)
                            (allocatorDepth := allocatorDepth)
                            (frameBase := 0) (fuelBound := fuel + 1)
                            (transcript := transcript) :=
                        hRecursive (fuel + 1) (by omega)
                          (root := selectedRoot)
                          (allocatorDepth := allocatorDepth)
                          (frameBase := 0)
                          hProgramScoped hSelectedFrameFunctions
                      have hBodyResult :=
                        hSelectedRecursive selectedCursor
                          (sourceFuel := fuel) (by omega)
                          selectedBoundary hOpen
                      obtain ⟨targetOutcome, hRuntime, hControl⟩ :=
                        hBodyResult.runtime
                      exact
                        ⟨targetOutcome, by
                          simpa [selectedRoot, selectedCursor,
                            AllocationObserverForward.BodyCursor.RootArtifact.ofSelected,
                            hPreparedMode, ActivationMode.atStackDepth] using
                            hRuntime⟩)
                exact
                  ⟨afterState, afterLocals, headCode, tail, hHead⟩
  | terminal kind =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.ResourceBoundary.terminalControlledHeadResultStack
          cursor hSource hBoundary
      exact ⟨afterState, afterLocals, headCode, tail, hHead⟩
  | terminalArgs kind args =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.ResourceBoundary.terminalArgsControlledHeadResultStack
          cursor hSource hBoundary
      exact ⟨afterState, afterLocals, headCode, tail, hHead⟩

/--
The canonical source-fuel induction for compiler-selected stack-only roots.

The proof shares the resource-indexed block result, control transport, exact
cursor composition, and selected-callee root interface with scratch recursion.
-/
theorem stackRecursiveProgramForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {transcript : Trace}
    (fuelBound : Nat) :
    StackRecursiveProgramForward (allocation := allocation)
      (program := program) (expressions := expressions)
      (transcript := transcript) fuelBound := by
  induction fuelBound using Nat.strong_induction_on with
  | h fuelBound ih =>
      intro compilation root allocatorDepth frameBase
        hProgramScoped hFrameFunctions
      intro scope live sourceBlock lowerState localsCtx mode sourceCtx
        finalCtx source target sourceFuel sourceOutcome cursor hFuel
        hBoundary hSource
      cases sourceFuel with
      | zero =>
          cases sourceBlock
          simp [Functions.Source.Effectful.Control.Block.runOpen,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ headFuel =>
          cases sourceBlock with
          | mk stmts =>
              cases stmts with
              | nil =>
                  exact
                    AllocationObserverDispatcher.BodyCursor.ResourceBoundary.nilBlockResult
                      cursor hBoundary hSource
              | cons stmt rest =>
                  have hSmaller :
                      StackRecursiveProgramForward (allocation := allocation)
                        (program := program) (expressions := expressions)
                        (transcript := transcript) (headFuel + 1) :=
                    ih (headFuel + 1) (by omega)
                  rcases
                      Functions.Source.Effectful.Block.runOpen_cons_cases
                        (Functions.ObserverSemantics.stateModel transcript)
                        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                          program.memoryContract transcript)
                        program hSource with
                    hRegular | hAbrupt
                  · rcases hRegular with
                      ⟨sourceMid, headCtx, hHeadSource, hTailSource⟩
                    obtain
                        ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                      controlledHeadResultStack hFrameFunctions hProgramScoped
                        (fun smallerBound hSmallerBound =>
                          ih smallerBound (by omega))
                        cursor hHeadSource hBoundary
                    exact
                      AllocationObserverDispatcher.BodyCursor.ResourceBoundary.consBlockResult
                        cursor hBoundary tail hHead
                        (by
                          intro sourceMid' targetMid midMode hForward hControl
                            hTailBoundary
                          rcases hForward with
                            ⟨forwardFuel, targetFuel, hForwardSource,
                              hTarget, hInvariant, hSameFrame, hEffect⟩
                          have hCanonicalSource :=
                            AllocationObserverSafety.SafeSemantics.stmt_run_eq
                              hHeadSource
                          have hSourceEq :
                              (Functions.Source.Effectful.Outcome.regular
                                  sourceMid',
                                headCtx) =
                              (Functions.Source.Effectful.Outcome.regular
                                  sourceMid,
                                headCtx) :=
                            Functions.Source.Effectful.Stmt.run_success_unique
                              (Functions.ObserverSemantics.stateModel
                                transcript)
                              (Functions.ObserverSemantics.primitiveSemantics
                                transcript)
                              program hForwardSource hCanonicalSource
                          cases hSourceEq
                          exact
                            hSmaller hProgramScoped hFrameFunctions tail
                              (sourceFuel := headFuel)
                              (by omega) hTailBoundary hTailSource)
                        (by
                          intro hNotRegular
                          exact False.elim (hNotRegular rfl))
                  · rcases hAbrupt with
                      ⟨headOutcome, headCtx, hHeadSource, hHeadMode,
                        rfl, rfl⟩
                    obtain
                        ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                      controlledHeadResultStack hFrameFunctions hProgramScoped
                        (fun smallerBound hSmallerBound =>
                          ih smallerBound (by omega))
                        cursor hHeadSource hBoundary
                    exact
                      AllocationObserverDispatcher.BodyCursor.ResourceBoundary.consBlockResult
                        cursor hBoundary tail hHead
                        (by
                          intro sourceMid targetMid midMode hForward hControl
                            hTailBoundary
                          rcases hForward with
                            ⟨forwardFuel, targetFuel, hForwardSource,
                              hTarget, hInvariant, hSameFrame, hEffect⟩
                          have hCanonicalSource :=
                            AllocationObserverSafety.SafeSemantics.stmt_run_eq
                              hHeadSource
                          have hSourceEq :=
                            Functions.Source.Effectful.Stmt.run_success_unique
                              (Functions.ObserverSemantics.stateModel
                                transcript)
                              (Functions.ObserverSemantics.primitiveSemantics
                                transcript)
                              program hCanonicalSource hForwardSource
                          exact
                            False.elim
                              (hHeadMode
                                (congrArg
                                  (fun result => result.1.mode)
                                  hSourceEq)))
                        (by
                          intro _
                          exact ⟨rfl, rfl⟩)

/--
Dispatch one successful source statement using only the checked theorem owned
by its adjacent lowering pass.

The recursive argument is the shared block interface at the next larger fuel
bound. This theorem performs no target interpretation and constructs no
compiler evidence.
-/
theorem controlledHeadResult
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root : AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt}
    {rest : List Functions.Stmt}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Frame.Config}
    {allocatorDepth frameBase maxDepth sourceFuel : Nat}
    {transcript : Trace}
    {mode : ActivationMode}
    {sourceCtx finalCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hProgramScoped : program.Scoped)
    (hFuelSafe : Frame.FuelSafe config maxDepth)
    (hDepthBound : allocatorDepth + (sourceFuel + 1) ≤ maxDepth)
    (hRecursive :
      ∀ smallerBound,
        smallerBound ≤ sourceFuel + 1 →
          RecursiveProgramForward (allocation := allocation)
            (program := program) (expressions := expressions)
            (transcript := transcript) maxDepth smallerBound)
    (cursor :
      AllocationObserverForward.BodyCursor.CoreCursor root scope live
        { stmts := stmt :: rest } lowerState localsCtx)
    (hSource :
      Functions.Source.Effectful.Control.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel stmt source =
        .ok (sourceOutcome, finalCtx))
    (hBoundary :
      AllocationObserverDispatcher.BodyCursor.Boundary cursor
        (config := config) (allocatorDepth := allocatorDepth)
        (frameBase := frameBase) (mode := mode)
        (sourceCtx := sourceCtx) (source := source) (target := target)) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        AllocationObserverForward.BodyCursor.CoreCursor root scope
          (Functions.Scope.Stmt.outEnv live stmt)
          { stmts := rest } afterState afterLocals,
        AllocationObserverDispatcher.BodyCursor.ControlledHeadResult
          cursor hBoundary afterState afterLocals headCode tail
          (config := config) (allocatorDepth := allocatorDepth)
          (frameBase := frameBase) (mode := mode)
          (sourceCtx := sourceCtx) (finalCtx := finalCtx)
          (source := source) (target := target)
          (sourceOutcome := sourceOutcome) := by
  cases stmt with
  | expr expr =>
      have hSourceCopy := hSource
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSourceCopy
      cases hEval :
          Locals.Source.Effectful.Expr.Control.eval
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            expr source with
      | error err =>
          simp [hEval] at hSourceCopy
      | ok result =>
          rcases result with ⟨sourceFinal, values⟩
          simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
          have hEq :
              (Functions.Source.Effectful.Outcome.regular sourceFinal,
                sourceCtx) =
              (sourceOutcome, finalCtx) :=
            Except.ok.inj hSourceCopy
          cases hEq
          obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.HeadResult.exprOfSafeRun
              cursor hConfig hSource hBoundary.sourceScope
              hBoundary.invariant
          exact
            ⟨afterState, afterLocals, headCode, tail,
              AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
                cursor hBoundary tail hHead
                (by
                  intro sourceFinal hOutcome
                  have hMode :=
                    congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                  contradiction)
                (by
                  intro sourceFinal hOutcome
                  have hMode :=
                    congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                  contradiction)⟩
  | let_ name valueExpr =>
      have hSourceCopy := hSource
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSourceCopy
      cases hEval :
          Locals.Source.Effectful.Expr.Control.evalOne
            (Functions.ObserverSemantics.stateModel transcript)
            (AllocationObserverSafety.SafeSemantics.primitiveSemantics
              program.memoryContract transcript)
            valueExpr source with
      | error err =>
          simp [hEval] at hSourceCopy
      | ok result =>
          rcases result with ⟨evalFinal, value⟩
          simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
          have hEq :
              (Functions.Source.Effectful.Outcome.regular
                  ((Functions.ObserverSemantics.stateModel transcript).insert
                    evalFinal name value),
                { sourceCtx with scope := name :: sourceCtx.scope }) =
              (sourceOutcome, finalCtx) :=
            Except.ok.inj hSourceCopy
          cases hEq
          obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.HeadResult.letOfSafeRun
              cursor hConfig hSource hBoundary.sourceScope
              hBoundary.invariant
          exact
            ⟨afterState, afterLocals, headCode, tail,
              AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
                cursor hBoundary tail hHead
                (by
                  intro sourceFinal hOutcome
                  have hMode :=
                    congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                  contradiction)
                (by
                  intro sourceFinal hOutcome
                  have hMode :=
                    congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                  contradiction)⟩
  | assign name valueExpr =>
      have hSourceCopy := hSource
      simp only [Functions.Source.Effectful.Control.Stmt.run] at hSourceCopy
      cases hContains :
          (Functions.ObserverSemantics.stateModel transcript).vars source
            |>.contains name with
      | false =>
          simp [hContains, Functions.Source.invalid, Structured.invalid]
            at hSourceCopy
      | true =>
          simp only [hContains, ↓reduceIte] at hSourceCopy
          cases hEval :
              Locals.Source.Effectful.Expr.Control.evalOne
                (Functions.ObserverSemantics.stateModel transcript)
                (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                  program.memoryContract transcript)
                valueExpr source with
          | error err =>
              simp [hEval] at hSourceCopy
          | ok result =>
              rcases result with ⟨evalFinal, value⟩
              simp only [hEval, Bind.bind, Except.bind] at hSourceCopy
              have hEq :
                  (Functions.Source.Effectful.Outcome.regular
                      ((Functions.ObserverSemantics.stateModel transcript).withVars
                        evalFinal
                        (Locals.Source.Store.insert
                          ((Functions.ObserverSemantics.stateModel transcript).vars
                            evalFinal)
                          name value)),
                    sourceCtx) =
                  (sourceOutcome, finalCtx) :=
                Except.ok.inj hSourceCopy
              cases hEq
              obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                AllocationObserverDispatcher.BodyCursor.HeadResult.assignOfSafeRun
                  cursor hConfig hSource hBoundary.sourceScope
                  hBoundary.invariant
              exact
                ⟨afterState, afterLocals, headCode, tail,
                  AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
                    cursor hBoundary tail hHead
                    (by
                      intro sourceFinal hOutcome
                      have hMode :=
                        congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                      contradiction)
                    (by
                      intro sourceFinal hOutcome
                      have hMode :=
                        congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                      contradiction)⟩
  | block body =>
      obtain ⟨afterState, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.Boundary.blockControlledHeadResult
          cursor hSource hBoundary
          (by
            intro bodyOutcome bodyCtx bodyCursor hOpen bodyBoundary
            exact
              hRecursive (sourceFuel + 1) (by omega)
                hProgramScoped hFuelSafe hDepthBound hConfig
                bodyCursor (by omega) bodyBoundary hOpen)
      exact ⟨afterState, localsCtx, headCode, tail, hHead⟩
  | if_ cond body =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Control.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ fuel =>
          have hFinalCtx : finalCtx = sourceCtx := by
            rcases
                Functions.Source.Effectful.Stmt.run_if_cases
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource with hFalse | hTrue
            · rcases hFalse with
                ⟨afterCond, hCond, hOutcome, hFinal⟩
              exact hFinal
            · rcases hTrue with
                ⟨afterCond, bodyOutcome, hCond, hBody, hOutcome, hFinal⟩
              exact hFinal
          subst finalCtx
          obtain ⟨afterState, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.Boundary.ifControlledHeadResult
              cursor hConfig hSource hBoundary
              (by
                intro sourceAfterCond bodyOutcome bodyCtx bodyCursor hOpen
                  targetBodyStart bodyBoundary
                exact
                  hRecursive (fuel + 1) (by omega)
                    hProgramScoped hFuelSafe (by omega) hConfig
                    bodyCursor (by omega) bodyBoundary hOpen)
          exact ⟨afterState, localsCtx, headCode, tail, hHead⟩
  | switch scrutinee cases defaultBody =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Control.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ fuel =>
          have hFinalCtx : finalCtx = sourceCtx := by
            rcases
                Functions.Source.Effectful.Stmt.run_switch_cases
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource with hNone | hSome
            · rcases hNone with
                ⟨afterScrutinee, value, hEval, hSelect, hOutcome, hFinal⟩
              exact hFinal
            · rcases hSome with
                ⟨afterScrutinee, value, selected, bodyOutcome, hEval,
                  hSelect, hBody, hOutcome, hFinal⟩
              exact hFinal
          subst finalCtx
          obtain ⟨afterState, headCode, tail, hHead⟩ :=
            AllocationObserverDispatcher.BodyCursor.Boundary.switchControlledHeadResult
              cursor hConfig hSource hBoundary
              (by
                intro selected sourceAfterScrutinee bodyOutcome bodyCtx
                  selectedStart selectedPlanning bodyCursor hState hOpen
                  targetBodyStart bodyBoundary
                exact
                  hRecursive (fuel + 1) (by omega)
                    hProgramScoped hFuelSafe (by omega) hConfig
                    bodyCursor (by omega) bodyBoundary hOpen)
          exact ⟨afterState, localsCtx, headCode, tail, hHead⟩
  | for_ init cond post body =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Control.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ fuel =>
          let hLoopRecursive :
              AllocationObserverDispatcher.BodyCursor.RecursiveBlockForward
                (root := root) (config := config)
                (allocatorDepth := allocatorDepth)
                (frameBase := frameBase) (fuelBound := fuel + 1)
                (transcript := transcript) :=
            hRecursive (fuel + 1) (by omega)
              hProgramScoped hFuelSafe (by omega) hConfig
          rcases
              Functions.Source.Effectful.Stmt.run_for_cases
                (Functions.ObserverSemantics.stateModel transcript)
                (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                  program.memoryContract transcript)
                program hSource with hRegular | hExit
          · rcases hRegular with
              ⟨sourceAfterInit, initCtx, sourceLoopFinal, hInit, hLoop,
                hOutcome, hFinal⟩
            subst sourceOutcome
            subst finalCtx
            obtain ⟨afterState, headCode, tail, hHead⟩ :=
              AllocationObserverDispatcher.BodyCursor.Boundary.forRegularHeadResult
                cursor hConfig hBoundary hLoopRecursive hInit hLoop
            exact
              ⟨afterState, localsCtx, headCode, tail,
                AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
                  cursor hBoundary tail hHead
                  (by
                    intro sourceFinal hOutcome
                    have hMode :=
                      congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                    contradiction)
                  (by
                    intro sourceFinal hOutcome
                    have hMode :=
                      congrArg Locals.Source.Effectful.Outcome.mode hOutcome
                    contradiction)⟩
          · rcases hExit with hLoopExit | hInitExit
            · rcases hLoopExit with
                ⟨sourceAfterInit, initCtx, hInit, hLoop, hIsExit, hFinal⟩
              subst finalCtx
              obtain ⟨afterState, headCode, tail, hHead⟩ :=
                AllocationObserverDispatcher.BodyCursor.Boundary.forExitHeadResult
                  cursor hConfig hBoundary hLoopRecursive hInit hLoop hIsExit
              exact
                ⟨afterState, localsCtx, headCode, tail,
                  AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
                    cursor hBoundary tail hHead
                    (by
                      intro sourceFinal hOutcome
                      exact hIsExit.ne_brk sourceFinal hOutcome)
                    (by
                      intro sourceFinal hOutcome
                      exact hIsExit.ne_cont sourceFinal hOutcome)⟩
            · rcases hInitExit with ⟨initCtx, hInit, hIsExit, hFinal⟩
              subst finalCtx
              obtain ⟨afterState, headCode, tail, hHead⟩ :=
                AllocationObserverDispatcher.BodyCursor.Boundary.forInitExitHeadResult
                  cursor hBoundary hLoopRecursive hInit hIsExit
              exact
                ⟨afterState, localsCtx, headCode, tail,
                  AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
                    cursor hBoundary tail hHead
                    (by
                      intro sourceFinal hOutcome
                      exact hIsExit.ne_brk sourceFinal hOutcome)
                    (by
                      intro sourceFinal hOutcome
                      exact hIsExit.ne_cont sourceFinal hOutcome)⟩
  | brk =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.Boundary.brkControlledHeadResult
          cursor hSource hBoundary
      exact ⟨afterState, afterLocals, headCode, tail, hHead⟩
  | cont =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.Boundary.contControlledHeadResult
          cursor hSource hBoundary
      exact ⟨afterState, afterLocals, headCode, tail, hHead⟩
  | leave =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.Boundary.leaveHeadResult
          cursor hConfig hSource hBoundary
      exact
        ⟨afterState, afterLocals, headCode, tail,
          AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hOutcome
              have hMode :=
                congrArg Locals.Source.Effectful.Outcome.mode hOutcome
              rw [
                Functions.Source.Effectful.Stmt.run_leave_mode
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource] at hMode
              cases hMode)
            (by
              intro sourceFinal hOutcome
              have hMode :=
                congrArg Locals.Source.Effectful.Outcome.mode hOutcome
              rw [
                Functions.Source.Effectful.Stmt.run_leave_mode
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource] at hMode
              cases hMode)⟩
  | call targets functionName args =>
      cases sourceFuel with
      | zero =>
          simp [Functions.Source.Effectful.Control.Stmt.run,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ callFuel =>
          rcases
              Functions.Source.Effectful.Stmt.run_call_cases
                (Functions.ObserverSemantics.stateModel transcript)
                (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                  program.memoryContract transcript)
                program hSource with hRegular | hHalt
          · rcases hRegular with ⟨sourceFinal, rfl, rfl⟩
            cases callFuel with
            | zero =>
                obtain
                    ⟨stateAfterArgs, argValues, selectedFn,
                      stateAfterCall, returnValues, returnStore,
                      hTargets, hArgs, hFind, hBody, hAssign, hFinal⟩ :=
                  Functions.Source.Effectful.Stmt.call_regular_parts
                    (Functions.ObserverSemantics.stateModel transcript)
                    (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                      program.memoryContract transcript)
                    program hSource
                simp [Functions.Source.Effectful.Control.FunDef.runBody,
                  Functions.Source.invalid, Structured.invalid] at hBody
            | succ fuel =>
                obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                  AllocationObserverDispatcher.BodyCursor.Boundary.callRegularHeadResult
                    cursor hConfig hSource hBoundary
                    (by
                      intro selectedFn selected selectedPrepared
                        sourceBodyStart bodyOutcome bodyCtx' targetBodyStart
                        calleeDepth calleeFrameBase hOpen hCalleeDepth
                        hInvariant hReturnFrame
                      have hRecipe :
                          selected.recipe = compilation.recipe :=
                        (compilation.selected_agrees selected).1
                      have hSelectedConfig :
                          AllocationSupport.scratchFrameConfig?
                              program.memoryContract
                              selected.recipe.frameWords =
                            some config := by
                        rw [hRecipe]
                        exact hConfig
                      have hSelectedBudget :
                          Frame.Budget config calleeDepth :=
                        hFuelSafe.depth_safe (by omega)
                      let selectedRoot :=
                        AllocationObserverForward.BodyCursor.RootArtifact.ofSelected
                          selected selectedPrepared
                          (selected.bodyScoped hProgramScoped)
                      let selectedCursor := selectedRoot.cursor
                      let selectedBoundary :
                          AllocationObserverDispatcher.BodyCursor.Boundary
                            selectedCursor (config := config)
                            (allocatorDepth := calleeDepth)
                            (frameBase := calleeFrameBase)
                            (mode :=
                              selectedPrepared.mode.atStackDepth
                                (currentStackOrder selectedPrepared.plan
                                  ((selected.slots.returns.map Prod.fst).reverse ++
                                    (selected.slots.params.map
                                      Prod.fst).reverse)).length)
                            (sourceCtx :=
                              Functions.Source.Effectful.FunDef.bodyCtx
                                selectedFn)
                            (source := sourceBodyStart)
                            (target := targetBodyStart) :=
                        AllocationObserverDispatcher.BodyCursor.Boundary.functionBody
                          selectedPrepared hProgramScoped hReturnFrame
                          hSelectedBudget hInvariant
                      have hSelectedRecursive :
                          AllocationObserverDispatcher.BodyCursor.RecursiveBlockForward
                            (root := selectedRoot)
                            (config := config)
                            (allocatorDepth := calleeDepth)
                            (frameBase := calleeFrameBase)
                            (fuelBound := fuel + 1)
                            (transcript := transcript) :=
                        hRecursive (fuel + 1) (by omega)
                          hProgramScoped hFuelSafe (by omega)
                          hSelectedConfig
                      have hBodyResult :=
                        hSelectedRecursive selectedCursor
                          (sourceFuel := fuel) (by omega)
                          selectedBoundary hOpen
                      obtain ⟨targetOutcome, hRuntime, hControl⟩ :=
                        hBodyResult.runtime
                      exact ⟨targetOutcome, hRuntime⟩)
                exact
                  ⟨afterState, afterLocals, headCode, tail, hHead⟩
          · rcases hHalt with ⟨kind, sourceFinal, rfl, rfl⟩
            cases callFuel with
            | zero =>
                obtain
                    ⟨stateAfterArgs, argValues, selectedFn, hTargets,
                      hArgs, hFind, hBody⟩ :=
                  Functions.Source.Effectful.Stmt.call_halted_parts
                    (Functions.ObserverSemantics.stateModel transcript)
                    (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                      program.memoryContract transcript)
                    program hSource
                simp [Functions.Source.Effectful.Control.FunDef.runBody,
                  Functions.Source.invalid, Structured.invalid] at hBody
            | succ fuel =>
                obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                  AllocationObserverDispatcher.BodyCursor.Boundary.callHaltHeadResult
                    cursor hConfig hSource hBoundary
                    (by
                      intro selectedFn selected selectedPrepared
                        sourceBodyStart bodyOutcome bodyCtx' targetBodyStart
                        calleeDepth calleeFrameBase hOpen hCalleeDepth
                        hInvariant hReturnFrame
                      have hRecipe :
                          selected.recipe = compilation.recipe :=
                        (compilation.selected_agrees selected).1
                      have hSelectedConfig :
                          AllocationSupport.scratchFrameConfig?
                              program.memoryContract
                              selected.recipe.frameWords =
                            some config := by
                        rw [hRecipe]
                        exact hConfig
                      have hSelectedBudget :
                          Frame.Budget config calleeDepth :=
                        hFuelSafe.depth_safe (by omega)
                      let selectedRoot :=
                        AllocationObserverForward.BodyCursor.RootArtifact.ofSelected
                          selected selectedPrepared
                          (selected.bodyScoped hProgramScoped)
                      let selectedCursor := selectedRoot.cursor
                      let selectedBoundary :
                          AllocationObserverDispatcher.BodyCursor.Boundary
                            selectedCursor (config := config)
                            (allocatorDepth := calleeDepth)
                            (frameBase := calleeFrameBase)
                            (mode :=
                              selectedPrepared.mode.atStackDepth
                                (currentStackOrder selectedPrepared.plan
                                  ((selected.slots.returns.map Prod.fst).reverse ++
                                    (selected.slots.params.map
                                      Prod.fst).reverse)).length)
                            (sourceCtx :=
                              Functions.Source.Effectful.FunDef.bodyCtx
                                selectedFn)
                            (source := sourceBodyStart)
                            (target := targetBodyStart) :=
                        AllocationObserverDispatcher.BodyCursor.Boundary.functionBody
                          selectedPrepared hProgramScoped hReturnFrame
                          hSelectedBudget hInvariant
                      have hSelectedRecursive :
                          AllocationObserverDispatcher.BodyCursor.RecursiveBlockForward
                            (root := selectedRoot)
                            (config := config)
                            (allocatorDepth := calleeDepth)
                            (frameBase := calleeFrameBase)
                            (fuelBound := fuel + 1)
                            (transcript := transcript) :=
                        hRecursive (fuel + 1) (by omega)
                          hProgramScoped hFuelSafe (by omega)
                          hSelectedConfig
                      have hBodyResult :=
                        hSelectedRecursive selectedCursor
                          (sourceFuel := fuel) (by omega)
                          selectedBoundary hOpen
                      obtain ⟨targetOutcome, hRuntime, hControl⟩ :=
                        hBodyResult.runtime
                      exact ⟨targetOutcome, hRuntime⟩)
                exact
                  ⟨afterState, afterLocals, headCode, tail, hHead⟩
  | terminal kind =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.Boundary.terminalHeadResult
          cursor hSource hBoundary
      exact
        ⟨afterState, afterLocals, headCode, tail,
          AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hOutcome
              have hMode :=
                congrArg Locals.Source.Effectful.Outcome.mode hOutcome
              rw [
                Functions.Source.Effectful.Stmt.run_terminal_mode
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource] at hMode
              cases hMode)
            (by
              intro sourceFinal hOutcome
              have hMode :=
                congrArg Locals.Source.Effectful.Outcome.mode hOutcome
              rw [
                Functions.Source.Effectful.Stmt.run_terminal_mode
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource] at hMode
              cases hMode)⟩
  | terminalArgs kind args =>
      obtain ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
        AllocationObserverDispatcher.BodyCursor.Boundary.terminalArgsHeadResult
          cursor hConfig hSource hBoundary
      exact
        ⟨afterState, afterLocals, headCode, tail,
          AllocationObserverDispatcher.BodyCursor.ControlledHeadResult.of_no_control
            cursor hBoundary tail hHead
            (by
              intro sourceFinal hOutcome
              have hMode :=
                congrArg Locals.Source.Effectful.Outcome.mode hOutcome
              rw [
                Functions.Source.Effectful.Stmt.run_terminalArgs_mode
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource] at hMode
              cases hMode)
            (by
              intro sourceFinal hOutcome
              have hMode :=
                congrArg Locals.Source.Effectful.Outcome.mode hOutcome
              rw [
                Functions.Source.Effectful.Stmt.run_terminalArgs_mode
                  (Functions.ObserverSemantics.stateModel transcript)
                  (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                    program.memoryContract transcript)
                  program hSource] at hMode
              cases hMode)⟩

/--
The canonical source-fuel dispatcher for the Functions-to-allocation
boundary.

Strong induction is solely on source fuel. Every nested block and selected
callee body is discharged through `RecursiveBlockForward`; one regular head
is combined with its exact tail by the dispatcher sequence theorem.
-/
theorem recursiveProgramForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {transcript : Trace}
    (maxDepth fuelBound : Nat) :
    RecursiveProgramForward (allocation := allocation)
      (program := program) (expressions := expressions)
      (transcript := transcript) maxDepth fuelBound := by
  induction fuelBound using Nat.strong_induction_on with
  | h fuelBound ih =>
      intro compilation root config allocatorDepth frameBase
        hProgramScoped hFuelSafe hDepthBound hConfig
      intro scope live sourceBlock lowerState localsCtx mode sourceCtx
        finalCtx source target sourceFuel sourceOutcome cursor hFuel
        hBoundary hSource
      cases sourceFuel with
      | zero =>
          cases sourceBlock
          simp [Functions.Source.Effectful.Control.Block.runOpen,
            Functions.Source.invalid, Structured.invalid] at hSource
      | succ headFuel =>
          cases sourceBlock with
          | mk stmts =>
              cases stmts with
              | nil =>
                  exact
                    AllocationObserverDispatcher.BodyCursor.Boundary.nilBlockResult
                      cursor hBoundary hSource
              | cons stmt rest =>
                  have hSmaller :
                      RecursiveProgramForward (allocation := allocation)
                        (program := program) (expressions := expressions)
                        (transcript := transcript) maxDepth
                        (headFuel + 1) :=
                    ih (headFuel + 1) (by omega)
                  rcases
                      Functions.Source.Effectful.Block.runOpen_cons_cases
                        (Functions.ObserverSemantics.stateModel transcript)
                        (AllocationObserverSafety.SafeSemantics.primitiveSemantics
                          program.memoryContract transcript)
                        program hSource with
                    hRegular | hAbrupt
                  · rcases hRegular with
                      ⟨sourceMid, headCtx, hHeadSource, hTailSource⟩
                    obtain
                        ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                      controlledHeadResult hConfig hProgramScoped hFuelSafe
                        (by omega)
                        (fun smallerBound hSmallerBound =>
                          ih smallerBound (by omega))
                        cursor
                        hHeadSource hBoundary
                    exact
                      AllocationObserverDispatcher.BodyCursor.Boundary.consBlockResult
                        cursor hBoundary tail hHead
                        (by
                          intro sourceMid' targetMid midMode hForward hControl
                            hTailBoundary
                          rcases hForward with
                            ⟨forwardFuel, targetFuel, hForwardSource,
                              hTarget, hInvariant, hSameFrame, hEffect⟩
                          have hCanonicalSource :=
                            AllocationObserverSafety.SafeSemantics.stmt_run_eq
                              hHeadSource
                          have hSourceEq :
                              (Functions.Source.Effectful.Outcome.regular
                                  sourceMid',
                                headCtx) =
                              (Functions.Source.Effectful.Outcome.regular
                                  sourceMid,
                                headCtx) :=
                            Functions.Source.Effectful.Stmt.run_success_unique
                              (Functions.ObserverSemantics.stateModel
                                transcript)
                              (Functions.ObserverSemantics.primitiveSemantics
                                transcript)
                              program hForwardSource hCanonicalSource
                          cases hSourceEq
                          exact
                            hSmaller hProgramScoped hFuelSafe
                              (by omega) hConfig tail
                              (sourceFuel := headFuel)
                              (by omega) hTailBoundary
                              hTailSource)
                        (by
                          intro hNotRegular
                          exact False.elim (hNotRegular rfl))
                  · rcases hAbrupt with
                      ⟨headOutcome, headCtx, hHeadSource, hHeadMode,
                        rfl, rfl⟩
                    obtain
                        ⟨afterState, afterLocals, headCode, tail, hHead⟩ :=
                      controlledHeadResult hConfig hProgramScoped hFuelSafe
                        (by omega)
                        (fun smallerBound hSmallerBound =>
                          ih smallerBound (by omega))
                        cursor
                        hHeadSource hBoundary
                    exact
                      AllocationObserverDispatcher.BodyCursor.Boundary.consBlockResult
                        cursor hBoundary tail hHead
                        (by
                          intro sourceMid targetMid midMode hForward hControl
                            hTailBoundary
                          rcases hForward with
                            ⟨forwardFuel, targetFuel, hForwardSource,
                              hTarget, hInvariant, hSameFrame, hEffect⟩
                          have hCanonicalSource :=
                            AllocationObserverSafety.SafeSemantics.stmt_run_eq
                              hHeadSource
                          have hSourceEq :=
                            Functions.Source.Effectful.Stmt.run_success_unique
                              (Functions.ObserverSemantics.stateModel
                                transcript)
                              (Functions.ObserverSemantics.primitiveSemantics
                                transcript)
                              program hCanonicalSource hForwardSource
                          exact
                            False.elim
                              (hHeadMode
                                (congrArg
                                  (fun result => result.1.mode)
                                  hSourceEq)))
                        (by
                          intro _
                          exact ⟨rfl, rfl⟩)

/--
Specialize the program-wide fuel induction to one selected function boundary.
-/
theorem recursiveBlockForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {calleeName : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions calleeName fn}
    {prepared : AllocationObserverCall.SelectedCallee.Prepared artifact}
    {config : Frame.Config}
    {allocatorDepth frameBase maxDepth : Nat}
    {transcript : Trace}
    (fuelBound : Nat)
    (hProgramScoped : program.Scoped)
    (hFuelSafe : Frame.FuelSafe config maxDepth)
    (hDepthBound : allocatorDepth + fuelBound ≤ maxDepth)
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config) :
    AllocationObserverDispatcher.BodyCursor.RecursiveBlockForward
      (root :=
        AllocationObserverForward.BodyCursor.RootArtifact.ofSelected
          artifact prepared (artifact.bodyScoped hProgramScoped))
      (config := config)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (fuelBound := fuelBound) (transcript := transcript) :=
  recursiveProgramForward (allocation := allocation)
    (program := program) (expressions := expressions)
    (transcript := transcript) maxDepth fuelBound hProgramScoped hFuelSafe
    hDepthBound hConfig

/--
Specialize the stack-only source-fuel induction to any compiler-owned root.
-/
theorem stackRecursiveBlockForward
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation :
      AllocationObserverForward.Compilation allocation program expressions}
    {root :
      AllocationObserverForward.BodyCursor.RootArtifact compilation}
    {allocatorDepth frameBase : Nat}
    {transcript : Trace}
    (fuelBound : Nat)
    (hProgramScoped : program.Scoped)
    (hFrameFunctions :
      AllocationLowering.frameFunctions
          compilation.recipe compilation.stackSlots =
        []) :
    AllocationObserverDispatcher.BodyCursor.ResourceRecursiveBlockForward
      (root := root) (resource := .stackOnly)
      (allocatorDepth := allocatorDepth) (frameBase := frameBase)
      (fuelBound := fuelBound) (transcript := transcript) :=
  stackRecursiveProgramForward (allocation := allocation)
    (program := program) (expressions := expressions)
    (transcript := transcript) fuelBound hProgramScoped hFrameFunctions

end BodyCursor
end AllocationObserverRecursive
end Functions
end EvmCompiler
