import EvmCompiler.Functions.StackExactFuelPreservation

/-!
Compiler-owned recursive closure for stack allocation preservation.

The one-step theorem below is structural: it closes every nested source block
and fallthrough tail produced by the scheduler, while calls at source fuel zero
truncate before entering a callee. The source-fuel theorem builds on this base
and owns recursive callee dispatch without exposing a call oracle.
-/

namespace EvmCompiler
namespace Functions
namespace StackRecursivePreservation

open StackRelation
open StackStatementPreservation
open StackBlockPreservation
open StackExactFuelPreservation

variable (returnNames : List Name)

mutual

private def blockMeasure : Functions.Block → Nat
  | { stmts } => stmtListMeasure stmts

private def stmtListMeasure : List Functions.Stmt → Nat
  | [] => 0
  | stmt :: rest => stmtMeasure stmt + stmtListMeasure rest + 1

private def caseListMeasure : List (Word × Functions.Block) → Nat
  | [] => 0
  | (_, body) :: rest => blockMeasure body + caseListMeasure rest + 1

private def defaultMeasure : Option Functions.Block → Nat
  | none => 0
  | some body => blockMeasure body + 1

private def stmtMeasure : Functions.Stmt → Nat
  | .block body => blockMeasure body + 1
  | .if_ _ body => blockMeasure body + 1
  | .switch _ cases defaultBody =>
      caseListMeasure cases + defaultMeasure defaultBody + 1
  | .for_ init _ post body =>
      blockMeasure init + blockMeasure post + blockMeasure body + 1
  | _ => 0

end

@[simp] private theorem blockMeasure_eq (body : Functions.Block) :
    blockMeasure body = stmtListMeasure body.stmts := by
  cases body
  rfl

private theorem caseChild_measure_lt
    {cases : List (Word × Functions.Block)} {body : Functions.Block}
    (hChild : CaseChild cases body) :
    blockMeasure body < caseListMeasure cases := by
  induction hChild with
  | head =>
      simp only [caseListMeasure]
      omega
  | tail _ ih =>
      simp only [caseListMeasure]
      omega

private theorem defaultChild_measure_lt
    {defaultBody : Option Functions.Block} {body : Functions.Block}
    (hChild : DefaultChild defaultBody body) :
    blockMeasure body < defaultMeasure defaultBody := by
  cases hChild
  simp [defaultMeasure]

private theorem switchChild_measure_lt
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block} {body : Functions.Block}
    (hChild : SwitchChild cases defaultBody body)
    (scrutinee : Functions.Expr 1) (rest : List Functions.Stmt) :
    stmtListMeasure body.stmts <
      stmtListMeasure (.switch scrutinee cases defaultBody :: rest) := by
  cases hChild with
  | case hCase =>
      have hLt := caseChild_measure_lt hCase
      rw [blockMeasure_eq] at hLt
      simp only [stmtListMeasure, stmtMeasure]
      omega
  | default hDefault =>
      have hLt := defaultChild_measure_lt hDefault
      rw [blockMeasure_eq] at hLt
      simp only [stmtListMeasure, stmtMeasure]
      omega

private theorem forChild_measure_lt
    {outerCtx initCtx : Locals.Ctx} {init post body child : Functions.Block}
    {childTargets : StackSchedule.ControlTargets} {childCtx : Locals.Ctx}
    (hChild :
      ForChild outerCtx initCtx init post body childTargets childCtx child)
    (cond : Functions.Expr 1) (rest : List Functions.Stmt) :
    stmtListMeasure child.stmts <
      stmtListMeasure (.for_ init cond post body :: rest) := by
  cases hChild <;>
    simp only [stmtListMeasure, stmtMeasure, blockMeasure_eq] <;> omega

private theorem blockWFStmts
    {canBreak canContinue inFunction : Bool} {body : Functions.Block}
    (hWF : Functions.Block.WF canBreak canContinue inFunction body) :
    Functions.Block.WF canBreak canContinue inFunction
      { stmts := body.stmts } := by
  cases body
  exact hWF

private theorem blockStmtWF
    {canBreak canContinue inFunction : Bool} {body : Functions.Block}
    (hWF :
      Functions.Stmt.WF canBreak canContinue inFunction (.block body)) :
    Functions.Block.WF canBreak canContinue inFunction body := by
  cases hWF
  assumption

private theorem ifStmtWF
    {canBreak canContinue inFunction : Bool} {cond : Functions.Expr 1}
    {body : Functions.Block}
    (hWF :
      Functions.Stmt.WF canBreak canContinue inFunction (.if_ cond body)) :
    Functions.Block.WF canBreak canContinue inFunction body := by
  cases hWF
  assumption

private theorem blockScopedStmts
    {sourceEnv : List Name} {body : Functions.Block}
    (hScoped : Functions.Scope.Block.Scoped sourceEnv body) :
    Functions.Scope.StmtList.Scoped sourceEnv body.stmts := by
  cases body
  exact hScoped

private theorem blockSupportedStmts
    {body : Functions.Block}
    (hSupported : Functions.InteractionSemantics.Block.OpenSupported body) :
    Functions.InteractionSemantics.StmtList.OpenSupported body.stmts := by
  cases body
  exact hSupported

private theorem zeroPairOfOnePair
    {sourceProgram : Functions.Program}
    {targetProgram : Expressions.Program}
    {targets : StackSchedule.ControlTargets}
    {targetCtx finalCtx : Locals.Ctx}
    {stmts : List Functions.Stmt} {finalLayout : Locals.Layout}
    {code : List Expressions.Stmt}
    (hOne :
      ControlScheduledListPreservesAt sourceProgram targetProgram targets
          returnNames targetCtx finalCtx stmts finalLayout code 1 ∧
        finalCtx.layout.Nodup) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames targetCtx finalCtx stmts finalLayout code 0 ∧
      finalCtx.layout.Nodup :=
  ⟨controlListAtZero returnNames sourceProgram targetProgram targets targetCtx
      finalCtx stmts finalLayout code hOne.1.1,
    hOne.2⟩

/- Structural compiler closure at one source step. Every schedule, layout,
lowering, and Locals compilation artifact is an output of the existing passes;
none appears as an assumed semantic certificate. -/
private theorem compiledBlockAtOne
    (returnNames : List Name)
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel syntaxFuel : Nat)
    {canBreak canContinue inFunction : Bool}
    {sourceEnv : List Name} {body : Functions.Block}
    {facts : List AllocationLivenessFacts.Point}
    {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hWF : Functions.Block.WF canBreak canContinue inFunction body)
    (hScoped : Functions.Scope.StmtList.Scoped sourceEnv body.stmts)
    (hSupported :
      Functions.InteractionSemantics.StmtList.OpenSupported body.stmts)
    (hControl :
      StackLoweringCompilation.ControlCtxAgrees canBreak canContinue targets
        targetCtx)
    (hReturns : lowerCtx.returns = returnNames)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout body.stmts facts = some (points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx body.stmts points =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hNodup : targetCtx.layout.Nodup)
    (hMeasure : blockMeasure body < syntaxFuel) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames targetCtx finalCtx body.stmts finalLayout code 1 ∧
      finalCtx.layout.Nodup := by
  have hPositive : syntaxFuel ≠ 0 := by omega
  obtain ⟨nextFuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hPositive
  rcases body with ⟨stmts⟩
  cases stmts with
  | nil =>
      cases facts with
      | nil =>
          simp [StackSchedule.scheduleStmtListFuelWithTargets] at hSchedule
          have hPoints := hSchedule.1
          subst points
          have hFinal := hSchedule.2.symm
          subst finalLayout
          have hLowered := StackLowering.lowerStmtListFuel_nil_components hLower
          subst lowered
          simp [Locals.Block.compileOpen] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact
            ⟨StackBlockPreservation.controlNilAt returnNames sourceProgram
              targetProgram targets targetCtx 1,
              hNodup⟩
      | cons fact restFacts =>
          simp [StackSchedule.scheduleStmtListFuelWithTargets] at hSchedule
  | cons stmt rest =>
      have hCurrentBound : stmtListMeasure (stmt :: rest) ≤ nextFuel := by
        simpa only [blockMeasure_eq] using Nat.lt_succ_iff.mp hMeasure
      cases facts with
      | nil =>
          simp [StackSchedule.scheduleStmtListFuelWithTargets] at hSchedule
      | cons fact restFacts =>
          cases points with
          | nil =>
              obtain ⟨_order, _rawPoint, _hOrder, _hPoint, hCases⟩ :=
                StackSchedule.scheduleStmtListFuelWithTargets_cons_components
                  hSchedule
              rcases hCases with hFalls | hStops
              · obtain ⟨_hFalls, _retain, _tail, _tailFinal, _hRetain,
                    _hTail, hPoints, _hFinal⟩ := hFalls
                simp at hPoints
              · simp at hStops
          | cons point points =>
              cases hWF with
              | cons hStmtWF hRestWF =>
                have hTailZero :
                    ∀ {tailLayout tailFinal : Locals.Layout}
                      {tailLowered : List Locals.Stmt}
                      {middleCtx tailFinalCtx : Locals.Ctx}
                      {tailCode : List Expressions.Stmt},
                      middleCtx.layout = tailLayout →
                      middleCtx.layout.Nodup →
                      Locals.Ctx.SameControl targetCtx middleCtx →
                      StackSchedule.scheduleStmtListFuelWithTargets targets
                          scheduleFuel pinned tailLayout rest restFacts =
                        some (points, tailFinal) →
                      StackLowering.lowerStmtListFuel lowerFuel lowerCtx rest
                          points = some tailLowered →
                      Locals.Block.compileOpen middleCtx
                          { stmts := tailLowered } =
                        some (tailCode, tailFinalCtx) →
                      ControlScheduledListPreservesAt sourceProgram
                          targetProgram targets returnNames middleCtx
                          tailFinalCtx rest tailFinal tailCode 0 ∧
                        tailFinalCtx.layout.Nodup := by
                  intro tailLayout tailFinal tailLowered middleCtx tailFinalCtx
                    tailCode hMiddleLayout hMiddleNodup hSame hTailSchedule
                    hTailLower hTailCompile
                  have hTailMeasure :
                      blockMeasure { stmts := rest } < nextFuel := by
                    change stmtListMeasure rest < nextFuel
                    have hBound := hCurrentBound
                    simp only [stmtListMeasure] at hBound
                    omega
                  have hTailOne :=
                    compiledBlockAtOne returnNames sourceProgram targetProgram
                      lowerCtx targets pinned scheduleFuel lowerFuel nextFuel
                      (canBreak := canBreak) (canContinue := canContinue)
                      (inFunction := inFunction)
                      (sourceEnv := Functions.Scope.Stmt.outEnv sourceEnv stmt)
                      (body := { stmts := rest })
                      hRestWF
                      hScoped.2 hSupported.2
                      (hControl.afterSameControl hSame) hReturns
                      (by simpa [hMiddleLayout] using hTailSchedule)
                      hTailLower hTailCompile hMiddleNodup hTailMeasure
                  exact zeroPairOfOnePair returnNames hTailOne
                cases stmt with
                | expr expr =>
                    exact
                      exprConsAt_of_compilers returnNames sourceProgram
                        targetProgram lowerCtx targets pinned scheduleFuel
                        lowerFuel 0 expr rest fact restFacts hNodup hScoped.1
                        hSupported.1 hSchedule hLower hCompile hTailZero
                | let_ name value =>
                    exact
                      letConsAt_of_compilers returnNames sourceProgram
                        targetProgram lowerCtx targets pinned scheduleFuel
                        lowerFuel 0 name value rest fact restFacts hNodup
                        hScoped.1.2 hSupported.1 hSchedule hLower hCompile
                        hTailZero
                | assign name value =>
                    exact
                      assignConsAt_of_compilers returnNames sourceProgram
                        targetProgram lowerCtx targets pinned scheduleFuel
                        lowerFuel 0 name value rest fact restFacts hNodup
                        hScoped.1.2 hSupported.1 hSchedule hLower hCompile
                        hTailZero
                | block body =>
                    have hBodyWF := blockStmtWF hStmtWF
                    apply blockConsAt_of_compilers returnNames sourceProgram
                      targetProgram lowerCtx targets pinned scheduleFuel
                      lowerFuel 0 body rest fact restFacts
                      hNodup hSchedule hLower hCompile
                    · intro childCtx bodyFacts rawRegion bodyLowered bodyCode
                        bodyFinalCtx hSame hChildSchedule hChildLower
                        hChildCompile hChildNodup
                      have hChildMeasure : blockMeasure body < nextFuel := by
                        simp only [stmtListMeasure, stmtMeasure] at hCurrentBound
                        omega
                      have hChildOne :=
                        have hChildListSchedule :=
                          StackSchedule.scheduleBlockFuelWithTargets_statementList
                            hChildSchedule
                        compiledBlockAtOne returnNames sourceProgram
                          targetProgram lowerCtx targets
                          (StackSchedule.layoutSet childCtx.layout)
                          ((scheduleFuel - 1) - 1)
                          ((lowerFuel - 1) - 1) nextFuel
                          (canBreak := canBreak)
                          (canContinue := canContinue)
                          (inFunction := inFunction)
                          (sourceEnv := sourceEnv)
                          (body := body)
                          (facts := bodyFacts.points)
                          (points := rawRegion.points)
                          (finalLayout := rawRegion.finalLayout)
                          hBodyWF
                          (blockScopedStmts
                            (show Functions.Scope.Block.Scoped sourceEnv body
                              from hScoped.1))
                          (blockSupportedStmts
                            (show
                              Functions.InteractionSemantics.Block.OpenSupported
                                body
                              from hSupported.1))
                          ((hControl.afterSameControl hSame).withLayout
                            rawRegion.entry.target)
                          hReturns
                          (by
                            simpa [Locals.Ctx.withLayout] using
                              hChildListSchedule)
                          hChildLower hChildCompile hChildNodup hChildMeasure
                      exact (zeroPairOfOnePair returnNames hChildOne).1
                    · exact hTailZero
                | if_ cond body =>
                    have hBodyWF := ifStmtWF hStmtWF
                    apply ifConsAtOne_of_compilers returnNames sourceProgram
                      targetProgram lowerCtx targets pinned scheduleFuel
                      lowerFuel cond body rest fact restFacts
                      hNodup hScoped.1.1 hSupported.1.1 hSchedule hLower hCompile
                    · intro childCtx bodyFacts rawRegion bodyLowered bodyCode
                        bodyFinalCtx hSame hChildSchedule hChildLower
                        hChildCompile hChildNodup
                      have hChildMeasure : blockMeasure body < nextFuel := by
                        simp only [stmtListMeasure, stmtMeasure] at hCurrentBound
                        omega
                      have hChildOne :=
                        have hChildListSchedule :=
                          StackSchedule.scheduleBlockFuelWithTargets_statementList
                            hChildSchedule
                        compiledBlockAtOne returnNames sourceProgram
                          targetProgram lowerCtx targets
                          (StackSchedule.layoutSet childCtx.layout)
                          ((scheduleFuel - 1) - 1)
                          ((lowerFuel - 1) - 1) nextFuel
                          (canBreak := canBreak)
                          (canContinue := canContinue)
                          (inFunction := inFunction)
                          (sourceEnv := sourceEnv)
                          (body := body)
                          (facts := bodyFacts.points)
                          (points := rawRegion.points)
                          (finalLayout := rawRegion.finalLayout)
                          hBodyWF
                          (blockScopedStmts hScoped.1.2)
                          (blockSupportedStmts hSupported.1.2)
                          ((hControl.afterSameControl hSame).withLayout
                            rawRegion.entry.target)
                          hReturns
                          (by
                            simpa [Locals.Ctx.withLayout] using
                              hChildListSchedule)
                          hChildLower hChildCompile hChildNodup hChildMeasure
                      exact (zeroPairOfOnePair returnNames hChildOne).1
                    · exact hTailZero
                | switch scrutinee cases defaultBody =>
                    cases hStmtWF with
                    | switch hCasesWF hDefaultWF =>
                        apply switchConsAtOne_of_compilers returnNames
                          sourceProgram targetProgram lowerCtx targets pinned
                          scheduleFuel lowerFuel scrutinee cases defaultBody rest
                          fact restFacts hNodup hScoped.1.1 hSupported.1.1
                          hSchedule hLower hCompile
                        · intro child childCtx bodyFacts rawRegion bodyLowered
                            bodyCode bodyFinalCtx hOrigin hSame hChildSchedule
                            hChildLower hChildCompile hChildNodup
                          have hChildWF := hOrigin.wf hCasesWF hDefaultWF
                          have hChildMeasure : blockMeasure child < nextFuel := by
                            rw [blockMeasure_eq]
                            exact lt_of_lt_of_le
                              (switchChild_measure_lt hOrigin scrutinee rest)
                              hCurrentBound
                          have hChildOne :=
                            have hChildListSchedule :=
                              StackSchedule.scheduleBlockFuelWithTargets_statementList
                                hChildSchedule
                            compiledBlockAtOne returnNames sourceProgram
                              targetProgram lowerCtx targets
                              (StackSchedule.layoutSet childCtx.layout)
                              ((scheduleFuel - 1) - 1)
                              ((lowerFuel - 1) - 1) nextFuel
                              (canBreak := canBreak)
                              (canContinue := canContinue)
                              (inFunction := inFunction)
                              (sourceEnv := sourceEnv)
                              (body := child)
                              (facts := bodyFacts.points)
                              (points := rawRegion.points)
                              (finalLayout := rawRegion.finalLayout)
                              hChildWF
                              (blockScopedStmts
                                (hOrigin.scopePreserved hScoped.1.2.1
                                  hScoped.1.2.2))
                              (blockSupportedStmts
                                (hOrigin.supported hSupported.1.2.1
                                  hSupported.1.2.2))
                              ((hControl.afterSameControl hSame).withLayout
                                rawRegion.entry.target)
                              hReturns
                              (by
                                simpa [Locals.Ctx.withLayout] using
                                  hChildListSchedule)
                              hChildLower hChildCompile
                              hChildNodup hChildMeasure
                          exact (zeroPairOfOnePair returnNames hChildOne).1
                        · exact hTailZero
                | for_ init cond post body =>
                    cases hStmtWF with
                    | for_ hInitWF hPostWF hBodyWF =>
                        apply forConsAtOne_of_compilers returnNames
                          sourceProgram targetProgram lowerCtx targets pinned
                          scheduleFuel lowerFuel init cond post body rest fact
                          restFacts hNodup hScoped.1.2.1 hSupported.1.2.1
                          hSchedule hLower hCompile
                        · intro childFuel hChildFuel loopOuterCtx loopInitCtx
                            childTargets child childCtx childFacts rawRegion
                            childLowered childCode childFinalCtx hOrigin
                            hChildSchedule hChildLower hChildCompile
                            hChildNodup
                          obtain ⟨childEnv, hChildScoped⟩ :=
                            hOrigin.scopePreserved hScoped.1.1
                              hScoped.1.2.2.1 hScoped.1.2.2.2
                          obtain ⟨childBreak, childContinue, hChildWF,
                              hChildControl⟩ :=
                            hOrigin.wfAndControl hInitWF hPostWF hBodyWF
                          have hChildMeasure : blockMeasure child < nextFuel := by
                            rw [blockMeasure_eq]
                            exact lt_of_lt_of_le
                              (forChild_measure_lt hOrigin cond rest)
                              hCurrentBound
                          have hChildOne :=
                            have hChildListSchedule :=
                              StackSchedule.scheduleBlockFuelWithTargets_statementList
                                hChildSchedule
                            compiledBlockAtOne returnNames sourceProgram
                              targetProgram lowerCtx childTargets
                              (StackSchedule.layoutSet childCtx.layout)
                              ((scheduleFuel - 1) - 1)
                              ((lowerFuel - 1) - 1) nextFuel
                              (canBreak := childBreak)
                              (canContinue := childContinue)
                              (inFunction := inFunction)
                              (sourceEnv := childEnv)
                              (body := child)
                              (facts := childFacts.points)
                              (points := rawRegion.points)
                              (finalLayout := rawRegion.finalLayout)
                              hChildWF
                              (blockScopedStmts hChildScoped)
                              (blockSupportedStmts
                                (hOrigin.supported hSupported.1.1
                                  hSupported.1.2.2.1 hSupported.1.2.2.2))
                              (hChildControl.withLayout rawRegion.entry.target)
                              hReturns
                              (by
                                simpa [Locals.Ctx.withLayout] using
                                  hChildListSchedule)
                              hChildLower hChildCompile
                              hChildNodup hChildMeasure
                          have hZero := zeroPairOfOnePair returnNames hChildOne
                          have hFuelZero : childFuel = 0 := by omega
                          subst childFuel
                          simpa using hZero
                        · exact hTailZero
                | brk =>
                    cases hStmtWF with
                    | brk hAllowed =>
                        exact brkControlListAt_of_compilers returnNames
                          sourceProgram targetProgram lowerCtx targets pinned
                          scheduleFuel lowerFuel 0 rest fact restFacts hNodup
                          hControl hAllowed hSchedule hLower hCompile
                | cont =>
                    cases hStmtWF with
                    | cont hAllowed =>
                        exact contControlListAt_of_compilers returnNames
                          sourceProgram targetProgram lowerCtx targets pinned
                          scheduleFuel lowerFuel 0 rest fact restFacts hNodup
                          hControl hAllowed hSchedule hLower hCompile
                | leave =>
                    exact leaveControlListAt_of_compilers returnNames
                      sourceProgram targetProgram lowerCtx targets pinned
                      scheduleFuel lowerFuel 0 rest fact restFacts hNodup
                      hReturns hSchedule hLower hCompile
                | call callTargets functionName args =>
                    exact callConsAtOne_of_compilers returnNames sourceProgram
                      targetProgram lowerCtx targets pinned scheduleFuel
                      lowerFuel callTargets functionName args rest fact
                      restFacts hNodup hSchedule hLower hCompile hTailZero
                | terminal kind =>
                    cases hStmtWF with
                    | terminal hArgCount =>
                        exact terminalControlListAt_of_compilers returnNames
                          sourceProgram targetProgram lowerCtx targets pinned
                          scheduleFuel lowerFuel 0 kind rest fact restFacts
                          hNodup hArgCount hSchedule hLower hCompile
                | terminalArgs kind args =>
                    exact terminalArgsControlListAt_of_compilers returnNames
                      sourceProgram targetProgram lowerCtx targets pinned
                      scheduleFuel lowerFuel 0 kind args rest fact restFacts
                      hNodup hScoped.1 hSupported.1 hSchedule hLower hCompile
termination_by syntaxFuel
decreasing_by all_goals omega

/-- Compiler-owned structural closure at one source step. The recursive syntax
budget is computed internally and does not appear at the theorem boundary. -/
theorem compiledListAtOne
    (returnNames : List Name)
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel : Nat)
    {canBreak canContinue inFunction : Bool}
    {sourceEnv : List Name} {stmts : List Functions.Stmt}
    {facts : List AllocationLivenessFacts.Point}
    {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hWF : Functions.Block.WF canBreak canContinue inFunction { stmts })
    (hScoped : Functions.Scope.StmtList.Scoped sourceEnv stmts)
    (hSupported : Functions.InteractionSemantics.StmtList.OpenSupported stmts)
    (hControl :
      StackLoweringCompilation.ControlCtxAgrees canBreak canContinue targets
        targetCtx)
    (hReturns : lowerCtx.returns = returnNames)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout stmts facts = some (points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx stmts points =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hNodup : targetCtx.layout.Nodup) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames targetCtx finalCtx stmts finalLayout code 1 ∧
      finalCtx.layout.Nodup := by
  apply compiledBlockAtOne returnNames sourceProgram targetProgram lowerCtx
    targets pinned scheduleFuel lowerFuel
    (blockMeasure ({ stmts := stmts } : Functions.Block) + 1)
    (body := { stmts := stmts }) hWF hScoped hSupported hControl hReturns
    hSchedule hLower hCompile hNodup
  omega

private def CalleePreservesAt
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (sourceFuel : Nat) : Prop :=
  ∀ (functionName : Name) (args : List (Functions.Expr 1))
    (callCtx : Locals.Ctx) (fn : Functions.FunDef),
    Functions.Source.FunList.find? functionName sourceProgram.functions =
        some fn →
    ∀ (targetFuel : Nat)
      {suffix : List Word} {returns : List Structured.ReturnDest}
      {source sourceAfterArgs : Locals.Source.State}
      {target targetAfterArgs : Structured.RunState}
      {argValues : List Word},
      StateRel callCtx.layout suffix returns source target →
      Locals.InteractionPreservation.Expr.ResultRel args.length
          source target (sourceAfterArgs, argValues) targetAfterArgs →
      (∀ {proc : Expressions.Proc},
        Expressions.EffectSemantics.ProcList.lookup? functionName
            targetProgram.procs = some proc →
        Expressions.TargetFuel.Covers targetProgram sourceFuel
          (targetFuel - 1) proc.body.stmts) →
      Simulation.Interaction.ForwardRel
        FuelTruncated
        (StackCallPreservation.OpenAttachedCallResultRel
          fn.returns.length target.evm.stack returns)
        (Functions.InteractionSemantics.FunDef.openRunBody sourceProgram
          fn argValues sourceFuel sourceAfterArgs)
        (Expressions.InteractionSemantics.Stmt.openRun targetProgram
          targetFuel (.call functionName) targetAfterArgs)

private theorem compiledListAt_of_callees
    (returnNames : List Name)
    (sourceProgram : Functions.Program)
    (targetProgram : Expressions.Program)
    (lowerCtx : StackLowering.Ctx)
    (targets : StackSchedule.ControlTargets)
    (pinned : AllocationLiveness.LiveSet)
    (scheduleFuel lowerFuel sourceFuel : Nat)
    {canBreak canContinue inFunction : Bool}
    {sourceEnv : List Name} {stmts : List Functions.Stmt}
    {facts : List AllocationLivenessFacts.Point}
    {points : List StackSchedule.Point}
    {finalLayout : Locals.Layout} {lowered : List Locals.Stmt}
    {targetCtx finalCtx : Locals.Ctx} {code : List Expressions.Stmt}
    (hFunctions : lowerCtx.functions = sourceProgram.functions)
    (hCallees :
      ∀ calleeFuel, calleeFuel < sourceFuel →
        CalleePreservesAt sourceProgram targetProgram calleeFuel)
    (hWF : Functions.Block.WF canBreak canContinue inFunction { stmts })
    (hScoped : Functions.Scope.StmtList.Scoped sourceEnv stmts)
    (hSupported : Functions.InteractionSemantics.StmtList.OpenSupported stmts)
    (hControl :
      StackLoweringCompilation.ControlCtxAgrees canBreak canContinue targets
        targetCtx)
    (hReturns : lowerCtx.returns = returnNames)
    (hSchedule :
      StackSchedule.scheduleStmtListFuelWithTargets targets scheduleFuel pinned
          targetCtx.layout stmts facts = some (points, finalLayout))
    (hLower :
      StackLowering.lowerStmtListFuel lowerFuel lowerCtx stmts points =
        some lowered)
    (hCompile :
      Locals.Block.compileOpen targetCtx { stmts := lowered } =
        some (code, finalCtx))
    (hNodup : targetCtx.layout.Nodup) :
    ControlScheduledListPreservesAt sourceProgram targetProgram targets
        returnNames targetCtx finalCtx stmts finalLayout code sourceFuel ∧
      finalCtx.layout.Nodup := by
  induction sourceFuel using Nat.strong_induction_on generalizing lowerCtx
      targets pinned scheduleFuel lowerFuel canBreak canContinue inFunction
      sourceEnv stmts facts points finalLayout lowered targetCtx finalCtx code with
  | h sourceFuel ih =>
      cases sourceFuel with
      | zero =>
          exact zeroPairOfOnePair returnNames
            (compiledListAtOne returnNames sourceProgram targetProgram lowerCtx
              targets pinned scheduleFuel lowerFuel hWF hScoped hSupported
              hControl hReturns hSchedule hLower hCompile hNodup)
      | succ sourceFuel =>
          cases sourceFuel with
          | zero =>
              exact compiledListAtOne returnNames sourceProgram targetProgram
                lowerCtx targets pinned scheduleFuel lowerFuel hWF hScoped
                hSupported hControl hReturns hSchedule hLower hCompile hNodup
          | succ innerFuel =>
              cases stmts with
              | nil =>
                  cases facts with
                  | nil =>
                      simp [StackSchedule.scheduleStmtListFuelWithTargets]
                          at hSchedule
                      have hPoints := hSchedule.1
                      subst points
                      have hFinal := hSchedule.2.symm
                      subst finalLayout
                      have hLowered :=
                        StackLowering.lowerStmtListFuel_nil_components hLower
                      subst lowered
                      simp [Locals.Block.compileOpen] at hCompile
                      rcases hCompile with ⟨rfl, rfl⟩
                      exact
                        ⟨StackBlockPreservation.controlNilAt returnNames
                          sourceProgram targetProgram targets targetCtx
                          (innerFuel + 2), hNodup⟩
                  | cons fact restFacts =>
                      simp [StackSchedule.scheduleStmtListFuelWithTargets]
                        at hSchedule
              | cons stmt rest =>
                  cases facts with
                  | nil =>
                      simp [StackSchedule.scheduleStmtListFuelWithTargets]
                        at hSchedule
                  | cons fact restFacts =>
                      cases points with
                      | nil =>
                          obtain ⟨_order, _rawPoint, _hOrder, _hPoint,
                              hCases⟩ :=
                            StackSchedule.scheduleStmtListFuelWithTargets_cons_components
                              hSchedule
                          rcases hCases with hFalls | hStops
                          · obtain ⟨_hFalls, _retain, _tail, _tailFinal,
                                _hRetain, _hTail, hPoints, _hFinal⟩ := hFalls
                            simp at hPoints
                          · simp at hStops
                      | cons point points =>
                          cases hWF with
                          | cons hStmtWF hRestWF =>
                            have hTail :
                                ∀ {tailLayout tailFinal : Locals.Layout}
                                  {tailLowered : List Locals.Stmt}
                                  {middleCtx tailFinalCtx : Locals.Ctx}
                                  {tailCode : List Expressions.Stmt},
                                  middleCtx.layout = tailLayout →
                                  middleCtx.layout.Nodup →
                                  Locals.Ctx.SameControl targetCtx middleCtx →
                                  StackSchedule.scheduleStmtListFuelWithTargets
                                      targets scheduleFuel pinned tailLayout
                                      rest restFacts =
                                    some (points, tailFinal) →
                                  StackLowering.lowerStmtListFuel lowerFuel
                                      lowerCtx rest points = some tailLowered →
                                  Locals.Block.compileOpen middleCtx
                                      { stmts := tailLowered } =
                                    some (tailCode, tailFinalCtx) →
                                  ControlScheduledListPreservesAt sourceProgram
                                      targetProgram targets returnNames middleCtx
                                      tailFinalCtx rest tailFinal tailCode
                                      (innerFuel + 1) ∧
                                    tailFinalCtx.layout.Nodup := by
                              intro tailLayout tailFinal tailLowered middleCtx
                                tailFinalCtx tailCode hMiddleLayout
                                hMiddleNodup hSame hTailSchedule hTailLower
                                hTailCompile
                              apply ih (innerFuel + 1) (by omega) lowerCtx
                                targets pinned scheduleFuel lowerFuel
                                (sourceEnv :=
                                  Functions.Scope.Stmt.outEnv sourceEnv stmt)
                                hFunctions
                              · intro calleeFuel hLt
                                exact hCallees calleeFuel (by omega)
                              · exact hRestWF
                              · exact hScoped.2
                              · exact hSupported.2
                              · exact hControl.afterSameControl hSame
                              · exact hReturns
                              · simpa [hMiddleLayout] using hTailSchedule
                              · exact hTailLower
                              · exact hTailCompile
                              · exact hMiddleNodup
                            cases stmt with
                            | expr expr =>
                                simpa [Nat.add_assoc] using
                                  (exprConsAt_of_compilers returnNames
                                    sourceProgram targetProgram lowerCtx targets
                                    pinned scheduleFuel lowerFuel
                                    (innerFuel + 1) expr rest fact restFacts
                                    hNodup hScoped.1 hSupported.1 hSchedule
                                    hLower hCompile hTail)
                            | let_ name value =>
                                simpa [Nat.add_assoc] using
                                  (letConsAt_of_compilers returnNames
                                    sourceProgram targetProgram lowerCtx targets
                                    pinned scheduleFuel lowerFuel
                                    (innerFuel + 1) name value rest fact
                                    restFacts hNodup hScoped.1.2 hSupported.1
                                    hSchedule hLower hCompile hTail)
                            | assign name value =>
                                simpa [Nat.add_assoc] using
                                  (assignConsAt_of_compilers returnNames
                                    sourceProgram targetProgram lowerCtx targets
                                    pinned scheduleFuel lowerFuel
                                    (innerFuel + 1) name value rest fact
                                    restFacts hNodup hScoped.1.2 hSupported.1
                                    hSchedule hLower hCompile hTail)
                            | block body =>
                                rcases body with ⟨bodyStmts⟩
                                have hBodyWF := blockStmtWF hStmtWF
                                apply blockConsAt_of_compilers returnNames
                                  sourceProgram targetProgram lowerCtx targets
                                  pinned scheduleFuel lowerFuel (innerFuel + 1)
                                  { stmts := bodyStmts } rest fact restFacts
                                  hNodup hSchedule
                                  hLower hCompile
                                · intro childCtx bodyFacts rawRegion bodyLowered
                                    bodyCode bodyFinalCtx hSame hChildSchedule
                                    hChildLower hChildCompile hChildNodup
                                  have hChildListSchedule :=
                                    StackSchedule.scheduleBlockFuelWithTargets_statementList
                                      hChildSchedule
                                  exact (ih (innerFuel + 1) (by omega) lowerCtx
                                    targets (StackSchedule.layoutSet childCtx.layout)
                                    ((scheduleFuel - 1) - 1)
                                    ((lowerFuel - 1) - 1)
                                    (sourceEnv := sourceEnv) hFunctions
                                    (fun calleeFuel hLt =>
                                      hCallees calleeFuel (by omega))
                                    hBodyWF
                                    (blockScopedStmts hScoped.1)
                                    (blockSupportedStmts hSupported.1)
                                    ((hControl.afterSameControl hSame).withLayout
                                      rawRegion.entry.target)
                                    hReturns
                                    (by simpa [Locals.Ctx.withLayout] using
                                      hChildListSchedule)
                                    hChildLower hChildCompile hChildNodup).1
                                · exact hTail
                            | if_ cond body =>
                                rcases body with ⟨bodyStmts⟩
                                cases hStmtWF with
                                | if_ hBodyWF =>
                                    apply ifConsAtSucc_of_compilers returnNames
                                      sourceProgram targetProgram lowerCtx targets
                                      pinned scheduleFuel lowerFuel innerFuel cond
                                      { stmts := bodyStmts } rest fact restFacts
                                      hNodup hScoped.1.1
                                      hSupported.1.1 hSchedule hLower hCompile
                                    · intro childCtx bodyFacts rawRegion
                                        bodyLowered bodyCode bodyFinalCtx hSame
                                        hChildSchedule hChildLower hChildCompile
                                        hChildNodup
                                      have hChildListSchedule :=
                                        StackSchedule.scheduleBlockFuelWithTargets_statementList
                                          hChildSchedule
                                      exact (ih innerFuel (by omega) lowerCtx
                                        targets
                                        (StackSchedule.layoutSet childCtx.layout)
                                        ((scheduleFuel - 1) - 1)
                                        ((lowerFuel - 1) - 1)
                                        (sourceEnv := sourceEnv) hFunctions
                                        (fun calleeFuel hLt =>
                                          hCallees calleeFuel (by omega))
                                        hBodyWF
                                        (blockScopedStmts hScoped.1.2)
                                        (blockSupportedStmts hSupported.1.2)
                                        ((hControl.afterSameControl hSame).withLayout
                                          rawRegion.entry.target)
                                        hReturns
                                        (by simpa [Locals.Ctx.withLayout] using
                                          hChildListSchedule)
                                        hChildLower hChildCompile hChildNodup).1
                                    · exact hTail
                            | switch scrutinee cases defaultBody =>
                                cases hStmtWF with
                                | switch hCasesWF hDefaultWF =>
                                    apply switchConsAtSucc_of_compilers
                                      returnNames sourceProgram targetProgram
                                      lowerCtx targets pinned scheduleFuel
                                      lowerFuel innerFuel scrutinee cases
                                      defaultBody rest fact restFacts hNodup
                                      hScoped.1.1 hSupported.1.1 hSchedule hLower
                                      hCompile
                                    · intro child childCtx bodyFacts rawRegion
                                        bodyLowered bodyCode bodyFinalCtx hOrigin
                                        hSame hChildSchedule hChildLower
                                        hChildCompile hChildNodup
                                      rcases child with ⟨childStmts⟩
                                      have hChildListSchedule :=
                                        StackSchedule.scheduleBlockFuelWithTargets_statementList
                                          hChildSchedule
                                      exact (ih innerFuel (by omega) lowerCtx
                                        targets
                                        (StackSchedule.layoutSet childCtx.layout)
                                        ((scheduleFuel - 1) - 1)
                                        ((lowerFuel - 1) - 1)
                                        (sourceEnv := sourceEnv) hFunctions
                                        (fun calleeFuel hLt =>
                                          hCallees calleeFuel (by omega))
                                        (hOrigin.wf hCasesWF hDefaultWF)
                                        (blockScopedStmts
                                          (hOrigin.scopePreserved hScoped.1.2.1
                                            hScoped.1.2.2))
                                        (blockSupportedStmts
                                          (hOrigin.supported hSupported.1.2.1
                                            hSupported.1.2.2))
                                        ((hControl.afterSameControl hSame).withLayout
                                          rawRegion.entry.target)
                                        hReturns
                                        (by simpa [Locals.Ctx.withLayout] using
                                          hChildListSchedule)
                                        hChildLower hChildCompile hChildNodup).1
                                    · exact hTail
                            | for_ init cond post body =>
                                cases hStmtWF with
                                | for_ hInitWF hPostWF hBodyWF =>
                                    apply forConsAtSucc_of_compilers returnNames
                                      sourceProgram targetProgram lowerCtx targets
                                      pinned scheduleFuel lowerFuel innerFuel init
                                      cond post body rest fact restFacts hNodup
                                      hScoped.1.2.1 hSupported.1.2.1 hSchedule
                                      hLower hCompile
                                    · intro childFuel hChildFuel loopOuterCtx
                                        loopInitCtx childTargets child childCtx
                                        childFacts rawRegion childLowered childCode
                                        childFinalCtx hOrigin hChildSchedule
                                        hChildLower hChildCompile hChildNodup
                                      obtain ⟨childEnv, hChildScoped⟩ :=
                                        hOrigin.scopePreserved hScoped.1.1
                                          hScoped.1.2.2.1 hScoped.1.2.2.2
                                      obtain ⟨childBreak, childContinue,
                                          hChildWF, hChildControl⟩ :=
                                        hOrigin.wfAndControl hInitWF hPostWF
                                          hBodyWF
                                      rcases child with ⟨childStmts⟩
                                      have hChildListSchedule :=
                                        StackSchedule.scheduleBlockFuelWithTargets_statementList
                                          hChildSchedule
                                      exact ih childFuel (by omega) lowerCtx
                                        childTargets
                                        (StackSchedule.layoutSet childCtx.layout)
                                        ((scheduleFuel - 1) - 1)
                                        ((lowerFuel - 1) - 1)
                                        (sourceEnv := childEnv) hFunctions
                                        (fun calleeFuel hLt =>
                                          hCallees calleeFuel (by omega))
                                        hChildWF
                                        (blockScopedStmts hChildScoped)
                                        (blockSupportedStmts
                                          (hOrigin.supported hSupported.1.1
                                            hSupported.1.2.2.1
                                            hSupported.1.2.2.2))
                                        (hChildControl.withLayout
                                          rawRegion.entry.target)
                                        hReturns
                                        (by simpa [Locals.Ctx.withLayout] using
                                          hChildListSchedule)
                                        hChildLower hChildCompile hChildNodup
                                    · exact hTail
                            | brk =>
                                cases hStmtWF with
                                | brk hAllowed =>
                                    exact brkControlListAt_of_compilers
                                      returnNames sourceProgram targetProgram
                                      lowerCtx targets pinned scheduleFuel
                                      lowerFuel (innerFuel + 1) rest fact restFacts
                                      hNodup hControl hAllowed hSchedule hLower
                                      hCompile
                            | cont =>
                                cases hStmtWF with
                                | cont hAllowed =>
                                    exact contControlListAt_of_compilers
                                      returnNames sourceProgram targetProgram
                                      lowerCtx targets pinned scheduleFuel
                                      lowerFuel (innerFuel + 1) rest fact restFacts
                                      hNodup hControl hAllowed hSchedule hLower
                                      hCompile
                            | leave =>
                                exact leaveControlListAt_of_compilers returnNames
                                  sourceProgram targetProgram lowerCtx targets
                                  pinned scheduleFuel lowerFuel (innerFuel + 1)
                                  rest fact restFacts hNodup hReturns hSchedule
                                  hLower hCompile
                            | call callTargets functionName args =>
                                apply callConsAtSucc_of_compilers returnNames
                                  sourceProgram targetProgram lowerCtx targets
                                  pinned scheduleFuel lowerFuel innerFuel
                                  callTargets functionName args rest fact restFacts
                                  hFunctions hNodup hScoped.1.2.2 hSupported.1
                                  hSchedule hLower hCompile
                                · exact hCallees innerFuel (by omega) functionName
                                    args
                                · exact hTail
                            | terminal kind =>
                                cases hStmtWF with
                                | terminal hArgCount =>
                                    exact terminalControlListAt_of_compilers
                                      returnNames sourceProgram targetProgram
                                      lowerCtx targets pinned scheduleFuel
                                      lowerFuel (innerFuel + 1) kind rest fact
                                      restFacts hNodup hArgCount hSchedule hLower
                                      hCompile
                            | terminalArgs kind args =>
                                exact terminalArgsControlListAt_of_compilers
                                  returnNames sourceProgram targetProgram lowerCtx
                                  targets pinned scheduleFuel lowerFuel
                                  (innerFuel + 1) kind args rest fact restFacts
                                  hNodup hScoped.1 hSupported.1 hSchedule hLower
                                  hCompile

end StackRecursivePreservation
end Functions
end EvmCompiler
