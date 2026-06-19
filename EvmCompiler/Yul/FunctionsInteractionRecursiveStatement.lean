import EvmCompiler.Yul.FunctionsInteractionRecursiveExpression
import EvmCompiler.Yul.FunctionsInteractionSelectedStatementCall
import EvmCompiler.Yul.FunctionsInteractionTargetCost

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRecursiveStatement

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation

/-- One compiler-selected statement at fixed source and target fuels.  The
target-fuel premise is internal proof accounting over the ordinary compiler
output; it is not part of the public compiler theorem. -/
def StmtForwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (sourceFuel targetFuel : Nat) : Prop :=
  ∀ {compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {stmt : AstStmt}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx},
    SolcValidation.StmtOk? profile sourceProgram.contract
        functionNames layout canBreak canContinue canLeave stmt = true →
    (∀ name, name ∈ Stmt.names stmt → name ∈ before.used) →
    Stmt.toFunctionsListUncheckedFuel? compilerFuel before stmt =
      some (lower, after) →
    ScopedStateRel layout source target →
    TargetDomainWithin before.used target.vars →
    (∀ name, name ∈ layout → name ∈ before.used) →
    ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx →
    FunctionsInteractionStaticCost.programBudget
        sourceProgram sourceFuel +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel →
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used
        (SolcValidation.StmtOutVars layout stmt) sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec sourceFuel stmt
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target)

/-- Source-fuel prefix of the statement capability used in the mutual
whole-program induction. -/
def RecursiveStmtForward
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel targetFuel : Nat}, sourceFuel < bound →
    StmtForwardAt profile sourceProgram targetProgram sourceFuel targetFuel

/-- One compiler-selected statement list at fixed source and target fuels. -/
def ListForwardAt
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (sourceFuel targetFuel : Nat) : Prop :=
  ∀ {compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {stmts : List AstStmt}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx},
    SolcValidation.StmtsOk? profile sourceProgram.contract
        functionNames layout canBreak canContinue canLeave stmts = true →
    (∀ name, name ∈ Stmt.List.names stmts → name ∈ before.used) →
    Stmt.List.toFunctionsUncheckedFuel? compilerFuel before stmts =
      some (lower, after) →
    ScopedStateRel layout source target →
    TargetDomainWithin before.used target.vars →
    (∀ name, name ∈ layout → name ∈ before.used) →
    ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx →
    FunctionsInteractionStaticCost.programBudget
        sourceProgram sourceFuel +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel →
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used
        (SolcValidation.StmtsOutVars layout stmts) sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.execSeq sourceFuel stmts
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target)

def RecursiveListForward
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel targetFuel : Nat}, sourceFuel < bound →
    ListForwardAt profile sourceProgram targetProgram sourceFuel targetFuel

private theorem stmtOutVarsWithin
    {before after : Fresh.State} {layout : List Functions.Name}
    {stmt : AstStmt}
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hNames : ∀ name, name ∈ Stmt.names stmt → name ∈ before.used)
    (hExtends : Fresh.Extends before after) :
    ∀ name, name ∈ SolcValidation.StmtOutVars layout stmt →
      name ∈ after.used := by
  intro name hName
  cases stmt with
  | Let vars value? =>
      rcases List.mem_append.mp hName with hDeclared | hOuter
      · apply hExtends name
        apply hNames name
        cases value? <;> simp [Stmt.names, hDeclared]
      · exact hExtends name (hLayout name hOuter)
  | Block body => exact hExtends name (hLayout name hName)
  | Assign vars value => exact hExtends name (hLayout name hName)
  | ExprStmtCall value => exact hExtends name (hLayout name hName)
  | Switch value cases defaultBody =>
      exact hExtends name (hLayout name hName)
  | For value post body => exact hExtends name (hLayout name hName)
  | If value body => exact hExtends name (hLayout name hName)
  | Continue => exact hExtends name (hLayout name hName)
  | Break => exact hExtends name (hLayout name hName)
  | Leave => exact hExtends name (hLayout name hName)

private theorem layoutWithinStmtOutVars
    (layout : List Functions.Name) (stmt : AstStmt) :
    ∀ name, name ∈ layout →
      name ∈ SolcValidation.StmtOutVars layout stmt := by
  intro name hName
  cases stmt <;> simp [SolcValidation.StmtOutVars, hName]

private theorem layoutWithinStmtsOutVars
    (layout : List Functions.Name) (stmts : List AstStmt) :
    ∀ name, name ∈ layout →
      name ∈ SolcValidation.StmtsOutVars layout stmts := by
  induction stmts generalizing layout with
  | nil => exact fun _name hName => hName
  | cons head tail ih =>
      intro name hName
      apply ih (SolcValidation.StmtOutVars layout head)
      exact layoutWithinStmtOutVars layout head name hName

namespace CompoundForward

/-- Compose a checked prepared condition with the adjacent lexical-body
theorem. The target equation is the ordinary compiler output factored by
`PreparedCondition.run_if`; no condition evaluator is reproduced here. -/
theorem ifFromCondition
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {conditionFuel targetFuel : Nat}
    {layout used : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {cond : AstExpr} {body : List AstStmt}
    {pre : List Functions.Stmt} {lowerCond : Locals.Expr 1}
    {lowerBody : Functions.Block}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hTargetFuel : pre.length + 1 < targetFuel)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hCondition :
      Simulation.Interaction.ForwardRel Truncated
        (FunctionsInteractionPreparedCondition.DoneRel layout used ctx)
        (Yul.InteractionSemantics.evalValues conditionFuel cond
          (some sourceProgram.contract) source)
        (FunctionsInteractionPreparedCondition.run targetProgram.toFunctions
          ctx targetFuel pre lowerCond target))
    (hBody :
      ∀ {sourceAfter : Yul.InteractionSemantics.State}
        {targetAfter : Functions.InteractionSemantics.State}
        {ctxAfter : Functions.Source.Ctx},
        ScopedStateRel layout sourceAfter targetAfter →
        TargetDomainWithin used targetAfter.vars →
        ControlContextRel sourceScopes layout
            canBreak canContinue canLeave ctxAfter →
        Simulation.Interaction.ForwardRel Truncated
          (ControlDoneRel used layout sourceScopes
            canBreak canContinue canLeave)
          (Yul.InteractionSemantics.exec conditionFuel (.Block body)
            (some sourceProgram.contract) sourceAfter)
          (Functions.InteractionSemantics.Stmt.openRun
            targetProgram.toFunctions ctxAfter
            (targetFuel - pre.length - 2) (.block lowerBody) targetAfter)) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (conditionFuel + 1) (.If cond body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel
        { stmts := pre ++ [.if_ lowerCond lowerBody] } target) := by
  rw [Yul.InteractionSemantics.Exec.if_succ]
  rw [Yul.InteractionSemantics.eval_eq_bind,
    Simulation.Interaction.bind_assoc]
  rw [FunctionsInteractionPreparedCondition.run_if
    targetProgram.toFunctions ctx targetFuel pre lowerCond lowerBody target
    hTargetFuel]
  apply Simulation.Interaction.ForwardRel.bind_custom hCondition
  intro sourceDone targetDone hDone
  cases hDone with
  | error hError =>
      exact Simulation.Interaction.ForwardRel.done (.error hError)
  | terminal hTerminal =>
      cases hTerminal with
      | stop hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.stop hState))
      | return_ hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.return_ hState))
      | selfdestruct hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.selfdestruct hState))
      | revert hState =>
          exact Simulation.Interaction.ForwardRel.done
            (.terminal (.revert hState))
  | @regular sourceAfter values targetAfter truth ctxAfter value
      hValues hTruth hScoped hDomain hScope hSameControl =>
      have hControlAfter : ControlContextRel sourceScopes layout
          canBreak canContinue canLeave ctxAfter := by
        apply ControlContextRel.transport hControl
        · exact fun _name hName => hName
        · exact hSameControl
        · intro name hName
          exact hScope name (hControl.scope name hName)
      subst values
      simp only [List.head!_cons, Simulation.Interaction.bind_done_ok]
      by_cases hNonzero : value ≠ EvmYul.UInt256.ofNat 0
      · have hTruthTrue : truth = true := by
          exact
            FunctionsInteractionPreparedCondition.DoneRel.truth_eq_true_of_ne
              hTruth hNonzero
        have hBne :
            (value != EvmYul.UInt256.ofNat 0) = true :=
          hTruth.symm.trans hTruthTrue
        subst truth
        simp only [Simulation.Interaction.bind_done_ok, pure_bind,
          hNonzero, hBne, ↓reduceIte]
        rw [show
          (pure (sourceAfter, value) :
              Yul.InteractionSemantics.Open
                (Yul.InteractionSemantics.State × Word)) =
            Simulation.Interaction.pure (sourceAfter, value) by rfl]
        unfold Simulation.Interaction.pure
        rw [Simulation.Interaction.bind_done_ok]
        rw [if_pos hNonzero]
        change
          Simulation.Interaction.ForwardRel Truncated
            (ControlDoneRel used layout sourceScopes
              canBreak canContinue canLeave)
            (Yul.InteractionSemantics.exec conditionFuel (.Block body)
              (some sourceProgram.contract) sourceAfter)
            (Functions.InteractionSemantics.Stmt.openRun
              targetProgram.toFunctions ctxAfter
              (targetFuel - pre.length - 2) (.block lowerBody) targetAfter)
        exact hBody hScoped hDomain hControlAfter
      · have hZero : value = EvmYul.UInt256.ofNat 0 := by
          simpa using hNonzero
        subst value
        have hTruthFalse : truth = false := by
          simpa using hTruth
        subst truth
        simp only [ne_eq, not_true_eq_false, ↓reduceIte,
          Bool.false_eq_true, Simulation.Interaction.bind_done_ok]
        exact Simulation.Interaction.ForwardRel.done
          (.regular hScoped hDomain hControlAfter)

/-- Compiler-selected lexical block from the adjacent recursive list theorem.
The outer source/target cleanup is owned by `ControlDoneRel.block`; this wrapper
only decomposes the ordinary Yul compiler and discharges private target fuel. -/
theorem block
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {fuel targetFuel compilerFuel : Nat}
    {functionNames layout : List Functions.Name}
    {sourceScopes : SourceScopes}
    {canBreak canContinue canLeave : Bool}
    {before after : Fresh.State} {body : List AstStmt}
    {lower : List Functions.Stmt}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    {ctx : Functions.Source.Ctx}
    (hLists : ∀ recursiveTargetFuel,
      ListForwardAt profile sourceProgram targetProgram
        fuel recursiveTargetFuel)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave (.Block body) = true)
    (hNames : ∀ name, name ∈ Stmt.names (.Block body) →
      name ∈ before.used)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.Block body) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget
          sourceProgram (fuel + 1) +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Yul.InteractionSemantics.exec (fuel + 1) (.Block body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions ctx targetFuel { stmts := lower } target) := by
  obtain ⟨previous, lowerBody, rfl, hLowerBody, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_block_parts hLower
  obtain ⟨bodyCompilerFuel, lowerBodyStmts, rfl,
      hLowerList, rfl⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLowerBody
  have hBodyOk : SolcValidation.StmtsOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave body = true := by
    simpa [SolcValidation.StmtOk?] using hOk
  have hBodyNames : ∀ name, name ∈ Stmt.List.names body →
      name ∈ before.used := by
    simpa [Stmt.names] using hNames
  have hProgramMono :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel ≤
        FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) := by
    unfold FunctionsInteractionStaticCost.programBudget
    exact FunctionsInteractionFuel.executionBudgetFor_mono _ _ (by omega)
  have hTargetPositive : 2 ≤ targetFuel := by
    simp [FunctionsInteractionTargetCost.list,
      FunctionsInteractionTargetCost.stmt,
      FunctionsInteractionTargetCost.block] at hTargetFuel
    omega
  have hBodyFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
          FunctionsInteractionTargetCost.list lowerBodyStmts + 1 <
        targetFuel - 1 := by
    simp [FunctionsInteractionTargetCost.list,
      FunctionsInteractionTargetCost.stmt,
      FunctionsInteractionTargetCost.block] at hTargetFuel
    omega
  have hBody := hLists (targetFuel - 1)
    hBodyOk hBodyNames hLowerList hRel hDomain hLayout hControl hBodyFuel
  have hBlock := FunctionsInteractionStatement.ControlDoneRel.block
    hRel hControl (layoutWithinStmtsOutVars layout body) hBody
  have hStmtFuelEq : targetFuel - 2 + 1 = targetFuel - 1 := by omega
  have hBlock' :
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel after.used layout sourceScopes
          canBreak canContinue canLeave)
        (Yul.InteractionSemantics.exec (fuel + 1) (.Block body)
          (some sourceProgram.contract) source)
        (Functions.InteractionSemantics.Stmt.openRun
          targetProgram.toFunctions ctx (targetFuel - 2 + 1)
          (.block { stmts := lowerBodyStmts }) target) := by
    rw [hStmtFuelEq]
    exact hBlock
  have hFuelEq : targetFuel - 2 + 2 = targetFuel := by omega
  have hSingleton :=
    FunctionsInteractionStatement.ControlDoneRel.singleton
      (targetFuel := targetFuel - 2) hBlock'
  simpa [hFuelEq, SolcValidation.StmtOutVars] using hSingleton

end CompoundForward

namespace RecursiveListForward

/-- Generic exact-tail sequencing.  This is the list edge of the historical
five-way recursion graph, rebuilt over the canonical open-interaction result
instead of observer replay state. -/
theorem ofStmt
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {bound : Nat}
    (hStmt : RecursiveStmtForward
      profile sourceProgram targetProgram bound) :
    RecursiveListForward profile sourceProgram targetProgram (bound + 1) := by
  intro sourceFuel
  induction sourceFuel with
  | zero =>
      intro targetFuel hFuel
      intro compilerFuel functionNames layout sourceScopes
        canBreak canContinue canLeave before after stmts lower source target ctx
        hOk hNames hLower hRel hDomain hLayout hControl hTargetFuel
      rw [Yul.InteractionSemantics.ExecSeq.zero]
      exact Simulation.Interaction.ForwardRel.truncated
        (right := Functions.InteractionSemantics.Block.openRun
          targetProgram.toFunctions ctx targetFuel { stmts := lower } target)
        (by trivial)
  | succ fuel ih =>
      intro targetFuel hFuel
      intro compilerFuel functionNames layout sourceScopes
        canBreak canContinue canLeave before after stmts lower source target ctx
        hOk hNames hLower hRel hDomain hLayout hControl hTargetFuel
      cases stmts with
      | nil =>
          obtain ⟨previous, rfl, rfl, rfl⟩ :=
            Stmt.List.toFunctionsUncheckedFuel?_nil_parts hLower
          have hPositive : 0 < targetFuel := by
            simp only [FunctionsInteractionTargetCost.list] at hTargetFuel
            omega
          have hTargetEq : targetFuel = (targetFuel - 1) + 1 := by omega
          rw [hTargetEq]
          simpa using
            (FunctionsInteractionStatement.ControlDoneRel.nil
              (sourceFuel := fuel) (targetFuel := targetFuel - 1)
              hRel hDomain hControl)
      | cons head tail =>
          obtain ⟨previous, lowerHead, middle, lowerTail,
              rfl, hLowerHead, hLowerTail, rfl⟩ :=
            Stmt.List.toFunctionsUncheckedFuel?_cons_parts hLower
          obtain ⟨hHeadOk, hTailOk⟩ :=
            SolcValidation.stmtsOk_cons_parts hOk
          have hNameParts :
              (∀ name, name ∈ Stmt.names head → name ∈ before.used) ∧
              (∀ name, name ∈ Stmt.List.names tail →
                name ∈ before.used) := by
            constructor <;> intro name hName
            · exact hNames name (by simp [Stmt.List.names, hName])
            · exact hNames name (by simp [Stmt.List.names, hName])
          have hMiddleExtends : Fresh.Extends before middle :=
            Stmt.toFunctionsListUncheckedFuel?_stateExtends hLowerHead
          have hTailNames : ∀ name, name ∈ Stmt.List.names tail →
              name ∈ middle.used := by
            intro name hName
            exact hMiddleExtends name (hNameParts.2 name hName)
          have hMiddleLayout : ∀ name,
              name ∈ SolcValidation.StmtOutVars layout head →
                name ∈ middle.used :=
            stmtOutVarsWithin hLayout hNameParts.1 hMiddleExtends
          have hProgramMono :
              FunctionsInteractionStaticCost.programBudget
                  sourceProgram fuel ≤
                FunctionsInteractionStaticCost.programBudget
                  sourceProgram (fuel + 1) := by
            unfold FunctionsInteractionStaticCost.programBudget
            exact FunctionsInteractionFuel.executionBudgetFor_mono
              _ _ (by omega)
          have hHeadFuel :
              FunctionsInteractionStaticCost.programBudget
                  sourceProgram fuel +
                    FunctionsInteractionTargetCost.list lowerHead + 1 <
                targetFuel := by
            rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
            omega
          have hTailFuel :
              FunctionsInteractionStaticCost.programBudget
                  sourceProgram fuel +
                    FunctionsInteractionTargetCost.list lowerTail + 1 <
                targetFuel - lowerHead.length := by
            rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
            have hLength :=
              FunctionsInteractionTargetCost.length_le_list lowerHead
            omega
          have hHead := hStmt (sourceFuel := fuel)
            (targetFuel := targetFuel) (by omega)
            hHeadOk hNameParts.1 hLowerHead hRel hDomain hLayout
            hControl hHeadFuel
          apply FunctionsInteractionStatement.ControlDoneRel.cons hHead
          intro sourceMid targetMid ctxMid hMidRel hMidDomain hMidControl
          exact ih (targetFuel := targetFuel - lowerHead.length) (by omega)
            hTailOk hTailNames hLowerTail hMidRel hMidDomain hMiddleLayout
            hMidControl hTailFuel

end RecursiveListForward

end FunctionsInteractionRecursiveStatement
end Yul
end EvmCompiler
