import EvmCompiler.Yul.FunctionsInteractionSelectedStatementCall

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
        sourceProgram sourceFuel + lower.length + 1 < targetFuel →
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
        sourceProgram sourceFuel + lower.length + 1 < targetFuel →
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
            simp only [List.length_nil] at hTargetFuel
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
                    sourceProgram fuel + lowerHead.length + 1 <
                targetFuel := by
            simp only [List.length_append] at hTargetFuel
            omega
          have hTailFuel :
              FunctionsInteractionStaticCost.programBudget
                    sourceProgram fuel + lowerTail.length + 1 <
                targetFuel - lowerHead.length := by
            simp only [List.length_append] at hTargetFuel
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
