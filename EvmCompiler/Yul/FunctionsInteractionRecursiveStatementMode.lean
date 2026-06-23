import EvmCompiler.Yul.FunctionsInteractionPreparedStatementMode
import EvmCompiler.Yul.FunctionsInteractionPreparedPrimitiveMode
import EvmCompiler.Yul.FunctionsInteractionTargetCost

/-!
Mode-parametric recursive Yul-to-Functions statement interface. The compiler,
validation, fuel accounting, state relation, and control relation are shared;
`Mode` selects only the canonical primitive handlers.
-/

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRecursiveStatementMode

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation
open FunctionsInteractionMode

def StmtForwardAt (mode : Mode)
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
    TargetScopeWithin before.used ctx →
    (∀ name, name ∈ layout → name ∈ before.used) →
    ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx →
    FunctionsInteractionStaticCost.programBudget sourceProgram sourceFuel +
        FunctionsInteractionTargetCost.list lower + 1 < targetFuel →
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used
        (SolcValidation.StmtOutVars layout stmt) sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode sourceFuel stmt
        (some sourceProgram.contract) source)
      (Target.Block.openRun mode targetProgram.toFunctions ctx targetFuel
        { stmts := lower } target)

def RecursiveStmtForward (mode : Mode)
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel targetFuel : Nat}, sourceFuel < bound →
    StmtForwardAt mode profile sourceProgram targetProgram sourceFuel targetFuel

def ListForwardAt (mode : Mode)
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
    TargetScopeWithin before.used ctx →
    (∀ name, name ∈ layout → name ∈ before.used) →
    ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx →
    FunctionsInteractionStaticCost.programBudget sourceProgram sourceFuel +
        FunctionsInteractionTargetCost.list lower + 1 < targetFuel →
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used
        (SolcValidation.StmtsOutVars layout stmts) sourceScopes
        canBreak canContinue canLeave)
      (Source.execSeq mode sourceFuel stmts
        (some sourceProgram.contract) source)
      (Target.Block.openRun mode targetProgram.toFunctions ctx targetFuel
        { stmts := lower } target)

def RecursiveListForward (mode : Mode)
    (profile : SolcValidation.DialectProfile)
    (sourceProgram : Yul.Program) (targetProgram : Objects.Program)
    (bound : Nat) : Prop :=
  ∀ {sourceFuel targetFuel : Nat}, sourceFuel < bound →
    ListForwardAt mode profile sourceProgram targetProgram sourceFuel targetFuel

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

theorem layoutWithinStmtsOutVars
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

theorem block
    {mode : Mode} {profile : SolcValidation.DialectProfile}
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
      ListForwardAt mode profile sourceProgram targetProgram
        fuel recursiveTargetFuel)
    (hOk : SolcValidation.StmtOk? profile sourceProgram.contract
      functionNames layout canBreak canContinue canLeave (.Block body) = true)
    (hNames : ∀ name, name ∈ Stmt.names (.Block body) →
      name ∈ before.used)
    (hLower : Stmt.toFunctionsListUncheckedFuel? compilerFuel before
      (.Block body) = some (lower, after))
    (hRel : ScopedStateRel layout source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetScope : TargetScopeWithin before.used ctx)
    (hLayout : ∀ name, name ∈ layout → name ∈ before.used)
    (hControl : ControlContextRel sourceScopes layout
      canBreak canContinue canLeave ctx)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram (fuel + 1) +
          FunctionsInteractionTargetCost.list lower + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (ControlDoneRel after.used layout sourceScopes
        canBreak canContinue canLeave)
      (Source.exec mode (fuel + 1) (.Block body)
        (some sourceProgram.contract) source)
      (Target.Block.openRun mode targetProgram.toFunctions ctx targetFuel
        { stmts := lower } target) := by
  obtain ⟨previous, lowerBody, rfl, hLowerBody, rfl⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_block_parts hLower
  obtain ⟨bodyCompilerFuel, lowerBodyStmts, rfl, hLowerList, rfl⟩ :=
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
    hBodyOk hBodyNames hLowerList hRel hDomain hTargetScope hLayout hControl
    hBodyFuel
  have hBodyExtends : Fresh.Extends before after :=
    Stmt.List.toFunctionsUncheckedFuel?_stateExtends hLowerList
  have hBlock := FunctionsInteractionStatementMode.block
    hRel hControl (hTargetScope.mono hBodyExtends)
    (layoutWithinStmtsOutVars layout body) hBody
  have hStmtFuelEq : targetFuel - 2 + 1 = targetFuel - 1 := by omega
  have hBlock' :
      Simulation.Interaction.ForwardRel Truncated
        (ControlDoneRel after.used layout sourceScopes
          canBreak canContinue canLeave)
        (Source.exec mode (fuel + 1) (.Block body)
          (some sourceProgram.contract) source)
        (Target.Stmt.openRun mode targetProgram.toFunctions ctx
          (targetFuel - 2 + 1) (.block { stmts := lowerBodyStmts }) target) := by
    rw [hStmtFuelEq]
    exact hBlock
  have hFuelEq : targetFuel - 2 + 2 = targetFuel := by omega
  have hSingleton :=
    FunctionsInteractionStatementMode.ControlDoneRel.singleton
      mode (targetFuel := targetFuel - 2) hBlock'
  simpa [hFuelEq, SolcValidation.StmtOutVars] using hSingleton

end CompoundForward

namespace RecursiveListForward

theorem ofStmt
    {mode : Mode} {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {bound : Nat}
    (hStmt : RecursiveStmtForward mode
      profile sourceProgram targetProgram bound) :
    RecursiveListForward mode profile sourceProgram targetProgram
      (bound + 1) := by
  intro sourceFuel
  induction sourceFuel with
  | zero =>
      intro targetFuel hFuel
      intro compilerFuel functionNames layout sourceScopes
        canBreak canContinue canLeave before after stmts lower source target ctx
        hOk hNames hLower hRel hDomain hTargetScope hLayout hControl hTargetFuel
      rw [Source.execSeq_zero]
      exact Simulation.Interaction.ForwardRel.truncated
        (right := Target.Block.openRun mode targetProgram.toFunctions ctx
          targetFuel { stmts := lower } target) (by trivial)
  | succ fuel ih =>
      intro targetFuel hFuel
      intro compilerFuel functionNames layout sourceScopes
        canBreak canContinue canLeave before after stmts lower source target ctx
        hOk hNames hLower hRel hDomain hTargetScope hLayout hControl hTargetFuel
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
            (FunctionsInteractionStatementMode.ControlDoneRel.nil mode
              (sourceFuel := fuel) (targetFuel := targetFuel - 1)
              hRel hDomain hControl hTargetScope)
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
              FunctionsInteractionStaticCost.programBudget sourceProgram fuel ≤
                FunctionsInteractionStaticCost.programBudget
                  sourceProgram (fuel + 1) := by
            unfold FunctionsInteractionStaticCost.programBudget
            exact FunctionsInteractionFuel.executionBudgetFor_mono
              _ _ (by omega)
          have hHeadFuel :
              FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
                    FunctionsInteractionTargetCost.list lowerHead + 1 <
                targetFuel := by
            rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
            omega
          have hTailFuel :
              FunctionsInteractionStaticCost.programBudget sourceProgram fuel +
                    FunctionsInteractionTargetCost.list lowerTail + 1 <
                targetFuel - lowerHead.length := by
            rw [FunctionsInteractionTargetCost.list_append] at hTargetFuel
            have hLength :=
              FunctionsInteractionTargetCost.length_le_list lowerHead
            omega
          have hHead := hStmt (sourceFuel := fuel)
            (targetFuel := targetFuel) (by omega)
            hHeadOk hNameParts.1 hLowerHead hRel hDomain hTargetScope hLayout
            hControl hHeadFuel
          apply FunctionsInteractionStatementMode.ControlDoneRel.cons mode hHead
          intro sourceMid targetMid ctxMid hMidRel hMidDomain hMidControl
            hMidTargetScope
          exact ih (targetFuel := targetFuel - lowerHead.length) (by omega)
            hTailOk hTailNames hLowerTail hMidRel hMidDomain hMidTargetScope
            hMiddleLayout hMidControl hTailFuel

end RecursiveListForward

end FunctionsInteractionRecursiveStatementMode
end Yul
end EvmCompiler
