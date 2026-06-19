import EvmCompiler.Yul.FunctionsInteractionRecursiveStatement

namespace EvmCompiler
namespace Yul
namespace FunctionsInteractionRecursiveBody

open FunctionsInteractionPrimitive
open FunctionsInteractionRelation
open FunctionsInteractionControlRelation
open FunctionsInteractionRecursiveStatement

/-- Package one exact recursively preserved source body list as the selected
Functions function body. Target-fuel accounting remains an explicit private
premise here and is discharged by the source-owned compiler expansion bound. -/
theorem ofListAt
    {profile : SolcValidation.DialectProfile}
    {sourceProgram : Yul.Program} {targetProgram : Objects.Program}
    {listFuel targetFuel : Nat}
    {body : List AstStmt} {before after : Fresh.State}
    {fn : Functions.FunDef}
    {source : Yul.InteractionSemantics.State}
    {target : Functions.InteractionSemantics.State}
    (hList : ListForwardAt profile sourceProgram targetProgram
      listFuel targetFuel)
    (hLower : Stmt.List.toBlockUncheckedFuel?
      (FunctionList.fuel (Contract.functionEntries sourceProgram.contract))
      before body = some (fn.body, after))
    (hBodyOk : SolcValidation.StmtsOk? profile sourceProgram.contract
      ((Contract.functionEntries sourceProgram.contract).map Prod.fst)
      (fn.returns ++ fn.params) false false true body = true)
    (hReserved : ∀ name, name ∈ fn.returns ++ fn.params →
      name ∈ before.used)
    (hBodyNames : ∀ name, name ∈ Stmt.List.names body →
      name ∈ before.used)
    (hRel : ScopedStateRel (fn.returns ++ fn.params) source target)
    (hDomain : TargetDomainWithin before.used target.vars)
    (hTargetFuel :
      FunctionsInteractionStaticCost.programBudget sourceProgram listFuel +
          FunctionsInteractionTargetCost.list fn.body.stmts + 1 < targetFuel) :
    Simulation.Interaction.ForwardRel Truncated
      (FunctionsInteractionCall.FunctionBodyDoneRel
        (fn.returns ++ fn.params))
      (Yul.InteractionSemantics.exec (listFuel + 1) (.Block body)
        (some sourceProgram.contract) source)
      (Functions.InteractionSemantics.Block.openRun
        targetProgram.toFunctions
        (Functions.Source.Effectful.FunDef.bodyCtx fn)
        targetFuel fn.body target) := by
  obtain ⟨compilerFuel, lower, _hCompilerFuel, hLowerList, hFnBody⟩ :=
    Stmt.List.toBlockUncheckedFuel?_parts hLower
  obtain ⟨sourceScope, hScopeStore, hScopeUsed, hScopeLayout, hControl⟩ :=
    ControlContextRel.functionBody (fn := fn) rfl hRel hReserved
  have hTargetScope : TargetScopeWithin before.used
      (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    intro name hName
    exact hReserved name (by
      simpa [Functions.Source.Effectful.FunDef.bodyCtx,
        Functions.Source.Ctx.initial,
        Functions.Source.Ctx.withLeaveScope] using hName)
  have hBodyRel := hList hBodyOk hBodyNames hLowerList hRel hDomain
    hTargetScope hReserved hControl (by simpa [hFnBody] using hTargetFuel)
  apply FunctionsInteractionCall.functionBodyOfList
    (layout := fn.returns ++ fn.params)
    (bodyLayout := SolcValidation.StmtsOutVars
      (fn.returns ++ fn.params) body)
    (sourceScope := sourceScope) rfl hRel
  · simpa [hScopeStore]
  · exact hScopeLayout
  · exact FunctionsInteractionRecursiveStatement.layoutWithinStmtsOutVars
      (fn.returns ++ fn.params) body
  · simpa [hFnBody, hScopeUsed] using hBodyRel

end FunctionsInteractionRecursiveBody
end Yul
end EvmCompiler
