import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul
namespace FunctionsCompilerArtifact

/-!
Compiler decomposition owned by the adjacent Yul-to-Functions boundary.

This module does not define an observer-specific compiler.  It only exposes
the body and function lowering equations already executed by
`Program.toObjectsWithObservers?`.
-/

def Decomposition (program : Program)
    (targetProgram : Objects.Program) : Prop :=
  ∃ bodyStmts : List Functions.Stmt,
  ∃ afterBody : Fresh.State,
  ∃ functions : List Functions.FunDef,
  ∃ afterFunctions : Fresh.State,
    Stmt.toFunctionsListUncheckedFuel?
          (Stmt.fuel program.contract.dispatcher)
          (Fresh.initial (Contract.names program.contract))
          program.contract.dispatcher =
        some (bodyStmts, afterBody) ∧
      FunctionList.toFunDefsUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries program.contract))
          afterBody (Contract.functionEntries program.contract) =
        some (functions, afterFunctions) ∧
      targetProgram.toFunctions =
        { functions := functions
          body := { stmts := bodyStmts }
          memoryContract := program.memoryContract }

theorem decomposition_of_toObjectsWithObservers?
    {program : Program} {lower : Objects.Program}
    (hLower :
      Program.toObjectsWithObservers? program = some lower) :
    Decomposition program lower := by
  unfold Program.toObjectsWithObservers? at hLower
  cases hContract :
      Contract.toObjectsWithObservers? program.contract with
  | none =>
      simp [hContract] at hLower
  | some contractLower =>
      have hLowerEq :
          lower =
            contractLower.withMemoryContract program.memoryContract := by
        simpa [hContract] using hLower.symm
      unfold Contract.toObjectsWithObservers? at hContract
      cases hBody :
          Stmt.toFunctionsListUncheckedFuel?
            (Stmt.fuel program.contract.dispatcher)
            (Fresh.initial (Contract.names program.contract))
            program.contract.dispatcher with
      | none =>
          simp [hBody] at hContract
      | some bodyResult =>
          rcases bodyResult with ⟨bodyStmts, afterBody⟩
          cases hFunctions :
              FunctionList.toFunDefsUncheckedFuel?
                (FunctionList.fuel
                  (Contract.functionEntries program.contract))
                afterBody (Contract.functionEntries program.contract) with
          | none =>
              simp [hBody, hFunctions] at hContract
          | some functionResult =>
              rcases functionResult with ⟨functions, afterFunctions⟩
              have hContractEq :
                  contractLower =
                    { root :=
                        .mk "root"
                          { functions := functions
                            body := { stmts := bodyStmts } }
                          [] [] } := by
                simpa [hBody, hFunctions] using hContract.symm
              refine
                ⟨bodyStmts, afterBody, functions, afterFunctions,
                  hBody, hFunctions, ?_⟩
              subst lower
              subst contractLower
              rfl

theorem memoryContract_of_toObjectsWithObservers?
    {program : Program} {lower : Objects.Program}
    (hLower :
      Program.toObjectsWithObservers? program = some lower) :
    lower.toFunctions.memoryContract = program.memoryContract := by
  rcases decomposition_of_toObjectsWithObservers? hLower with
    ⟨bodyStmts, afterBody, functions, afterFunctions,
      hBody, hFunctions, hProgram⟩
  exact congrArg Functions.Program.memoryContract hProgram

theorem Decomposition.findFunction
    {program : Program} {targetProgram : Objects.Program}
    (hDecomposition : Decomposition program targetProgram)
    {name : Name} {fn : AstFunctionDefinition}
    (hLookup : program.contract.functions.lookup name = some fn) :
    ∃ before after lowerFn,
      Fresh.Extends
          (Fresh.initial (Contract.names program.contract)) before ∧
      Functions.Source.FunList.find? name
          targetProgram.toFunctions.functions =
        some lowerFn ∧
      FunctionDefinition.toFunDefUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries program.contract))
          before name fn =
        some (lowerFn, after) := by
  rcases hDecomposition with
    ⟨bodyStmts, afterBody, functions, afterFunctions,
      hBody, hFunctions, hTarget⟩
  have hLowering :
      FunctionList.UncheckedLowering
        (FunctionList.fuel
          (Contract.functionEntries program.contract))
        afterBody (Contract.functionEntries program.contract)
        functions afterFunctions :=
    FunctionList.uncheckedLowering_of_toFunDefsUncheckedFuel?
      hFunctions
  obtain ⟨before, after, lowerFn, hFunctionsPrefix, hFind, hLowerFn⟩ :=
    hLowering.find_of_mem_stateExtends
      (Contract.functionEntries_names_nodup program.contract)
      (Contract.functionEntries_mem_of_lookup hLookup)
  have hBodyPrefix :
      Fresh.Extends
        (Fresh.initial (Contract.names program.contract)) afterBody :=
    Stmt.toFunctionsListUncheckedFuel?_stateExtends hBody
  refine
    ⟨before, after, lowerFn,
      Fresh.Extends.trans hBodyPrefix hFunctionsPrefix, ?_, hLowerFn⟩
  rw [hTarget]
  exact hFind

theorem Decomposition.findFunction_parts
    {program : Program} {targetProgram : Objects.Program}
    (hDecomposition : Decomposition program targetProgram)
    {name : Name} {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hLookup :
      program.contract.functions.lookup name =
        some (.Def params returns body)) :
    ∃ before after lowerFn,
      Fresh.Extends
          (Fresh.initial (Contract.names program.contract)) before ∧
      Functions.Source.FunList.find? name
          targetProgram.toFunctions.functions =
        some lowerFn ∧
      lowerFn.name = name ∧
      lowerFn.params = identNames params ∧
      lowerFn.returns = identNames returns ∧
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel
            (Contract.functionEntries program.contract))
          before body =
        some (lowerFn.body, after) ∧
      ∀ candidate,
        candidate ∈ lowerFn.returns ++ lowerFn.params →
          candidate ∈ before.used := by
  obtain ⟨before, after, lowerFn, hPrefix, hFind, hLower⟩ :=
    hDecomposition.findFunction hLookup
  obtain ⟨hName, hParams, hReturns, hBody⟩ :=
    FunctionDefinition.toFunDefUncheckedFuel?_parts hLower
  refine
    ⟨before, after, lowerFn, hPrefix, hFind, hName, hParams, hReturns,
      hBody, ?_⟩
  intro candidate hCandidate
  rw [hReturns, hParams] at hCandidate
  apply hPrefix candidate
  change candidate ∈ Contract.names program.contract
  rcases List.mem_append.mp hCandidate with hReturn | hParam
  · exact
      Contract.function_return_mem_names_of_lookup hLookup hReturn
  · exact
      Contract.function_param_mem_names_of_lookup hLookup hParam

end FunctionsCompilerArtifact
end Yul
end EvmCompiler
