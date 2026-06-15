import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCompiler

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

theorem Decomposition.findFunction
    {program : Program} {targetProgram : Objects.Program}
    (hDecomposition : Decomposition program targetProgram)
    {name : Name} {fn : AstFunctionDefinition}
    (hLookup : program.contract.functions.lookup name = some fn) :
    ∃ before after lowerFn,
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
  obtain ⟨before, after, lowerFn, hFind, hLowerFn⟩ :=
    hLowering.find_of_mem
      (Contract.functionEntries_names_nodup program.contract)
      (Contract.functionEntries_mem_of_lookup hLookup)
  refine ⟨before, after, lowerFn, ?_, hLowerFn⟩
  rw [hTarget]
  exact hFind

end FunctionsObserverCompiler
end Yul
end EvmCompiler
