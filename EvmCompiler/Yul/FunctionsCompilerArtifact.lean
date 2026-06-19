import EvmCompiler.Yul.Compiler

namespace EvmCompiler
namespace Yul

namespace FunctionList

private theorem lookup_foldl_insert_of_not_mem
    (entries : List (Name × AstFunctionDefinition))
    (state : Finmap (fun (_ : Name) => AstFunctionDefinition))
    (name : Name)
    (hNotMem : name ∉ entries.map Prod.fst) :
    (entries.foldl
        (fun acc entry => acc.insert entry.fst entry.snd) state).lookup name =
      state.lookup name := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨headName, headFn⟩
      simp only [List.map_cons, List.mem_cons, not_or] at hNotMem
      rw [List.foldl_cons, ih _ hNotMem.2]
      exact Finmap.lookup_insert_of_ne state hNotMem.1

private theorem lookup_foldl_insert_of_mem
    {entries : List (Name × AstFunctionDefinition)}
    (hNames : (entries.map Prod.fst).Nodup)
    {name : Name} {fn : AstFunctionDefinition}
    (hMem : (name, fn) ∈ entries)
    (state : Finmap (fun (_ : Name) => AstFunctionDefinition)) :
    (entries.foldl
        (fun acc entry => acc.insert entry.fst entry.snd) state).lookup name =
      some fn := by
  induction entries generalizing state with
  | nil => simp at hMem
  | cons entry rest ih =>
      rcases entry with ⟨headName, headFn⟩
      simp only [List.map_cons, List.nodup_cons] at hNames
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with hHere | hTail
      · rcases hHere with ⟨rfl, rfl⟩
        rw [List.foldl_cons,
          lookup_foldl_insert_of_not_mem rest _ name hNames.1]
        exact Finmap.lookup_insert _
      · rw [List.foldl_cons]
        exact ih hNames.2 hTail _

theorem lookup_functionMap_of_mem
    {entries : List (Name × AstFunctionDefinition)}
    (hNames : (entries.map Prod.fst).Nodup)
    {name : Name} {fn : AstFunctionDefinition}
    (hMem : (name, fn) ∈ entries) :
    (functionMap entries).lookup name = some fn := by
  exact lookup_foldl_insert_of_mem hNames hMem _

private theorem mem_foldl_insert
    (entries : List (Name × AstFunctionDefinition))
    (state : Finmap (fun (_ : Name) => AstFunctionDefinition))
    (name : Name)
    (hMem : name ∈ entries.foldl
      (fun acc entry => acc.insert entry.fst entry.snd) state) :
    name ∈ state ∨ name ∈ entries.map Prod.fst := by
  induction entries generalizing state with
  | nil => exact Or.inl hMem
  | cons entry rest ih =>
      rcases entry with ⟨headName, headFn⟩
      rw [List.foldl_cons] at hMem
      rcases ih (state.insert headName headFn) hMem with
        hInserted | hRest
      · rw [Finmap.mem_insert] at hInserted
        rcases hInserted with hHead | hState
        · exact Or.inr (by simp [hHead])
        · exact Or.inl hState
      · exact Or.inr (by simp [hRest])

theorem mem_of_lookup_functionMap
    {entries : List (Name × AstFunctionDefinition)}
    (hNames : (entries.map Prod.fst).Nodup)
    {name : Name} {fn : AstFunctionDefinition}
    (hLookup : (functionMap entries).lookup name = some fn) :
    (name, fn) ∈ entries := by
  have hKey : name ∈ (functionMap entries) :=
    Finmap.mem_of_lookup_eq_some hLookup
  have hNamesPresent : name ∈ entries.map Prod.fst := by
    rcases mem_foldl_insert entries ∅ name hKey with hEmpty | hEntries
    · exact (Finmap.notMem_empty hEmpty).elim
    · exact hEntries
  obtain ⟨entry, hEntry, hEntryName⟩ :=
    List.mem_map.mp hNamesPresent
  rcases entry with ⟨entryName, entryFn⟩
  simp only at hEntryName
  subst entryName
  have hEntryLookup := lookup_functionMap_of_mem hNames hEntry
  rw [hLookup] at hEntryLookup
  injection hEntryLookup with hFn
  subst entryFn
  exact hEntry

theorem names_mono
    {source target : List (Name × AstFunctionDefinition)}
    (hEntries : ∀ {name fn}, (name, fn) ∈ source →
      (name, fn) ∈ target) :
    ∀ {candidate}, candidate ∈ names source → candidate ∈ names target := by
  intro candidate hCandidate
  induction source with
  | nil => simp [names] at hCandidate
  | cons entry rest ih =>
      rcases entry with ⟨name, fn⟩
      have hHead : (name, fn) ∈ target :=
        hEntries (List.mem_cons_self)
      have hHeadNames := function_names_mem hHead
      change candidate ∈
        name :: (FunctionDefinition.names fn ++ names rest) at hCandidate
      rcases List.mem_cons.mp hCandidate with hName | hTail
      · subst candidate
        exact hHeadNames.1
      · rcases List.mem_append.mp hTail with hFn | hRest
        · exact hHeadNames.2 candidate hFn
        · apply ih
          intro entryName entryFn hMem
          exact hEntries (List.mem_cons_of_mem _ hMem)
          exact hRest

end FunctionList

namespace Contract

theorem lookup_of_functionEntries_mem
    {contract : AstContract} {name : Name}
    {fn : AstFunctionDefinition}
    (hMem : (name, fn) ∈ functionEntries contract) :
    contract.functions.lookup name = some fn := by
  unfold functionEntries at hMem
  obtain ⟨candidate, _hCandidate, hEmit⟩ :=
    List.mem_filterMap.mp hMem
  cases hLookup : contract.functions.lookup candidate with
  | none => simp [hLookup] at hEmit
  | some candidateFn =>
      simp [hLookup] at hEmit
      rcases hEmit with ⟨rfl, rfl⟩
      exact hLookup

end Contract

namespace FunctionsCompilerArtifact

/-!
Compiler decomposition owned by the adjacent Yul-to-Functions boundary.

This module exposes the body and function lowering equations already executed
by the canonical effect-complete `Program.toObjectsCanonical?` pass.
-/

def DecompositionFor (program : Program)
    (targetProgram : Objects.Program)
    (functionEntries : List (Name × AstFunctionDefinition))
    (initialNames : List Name) : Prop :=
  ∃ bodyStmts : List Functions.Stmt,
  ∃ afterBody : Fresh.State,
  ∃ functions : List Functions.FunDef,
  ∃ afterFunctions : Fresh.State,
    Stmt.toFunctionsListUncheckedFuel?
          (Stmt.fuel program.contract.dispatcher)
          (Fresh.initial initialNames)
          program.contract.dispatcher =
        some (bodyStmts, afterBody) ∧
      FunctionList.toFunDefsUncheckedFuel?
          (FunctionList.fuel functionEntries)
          afterBody functionEntries =
        some (functions, afterFunctions) ∧
      targetProgram.toFunctions =
        { functions := functions
          body := { stmts := bodyStmts }
          memoryContract := program.memoryContract }

/-- Compatibility view for the former map-enumerated compiler. -/
abbrev Decomposition (program : Program)
    (targetProgram : Objects.Program) : Prop :=
  DecompositionFor program targetProgram
    (Contract.functionEntries program.contract)
    (Contract.names program.contract)

/-- Executable source-order view of the same adjacent compiler artifact. -/
abbrev OrderedDecomposition (ordered : OrderedProgram)
    (targetProgram : Objects.Program) : Prop :=
  DecompositionFor ordered.program targetProgram
    ordered.functionEntries ordered.names

/-- Stable adjacent-pass interface shared by canonical and executable ordered
lowering. Source representation and reservation coverage are properties of the
source artifact, while the lowering equations remain owned by this pass. -/
structure PassDecomposition (program : Program)
    (targetProgram : Objects.Program) : Type where
  functionEntries : List (Name × AstFunctionDefinition)
  initialNames : List Name
  compiler :
    DecompositionFor program targetProgram functionEntries initialNames
  functionNamesNodup : (functionEntries.map Prod.fst).Nodup
  lookup_mem : ∀ {name fn},
    program.contract.functions.lookup name = some fn →
      (name, fn) ∈ functionEntries
  mem_lookup : ∀ {name fn}, (name, fn) ∈ functionEntries →
    program.contract.functions.lookup name = some fn
  sourceNamesReserved : ∀ candidate,
    candidate ∈ Contract.names program.contract →
      candidate ∈ initialNames

theorem decomposition_of_toObjectsCanonical?
    {program : Program} {lower : Objects.Program}
    (hLower :
      Program.toObjectsCanonical? program = some lower) :
    Decomposition program lower := by
  unfold Program.toObjectsCanonical? at hLower
  cases hContract :
      Contract.toObjectsCanonical? program.contract with
  | none =>
      simp [hContract] at hLower
  | some contractLower =>
      have hLowerEq :
          lower =
            contractLower.withMemoryContract program.memoryContract := by
        simpa [hContract] using hLower.symm
      unfold Contract.toObjectsCanonical? at hContract
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

theorem orderedDecomposition_of_toObjects?
    {ordered : OrderedProgram} {lower : Objects.Program}
    (hLower : ordered.toObjects? = some lower) :
    OrderedDecomposition ordered lower := by
  unfold OrderedProgram.toObjects? at hLower
  cases hBody :
      Stmt.toFunctionsListUncheckedFuel?
        (Stmt.fuel ordered.program.contract.dispatcher)
        (Fresh.initial ordered.names)
        ordered.program.contract.dispatcher with
  | none => simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨bodyStmts, afterBody⟩
      cases hFunctions :
          FunctionList.toFunDefsUncheckedFuel?
            (FunctionList.fuel ordered.functionEntries)
            afterBody ordered.functionEntries with
      | none => simp [hBody, hFunctions] at hLower
      | some functionResult =>
          rcases functionResult with ⟨functions, afterFunctions⟩
          have hLowerEq :
              lower =
                { root :=
                    .mk "root"
                      { functions := functions
                        body := { stmts := bodyStmts }
                        memoryContract := ordered.program.memoryContract }
                      [] [] } := by
            simpa [hBody, hFunctions] using hLower.symm
          refine
            ⟨bodyStmts, afterBody, functions, afterFunctions,
              hBody, hFunctions, ?_⟩
          subst lower
          rfl

noncomputable def passDecomposition_of_toObjectsCanonical?
    {program : Program} {lower : Objects.Program}
    (hLower : Program.toObjectsCanonical? program = some lower) :
    PassDecomposition program lower where
  functionEntries := Contract.functionEntries program.contract
  initialNames := Contract.names program.contract
  compiler := decomposition_of_toObjectsCanonical? hLower
  functionNamesNodup :=
    Contract.functionEntries_names_nodup program.contract
  lookup_mem := Contract.functionEntries_mem_of_lookup
  mem_lookup := Contract.lookup_of_functionEntries_mem
  sourceNamesReserved := by
    intro candidate hCandidate
    exact hCandidate

noncomputable def passDecomposition_of_ordered_toObjects?
    {ordered : OrderedProgram} {lower : Objects.Program}
    (hLower : ordered.toObjects? = some lower)
    (hRepresents : ordered.RepresentsSource)
    (hNames : ordered.FunctionNamesNodup) :
    PassDecomposition ordered.program lower where
  functionEntries := ordered.functionEntries
  initialNames := ordered.names
  compiler := orderedDecomposition_of_toObjects? hLower
  functionNamesNodup := hNames
  lookup_mem := by
    intro name fn hLookup
    apply FunctionList.mem_of_lookup_functionMap hNames
    rw [← hRepresents]
    exact hLookup
  mem_lookup := by
    intro name fn hMem
    rw [hRepresents]
    exact FunctionList.lookup_functionMap_of_mem hNames hMem
  sourceNamesReserved := by
    intro candidate hCandidate
    rcases List.mem_append.mp hCandidate with hDispatcher | hFunctions
    · exact List.mem_append_left _ hDispatcher
    · apply List.mem_append_right _
      apply FunctionList.names_mono _ hFunctions
      intro name fn hCanonical
      apply FunctionList.mem_of_lookup_functionMap hNames
      rw [← hRepresents]
      exact Contract.lookup_of_functionEntries_mem hCanonical

theorem decomposition_of_toObjectsWithObservers?
    {program : Program} {lower : Objects.Program}
    (hLower :
      Program.toObjectsWithObservers? program = some lower) :
    Decomposition program lower := by
  apply decomposition_of_toObjectsCanonical?
  simpa [Program.toObjectsWithObservers?] using hLower

theorem memoryContract_of_toObjectsCanonical?
    {program : Program} {lower : Objects.Program}
    (hLower :
      Program.toObjectsCanonical? program = some lower) :
    lower.toFunctions.memoryContract = program.memoryContract := by
  rcases decomposition_of_toObjectsCanonical? hLower with
    ⟨bodyStmts, afterBody, functions, afterFunctions,
      hBody, hFunctions, hProgram⟩
  exact congrArg Functions.Program.memoryContract hProgram

theorem memoryContract_of_toObjectsWithObservers?
    {program : Program} {lower : Objects.Program}
    (hLower :
      Program.toObjectsWithObservers? program = some lower) :
    lower.toFunctions.memoryContract = program.memoryContract := by
  apply memoryContract_of_toObjectsCanonical?
  simpa [Program.toObjectsWithObservers?] using hLower

theorem DecompositionFor.findFunction
    {program : Program} {targetProgram : Objects.Program}
    {functionEntries : List (Name × AstFunctionDefinition)}
    {initialNames : List Name}
    (hDecomposition :
      DecompositionFor program targetProgram functionEntries initialNames)
    (hNames : (functionEntries.map Prod.fst).Nodup)
    {name : Name} {fn : AstFunctionDefinition}
    (hMem : (name, fn) ∈ functionEntries) :
    ∃ before after lowerFn,
      Fresh.Extends (Fresh.initial initialNames) before ∧
      Functions.Source.FunList.find? name
          targetProgram.toFunctions.functions = some lowerFn ∧
      FunctionDefinition.toFunDefUncheckedFuel?
          (FunctionList.fuel functionEntries) before name fn =
        some (lowerFn, after) := by
  rcases hDecomposition with
    ⟨bodyStmts, afterBody, functions, afterFunctions,
      hBody, hFunctions, hTarget⟩
  have hLowering :
      FunctionList.UncheckedLowering
        (FunctionList.fuel functionEntries)
        afterBody functionEntries functions afterFunctions :=
    FunctionList.uncheckedLowering_of_toFunDefsUncheckedFuel?
      hFunctions
  obtain ⟨before, after, lowerFn, hFunctionsPrefix, hFind, hLowerFn⟩ :=
    hLowering.find_of_mem_stateExtends hNames hMem
  have hBodyPrefix :
      Fresh.Extends (Fresh.initial initialNames) afterBody :=
    Stmt.toFunctionsListUncheckedFuel?_stateExtends hBody
  refine
    ⟨before, after, lowerFn,
      Fresh.Extends.trans hBodyPrefix hFunctionsPrefix, ?_, hLowerFn⟩
  rw [hTarget]
  exact hFind

theorem DecompositionFor.findFunction_parts
    {program : Program} {targetProgram : Objects.Program}
    {functionEntries : List (Name × AstFunctionDefinition)}
    {initialNames : List Name}
    (hDecomposition :
      DecompositionFor program targetProgram functionEntries initialNames)
    (hNames : (functionEntries.map Prod.fst).Nodup)
    (hInitialNames : ∀ candidate,
      candidate ∈ FunctionList.names functionEntries →
        candidate ∈ initialNames)
    {name : Name} {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hMem : (name, .Def params returns body) ∈ functionEntries) :
    ∃ before after lowerFn,
      Fresh.Extends (Fresh.initial initialNames) before ∧
      Functions.Source.FunList.find? name
          targetProgram.toFunctions.functions = some lowerFn ∧
      lowerFn.name = name ∧
      lowerFn.params = identNames params ∧
      lowerFn.returns = identNames returns ∧
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel functionEntries)
          before body = some (lowerFn.body, after) ∧
      ∀ candidate,
        candidate ∈ lowerFn.returns ++ lowerFn.params →
          candidate ∈ before.used := by
  obtain ⟨before, after, lowerFn, hPrefix, hFind, hLower⟩ :=
    hDecomposition.findFunction hNames hMem
  obtain ⟨hName, hParams, hReturns, hBody⟩ :=
    FunctionDefinition.toFunDefUncheckedFuel?_parts hLower
  refine
    ⟨before, after, lowerFn, hPrefix, hFind, hName, hParams, hReturns,
      hBody, ?_⟩
  intro candidate hCandidate
  apply hPrefix candidate
  apply hInitialNames candidate
  rw [hReturns, hParams] at hCandidate
  apply (FunctionList.function_names_mem hMem).2 candidate
  rcases List.mem_append.mp hCandidate with hReturn | hParam
  · simp [FunctionDefinition.names, hReturn]
  · simp [FunctionDefinition.names, hParam]

theorem PassDecomposition.findFunction_parts
    {program : Program} {targetProgram : Objects.Program}
    (hDecomposition : PassDecomposition program targetProgram)
    {name : Name} {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hLookup : program.contract.functions.lookup name =
      some (.Def params returns body)) :
    ∃ before after lowerFn,
      Fresh.Extends
          (Fresh.initial hDecomposition.initialNames) before ∧
      Functions.Source.FunList.find? name
          targetProgram.toFunctions.functions = some lowerFn ∧
      lowerFn.name = name ∧
      lowerFn.params = identNames params ∧
      lowerFn.returns = identNames returns ∧
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel hDecomposition.functionEntries)
          before body = some (lowerFn.body, after) ∧
      ∀ candidate,
        candidate ∈ lowerFn.returns ++ lowerFn.params →
          candidate ∈ before.used := by
  apply DecompositionFor.findFunction_parts hDecomposition.compiler
    hDecomposition.functionNamesNodup
  · intro candidate hCandidate
    apply hDecomposition.sourceNamesReserved candidate
    apply List.mem_append_right _
    apply FunctionList.names_mono _ hCandidate
    intro entryName entryFn hEntry
    exact Contract.functionEntries_mem_of_lookup
      (hDecomposition.mem_lookup hEntry)
  · exact hDecomposition.lookup_mem hLookup

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
  exact DecompositionFor.findFunction hDecomposition
    (Contract.functionEntries_names_nodup program.contract)
    (Contract.functionEntries_mem_of_lookup hLookup)

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
  apply DecompositionFor.findFunction_parts hDecomposition
    (Contract.functionEntries_names_nodup program.contract)
  · intro candidate hCandidate
    exact List.mem_append_right _ hCandidate
  · exact Contract.functionEntries_mem_of_lookup hLookup

theorem OrderedDecomposition.findFunction_parts
    {ordered : OrderedProgram} {targetProgram : Objects.Program}
    (hDecomposition : OrderedDecomposition ordered targetProgram)
    (hRepresents : ordered.RepresentsSource)
    (hNames : ordered.FunctionNamesNodup)
    {name : Name} {params returns : List EvmYul.Identifier}
    {body : List AstStmt}
    (hLookup : ordered.program.contract.functions.lookup name =
      some (.Def params returns body)) :
    ∃ before after lowerFn,
      Fresh.Extends (Fresh.initial ordered.names) before ∧
      Functions.Source.FunList.find? name
          targetProgram.toFunctions.functions = some lowerFn ∧
      lowerFn.name = name ∧
      lowerFn.params = identNames params ∧
      lowerFn.returns = identNames returns ∧
      Stmt.List.toBlockUncheckedFuel?
          (FunctionList.fuel ordered.functionEntries)
          before body = some (lowerFn.body, after) ∧
      ∀ candidate,
        candidate ∈ lowerFn.returns ++ lowerFn.params →
          candidate ∈ before.used := by
  apply DecompositionFor.findFunction_parts hDecomposition hNames
  · intro candidate hCandidate
    exact List.mem_append_right _ hCandidate
  · apply FunctionList.mem_of_lookup_functionMap hNames
    rw [← hRepresents]
    exact hLookup

end FunctionsCompilerArtifact
end Yul
end EvmCompiler
