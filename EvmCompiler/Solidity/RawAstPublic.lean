import EvmCompiler.Solidity.RawAstSourceSemantics
import EvmCompiler.Solidity.Public

/-!
Checked artifact-facing wrappers for the raw solc frontend.

The raw decoder/elaborator itself stays in `Solidity.RawAst` and stops at
`Solidity.Frontend.Program`.  This module is the narrow integration point with
the existing checked stack-object artifact API.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst

def compileArtifactFromRawSolcIrWithLinkerSymbols? (rawJson : String)
    (selection : Selection)
    (linkerSymbols : List (Frontend.Name × Frontend.Word)) :
    Option Frontend.Program.Artifact := do
  let program ← decodeAndElaborateSolcIr? rawJson selection
  program.compileArtifactWithLinkerSymbols? linkerSymbols

def compileArtifactFromRawSolcIr? (rawJson : String)
    (selection : Selection) : Option Frontend.Program.Artifact :=
  match Lean.Json.parse rawJson with
  | .error _ => none
  | .ok json =>
      match decodeAndElaborateSolcIrJson json selection with
      | .error _ => none
      | .ok program =>
          match decodeLinkerSymbolsJson json selection with
          | .error _ => none
          | .ok linkerSymbols =>
              program.compileArtifactWithLinkerSymbols? linkerSymbols

/-- Unlinked-library variant of the raw entry point: `linkersymbol` names
absent from the Standard JSON `settings.libraries` metadata are compiled as
unresolved link references instead of failing the compile.  When the
metadata covers every library name this coincides with substituting nothing
and gating the ordinary compile. -/
def compileArtifactUnlinkedFromRawSolcIr? (rawJson : String)
    (selection : Selection) : Option Frontend.Program.Artifact :=
  match Lean.Json.parse rawJson with
  | .error _ => none
  | .ok json =>
      match decodeAndElaborateSolcIrJson json selection with
      | .error _ => none
      | .ok program =>
          match decodeLinkerSymbolsJson json selection with
          | .error _ => none
          | .ok linkerSymbols =>
              program.compileArtifactUnlinked? linkerSymbols

theorem compileArtifactUnlinkedFromRawSolcIr?_decoded
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactUnlinkedFromRawSolcIr? rawJson selection =
        some artifact) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
          program.compileArtifactUnlinked? linkerSymbols = some artifact := by
  unfold compileArtifactUnlinkedFromRawSolcIr? at hCompile
  cases hParse : Lean.Json.parse rawJson with
  | error err =>
      simp [hParse] at hCompile
  | ok json =>
      cases hDecode : decodeAndElaborateSolcIrJson json selection with
      | error err =>
          simp [hParse, hDecode] at hCompile
      | ok program =>
          cases hLinker : decodeLinkerSymbolsJson json selection with
          | error err =>
              simp [hParse, hDecode, hLinker] at hCompile
          | ok linkerSymbols =>
              have hProgramCompile :
                  program.compileArtifactUnlinked? linkerSymbols =
                    some artifact := by
                simpa [hParse, hDecode, hLinker] using hCompile
              refine ⟨program, linkerSymbols, ?_, ?_, hProgramCompile⟩
              · simp [decodeAndElaborateSolcIr?, hParse, hDecode]
              · simp [decodeLinkerSymbols?, hParse, hLinker]

theorem compileArtifactFromRawSolcIr?_decoded
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
          program.compileArtifactWithLinkerSymbols? linkerSymbols =
            some artifact := by
  unfold compileArtifactFromRawSolcIr? at hCompile
  cases hParse : Lean.Json.parse rawJson with
  | error err =>
      simp [hParse] at hCompile
  | ok json =>
      cases hDecode : decodeAndElaborateSolcIrJson json selection with
      | error err =>
          simp [hParse, hDecode] at hCompile
      | ok program =>
          cases hLinker : decodeLinkerSymbolsJson json selection with
          | error err =>
              simp [hParse, hDecode, hLinker] at hCompile
          | ok linkerSymbols =>
              have hProgramCompile :
                  program.compileArtifactWithLinkerSymbols? linkerSymbols =
                    some artifact := by
                simpa [hParse, hDecode, hLinker] using hCompile
              refine ⟨program, linkerSymbols, ?_, ?_, hProgramCompile⟩
              · simp [decodeAndElaborateSolcIr?, hParse, hDecode]
              · simp [decodeLinkerSymbols?, hParse, hLinker]

theorem compileArtifactFromRawSolcIr?_valid
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeAndElaborateSolcIrJson json selection = .ok program ∧
          decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
            Frontend.Object.VerifiedStackObjectArtifact.ValidFor
              linkerSymbols program.object artifact := by
  unfold compileArtifactFromRawSolcIr? at hCompile
  cases hParse : Lean.Json.parse rawJson with
  | error err =>
      simp [hParse] at hCompile
  | ok json =>
      cases hDecode : decodeAndElaborateSolcIrJson json selection with
      | error err =>
          simp [hParse, hDecode] at hCompile
      | ok program =>
          cases hLinker : decodeLinkerSymbolsJson json selection with
          | error err =>
              simp [hParse, hDecode, hLinker] at hCompile
          | ok linkerSymbols =>
              have hProgramCompile :
                  program.compileArtifactWithLinkerSymbols? linkerSymbols =
                    some artifact := by
                simpa [hParse, hDecode, hLinker] using hCompile
              refine ⟨json, program, linkerSymbols, ?_, ?_, ?_, ?_⟩
              · rfl
              · simp [hDecode]
              · simp [hLinker]
              · exact
                  Frontend.Program.compileArtifactWithLinkerSymbols?_valid
                    (program := program) (linkerSymbols := linkerSymbols)
                    (artifact := artifact) hProgramCompile

theorem compileArtifactFromRawSolcIr?_rawParts
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
                Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                  linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_parts hDecode with
    ⟨selected, object, hSelected, hObject, hProgram⟩
  exact
    ⟨json, selected, object, program, linkerSymbols,
      hParse, hSelected, hObject, hProgram, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_itemRefsPreserveOrder
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Raw.Object.itemRefsPreserveOrder? selected.root object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
                  Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                    linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_itemRefsPreserveOrder hDecode with
    ⟨selected, object, hSelected, hObject, hOrder, hProgram⟩
  exact
    ⟨json, selected, object, program, linkerSymbols,
      hParse, hSelected, hObject, hOrder, hProgram, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_noRawClzCall
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.noRawClzCall? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
                  Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                    linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_noRawClzCall hDecode with
    ⟨selected, object, hSelected, hObject, hNoRawClz, hProgram⟩
  exact
    ⟨json, selected, object, program, linkerSymbols,
      hParse, hSelected, hObject, hNoRawClz, hProgram, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_functionDefStubsRetained
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.functionDefStubsRetained? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
                  Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                    linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_functionDefStubsRetained
      hDecode with
    ⟨selected, object, hSelected, hObject, hStubs, hProgram⟩
  exact
    ⟨json, selected, object, program, linkerSymbols,
      hParse, hSelected, hObject, hStubs, hProgram, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_userCallsResolved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.userCallsResolved? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
                  Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                    linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_userCallsResolved hDecode with
    ⟨selected, object, hSelected, hObject, hResolved, hProgram⟩
  exact
    ⟨json, selected, object, program, linkerSymbols,
      hParse, hSelected, hObject, hResolved, hProgram, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_clzExpansionOk
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.ClzExpansionOk selected.root program.object ∧
            decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
              Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_clzExpansionOk hDecode with
    ⟨selected, hSelected, hClz⟩
  exact ⟨json, selected, program, linkerSymbols,
    hParse, hSelected, hClz, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_clzHelperSpecOk
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.ClzHelperSpecOk selected.root program.object ∧
            decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
              Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_clzHelperSpecOk hDecode with
    ⟨selected, hSelected, hClzSpec⟩
  exact ⟨json, selected, program, linkerSymbols,
    hParse, hSelected, hClzSpec, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_hoistedFunctionsRetained
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.HoistedFunctionsRetained selected.root program.object ∧
            decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
              Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_hoistedFunctionsRetained hDecode with
    ⟨selected, hSelected, hHoisted⟩
  exact ⟨json, selected, program, linkerSymbols,
    hParse, hSelected, hHoisted, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_hoistedFunction_ordered_entry
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {json : Lean.Json} {selected : SelectedIr}
    {code : List Raw.Stmt} {coreDispatcher : List Frontend.Stmt}
    {state : Elab.State} {name : Frontend.Name}
    {fn : Frontend.FunctionDef}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (hParse : Lean.Json.parse rawJson = .ok json)
    (hSelected : decodeSelectedIr json selection = .ok selected)
    (hCode : selected.root.code? = some code)
    (hCore :
      Elab.elaborateCodeCore code = .ok (coreDispatcher, state))
    (hHoisted : (name, fn) ∈ state.hoistedFunctions) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word))
        (context : Frontend.ObjectBuiltinContext)
        (memoryContract : EvmCompiler.MemoryContract.Contract)
        (resolvedFn : Frontend.FunctionDef)
        (yulBody : List Frontend.AstStmt),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
          program.compileArtifactWithLinkerSymbols? linkerSymbols =
            some artifact ∧
          program.object.compileVerifiedStackCodeArtifactIn? context =
            some artifact.codeArtifact ∧
          Frontend.MemoryGuard.Object.inferredContract? program.object =
            some memoryContract ∧
          Frontend.FunctionDef.resolveObjectBuiltinsIn? fn
              { context with memoryContract := memoryContract } =
            some resolvedFn ∧
          (name, resolvedFn) ∈ artifact.codeArtifact.resolved.functions ∧
          resolvedFn.params = fn.params ∧
          resolvedFn.returns = fn.returns ∧
          Frontend.Stmt.List.toYul? resolvedFn.body = some yulBody ∧
          (name,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              resolvedFn.params resolvedFn.returns yulBody) ∈
            artifact.codeArtifact.ordered.functionEntries := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, hDecode, hLinker, hProgramCompile⟩
  rcases decodeAndElaborateSolcIr?_hoistedFunctionsRetained hDecode with
    ⟨json', selected', hParse', hSelected', hRetained⟩
  rw [hParse] at hParse'
  cases hParse'
  rw [hSelected] at hSelected'
  cases hSelected'
  unfold Raw.Object.HoistedFunctionsRetained at hRetained
  rw [hCode] at hRetained
  rcases hRetained with
    ⟨coreDispatcher', state', helper?, arg?, ret?,
      hCore', _hCodeElab, hKeep⟩
  rw [hCore] at hCore'
  cases hCore'
  have hFrontendMem : (name, fn) ∈ program.object.functions :=
    hKeep (name, fn) hHoisted
  rcases
      Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
        hProgramCompile with
    ⟨_childArtifacts, plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCodeArtifact, _hArtifactChildren, _hContext, _hChildImages,
      _hPayload, _hImage⟩
  rcases Frontend.Object.compileVerifiedStackCodeArtifactIn?_function_entry
      hCodeArtifact hFrontendMem with
    ⟨memoryContract, resolvedFn, yulBody, hMemory, hFnResolve,
      hResolvedMem, hParams, hReturns, hBodyYul, hEntry⟩
  exact
    ⟨program, linkerSymbols, plan.context, memoryContract, resolvedFn,
      yulBody, hDecode, hLinker, hProgramCompile, hCodeArtifact, hMemory,
      hFnResolve, hResolvedMem, hParams, hReturns, hBodyYul, hEntry⟩

theorem compileArtifactFromRawSolcIr?_frontendValidated
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Raw.Object.FrontendValidated selected.root object ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                decodeLinkerSymbolsJson json selection = .ok linkerSymbols ∧
                  Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                    linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIr?_valid hCompile with
    ⟨json, program, linkerSymbols, hParse, hDecode, hLinker, hValid⟩
  rcases decodeAndElaborateSolcIrJson_frontendValidated hDecode with
    ⟨selected, object, hSelected, hObject, hValidated, hProgram⟩
  exact
    ⟨json, selected, object, program, linkerSymbols, hParse, hSelected,
      hObject, hValidated, hProgram, hLinker, hValid⟩

theorem compileArtifactFromRawSolcIr?_function_name_entry
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {program : Frontend.Program} {name : Frontend.Name}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (hDecode : decodeAndElaborateSolcIr? rawJson selection = some program)
    (hContains :
      (program.object.functions.map Prod.fst).contains name = true) :
    ∃ (linkerSymbols : List (Frontend.Name × Frontend.Word))
        (context : Frontend.ObjectBuiltinContext)
        (fn resolvedFn : Frontend.FunctionDef)
        (memoryContract : EvmCompiler.MemoryContract.Contract)
        (yulBody : List Frontend.AstStmt),
      decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        program.object.compileVerifiedStackCodeArtifactIn? context =
          some artifact.codeArtifact ∧
        (name, fn) ∈ program.object.functions ∧
        Frontend.MemoryGuard.Object.inferredContract? program.object =
          some memoryContract ∧
        Frontend.FunctionDef.resolveObjectBuiltinsIn? fn
            { context with memoryContract := memoryContract } =
          some resolvedFn ∧
        (name, resolvedFn) ∈ artifact.codeArtifact.resolved.functions ∧
        resolvedFn.params = fn.params ∧
        resolvedFn.returns = fn.returns ∧
        Frontend.Stmt.List.toYul? resolvedFn.body = some yulBody ∧
        (name,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            resolvedFn.params resolvedFn.returns yulBody) ∈
          artifact.codeArtifact.ordered.functionEntries := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨decodedProgram, linkerSymbols, hDecoded, hLinker, hProgramCompile⟩
  rw [hDecode] at hDecoded
  cases hDecoded
  rcases
      Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
        hProgramCompile with
    ⟨_childArtifacts, plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCodeArtifact, _hArtifactChildren, _hContext, _hChildImages,
      _hPayload, _hImage⟩
  rcases
      Frontend.Object.compileVerifiedStackCodeArtifactIn?_function_name_entry
        hCodeArtifact hContains with
    ⟨fn, memoryContract, resolvedFn, yulBody, hMem, hMemory, hFnResolve,
      hResolvedMem, hParams, hReturns, hBodyYul, hYulEntry⟩
  exact
    ⟨linkerSymbols, plan.context, fn, resolvedFn, memoryContract, yulBody,
      hLinker, hProgramCompile, hCodeArtifact, hMem, hMemory, hFnResolve,
      hResolvedMem, hParams, hReturns, hBodyYul, hYulEntry⟩

theorem compileArtifactFromRawSolcIr?_resolved_ordered
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word))
        (context : Frontend.ObjectBuiltinContext),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        program.object.compileVerifiedStackCodeArtifactIn? context =
          some artifact.codeArtifact ∧
        program.object.resolveObjectBuiltinsIn? context =
          some artifact.codeArtifact.resolved ∧
        artifact.codeArtifact.resolved.toSolcYulOrderedProgram? =
          some artifact.codeArtifact.ordered := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, hDecode, hLinker, hProgramCompile⟩
  rcases
      Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
        hProgramCompile with
    ⟨_childArtifacts, plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCodeArtifact, _hArtifactChildren, _hContext, _hChildImages,
      _hPayload, _hImage⟩
  obtain ⟨hResolved, hOrdered, _hLower, _hStack, _pushPlan, _hPlan,
      _hCompact, _hBytes, _hMarker⟩ :=
    Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCodeArtifact
  exact
    ⟨program, linkerSymbols, plan.context, hDecode, hLinker, hProgramCompile,
      hCodeArtifact, hResolved, hOrdered⟩

/-- Boundary package for the future raw-source theorem.

Successful raw compilation internally fixes the selected raw solc object and the
checked object-builtin context whose resolution produced the ordered Yul
artifact.  Consumers should use this package instead of passing a public
context/certificate premise.
-/
theorem compileArtifactFromRawSolcIr?_raw_source_ordered_context
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word))
        (context : Frontend.ObjectBuiltinContext),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
        decodeAndElaborateSolcIr? rawJson selection = some program ∧
        selected.root.elaborate? selected.evmVersion =
          .ok program.object ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        program.object.compileVerifiedStackCodeArtifactIn? context =
          some artifact.codeArtifact ∧
        program.object.resolveObjectBuiltinsIn? context =
          some artifact.codeArtifact.resolved ∧
        artifact.codeArtifact.resolved.toSolcYulOrderedProgram? =
          some artifact.codeArtifact.ordered ∧
        Raw.SourceSemantics.contextForObject context =
          { objectBuiltins := context } := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, hDecode, hLinker, hProgramCompile⟩
  rcases decodeAndElaborateSolcIr?_parts hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram⟩
  subst program
  rcases
      Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_parts
        hProgramCompile with
    ⟨_childArtifacts, plan, _codeArtifact, _hChildren, _hPlan, _hFinish,
      hCodeArtifact, _hArtifactChildren, _hContext, _hChildImages,
      _hPayload, _hImage⟩
  obtain ⟨hResolved, hOrdered, _hLower, _hStack, _pushPlan, _hPlan,
      _hCompact, _hBytes, _hMarker⟩ :=
    Frontend.Object.compileVerifiedStackCodeArtifactIn?_parts hCodeArtifact
  exact
    ⟨json, selected,
      { source := selected.source, contract := selected.contract,
        object := object },
      linkerSymbols, plan.context, hParse, hSelected,
      by simpa using hDecode, hObject, hLinker,
      hProgramCompile, hCodeArtifact, hResolved, hOrdered, rfl⟩

theorem compileArtifactFromRawSolcIr?_sourceLocalFunction_noShadow_program_entries
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {json : Lean.Json} {selected : SelectedIr}
    {code : List Raw.Stmt}
    {topName : Frontend.Name} {topParams topReturns : List Frontend.Name}
    {topBody : List Raw.Stmt}
    {name : Frontend.Name} {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (hParse : Lean.Json.parse rawJson = .ok json)
    (hSelected : decodeSelectedIr json selection = .ok selected)
    (hCode : selected.root.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word))
        (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (args' : List Frontend.Expr)
        (topFn : Frontend.FunctionDef),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact ∧
        (topName, topFn) ∈ program.object.functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
        (generated, localFn) ∈ program.object.functions := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, hDecode, hLinker, hProgramCompile⟩
  rcases
    decodeAndElaborateSolcIr?_sourceLocalFunction_noShadow_function_entries
      hParse hSelected hCode hTop hLocal hOccurs hDecode with
    ⟨generated, localFn, args', topFn,
      hTopEntry, hOccurrence, hLocalEntry⟩
  exact
    ⟨program, linkerSymbols, generated, localFn, args', topFn,
      hDecode, hLinker, hProgramCompile,
      Frontend.Program.compileArtifactWithLinkerSymbols?_valid
        hProgramCompile,
      hTopEntry, hOccurrence, hLocalEntry⟩

theorem compileArtifactFromRawSolcIr?_sourceLocalFunction_noShadow_alphaPreserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {json : Lean.Json} {selected : SelectedIr}
    {code : List Raw.Stmt}
    {topName : Frontend.Name} {topParams topReturns : List Frontend.Name}
    {topBody : List Raw.Stmt}
    {name : Frontend.Name} {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (hParse : Lean.Json.parse rawJson = .ok json)
    (hSelected : decodeSelectedIr json selection = .ok selected)
    (hCode : selected.root.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word)),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact ∧
        Raw.Source.AlphaRenamedLocalCallPreserved
          topBody program.object.functions topName name
            localParams localReturns localBody args := by
  rcases
      compileArtifactFromRawSolcIr?_sourceLocalFunction_noShadow_program_entries
        hCompile hParse hSelected hCode hTop hLocal hOccurs with
    ⟨program, linkerSymbols, generated, localFn, frontArgs, topFn,
      hDecode, hLinker, hProgramCompile, hValid,
      hTopEntry, hOccurrence, hCalleeEntry⟩
  exact
    ⟨program, linkerSymbols, hDecode, hLinker, hProgramCompile, hValid,
      Raw.Source.AlphaRenamedLocalCallPreserved.of_entries
        hLocal hOccurs hTopEntry hOccurrence hCalleeEntry⟩

theorem compileArtifactFromRawSolcIr?_decodingCorrect
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    Assembly.Compact.DecodingCorrect
      artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList artifact.image.bytes) := by
  unfold compileArtifactFromRawSolcIr? at hCompile
  cases hParse : Lean.Json.parse rawJson with
  | error err =>
      simp [hParse] at hCompile
  | ok json =>
      cases hDecode : decodeAndElaborateSolcIrJson json selection with
      | error err =>
          simp [hParse, hDecode] at hCompile
      | ok program =>
          cases hLinker : decodeLinkerSymbolsJson json selection with
          | error err =>
              simp [hParse, hDecode, hLinker] at hCompile
          | ok linkerSymbols =>
              have hProgramCompile :
                  program.compileArtifactWithLinkerSymbols? linkerSymbols =
                    some artifact := by
                simpa [hParse, hDecode, hLinker] using hCompile
              exact
                Frontend.Program.compileArtifactWithLinkerSymbols?_decodingCorrect
                  (program := program) (linkerSymbols := linkerSymbols)
                  (artifact := artifact) hProgramCompile

/-- Suffix-tolerant decoding correctness for the raw-solc entry point: the
checked image remains a correct decoding prefix with any appended caller-owned
byte suffix (for example ABI-encoded constructor arguments in a creation
frame). `compileArtifactFromRawSolcIr?_decodingCorrect` is the `suffix := []`
instance. -/
theorem compileArtifactFromRawSolcIr?_decodingCorrect_withCodeSuffix
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (suffix : List UInt8) :
    Assembly.Compact.DecodingCorrect
      artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList (artifact.image.bytes ++ suffix)) := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, _hDecode, _hLinker, hProgramCompile⟩
  exact
    Frontend.Object.compileVerifiedStackObjectArtifactWithLinkerSymbols?_decodingCorrect_withCodeSuffix
      hProgramCompile suffix

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_valid
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ program : Frontend.Program,
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact := by
  unfold compileArtifactFromRawSolcIrWithLinkerSymbols? at hCompile
  cases hDecode : decodeAndElaborateSolcIr? rawJson selection with
  | none =>
      simp [hDecode] at hCompile
  | some program =>
      have hValid :=
        Frontend.Program.compileArtifactWithLinkerSymbols?_valid
          (program := program) (linkerSymbols := linkerSymbols)
          (artifact := artifact)
      have hProgramCompile :
          program.compileArtifactWithLinkerSymbols? linkerSymbols =
            some artifact := by
        simpa [hDecode] using hCompile
      exact ⟨program, rfl, hValid hProgramCompile⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_rawParts
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            program =
              { source := selected.source
                contract := selected.contract
                object := object } ∧
              Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_parts hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hProgram⟩
  exact
    ⟨json, selected, object, program,
      hParse, hSelected, hObject, hProgram, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_itemRefsPreserveOrder
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Raw.Object.itemRefsPreserveOrder? selected.root object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                  linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_itemRefsPreserveOrder hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hOrder, hProgram⟩
  exact
    ⟨json, selected, object, program,
      hParse, hSelected, hObject, hOrder, hProgram, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_noRawClzCall
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.noRawClzCall? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                  linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_noRawClzCall hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hNoRawClz, hProgram⟩
  exact
    ⟨json, selected, object, program,
      hParse, hSelected, hObject, hNoRawClz, hProgram, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_functionDefStubsRetained
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.functionDefStubsRetained? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                  linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_functionDefStubsRetained hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hStubs, hProgram⟩
  exact
    ⟨json, selected, object, program,
      hParse, hSelected, hObject, hStubs, hProgram, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_userCallsResolved
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Frontend.Object.userCallsResolved? object = true ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                  linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_userCallsResolved hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hResolved, hProgram⟩
  exact
    ⟨json, selected, object, program,
      hParse, hSelected, hObject, hResolved, hProgram, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_clzExpansionOk
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.ClzExpansionOk selected.root program.object ∧
            Frontend.Object.VerifiedStackObjectArtifact.ValidFor
              linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_clzExpansionOk hDecode with
    ⟨json, selected, hParse, hSelected, hClz⟩
  exact ⟨json, selected, program, hParse, hSelected, hClz, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_clzHelperSpecOk
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.ClzHelperSpecOk selected.root program.object ∧
            Frontend.Object.VerifiedStackObjectArtifact.ValidFor
              linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_clzHelperSpecOk hDecode with
    ⟨json, selected, hParse, hSelected, hClzSpec⟩
  exact ⟨json, selected, program, hParse, hSelected, hClzSpec, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_hoistedFunctionsRetained
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          Raw.Object.HoistedFunctionsRetained selected.root program.object ∧
            Frontend.Object.VerifiedStackObjectArtifact.ValidFor
              linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_hoistedFunctionsRetained hDecode with
    ⟨json, selected, hParse, hSelected, hHoisted⟩
  exact ⟨json, selected, program, hParse, hSelected, hHoisted, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_frontendValidated
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    ∃ (json : Lean.Json) (selected : SelectedIr)
        (object : Frontend.Object) (program : Frontend.Program),
      Lean.Json.parse rawJson = .ok json ∧
        decodeSelectedIr json selection = .ok selected ∧
          selected.root.elaborate? selected.evmVersion = .ok object ∧
            Raw.Object.FrontendValidated selected.root object ∧
              program =
                { source := selected.source
                  contract := selected.contract
                  object := object } ∧
                Frontend.Object.VerifiedStackObjectArtifact.ValidFor
                  linkerSymbols program.object artifact := by
  rcases compileArtifactFromRawSolcIrWithLinkerSymbols?_valid hCompile with
    ⟨program, hDecode, hValid⟩
  rcases decodeAndElaborateSolcIr?_frontendValidated hDecode with
    ⟨json, selected, object, hParse, hSelected, hObject, hValidated, hProgram⟩
  exact
    ⟨json, selected, object, program, hParse, hSelected,
      hObject, hValidated, hProgram, hValid⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_sourceLocalFunction_noShadow_program_entries
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    {json : Lean.Json} {selected : SelectedIr}
    {code : List Raw.Stmt}
    {topName : Frontend.Name} {topParams topReturns : List Frontend.Name}
    {topBody : List Raw.Stmt}
    {name : Frontend.Name} {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact)
    (hParse : Lean.Json.parse rawJson = .ok json)
    (hSelected : decodeSelectedIr json selection = .ok selected)
    (hCode : selected.root.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args) :
    ∃ (program : Frontend.Program)
        (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (args' : List Frontend.Expr)
        (topFn : Frontend.FunctionDef),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact ∧
        (topName, topFn) ∈ program.object.functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
        (generated, localFn) ∈ program.object.functions := by
  unfold compileArtifactFromRawSolcIrWithLinkerSymbols? at hCompile
  cases hDecode : decodeAndElaborateSolcIr? rawJson selection with
  | none =>
      simp [hDecode] at hCompile
  | some program =>
      have hProgramCompile :
          program.compileArtifactWithLinkerSymbols? linkerSymbols =
            some artifact := by
        simpa [hDecode] using hCompile
      rcases
        decodeAndElaborateSolcIr?_sourceLocalFunction_noShadow_function_entries
          hParse hSelected hCode hTop hLocal hOccurs hDecode with
        ⟨generated, localFn, args', topFn,
          hTopEntry, hOccurrence, hLocalEntry⟩
      exact
        ⟨program, generated, localFn, args', topFn,
          rfl, hProgramCompile,
          Frontend.Program.compileArtifactWithLinkerSymbols?_valid
            hProgramCompile,
          hTopEntry, hOccurrence, hLocalEntry⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_sourceLocalFunction_noShadow_alphaPreserved
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    {json : Lean.Json} {selected : SelectedIr}
    {code : List Raw.Stmt}
    {topName : Frontend.Name} {topParams topReturns : List Frontend.Name}
    {topBody : List Raw.Stmt}
    {name : Frontend.Name} {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt} {args : List Raw.Expr}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact)
    (hParse : Lean.Json.parse rawJson = .ok json)
    (hSelected : decodeSelectedIr json selection = .ok selected)
    (hCode : selected.root.code? = some code)
    (hTop :
      .functionDefinition topName topParams topReturns topBody ∈ code)
    (hLocal :
      Raw.Source.LocalFunction topBody
        name localParams localReturns localBody)
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args) :
    ∃ (program : Frontend.Program),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact ∧
        Raw.Source.AlphaRenamedLocalCallPreserved
          topBody program.object.functions topName name
            localParams localReturns localBody args := by
  rcases
      compileArtifactFromRawSolcIrWithLinkerSymbols?_sourceLocalFunction_noShadow_program_entries
        hCompile hParse hSelected hCode hTop hLocal hOccurs with
    ⟨program, generated, localFn, frontArgs, topFn,
      hDecode, hProgramCompile, hValid,
      hTopEntry, hOccurrence, hCalleeEntry⟩
  exact
    ⟨program, hDecode, hProgramCompile, hValid,
      Raw.Source.AlphaRenamedLocalCallPreserved.of_entries
        hLocal hOccurs hTopEntry hOccurrence hCalleeEntry⟩

theorem compileArtifactFromRawSolcIrWithLinkerSymbols?_decodingCorrect
    {rawJson : String} {selection : Selection}
    {linkerSymbols : List (Frontend.Name × Frontend.Word)}
    {artifact : Frontend.Program.Artifact}
    (hCompile :
      compileArtifactFromRawSolcIrWithLinkerSymbols? rawJson selection
        linkerSymbols = some artifact) :
    Assembly.Compact.DecodingCorrect
      artifact.codeArtifact.compact.program
      (Assembly.Bytecode.ofList artifact.image.bytes) := by
  unfold compileArtifactFromRawSolcIrWithLinkerSymbols? at hCompile
  cases hDecode : decodeAndElaborateSolcIr? rawJson selection with
  | none =>
      simp [hDecode] at hCompile
  | some program =>
      have hCorrect :=
        Frontend.Program.compileArtifactWithLinkerSymbols?_decodingCorrect
          (program := program) (linkerSymbols := linkerSymbols)
          (artifact := artifact)
      have hProgramCompile :
          program.compileArtifactWithLinkerSymbols? linkerSymbols =
            some artifact := by
        simpa [hDecode] using hCompile
      exact hCorrect hProgramCompile

end RawAst
end Solidity
end EvmCompiler
