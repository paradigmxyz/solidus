import EvmCompiler.Solidity.RawAstPublic
import EvmCompiler.Yul.EndToEnd

/-!
Raw solc Standard JSON to bytecode theorem composition.

The raw decoder/elaborator and artifact wrapper stay Solidity-owned. This
module is only the thin public composition that feeds their checked artifact
result into the existing optimized-Yul end-to-end theorem.
-/

namespace EvmCompiler
namespace Solidity
namespace RawAst

/-- Primary raw-solc theorem. A successful checked compilation from raw solc
Standard JSON internally decodes the selected `irOptimizedAst`, elaborates it to
`Solidity.Frontend`, extracts linker metadata, and preserves every finite
ordered open-world prefix to the emitted raw bytecode image. -/
theorem optimizedRawSolcIrToRawBytecode
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, _hDecode, _hLinker, hProgramCompile⟩
  exact
    Yul.EndToEnd.optimizedSolcYulToRawBytecode
      (object := program.object)
      (linkerSymbols := linkerSymbols)
      (artifact := artifact)
      (sourceFuel := sourceFuel)
      (baseSource := baseSource)
      hProgramCompile

/-- Raw-solc finite-prefix theorem with source-local nested-call evidence.

This composes the Solidity-owned raw frontend caller/callee preservation facts
with the public optimized-Yul-to-bytecode theorem, so consumers do not need a
separate proof corridor to recover the generated caller/callee entries for
alpha-renamed local calls. -/
theorem optimizedRawSolcIrToRawBytecode_sourceLocalFunction_noShadow
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
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
        (topFn : Frontend.FunctionDef)
        (structuredFuel : Nat),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact ∧
        (topName, topFn) ∈ program.object.functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
        (generated, localFn) ∈ program.object.functions ∧
        Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_sourceLocalFunction_noShadow_program_entries
      hCompile hParse hSelected hCode hTop hLocal hOccurs with
    ⟨program, linkerSymbols, generated, localFn, args', topFn,
      hDecode, hLinker, hProgramCompile, hValid, hTopEntry,
      hOccurrence, hLocalEntry⟩
  rcases optimizedRawSolcIrToRawBytecode
      (sourceFuel := sourceFuel) (baseSource := baseSource) hCompile with
    ⟨structuredFuel, hAccepted, hForward⟩
  exact
    ⟨program, linkerSymbols, generated, localFn, args', topFn,
      structuredFuel, hDecode, hLinker, hProgramCompile, hValid,
      hTopEntry, hOccurrence, hLocalEntry, hAccepted, hForward⟩

/-- Raw-solc finite-prefix theorem with a source-facing alpha-preservation fact
for nested local calls.  This theorem keeps the generated callee name
existential inside `AlphaRenamedLocalCallPreserved`, so the public statement
talks about the raw local declaration/call and the resulting frontend
resolution relation rather than a loose tuple of generated artifacts. -/
theorem optimizedRawSolcIrToRawBytecode_sourceLocalFunction_noShadow_alphaPreserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
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
        (structuredFuel : Nat),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact ∧
        Raw.Source.AlphaRenamedLocalCallPreserved
          topBody program.object.functions topName name
            localParams localReturns localBody args ∧
        Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.ForwardRel
          Yul.FunctionsInteractionPrimitive.Truncated
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_sourceLocalFunction_noShadow_alphaPreserved
      hCompile hParse hSelected hCode hTop hLocal hOccurs with
    ⟨program, linkerSymbols, hDecode, hLinker, hProgramCompile,
      hValid, hAlpha⟩
  rcases optimizedRawSolcIrToRawBytecode
      (sourceFuel := sourceFuel) (baseSource := baseSource) hCompile with
    ⟨structuredFuel, hAccepted, hForward⟩
  exact
    ⟨program, linkerSymbols, structuredFuel, hDecode, hLinker,
      hProgramCompile, hValid, hAlpha, hAccepted, hForward⟩

/-- Semantic call corollary for an alpha-preserved raw local call.

Once frontend ordered-Yul conversion has populated the active contract's
function map with the generated local callee, the generic Yul call semantics
uses that exact callee body.  This is the first source-local-call bridge to the
interpreter rule itself; the surrounding same-observation theorem still needs
the caller context and source argument evaluation relation. -/
theorem alphaRenamedLocalCallPreserved_call_succ_of_local_body
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (topFn : Frontend.FunctionDef)
        (topYulBody localYulBody : List Frontend.AstStmt),
      (topName, topFn) ∈ object.functions ∧
        FrontendOccurrence.StmtListUserCall
          topFn.body generated frontArgs ∧
        (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {fuel : Nat} {callArgs : List Frontend.Word}
          {state stateAfterBody : σ},
          Yul.Source.Effectful.exec model prim fuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource state
                (EvmYul.Yul.State.mkOk
                  ((model.source state).initcall
                    localFn.params localFn.returns callArgs))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.call model prim (fuel + 1)
              callArgs (some generated)
              (some ordered.program.contract) state =
            .ok
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source state)).setStore (model.source state)),
                List.map (model.source stateAfterBody).lookup!
                  localFn.returns) := by
  rcases
      Raw.Source.AlphaRenamedLocalCallPreserved.toSolcYulOrderedProgram?_callable_entries
        hAlpha hConvert with
    ⟨generated, localFn, frontArgs, topFn, topYulBody, localYulBody,
      hTopMem, hOccurrence, hCalleeMem, hTopYul, hLocalYul,
      _hTopLookup, hCalleeLookup⟩
  refine
    ⟨generated, localFn, frontArgs, topFn, topYulBody, localYulBody,
      hTopMem, hOccurrence, hCalleeMem, hTopYul, hLocalYul,
      hCalleeLookup, ?_⟩
  intro σ model prim fuel callArgs state stateAfterBody hBody
  exact
    Yul.Source.Effectful.call_succ_of_explicit_parts
      model prim hCalleeLookup hBody

/-- Common lowered-Yul evidence for an alpha-renamed raw local call.

This bundles the generated callee entry, lowered argument list, exact Yul
lookup, and the lowerable/retained-stub occurrence route split.  Later
statement-context theorems can consume one evidence object instead of repeating
the same existential spine. -/
structure AlphaRenamedLocalCallYulEvidence
    (object : Frontend.Object)
    (ordered : Yul.OrderedProgram)
    (topName : Frontend.Name) where
  generated : Frontend.Name
  localFn : Frontend.FunctionDef
  frontArgs : List Frontend.Expr
  localYulBody : List Frontend.AstStmt
  yulArgs : List Frontend.AstExpr
  calleeMem : (generated, localFn) ∈ object.functions
  localYul :
    Frontend.Stmt.List.toYul? localFn.body = some localYulBody
  argsYul :
    Frontend.Expr.List.toYul? frontArgs = some yulArgs
  calleeLookup :
    ordered.program.contract.functions.lookup generated =
      some
        (EvmYul.Yul.Ast.FunctionDefinition.Def
          localFn.params localFn.returns localYulBody)
  routes :
    ((∃ (topFn : Frontend.FunctionDef)
        (topYulBody : List Frontend.AstStmt),
      (topName, topFn) ∈ object.functions ∧
        FrontendOccurrence.LowerableStmtListUserCall
          topFn.body generated frontArgs ∧
        Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
        YulOccurrence.StmtListUserCall
          topYulBody generated yulArgs ∧
        (topName,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            topFn.params topFn.returns topYulBody) ∈
          ordered.functionEntries) ∨
      ∃ (topFn : Frontend.FunctionDef)
        (stubName : Frontend.Name)
        (params returns : List Frontend.Name)
        (body : List Frontend.Stmt)
        (yulBody : List Frontend.AstStmt),
      (topName, topFn) ∈ object.functions ∧
        FrontendOccurrence.StubBodyStmtListUserCall
          topFn.body generated frontArgs ∧
        Frontend.Stmt.List.toYul? body = some yulBody ∧
        ordered.functionEntries.contains
          (stubName,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              params returns yulBody) = true ∧
        YulOccurrence.StmtListUserCall
          yulBody generated yulArgs)

/-- The source-facing alpha-preservation relation supplies the common lowered
Yul evidence used by all generated-call semantic context lemmas. -/
theorem alphaRenamedLocalCallPreserved_yulEvidence
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    Nonempty (AlphaRenamedLocalCallYulEvidence object ordered topName) := by
  rcases
      Raw.Source.AlphaRenamedLocalCallPreserved.toSolcYulOrderedProgram?_call_occurrence_routes_lookup
        hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes⟩
  exact
    ⟨{ generated := generated
       localFn := localFn
       frontArgs := frontArgs
       localYulBody := localYulBody
       yulArgs := yulArgs
       calleeMem := hCalleeMem
       localYul := hLocalYul
       argsYul := hArgsYul
       calleeLookup := hCalleeLookup
       routes := hRoutes }⟩

/-- Semantic call corollary that also exposes the concrete generated Yul call
occurrence route.

This packages the two frontend cases behind the source-facing
`AlphaRenamedLocalCallPreserved` relation: either the generated call occurs in
the lowered caller body, or it occurs in an emitted retained-stub function body.
Both routes share the same generated callee lookup used by the Yul call rule. -/
theorem alphaRenamedLocalCallPreserved_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {fuel : Nat} {callArgs : List Frontend.Word}
          {state stateAfterBody : σ},
          Yul.Source.Effectful.exec model prim fuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource state
                (EvmYul.Yul.State.mkOk
                  ((model.source state).initcall
                    localFn.params localFn.returns callArgs))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.call model prim (fuel + 1)
              callArgs (some generated)
              (some ordered.program.contract) state =
            .ok
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source state)).setStore (model.source state)),
                List.map (model.source stateAfterBody).lookup!
                  localFn.returns) := by
  rcases
      Raw.Source.AlphaRenamedLocalCallPreserved.toSolcYulOrderedProgram?_call_occurrence_routes_lookup
        hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim fuel callArgs state stateAfterBody hBody
  exact
    Yul.Source.Effectful.call_succ_of_explicit_parts
      model prim hCalleeLookup hBody

/-- Generated-call expression evaluation for an alpha-preserved raw local call.

This is the argument-evaluation step around the call rule: after the concrete
lowered Yul arguments evaluate, executing the generated callee body gives the
same result as evaluating the generated internal-call expression. -/
theorem alphaRenamedLocalCallPreserved_evalValues_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {state stateAfterArgs stateAfterBody : σ}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalValues model prim (bodyFuel + 2)
              (.Call (.inr generated) yulArgs)
              (some ordered.program.contract) state =
            .ok
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)),
                List.map (model.source stateAfterBody).lookup!
                  localFn.returns) := by
  rcases
      Raw.Source.AlphaRenamedLocalCallPreserved.toSolcYulOrderedProgram?_call_occurrence_routes_lookup
        hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel state stateAfterArgs stateAfterBody
    reversedValues hArgs hBody
  have hCall :
      Yul.Source.Effectful.call model prim (bodyFuel + 1)
          reversedValues.reverse (some generated)
          (some ordered.program.contract) stateAfterArgs =
        .ok
          (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)),
            List.map (model.source stateAfterBody).lookup!
              localFn.returns) :=
    Yul.Source.Effectful.call_succ_of_explicit_parts
      model prim hCalleeLookup hBody
  simp [Yul.Source.Effectful.evalValues, hArgs, hCall]

/-- Single-value evaluation of a generated alpha-renamed local call.

This is the condition-expression view of the generated-call theorem used by
`if` and `switch`: ordinary Yul `eval` observes the head of the returned value
list after generated arguments and the generated callee body execute. -/
theorem alphaRenamedLocalCallPreserved_eval_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {state stateAfterArgs stateAfterBody : σ}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.eval model prim (bodyFuel + 2)
              (.Call (.inr generated) yulArgs)
              (some ordered.program.contract) state =
            .ok
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)),
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head!) := by
  rcases
      Raw.Source.AlphaRenamedLocalCallPreserved.toSolcYulOrderedProgram?_call_occurrence_routes_lookup
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel state stateAfterArgs stateAfterBody
    reversedValues hArgs hBody
  have hCall :
      Yul.Source.Effectful.call model prim (bodyFuel + 1)
          reversedValues.reverse (some generated)
          (some ordered.program.contract) stateAfterArgs =
        .ok
          (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)),
            List.map (model.source stateAfterBody).lookup!
              localFn.returns) :=
    Yul.Source.Effectful.call_succ_of_explicit_parts
      model prim hCalleeLookup hBody
  exact Yul.Source.Effectful.eval_function_of_parts model prim hArgs hCall

/-- Outer-call argument evaluation for an alpha-renamed local call.

This lifts the single-value generated-call theorem through one surrounding Yul
call argument list, for both primitive calls and user-function calls.  The
argument order matches `evalValues`: right-side arguments are evaluated first,
then the focused generated call, then left-side arguments. -/
theorem alphaRenamedLocalCallPreserved_outerArg_evalValues_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          Yul.Source.Effectful.evalValues model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Call (.inl outerPrim)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              (some ordered.program.contract) state =
            .ok (final, outputs)) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          Yul.Source.Effectful.evalValues model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Call (.inr functionName)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              (some ordered.program.contract) state =
            .ok (final, outputs)) := by
  rcases alphaRenamedLocalCallPreserved_eval_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hEval⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues outputs hRight hArgs
      hBody hLeft hPrim
    have hFocus :
        Yul.Source.Effectful.eval model prim ((bodyFuel + 1) + 1)
            (.Call (.inr generated) yulArgs)
            (some ordered.program.contract) stateBeforeFocus =
          .ok
            (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs)),
              (List.map (model.source stateAfterBody).lookup!
                localFn.returns).head!) := by
      simpa [Nat.add_assoc] using hEval model prim hArgs hBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.evalValues_primitive_split_focus_of_parts
        model prim
        (tailFuel := bodyFuel + 1) (prim := outerPrim)
        (left := left) (right := right)
        (focus := .Call (.inr generated) yulArgs)
        (codeOverride := some ordered.program.contract)
        (state := state) (beforeFocus := stateBeforeFocus)
        (afterFocus :=
          model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs)))
        (stateAfterArgs := stateAfterOuterArgs)
        (final := final) (rightValues := rightValues)
        (leftValues := leftValues)
        (focusValue :=
          (List.map (model.source stateAfterBody).lookup!
            localFn.returns).head!)
        (outputs := outputs)
        (by omega) hRight hFocus hLeft hPrim
  · intro σ model prim bodyFuel functionName left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues outputs hRight hArgs
      hBody hLeft hCall
    have hFocus :
        Yul.Source.Effectful.eval model prim ((bodyFuel + 1) + 1)
            (.Call (.inr generated) yulArgs)
            (some ordered.program.contract) stateBeforeFocus =
          .ok
            (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs)),
              (List.map (model.source stateAfterBody).lookup!
                localFn.returns).head!) := by
      simpa [Nat.add_assoc] using hEval model prim hArgs hBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.evalValues_function_split_focus_of_parts
        model prim
        (tailFuel := bodyFuel + 1) (functionName := functionName)
        (left := left) (right := right)
        (focus := .Call (.inr generated) yulArgs)
        (codeOverride := some ordered.program.contract)
        (state := state) (beforeFocus := stateBeforeFocus)
        (afterFocus :=
          model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs)))
        (stateAfterArgs := stateAfterOuterArgs)
        (final := final) (rightValues := rightValues)
        (leftValues := leftValues)
        (focusValue :=
          (List.map (model.source stateAfterBody).lookup!
            localFn.returns).head!)
        (outputs := outputs)
        (by omega) hRight hFocus hLeft hCall

/-- Single-value evaluation for outer calls containing a generated call.

This is the condition-expression view of the outer-call argument theorem:
when the surrounding primitive or user-function call returns exactly one value,
ordinary Yul `eval` observes that value after the nested generated call has
executed. -/
theorem alphaRenamedLocalCallPreserved_outerArg_eval_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {value : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, [value]) →
          Yul.Source.Effectful.eval model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Call (.inl outerPrim)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              (some ordered.program.contract) state =
            .ok (final, value)) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {value : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, [value]) →
          Yul.Source.Effectful.eval model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Call (.inr functionName)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              (some ordered.program.contract) state =
            .ok (final, value)) := by
  rcases alphaRenamedLocalCallPreserved_outerArg_evalValues_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimOuter, hFunctionOuter⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues value hRight hArgs hBody
      hLeft hPrim
    exact
      Yul.Source.Effectful.eval_of_evalValues_singleton model prim
        (hPrimOuter model prim hRight hArgs hBody hLeft hPrim)
  · intro σ model prim bodyFuel functionName left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues value hRight hArgs hBody
      hLeft hCall
    exact
      Yul.Source.Effectful.eval_of_evalValues_singleton model prim
        (hFunctionOuter model prim hRight hArgs hBody hLeft hCall)

/-- If-condition execution for outer calls containing a generated call.

This lifts the outer-call single-value theorem through ordinary Yul `if`
semantics.  Both primitive and user-function outer calls are covered, and the
zero/nonzero branch split is kept explicit for later sequence/block composition. -/
theorem alphaRenamedLocalCallPreserved_ifCondition_outerArg_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {ifBody : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterCond : σ}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterCond, [condValue]) →
          condValue = EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.If
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                ifBody)
              (some ordered.program.contract) state =
            .ok stateAfterCond) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {ifBody : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterCond final : σ}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterCond, [condValue]) →
          condValue ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block ifBody)
              (some ordered.program.contract) stateAfterCond =
            .ok final →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.If
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                ifBody)
              (some ordered.program.contract) state =
            .ok final) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {ifBody : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterCond : σ}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterCond, [condValue]) →
          condValue = EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.If
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                ifBody)
              (some ordered.program.contract) state =
            .ok stateAfterCond) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {ifBody : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterCond final : σ}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterCond, [condValue]) →
          condValue ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block ifBody)
              (some ordered.program.contract) stateAfterCond =
            .ok final →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.If
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                ifBody)
              (some ordered.program.contract) state =
            .ok final) := by
  rcases alphaRenamedLocalCallPreserved_outerArg_eval_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimOuter, hFunctionOuter⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right ifBody state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterCond rightValues leftValues reversedValues condValue
      hRight hArgs hBody hLeft hPrim hZero
    have hEval := hPrimOuter model prim hRight hArgs hBody hLeft hPrim
    exact Yul.Source.Effectful.exec_if_false_of_eval model prim hEval hZero
  · intro σ model prim bodyFuel outerPrim left right ifBody state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterCond final rightValues leftValues reversedValues condValue
      hRight hArgs hBody hLeft hPrim hNonzero hIfBody
    have hEval := hPrimOuter model prim hRight hArgs hBody hLeft hPrim
    exact
      Yul.Source.Effectful.exec_if_true_of_eval model prim hEval hNonzero
        hIfBody
  · intro σ model prim bodyFuel functionName left right ifBody state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterCond rightValues leftValues reversedValues condValue
      hRight hArgs hBody hLeft hCall hZero
    have hEval := hFunctionOuter model prim hRight hArgs hBody hLeft hCall
    exact Yul.Source.Effectful.exec_if_false_of_eval model prim hEval hZero
  · intro σ model prim bodyFuel functionName left right ifBody state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterCond final rightValues leftValues reversedValues condValue
      hRight hArgs hBody hLeft hCall hNonzero hIfBody
    have hEval := hFunctionOuter model prim hRight hArgs hBody hLeft hCall
    exact
      Yul.Source.Effectful.exec_if_true_of_eval model prim hEval hNonzero
        hIfBody

/-- Switch-scrutinee execution for outer calls containing a generated call.

This is the switch sibling of the outer-call `if` theorem: after the surrounding
primitive or user-function call returns the scrutinee value, ordinary Yul
`switch` semantics executes the selected case/default body from that post-call
state. -/
theorem alphaRenamedLocalCallPreserved_switchScrutinee_outerArg_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterScrutinee final : σ}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {scrutineeValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterScrutinee, [scrutineeValue]) →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block
                (EvmYul.Yul.selectSwitchCase scrutineeValue defaultBody cases))
              (some ordered.program.contract) stateAfterScrutinee =
            .ok final →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.Switch
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                cases defaultBody)
              (some ordered.program.contract) state =
            .ok final) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterScrutinee final : σ}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {scrutineeValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterScrutinee, [scrutineeValue]) →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block
                (EvmYul.Yul.selectSwitchCase scrutineeValue defaultBody cases))
              (some ordered.program.contract) stateAfterScrutinee =
            .ok final →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.Switch
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                cases defaultBody)
              (some ordered.program.contract) state =
            .ok final := by
  rcases alphaRenamedLocalCallPreserved_outerArg_eval_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimOuter, hFunctionOuter⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right cases defaultBody state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterScrutinee final rightValues leftValues reversedValues
      scrutineeValue hRight hArgs hBody hLeft hPrim hSelected
    have hEval := hPrimOuter model prim hRight hArgs hBody hLeft hPrim
    exact Yul.Source.Effectful.exec_switch_of_eval model prim hEval hSelected
  · intro σ model prim bodyFuel functionName left right cases defaultBody state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterScrutinee final rightValues leftValues reversedValues
      scrutineeValue hRight hArgs hBody hLeft hCall hSelected
    have hEval := hFunctionOuter model prim hRight hArgs hBody hLeft hCall
    exact Yul.Source.Effectful.exec_switch_of_eval model prim hEval hSelected

/-- Sequence-head if-condition contexts for outer calls.

This lifts outer-call `if` condition execution through `execSeq`: after the
condition statement completes regularly, ordinary Yul sequence semantics
continues with the remaining statements. -/
theorem alphaRenamedLocalCallPreserved_ifCondition_outerArg_seqHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {ifBody rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterCond afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterCond, [condValue]) →
          condValue = EvmYul.UInt256.ofNat 0 →
          model.source stateAfterCond = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) stateAfterCond =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.If
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                ifBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {ifBody rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterCond afterIf afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterCond, [condValue]) →
          condValue ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block ifBody)
              (some ordered.program.contract) stateAfterCond =
            .ok afterIf →
          model.source afterIf = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) afterIf =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.If
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                ifBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {ifBody rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterCond afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterCond, [condValue]) →
          condValue = EvmYul.UInt256.ofNat 0 →
          model.source stateAfterCond = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) stateAfterCond =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.If
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                ifBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {ifBody rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterCond afterIf afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterCond, [condValue]) →
          condValue ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block ifBody)
              (some ordered.program.contract) stateAfterCond =
            .ok afterIf →
          model.source afterIf = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) afterIf =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.If
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                ifBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_ifCondition_outerArg_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimFalse, hPrimTrue, hFunctionFalse, hFunctionTrue⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right ifBody rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterCond afterRest shared vars rightValues leftValues
      reversedValues condValue hRight hArgs hBody hLeft hPrim hZero
      hSource hRest
    have hStmt :=
      hPrimFalse (ifBody := ifBody) model prim hRight hArgs hBody hLeft
        hPrim hZero
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel outerPrim left right ifBody rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterCond afterIf afterRest shared vars rightValues leftValues
      reversedValues condValue hRight hArgs hBody hLeft hPrim hNonzero
      hIfBody hSource hRest
    have hStmt :=
      hPrimTrue (ifBody := ifBody) model prim hRight hArgs hBody hLeft
        hPrim hNonzero hIfBody
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel functionName left right ifBody rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterCond afterRest shared vars rightValues leftValues
      reversedValues condValue hRight hArgs hBody hLeft hCall hZero
      hSource hRest
    have hStmt :=
      hFunctionFalse (ifBody := ifBody) model prim hRight hArgs hBody hLeft
        hCall hZero
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel functionName left right ifBody rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      stateAfterCond afterIf afterRest shared vars rightValues leftValues
      reversedValues condValue hRight hArgs hBody hLeft hCall hNonzero
      hIfBody hSource hRest
    have hStmt :=
      hFunctionTrue (ifBody := ifBody) model prim hRight hArgs hBody hLeft
        hCall hNonzero hIfBody
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest

/-- Sequence-head switch-scrutinee contexts for outer calls.

This lifts outer-call `switch` scrutinee execution through `execSeq`, exposing
the selected case/default body as a regular statement head for recursive
statement-list composition. -/
theorem alphaRenamedLocalCallPreserved_switchScrutinee_outerArg_seqHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterScrutinee afterSwitch
            afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {scrutineeValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterScrutinee, [scrutineeValue]) →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block
                (EvmYul.Yul.selectSwitchCase scrutineeValue defaultBody cases))
              (some ordered.program.contract) stateAfterScrutinee =
            .ok afterSwitch →
          model.source afterSwitch = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) afterSwitch =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.Switch
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                cases defaultBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs stateAfterScrutinee afterSwitch
            afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {scrutineeValue : Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterScrutinee, [scrutineeValue]) →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block
                (EvmYul.Yul.selectSwitchCase scrutineeValue defaultBody cases))
              (some ordered.program.contract) stateAfterScrutinee =
            .ok afterSwitch →
          model.source afterSwitch = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) afterSwitch =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.Switch
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))
                cases defaultBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_switchScrutinee_outerArg_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimSwitch, hFunctionSwitch⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right cases defaultBody rest
      state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterScrutinee afterSwitch afterRest shared
      vars rightValues leftValues reversedValues scrutineeValue hRight hArgs
      hBody hLeft hPrim hSelected hSource hRest
    have hStmt :=
      hPrimSwitch model prim hRight hArgs hBody hLeft hPrim hSelected
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel functionName left right cases defaultBody rest
      state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterScrutinee afterSwitch afterRest shared
      vars rightValues leftValues reversedValues scrutineeValue hRight hArgs
      hBody hLeft hCall hSelected hSource hRest
    have hStmt :=
      hFunctionSwitch model prim hRight hArgs hBody hLeft hCall hSelected
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest

/-- Prefix/tail switch-scrutinee contexts for outer calls.

This lifts the outer-call switch sequence-head theorem through an arbitrary
regularly executed prefix, exposing selected case/default tail-occurrence
bridges for recursive statement-list composition. -/
theorem alphaRenamedLocalCallPreserved_switchScrutinee_outerArg_seqPrefix_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs stateAfterScrutinee
            afterSwitch afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {scrutineeValue : Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterScrutinee, [scrutineeValue]) →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block
                (EvmYul.Yul.selectSwitchCase scrutineeValue defaultBody cases))
              (some ordered.program.contract) stateAfterScrutinee =
            .ok afterSwitch →
          model.source afterSwitch = .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) afterSwitch =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.Switch
                  (.Call (.inl outerPrim)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))
                  cases defaultBody) :: rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs stateAfterScrutinee
            afterSwitch afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {scrutineeValue : Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterScrutinee, [scrutineeValue]) →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block
                (EvmYul.Yul.selectSwitchCase scrutineeValue defaultBody cases))
              (some ordered.program.contract) stateAfterScrutinee =
            .ok afterSwitch →
          model.source afterSwitch = .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) afterSwitch =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.Switch
                  (.Call (.inr functionName)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))
                  cases defaultBody) :: rest))
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_switchScrutinee_outerArg_seqHead_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimSwitch, hFunctionSwitch⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right cases defaultBody pre rest
      state stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterScrutinee afterSwitch afterRest
      prefixShared stmtShared prefixVars stmtVars rightValues leftValues
      reversedValues scrutineeValue hPrefix hPrefixSource hRight hArgs hBody
      hLeft hPrim hSelected hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.Switch
              (.Call (.inl outerPrim)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              cases defaultBody) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hPrimSwitch model prim hRight hArgs hBody hLeft hPrim hSelected
        hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.Switch
            (.Call (.inl outerPrim)
              (left ++ (.Call (.inr generated) yulArgs) :: right))
            cases defaultBody) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel functionName left right cases defaultBody pre
      rest state stateBeforeCall stateBeforeFocus stateAfterArgs
      stateAfterBody stateAfterOuterArgs stateAfterScrutinee afterSwitch
      afterRest prefixShared stmtShared prefixVars stmtVars rightValues
      leftValues reversedValues scrutineeValue hPrefix hPrefixSource hRight
      hArgs hBody hLeft hCall hSelected hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.Switch
              (.Call (.inr functionName)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              cases defaultBody) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hFunctionSwitch model prim hRight hArgs hBody hLeft hCall hSelected
        hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.Switch
            (.Call (.inr functionName)
              (left ++ (.Call (.inr generated) yulArgs) :: right))
            cases defaultBody) :: rest)
        hPrefix hPrefixSource hSuffix

/-- Prefix/tail if-condition contexts for outer calls.

This lifts the outer-call if-condition sequence-head theorem through an
arbitrary regularly executed prefix, exposing zero and nonzero branch
tail-occurrence bridges for recursive statement-list composition. -/
theorem alphaRenamedLocalCallPreserved_ifCondition_outerArg_seqPrefix_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {ifBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs stateAfterCond afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterCond, [condValue]) →
          condValue = EvmYul.UInt256.ofNat 0 →
          model.source stateAfterCond = .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) stateAfterCond =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.If
                  (.Call (.inl outerPrim)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))
                  ifBody) :: rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {ifBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs stateAfterCond afterIf
            afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (stateAfterCond, [condValue]) →
          condValue ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block ifBody)
              (some ordered.program.contract) stateAfterCond =
            .ok afterIf →
          model.source afterIf = .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) afterIf =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.If
                  (.Call (.inl outerPrim)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))
                  ifBody) :: rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {ifBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs stateAfterCond afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterCond, [condValue]) →
          condValue = EvmYul.UInt256.ofNat 0 →
          model.source stateAfterCond = .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) stateAfterCond =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.If
                  (.Call (.inr functionName)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))
                  ifBody) :: rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {ifBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs stateAfterCond afterIf
            afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues : List Frontend.Word}
          {condValue : Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (stateAfterCond, [condValue]) →
          condValue ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.Block ifBody)
              (some ordered.program.contract) stateAfterCond =
            .ok afterIf →
          model.source afterIf = .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract) afterIf =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.If
                  (.Call (.inr functionName)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))
                  ifBody) :: rest))
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_ifCondition_outerArg_seqHead_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimFalse, hPrimTrue, hFunctionFalse, hFunctionTrue⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right ifBody pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterCond afterRest prefixShared stmtShared
      prefixVars stmtVars rightValues leftValues reversedValues condValue
      hPrefix hPrefixSource hRight hArgs hBody hLeft hPrim hZero
      hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.If
              (.Call (.inl outerPrim)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              ifBody) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hPrimFalse (ifBody := ifBody) model prim hRight hArgs hBody hLeft
        hPrim hZero hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.If
            (.Call (.inl outerPrim)
              (left ++ (.Call (.inr generated) yulArgs) :: right))
            ifBody) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel outerPrim left right ifBody pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterCond afterIf afterRest prefixShared
      stmtShared prefixVars stmtVars rightValues leftValues reversedValues
      condValue hPrefix hPrefixSource hRight hArgs hBody hLeft hPrim
      hNonzero hIfBody hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.If
              (.Call (.inl outerPrim)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              ifBody) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hPrimTrue (ifBody := ifBody) model prim hRight hArgs hBody hLeft
        hPrim hNonzero hIfBody hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.If
            (.Call (.inl outerPrim)
              (left ++ (.Call (.inr generated) yulArgs) :: right))
            ifBody) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel functionName left right ifBody pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterCond afterRest prefixShared stmtShared
      prefixVars stmtVars rightValues leftValues reversedValues condValue
      hPrefix hPrefixSource hRight hArgs hBody hLeft hCall hZero
      hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.If
              (.Call (.inr functionName)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              ifBody) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hFunctionFalse (ifBody := ifBody) model prim hRight hArgs hBody hLeft
        hCall hZero hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.If
            (.Call (.inr functionName)
              (left ++ (.Call (.inr generated) yulArgs) :: right))
            ifBody) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel functionName left right ifBody pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterCond afterIf afterRest prefixShared
      stmtShared prefixVars stmtVars rightValues leftValues reversedValues
      condValue hPrefix hPrefixSource hRight hArgs hBody hLeft hCall
      hNonzero hIfBody hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.If
              (.Call (.inr functionName)
                (left ++ (.Call (.inr generated) yulArgs) :: right))
              ifBody) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hFunctionTrue (ifBody := ifBody) model prim hRight hArgs hBody hLeft
        hCall hNonzero hIfBody hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.If
            (.Call (.inr functionName)
              (left ++ (.Call (.inr generated) yulArgs) :: right))
            ifBody) :: rest)
        hPrefix hPrefixSource hSuffix

/-- Assignment/declaration contexts for outer calls containing a generated call.

This composes the outer-call argument theorem with ordinary Yul
assignment/declaration writeback, covering the case where the alpha-renamed
generated call appears as an argument to the expression being assigned or
declared. -/
theorem alphaRenamedLocalCallPreserved_assignLet_outerArg_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          EvmYul.Yul.checkAssignment (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.Assign names
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right)))
              (some ordered.program.contract) state =
            .ok (model.multifill names final outputs)) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          EvmYul.Yul.checkAssignment (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.Assign names
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right)))
              (some ordered.program.contract) state =
            .ok (model.multifill names final outputs)) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          EvmYul.Yul.checkDeclaration (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.Let names
                (some
                  (.Call (.inl outerPrim)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))))
              (some ordered.program.contract) state =
            .ok (model.multifill names final outputs)) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          EvmYul.Yul.checkDeclaration (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          Yul.Source.Effectful.exec model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              (.Let names
                (some
                  (.Call (.inr functionName)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))))
              (some ordered.program.contract) state =
            .ok (model.multifill names final outputs)) := by
  rcases alphaRenamedLocalCallPreserved_outerArg_evalValues_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimOuter, hFunctionOuter⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim names left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues outputs hCheck hRight
      hArgs hBody hLeft hPrim
    exact
      Yul.Source.Effectful.exec_assign_of_evalValues model prim hCheck
        (hPrimOuter model prim hRight hArgs hBody hLeft hPrim)
  · intro σ model prim bodyFuel functionName names left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues outputs hCheck hRight
      hArgs hBody hLeft hCall
    exact
      Yul.Source.Effectful.exec_assign_of_evalValues model prim hCheck
        (hFunctionOuter model prim hRight hArgs hBody hLeft hCall)
  · intro σ model prim bodyFuel outerPrim names left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues outputs hCheck hRight
      hArgs hBody hLeft hPrim
    exact
      Yul.Source.Effectful.exec_let_some_of_evalValues model prim hCheck
        (hPrimOuter model prim hRight hArgs hBody hLeft hPrim)
  · intro σ model prim bodyFuel functionName names left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues outputs hCheck hRight
      hArgs hBody hLeft hCall
    exact
      Yul.Source.Effectful.exec_let_some_of_evalValues model prim hCheck
        (hFunctionOuter model prim hRight hArgs hBody hLeft hCall)

/-- Sequence-head assignment/declaration contexts for outer calls.

This lifts outer-call assignment and declaration writeback through `execSeq`:
after the statement completes regularly with `multifill`, ordinary Yul sequence
semantics continues with the remaining statements. -/
theorem alphaRenamedLocalCallPreserved_assignLet_outerArg_seqHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          EvmYul.Yul.checkAssignment (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          model.source (model.multifill names final outputs) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill names final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.Assign names
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
                rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          EvmYul.Yul.checkAssignment (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          model.source (model.multifill names final outputs) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill names final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.Assign names
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
                rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          EvmYul.Yul.checkDeclaration (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          model.source (model.multifill names final outputs) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill names final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.Let names
                (some
                  (.Call (.inl outerPrim)
                    (left ++ (.Call (.inr generated) yulArgs) :: right)))) ::
                rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          EvmYul.Yul.checkDeclaration (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          model.source (model.multifill names final outputs) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill names final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1)
              ((.Let names
                (some
                  (.Call (.inr functionName)
                    (left ++ (.Call (.inr generated) yulArgs) :: right)))) ::
                rest)
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_assignLet_outerArg_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hAssignPrim, hAssignFunction, hLetPrim, hLetFunction⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim names left right rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final afterRest shared vars rightValues leftValues reversedValues
      outputs hCheck hRight hArgs hBody hLeft hPrim hSource hRest
    have hStmt :=
      hAssignPrim model prim hCheck hRight hArgs hBody hLeft hPrim
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel functionName names left right rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final afterRest shared vars rightValues leftValues reversedValues
      outputs hCheck hRight hArgs hBody hLeft hCall hSource hRest
    have hStmt :=
      hAssignFunction model prim hCheck hRight hArgs hBody hLeft hCall
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel outerPrim names left right rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final afterRest shared vars rightValues leftValues reversedValues
      outputs hCheck hRight hArgs hBody hLeft hPrim hSource hRest
    have hStmt :=
      hLetPrim model prim hCheck hRight hArgs hBody hLeft hPrim
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel functionName names left right rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final afterRest shared vars rightValues leftValues reversedValues
      outputs hCheck hRight hArgs hBody hLeft hCall hSource hRest
    have hStmt :=
      hLetFunction model prim hCheck hRight hArgs hBody hLeft hCall
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest

/-- Prefix/tail assignment/declaration contexts for outer calls.

This lifts the outer-call assignment/declaration sequence-head theorem through
an arbitrary regularly executed prefix, exposing returned-value writeback
tail-occurrence bridges for recursive statement-list composition. -/
theorem alphaRenamedLocalCallPreserved_assignLet_outerArg_seqPrefix_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs final afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          EvmYul.Yul.checkAssignment
              (model.source stateBeforeCall) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          model.source (model.multifill names final outputs) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill names final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.Assign names
                  (.Call (.inl outerPrim)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
                  rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs final afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          EvmYul.Yul.checkAssignment
              (model.source stateBeforeCall) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          model.source (model.multifill names final outputs) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill names final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.Assign names
                  (.Call (.inr functionName)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
                  rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs final afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          EvmYul.Yul.checkDeclaration
              (model.source stateBeforeCall) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          model.source (model.multifill names final outputs) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill names final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.Let names
                  (some
                    (.Call (.inl outerPrim)
                      (left ++ (.Call (.inr generated) yulArgs) :: right)))) ::
                  rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {names : List Frontend.Name}
          {left right : List Frontend.AstExpr}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs final afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          EvmYul.Yul.checkDeclaration
              (model.source stateBeforeCall) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          model.source (model.multifill names final outputs) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill names final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + 1 + pre.length)
              (pre ++
                ((.Let names
                  (some
                    (.Call (.inr functionName)
                      (left ++ (.Call (.inr generated) yulArgs) :: right)))) ::
                  rest))
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_assignLet_outerArg_seqHead_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hAssignPrim, hAssignFunction, hLetPrim, hLetFunction⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim names left right pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final afterRest prefixShared stmtShared prefixVars
      stmtVars rightValues leftValues reversedValues outputs hPrefix
      hPrefixSource hCheck hRight hArgs hBody hLeft hPrim hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.Assign names
              (.Call (.inl outerPrim)
                (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
              rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hAssignPrim model prim hCheck hRight hArgs hBody hLeft hPrim
        hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.Assign names
            (.Call (.inl outerPrim)
              (left ++ (.Call (.inr generated) yulArgs) :: right))) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel functionName names left right pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final afterRest prefixShared stmtShared prefixVars
      stmtVars rightValues leftValues reversedValues outputs hPrefix
      hPrefixSource hCheck hRight hArgs hBody hLeft hCall hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.Assign names
              (.Call (.inr functionName)
                (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
              rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hAssignFunction model prim hCheck hRight hArgs hBody hLeft hCall
        hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.Assign names
            (.Call (.inr functionName)
              (left ++ (.Call (.inr generated) yulArgs) :: right))) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel outerPrim names left right pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final afterRest prefixShared stmtShared prefixVars
      stmtVars rightValues leftValues reversedValues outputs hPrefix
      hPrefixSource hCheck hRight hArgs hBody hLeft hPrim hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.Let names
              (some
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right)))) ::
              rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hLetPrim model prim hCheck hRight hArgs hBody hLeft hPrim
        hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.Let names
            (some
              (.Call (.inl outerPrim)
                (left ++ (.Call (.inr generated) yulArgs) :: right)))) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel functionName names left right pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final afterRest prefixShared stmtShared prefixVars
      stmtVars rightValues leftValues reversedValues outputs hPrefix
      hPrefixSource hCheck hRight hArgs hBody hLeft hCall hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1)
            ((.Let names
              (some
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right)))) ::
              rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hLetFunction model prim hCheck hRight hArgs hBody hLeft hCall
        hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.Let names
            (some
              (.Call (.inr functionName)
                (left ++ (.Call (.inr generated) yulArgs) :: right)))) :: rest)
        hPrefix hPrefixSource hSuffix

/-- Expression-statement contexts for outer calls containing a generated call.

This is the no-target sibling of the outer assignment/declaration theorem.  The
primitive outer-call branch reuses the ordinary `evalValues` expression-statement
rule; the user-function branch follows the Yul statement interpreter's extra
fuel step before the internal call. -/
theorem alphaRenamedLocalCallPreserved_exprStmt_outerArg_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              (.ExprStmtCall
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right)))
              (some ordered.program.contract) state =
            .ok (model.multifill [] final outputs)) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final : σ}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 1) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          Yul.Source.Effectful.exec model prim
              ((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2)
              (.ExprStmtCall
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right)))
              (some ordered.program.contract) state =
            .ok (model.multifill [] final outputs)) := by
  rcases alphaRenamedLocalCallPreserved_eval_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hEval⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues outputs hRight hArgs
      hBody hLeft hPrim
    have hFocus :
        Yul.Source.Effectful.eval model prim ((bodyFuel + 1) + 1)
            (.Call (.inr generated) yulArgs)
            (some ordered.program.contract) stateBeforeFocus =
          .ok
            (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs)),
              (List.map (model.source stateAfterBody).lookup!
                localFn.returns).head!) := by
      simpa [Nat.add_assoc] using hEval model prim hArgs hBody
    exact
      Yul.Source.Effectful.exec_expr_primitive_of_evalValues model prim
        (Yul.Source.Effectful.evalValues_primitive_split_focus_of_parts
          model prim
          (tailFuel := bodyFuel + 1) (prim := outerPrim)
          (left := left) (right := right)
          (focus := .Call (.inr generated) yulArgs)
          (codeOverride := some ordered.program.contract)
          (state := state) (beforeFocus := stateBeforeFocus)
          (afterFocus :=
            model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
          (stateAfterArgs := stateAfterOuterArgs)
          (final := final) (rightValues := rightValues)
          (leftValues := leftValues)
          (focusValue :=
            (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head!)
          (outputs := outputs)
          (by omega) hRight hFocus hLeft hPrim)
  · intro σ model prim bodyFuel functionName left right state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final rightValues leftValues reversedValues outputs hRight hArgs
      hBody hLeft hCall
    have hFocus :
        Yul.Source.Effectful.eval model prim ((bodyFuel + 1) + 1)
            (.Call (.inr generated) yulArgs)
            (some ordered.program.contract) stateBeforeFocus =
          .ok
            (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs)),
              (List.map (model.source stateAfterBody).lookup!
                localFn.returns).head!) := by
      simpa [Nat.add_assoc] using hEval model prim hArgs hBody
    have hOuterArgs :
        Yul.Source.Effectful.evalArgs model prim
            (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
            (left ++ (.Call (.inr generated) yulArgs) :: right).reverse
            (some ordered.program.contract) state =
          .ok
            (stateAfterOuterArgs,
              rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)) :=
      Yul.Source.Effectful.evalArgs_split_focus_of_parts
        model prim
        (tailFuel := bodyFuel + 1)
        (left := left) (right := right)
        (focus := .Call (.inr generated) yulArgs)
        (codeOverride := some ordered.program.contract)
        (source := state) (beforeFocus := stateBeforeFocus)
        (afterFocus :=
          model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs)))
        (final := stateAfterOuterArgs)
        (rightValues := rightValues)
        (leftValues := leftValues)
        (focusValue :=
          (List.map (model.source stateAfterBody).lookup!
            localFn.returns).head!)
        (by omega) hRight hFocus hLeft
    have hOuterArgs' :
        Yul.Source.Effectful.evalArgs model prim
            ((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 1)
            (left ++ (.Call (.inr generated) yulArgs) :: right).reverse
            (some ordered.program.contract) state =
            .ok
              (stateAfterOuterArgs,
                rightValues ++
                  ((List.map (model.source stateAfterBody).lookup!
                    localFn.returns).head! :: leftValues)) := by
      have hFuel :
          ((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 1) =
            (((bodyFuel + 1) + 2) + 2 * right.reverse.length) := by
        omega
      rw [hFuel]
      exact hOuterArgs
    exact
      Yul.Source.Effectful.exec_expr_function_of_parts model prim
        (fuel := (((bodyFuel + 1) + 1) + 2 * right.reverse.length))
        (functionName := functionName)
        (args := left ++ (.Call (.inr generated) yulArgs) :: right)
        (codeOverride := some ordered.program.contract)
        (state := state)
        (stateAfterArgs := stateAfterOuterArgs)
        (final := final)
        (reversedValues :=
          rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! :: leftValues))
        (values := outputs)
        hOuterArgs' hCall

/-- Sequence-head expression-statement contexts for outer calls.

This lifts the outer-call expression-statement theorem through `execSeq`: after
the outer call statement completes regularly, ordinary Yul sequence semantics
continues with the remaining statements. -/
theorem alphaRenamedLocalCallPreserved_exprStmt_outerArg_seqHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          model.source (model.multifill [] final outputs) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill [] final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
              ((.ExprStmtCall
                (.Call (.inl outerPrim)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
                rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {rest : List Frontend.AstStmt}
          {state stateBeforeFocus stateAfterArgs stateAfterBody
            stateAfterOuterArgs final afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) state =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 1) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          model.source (model.multifill [] final outputs) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim
              ((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2)
              rest
              (some ordered.program.contract)
              (model.multifill [] final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              (((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2) + 1)
              ((.ExprStmtCall
                (.Call (.inr functionName)
                  (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
                rest)
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_exprStmt_outerArg_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimStmt, hFunctionStmt⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final afterRest shared vars rightValues leftValues reversedValues
      outputs hRight hArgs hBody hLeft hPrim hSource hRest
    have hStmt := hPrimStmt model prim hRight hArgs hBody hLeft hPrim
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel functionName left right rest state
      stateBeforeFocus stateAfterArgs stateAfterBody stateAfterOuterArgs
      final afterRest shared vars rightValues leftValues reversedValues
      outputs hRight hArgs hBody hLeft hCall hSource hRest
    have hStmt := hFunctionStmt model prim hRight hArgs hBody hLeft hCall
    exact
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest

/-- Prefix/tail expression-statement contexts for outer calls.

This lifts the outer-call expression-statement sequence-head theorem through
an arbitrary regularly executed prefix, exposing the tail-occurrence bridge
needed by recursive statement-list composition. -/
theorem alphaRenamedLocalCallPreserved_exprStmt_outerArg_seqPrefix_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
          {left right : List Frontend.AstExpr}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs final afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              stateAfterOuterArgs outerPrim
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse =
            .ok (final, outputs) →
          model.source (model.multifill [] final outputs) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
              rest
              (some ordered.program.contract)
              (model.multifill [] final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
                + pre.length)
              (pre ++
                ((.ExprStmtCall
                  (.Call (.inl outerPrim)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
                  rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {functionName : Frontend.Name}
          {left right : List Frontend.AstExpr}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateBeforeFocus stateAfterArgs
            stateAfterBody stateAfterOuterArgs final afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {rightValues leftValues reversedValues outputs :
            List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2) + 1)
                + pre.length)
              pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim
              (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
              right.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateBeforeFocus, rightValues) →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeFocus =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              left.reverse
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok (stateAfterOuterArgs, leftValues) →
          Yul.Source.Effectful.call model prim
              (((bodyFuel + 1) + 1) + 2 * right.reverse.length)
              (rightValues ++
                ((List.map (model.source stateAfterBody).lookup!
                  localFn.returns).head! :: leftValues)).reverse
              (some functionName)
              (some ordered.program.contract) stateAfterOuterArgs =
            .ok (final, outputs) →
          model.source (model.multifill [] final outputs) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim
              ((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2)
              rest
              (some ordered.program.contract)
              (model.multifill [] final outputs) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2) + 1)
                + pre.length)
              (pre ++
                ((.ExprStmtCall
                  (.Call (.inr functionName)
                    (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
                  rest))
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_exprStmt_outerArg_seqHead_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hPrimSeq, hFunctionSeq⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel outerPrim left right pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final afterRest prefixShared stmtShared prefixVars
      stmtVars rightValues leftValues reversedValues outputs hPrefix
      hPrefixSource hRight hArgs hBody hLeft hPrim hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
            ((.ExprStmtCall
              (.Call (.inl outerPrim)
                (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
              rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hPrimSeq model prim hRight hArgs hBody hLeft hPrim hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1))
        (pre := pre)
        (suffix :=
          (.ExprStmtCall
            (.Call (.inl outerPrim)
              (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
            rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel functionName left right pre rest state
      stateBeforeCall stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final afterRest prefixShared stmtShared prefixVars
      stmtVars rightValues leftValues reversedValues outputs hPrefix
      hPrefixSource hRight hArgs hBody hLeft hCall hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim
            (((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2) + 1)
            ((.ExprStmtCall
              (.Call (.inr functionName)
                (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
              rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hFunctionSeq model prim hRight hArgs hBody hLeft hCall hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel :=
          (((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2) + 1))
        (pre := pre)
        (suffix :=
          (.ExprStmtCall
            (.Call (.inr functionName)
              (left ++ (.Call (.inr generated) yulArgs) :: right))) ::
            rest)
        hPrefix hPrefixSource hSuffix

/-- If-condition execution for a generated alpha-renamed local call.

This is the direct statement-context wrapper around the single-value `eval`
view: after the generated call returns its head value, ordinary Yul `if`
semantics either skips the body on zero or executes the selected body from the
post-call state. -/
theorem alphaRenamedLocalCallPreserved_ifCondition_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {ifBody : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody : σ}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! = EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim (bodyFuel + 3)
              (.If (.Call (.inr generated) yulArgs) ifBody)
              (some ordered.program.contract) state =
            .ok
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {ifBody : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody final : σ}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim (bodyFuel + 2)
              (.Block ifBody)
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs))) =
            .ok final →
          Yul.Source.Effectful.exec model prim (bodyFuel + 3)
              (.If (.Call (.inr generated) yulArgs) ifBody)
              (some ordered.program.contract) state =
            .ok final := by
  rcases alphaRenamedLocalCallPreserved_eval_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hEval⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel ifBody state stateAfterArgs
      stateAfterBody reversedValues hArgs hBody hZero
    have hEvalCall := hEval model prim hArgs hBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.exec_if_false_of_eval
        model prim hEvalCall hZero
  · intro σ model prim bodyFuel ifBody state stateAfterArgs
      stateAfterBody final reversedValues hArgs hBody hNonzero hIfBody
    have hEvalCall := hEval model prim hArgs hBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.exec_if_true_of_eval
        model prim hEvalCall hNonzero hIfBody

/-- Switch-scrutinee execution for a generated alpha-renamed local call.

After the generated call returns its head value, ordinary Yul `switch`
semantics selects the matching case/default body and executes it from the
post-call state. -/
theorem alphaRenamedLocalCallPreserved_switchScrutinee_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody final : σ}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.exec model prim (bodyFuel + 2)
              (.Block
                (EvmYul.Yul.selectSwitchCase
                  (List.map (model.source stateAfterBody).lookup!
                    localFn.returns).head!
                  defaultBody cases))
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs))) =
            .ok final →
          Yul.Source.Effectful.exec model prim (bodyFuel + 3)
              (.Switch (.Call (.inr generated) yulArgs) cases defaultBody)
              (some ordered.program.contract) state =
            .ok final := by
  rcases alphaRenamedLocalCallPreserved_eval_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hEval⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel cases defaultBody state stateAfterArgs
    stateAfterBody final reversedValues hArgs hBody hSelected
  have hEvalCall := hEval model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.exec_switch_of_eval
      model prim hEvalCall hSelected

/-- Block-head if-condition context for generated calls.

This lifts the direct generated-call `if` condition theorem through the head
of a surrounding Yul block, leaving the remaining statement sequence as the
next compositional premise. -/
theorem alphaRenamedLocalCallPreserved_ifCondition_blockHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {ifBody rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! = EvmYul.UInt256.ofNat 0 →
          model.source
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok afterRest →
          Yul.Source.Effectful.exec model prim (bodyFuel + 5)
              (.Block ((.If (.Call (.inr generated) yulArgs) ifBody) ::
                rest))
              (some ordered.program.contract) state =
            .ok
              (model.withSource afterRest
                ((model.source afterRest).restrictStoreTo
                  (model.source state).store))) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {ifBody rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterIf afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim (bodyFuel + 2)
              (.Block ifBody)
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs))) =
            .ok afterIf →
          model.source afterIf = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract) afterIf =
            .ok afterRest →
          Yul.Source.Effectful.exec model prim (bodyFuel + 5)
              (.Block ((.If (.Call (.inr generated) yulArgs) ifBody) ::
                rest))
              (some ordered.program.contract) state =
            .ok
              (model.withSource afterRest
                ((model.source afterRest).restrictStoreTo
                  (model.source state).store)) := by
  rcases alphaRenamedLocalCallPreserved_ifCondition_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hIfFalse, hIfTrue⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel ifBody rest state stateAfterArgs
      stateAfterBody afterRest shared vars reversedValues
      hArgs hBody hZero hSource hRest
    have hStmt := hIfFalse (ifBody := ifBody) model prim hArgs hBody hZero
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.exec_block_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel ifBody rest state stateAfterArgs
      stateAfterBody afterIf afterRest shared vars reversedValues
      hArgs hBody hNonzero hIfBody hSource hRest
    have hStmt := hIfTrue (ifBody := ifBody) model prim hArgs hBody
      hNonzero hIfBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.exec_block_cons_of_regular
        model prim hStmt hSource hRest

/-- Block-head switch-scrutinee context for generated calls.

This lifts the direct generated-call `switch` scrutinee theorem through the
head of a surrounding Yul block, leaving the remaining statement sequence as
the next compositional premise. -/
theorem alphaRenamedLocalCallPreserved_switchScrutinee_blockHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterSwitch afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.exec model prim (bodyFuel + 2)
              (.Block
                (EvmYul.Yul.selectSwitchCase
                  (List.map (model.source stateAfterBody).lookup!
                    localFn.returns).head!
                  defaultBody cases))
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs))) =
            .ok afterSwitch →
          model.source afterSwitch = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract) afterSwitch =
            .ok afterRest →
          Yul.Source.Effectful.exec model prim (bodyFuel + 5)
              (.Block
                ((.Switch (.Call (.inr generated) yulArgs) cases
                  defaultBody) :: rest))
              (some ordered.program.contract) state =
            .ok
              (model.withSource afterRest
                ((model.source afterRest).restrictStoreTo
                  (model.source state).store)) := by
  rcases alphaRenamedLocalCallPreserved_switchScrutinee_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hSwitch⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel cases defaultBody rest state stateAfterArgs
    stateAfterBody afterSwitch afterRest shared vars reversedValues
    hArgs hBody hSelected hSource hRest
  have hStmt := hSwitch (cases := cases) (defaultBody := defaultBody)
    model prim hArgs hBody hSelected
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.exec_block_cons_of_regular
      model prim hStmt hSource hRest

/-- Sequence-head if-condition context for generated calls.

This is the statement-list form of the generated-call `if` condition theorem:
after the branch statement completes regularly, ordinary Yul sequence semantics
continues with the remaining statements. -/
theorem alphaRenamedLocalCallPreserved_ifCondition_seqHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {ifBody rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! = EvmYul.UInt256.ofNat 0 →
          model.source
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
              ((.If (.Call (.inr generated) yulArgs) ifBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {ifBody rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterIf afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim (bodyFuel + 2)
              (.Block ifBody)
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs))) =
            .ok afterIf →
          model.source afterIf = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract) afterIf =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
              ((.If (.Call (.inr generated) yulArgs) ifBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_ifCondition_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hIfFalse, hIfTrue⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel ifBody rest state stateAfterArgs
      stateAfterBody afterRest shared vars reversedValues
      hArgs hBody hZero hSource hRest
    have hStmt := hIfFalse (ifBody := ifBody) model prim hArgs hBody hZero
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel ifBody rest state stateAfterArgs
      stateAfterBody afterIf afterRest shared vars reversedValues
      hArgs hBody hNonzero hIfBody hSource hRest
    have hStmt := hIfTrue (ifBody := ifBody) model prim hArgs hBody
      hNonzero hIfBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest

/-- Prefix/tail if-condition context for generated calls.

This lifts the `if` condition sequence-head theorem through an arbitrary
regularly executed prefix, exposing both zero and nonzero branch shapes for
tail-occurrence composition. -/
theorem alphaRenamedLocalCallPreserved_ifCondition_seqPrefix_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {ifBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateAfterArgs stateAfterBody afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length) pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! = EvmYul.UInt256.ofNat 0 →
          model.source
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                (((model.source stateAfterBody).reviveJump.overwrite?
                    (model.source stateAfterArgs)).setStore
                      (model.source stateAfterArgs))) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length)
              (pre ++ ((.If (.Call (.inr generated) yulArgs) ifBody) ::
                rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {ifBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateAfterArgs stateAfterBody afterIf
            afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length) pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          (List.map (model.source stateAfterBody).lookup!
              localFn.returns).head! ≠ EvmYul.UInt256.ofNat 0 →
          Yul.Source.Effectful.exec model prim (bodyFuel + 2)
              (.Block ifBody)
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs))) =
            .ok afterIf →
          model.source afterIf = .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract) afterIf =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length)
              (pre ++ ((.If (.Call (.inr generated) yulArgs) ifBody) ::
                rest))
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_ifCondition_seqHead_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hIfFalse, hIfTrue⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel ifBody pre rest state stateBeforeCall
      stateAfterArgs stateAfterBody afterRest prefixShared stmtShared
      prefixVars stmtVars reversedValues hPrefix hPrefixSource hArgs hBody
      hZero hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
            ((.If (.Call (.inr generated) yulArgs) ifBody) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hIfFalse model prim hArgs hBody hZero hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel := bodyFuel + 4) (pre := pre)
        (suffix := (.If (.Call (.inr generated) yulArgs) ifBody) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel ifBody pre rest state stateBeforeCall
      stateAfterArgs stateAfterBody afterIf afterRest prefixShared stmtShared
      prefixVars stmtVars reversedValues hPrefix hPrefixSource hArgs hBody
      hNonzero hIfBody hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
            ((.If (.Call (.inr generated) yulArgs) ifBody) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hIfTrue model prim hArgs hBody hNonzero hIfBody hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel := bodyFuel + 4) (pre := pre)
        (suffix := (.If (.Call (.inr generated) yulArgs) ifBody) :: rest)
        hPrefix hPrefixSource hSuffix

/-- Sequence-head switch-scrutinee context for generated calls.

This is the statement-list form of the generated-call `switch` scrutinee
theorem: after the selected switch body completes regularly, ordinary Yul
sequence semantics continues with the remaining statements. -/
theorem alphaRenamedLocalCallPreserved_switchScrutinee_seqHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterSwitch afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.exec model prim (bodyFuel + 2)
              (.Block
                (EvmYul.Yul.selectSwitchCase
                  (List.map (model.source stateAfterBody).lookup!
                    localFn.returns).head!
                  defaultBody cases))
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs))) =
            .ok afterSwitch →
          model.source afterSwitch = .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract) afterSwitch =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
              ((.Switch (.Call (.inr generated) yulArgs) cases
                defaultBody) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_switchScrutinee_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hSwitch⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel cases defaultBody rest state stateAfterArgs
    stateAfterBody afterSwitch afterRest shared vars reversedValues
    hArgs hBody hSelected hSource hRest
  have hStmt := hSwitch (cases := cases) (defaultBody := defaultBody)
    model prim hArgs hBody hSelected
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt hSource hRest

/-- Prefix/tail switch-scrutinee context for generated calls.

This lifts the switch sequence-head theorem through an arbitrary regularly
executed prefix, exposing the selected-body shape for tail-occurrence
composition. -/
theorem alphaRenamedLocalCallPreserved_switchScrutinee_seqPrefix_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {cases : List (Frontend.Word × List Frontend.AstStmt)}
          {defaultBody pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateAfterArgs stateAfterBody afterSwitch
            afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length) pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.exec model prim (bodyFuel + 2)
              (.Block
                (EvmYul.Yul.selectSwitchCase
                  (List.map (model.source stateAfterBody).lookup!
                    localFn.returns).head!
                  defaultBody cases))
              (some ordered.program.contract)
              (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs))) =
            .ok afterSwitch →
          model.source afterSwitch = .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract) afterSwitch =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length)
              (pre ++ ((.Switch (.Call (.inr generated) yulArgs) cases
                defaultBody) :: rest))
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_switchScrutinee_seqHead_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hSwitch⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel cases defaultBody pre rest state
    stateBeforeCall stateAfterArgs stateAfterBody afterSwitch afterRest
    prefixShared stmtShared prefixVars stmtVars reversedValues
    hPrefix hPrefixSource hArgs hBody hSelected hStmtSource hRest
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
          ((.Switch (.Call (.inr generated) yulArgs) cases defaultBody) ::
            rest)
          (some ordered.program.contract) stateBeforeCall =
        .ok afterRest :=
    hSwitch model prim hArgs hBody hSelected hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := bodyFuel + 4) (pre := pre)
      (suffix :=
        (.Switch (.Call (.inr generated) yulArgs) cases defaultBody) :: rest)
      hPrefix hPrefixSource hSuffix

/-- Caller statement writeback for generated assignment/declaration calls.

Once the generated call expression evaluates, ordinary Yul statement semantics
performs the checked assignment or declaration writeback with `multifill`.
This covers the two caller-context writeback cases that bind returned values;
expression statements are the zero-target specialization handled by the same
call/evaluation boundary. -/
theorem alphaRenamedLocalCallPreserved_assignLet_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {names : List Frontend.Name}
          {state stateAfterArgs stateAfterBody : σ}
          {reversedValues : List Frontend.Word},
          EvmYul.Yul.checkAssignment (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.exec model prim (bodyFuel + 3)
              (.Assign names (.Call (.inr generated) yulArgs))
              (some ordered.program.contract) state =
            .ok
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns))) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {names : List Frontend.Name}
          {state stateAfterArgs stateAfterBody : σ}
          {reversedValues : List Frontend.Word},
          EvmYul.Yul.checkDeclaration (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.exec model prim (bodyFuel + 3)
              (.Let names (some (.Call (.inr generated) yulArgs)))
              (some ordered.program.contract) state =
            .ok
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) := by
  rcases alphaRenamedLocalCallPreserved_evalValues_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hEval⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel names state stateAfterArgs stateAfterBody
      reversedValues hCheck hArgs hBody
    exact
      Yul.Source.Effectful.exec_assign_of_evalValues model prim hCheck
        (hEval model prim hArgs hBody)
  · intro σ model prim bodyFuel names state stateAfterArgs stateAfterBody
      reversedValues hCheck hArgs hBody
    exact
      Yul.Source.Effectful.exec_let_some_of_evalValues model prim hCheck
        (hEval model prim hArgs hBody)

/-- Sequence-head assignment/declaration contexts for generated calls.

This is the statement-list form of the assignment/declaration generated-call
theorem: after the returned-value writeback statement completes regularly,
ordinary Yul sequence semantics continues with the remaining statements. -/
theorem alphaRenamedLocalCallPreserved_assignLet_seqHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {names : List Frontend.Name}
          {rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          EvmYul.Yul.checkAssignment (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
              ((.Assign names (.Call (.inr generated) yulArgs)) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {names : List Frontend.Name}
          {rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          EvmYul.Yul.checkDeclaration (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
              ((.Let names (some (.Call (.inr generated) yulArgs))) ::
                rest)
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_assignLet_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hAssign, hLet⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel names rest state stateAfterArgs stateAfterBody
      afterRest shared vars reversedValues hCheck hArgs hBody hSource hRest
    have hStmt := hAssign model prim hCheck hArgs hBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel names rest state stateAfterArgs stateAfterBody
      afterRest shared vars reversedValues hCheck hArgs hBody hSource hRest
    have hStmt := hLet model prim hCheck hArgs hBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.execSeq_cons_of_regular
        model prim hStmt hSource hRest

/-- Prefix/tail assignment/declaration contexts for generated calls.

This lifts the assignment/declaration sequence-head theorem through an
arbitrary regularly executed prefix, giving the returned-value sibling of the
expression-statement tail-occurrence bridge. -/
theorem alphaRenamedLocalCallPreserved_assignLet_seqPrefix_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {names : List Frontend.Name}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateAfterArgs stateAfterBody afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length) pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          EvmYul.Yul.checkAssignment
              (model.source stateBeforeCall) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length)
              (pre ++ ((.Assign names (.Call (.inr generated) yulArgs)) ::
                rest))
              (some ordered.program.contract) state =
            .ok afterRest) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {names : List Frontend.Name}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateAfterArgs stateAfterBody afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length) pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          EvmYul.Yul.checkDeclaration
              (model.source stateBeforeCall) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length)
              (pre ++
                ((.Let names (some (.Call (.inr generated) yulArgs))) ::
                  rest))
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_assignLet_seqHead_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hAssign, hLet⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel names pre rest state stateBeforeCall
      stateAfterArgs stateAfterBody afterRest prefixShared stmtShared
      prefixVars stmtVars reversedValues hPrefix hPrefixSource hCheck
      hArgs hBody hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
            ((.Assign names (.Call (.inr generated) yulArgs)) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hAssign model prim hCheck hArgs hBody hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel := bodyFuel + 4) (pre := pre)
        (suffix := (.Assign names (.Call (.inr generated) yulArgs)) :: rest)
        hPrefix hPrefixSource hSuffix
  · intro σ model prim bodyFuel names pre rest state stateBeforeCall
      stateAfterArgs stateAfterBody afterRest prefixShared stmtShared
      prefixVars stmtVars reversedValues hPrefix hPrefixSource hCheck
      hArgs hBody hStmtSource hRest
    have hSuffix :
        Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
            ((.Let names (some (.Call (.inr generated) yulArgs))) :: rest)
            (some ordered.program.contract) stateBeforeCall =
          .ok afterRest :=
      hLet model prim hCheck hArgs hBody hStmtSource hRest
    exact
      Yul.Source.Effectful.execSeq_append_of_regular_prefix
        model prim
        (fuel := bodyFuel + 4) (pre := pre)
        (suffix :=
          (.Let names (some (.Call (.inr generated) yulArgs))) :: rest)
        hPrefix hPrefixSource hSuffix

/-- Block-head assignment/declaration contexts for generated calls.

This lifts the direct assignment/declaration generated-call theorem through the
head of a surrounding Yul block, leaving the remaining statement sequence as
the next compositional premise. -/
theorem alphaRenamedLocalCallPreserved_assignLet_blockHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        (∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {names : List Frontend.Name}
          {rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          EvmYul.Yul.checkAssignment (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.exec model prim (bodyFuel + 5)
              (.Block
                ((.Assign names (.Call (.inr generated) yulArgs)) :: rest))
              (some ordered.program.contract) state =
            .ok
              (model.withSource afterRest
                ((model.source afterRest).restrictStoreTo
                  (model.source state).store))) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat} {names : List Frontend.Name}
          {rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          EvmYul.Yul.checkDeclaration (model.source state) names = .ok () →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill names
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.exec model prim (bodyFuel + 5)
              (.Block
                ((.Let names (some (.Call (.inr generated) yulArgs))) ::
                  rest))
              (some ordered.program.contract) state =
            .ok
              (model.withSource afterRest
                ((model.source afterRest).restrictStoreTo
                  (model.source state).store)) := by
  rcases alphaRenamedLocalCallPreserved_assignLet_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hAssign, hLet⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_, ?_⟩
  · intro σ model prim bodyFuel names rest state stateAfterArgs stateAfterBody
      afterRest shared vars reversedValues hCheck hArgs hBody hSource hRest
    have hStmt := hAssign model prim hCheck hArgs hBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.exec_block_cons_of_regular
        model prim hStmt hSource hRest
  · intro σ model prim bodyFuel names rest state stateAfterArgs stateAfterBody
      afterRest shared vars reversedValues hCheck hArgs hBody hSource hRest
    have hStmt := hLet model prim hCheck hArgs hBody
    simpa [Nat.add_assoc] using
      Yul.Source.Effectful.exec_block_cons_of_regular
        model prim hStmt hSource hRest

/-- Caller expression-statement context for generated calls.

This is the no-target sibling of the assignment/declaration writeback theorem:
after generated arguments evaluate and the generated callee body executes, the
ordinary Yul expression-statement rule performs empty-target `multifill`. -/
theorem alphaRenamedLocalCallPreserved_exprStmt_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {state stateAfterArgs stateAfterBody : σ}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 2)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          Yul.Source.Effectful.exec model prim (bodyFuel + 3)
              (.ExprStmtCall (.Call (.inr generated) yulArgs))
              (some ordered.program.contract) state =
            .ok
              (model.multifill []
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) := by
  rcases alphaRenamedLocalCallPreserved_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hCall⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel state stateAfterArgs stateAfterBody
    reversedValues hArgs hBody
  exact
    Yul.Source.Effectful.exec_expr_function_of_parts model prim hArgs
      (hCall model prim hBody)

/-- Sequence-head expression-statement context for generated calls.

This is the statement-list form of the expression-statement generated-call
theorem: after the call statement completes regularly, ordinary Yul sequence
semantics continues with the remaining statements. -/
theorem alphaRenamedLocalCallPreserved_exprStmt_seqHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 2)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill []
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill []
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
              ((.ExprStmtCall (.Call (.inr generated) yulArgs)) :: rest)
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_exprStmt_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hExprStmt⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel rest state stateAfterArgs stateAfterBody
    afterRest shared vars reversedValues hArgs hBody hSource hRest
  have hStmt := hExprStmt model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt hSource hRest

/-- Prefix/tail expression-statement context for generated calls.

This lifts the expression-statement sequence-head theorem through an arbitrary
regularly executed prefix, exposing the reusable tail-occurrence shape for
recursive statement-list composition. -/
theorem alphaRenamedLocalCallPreserved_exprStmt_seqPrefix_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {pre rest : List Frontend.AstStmt}
          {state stateBeforeCall stateAfterArgs stateAfterBody afterRest : σ}
          {prefixShared stmtShared : EvmYul.SharedState .Yul}
          {prefixVars stmtVars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length) pre
              (some ordered.program.contract) state =
            .ok stateBeforeCall →
          model.source stateBeforeCall = .Ok prefixShared prefixVars →
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 2)
              yulArgs.reverse
              (some ordered.program.contract) stateBeforeCall =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill []
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok stmtShared stmtVars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill []
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.execSeq model prim
              ((bodyFuel + 4) + pre.length)
              (pre ++ ((.ExprStmtCall (.Call (.inr generated) yulArgs)) ::
                rest))
              (some ordered.program.contract) state =
            .ok afterRest := by
  rcases alphaRenamedLocalCallPreserved_exprStmt_seqHead_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hSeqHead⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel pre rest state stateBeforeCall stateAfterArgs
    stateAfterBody afterRest prefixShared stmtShared prefixVars stmtVars
    reversedValues hPrefix hPrefixSource hArgs hBody hStmtSource hRest
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
          ((.ExprStmtCall (.Call (.inr generated) yulArgs)) :: rest)
          (some ordered.program.contract) stateBeforeCall =
        .ok afterRest :=
    hSeqHead model prim hArgs hBody hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := bodyFuel + 4) (pre := pre)
      (suffix := (.ExprStmtCall (.Call (.inr generated) yulArgs)) :: rest)
      hPrefix hPrefixSource hSuffix

/-- Block-head expression-statement context for generated calls.

This lifts the direct expression-statement generated-call theorem through the
head of a surrounding Yul block, leaving the remaining statement sequence as
the next compositional premise. -/
theorem alphaRenamedLocalCallPreserved_exprStmt_blockHead_call_occurrence_routes_succ
    {topBody : List Raw.Stmt}
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName name : Frontend.Name}
    {localParams localReturns : List Frontend.Name}
    {localBody : List Raw.Stmt}
    {args : List Raw.Expr}
    (hAlpha :
      Raw.Source.AlphaRenamedLocalCallPreserved
        topBody object.functions topName name
          localParams localReturns localBody args)
    (hConvert :
      object.toSolcYulOrderedProgram? = some ordered) :
    ∃ (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (frontArgs : List Frontend.Expr)
        (localYulBody : List Frontend.AstStmt)
        (yulArgs : List Frontend.AstExpr),
      (generated, localFn) ∈ object.functions ∧
        Frontend.Stmt.List.toYul? localFn.body = some localYulBody ∧
        Frontend.Expr.List.toYul? frontArgs = some yulArgs ∧
        ordered.program.contract.functions.lookup generated =
          some
            (EvmYul.Yul.Ast.FunctionDefinition.Def
              localFn.params localFn.returns localYulBody) ∧
        ((∃ (topFn : Frontend.FunctionDef)
            (topYulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.LowerableStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? topFn.body = some topYulBody ∧
            YulOccurrence.StmtListUserCall
              topYulBody generated yulArgs ∧
            (topName,
              EvmYul.Yul.Ast.FunctionDefinition.Def
                topFn.params topFn.returns topYulBody) ∈
              ordered.functionEntries) ∨
          ∃ (topFn : Frontend.FunctionDef)
            (stubName : Frontend.Name)
            (params returns : List Frontend.Name)
            (body : List Frontend.Stmt)
            (yulBody : List Frontend.AstStmt),
          (topName, topFn) ∈ object.functions ∧
            FrontendOccurrence.StubBodyStmtListUserCall
              topFn.body generated frontArgs ∧
            Frontend.Stmt.List.toYul? body = some yulBody ∧
            ordered.functionEntries.contains
              (stubName,
                EvmYul.Yul.Ast.FunctionDefinition.Def
                  params returns yulBody) = true ∧
            YulOccurrence.StmtListUserCall
              yulBody generated yulArgs) ∧
        ∀ {σ : Type}
          (model : Yul.Source.Effectful.StateModel σ)
          (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
          {bodyFuel : Nat}
          {rest : List Frontend.AstStmt}
          {state stateAfterArgs stateAfterBody afterRest : σ}
          {shared : EvmYul.SharedState .Yul}
          {vars : EvmYul.Yul.VarStore}
          {reversedValues : List Frontend.Word},
          Yul.Source.Effectful.evalArgs model prim (bodyFuel + 2)
              yulArgs.reverse
              (some ordered.program.contract) state =
            .ok (stateAfterArgs, reversedValues) →
          Yul.Source.Effectful.exec model prim bodyFuel
              (.Block localYulBody)
              (some ordered.program.contract)
              (model.withSource stateAfterArgs
                (EvmYul.Yul.State.mkOk
                  ((model.source stateAfterArgs).initcall
                    localFn.params localFn.returns
                    reversedValues.reverse))) =
            .ok stateAfterBody →
          model.source
              (model.multifill []
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .Ok shared vars →
          Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
              rest
              (some ordered.program.contract)
              (model.multifill []
                (model.withSource stateAfterBody
                  (((model.source stateAfterBody).reviveJump.overwrite?
                      (model.source stateAfterArgs)).setStore
                        (model.source stateAfterArgs)))
                (List.map (model.source stateAfterBody).lookup!
                  localFn.returns)) =
            .ok afterRest →
          Yul.Source.Effectful.exec model prim (bodyFuel + 5)
              (.Block
                ((.ExprStmtCall (.Call (.inr generated) yulArgs)) :: rest))
              (some ordered.program.contract) state =
            .ok
              (model.withSource afterRest
                ((model.source afterRest).restrictStoreTo
                  (model.source state).store)) := by
  rcases alphaRenamedLocalCallPreserved_exprStmt_call_occurrence_routes_succ
      hAlpha hConvert with
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup, hRoutes,
      hExprStmt⟩
  refine
    ⟨generated, localFn, frontArgs, localYulBody, yulArgs,
      hCalleeMem, hLocalYul, hArgsYul, hCalleeLookup,
      hRoutes, ?_⟩
  intro σ model prim bodyFuel rest state stateAfterArgs stateAfterBody
    afterRest shared vars reversedValues hArgs hBody hSource hRest
  have hStmt := hExprStmt model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.exec_block_cons_of_regular
      model prim hStmt hSource hRest

/-- Finished-source corollary for the raw-solc theorem. This retains the
unconditional theorem as primary; the source-finished premise is only used to
upgrade finite-prefix preservation to a full open-world relation. -/
theorem optimizedRawSolcIrToRawBytecodeFinished
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
    (hCompile :
      compileArtifactFromRawSolcIr? rawJson selection = some artifact)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (Yul.EndToEnd.installedSourceState artifact baseSource))) :
    ∃ structuredFuel,
      Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_decoded hCompile with
    ⟨program, linkerSymbols, _hDecode, _hLinker, hProgramCompile⟩
  exact
    Yul.EndToEnd.optimizedSolcYulToRawBytecodeFinished
      (object := program.object)
      (linkerSymbols := linkerSymbols)
      (artifact := artifact)
      (sourceFuel := sourceFuel)
      (baseSource := baseSource)
      hProgramCompile
      hFinished

/-- Finished-source raw-solc corollary with source-local nested-call evidence. -/
theorem optimizedRawSolcIrToRawBytecodeFinished_sourceLocalFunction_noShadow
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
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
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (Yul.EndToEnd.installedSourceState artifact baseSource))) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word))
        (generated : Frontend.Name)
        (localFn : Frontend.FunctionDef)
        (args' : List Frontend.Expr)
        (topFn : Frontend.FunctionDef)
        (structuredFuel : Nat),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact ∧
        (topName, topFn) ∈ program.object.functions ∧
        FrontendOccurrence.StmtListUserCall topFn.body generated args' ∧
        (generated, localFn) ∈ program.object.functions ∧
        Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_sourceLocalFunction_noShadow_program_entries
      hCompile hParse hSelected hCode hTop hLocal hOccurs with
    ⟨program, linkerSymbols, generated, localFn, args', topFn,
      hDecode, hLinker, hProgramCompile, hValid, hTopEntry,
      hOccurrence, hLocalEntry⟩
  rcases optimizedRawSolcIrToRawBytecodeFinished
      (sourceFuel := sourceFuel) (baseSource := baseSource)
      hCompile hFinished with
    ⟨structuredFuel, hAccepted, hRel⟩
  exact
    ⟨program, linkerSymbols, generated, localFn, args', topFn,
      structuredFuel, hDecode, hLinker, hProgramCompile, hValid,
      hTopEntry, hOccurrence, hLocalEntry, hAccepted, hRel⟩

/-- Finished-source raw-solc corollary with source-facing alpha-preservation
for nested local calls. -/
theorem optimizedRawSolcIrToRawBytecodeFinished_sourceLocalFunction_noShadow_alphaPreserved
    {rawJson : String} {selection : Selection}
    {artifact : Frontend.Program.Artifact}
    {sourceFuel : Nat}
    {baseSource : EvmYul.SharedState .Yul}
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
    (hOccurs : Raw.Source.NoShadowStmtListCall topBody name args)
    (hFinished : Simulation.Interaction.AllDone
      Yul.FunctionsInteractionProgram.SourceFinished
      (Yul.InteractionSemantics.exec (sourceFuel + 1)
        (.Block [artifact.codeArtifact.ordered.program.contract.dispatcher])
        (some artifact.codeArtifact.ordered.program.contract)
        (Yul.EndToEnd.installedSourceState artifact baseSource))) :
    ∃ (program : Frontend.Program)
        (linkerSymbols : List (Frontend.Name × Frontend.Word))
        (structuredFuel : Nat),
      decodeAndElaborateSolcIr? rawJson selection = some program ∧
        decodeLinkerSymbols? rawJson selection = some linkerSymbols ∧
        program.compileArtifactWithLinkerSymbols? linkerSymbols =
          some artifact ∧
        Frontend.Object.VerifiedStackObjectArtifact.ValidFor
          linkerSymbols program.object artifact ∧
        Raw.Source.AlphaRenamedLocalCallPreserved
          topBody program.object.functions topName name
            localParams localReturns localBody args ∧
        Assembly.Accepted artifact.codeArtifact.compiled.certified.target ∧
        Simulation.Interaction.Rel
          (Compiler.OpenInteractionComposition.VerifiedStackObjectPrefixDoneRel
            artifact)
          (Yul.InteractionSemantics.exec (sourceFuel + 1)
            (.Block
              [artifact.codeArtifact.ordered.program.contract.dispatcher])
            (some artifact.codeArtifact.ordered.program.contract)
            (Yul.EndToEnd.installedSourceState artifact baseSource))
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList artifact.image.bytes)
            (2 *
              ((Structured.InteractionStaticCost.blockBudget
                  artifact.codeArtifact.compiled.expressions.toStructured
                  structuredFuel
                  artifact.codeArtifact.compiled.expressions.toStructured.body +
                    1) *
                TypedCfg.InteractionSemantics.CompiledProgram.fuelBudget
                  artifact.codeArtifact.compiled.cfg))
            { (Yul.EndToEnd.initialExpressionsState artifact baseSource).evm with
              pc := EvmYul.UInt256.ofNat 0 }) := by
  rcases compileArtifactFromRawSolcIr?_sourceLocalFunction_noShadow_alphaPreserved
      hCompile hParse hSelected hCode hTop hLocal hOccurs with
    ⟨program, linkerSymbols, hDecode, hLinker, hProgramCompile,
      hValid, hAlpha⟩
  rcases optimizedRawSolcIrToRawBytecodeFinished
      (sourceFuel := sourceFuel) (baseSource := baseSource)
      hCompile hFinished with
    ⟨structuredFuel, hAccepted, hRel⟩
  exact
    ⟨program, linkerSymbols, structuredFuel, hDecode, hLinker,
      hProgramCompile, hValid, hAlpha, hAccepted, hRel⟩

end RawAst
end Solidity
end EvmCompiler
