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
