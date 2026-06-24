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
