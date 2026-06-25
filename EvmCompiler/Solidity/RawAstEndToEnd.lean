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

namespace AlphaRenamedLocalCallYulEvidence

/-- The bundled generated callee lookup is enough to run the ordinary Yul
call rule once the generated callee body has executed from the initialized
call frame. -/
theorem call_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {fuel : Nat} {callArgs : List Frontend.Word}
    {state stateAfterBody : σ}
    (hBody :
      Yul.Source.Effectful.exec model prim fuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource state
            (EvmYul.Yul.State.mkOk
              ((model.source state).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                callArgs))) =
        .ok stateAfterBody) :
    Yul.Source.Effectful.call model prim (fuel + 1)
        callArgs (some hEvidence.generated)
        (some ordered.program.contract) state =
      .ok
        (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source state)).setStore (model.source state)),
          List.map (model.source stateAfterBody).lookup!
            hEvidence.localFn.returns) :=
  Yul.Source.Effectful.call_succ_of_explicit_parts
    model prim hEvidence.calleeLookup hBody

/-- Multi-value evaluation of the generated alpha-renamed call from the bundled
Yul evidence. -/
theorem evalValues_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {state stateAfterArgs stateAfterBody : σ}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody) :
    Yul.Source.Effectful.evalValues model prim (bodyFuel + 2)
        (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
        (some ordered.program.contract) state =
      .ok
        (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs)),
          List.map (model.source stateAfterBody).lookup!
            hEvidence.localFn.returns) := by
  have hCall :
      Yul.Source.Effectful.call model prim (bodyFuel + 1)
          reversedValues.reverse (some hEvidence.generated)
          (some ordered.program.contract) stateAfterArgs =
        .ok
          (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)),
            List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns) :=
    hEvidence.call_succ model prim hBody
  simp [Yul.Source.Effectful.evalValues, hArgs, hCall]

/-- Single-value evaluation view of the generated alpha-renamed call from the
bundled Yul evidence. -/
theorem eval_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {state stateAfterArgs stateAfterBody : σ}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody) :
    Yul.Source.Effectful.eval model prim (bodyFuel + 2)
        (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
        (some ordered.program.contract) state =
      .ok
        (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs)),
          (List.map (model.source stateAfterBody).lookup!
            hEvidence.localFn.returns).head!) := by
  have hCall :
      Yul.Source.Effectful.call model prim (bodyFuel + 1)
          reversedValues.reverse (some hEvidence.generated)
          (some ordered.program.contract) stateAfterArgs =
        .ok
          (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)),
            List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns) :=
    hEvidence.call_succ model prim hBody
  exact Yul.Source.Effectful.eval_function_of_parts model prim hArgs hCall

/-- Runtime semantics for one focused generated local-call occurrence.

The static `AlphaRenamedLocalCallYulEvidence` identifies the generated callee
and lowered Yul arguments.  This structure packages the dynamic part shared by
all statement contexts: Yul argument evaluation, generated callee-body
execution, revived/store-restored return state, return values, and the
resulting `evalValues`/single-value `eval` facts for the generated call
expression. -/
structure GeneratedCallRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (bodyFuel : Nat)
    (state : σ) where
  stateAfterArgs : σ
  stateAfterBody : σ
  reversedValues : List Frontend.Word
  hArgs :
    Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
        hEvidence.yulArgs.reverse
        (some ordered.program.contract) state =
      .ok (stateAfterArgs, reversedValues)
  hBody :
    Yul.Source.Effectful.exec model prim bodyFuel
        (.Block hEvidence.localYulBody)
        (some ordered.program.contract)
        (model.withSource stateAfterArgs
          (EvmYul.Yul.State.mkOk
            ((model.source stateAfterArgs).initcall
              hEvidence.localFn.params hEvidence.localFn.returns
              reversedValues.reverse))) =
      .ok stateAfterBody
  postState : σ
  returns : List Frontend.Word
  postState_eq :
    postState =
      model.withSource stateAfterBody
        (((model.source stateAfterBody).reviveJump.overwrite?
            (model.source stateAfterArgs)).setStore
              (model.source stateAfterArgs))
  returns_eq :
    returns =
      List.map (model.source stateAfterBody).lookup!
        hEvidence.localFn.returns
  hEvalValues :
    Yul.Source.Effectful.evalValues model prim (bodyFuel + 2)
        (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
        (some ordered.program.contract) state =
      .ok (postState, returns)
  hEval :
    Yul.Source.Effectful.eval model prim (bodyFuel + 2)
        (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
        (some ordered.program.contract) state =
      .ok (postState, returns.head!)

def generatedCallRun_of_parts
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {state stateAfterArgs stateAfterBody : σ}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody) :
    GeneratedCallRun hEvidence model prim bodyFuel state := by
  let postState :=
    model.withSource stateAfterBody
      (((model.source stateAfterBody).reviveJump.overwrite?
          (model.source stateAfterArgs)).setStore
            (model.source stateAfterArgs))
  let returns :=
    List.map (model.source stateAfterBody).lookup!
      hEvidence.localFn.returns
  refine
    { stateAfterArgs := stateAfterArgs
      stateAfterBody := stateAfterBody
      reversedValues := reversedValues
      hArgs := hArgs
      hBody := hBody
      postState := postState
      returns := returns
      postState_eq := rfl
      returns_eq := rfl
      hEvalValues := ?_
      hEval := ?_ }
  · dsimp [postState, returns]
    exact hEvidence.evalValues_succ model prim hArgs hBody
  · dsimp [postState, returns]
    exact hEvidence.eval_succ model prim hArgs hBody

/-- Generic execution relation for a direct incoming statement whose focused
expression is the generated local call.

This relation is deliberately statement-shaped rather than theorem-name-shaped:
assignment, declaration, expression statement, `if`, and `switch` consume the
same focused-call facts through the ordinary Yul semantic constructors. -/
inductive DirectIncomingStmtRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (state : σ) :
    Nat → Frontend.AstStmt → σ → Prop where
  | assign
      {fuel : Nat} {names : List Frontend.Name}
      {stateAfterValue : σ} {values : List Frontend.Word}
      (hCheck :
        EvmYul.Yul.checkAssignment (model.source state) names = .ok ())
      (hValues :
        Yul.Source.Effectful.evalValues model prim fuel
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
            (some ordered.program.contract) state =
          .ok (stateAfterValue, values)) :
      DirectIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.Assign names
          (.Call (.inr hEvidence.generated) hEvidence.yulArgs))
        (model.multifill names stateAfterValue values)
  | letValue
      {fuel : Nat} {names : List Frontend.Name}
      {stateAfterValue : σ} {values : List Frontend.Word}
      (hCheck :
        EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
      (hValues :
        Yul.Source.Effectful.evalValues model prim fuel
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
            (some ordered.program.contract) state =
          .ok (stateAfterValue, values)) :
      DirectIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.Let names
          (some (.Call (.inr hEvidence.generated) hEvidence.yulArgs)))
        (model.multifill names stateAfterValue values)
  | exprStmt
      {fuel : Nat}
      {stateAfterArgs final : σ}
      {reversedValues values : List Frontend.Word}
      (hArgs :
        Yul.Source.Effectful.evalArgs model prim (fuel + 1)
            hEvidence.yulArgs.reverse
            (some ordered.program.contract) state =
          .ok (stateAfterArgs, reversedValues))
      (hCall :
        Yul.Source.Effectful.call model prim fuel
            reversedValues.reverse
            (some hEvidence.generated)
            (some ordered.program.contract) stateAfterArgs =
          .ok (final, values)) :
      DirectIncomingStmtRun hEvidence model prim state (fuel + 2)
        (.ExprStmtCall
          (.Call (.inr hEvidence.generated) hEvidence.yulArgs))
        (model.multifill [] final values)
  | ifFalse
      {fuel : Nat} {ifBody : List Frontend.AstStmt}
      {stateAfterCond : σ} {condValue : Frontend.Word}
      (hEval :
        Yul.Source.Effectful.eval model prim fuel
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
            (some ordered.program.contract) state =
          .ok (stateAfterCond, condValue))
      (hZero : condValue = EvmYul.UInt256.ofNat 0) :
      DirectIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ifBody)
        stateAfterCond
  | ifTrue
      {fuel : Nat} {ifBody : List Frontend.AstStmt}
      {stateAfterCond final : σ} {condValue : Frontend.Word}
      (hEval :
        Yul.Source.Effectful.eval model prim fuel
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
            (some ordered.program.contract) state =
          .ok (stateAfterCond, condValue))
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      (hIfBody :
        Yul.Source.Effectful.exec model prim fuel
            (.Block ifBody)
            (some ordered.program.contract) stateAfterCond =
          .ok final) :
      DirectIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ifBody)
        final
  | switch
      {fuel : Nat}
      {cases : List (Frontend.Word × List Frontend.AstStmt)}
      {defaultBody : List Frontend.AstStmt}
      {stateAfterScrutinee final : σ} {scrutineeValue : Frontend.Word}
      (hEval :
        Yul.Source.Effectful.eval model prim fuel
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
            (some ordered.program.contract) state =
          .ok (stateAfterScrutinee, scrutineeValue))
      (hSelected :
        Yul.Source.Effectful.exec model prim fuel
            (.Block
              (EvmYul.Yul.selectSwitchCase
                scrutineeValue defaultBody cases))
            (some ordered.program.contract) stateAfterScrutinee =
          .ok final) :
      DirectIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.Switch (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          cases defaultBody)
        final

namespace DirectIncomingStmtRun

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      DirectIncomingStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    Yul.Source.Effectful.exec model prim fuel stmt
        (some ordered.program.contract) state =
      .ok afterStmt := by
  cases hRun with
  | assign hCheck hValues =>
      exact
        Yul.Source.Effectful.exec_assign_of_evalValues
          model prim hCheck hValues
  | letValue hCheck hValues =>
      exact
        Yul.Source.Effectful.exec_let_some_of_evalValues
          model prim hCheck hValues
  | exprStmt hArgs hCall =>
      exact
        Yul.Source.Effectful.exec_expr_function_of_parts
          model prim hArgs hCall
  | ifFalse hEval hZero =>
      exact
        Yul.Source.Effectful.exec_if_false_of_eval
          model prim hEval hZero
  | ifTrue hEval hNonzero hIfBody =>
      exact
        Yul.Source.Effectful.exec_if_true_of_eval
          model prim hEval hNonzero hIfBody
  | switch hEval hSelected =>
      exact
        Yul.Source.Effectful.exec_switch_of_eval
          model prim hEval hSelected

theorem execSeq_prefix
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {pre rest : List Frontend.AstStmt}
    {stmt : Frontend.AstStmt}
    {state stateBeforeStmt afterStmt afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((prefixFuel + 1) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeStmt)
    (hPrefixSource :
      model.source stateBeforeStmt = .Ok prefixShared prefixVars)
    (hStmt :
      DirectIncomingStmtRun hEvidence model prim stateBeforeStmt
        prefixFuel stmt afterStmt)
    (hStmtSource :
      model.source afterStmt = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim prefixFuel rest
          (some ordered.program.contract) afterStmt =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) (pre ++ stmt :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (prefixFuel + 1)
          (stmt :: rest)
          (some ordered.program.contract) stateBeforeStmt =
        .ok afterRest :=
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt.exec hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := prefixFuel + 1) (pre := pre)
      (suffix := stmt :: rest)
      hPrefix hPrefixSource hSuffix

theorem execSeq_of_split
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts pre rest : List Frontend.AstStmt}
    {stmt : Frontend.AstStmt}
    {state stateBeforeStmt afterStmt afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    (hSplit : stmts = pre ++ stmt :: rest)
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((prefixFuel + 1) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeStmt)
    (hPrefixSource :
      model.source stateBeforeStmt = .Ok prefixShared prefixVars)
    (hStmt :
      DirectIncomingStmtRun hEvidence model prim stateBeforeStmt
        prefixFuel stmt afterStmt)
    (hStmtSource :
      model.source afterStmt = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim prefixFuel rest
          (some ordered.program.contract) afterStmt =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) stmts
        (some ordered.program.contract) state =
      .ok afterRest := by
  subst stmts
  exact execSeq_prefix hPrefix hPrefixSource hStmt hStmtSource hRest

end DirectIncomingStmtRun

/-- Statement-list execution package for the direct incoming occurrence branch.

This ties the syntactic split from `YulOccurrence.StmtListUserCall` to the
generic direct-statement semantic interface.  The focused statement is known to
contain the generated call directly in its incoming expression field; all
statement-specific runtime facts are carried by `DirectIncomingStmtRun`.
-/
structure DirectStmtListOccurrenceRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (stmts : List Frontend.AstStmt)
    (state : σ) where
  pre : List Frontend.AstStmt
  stmt : Frontend.AstStmt
  rest : List Frontend.AstStmt
  hSplit : stmts = pre ++ stmt :: rest
  hDirect :
    YulOccurrence.StmtIncomingUserCall.Direct
      stmt hEvidence.generated hEvidence.yulArgs
  stateBeforeStmt : σ
  afterStmt : σ
  afterRest : σ
  prefixShared : EvmYul.SharedState .Yul
  prefixVars : EvmYul.Yul.VarStore
  stmtShared : EvmYul.SharedState .Yul
  stmtVars : EvmYul.Yul.VarStore
  hPrefix :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) pre
        (some ordered.program.contract) state =
      .ok stateBeforeStmt
  hPrefixSource :
    model.source stateBeforeStmt = .Ok prefixShared prefixVars
  hStmt :
    DirectIncomingStmtRun hEvidence model prim stateBeforeStmt
      prefixFuel stmt afterStmt
  hStmtSource :
    model.source afterStmt = .Ok stmtShared stmtVars
  hRest :
    Yul.Source.Effectful.execSeq model prim prefixFuel rest
        (some ordered.program.contract) afterStmt =
      .ok afterRest

namespace DirectStmtListOccurrenceRun

theorem execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      DirectStmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + hRun.pre.length) stmts
        (some ordered.program.contract) state =
      .ok hRun.afterRest :=
  DirectIncomingStmtRun.execSeq_of_split
    hRun.hSplit hRun.hPrefix hRun.hPrefixSource hRun.hStmt
    hRun.hStmtSource hRun.hRest

end DirectStmtListOccurrenceRun

/-- Runtime semantics for a focused expression that contains the generated
local call.

For the direct focus this is built from `GeneratedCallRun`; for nested
arguments it is the recursive expression-level interface consumed by the outer
call semantics below. -/
structure FocusedExprRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (fuel : Nat)
    (focus : Frontend.AstExpr)
    (state : σ) where
  hOccurrence :
    YulOccurrence.UserCall focus hEvidence.generated hEvidence.yulArgs
  afterFocus : σ
  value : Frontend.Word
  hEval :
    Yul.Source.Effectful.eval model prim fuel focus
        (some ordered.program.contract) state =
      .ok (afterFocus, value)

namespace FocusedExprRun

def ofGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    (hRun : GeneratedCallRun hEvidence model prim bodyFuel state) :
    FocusedExprRun hEvidence model prim (bodyFuel + 2)
      (.Call (.inr hEvidence.generated) hEvidence.yulArgs) state where
  hOccurrence := YulOccurrence.UserCall.here
  afterFocus := hRun.postState
  value := hRun.returns.head!
  hEval := hRun.hEval

end FocusedExprRun

/-- Value-producing semantics for a surrounding call whose focused argument
contains the generated local call.

This packages the common right-to-left Yul argument evaluation order: evaluate
the right suffix, evaluate the focused occurrence, evaluate the left prefix,
then run the surrounding primitive or user-function callee. -/
inductive OuterArgCallRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (state : σ) :
    Nat → Sum (EvmYul.Operation .Yul) Frontend.Name →
      List Frontend.AstExpr → Frontend.AstExpr →
      List Frontend.AstExpr → σ → List Frontend.Word → Prop where
  | primitive
      {tailFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {stateBeforeFocus stateAfterOuterArgs final : σ}
      {rightValues leftValues outputs : List Frontend.Word}
      (hTailFuel : 1 ≤ tailFuel)
      (hRight :
        Yul.Source.Effectful.evalArgs model prim
            ((tailFuel + 2) + 2 * right.reverse.length)
            right.reverse
            (some ordered.program.contract) state =
          .ok (stateBeforeFocus, rightValues))
      (hFocus :
        FocusedExprRun hEvidence model prim (tailFuel + 1)
          focus stateBeforeFocus)
      (hLeft :
        Yul.Source.Effectful.evalArgs model prim tailFuel
            left.reverse
            (some ordered.program.contract) hFocus.afterFocus =
          .ok (stateAfterOuterArgs, leftValues))
      (hPrim :
        prim.eval ((tailFuel + 2) + 2 * right.reverse.length)
            stateAfterOuterArgs outerPrim
            (rightValues ++ hFocus.value :: leftValues).reverse =
          .ok (final, outputs)) :
      OuterArgCallRun hEvidence model prim state
        (((tailFuel + 2) + 2 * right.reverse.length) + 1)
        (.inl outerPrim) left focus right final outputs
  | function
      {tailFuel : Nat} {functionName : Frontend.Name}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {stateBeforeFocus stateAfterOuterArgs final : σ}
      {rightValues leftValues outputs : List Frontend.Word}
      (hTailFuel : 1 ≤ tailFuel)
      (hRight :
        Yul.Source.Effectful.evalArgs model prim
            ((tailFuel + 2) + 2 * right.reverse.length)
            right.reverse
            (some ordered.program.contract) state =
          .ok (stateBeforeFocus, rightValues))
      (hFocus :
        FocusedExprRun hEvidence model prim (tailFuel + 1)
          focus stateBeforeFocus)
      (hLeft :
        Yul.Source.Effectful.evalArgs model prim tailFuel
            left.reverse
            (some ordered.program.contract) hFocus.afterFocus =
          .ok (stateAfterOuterArgs, leftValues))
      (hCall :
        Yul.Source.Effectful.call model prim
            ((tailFuel + 2) + 2 * right.reverse.length)
            (rightValues ++ hFocus.value :: leftValues).reverse
            (some functionName)
            (some ordered.program.contract) stateAfterOuterArgs =
          .ok (final, outputs)) :
      OuterArgCallRun hEvidence model prim state
        (((tailFuel + 2) + 2 * right.reverse.length) + 1)
        (.inr functionName) left focus right final outputs

namespace OuterArgCallRun

theorem evalValues
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
    {left right : List Frontend.AstExpr}
    {focus : Frontend.AstExpr}
    {final : σ}
    {outputs : List Frontend.Word}
    (hRun :
      OuterArgCallRun hEvidence model prim state
        fuel callee left focus right final outputs) :
    Yul.Source.Effectful.evalValues model prim fuel
        (.Call callee (left ++ focus :: right))
        (some ordered.program.contract) state =
      .ok (final, outputs) := by
  cases hRun with
  | primitive hTailFuel hRight hFocus hLeft hPrim =>
      exact
        Yul.Source.Effectful.evalValues_primitive_split_focus_of_parts
          model prim
          hTailFuel
          hRight hFocus.hEval hLeft hPrim
  | function hTailFuel hRight hFocus hLeft hCall =>
      exact
        Yul.Source.Effectful.evalValues_function_split_focus_of_parts
          model prim
          hTailFuel
          hRight hFocus.hEval hLeft hCall

theorem eval_of_singleton
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
    {left right : List Frontend.AstExpr}
    {focus : Frontend.AstExpr}
    {final : σ}
    {value : Frontend.Word}
    (hRun :
      OuterArgCallRun hEvidence model prim state
        fuel callee left focus right final [value]) :
    Yul.Source.Effectful.eval model prim fuel
        (.Call callee (left ++ focus :: right))
        (some ordered.program.contract) state =
      .ok (final, value) :=
  Yul.Source.Effectful.eval_of_evalValues_singleton model prim
    hRun.evalValues

end OuterArgCallRun

/-- No-target expression-statement execution for a surrounding call whose
focused argument contains the generated local call. -/
inductive OuterArgExprStmtRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (state : σ) :
    Nat → Sum (EvmYul.Operation .Yul) Frontend.Name →
      List Frontend.AstExpr → Frontend.AstExpr →
      List Frontend.AstExpr → σ → Prop where
  | primitive
      {fuel : Nat} {outerPrim : EvmYul.Operation .Yul}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {final : σ} {outputs : List Frontend.Word}
      (hOuter :
        OuterArgCallRun hEvidence model prim state
          fuel (.inl outerPrim) left focus right final outputs) :
      OuterArgExprStmtRun hEvidence model prim state
        fuel (.inl outerPrim) left focus right
        (model.multifill [] final outputs)
  | function
      {fuel : Nat} {functionName : Frontend.Name}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {stateAfterOuterArgs final : σ}
      {reversedValues outputs : List Frontend.Word}
      (hArgs :
        Yul.Source.Effectful.evalArgs model prim
            (fuel + 1) (left ++ focus :: right).reverse
            (some ordered.program.contract) state =
          .ok (stateAfterOuterArgs, reversedValues))
      (hCall :
        Yul.Source.Effectful.call model prim
            fuel reversedValues.reverse
            (some functionName)
            (some ordered.program.contract) stateAfterOuterArgs =
          .ok (final, outputs)) :
      OuterArgExprStmtRun hEvidence model prim state
        (fuel + 2)
        (.inr functionName) left focus right
        (model.multifill [] final outputs)

namespace OuterArgExprStmtRun

theorem function_of_split
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {tailFuel : Nat} {functionName : Frontend.Name}
    {left right : List Frontend.AstExpr}
    {focus : Frontend.AstExpr}
    {stateBeforeFocus stateAfterOuterArgs final : σ}
    {rightValues leftValues outputs : List Frontend.Word}
    (hTailFuel : 1 ≤ tailFuel)
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          ((tailFuel + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hFocus :
      FocusedExprRun hEvidence model prim (tailFuel + 1)
        focus stateBeforeFocus)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim tailFuel
          left.reverse
          (some ordered.program.contract) hFocus.afterFocus =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          ((tailFuel + 1) + 2 * right.reverse.length)
          (rightValues ++ hFocus.value :: leftValues).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (final, outputs)) :
    OuterArgExprStmtRun hEvidence model prim state
      (((tailFuel + 1) + 2 * right.reverse.length) + 2)
      (.inr functionName) left focus right
      (model.multifill [] final outputs) := by
  have hOuterArgs :
      Yul.Source.Effectful.evalArgs model prim
          ((tailFuel + 2) + 2 * right.reverse.length)
          (left ++ focus :: right).reverse
          (some ordered.program.contract) state =
        .ok
          (stateAfterOuterArgs,
            rightValues ++ hFocus.value :: leftValues) :=
    Yul.Source.Effectful.evalArgs_split_focus_of_parts
      model prim hTailFuel hRight hFocus.hEval hLeft
  have hOuterArgs' :
      Yul.Source.Effectful.evalArgs model prim
          (((tailFuel + 1) + 2 * right.reverse.length) + 1)
          (left ++ focus :: right).reverse
          (some ordered.program.contract) state =
        .ok
          (stateAfterOuterArgs,
            rightValues ++ hFocus.value :: leftValues) := by
    have hFuel :
        (((tailFuel + 1) + 2 * right.reverse.length) + 1) =
          ((tailFuel + 2) + 2 * right.reverse.length) := by
      omega
    rw [hFuel]
    exact hOuterArgs
  exact
    .function hOuterArgs' hCall

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
    {left right : List Frontend.AstExpr}
    {focus : Frontend.AstExpr}
    {afterStmt : σ}
    (hRun :
      OuterArgExprStmtRun hEvidence model prim state
        fuel callee left focus right afterStmt) :
    Yul.Source.Effectful.exec model prim fuel
        (.ExprStmtCall (.Call callee (left ++ focus :: right)))
        (some ordered.program.contract) state =
      .ok afterStmt := by
  cases hRun with
  | primitive hOuter =>
      exact
        Yul.Source.Effectful.exec_expr_primitive_of_evalValues
          model prim hOuter.evalValues
  | function hArgs hCall =>
      exact
        Yul.Source.Effectful.exec_expr_function_of_parts
          model prim hArgs hCall

end OuterArgExprStmtRun

/-- Generic execution relation for an incoming statement whose expression is a
surrounding call argument containing the generated local call. -/
inductive OuterIncomingStmtRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (state : σ) :
    Nat → Frontend.AstStmt → σ → Prop where
  | assign
      {fuel : Nat} {names : List Frontend.Name}
      {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {final : σ} {outputs : List Frontend.Word}
      (hCheck :
        EvmYul.Yul.checkAssignment (model.source state) names = .ok ())
      (hOuter :
        OuterArgCallRun hEvidence model prim state
          fuel callee left focus right final outputs) :
      OuterIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.Assign names (.Call callee (left ++ focus :: right)))
        (model.multifill names final outputs)
  | letValue
      {fuel : Nat} {names : List Frontend.Name}
      {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {final : σ} {outputs : List Frontend.Word}
      (hCheck :
        EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
      (hOuter :
        OuterArgCallRun hEvidence model prim state
          fuel callee left focus right final outputs) :
      OuterIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.Let names (some (.Call callee (left ++ focus :: right))))
        (model.multifill names final outputs)
  | exprStmt
      {fuel : Nat}
      {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {afterStmt : σ}
      (hExpr :
        OuterArgExprStmtRun hEvidence model prim state
          fuel callee left focus right afterStmt) :
      OuterIncomingStmtRun hEvidence model prim state fuel
        (.ExprStmtCall (.Call callee (left ++ focus :: right)))
        afterStmt
  | ifFalse
      {fuel : Nat} {ifBody : List Frontend.AstStmt}
      {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {stateAfterCond : σ} {condValue : Frontend.Word}
      (hOuter :
        OuterArgCallRun hEvidence model prim state
          fuel callee left focus right stateAfterCond [condValue])
      (hZero : condValue = EvmYul.UInt256.ofNat 0) :
      OuterIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.If (.Call callee (left ++ focus :: right)) ifBody)
        stateAfterCond
  | ifTrue
      {fuel : Nat} {ifBody : List Frontend.AstStmt}
      {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {stateAfterCond final : σ} {condValue : Frontend.Word}
      (hOuter :
        OuterArgCallRun hEvidence model prim state
          fuel callee left focus right stateAfterCond [condValue])
      (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
      (hIfBody :
        Yul.Source.Effectful.exec model prim fuel
            (.Block ifBody)
            (some ordered.program.contract) stateAfterCond =
          .ok final) :
      OuterIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.If (.Call callee (left ++ focus :: right)) ifBody)
        final
  | switch
      {fuel : Nat}
      {cases : List (Frontend.Word × List Frontend.AstStmt)}
      {defaultBody : List Frontend.AstStmt}
      {callee : Sum (EvmYul.Operation .Yul) Frontend.Name}
      {left right : List Frontend.AstExpr}
      {focus : Frontend.AstExpr}
      {stateAfterScrutinee final : σ}
      {scrutineeValue : Frontend.Word}
      (hOuter :
        OuterArgCallRun hEvidence model prim state
          fuel callee left focus right stateAfterScrutinee [scrutineeValue])
      (hSelected :
        Yul.Source.Effectful.exec model prim fuel
            (.Block
              (EvmYul.Yul.selectSwitchCase
                scrutineeValue defaultBody cases))
            (some ordered.program.contract) stateAfterScrutinee =
          .ok final) :
      OuterIncomingStmtRun hEvidence model prim state (fuel + 1)
        (.Switch (.Call callee (left ++ focus :: right))
          cases defaultBody)
        final

namespace OuterIncomingStmtRun

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      OuterIncomingStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    Yul.Source.Effectful.exec model prim fuel stmt
        (some ordered.program.contract) state =
      .ok afterStmt := by
  cases hRun with
  | assign hCheck hOuter =>
      exact
        Yul.Source.Effectful.exec_assign_of_evalValues
          model prim hCheck hOuter.evalValues
  | letValue hCheck hOuter =>
      exact
        Yul.Source.Effectful.exec_let_some_of_evalValues
          model prim hCheck hOuter.evalValues
  | exprStmt hExpr =>
      exact hExpr.exec
  | ifFalse hOuter hZero =>
      exact
        Yul.Source.Effectful.exec_if_false_of_eval
          model prim hOuter.eval_of_singleton hZero
  | ifTrue hOuter hNonzero hIfBody =>
      exact
        Yul.Source.Effectful.exec_if_true_of_eval
          model prim hOuter.eval_of_singleton hNonzero hIfBody
  | switch hOuter hSelected =>
      exact
        Yul.Source.Effectful.exec_switch_of_eval
          model prim hOuter.eval_of_singleton hSelected

theorem execSeq_prefix
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {pre rest : List Frontend.AstStmt}
    {stmt : Frontend.AstStmt}
    {state stateBeforeStmt afterStmt afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((prefixFuel + 1) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeStmt)
    (hPrefixSource :
      model.source stateBeforeStmt = .Ok prefixShared prefixVars)
    (hStmt :
      OuterIncomingStmtRun hEvidence model prim stateBeforeStmt
        prefixFuel stmt afterStmt)
    (hStmtSource :
      model.source afterStmt = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim prefixFuel rest
          (some ordered.program.contract) afterStmt =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) (pre ++ stmt :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (prefixFuel + 1)
          (stmt :: rest)
          (some ordered.program.contract) stateBeforeStmt =
        .ok afterRest :=
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt.exec hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := prefixFuel + 1) (pre := pre)
      (suffix := stmt :: rest)
      hPrefix hPrefixSource hSuffix

theorem execSeq_of_split
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts pre rest : List Frontend.AstStmt}
    {stmt : Frontend.AstStmt}
    {state stateBeforeStmt afterStmt afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    (hSplit : stmts = pre ++ stmt :: rest)
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((prefixFuel + 1) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeStmt)
    (hPrefixSource :
      model.source stateBeforeStmt = .Ok prefixShared prefixVars)
    (hStmt :
      OuterIncomingStmtRun hEvidence model prim stateBeforeStmt
        prefixFuel stmt afterStmt)
    (hStmtSource :
      model.source afterStmt = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim prefixFuel rest
          (some ordered.program.contract) afterStmt =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) stmts
        (some ordered.program.contract) state =
      .ok afterRest := by
  subst stmts
  exact execSeq_prefix hPrefix hPrefixSource hStmt hStmtSource hRest

end OuterIncomingStmtRun

/-- Statement-list execution package for the one-step outer-argument incoming
occurrence branch. -/
structure OuterStmtListOccurrenceRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (stmts : List Frontend.AstStmt)
    (state : σ) where
  pre : List Frontend.AstStmt
  stmt : Frontend.AstStmt
  rest : List Frontend.AstStmt
  hSplit : stmts = pre ++ stmt :: rest
  hOuter :
    YulOccurrence.StmtIncomingUserCall.OuterArg
      stmt hEvidence.generated hEvidence.yulArgs
  stateBeforeStmt : σ
  afterStmt : σ
  afterRest : σ
  prefixShared : EvmYul.SharedState .Yul
  prefixVars : EvmYul.Yul.VarStore
  stmtShared : EvmYul.SharedState .Yul
  stmtVars : EvmYul.Yul.VarStore
  hPrefix :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) pre
        (some ordered.program.contract) state =
      .ok stateBeforeStmt
  hPrefixSource :
    model.source stateBeforeStmt = .Ok prefixShared prefixVars
  hStmt :
    OuterIncomingStmtRun hEvidence model prim stateBeforeStmt
      prefixFuel stmt afterStmt
  hStmtSource :
    model.source afterStmt = .Ok stmtShared stmtVars
  hRest :
    Yul.Source.Effectful.execSeq model prim prefixFuel rest
        (some ordered.program.contract) afterStmt =
      .ok afterRest

namespace OuterStmtListOccurrenceRun

theorem execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      OuterStmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + hRun.pre.length) stmts
        (some ordered.program.contract) state =
      .ok hRun.afterRest :=
  OuterIncomingStmtRun.execSeq_of_split
    hRun.hSplit hRun.hPrefix hRun.hPrefixSource hRun.hStmt
    hRun.hStmtSource hRun.hRest

end OuterStmtListOccurrenceRun

/-- Execution relation for one focused statement selected from a statement-list
occurrence.

Direct and one-step outer-argument incoming statements consume the checked
generic interfaces above.  The context case is intentionally a semantic
sub-interface: a syntactic occurrence in an `if` body, switch case, or loop
component is useful only when that nested context is actually the executed
context for the run.  Later recursive context lemmas inhabit this constructor
from nested statement-list runs. -/
inductive FocusedStmtRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (state : σ) :
    Nat → Frontend.AstStmt → σ → Prop where
  | direct
      {fuel : Nat} {stmt : Frontend.AstStmt} {afterStmt : σ}
      (hDirect :
        YulOccurrence.StmtIncomingUserCall.Direct
          stmt hEvidence.generated hEvidence.yulArgs)
      (hRun :
        DirectIncomingStmtRun hEvidence model prim state
          fuel stmt afterStmt) :
      FocusedStmtRun hEvidence model prim state fuel stmt afterStmt
  | outer
      {fuel : Nat} {stmt : Frontend.AstStmt} {afterStmt : σ}
      (hOuter :
        YulOccurrence.StmtIncomingUserCall.OuterArg
          stmt hEvidence.generated hEvidence.yulArgs)
      (hRun :
        OuterIncomingStmtRun hEvidence model prim state
          fuel stmt afterStmt) :
      FocusedStmtRun hEvidence model prim state fuel stmt afterStmt
  | context
      {fuel : Nat} {stmt : Frontend.AstStmt} {afterStmt : σ}
      (hContext :
        YulOccurrence.StmtUserCall.Context
          stmt hEvidence.generated hEvidence.yulArgs)
      (hExec :
        Yul.Source.Effectful.exec model prim fuel stmt
            (some ordered.program.contract) state =
          .ok afterStmt) :
      FocusedStmtRun hEvidence model prim state fuel stmt afterStmt

namespace FocusedStmtRun

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      FocusedStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    Yul.Source.Effectful.exec model prim fuel stmt
        (some ordered.program.contract) state =
      .ok afterStmt := by
  cases hRun with
  | direct _ hDirectRun =>
      exact hDirectRun.exec
  | outer _ hOuterRun =>
      exact hOuterRun.exec
  | context _ hExec =>
      exact hExec

theorem occurrence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      FocusedStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    YulOccurrence.StmtUserCall stmt
      hEvidence.generated hEvidence.yulArgs := by
  cases hRun with
  | direct hDirect _ =>
      exact .incoming hDirect.toIncoming
  | outer hOuter _ =>
      exact .incoming hOuter.toIncoming
  | context hContext _ =>
      exact hContext.toStmtUserCall

theorem direct_or_outerArg_or_context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      FocusedStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    YulOccurrence.StmtIncomingUserCall.Direct stmt
        hEvidence.generated hEvidence.yulArgs ∨
      YulOccurrence.StmtIncomingUserCall.OuterArg stmt
          hEvidence.generated hEvidence.yulArgs ∨
        YulOccurrence.StmtUserCall.Context stmt
          hEvidence.generated hEvidence.yulArgs := by
  cases hRun with
  | direct hDirect _ =>
      exact Or.inl hDirect
  | outer hOuter _ =>
      exact Or.inr (Or.inl hOuter)
  | context hContext _ =>
      exact Or.inr (Or.inr hContext)

theorem execSeq_prefix
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {pre rest : List Frontend.AstStmt}
    {stmt : Frontend.AstStmt}
    {state stateBeforeStmt afterStmt afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((prefixFuel + 1) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeStmt)
    (hPrefixSource :
      model.source stateBeforeStmt = .Ok prefixShared prefixVars)
    (hStmt :
      FocusedStmtRun hEvidence model prim stateBeforeStmt
        prefixFuel stmt afterStmt)
    (hStmtSource :
      model.source afterStmt = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim prefixFuel rest
          (some ordered.program.contract) afterStmt =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) (pre ++ stmt :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (prefixFuel + 1)
          (stmt :: rest)
          (some ordered.program.contract) stateBeforeStmt =
        .ok afterRest :=
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt.exec hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := prefixFuel + 1) (pre := pre)
      (suffix := stmt :: rest)
      hPrefix hPrefixSource hSuffix

theorem execSeq_of_split
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts pre rest : List Frontend.AstStmt}
    {stmt : Frontend.AstStmt}
    {state stateBeforeStmt afterStmt afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    (hSplit : stmts = pre ++ stmt :: rest)
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((prefixFuel + 1) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeStmt)
    (hPrefixSource :
      model.source stateBeforeStmt = .Ok prefixShared prefixVars)
    (hStmt :
      FocusedStmtRun hEvidence model prim stateBeforeStmt
        prefixFuel stmt afterStmt)
    (hStmtSource :
      model.source afterStmt = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim prefixFuel rest
          (some ordered.program.contract) afterStmt =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) stmts
        (some ordered.program.contract) state =
      .ok afterRest := by
  subst stmts
  exact execSeq_prefix hPrefix hPrefixSource hStmt hStmtSource hRest

end FocusedStmtRun

/-- Generic statement-list occurrence execution package over the checked
`YulOccurrence.StmtListUserCall.exists_split_stmt` splitter.

The selected focused statement may be a direct incoming call, a one-step
outer-argument incoming call, or a nested context whose own semantic execution
has already been discharged. -/
structure StmtListOccurrenceRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (stmts : List Frontend.AstStmt)
    (state : σ) where
  pre : List Frontend.AstStmt
  stmt : Frontend.AstStmt
  rest : List Frontend.AstStmt
  hSplit : stmts = pre ++ stmt :: rest
  hOccurrence :
    YulOccurrence.StmtUserCall stmt
      hEvidence.generated hEvidence.yulArgs
  stateBeforeStmt : σ
  afterStmt : σ
  afterRest : σ
  prefixShared : EvmYul.SharedState .Yul
  prefixVars : EvmYul.Yul.VarStore
  stmtShared : EvmYul.SharedState .Yul
  stmtVars : EvmYul.Yul.VarStore
  hPrefix :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) pre
        (some ordered.program.contract) state =
      .ok stateBeforeStmt
  hPrefixSource :
    model.source stateBeforeStmt = .Ok prefixShared prefixVars
  hStmt :
    FocusedStmtRun hEvidence model prim stateBeforeStmt
      prefixFuel stmt afterStmt
  hStmtSource :
    model.source afterStmt = .Ok stmtShared stmtVars
  hRest :
    Yul.Source.Effectful.execSeq model prim prefixFuel rest
        (some ordered.program.contract) afterStmt =
      .ok afterRest

namespace StmtListOccurrenceRun

theorem occurrence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      StmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state) :
    YulOccurrence.StmtListUserCall stmts
      hEvidence.generated hEvidence.yulArgs := by
  rw [hRun.hSplit]
  exact
    YulOccurrence.StmtListUserCall.append_right hRun.pre
      (YulOccurrence.StmtListUserCall.head hRun.hOccurrence)

theorem exists_split_direct_or_outerArg_or_context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      StmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state) :
    ∃ (pre : List Frontend.AstStmt)
        (stmt : Frontend.AstStmt)
        (rest : List Frontend.AstStmt),
      stmts = pre ++ stmt :: rest ∧
        (YulOccurrence.StmtIncomingUserCall.Direct stmt
            hEvidence.generated hEvidence.yulArgs ∨
          YulOccurrence.StmtIncomingUserCall.OuterArg stmt
              hEvidence.generated hEvidence.yulArgs ∨
            YulOccurrence.StmtUserCall.Context stmt
              hEvidence.generated hEvidence.yulArgs) :=
  ⟨hRun.pre, hRun.stmt, hRun.rest, hRun.hSplit,
    hRun.hStmt.direct_or_outerArg_or_context⟩

theorem execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      StmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + hRun.pre.length) stmts
        (some ordered.program.contract) state =
      .ok hRun.afterRest :=
  FocusedStmtRun.execSeq_of_split
    hRun.hSplit hRun.hPrefix hRun.hPrefixSource hRun.hStmt
    hRun.hStmtSource hRun.hRest

theorem classified_split_execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      StmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state) :
    ∃ (pre : List Frontend.AstStmt)
        (stmt : Frontend.AstStmt)
        (rest : List Frontend.AstStmt),
      stmts = pre ++ stmt :: rest ∧
        (YulOccurrence.StmtIncomingUserCall.Direct stmt
            hEvidence.generated hEvidence.yulArgs ∨
          YulOccurrence.StmtIncomingUserCall.OuterArg stmt
              hEvidence.generated hEvidence.yulArgs ∨
            YulOccurrence.StmtUserCall.Context stmt
              hEvidence.generated hEvidence.yulArgs) ∧
        Yul.Source.Effectful.execSeq model prim
            ((prefixFuel + 1) + pre.length) stmts
            (some ordered.program.contract) state =
          .ok hRun.afterRest :=
  ⟨hRun.pre, hRun.stmt, hRun.rest, hRun.hSplit,
    hRun.hStmt.direct_or_outerArg_or_context, hRun.execSeq⟩

def ofFocusedSplit
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts pre rest : List Frontend.AstStmt}
    {stmt : Frontend.AstStmt}
    {state stateBeforeStmt afterStmt afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    (hSplit : stmts = pre ++ stmt :: rest)
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((prefixFuel + 1) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeStmt)
    (hPrefixSource :
      model.source stateBeforeStmt = .Ok prefixShared prefixVars)
    (hStmt :
      FocusedStmtRun hEvidence model prim stateBeforeStmt
        prefixFuel stmt afterStmt)
    (hStmtSource :
      model.source afterStmt = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim prefixFuel rest
          (some ordered.program.contract) afterStmt =
        .ok afterRest) :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel stmts state where
  pre := pre
  stmt := stmt
  rest := rest
  hSplit := hSplit
  hOccurrence := hStmt.occurrence
  stateBeforeStmt := stateBeforeStmt
  afterStmt := afterStmt
  afterRest := afterRest
  prefixShared := prefixShared
  prefixVars := prefixVars
  stmtShared := stmtShared
  stmtVars := stmtVars
  hPrefix := hPrefix
  hPrefixSource := hPrefixSource
  hStmt := hStmt
  hStmtSource := hStmtSource
  hRest := hRest

theorem execSeq_of_focused_split
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts pre rest : List Frontend.AstStmt}
    {stmt : Frontend.AstStmt}
    {state stateBeforeStmt afterStmt afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    (hSplit : stmts = pre ++ stmt :: rest)
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((prefixFuel + 1) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeStmt)
    (hPrefixSource :
      model.source stateBeforeStmt = .Ok prefixShared prefixVars)
    (hStmt :
      FocusedStmtRun hEvidence model prim stateBeforeStmt
        prefixFuel stmt afterStmt)
    (hStmtSource :
      model.source afterStmt = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim prefixFuel rest
          (some ordered.program.contract) afterStmt =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) stmts
        (some ordered.program.contract) state =
      .ok afterRest :=
  (ofFocusedSplit hSplit hPrefix hPrefixSource hStmt hStmtSource hRest).execSeq

/-- Generic execution package for a statement-list occurrence after applying
`YulOccurrence.StmtListUserCall.exists_split_stmt`.

This is the semantic shape the recursive caller/context theorem should target:
the splitter chooses `pre ++ stmt :: rest`, the prefix executes regularly to
the focused statement, the focused statement is discharged by `FocusedStmtRun`,
and the suffix executes from the focused post-state. -/
structure SplitFocusedRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (stmts : List Frontend.AstStmt)
    (state : σ) where
  hListOccurrence :
    YulOccurrence.StmtListUserCall stmts
      hEvidence.generated hEvidence.yulArgs
  pre : List Frontend.AstStmt
  stmt : Frontend.AstStmt
  rest : List Frontend.AstStmt
  hSplit : stmts = pre ++ stmt :: rest
  hStmtOccurrence :
    YulOccurrence.StmtUserCall stmt
      hEvidence.generated hEvidence.yulArgs
  stateBeforeStmt : σ
  afterStmt : σ
  afterRest : σ
  prefixShared : EvmYul.SharedState .Yul
  prefixVars : EvmYul.Yul.VarStore
  stmtShared : EvmYul.SharedState .Yul
  stmtVars : EvmYul.Yul.VarStore
  hPrefix :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) pre
        (some ordered.program.contract) state =
      .ok stateBeforeStmt
  hPrefixSource :
    model.source stateBeforeStmt = .Ok prefixShared prefixVars
  hStmt :
    FocusedStmtRun hEvidence model prim stateBeforeStmt
      prefixFuel stmt afterStmt
  hStmtSource :
    model.source afterStmt = .Ok stmtShared stmtVars
  hRest :
    Yul.Source.Effectful.execSeq model prim prefixFuel rest
        (some ordered.program.contract) afterStmt =
      .ok afterRest

namespace SplitFocusedRun

def toStmtListOccurrenceRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      SplitFocusedRun hEvidence model prim prefixFuel stmts state) :
    StmtListOccurrenceRun hEvidence model prim prefixFuel stmts state :=
  ofFocusedSplit
    hRun.hSplit hRun.hPrefix hRun.hPrefixSource hRun.hStmt
    hRun.hStmtSource hRun.hRest

def ofStmtListOccurrenceRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      StmtListOccurrenceRun hEvidence model prim prefixFuel stmts state) :
    SplitFocusedRun hEvidence model prim prefixFuel stmts state where
  hListOccurrence := hRun.occurrence
  pre := hRun.pre
  stmt := hRun.stmt
  rest := hRun.rest
  hSplit := hRun.hSplit
  hStmtOccurrence := hRun.hOccurrence
  stateBeforeStmt := hRun.stateBeforeStmt
  afterStmt := hRun.afterStmt
  afterRest := hRun.afterRest
  prefixShared := hRun.prefixShared
  prefixVars := hRun.prefixVars
  stmtShared := hRun.stmtShared
  stmtVars := hRun.stmtVars
  hPrefix := hRun.hPrefix
  hPrefixSource := hRun.hPrefixSource
  hStmt := hRun.hStmt
  hStmtSource := hRun.hStmtSource
  hRest := hRun.hRest

theorem execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      SplitFocusedRun hEvidence model prim prefixFuel stmts state) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + hRun.pre.length) stmts
        (some ordered.program.contract) state =
      .ok hRun.afterRest :=
  hRun.toStmtListOccurrenceRun.execSeq

theorem split
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      SplitFocusedRun hEvidence model prim prefixFuel stmts state) :
    ∃ (pre : List Frontend.AstStmt)
        (stmt : Frontend.AstStmt)
        (rest : List Frontend.AstStmt),
      stmts = pre ++ stmt :: rest ∧
        YulOccurrence.StmtUserCall stmt
          hEvidence.generated hEvidence.yulArgs :=
  ⟨hRun.pre, hRun.stmt, hRun.rest, hRun.hSplit,
    hRun.hStmtOccurrence⟩

theorem classified_split_execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      SplitFocusedRun hEvidence model prim prefixFuel stmts state) :
    ∃ (pre : List Frontend.AstStmt)
        (stmt : Frontend.AstStmt)
        (rest : List Frontend.AstStmt),
      stmts = pre ++ stmt :: rest ∧
        YulOccurrence.StmtUserCall stmt
          hEvidence.generated hEvidence.yulArgs ∧
        Yul.Source.Effectful.execSeq model prim
            ((prefixFuel + 1) + pre.length) stmts
            (some ordered.program.contract) state =
          .ok hRun.afterRest :=
  ⟨hRun.pre, hRun.stmt, hRun.rest, hRun.hSplit,
    hRun.hStmtOccurrence, hRun.execSeq⟩

end SplitFocusedRun

def ofDirect
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      DirectStmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state)
    (hOccurrence :
      YulOccurrence.StmtUserCall hRun.stmt
        hEvidence.generated hEvidence.yulArgs) :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel stmts state where
  pre := hRun.pre
  stmt := hRun.stmt
  rest := hRun.rest
  hSplit := hRun.hSplit
  hOccurrence := hOccurrence
  stateBeforeStmt := hRun.stateBeforeStmt
  afterStmt := hRun.afterStmt
  afterRest := hRun.afterRest
  prefixShared := hRun.prefixShared
  prefixVars := hRun.prefixVars
  stmtShared := hRun.stmtShared
  stmtVars := hRun.stmtVars
  hPrefix := hRun.hPrefix
  hPrefixSource := hRun.hPrefixSource
  hStmt := .direct hRun.hDirect hRun.hStmt
  hStmtSource := hRun.hStmtSource
  hRest := hRun.hRest

def ofOuter
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      OuterStmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state)
    (hOccurrence :
      YulOccurrence.StmtUserCall hRun.stmt
        hEvidence.generated hEvidence.yulArgs) :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel stmts state where
  pre := hRun.pre
  stmt := hRun.stmt
  rest := hRun.rest
  hSplit := hRun.hSplit
  hOccurrence := hOccurrence
  stateBeforeStmt := hRun.stateBeforeStmt
  afterStmt := hRun.afterStmt
  afterRest := hRun.afterRest
  prefixShared := hRun.prefixShared
  prefixVars := hRun.prefixVars
  stmtShared := hRun.stmtShared
  stmtVars := hRun.stmtVars
  hPrefix := hRun.hPrefix
  hPrefixSource := hRun.hPrefixSource
  hStmt := .outer hRun.hOuter hRun.hStmt
  hStmtSource := hRun.hStmtSource
  hRest := hRun.hRest

end StmtListOccurrenceRun

/-- Executed `.Block` context whose body contains the focused generated-call
occurrence. -/
structure BlockContextRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (body : List Frontend.AstStmt)
    (state : σ) where
  bodyRun :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel body state
  afterBlock : σ
  hAfterBlock :
    afterBlock =
      model.withSource bodyRun.afterRest
        ((model.source bodyRun.afterRest).restrictStoreTo
          (model.source state).store)

namespace BlockContextRun

def ofSplitFocused
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      StmtListOccurrenceRun.SplitFocusedRun hEvidence model prim
        prefixFuel body state) :
    BlockContextRun hEvidence model prim prefixFuel body state where
  bodyRun := hRun.toStmtListOccurrenceRun
  afterBlock :=
    model.withSource hRun.afterRest
      ((model.source hRun.afterRest).restrictStoreTo
        (model.source state).store)
  hAfterBlock := rfl

theorem context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      BlockContextRun hEvidence model prim prefixFuel body state) :
    YulOccurrence.StmtUserCall.Context (.Block body)
      hEvidence.generated hEvidence.yulArgs :=
  .block hRun.bodyRun.occurrence

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      BlockContextRun hEvidence model prim prefixFuel body state) :
    Yul.Source.Effectful.exec model prim
        (((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1)
        (.Block body)
        (some ordered.program.contract) state =
      .ok hRun.afterBlock := by
  have hBody := hRun.bodyRun.execSeq
  have hExec :=
    Yul.Source.Effectful.exec_block_of_execSeq model prim hBody
  rw [hRun.hAfterBlock]
  exact hExec

def focusedStmt
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      BlockContextRun hEvidence model prim prefixFuel body state) :
    FocusedStmtRun hEvidence model prim state
      (((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1)
      (.Block body) hRun.afterBlock :=
  .context hRun.context hRun.exec

end BlockContextRun

/-- Executed `.Switch` context whose selected body contains the focused
generated-call occurrence.  The selected-body equality is semantic: occurrences
in unselected cases/defaults do not inhabit this run. -/
structure SwitchContextRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (scrutinee : Frontend.AstExpr)
    (cases : List (Frontend.Word × List Frontend.AstStmt))
    (defaultBody selectedBody : List Frontend.AstStmt)
    (state : σ) where
  stateAfterScrutinee : σ
  scrutineeValue : Frontend.Word
  bodyRun :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel selectedBody stateAfterScrutinee
  hEval :
    Yul.Source.Effectful.eval model prim
        (((prefixFuel + 1) + bodyRun.pre.length) + 1)
        scrutinee (some ordered.program.contract) state =
      .ok (stateAfterScrutinee, scrutineeValue)
  hSelected :
    EvmYul.Yul.selectSwitchCase scrutineeValue defaultBody cases =
      selectedBody
  hContext :
    YulOccurrence.StmtUserCall.Context
      (.Switch scrutinee cases defaultBody)
      hEvidence.generated hEvidence.yulArgs
  afterSwitch : σ
  hAfterSwitch :
    afterSwitch =
      model.withSource bodyRun.afterRest
        ((model.source bodyRun.afterRest).restrictStoreTo
          (model.source stateAfterScrutinee).store)

namespace SwitchContextRun

def ofSplitFocused
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {scrutinee : Frontend.AstExpr}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody selectedBody : List Frontend.AstStmt}
    {state stateAfterScrutinee : σ}
    {scrutineeValue : Frontend.Word}
    (bodyRun :
      StmtListOccurrenceRun.SplitFocusedRun hEvidence model prim
        prefixFuel selectedBody stateAfterScrutinee)
    (hEval :
      Yul.Source.Effectful.eval model prim
          (((prefixFuel + 1) + bodyRun.pre.length) + 1)
          scrutinee (some ordered.program.contract) state =
        .ok (stateAfterScrutinee, scrutineeValue))
    (hSelected :
      EvmYul.Yul.selectSwitchCase scrutineeValue defaultBody cases =
        selectedBody)
    (hContext :
      YulOccurrence.StmtUserCall.Context
        (.Switch scrutinee cases defaultBody)
        hEvidence.generated hEvidence.yulArgs) :
    SwitchContextRun hEvidence model prim prefixFuel
      scrutinee cases defaultBody selectedBody state where
  stateAfterScrutinee := stateAfterScrutinee
  scrutineeValue := scrutineeValue
  bodyRun := bodyRun.toStmtListOccurrenceRun
  hEval := hEval
  hSelected := hSelected
  hContext := hContext
  afterSwitch :=
    model.withSource bodyRun.afterRest
      ((model.source bodyRun.afterRest).restrictStoreTo
        (model.source stateAfterScrutinee).store)
  hAfterSwitch := rfl

theorem context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {scrutinee : Frontend.AstExpr}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody selectedBody : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      SwitchContextRun hEvidence model prim prefixFuel
        scrutinee cases defaultBody selectedBody state) :
    YulOccurrence.StmtUserCall.Context
      (.Switch scrutinee cases defaultBody)
      hEvidence.generated hEvidence.yulArgs :=
  hRun.hContext

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {scrutinee : Frontend.AstExpr}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody selectedBody : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      SwitchContextRun hEvidence model prim prefixFuel
        scrutinee cases defaultBody selectedBody state) :
    Yul.Source.Effectful.exec model prim
        ((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1)
        (.Switch scrutinee cases defaultBody)
        (some ordered.program.contract) state =
      .ok hRun.afterSwitch := by
  have hBodySeq := hRun.bodyRun.execSeq
  have hBodyBlockSelected :
      Yul.Source.Effectful.exec model prim
          (((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1)
          (.Block
            (EvmYul.Yul.selectSwitchCase
              hRun.scrutineeValue defaultBody cases))
          (some ordered.program.contract) hRun.stateAfterScrutinee =
        .ok hRun.afterSwitch := by
    rw [hRun.hSelected]
    have hBodyBlock :=
      Yul.Source.Effectful.exec_block_of_execSeq model prim hBodySeq
    rw [hRun.hAfterSwitch]
    exact hBodyBlock
  exact
    Yul.Source.Effectful.exec_switch_of_eval
      model prim hRun.hEval hBodyBlockSelected

def focusedStmt
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {scrutinee : Frontend.AstExpr}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody selectedBody : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      SwitchContextRun hEvidence model prim prefixFuel
        scrutinee cases defaultBody selectedBody state) :
    FocusedStmtRun hEvidence model prim state
      ((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1)
      (.Switch scrutinee cases defaultBody) hRun.afterSwitch :=
  .context hRun.context hRun.exec

end SwitchContextRun

/-- Executed `.If` context whose body contains the focused generated-call
occurrence.  The nonzero condition premise makes this an executed-body
interface, not merely a syntactic occurrence in the branch. -/
structure IfContextRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (condition : Frontend.AstExpr)
    (body : List Frontend.AstStmt)
    (state : σ) where
  stateAfterCondition : σ
  conditionValue : Frontend.Word
  bodyRun :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel body stateAfterCondition
  hEval :
    Yul.Source.Effectful.eval model prim
        (((prefixFuel + 1) + bodyRun.pre.length) + 1)
        condition (some ordered.program.contract) state =
      .ok (stateAfterCondition, conditionValue)
  hNonzero :
    conditionValue ≠ EvmYul.UInt256.ofNat 0
  afterIf : σ
  hAfterIf :
    afterIf =
      model.withSource bodyRun.afterRest
        ((model.source bodyRun.afterRest).restrictStoreTo
          (model.source stateAfterCondition).store)

namespace IfContextRun

def ofSplitFocused
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {body : List Frontend.AstStmt}
    {state stateAfterCondition : σ}
    {conditionValue : Frontend.Word}
    (bodyRun :
      StmtListOccurrenceRun.SplitFocusedRun hEvidence model prim
        prefixFuel body stateAfterCondition)
    (hEval :
      Yul.Source.Effectful.eval model prim
          (((prefixFuel + 1) + bodyRun.pre.length) + 1)
          condition (some ordered.program.contract) state =
        .ok (stateAfterCondition, conditionValue))
    (hNonzero :
      conditionValue ≠ EvmYul.UInt256.ofNat 0) :
    IfContextRun hEvidence model prim prefixFuel condition body state where
  stateAfterCondition := stateAfterCondition
  conditionValue := conditionValue
  bodyRun := bodyRun.toStmtListOccurrenceRun
  hEval := hEval
  hNonzero := hNonzero
  afterIf :=
    model.withSource bodyRun.afterRest
      ((model.source bodyRun.afterRest).restrictStoreTo
        (model.source stateAfterCondition).store)
  hAfterIf := rfl

theorem context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      IfContextRun hEvidence model prim prefixFuel condition body state) :
    YulOccurrence.StmtUserCall.Context (.If condition body)
      hEvidence.generated hEvidence.yulArgs :=
  .ifBody hRun.bodyRun.occurrence

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      IfContextRun hEvidence model prim prefixFuel condition body state) :
    Yul.Source.Effectful.exec model prim
        ((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1)
        (.If condition body)
        (some ordered.program.contract) state =
      .ok hRun.afterIf := by
  have hBodySeq := hRun.bodyRun.execSeq
  have hBodyBlock :
      Yul.Source.Effectful.exec model prim
          (((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1)
          (.Block body)
          (some ordered.program.contract) hRun.stateAfterCondition =
        .ok hRun.afterIf := by
    have hBlock :=
      Yul.Source.Effectful.exec_block_of_execSeq model prim hBodySeq
    rw [hRun.hAfterIf]
    exact hBlock
  exact
    Yul.Source.Effectful.exec_if_true_of_eval
      model prim hRun.hEval hRun.hNonzero hBodyBlock

def focusedStmt
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      IfContextRun hEvidence model prim prefixFuel condition body state) :
    FocusedStmtRun hEvidence model prim state
      ((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1)
      (.If condition body) hRun.afterIf :=
  .context hRun.context hRun.exec

end IfContextRun

/-- Executed `.For` context whose condition expression contains the focused
generated-call occurrence.  The condition run is the loop's actual first
condition evaluation; the remaining loop behavior is summarized by the generic
Yul `LoopAfterCondCase` interface. -/
structure ForConditionContextRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (conditionFuel : Nat)
    (condition : Frontend.AstExpr)
    (post body : List Frontend.AstStmt)
    (state : σ) where
  conditionRun :
    FocusedExprRun hEvidence model prim conditionFuel condition
      (model.withSource state
        (EvmYul.Yul.State.mkOk (model.source state)))
  afterFor : σ
  hCase :
    Yul.Source.Effectful.LoopAfterCondCase model prim
      conditionFuel condition post body
      (some ordered.program.contract)
      (model.source state) conditionRun.afterFocus
      conditionRun.value afterFor

namespace ForConditionContextRun

theorem context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {conditionFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForConditionContextRun hEvidence model prim conditionFuel
        condition post body state) :
    YulOccurrence.StmtUserCall.Context (.For condition post body)
      hEvidence.generated hEvidence.yulArgs :=
  .forCondition hRun.conditionRun.hOccurrence

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {conditionFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForConditionContextRun hEvidence model prim conditionFuel
        condition post body state) :
    Yul.Source.Effectful.exec model prim
        ((conditionFuel + 1 + 1) + 1)
        (.For condition post body)
        (some ordered.program.contract) state =
      .ok hRun.afterFor := by
  have hLoop :
      Yul.Source.Effectful.loop model prim
          (conditionFuel + 1 + 1) condition post body
          (some ordered.program.contract) state =
        .ok hRun.afterFor :=
    Yul.Source.Effectful.loop_of_eval_after_cond_case
      model prim hRun.conditionRun.hEval hRun.hCase
  exact Yul.Source.Effectful.exec_for_of_loop model prim hLoop

def focusedStmt
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {conditionFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForConditionContextRun hEvidence model prim conditionFuel
        condition post body state) :
    FocusedStmtRun hEvidence model prim state
      ((conditionFuel + 1 + 1) + 1)
      (.For condition post body) hRun.afterFor :=
  .context hRun.context hRun.exec

end ForConditionContextRun

/-- Remaining loop behavior after an executed loop body.  The body block
execution itself is supplied by the enclosing body-context run; this relation
packages the possible Yul continuations without re-opening the frontend
occurrence proof. -/
inductive ForBodyContinuationRun
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (loopFuel : Nat)
    (condition : Frontend.AstExpr)
    (post body : List Frontend.AstStmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state stateAfterCondition : σ)
    (conditionValue : Frontend.Word)
    (afterBody : σ) :
    σ → Prop where
  | bodyOutOfFuel
      (hBodySource : model.source afterBody = .OutOfFuel)
      {afterFor : σ}
      (hFinal :
        afterFor =
          model.withSource afterBody
            ((model.source afterBody).overwrite? (model.source state))) :
      ForBodyContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue afterBody
        afterFor
  | bodyBreak
      {shared : EvmYul.SharedState .Yul}
      {store : EvmYul.Yul.VarStore}
      (hBodySource :
        model.source afterBody = .Checkpoint (.Break shared store))
      {afterFor : σ}
      (hFinal :
        afterFor =
          model.withSource afterBody
            ((model.source afterBody).reviveJump.overwrite?
              (model.source state))) :
      ForBodyContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue afterBody
        afterFor
  | bodyLeave
      {shared : EvmYul.SharedState .Yul}
      {store : EvmYul.Yul.VarStore}
      (hBodySource :
        model.source afterBody = .Checkpoint (.Leave shared store))
      {afterFor : σ}
      (hFinal :
        afterFor =
          model.withSource afterBody
            ((model.source afterBody).overwrite? (model.source state))) :
      ForBodyContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue afterBody
        afterFor
  | postOutOfFuel
      (hBodyContinues :
        Yul.Source.Effectful.LoopBodyContinues (model.source afterBody))
      {afterPost afterFor : σ}
      (hPost :
        Yul.Source.Effectful.exec model prim loopFuel (.Block post)
            codeOverride
            (model.withSource afterBody
              (model.source afterBody).reviveJump) =
          .ok afterPost)
      (hPostSource : model.source afterPost = .OutOfFuel)
      (hFinal :
        afterFor =
          model.withSource afterPost
            ((model.source afterPost).overwrite? (model.source state))) :
      ForBodyContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue afterBody
        afterFor
  | postLeave
      (hBodyContinues :
        Yul.Source.Effectful.LoopBodyContinues (model.source afterBody))
      {afterPost afterFor : σ}
      {shared : EvmYul.SharedState .Yul}
      {store : EvmYul.Yul.VarStore}
      (hPost :
        Yul.Source.Effectful.exec model prim loopFuel (.Block post)
            codeOverride
            (model.withSource afterBody
              (model.source afterBody).reviveJump) =
          .ok afterPost)
      (hPostSource :
        model.source afterPost = .Checkpoint (.Leave shared store))
      (hFinal :
        afterFor =
          model.withSource afterPost
            ((model.source afterPost).overwrite? (model.source state))) :
      ForBodyContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue afterBody
        afterFor
  | recurse
      (hBodyContinues :
        Yul.Source.Effectful.LoopBodyContinues (model.source afterBody))
      {afterPost afterLoop afterFor : σ}
      (hPost :
        Yul.Source.Effectful.exec model prim loopFuel (.Block post)
            codeOverride
            (model.withSource afterBody
              (model.source afterBody).reviveJump) =
          .ok afterPost)
      (hPostRecurs :
        Yul.Source.Effectful.LoopPostRecurs (model.source afterPost))
      (hLoop :
        Yul.Source.Effectful.exec model prim loopFuel
            (.For condition post body) codeOverride
            (model.withSource afterPost
              ((model.source afterPost).overwrite? (model.source state))) =
          .ok afterLoop)
      (hFinal :
        afterFor =
          model.withSource afterLoop
            ((model.source afterLoop).overwrite? (model.source state))) :
      ForBodyContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue afterBody
        afterFor

namespace ForBodyContinuationRun

theorem loopAfterCondCase
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {loopFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterCondition : σ}
    {conditionValue : Frontend.Word}
    {afterBody afterFor : σ}
    (hNonzero : conditionValue ≠ EvmYul.UInt256.ofNat 0)
    (hBody :
      Yul.Source.Effectful.exec model prim loopFuel (.Block body)
          codeOverride stateAfterCondition =
        .ok afterBody)
    (hRun :
      ForBodyContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue afterBody
        afterFor) :
    Yul.Source.Effectful.LoopAfterCondCase model prim loopFuel
      condition post body codeOverride (model.source state)
      stateAfterCondition conditionValue afterFor := by
  cases hRun with
  | bodyOutOfFuel hBodySource hFinal =>
      exact .bodyOutOfFuel hNonzero hBody hBodySource hFinal
  | bodyBreak hBodySource hFinal =>
      exact .bodyBreak hNonzero hBody hBodySource hFinal
  | bodyLeave hBodySource hFinal =>
      exact .bodyLeave hNonzero hBody hBodySource hFinal
  | postOutOfFuel hBodyContinues hPost hPostSource hFinal =>
      exact
        .postOutOfFuel hNonzero hBody hBodyContinues
          hPost hPostSource hFinal
  | postLeave hBodyContinues hPost hPostSource hFinal =>
      exact
        .postLeave hNonzero hBody hBodyContinues
          hPost hPostSource hFinal
  | recurse hBodyContinues hPost hPostRecurs hLoop hFinal =>
      exact
        .recurse hNonzero hBody hBodyContinues
          hPost hPostRecurs hLoop hFinal

end ForBodyContinuationRun

/-- Executed `.For` context whose body contains the focused generated-call
occurrence.  The nested body run supplies the exact body block execution used
by the loop continuation case. -/
structure ForBodyContextRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (condition : Frontend.AstExpr)
    (post body : List Frontend.AstStmt)
    (state : σ) where
  stateAfterCondition : σ
  conditionValue : Frontend.Word
  bodyRun :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel body stateAfterCondition
  hEval :
    Yul.Source.Effectful.eval model prim
        (((prefixFuel + 1) + bodyRun.pre.length) + 1)
        condition (some ordered.program.contract)
        (model.withSource state
          (EvmYul.Yul.State.mkOk (model.source state))) =
      .ok (stateAfterCondition, conditionValue)
  hNonzero :
    conditionValue ≠ EvmYul.UInt256.ofNat 0
  afterBody : σ
  hAfterBody :
    afterBody =
      model.withSource bodyRun.afterRest
        ((model.source bodyRun.afterRest).restrictStoreTo
          (model.source stateAfterCondition).store)
  afterFor : σ
  hContinuation :
    ForBodyContinuationRun model prim
      (((prefixFuel + 1) + bodyRun.pre.length) + 1)
      condition post body (some ordered.program.contract)
      state stateAfterCondition conditionValue afterBody afterFor

namespace ForBodyContextRun

def ofSplitFocused
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state stateAfterCondition : σ}
    {conditionValue : Frontend.Word}
    {afterFor : σ}
    (bodyRun :
      StmtListOccurrenceRun.SplitFocusedRun hEvidence model prim
        prefixFuel body stateAfterCondition)
    (hEval :
      Yul.Source.Effectful.eval model prim
          (((prefixFuel + 1) + bodyRun.pre.length) + 1)
          condition (some ordered.program.contract)
          (model.withSource state
            (EvmYul.Yul.State.mkOk (model.source state))) =
        .ok (stateAfterCondition, conditionValue))
    (hNonzero :
      conditionValue ≠ EvmYul.UInt256.ofNat 0)
    (hContinuation :
      ForBodyContinuationRun model prim
        (((prefixFuel + 1) + bodyRun.pre.length) + 1)
        condition post body (some ordered.program.contract)
        state stateAfterCondition conditionValue
        (model.withSource bodyRun.afterRest
          ((model.source bodyRun.afterRest).restrictStoreTo
            (model.source stateAfterCondition).store))
        afterFor) :
    ForBodyContextRun hEvidence model prim prefixFuel
      condition post body state where
  stateAfterCondition := stateAfterCondition
  conditionValue := conditionValue
  bodyRun := bodyRun.toStmtListOccurrenceRun
  hEval := hEval
  hNonzero := hNonzero
  afterBody :=
    model.withSource bodyRun.afterRest
      ((model.source bodyRun.afterRest).restrictStoreTo
        (model.source stateAfterCondition).store)
  hAfterBody := rfl
  afterFor := afterFor
  hContinuation := hContinuation

theorem context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForBodyContextRun hEvidence model prim prefixFuel
        condition post body state) :
    YulOccurrence.StmtUserCall.Context (.For condition post body)
      hEvidence.generated hEvidence.yulArgs :=
  .forBody hRun.bodyRun.occurrence

theorem bodyBlock
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForBodyContextRun hEvidence model prim prefixFuel
        condition post body state) :
    Yul.Source.Effectful.exec model prim
        (((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1)
        (.Block body)
        (some ordered.program.contract) hRun.stateAfterCondition =
      .ok hRun.afterBody := by
  have hBodySeq := hRun.bodyRun.execSeq
  have hBlock :=
    Yul.Source.Effectful.exec_block_of_execSeq model prim hBodySeq
  rw [hRun.hAfterBody]
  exact hBlock

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForBodyContextRun hEvidence model prim prefixFuel
        condition post body state) :
    Yul.Source.Effectful.exec model prim
        ((((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1) + 1) + 1)
        (.For condition post body)
        (some ordered.program.contract) state =
      .ok hRun.afterFor := by
  have hCase :=
    ForBodyContinuationRun.loopAfterCondCase
      hRun.hNonzero hRun.bodyBlock hRun.hContinuation
  have hLoop :
      Yul.Source.Effectful.loop model prim
          ((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1 + 1)
          condition post body (some ordered.program.contract) state =
        .ok hRun.afterFor :=
    Yul.Source.Effectful.loop_of_eval_after_cond_case
      model prim hRun.hEval hCase
  exact Yul.Source.Effectful.exec_for_of_loop model prim hLoop

def focusedStmt
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForBodyContextRun hEvidence model prim prefixFuel
        condition post body state) :
    FocusedStmtRun hEvidence model prim state
      ((((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1) + 1) + 1)
      (.For condition post body) hRun.afterFor :=
  .context hRun.context hRun.exec

end ForBodyContextRun

/-- Remaining loop behavior after an executed loop post block.  The post block
execution itself is supplied by the enclosing post-context run. -/
inductive ForPostContinuationRun
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (loopFuel : Nat)
    (condition : Frontend.AstExpr)
    (post body : List Frontend.AstStmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state stateAfterCondition : σ)
    (conditionValue : Frontend.Word)
    (afterBody afterPost : σ) :
    σ → Prop where
  | postOutOfFuel
      (hPostSource : model.source afterPost = .OutOfFuel)
      {afterFor : σ}
      (hFinal :
        afterFor =
          model.withSource afterPost
            ((model.source afterPost).overwrite? (model.source state))) :
      ForPostContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue
        afterBody afterPost afterFor
  | postLeave
      {shared : EvmYul.SharedState .Yul}
      {store : EvmYul.Yul.VarStore}
      (hPostSource :
        model.source afterPost = .Checkpoint (.Leave shared store))
      {afterFor : σ}
      (hFinal :
        afterFor =
          model.withSource afterPost
            ((model.source afterPost).overwrite? (model.source state))) :
      ForPostContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue
        afterBody afterPost afterFor
  | recurse
      (hPostRecurs :
        Yul.Source.Effectful.LoopPostRecurs (model.source afterPost))
      {afterLoop afterFor : σ}
      (hLoop :
        Yul.Source.Effectful.exec model prim loopFuel
            (.For condition post body) codeOverride
            (model.withSource afterPost
              ((model.source afterPost).overwrite? (model.source state))) =
          .ok afterLoop)
      (hFinal :
        afterFor =
          model.withSource afterLoop
            ((model.source afterLoop).overwrite? (model.source state))) :
      ForPostContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue
        afterBody afterPost afterFor

namespace ForPostContinuationRun

theorem loopAfterCondCase
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {loopFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {state stateAfterCondition : σ}
    {conditionValue : Frontend.Word}
    {afterBody afterPost afterFor : σ}
    (hNonzero : conditionValue ≠ EvmYul.UInt256.ofNat 0)
    (hBody :
      Yul.Source.Effectful.exec model prim loopFuel (.Block body)
          codeOverride stateAfterCondition =
        .ok afterBody)
    (hBodyContinues :
      Yul.Source.Effectful.LoopBodyContinues (model.source afterBody))
    (hPost :
      Yul.Source.Effectful.exec model prim loopFuel (.Block post)
          codeOverride
          (model.withSource afterBody
            (model.source afterBody).reviveJump) =
        .ok afterPost)
    (hRun :
      ForPostContinuationRun model prim loopFuel condition post body
        codeOverride state stateAfterCondition conditionValue
        afterBody afterPost afterFor) :
    Yul.Source.Effectful.LoopAfterCondCase model prim loopFuel
      condition post body codeOverride (model.source state)
      stateAfterCondition conditionValue afterFor := by
  cases hRun with
  | postOutOfFuel hPostSource hFinal =>
      exact
        .postOutOfFuel hNonzero hBody hBodyContinues
          hPost hPostSource hFinal
  | postLeave hPostSource hFinal =>
      exact
        .postLeave hNonzero hBody hBodyContinues
          hPost hPostSource hFinal
  | recurse hPostRecurs hLoop hFinal =>
      exact
        .recurse hNonzero hBody hBodyContinues
          hPost hPostRecurs hLoop hFinal

end ForPostContinuationRun

/-- Executed `.For` context whose post block contains the focused generated-call
occurrence.  The nested post run supplies the exact post block execution used by
the loop continuation case. -/
structure ForPostContextRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (condition : Frontend.AstExpr)
    (post body : List Frontend.AstStmt)
    (state : σ) where
  stateAfterCondition : σ
  conditionValue : Frontend.Word
  afterBody : σ
  postRun :
    StmtListOccurrenceRun hEvidence model prim prefixFuel post
      (model.withSource afterBody
        (model.source afterBody).reviveJump)
  hEval :
    Yul.Source.Effectful.eval model prim
        (((prefixFuel + 1) + postRun.pre.length) + 1)
        condition (some ordered.program.contract)
        (model.withSource state
          (EvmYul.Yul.State.mkOk (model.source state))) =
      .ok (stateAfterCondition, conditionValue)
  hNonzero :
    conditionValue ≠ EvmYul.UInt256.ofNat 0
  hBody :
    Yul.Source.Effectful.exec model prim
        (((prefixFuel + 1) + postRun.pre.length) + 1)
        (.Block body)
        (some ordered.program.contract) stateAfterCondition =
      .ok afterBody
  hBodyContinues :
    Yul.Source.Effectful.LoopBodyContinues (model.source afterBody)
  afterPost : σ
  hAfterPost :
    afterPost =
      model.withSource postRun.afterRest
        ((model.source postRun.afterRest).restrictStoreTo
          (model.source
            (model.withSource afterBody
              (model.source afterBody).reviveJump)).store)
  afterFor : σ
  hContinuation :
    ForPostContinuationRun model prim
      (((prefixFuel + 1) + postRun.pre.length) + 1)
      condition post body (some ordered.program.contract)
      state stateAfterCondition conditionValue afterBody afterPost afterFor

namespace ForPostContextRun

def ofSplitFocused
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state stateAfterCondition afterBody : σ}
    {conditionValue : Frontend.Word}
    {afterFor : σ}
    (postRun :
      StmtListOccurrenceRun.SplitFocusedRun hEvidence model prim
        prefixFuel post
        (model.withSource afterBody
          (model.source afterBody).reviveJump))
    (hEval :
      Yul.Source.Effectful.eval model prim
          (((prefixFuel + 1) + postRun.pre.length) + 1)
          condition (some ordered.program.contract)
          (model.withSource state
            (EvmYul.Yul.State.mkOk (model.source state))) =
        .ok (stateAfterCondition, conditionValue))
    (hNonzero :
      conditionValue ≠ EvmYul.UInt256.ofNat 0)
    (hBody :
      Yul.Source.Effectful.exec model prim
          (((prefixFuel + 1) + postRun.pre.length) + 1)
          (.Block body)
          (some ordered.program.contract) stateAfterCondition =
        .ok afterBody)
    (hBodyContinues :
      Yul.Source.Effectful.LoopBodyContinues (model.source afterBody))
    (hContinuation :
      ForPostContinuationRun model prim
        (((prefixFuel + 1) + postRun.pre.length) + 1)
        condition post body (some ordered.program.contract)
        state stateAfterCondition conditionValue afterBody
        (model.withSource postRun.afterRest
          ((model.source postRun.afterRest).restrictStoreTo
            (model.source
              (model.withSource afterBody
                (model.source afterBody).reviveJump)).store))
        afterFor) :
    ForPostContextRun hEvidence model prim prefixFuel
      condition post body state where
  stateAfterCondition := stateAfterCondition
  conditionValue := conditionValue
  afterBody := afterBody
  postRun := postRun.toStmtListOccurrenceRun
  hEval := hEval
  hNonzero := hNonzero
  hBody := hBody
  hBodyContinues := hBodyContinues
  afterPost :=
    model.withSource postRun.afterRest
      ((model.source postRun.afterRest).restrictStoreTo
        (model.source
          (model.withSource afterBody
            (model.source afterBody).reviveJump)).store)
  hAfterPost := rfl
  afterFor := afterFor
  hContinuation := hContinuation

theorem context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForPostContextRun hEvidence model prim prefixFuel
        condition post body state) :
    YulOccurrence.StmtUserCall.Context (.For condition post body)
      hEvidence.generated hEvidence.yulArgs :=
  .forPost hRun.postRun.occurrence

theorem postBlock
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForPostContextRun hEvidence model prim prefixFuel
        condition post body state) :
    Yul.Source.Effectful.exec model prim
        (((prefixFuel + 1) + hRun.postRun.pre.length) + 1)
        (.Block post)
        (some ordered.program.contract)
        (model.withSource hRun.afterBody
          (model.source hRun.afterBody).reviveJump) =
      .ok hRun.afterPost := by
  have hPostSeq := hRun.postRun.execSeq
  have hBlock :=
    Yul.Source.Effectful.exec_block_of_execSeq model prim hPostSeq
  rw [hRun.hAfterPost]
  exact hBlock

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForPostContextRun hEvidence model prim prefixFuel
        condition post body state) :
    Yul.Source.Effectful.exec model prim
        ((((((prefixFuel + 1) + hRun.postRun.pre.length) + 1) + 1) + 1) + 1)
        (.For condition post body)
        (some ordered.program.contract) state =
      .ok hRun.afterFor := by
  have hCase :=
    ForPostContinuationRun.loopAfterCondCase
      hRun.hNonzero hRun.hBody hRun.hBodyContinues
      hRun.postBlock hRun.hContinuation
  have hLoop :
      Yul.Source.Effectful.loop model prim
          ((((prefixFuel + 1) + hRun.postRun.pre.length) + 1) + 1 + 1)
          condition post body (some ordered.program.contract) state =
        .ok hRun.afterFor :=
    Yul.Source.Effectful.loop_of_eval_after_cond_case
      model prim hRun.hEval hCase
  exact Yul.Source.Effectful.exec_for_of_loop model prim hLoop

def focusedStmt
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {condition : Frontend.AstExpr}
    {post body : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ForPostContextRun hEvidence model prim prefixFuel
        condition post body state) :
    FocusedStmtRun hEvidence model prim state
      ((((((prefixFuel + 1) + hRun.postRun.pre.length) + 1) + 1) + 1) + 1)
      (.For condition post body) hRun.afterFor :=
  .context hRun.context hRun.exec

end ForPostContextRun

/-- Semantic interface for one executed nested statement/control context that
contains the focused generated-call occurrence. -/
inductive ContextStmtRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (state : σ) :
    Nat → Frontend.AstStmt → σ → Prop where
  | block
      {prefixFuel : Nat}
      {body : List Frontend.AstStmt}
      (hRun :
        BlockContextRun hEvidence model prim prefixFuel body state) :
      ContextStmtRun hEvidence model prim state
        (((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1)
        (.Block body) hRun.afterBlock
  | switch
      {prefixFuel : Nat}
      {scrutinee : Frontend.AstExpr}
      {cases : List (Frontend.Word × List Frontend.AstStmt)}
      {defaultBody selectedBody : List Frontend.AstStmt}
      (hRun :
        SwitchContextRun hEvidence model prim prefixFuel
          scrutinee cases defaultBody selectedBody state) :
      ContextStmtRun hEvidence model prim state
        ((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1)
        (.Switch scrutinee cases defaultBody) hRun.afterSwitch
  | ifBody
      {prefixFuel : Nat}
      {condition : Frontend.AstExpr}
      {body : List Frontend.AstStmt}
      (hRun :
        IfContextRun hEvidence model prim prefixFuel condition body state) :
      ContextStmtRun hEvidence model prim state
        ((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1)
        (.If condition body) hRun.afterIf
  | forCondition
      {conditionFuel : Nat}
      {condition : Frontend.AstExpr}
      {post body : List Frontend.AstStmt}
      (hRun :
        ForConditionContextRun hEvidence model prim conditionFuel
          condition post body state) :
      ContextStmtRun hEvidence model prim state
        ((conditionFuel + 1 + 1) + 1)
        (.For condition post body) hRun.afterFor
  | forBody
      {prefixFuel : Nat}
      {condition : Frontend.AstExpr}
      {post body : List Frontend.AstStmt}
      (hRun :
        ForBodyContextRun hEvidence model prim prefixFuel
          condition post body state) :
      ContextStmtRun hEvidence model prim state
        ((((((prefixFuel + 1) + hRun.bodyRun.pre.length) + 1) + 1) + 1) + 1)
        (.For condition post body) hRun.afterFor
  | forPost
      {prefixFuel : Nat}
      {condition : Frontend.AstExpr}
      {post body : List Frontend.AstStmt}
      (hRun :
        ForPostContextRun hEvidence model prim prefixFuel
          condition post body state) :
      ContextStmtRun hEvidence model prim state
        ((((((prefixFuel + 1) + hRun.postRun.pre.length) + 1) + 1) + 1) + 1)
        (.For condition post body) hRun.afterFor

namespace ContextStmtRun

private theorem stmtUserCall_of_context
    {stmt : Frontend.AstStmt}
    {generated : Frontend.Name}
    {args : List Frontend.AstExpr}
    (hContext :
      YulOccurrence.StmtUserCall.Context stmt generated args) :
    YulOccurrence.StmtUserCall stmt generated args := by
  cases hContext with
  | block hBody =>
      exact .block hBody
  | switchCase hCases =>
      exact .switchCase hCases
  | switchDefault hDefault =>
      exact .switchDefault hDefault
  | forCondition hCondition =>
      exact .forCondition hCondition
  | forPost hPost =>
      exact .forPost hPost
  | forBody hBody =>
      exact .forBody hBody
  | ifBody hBody =>
      exact .ifBody hBody

theorem context
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      ContextStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    YulOccurrence.StmtUserCall.Context stmt
      hEvidence.generated hEvidence.yulArgs := by
  cases hRun with
  | block hBlock =>
      exact hBlock.context
  | switch hSwitch =>
      exact hSwitch.context
  | ifBody hIf =>
      exact hIf.context
  | forCondition hFor =>
      exact hFor.context
  | forBody hFor =>
      exact hFor.context
  | forPost hFor =>
      exact hFor.context

theorem occurrence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      ContextStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    YulOccurrence.StmtUserCall stmt
      hEvidence.generated hEvidence.yulArgs :=
  stmtUserCall_of_context hRun.context

theorem exec
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      ContextStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    Yul.Source.Effectful.exec model prim fuel stmt
        (some ordered.program.contract) state =
      .ok afterStmt := by
  cases hRun with
  | block hBlock =>
      exact hBlock.exec
  | switch hSwitch =>
      exact hSwitch.exec
  | ifBody hIf =>
      exact hIf.exec
  | forCondition hFor =>
      exact hFor.exec
  | forBody hFor =>
      exact hFor.exec
  | forPost hFor =>
      exact hFor.exec

def focusedStmt
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {state : σ}
    {fuel : Nat}
    {stmt : Frontend.AstStmt}
    {afterStmt : σ}
    (hRun :
      ContextStmtRun hEvidence model prim state
        fuel stmt afterStmt) :
    FocusedStmtRun hEvidence model prim state fuel stmt afterStmt :=
  .context hRun.context hRun.exec

end ContextStmtRun

/-- Statement-list occurrence execution package for the nested-context branch.

This mirrors the direct and one-step outer-argument occurrence packages, but
all nested statement/control forms are consumed through `ContextStmtRun`. -/
structure ContextStmtListOccurrenceRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (stmts : List Frontend.AstStmt)
    (state : σ) where
  pre : List Frontend.AstStmt
  stmt : Frontend.AstStmt
  rest : List Frontend.AstStmt
  hSplit : stmts = pre ++ stmt :: rest
  stateBeforeStmt : σ
  afterStmt : σ
  afterRest : σ
  prefixShared : EvmYul.SharedState .Yul
  prefixVars : EvmYul.Yul.VarStore
  stmtShared : EvmYul.SharedState .Yul
  stmtVars : EvmYul.Yul.VarStore
  hPrefix :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + pre.length) pre
        (some ordered.program.contract) state =
      .ok stateBeforeStmt
  hPrefixSource :
    model.source stateBeforeStmt = .Ok prefixShared prefixVars
  hStmt :
    ContextStmtRun hEvidence model prim stateBeforeStmt
      prefixFuel stmt afterStmt
  hStmtSource :
    model.source afterStmt = .Ok stmtShared stmtVars
  hRest :
    Yul.Source.Effectful.execSeq model prim prefixFuel rest
        (some ordered.program.contract) afterStmt =
      .ok afterRest

namespace ContextStmtListOccurrenceRun

theorem execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ContextStmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + hRun.pre.length) stmts
        (some ordered.program.contract) state =
      .ok hRun.afterRest :=
  FocusedStmtRun.execSeq_of_split
    hRun.hSplit hRun.hPrefix hRun.hPrefixSource
    hRun.hStmt.focusedStmt hRun.hStmtSource hRun.hRest

end ContextStmtListOccurrenceRun

namespace StmtListOccurrenceRun

def ofContext
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {stmts : List Frontend.AstStmt}
    {state : σ}
    (hRun :
      ContextStmtListOccurrenceRun hEvidence model prim
        prefixFuel stmts state) :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel stmts state where
  pre := hRun.pre
  stmt := hRun.stmt
  rest := hRun.rest
  hSplit := hRun.hSplit
  hOccurrence := hRun.hStmt.occurrence
  stateBeforeStmt := hRun.stateBeforeStmt
  afterStmt := hRun.afterStmt
  afterRest := hRun.afterRest
  prefixShared := hRun.prefixShared
  prefixVars := hRun.prefixVars
  stmtShared := hRun.stmtShared
  stmtVars := hRun.stmtVars
  hPrefix := hRun.hPrefix
  hPrefixSource := hRun.hPrefixSource
  hStmt := hRun.hStmt.focusedStmt
  hStmtSource := hRun.hStmtSource
  hRest := hRun.hRest

end StmtListOccurrenceRun

/-- A lowered Yul statement-list body selected by the occurrence route stored
in `AlphaRenamedLocalCallYulEvidence`.

The lowerable route is the ordinary caller body. The stub route is a retained
nested-function body whose lowered Yul function entry is emitted separately.
Both cases carry the concrete statement-list occurrence needed by the generic
semantic statement-list interface. -/
inductive BodyRoute
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName) :
    List Frontend.AstStmt → Prop where
  | lowerable
      {topFn : Frontend.FunctionDef}
      {topYulBody : List Frontend.AstStmt}
      (hTopMem : (topName, topFn) ∈ object.functions)
      (hLowerable :
        FrontendOccurrence.LowerableStmtListUserCall
          topFn.body hEvidence.generated hEvidence.frontArgs)
      (hTopYul :
        Frontend.Stmt.List.toYul? topFn.body = some topYulBody)
      (hOccurrence :
        YulOccurrence.StmtListUserCall topYulBody
          hEvidence.generated hEvidence.yulArgs)
      (hEntry :
        (topName,
          EvmYul.Yul.Ast.FunctionDefinition.Def
            topFn.params topFn.returns topYulBody) ∈
          ordered.functionEntries) :
      BodyRoute hEvidence topYulBody
  | stub
      {topFn : Frontend.FunctionDef}
      {stubName : Frontend.Name}
      {params returns : List Frontend.Name}
      {body : List Frontend.Stmt}
      {yulBody : List Frontend.AstStmt}
      (hTopMem : (topName, topFn) ∈ object.functions)
      (hStub :
        FrontendOccurrence.StubBodyStmtListUserCall
          topFn.body hEvidence.generated hEvidence.frontArgs)
      (hYul :
        Frontend.Stmt.List.toYul? body = some yulBody)
      (hEntry :
        ordered.functionEntries.contains
          (stubName,
            EvmYul.Yul.Ast.FunctionDefinition.Def
              params returns yulBody) = true)
      (hOccurrence :
        YulOccurrence.StmtListUserCall yulBody
          hEvidence.generated hEvidence.yulArgs) :
      BodyRoute hEvidence yulBody

namespace BodyRoute

theorem exists_of_routes
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName) :
    ∃ (yulBody : List Frontend.AstStmt),
      BodyRoute hEvidence yulBody := by
  rcases hEvidence.routes with hLowerable | hStub
  · rcases hLowerable with
      ⟨topFn, topYulBody, hTopMem, hLowerable, hTopYul,
        hOccurrence, hEntry⟩
    exact
      ⟨topYulBody,
        BodyRoute.lowerable
          hTopMem hLowerable hTopYul hOccurrence hEntry⟩
  · rcases hStub with
      ⟨topFn, stubName, params, returns, body, yulBody,
        hTopMem, hStubBody, hYul, hEntry, hOccurrence⟩
    exact
      ⟨yulBody,
        BodyRoute.stub
          hTopMem hStubBody hYul hEntry hOccurrence⟩

theorem occurrence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {yulBody : List Frontend.AstStmt}
    (hRoute : BodyRoute hEvidence yulBody) :
    YulOccurrence.StmtListUserCall yulBody
      hEvidence.generated hEvidence.yulArgs := by
  cases hRoute with
  | lowerable _ _ _ hOccurrence _ =>
      exact hOccurrence
  | stub _ _ _ _ hOccurrence =>
      exact hOccurrence

end BodyRoute

/-- Compiler-derived route evidence for an alpha-renamed local call.

This keeps the generated Yul evidence and its selected lowerable/stub body
route together, so later public theorems do not need to expose or replay the
route disjunction stored in `AlphaRenamedLocalCallYulEvidence.routes`. -/
structure BodyRouteEvidence
    (object : Frontend.Object)
    (ordered : Yul.OrderedProgram)
    (topName : Frontend.Name) where
  yulEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName
  yulBody : List Frontend.AstStmt
  route : BodyRoute yulEvidence yulBody

namespace BodyRouteEvidence

theorem ofYulEvidence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName) :
    Nonempty (BodyRouteEvidence object ordered topName) := by
  rcases BodyRoute.exists_of_routes hEvidence with
    ⟨yulBody, hRoute⟩
  exact
    ⟨{ yulEvidence := hEvidence
       yulBody := yulBody
       route := hRoute }⟩

theorem occurrence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : BodyRouteEvidence object ordered topName) :
    YulOccurrence.StmtListUserCall hEvidence.yulBody
      hEvidence.yulEvidence.generated hEvidence.yulEvidence.yulArgs :=
  hEvidence.route.occurrence

end BodyRouteEvidence

/-- Bundled semantic interface for one focused generated local-call occurrence.

This is the small proof handle that later recursive statement/list
preservation should consume.  It keeps together the compiler-derived generated
callee and body route (`BodyRouteEvidence`) with the dynamic Yul execution of
that generated call (`GeneratedCallRun`): argument evaluation, callee-body
execution, revive/store-restored return state, returned values, and the
resulting `evalValues`/`eval` facts. -/
structure FocusedGeneratedCallRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (bodyFuel : Nat)
    (state : σ) where
  routeEvidence : BodyRouteEvidence object ordered topName
  run :
    GeneratedCallRun routeEvidence.yulEvidence model prim bodyFuel state

namespace FocusedGeneratedCallRun

def of_parts
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {state stateAfterArgs stateAfterBody : σ}
    {reversedValues : List Frontend.Word}
    (routeEvidence : BodyRouteEvidence object ordered topName)
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          routeEvidence.yulEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block routeEvidence.yulEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                routeEvidence.yulEvidence.localFn.params
                routeEvidence.yulEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody) :
    FocusedGeneratedCallRun (object := object) (ordered := ordered)
      (topName := topName) model prim bodyFuel state where
  routeEvidence := routeEvidence
  run :=
    generatedCallRun_of_parts routeEvidence.yulEvidence
      model prim hArgs hBody

theorem route_occurrence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state) :
    YulOccurrence.StmtListUserCall hRun.routeEvidence.yulBody
      hRun.routeEvidence.yulEvidence.generated
      hRun.routeEvidence.yulEvidence.yulArgs :=
  hRun.routeEvidence.occurrence

theorem evalValues
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state) :
    Yul.Source.Effectful.evalValues model prim (bodyFuel + 2)
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)
        (some ordered.program.contract) state =
      .ok (hRun.run.postState, hRun.run.returns) :=
  hRun.run.hEvalValues

theorem eval
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state) :
    Yul.Source.Effectful.eval model prim (bodyFuel + 2)
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)
        (some ordered.program.contract) state =
      .ok (hRun.run.postState, hRun.run.returns.head!) :=
  hRun.run.hEval

def focusedExpr
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state) :
    FocusedExprRun hRun.routeEvidence.yulEvidence model prim
      (bodyFuel + 2)
      (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
        hRun.routeEvidence.yulEvidence.yulArgs)
      state :=
  FocusedExprRun.ofGenerated hRun.run

end FocusedGeneratedCallRun

namespace DirectIncomingStmtRun

def assignOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    {names : List Frontend.Name}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hCheck :
      EvmYul.Yul.checkAssignment (model.source state) names = .ok ()) :
    DirectIncomingStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.Assign names
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs))
      (model.multifill names hRun.run.postState hRun.run.returns) :=
  .assign hCheck hRun.evalValues

def letOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    {names : List Frontend.Name}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ()) :
    DirectIncomingStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.Let names
        (some (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)))
      (model.multifill names hRun.run.postState hRun.run.returns) :=
  .letValue hCheck hRun.evalValues

def ifFalseOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    {ifBody : List Frontend.AstStmt}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hZero :
      hRun.run.returns.head! = EvmYul.UInt256.ofNat 0) :
    DirectIncomingStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.If
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)
        ifBody)
      hRun.run.postState :=
  .ifFalse hRun.eval hZero

def ifTrueOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state final : σ}
    {ifBody : List Frontend.AstStmt}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hNonzero :
      hRun.run.returns.head! ≠ EvmYul.UInt256.ofNat 0)
    (hIfBody :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block ifBody)
          (some ordered.program.contract) hRun.run.postState =
        .ok final) :
    DirectIncomingStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.If
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)
        ifBody)
      final :=
  .ifTrue hRun.eval hNonzero hIfBody

def switchOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state final : σ}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody : List Frontend.AstStmt}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hSelected :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block
            (EvmYul.Yul.selectSwitchCase
              hRun.run.returns.head! defaultBody cases))
          (some ordered.program.contract) hRun.run.postState =
        .ok final) :
    DirectIncomingStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.Switch
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)
        cases defaultBody)
      final :=
  .switch hRun.eval hSelected

end DirectIncomingStmtRun

namespace FocusedStmtRun

def assignOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    {names : List Frontend.Name}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hCheck :
      EvmYul.Yul.checkAssignment (model.source state) names = .ok ()) :
    FocusedStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.Assign names
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs))
      (model.multifill names hRun.run.postState hRun.run.returns) :=
  .direct .assignmentValue
    (DirectIncomingStmtRun.assignOfFocusedGenerated hRun hCheck)

def letOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    {names : List Frontend.Name}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ()) :
    FocusedStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.Let names
        (some (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)))
      (model.multifill names hRun.run.postState hRun.run.returns) :=
  .direct .letValue
    (DirectIncomingStmtRun.letOfFocusedGenerated hRun hCheck)

def ifFalseOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state : σ}
    {ifBody : List Frontend.AstStmt}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hZero :
      hRun.run.returns.head! = EvmYul.UInt256.ofNat 0) :
    FocusedStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.If
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)
        ifBody)
      hRun.run.postState :=
  .direct .ifCondition
    (DirectIncomingStmtRun.ifFalseOfFocusedGenerated hRun hZero)

def ifTrueOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state final : σ}
    {ifBody : List Frontend.AstStmt}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hNonzero :
      hRun.run.returns.head! ≠ EvmYul.UInt256.ofNat 0)
    (hIfBody :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block ifBody)
          (some ordered.program.contract) hRun.run.postState =
        .ok final) :
    FocusedStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.If
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)
        ifBody)
      final :=
  .direct .ifCondition
    (DirectIncomingStmtRun.ifTrueOfFocusedGenerated
      hRun hNonzero hIfBody)

def switchOfFocusedGenerated
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel : Nat}
    {state final : σ}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody : List Frontend.AstStmt}
    (hRun :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel state)
    (hSelected :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block
            (EvmYul.Yul.selectSwitchCase
              hRun.run.returns.head! defaultBody cases))
          (some ordered.program.contract) hRun.run.postState =
        .ok final) :
    FocusedStmtRun hRun.routeEvidence.yulEvidence model prim state
      ((bodyFuel + 2) + 1)
      (.Switch
        (.Call (.inr hRun.routeEvidence.yulEvidence.generated)
          hRun.routeEvidence.yulEvidence.yulArgs)
        cases defaultBody)
      final :=
  .direct .switchScrutinee
    (DirectIncomingStmtRun.switchOfFocusedGenerated hRun hSelected)

end FocusedStmtRun

/-- Semantic execution package for the concrete route body selected by
`AlphaRenamedLocalCallYulEvidence.routes`.

This is the route-level bridge from frontend/Yul occurrence evidence to the
generic statement-list run interface; later public theorems can consume this
single package rather than reopening lowerable and retained-stub routes. -/
structure BodyRouteRun
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    (prefixFuel : Nat)
    (state : σ) where
  yulBody : List Frontend.AstStmt
  route : BodyRoute hEvidence yulBody
  run :
    StmtListOccurrenceRun hEvidence model prim
      prefixFuel yulBody state

namespace BodyRouteRun

def ofSplitFocused
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {state : σ}
    {yulBody : List Frontend.AstStmt}
    (route : BodyRoute hEvidence yulBody)
    (hRun :
      StmtListOccurrenceRun.SplitFocusedRun hEvidence model prim
        prefixFuel yulBody state) :
    BodyRouteRun hEvidence model prim prefixFuel state where
  yulBody := yulBody
  route := route
  run := hRun.toStmtListOccurrenceRun

def ofFocusedGeneratedSplit
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {bodyFuel prefixFuel : Nat}
    {state generatedState : σ}
    (hFocused :
      FocusedGeneratedCallRun (object := object) (ordered := ordered)
        (topName := topName) model prim bodyFuel generatedState)
    (hRun :
      StmtListOccurrenceRun.SplitFocusedRun
        hFocused.routeEvidence.yulEvidence model prim
        prefixFuel hFocused.routeEvidence.yulBody state) :
    BodyRouteRun hFocused.routeEvidence.yulEvidence
      model prim prefixFuel state :=
  ofSplitFocused hFocused.routeEvidence.route hRun

def splitFocused
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {state : σ}
    (hRun :
      BodyRouteRun hEvidence model prim prefixFuel state) :
    StmtListOccurrenceRun.SplitFocusedRun hEvidence model prim
      prefixFuel hRun.yulBody state :=
  StmtListOccurrenceRun.SplitFocusedRun.ofStmtListOccurrenceRun hRun.run

theorem occurrence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {state : σ}
    (hRun :
      BodyRouteRun hEvidence model prim prefixFuel state) :
    YulOccurrence.StmtListUserCall hRun.yulBody
      hEvidence.generated hEvidence.yulArgs :=
  hRun.run.occurrence

theorem route_occurrence
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {state : σ}
    (hRun :
      BodyRouteRun hEvidence model prim prefixFuel state) :
    YulOccurrence.StmtListUserCall hRun.yulBody
      hEvidence.generated hEvidence.yulArgs :=
  hRun.route.occurrence

theorem execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {state : σ}
    (hRun :
      BodyRouteRun hEvidence model prim prefixFuel state) :
    Yul.Source.Effectful.execSeq model prim
        ((prefixFuel + 1) + hRun.run.pre.length) hRun.yulBody
        (some ordered.program.contract) state =
      .ok hRun.run.afterRest :=
  hRun.run.execSeq

theorem classified_split_execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {state : σ}
    (hRun :
      BodyRouteRun hEvidence model prim prefixFuel state) :
    ∃ (pre : List Frontend.AstStmt)
        (stmt : Frontend.AstStmt)
        (rest : List Frontend.AstStmt),
      hRun.yulBody = pre ++ stmt :: rest ∧
        (YulOccurrence.StmtIncomingUserCall.Direct stmt
            hEvidence.generated hEvidence.yulArgs ∨
          YulOccurrence.StmtIncomingUserCall.OuterArg stmt
              hEvidence.generated hEvidence.yulArgs ∨
            YulOccurrence.StmtUserCall.Context stmt
              hEvidence.generated hEvidence.yulArgs) ∧
        Yul.Source.Effectful.execSeq model prim
            ((prefixFuel + 1) + pre.length) hRun.yulBody
            (some ordered.program.contract) state =
          .ok hRun.run.afterRest :=
  hRun.run.classified_split_execSeq

theorem focused_split_execSeq
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    {hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName}
    {σ : Type}
    {model : Yul.Source.Effectful.StateModel σ}
    {prim : Yul.Source.Effectful.PrimitiveSemantics σ}
    {prefixFuel : Nat}
    {state : σ}
    (hRun :
      BodyRouteRun hEvidence model prim prefixFuel state) :
    ∃ (pre : List Frontend.AstStmt)
        (stmt : Frontend.AstStmt)
        (rest : List Frontend.AstStmt),
      hRun.yulBody = pre ++ stmt :: rest ∧
        YulOccurrence.StmtUserCall stmt
          hEvidence.generated hEvidence.yulArgs ∧
        Yul.Source.Effectful.execSeq model prim
            ((prefixFuel + 1) + pre.length) hRun.yulBody
            (some ordered.program.contract) state =
          .ok hRun.run.afterRest :=
  hRun.splitFocused.classified_split_execSeq

end BodyRouteRun

/-- Direct assignment statement execution for a generated alpha-renamed call
from the bundled Yul evidence. -/
theorem assign_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {names : List Frontend.Name}
    {state stateAfterArgs stateAfterBody : σ}
    {reversedValues : List Frontend.Word}
    (hCheck :
      EvmYul.Yul.checkAssignment (model.source state) names = .ok ())
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody) :
    Yul.Source.Effectful.exec model prim (bodyFuel + 3)
        (.Assign names (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs))
        (some ordered.program.contract) state =
      .ok
        (model.multifill names
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs)))
          (List.map (model.source stateAfterBody).lookup!
            hEvidence.localFn.returns)) :=
  Yul.Source.Effectful.exec_assign_of_evalValues model prim hCheck
    (hEvidence.evalValues_succ model prim hArgs hBody)

/-- Direct declaration statement execution for a generated alpha-renamed call
from the bundled Yul evidence. -/
theorem let_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {names : List Frontend.Name}
    {state stateAfterArgs stateAfterBody : σ}
    {reversedValues : List Frontend.Word}
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody) :
    Yul.Source.Effectful.exec model prim (bodyFuel + 3)
        (.Let names (some (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs)))
        (some ordered.program.contract) state =
      .ok
        (model.multifill names
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs)))
          (List.map (model.source stateAfterBody).lookup!
            hEvidence.localFn.returns)) :=
  Yul.Source.Effectful.exec_let_some_of_evalValues model prim hCheck
    (hEvidence.evalValues_succ model prim hArgs hBody)

/-- Direct expression-statement execution for a generated alpha-renamed call
from the bundled Yul evidence. -/
theorem exprStmt_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {state stateAfterArgs stateAfterBody : σ}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 2)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody) :
    Yul.Source.Effectful.exec model prim (bodyFuel + 3)
        (.ExprStmtCall (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs))
        (some ordered.program.contract) state =
      .ok
        (model.multifill []
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs)))
          (List.map (model.source stateAfterBody).lookup!
            hEvidence.localFn.returns)) := by
  have hCall :
      Yul.Source.Effectful.call model prim (bodyFuel + 1)
          reversedValues.reverse (some hEvidence.generated)
          (some ordered.program.contract) stateAfterArgs =
        .ok
          (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)),
            List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns) :=
    hEvidence.call_succ model prim hBody
  exact
    Yul.Source.Effectful.exec_expr_function_of_parts model prim hArgs hCall

/-- Sequence-head assignment execution for a generated alpha-renamed call from
the bundled Yul evidence. -/
theorem assign_seqHead_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {names : List Frontend.Name}
    {rest : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody afterRest : σ}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hCheck :
      EvmYul.Yul.checkAssignment (model.source state) names = .ok ())
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hSource :
      model.source
          (model.multifill names
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .Ok shared vars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract)
          (model.multifill names
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
        ((.Assign names (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs)) :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hStmt := hEvidence.assign_succ model prim hCheck hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt hSource hRest

/-- Sequence-head declaration execution for a generated alpha-renamed call from
the bundled Yul evidence. -/
theorem let_seqHead_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {names : List Frontend.Name}
    {rest : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody afterRest : σ}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hSource :
      model.source
          (model.multifill names
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .Ok shared vars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract)
          (model.multifill names
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
        ((.Let names (some (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs))) :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hStmt := hEvidence.let_succ model prim hCheck hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt hSource hRest

/-- Sequence-head expression-statement execution for a generated alpha-renamed
call from the bundled Yul evidence. -/
theorem exprStmt_seqHead_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {rest : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody afterRest : σ}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 2)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hSource :
      model.source
          (model.multifill []
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .Ok shared vars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract)
          (model.multifill []
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
        ((.ExprStmtCall (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs)) :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hStmt := hEvidence.exprStmt_succ model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt hSource hRest

/-- Prefix/tail assignment execution for a generated alpha-renamed call from
the bundled Yul evidence. -/
theorem assign_seqPrefix_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {names : List Frontend.Name}
    {pre rest : List Frontend.AstStmt}
    {state stateBeforeCall stateAfterArgs stateAfterBody afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((bodyFuel + 4) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeCall)
    (hPrefixSource :
      model.source stateBeforeCall = .Ok prefixShared prefixVars)
    (hCheck :
      EvmYul.Yul.checkAssignment
          (model.source stateBeforeCall) names = .ok ())
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeCall =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hStmtSource :
      model.source
          (model.multifill names
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract)
          (model.multifill names
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((bodyFuel + 4) + pre.length)
        (pre ++ ((.Assign names (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs)) :: rest))
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
          ((.Assign names (.Call (.inr hEvidence.generated)
            hEvidence.yulArgs)) :: rest)
          (some ordered.program.contract) stateBeforeCall =
        .ok afterRest :=
    hEvidence.assign_seqHead_succ model prim hCheck hArgs hBody
      hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := bodyFuel + 4) (pre := pre)
      (suffix :=
        (.Assign names (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs)) :: rest)
      hPrefix hPrefixSource hSuffix

/-- Prefix/tail declaration execution for a generated alpha-renamed call from
the bundled Yul evidence. -/
theorem let_seqPrefix_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {names : List Frontend.Name}
    {pre rest : List Frontend.AstStmt}
    {state stateBeforeCall stateAfterArgs stateAfterBody afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((bodyFuel + 4) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeCall)
    (hPrefixSource :
      model.source stateBeforeCall = .Ok prefixShared prefixVars)
    (hCheck :
      EvmYul.Yul.checkDeclaration
          (model.source stateBeforeCall) names = .ok ())
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeCall =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hStmtSource :
      model.source
          (model.multifill names
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract)
          (model.multifill names
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((bodyFuel + 4) + pre.length)
        (pre ++
          ((.Let names (some (.Call (.inr hEvidence.generated)
            hEvidence.yulArgs))) :: rest))
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
          ((.Let names (some (.Call (.inr hEvidence.generated)
            hEvidence.yulArgs))) :: rest)
          (some ordered.program.contract) stateBeforeCall =
        .ok afterRest :=
    hEvidence.let_seqHead_succ model prim hCheck hArgs hBody
      hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := bodyFuel + 4) (pre := pre)
      (suffix :=
        (.Let names (some (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs))) :: rest)
      hPrefix hPrefixSource hSuffix

/-- Prefix/tail expression-statement execution for a generated alpha-renamed
call from the bundled Yul evidence. -/
theorem exprStmt_seqPrefix_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {pre rest : List Frontend.AstStmt}
    {state stateBeforeCall stateAfterArgs stateAfterBody afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((bodyFuel + 4) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeCall)
    (hPrefixSource :
      model.source stateBeforeCall = .Ok prefixShared prefixVars)
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 2)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeCall =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hStmtSource :
      model.source
          (model.multifill []
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract)
          (model.multifill []
            (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)))
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns)) =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((bodyFuel + 4) + pre.length)
        (pre ++ ((.ExprStmtCall (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs)) :: rest))
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
          ((.ExprStmtCall (.Call (.inr hEvidence.generated)
            hEvidence.yulArgs)) :: rest)
          (some ordered.program.contract) stateBeforeCall =
        .ok afterRest :=
    hEvidence.exprStmt_seqHead_succ model prim hArgs hBody
      hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := bodyFuel + 4) (pre := pre)
      (suffix :=
        (.ExprStmtCall (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs)) :: rest)
      hPrefix hPrefixSource hSuffix

/-- Direct false-branch `if` execution for a generated alpha-renamed call from
the bundled Yul evidence. -/
theorem ifFalse_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {ifBody : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody : σ}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hZero :
      (List.map (model.source stateAfterBody).lookup!
          hEvidence.localFn.returns).head! = EvmYul.UInt256.ofNat 0) :
    Yul.Source.Effectful.exec model prim (bodyFuel + 3)
        (.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ifBody)
        (some ordered.program.contract) state =
      .ok
        (model.withSource stateAfterBody
          (((model.source stateAfterBody).reviveJump.overwrite?
              (model.source stateAfterArgs)).setStore
                (model.source stateAfterArgs))) := by
  have hEval := hEvidence.eval_succ model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.exec_if_false_of_eval model prim hEval hZero

/-- Direct true-branch `if` execution for a generated alpha-renamed call from
the bundled Yul evidence. -/
theorem ifTrue_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {ifBody : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody final : σ}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hNonzero :
      (List.map (model.source stateAfterBody).lookup!
          hEvidence.localFn.returns).head! ≠ EvmYul.UInt256.ofNat 0)
    (hIfBody :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block ifBody)
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok final) :
    Yul.Source.Effectful.exec model prim (bodyFuel + 3)
        (.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ifBody)
        (some ordered.program.contract) state =
      .ok final := by
  have hEval := hEvidence.eval_succ model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.exec_if_true_of_eval
      model prim hEval hNonzero hIfBody

/-- Direct `switch` execution for a generated alpha-renamed call from the
bundled Yul evidence. -/
theorem switch_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody final : σ}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hSelected :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block
            (EvmYul.Yul.selectSwitchCase
              (List.map (model.source stateAfterBody).lookup!
                hEvidence.localFn.returns).head!
              defaultBody cases))
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok final) :
    Yul.Source.Effectful.exec model prim (bodyFuel + 3)
        (.Switch (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          cases defaultBody)
        (some ordered.program.contract) state =
      .ok final := by
  have hEval := hEvidence.eval_succ model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.exec_switch_of_eval model prim hEval hSelected

/-- Sequence-head false-branch `if` execution for a generated alpha-renamed
call from the bundled Yul evidence. -/
theorem ifFalse_seqHead_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {ifBody rest : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody afterRest : σ}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hZero :
      (List.map (model.source stateAfterBody).lookup!
          hEvidence.localFn.returns).head! = EvmYul.UInt256.ofNat 0)
    (hSource :
      model.source
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .Ok shared vars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
        ((.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          ifBody) :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hStmt :=
    hEvidence.ifFalse_succ (ifBody := ifBody) model prim hArgs hBody hZero
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt hSource hRest

/-- Sequence-head true-branch `if` execution for a generated alpha-renamed call
from the bundled Yul evidence. -/
theorem ifTrue_seqHead_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {ifBody rest : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody afterIf afterRest : σ}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hNonzero :
      (List.map (model.source stateAfterBody).lookup!
          hEvidence.localFn.returns).head! ≠ EvmYul.UInt256.ofNat 0)
    (hIfBody :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block ifBody)
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok afterIf)
    (hSource : model.source afterIf = .Ok shared vars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract) afterIf =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
        ((.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          ifBody) :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hStmt :=
    hEvidence.ifTrue_succ (ifBody := ifBody) model prim hArgs hBody
      hNonzero hIfBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt hSource hRest

/-- Sequence-head `switch` execution for a generated alpha-renamed call from
the bundled Yul evidence. -/
theorem switch_seqHead_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody rest : List Frontend.AstStmt}
    {state stateAfterArgs stateAfterBody afterSwitch afterRest : σ}
    {shared : EvmYul.SharedState .Yul}
    {vars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) state =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hSelected :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block
            (EvmYul.Yul.selectSwitchCase
              (List.map (model.source stateAfterBody).lookup!
                hEvidence.localFn.returns).head!
              defaultBody cases))
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok afterSwitch)
    (hSource : model.source afterSwitch = .Ok shared vars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract) afterSwitch =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
        ((.Switch (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          cases defaultBody) :: rest)
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hStmt :=
    hEvidence.switch_succ model prim hArgs hBody hSelected
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.execSeq_cons_of_regular
      model prim hStmt hSource hRest

/-- Prefix/tail false-branch `if` execution for a generated alpha-renamed call
from the bundled Yul evidence. -/
theorem ifFalse_seqPrefix_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {ifBody pre rest : List Frontend.AstStmt}
    {state stateBeforeCall stateAfterArgs stateAfterBody afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((bodyFuel + 4) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeCall)
    (hPrefixSource :
      model.source stateBeforeCall = .Ok prefixShared prefixVars)
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeCall =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hZero :
      (List.map (model.source stateAfterBody).lookup!
          hEvidence.localFn.returns).head! = EvmYul.UInt256.ofNat 0)
    (hStmtSource :
      model.source
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((bodyFuel + 4) + pre.length)
        (pre ++ ((.If (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs) ifBody) :: rest))
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
          ((.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
            ifBody) :: rest)
          (some ordered.program.contract) stateBeforeCall =
        .ok afterRest :=
    hEvidence.ifFalse_seqHead_succ model prim hArgs hBody hZero
      hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := bodyFuel + 4) (pre := pre)
      (suffix :=
        (.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          ifBody) :: rest)
      hPrefix hPrefixSource hSuffix

/-- Prefix/tail true-branch `if` execution for a generated alpha-renamed call
from the bundled Yul evidence. -/
theorem ifTrue_seqPrefix_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {ifBody pre rest : List Frontend.AstStmt}
    {state stateBeforeCall stateAfterArgs stateAfterBody afterIf
      afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((bodyFuel + 4) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeCall)
    (hPrefixSource :
      model.source stateBeforeCall = .Ok prefixShared prefixVars)
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeCall =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hNonzero :
      (List.map (model.source stateAfterBody).lookup!
          hEvidence.localFn.returns).head! ≠ EvmYul.UInt256.ofNat 0)
    (hIfBody :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block ifBody)
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok afterIf)
    (hStmtSource : model.source afterIf = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract) afterIf =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((bodyFuel + 4) + pre.length)
        (pre ++ ((.If (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs) ifBody) :: rest))
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
          ((.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
            ifBody) :: rest)
          (some ordered.program.contract) stateBeforeCall =
        .ok afterRest :=
    hEvidence.ifTrue_seqHead_succ model prim hArgs hBody hNonzero
      hIfBody hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := bodyFuel + 4) (pre := pre)
      (suffix :=
        (.If (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          ifBody) :: rest)
      hPrefix hPrefixSource hSuffix

/-- Prefix/tail `switch` execution for a generated alpha-renamed call from the
bundled Yul evidence. -/
theorem switch_seqPrefix_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody pre rest : List Frontend.AstStmt}
    {state stateBeforeCall stateAfterArgs stateAfterBody afterSwitch
      afterRest : σ}
    {prefixShared stmtShared : EvmYul.SharedState .Yul}
    {prefixVars stmtVars : EvmYul.Yul.VarStore}
    {reversedValues : List Frontend.Word}
    (hPrefix :
      Yul.Source.Effectful.execSeq model prim
          ((bodyFuel + 4) + pre.length) pre
          (some ordered.program.contract) state =
        .ok stateBeforeCall)
    (hPrefixSource :
      model.source stateBeforeCall = .Ok prefixShared prefixVars)
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeCall =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hSelected :
      Yul.Source.Effectful.exec model prim (bodyFuel + 2)
          (.Block
            (EvmYul.Yul.selectSwitchCase
              (List.map (model.source stateAfterBody).lookup!
                hEvidence.localFn.returns).head!
              defaultBody cases))
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok afterSwitch)
    (hStmtSource : model.source afterSwitch = .Ok stmtShared stmtVars)
    (hRest :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 3)
          rest
          (some ordered.program.contract) afterSwitch =
        .ok afterRest) :
    Yul.Source.Effectful.execSeq model prim
        ((bodyFuel + 4) + pre.length)
        (pre ++ ((.Switch (.Call (.inr hEvidence.generated)
          hEvidence.yulArgs) cases defaultBody) :: rest))
        (some ordered.program.contract) state =
      .ok afterRest := by
  have hSuffix :
      Yul.Source.Effectful.execSeq model prim (bodyFuel + 4)
          ((.Switch (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
            cases defaultBody) :: rest)
          (some ordered.program.contract) stateBeforeCall =
        .ok afterRest :=
    hEvidence.switch_seqHead_succ model prim hArgs hBody hSelected
      hStmtSource hRest
  exact
    Yul.Source.Effectful.execSeq_append_of_regular_prefix
      model prim
      (fuel := bodyFuel + 4) (pre := pre)
      (suffix :=
        (.Switch (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          cases defaultBody) :: rest)
      hPrefix hPrefixSource hSuffix

/-- Primitive outer-call evaluation when the focused argument is the generated
alpha-renamed call described by the bundled Yul evidence. -/
theorem outerArgPrimitive_evalValues_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues outputs : List Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hPrim :
      prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          stateAfterOuterArgs outerPrim
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse =
        .ok (final, outputs)) :
    Yul.Source.Effectful.evalValues model prim
        ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
        (.Call (.inl outerPrim)
          (left ++
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
              right))
        (some ordered.program.contract) state =
      .ok (final, outputs) := by
  have hFocus :
      Yul.Source.Effectful.eval model prim ((bodyFuel + 1) + 1)
          (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          (some ordered.program.contract) stateBeforeFocus =
        .ok
          (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)),
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head!) := by
    simpa [Nat.add_assoc] using
      hEvidence.eval_succ model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.evalValues_primitive_split_focus_of_parts
      model prim
      (tailFuel := bodyFuel + 1) (prim := outerPrim)
      (left := left) (right := right)
      (focus := .Call (.inr hEvidence.generated) hEvidence.yulArgs)
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
          hEvidence.localFn.returns).head!)
      (outputs := outputs)
      (by omega) hRight hFocus hLeft hPrim

/-- User-function outer-call evaluation when the focused argument is the
generated alpha-renamed call described by the bundled Yul evidence. -/
theorem outerArgFunction_evalValues_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {functionName : Frontend.Name}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues outputs : List Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (final, outputs)) :
    Yul.Source.Effectful.evalValues model prim
        ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
        (.Call (.inr functionName)
          (left ++
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
              right))
        (some ordered.program.contract) state =
      .ok (final, outputs) := by
  have hFocus :
      Yul.Source.Effectful.eval model prim ((bodyFuel + 1) + 1)
          (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          (some ordered.program.contract) stateBeforeFocus =
        .ok
          (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)),
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head!) := by
    simpa [Nat.add_assoc] using
      hEvidence.eval_succ model prim hArgs hBody
  simpa [Nat.add_assoc] using
    Yul.Source.Effectful.evalValues_function_split_focus_of_parts
      model prim
      (tailFuel := bodyFuel + 1) (functionName := functionName)
      (left := left) (right := right)
      (focus := .Call (.inr hEvidence.generated) hEvidence.yulArgs)
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
          hEvidence.localFn.returns).head!)
      (outputs := outputs)
      (by omega) hRight hFocus hLeft hCall

/-- Single-value primitive outer-call evaluation for a generated alpha-renamed
focused argument from the bundled Yul evidence. -/
theorem outerArgPrimitive_eval_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues : List Frontend.Word}
    {value : Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hPrim :
      prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          stateAfterOuterArgs outerPrim
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse =
        .ok (final, [value])) :
    Yul.Source.Effectful.eval model prim
        ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
        (.Call (.inl outerPrim)
          (left ++
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
              right))
        (some ordered.program.contract) state =
      .ok (final, value) :=
  Yul.Source.Effectful.eval_of_evalValues_singleton model prim
    (hEvidence.outerArgPrimitive_evalValues_succ model prim
      hRight hArgs hBody hLeft hPrim)

/-- Single-value user-function outer-call evaluation for a generated
alpha-renamed focused argument from the bundled Yul evidence. -/
theorem outerArgFunction_eval_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {functionName : Frontend.Name}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues : List Frontend.Word}
    {value : Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (final, [value])) :
    Yul.Source.Effectful.eval model prim
        ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
        (.Call (.inr functionName)
          (left ++
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
              right))
        (some ordered.program.contract) state =
      .ok (final, value) :=
  Yul.Source.Effectful.eval_of_evalValues_singleton model prim
    (hEvidence.outerArgFunction_evalValues_succ model prim
      hRight hArgs hBody hLeft hCall)

/-- Assignment statement execution for a primitive outer call containing the
generated alpha-renamed call as one argument. -/
theorem assign_outerArgPrimitive_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
    {names : List Frontend.Name}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues outputs : List Frontend.Word}
    (hCheck :
      EvmYul.Yul.checkAssignment (model.source state) names = .ok ())
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hPrim :
      prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          stateAfterOuterArgs outerPrim
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse =
        .ok (final, outputs)) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.Assign names
          (.Call (.inl outerPrim)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right)))
        (some ordered.program.contract) state =
      .ok (model.multifill names final outputs) :=
  Yul.Source.Effectful.exec_assign_of_evalValues model prim hCheck
    (hEvidence.outerArgPrimitive_evalValues_succ model prim
      hRight hArgs hBody hLeft hPrim)

/-- Assignment statement execution for a user-function outer call containing
the generated alpha-renamed call as one argument. -/
theorem assign_outerArgFunction_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {functionName : Frontend.Name}
    {names : List Frontend.Name}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues outputs : List Frontend.Word}
    (hCheck :
      EvmYul.Yul.checkAssignment (model.source state) names = .ok ())
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (final, outputs)) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.Assign names
          (.Call (.inr functionName)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right)))
        (some ordered.program.contract) state =
      .ok (model.multifill names final outputs) :=
  Yul.Source.Effectful.exec_assign_of_evalValues model prim hCheck
    (hEvidence.outerArgFunction_evalValues_succ model prim
      hRight hArgs hBody hLeft hCall)

/-- Declaration statement execution for a primitive outer call containing the
generated alpha-renamed call as one argument. -/
theorem let_outerArgPrimitive_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
    {names : List Frontend.Name}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues outputs : List Frontend.Word}
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hPrim :
      prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          stateAfterOuterArgs outerPrim
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse =
        .ok (final, outputs)) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.Let names
          (some
            (.Call (.inl outerPrim)
              (left ++
                (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                  right))))
        (some ordered.program.contract) state =
      .ok (model.multifill names final outputs) :=
  Yul.Source.Effectful.exec_let_some_of_evalValues model prim hCheck
    (hEvidence.outerArgPrimitive_evalValues_succ model prim
      hRight hArgs hBody hLeft hPrim)

/-- Declaration statement execution for a user-function outer call containing
the generated alpha-renamed call as one argument. -/
theorem let_outerArgFunction_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {functionName : Frontend.Name}
    {names : List Frontend.Name}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues outputs : List Frontend.Word}
    (hCheck :
      EvmYul.Yul.checkDeclaration (model.source state) names = .ok ())
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (final, outputs)) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.Let names
          (some
            (.Call (.inr functionName)
              (left ++
                (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                  right))))
        (some ordered.program.contract) state =
      .ok (model.multifill names final outputs) :=
  Yul.Source.Effectful.exec_let_some_of_evalValues model prim hCheck
    (hEvidence.outerArgFunction_evalValues_succ model prim
      hRight hArgs hBody hLeft hCall)

/-- Expression-statement execution for a primitive outer call containing the
generated alpha-renamed call as one argument. -/
theorem exprStmt_outerArgPrimitive_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues outputs : List Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hPrim :
      prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          stateAfterOuterArgs outerPrim
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse =
        .ok (final, outputs)) :
    Yul.Source.Effectful.exec model prim
        ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
        (.ExprStmtCall
          (.Call (.inl outerPrim)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right)))
        (some ordered.program.contract) state =
      .ok (model.multifill [] final outputs) :=
  Yul.Source.Effectful.exec_expr_primitive_of_evalValues model prim
    (hEvidence.outerArgPrimitive_evalValues_succ model prim
      hRight hArgs hBody hLeft hPrim)

/-- Expression-statement execution for a user-function outer call containing
the generated alpha-renamed call as one argument. -/
theorem exprStmt_outerArgFunction_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {functionName : Frontend.Name}
    {left right : List Frontend.AstExpr}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs final : σ}
    {rightValues leftValues reversedValues outputs : List Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          (((bodyFuel + 1) + 1) + 2 * right.reverse.length)
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (final, outputs)) :
    Yul.Source.Effectful.exec model prim
        ((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 2)
        (.ExprStmtCall
          (.Call (.inr functionName)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right)))
        (some ordered.program.contract) state =
      .ok (model.multifill [] final outputs) := by
  have hFocus :
      Yul.Source.Effectful.eval model prim ((bodyFuel + 1) + 1)
          (.Call (.inr hEvidence.generated) hEvidence.yulArgs)
          (some ordered.program.contract) stateBeforeFocus =
        .ok
          (model.withSource stateAfterBody
              (((model.source stateAfterBody).reviveJump.overwrite?
                  (model.source stateAfterArgs)).setStore
                    (model.source stateAfterArgs)),
            (List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head!) := by
    simpa [Nat.add_assoc] using
      hEvidence.eval_succ model prim hArgs hBody
  have hOuterArgs :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          (left ++
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
              right).reverse
          (some ordered.program.contract) state =
        .ok
          (stateAfterOuterArgs,
            rightValues ++
              ((List.map (model.source stateAfterBody).lookup!
                hEvidence.localFn.returns).head! :: leftValues)) :=
    Yul.Source.Effectful.evalArgs_split_focus_of_parts
      model prim
      (tailFuel := bodyFuel + 1)
      (left := left) (right := right)
      (focus := .Call (.inr hEvidence.generated) hEvidence.yulArgs)
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
          hEvidence.localFn.returns).head!)
      (by omega) hRight hFocus hLeft
  have hOuterArgs' :
      Yul.Source.Effectful.evalArgs model prim
          ((((bodyFuel + 1) + 1) + 2 * right.reverse.length) + 1)
          (left ++
            (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
              right).reverse
          (some ordered.program.contract) state =
        .ok
          (stateAfterOuterArgs,
            rightValues ++
              ((List.map (model.source stateAfterBody).lookup!
                hEvidence.localFn.returns).head! :: leftValues)) := by
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
      (args :=
        left ++
          (.Call (.inr hEvidence.generated) hEvidence.yulArgs) :: right)
      (codeOverride := some ordered.program.contract)
      (state := state)
      (stateAfterArgs := stateAfterOuterArgs)
      (final := final)
      (reversedValues :=
        rightValues ++
          ((List.map (model.source stateAfterBody).lookup!
            hEvidence.localFn.returns).head! :: leftValues))
      (values := outputs)
      hOuterArgs' hCall

/-- False-branch `if` execution for a primitive outer call containing the
generated alpha-renamed call as one argument. -/
theorem ifFalse_outerArgPrimitive_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
    {left right : List Frontend.AstExpr}
    {ifBody : List Frontend.AstStmt}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterCond : σ}
    {rightValues leftValues reversedValues : List Frontend.Word}
    {condValue : Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hPrim :
      prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          stateAfterOuterArgs outerPrim
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse =
        .ok (stateAfterCond, [condValue]))
    (hZero : condValue = EvmYul.UInt256.ofNat 0) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.If
          (.Call (.inl outerPrim)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right))
          ifBody)
        (some ordered.program.contract) state =
      .ok stateAfterCond := by
  have hEval :=
    hEvidence.outerArgPrimitive_eval_succ model prim
      hRight hArgs hBody hLeft hPrim
  exact Yul.Source.Effectful.exec_if_false_of_eval model prim hEval hZero

/-- True-branch `if` execution for a primitive outer call containing the
generated alpha-renamed call as one argument. -/
theorem ifTrue_outerArgPrimitive_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
    {left right : List Frontend.AstExpr}
    {ifBody : List Frontend.AstStmt}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterCond final : σ}
    {rightValues leftValues reversedValues : List Frontend.Word}
    {condValue : Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hPrim :
      prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          stateAfterOuterArgs outerPrim
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse =
        .ok (stateAfterCond, [condValue]))
    (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
    (hIfBody :
      Yul.Source.Effectful.exec model prim
          ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
          (.Block ifBody)
          (some ordered.program.contract) stateAfterCond =
        .ok final) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.If
          (.Call (.inl outerPrim)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right))
          ifBody)
        (some ordered.program.contract) state =
      .ok final := by
  have hEval :=
    hEvidence.outerArgPrimitive_eval_succ model prim
      hRight hArgs hBody hLeft hPrim
  exact
    Yul.Source.Effectful.exec_if_true_of_eval model prim hEval hNonzero
      hIfBody

/-- False-branch `if` execution for a user-function outer call containing the
generated alpha-renamed call as one argument. -/
theorem ifFalse_outerArgFunction_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {functionName : Frontend.Name}
    {left right : List Frontend.AstExpr}
    {ifBody : List Frontend.AstStmt}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterCond : σ}
    {rightValues leftValues reversedValues : List Frontend.Word}
    {condValue : Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (stateAfterCond, [condValue]))
    (hZero : condValue = EvmYul.UInt256.ofNat 0) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.If
          (.Call (.inr functionName)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right))
          ifBody)
        (some ordered.program.contract) state =
      .ok stateAfterCond := by
  have hEval :=
    hEvidence.outerArgFunction_eval_succ model prim
      hRight hArgs hBody hLeft hCall
  exact Yul.Source.Effectful.exec_if_false_of_eval model prim hEval hZero

/-- True-branch `if` execution for a user-function outer call containing the
generated alpha-renamed call as one argument. -/
theorem ifTrue_outerArgFunction_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {functionName : Frontend.Name}
    {left right : List Frontend.AstExpr}
    {ifBody : List Frontend.AstStmt}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterCond final : σ}
    {rightValues leftValues reversedValues : List Frontend.Word}
    {condValue : Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (stateAfterCond, [condValue]))
    (hNonzero : condValue ≠ EvmYul.UInt256.ofNat 0)
    (hIfBody :
      Yul.Source.Effectful.exec model prim
          ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
          (.Block ifBody)
          (some ordered.program.contract) stateAfterCond =
        .ok final) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.If
          (.Call (.inr functionName)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right))
          ifBody)
        (some ordered.program.contract) state =
      .ok final := by
  have hEval :=
    hEvidence.outerArgFunction_eval_succ model prim
      hRight hArgs hBody hLeft hCall
  exact
    Yul.Source.Effectful.exec_if_true_of_eval model prim hEval hNonzero
      hIfBody

/-- `switch` execution for a primitive outer call containing the generated
alpha-renamed call as one argument. -/
theorem switch_outerArgPrimitive_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {outerPrim : EvmYul.Operation .Yul}
    {left right : List Frontend.AstExpr}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody : List Frontend.AstStmt}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterScrutinee final : σ}
    {rightValues leftValues reversedValues : List Frontend.Word}
    {scrutineeValue : Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hPrim :
      prim.eval (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          stateAfterOuterArgs outerPrim
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse =
        .ok (stateAfterScrutinee, [scrutineeValue]))
    (hSelected :
      Yul.Source.Effectful.exec model prim
          ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
          (.Block
            (EvmYul.Yul.selectSwitchCase
              scrutineeValue defaultBody cases))
          (some ordered.program.contract) stateAfterScrutinee =
        .ok final) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.Switch
          (.Call (.inl outerPrim)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right))
          cases defaultBody)
        (some ordered.program.contract) state =
      .ok final := by
  have hEval :=
    hEvidence.outerArgPrimitive_eval_succ model prim
      hRight hArgs hBody hLeft hPrim
  exact Yul.Source.Effectful.exec_switch_of_eval model prim hEval hSelected

/-- `switch` execution for a user-function outer call containing the generated
alpha-renamed call as one argument. -/
theorem switch_outerArgFunction_succ
    {object : Frontend.Object}
    {ordered : Yul.OrderedProgram}
    {topName : Frontend.Name}
    (hEvidence : AlphaRenamedLocalCallYulEvidence object ordered topName)
    {σ : Type}
    (model : Yul.Source.Effectful.StateModel σ)
    (prim : Yul.Source.Effectful.PrimitiveSemantics σ)
    {bodyFuel : Nat} {functionName : Frontend.Name}
    {left right : List Frontend.AstExpr}
    {cases : List (Frontend.Word × List Frontend.AstStmt)}
    {defaultBody : List Frontend.AstStmt}
    {state stateBeforeFocus stateAfterArgs stateAfterBody
      stateAfterOuterArgs stateAfterScrutinee final : σ}
    {rightValues leftValues reversedValues : List Frontend.Word}
    {scrutineeValue : Frontend.Word}
    (hRight :
      Yul.Source.Effectful.evalArgs model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          right.reverse
          (some ordered.program.contract) state =
        .ok (stateBeforeFocus, rightValues))
    (hArgs :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          hEvidence.yulArgs.reverse
          (some ordered.program.contract) stateBeforeFocus =
        .ok (stateAfterArgs, reversedValues))
    (hBody :
      Yul.Source.Effectful.exec model prim bodyFuel
          (.Block hEvidence.localYulBody)
          (some ordered.program.contract)
          (model.withSource stateAfterArgs
            (EvmYul.Yul.State.mkOk
              ((model.source stateAfterArgs).initcall
                hEvidence.localFn.params hEvidence.localFn.returns
                reversedValues.reverse))) =
        .ok stateAfterBody)
    (hLeft :
      Yul.Source.Effectful.evalArgs model prim (bodyFuel + 1)
          left.reverse
          (some ordered.program.contract)
          (model.withSource stateAfterBody
            (((model.source stateAfterBody).reviveJump.overwrite?
                (model.source stateAfterArgs)).setStore
                  (model.source stateAfterArgs))) =
        .ok (stateAfterOuterArgs, leftValues))
    (hCall :
      Yul.Source.Effectful.call model prim
          (((bodyFuel + 1) + 2) + 2 * right.reverse.length)
          (rightValues ++
            ((List.map (model.source stateAfterBody).lookup!
              hEvidence.localFn.returns).head! :: leftValues)).reverse
          (some functionName)
          (some ordered.program.contract) stateAfterOuterArgs =
        .ok (stateAfterScrutinee, [scrutineeValue]))
    (hSelected :
      Yul.Source.Effectful.exec model prim
          ((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1)
          (.Block
            (EvmYul.Yul.selectSwitchCase
              scrutineeValue defaultBody cases))
          (some ordered.program.contract) stateAfterScrutinee =
        .ok final) :
    Yul.Source.Effectful.exec model prim
        (((((bodyFuel + 1) + 2) + 2 * right.reverse.length) + 1) + 1)
        (.Switch
          (.Call (.inr functionName)
            (left ++
              (.Call (.inr hEvidence.generated) hEvidence.yulArgs) ::
                right))
          cases defaultBody)
        (some ordered.program.contract) state =
      .ok final := by
  have hEval :=
    hEvidence.outerArgFunction_eval_succ model prim
      hRight hArgs hBody hLeft hCall
  exact Yul.Source.Effectful.exec_switch_of_eval model prim hEval hSelected

end AlphaRenamedLocalCallYulEvidence

/-- The source-facing alpha-preservation relation supplies the compiler-derived
Yul evidence and selects the concrete lowered body route internally.

This is the route-level successor to the older public theorem family that
returned generated names plus a lowerable/stub occurrence-route disjunction. -/
theorem alphaRenamedLocalCallPreserved_bodyRouteEvidence
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
    Nonempty
      (AlphaRenamedLocalCallYulEvidence.BodyRouteEvidence
        object ordered topName) := by
  rcases alphaRenamedLocalCallPreserved_yulEvidence hAlpha hConvert with
    ⟨hEvidence⟩
  exact
    AlphaRenamedLocalCallYulEvidence.BodyRouteEvidence.ofYulEvidence
      hEvidence

/-- Raw-solc finite-prefix theorem with internally derived body-route evidence
for a source-local nested call.

The generated callee name, lowered arguments, and lowerable/stub body route are
kept inside `BodyRouteEvidence`. Consumers only provide the ordinary checked
ordered-Yul conversion of the decoded frontend object when they need to open
the route for a semantic statement-list proof. -/
theorem optimizedRawSolcIrToRawBytecode_sourceLocalFunction_noShadow_bodyRouteEvidence
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
        (∀ {ordered : Yul.OrderedProgram},
          program.object.toSolcYulOrderedProgram? = some ordered →
            Nonempty
              (AlphaRenamedLocalCallYulEvidence.BodyRouteEvidence
                program.object ordered topName)) ∧
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
  refine
    ⟨program, linkerSymbols, structuredFuel, hDecode, hLinker,
      hProgramCompile, hValid, ?_, hAccepted, hForward⟩
  intro ordered hConvert
  exact
    alphaRenamedLocalCallPreserved_bodyRouteEvidence
      hAlpha hConvert

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
