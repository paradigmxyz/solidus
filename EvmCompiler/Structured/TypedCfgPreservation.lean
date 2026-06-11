import EvmCompiler.Structured.TypedCfgPreservation.Core

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation

namespace Stmt

/--
Ambient-program form of straight-line statement preservation.
-/
theorem eventually_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRun : Structured.Code.runState code state = .ok final) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump regular final.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      let generated : TypedCfg.Block :=
        { label := entry
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jump regular }
      have hFind :
          cfg.findBlock? entry = some generated := by
        exact hBlocks generated (by simp [generated])
      refine ⟨1, ?_⟩
      simp [TypedCfg.Program.runN, TypedCfg.Program.step, hFind,
        generated, TypedCfg.Block.run, Code.runState_toCfg hType, hRun,
        Except.map, Bind.bind, Except.bind, TypedCfg.Block.runTerm]

/--
Straight-line statement compilation produces a compositional regular
execution certificate.
-/
theorem regular_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRun : Structured.Code.runState code state = .ok final) :
    RegularExecution result cfg entry regular state.evm final.evm := by
  have hEventually :=
    eventually_code_of_compileStmtFuel? hCompile hBlocks hRun
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      exact ⟨output, rfl, hEventually⟩

/--
Straight-line statement preservation under concrete return-token frames and
CFG-owned control counters.
-/
theorem preserves_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : code.FrameSafe)
    (hRun : Structured.Code.runState code source = .ok final) :
    RegularPreserves result cfg entry regular source final tokens := by
  intro target hRel
  rcases StateRel.runCode hFrameSafe hRun hRel with
    ⟨targetFinal, hTargetRun, hFinalRel⟩
  have hTargetRunState :
      Structured.Code.runState code (source.withEVM target) =
        .ok (source.withEVM targetFinal) := by
    simp [Structured.Code.runState, hTargetRun, RunState.withEVM,
      Bind.bind, Except.bind]
  refine ⟨targetFinal, ?_, hFinalRel⟩
  simpa [RunState.withEVM] using
    (regular_code_of_compileStmtFuel?
      hCompile hBlocks hTargetRunState)

/--
Straight-line statements satisfy the uniform outcome certificate.
-/
theorem outcome_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : code.FrameSafe)
    (hRun : Structured.Code.runState code source = .ok final) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source (Structured.Outcome.regular final) tokens := by
  have hExecution :=
    regular_code_of_compileStmtFuel? hCompile hBlocks hRun
  rcases hExecution with
    ⟨output, hFallthrough, _hEventually⟩
  apply OutcomeSimulation.Preserves.of_regular rfl
  · exact ⟨output, hFallthrough⟩
  · exact
      preserves_code_of_compileStmtFuel?
        hCompile hBlocks hFrameSafe hRun

/--
If the independent Structured condition evaluates to false, the compiled
conditional reaches the regular continuation without entering the body.
-/
theorem eventually_if_false_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCond :
      Structured.Code.runConditionState cond state = .ok (final, false)) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump regular final.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              apply BlocksInProgram.eventually_of_run hBlocks
                (block := generated)
              · simp [generated]
              · simpa [generated] using
                  (Code.run_jumpi_toCfg
                    (target := LabelSupply.label supply 0)
                    (fallthrough := regular) hType hCond)

/--
False conditional execution also produces a regular fragment certificate.
-/
theorem regular_if_false_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCond :
      Structured.Code.runConditionState cond state = .ok (final, false)) :
    RegularExecution result cfg entry regular state.evm final.evm := by
  have hEventually :=
    eventually_if_false_of_compileStmtFuel? hCompile hBlocks hCond
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              exact
                ⟨{ output with slots := output.slots.tail }, rfl,
                  hEventually⟩

/--
Relational false-branch preservation under concrete procedure frames.
-/
theorem preserves_if_false_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (final, false)) :
    RegularPreserves result cfg entry regular source final tokens := by
  intro target hRel
  rcases StateRel.runCondition hFrameSafe hCond hRel with
    ⟨targetFinal, hTargetCond, hFinalRel⟩
  refine ⟨targetFinal, ?_, hFinalRel⟩
  simpa [RunState.withEVM] using
    (regular_if_false_of_compileStmtFuel?
      hCompile hBlocks hTargetCond)

/--
The false conditional branch satisfies the uniform outcome certificate.
-/
theorem outcome_if_false_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (final, false)) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source (Structured.Outcome.regular final) tokens := by
  have hExecution :=
    regular_if_false_of_compileStmtFuel? hCompile hBlocks hCond
  rcases hExecution with
    ⟨output, hFallthrough, _hEventually⟩
  apply OutcomeSimulation.Preserves.of_regular rfl
  · exact ⟨output, hFallthrough⟩
  · exact
      preserves_if_false_of_compileStmtFuel?
        hCompile hBlocks hFrameSafe hCond

/--
True conditional execution composes the generated `jumpi` head with any
checked preservation result for the recursively compiled body.
-/
theorem eventually_if_true_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state final : RunState} {outcome : TypedCfg.Outcome}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCond :
      Structured.Code.runConditionState cond state = .ok (final, true))
    (hBodyEventually :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0) bodyInput regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        cfg.Eventually (LabelSupply.label supply 0) final.evm outcome) :
    cfg.Eventually entry state.evm outcome := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hHeadEventually :
                  cfg.Eventually entry state.evm
                    (.jump (LabelSupply.label supply 0) final.evm) := by
                apply BlocksInProgram.eventually_of_run hBlocks
                  (block := generated)
                · simp [generated]
                · simpa [generated] using
                    (Code.run_jumpi_toCfg
                      (target := LabelSupply.label supply 0)
                      (fallthrough := regular) hType hCond)
              have hBodyBlocks : BlocksInProgram bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              exact
                TypedCfg.Program.Eventually.bind_jump hHeadEventually
                  (hBodyEventually hBody hBodyBlocks)

/--
Regular true-branch execution produces the same regular fragment certificate
as false-branch execution, using the recursive body certificate only for its
semantic execution witness.
-/
theorem regular_if_true_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state afterCond final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCond :
      Structured.Code.runConditionState cond state =
        .ok (afterCond, true))
    (hBodyRegular :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0) bodyInput regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularExecution bodyResult cfg
          (LabelSupply.label supply 0) regular
          afterCond.evm final.evm) :
    RegularExecution result cfg entry regular state.evm final.evm := by
  have hEventually :
      cfg.Eventually entry state.evm
        (TypedCfg.Outcome.jump regular final.evm) :=
    eventually_if_true_of_compileStmtFuel? hCompile hBlocks hCond
      (by
        intro bodyInput bodyResult hBodyCompile hBodyBlocks
        rcases hBodyRegular hBodyCompile hBodyBlocks with
          ⟨output, hFallthrough, hBodyEventually⟩
        exact hBodyEventually)
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              exact
                ⟨{ output with slots := output.slots.tail }, rfl,
                  hEventually⟩

/--
Relational true-branch preservation composes the generated conditional head
with the recursively compiled body.
-/
theorem preserves_if_true_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterCond final : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (afterCond, true))
    (hBodyPreserves :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0) bodyInput regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg
          (LabelSupply.label supply 0) regular
          afterCond final tokens) :
    RegularPreserves result cfg entry regular source final tokens := by
  intro target hRel
  rcases StateRel.runCondition hFrameSafe hCond hRel with
    ⟨targetAfterCond, hTargetCond, hAfterCondRel⟩
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              have hBodyBlocks : BlocksInProgram bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              rcases
                  hBodyPreserves hBody hBodyBlocks
                    targetAfterCond hAfterCondRel with
                ⟨targetFinal, hBodyExecution, hFinalRel⟩
              rcases hBodyExecution with
                ⟨bodyOutput, hBodyFallthrough, hBodyEventually⟩
              let generated : TypedCfg.Block :=
                { label := entry
                  input := input
                  body := TypedCfgCompiler.Code.toCfg cond
                  output := output
                  term :=
                    .jumpi (LabelSupply.label supply 0) regular }
              have hHeadEventually :
                  cfg.Eventually entry target
                    (.jump (LabelSupply.label supply 0) targetAfterCond) := by
                apply BlocksInProgram.eventually_of_run hBlocks
                  (block := generated)
                · simp [generated]
                · simpa [generated, RunState.withEVM] using
                    (Code.run_jumpi_toCfg
                      (target := LabelSupply.label supply 0)
                      (fallthrough := regular) hType hTargetCond)
              refine ⟨targetFinal, ?_, hFinalRel⟩
              refine
                ⟨{ output with slots := output.slots.tail }, rfl, ?_⟩
              exact
                TypedCfg.Program.Eventually.bind_jump
                  hHeadEventually hBodyEventually

/--
Outcome-indexed true-branch preservation.

Unlike the historical regular-only theorem, the recursively compiled body may
produce any Structured outcome. The generated condition head is composed with
the body's shared outcome path.
-/
theorem outcome_if_true_of_compileStmtFuel?
    {compilerFuel : Nat} {cond : Structured.Code} {body : Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterCond : RunState} {outcome : Structured.Outcome}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.if_ cond body) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCalls : CallsInProgram result globalCalls)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (afterCond, true))
    (hBodyPreserves :
      ∀ {bodyInput : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (LabelSupply.label supply 0) bodyInput regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        CallsInProgram bodyResult globalCalls →
        OutcomeSimulation.Path cfg (LabelSupply.label supply 0)
          (OutcomeSimulation.Continuations.ofContext ctx regular)
          afterCond outcome tokens) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source outcome tokens := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg cond) input with
  | none =>
      simp [hType] at hCompile
  | some output =>
      cases hHead : output.slots.head? with
      | none =>
          simp [hType, hHead] at hCompile
      | some condition =>
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
                (supply + 1) (LabelSupply.label supply 0)
                { output with slots := output.slots.tail } regular with
          | none =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
          | some bodyResult =>
              simp [hType, hHead, TypedCfgCompiler.mkBlock?, hBody] at hCompile
              cases hCompile
              have hBodyBlocks : BlocksInProgram bodyResult cfg := by
                intro block hMem
                apply hBlocks block
                simp [hMem]
              have hBodyCalls : CallsInProgram bodyResult globalCalls := by
                intro site hMem
                apply hCalls site
                simpa using hMem
              refine ⟨?_, ?_⟩
              · intro target hRel
                rcases
                    StateRel.runCondition hFrameSafe hCond hRel with
                  ⟨targetAfterCond, hTargetCond, hAfterCondRel⟩
                let generated : TypedCfg.Block :=
                  { label := entry
                    input := input
                    body := TypedCfgCompiler.Code.toCfg cond
                    output := output
                    term :=
                      .jumpi (LabelSupply.label supply 0) regular }
                have hHeadEventually :
                    cfg.Eventually entry target
                      (.jump (LabelSupply.label supply 0)
                        targetAfterCond) := by
                  apply BlocksInProgram.eventually_of_run hBlocks
                    (block := generated)
                  · simp [generated]
                  · simpa [generated, RunState.withEVM] using
                      (Code.run_jumpi_toCfg
                        (target := LabelSupply.label supply 0)
                        (fallthrough := regular) hType hTargetCond)
                rcases
                    hBodyPreserves hBody hBodyBlocks hBodyCalls
                      targetAfterCond hAfterCondRel with
                  ⟨targetOutcome, hBodyEventually, hOutcomeRel⟩
                exact
                  ⟨targetOutcome,
                    TypedCfg.Program.Eventually.bind_jump
                      hHeadEventually hBodyEventually,
                    hOutcomeRel⟩
              · intro _hRegular
                exact
                  ⟨{ output with slots := output.slots.tail }, rfl⟩

/--
The straight-line statement compiler preserves the independent Structured
semantics and reaches its supplied regular continuation in one CFG block.
-/
theorem runN_code_of_compileStmtFuel?
    {fuel : Nat} {code : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {state final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.code code) ctx
        supply entry input regular = some result)
    (hRun : Structured.Code.runState code state = .ok final) :
    (resultProgram result entry).runN 1 entry state.evm =
      Except.ok (TypedCfg.Outcome.jump regular final.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg code) input with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
  | some output =>
      simp [TypedCfgCompiler.mkBlock?, hType] at hCompile
      cases hCompile
      simp [TypedCfg.Program.runN, TypedCfg.Program.step,
        resultProgram, TypedCfg.Program.findBlock?, TypedCfg.Block.run,
        Code.runState_toCfg hType, hRun, Except.map, Bind.bind, Except.bind,
        TypedCfg.Block.runTerm]

/--
Compiled `break` reaches the break continuation selected by the compiler
context.
-/
theorem eventually_brk_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hTarget : ctx.breakLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .brk ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump target state.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.jumpOrInvalid, hTarget,
    TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  apply BlocksInProgram.eventually_of_run hBlocks
    (block := generated)
  · simp [generated]
  · simp [generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]

/--
Compiled `continue` reaches the continue continuation selected by the compiler
context.
-/
theorem eventually_cont_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hTarget : ctx.continueLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .cont ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump target state.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.jumpOrInvalid, hTarget,
    TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  apply BlocksInProgram.eventually_of_run hBlocks
    (block := generated)
  · simp [generated]
  · simp [generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]

/--
Compiled `leave` reaches the procedure-exit continuation selected by the
compiler context.
-/
theorem eventually_leave_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hTarget : ctx.leaveLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .leave ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump target state.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.jumpOrInvalid, hTarget,
    TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump target }
  apply BlocksInProgram.eventually_of_run hBlocks
    (block := generated)
  · simp [generated]
  · simp [generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]

/--
The TypedCfg halt outcome records the state immediately before executing the
terminal EVM opcode. The lower-level Assembly simulation executes that opcode
when interpreting this outcome.
-/
theorem eventually_terminal_of_compileStmtFuel?
    {fuel : Nat} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.terminal kind) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.halt kind state.evm) := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .halt kind }
  apply BlocksInProgram.eventually_of_run hBlocks
    (block := generated)
  · simp [generated]
  · simp [generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, Bind.bind, Except.bind]

namespace Terminal

/--
Terminal execution preserves concrete return-token realization.

This is the exact local obligation needed because TypedCfg records the
pre-terminal state and the shared outcome contract relates the state after the
terminal EVM operation.
-/
def RelSafe (kind : Assembly.HaltKind) : Prop :=
  ∀ {source : RunState} {sourceFinal target : EVMState}
    {tokens : List Word},
    StateRel source tokens target →
      Structured.Terminal.step kind source.evm = .ok sourceFinal →
        ∃ targetFinal,
          Structured.Terminal.step kind target = .ok targetFinal ∧
            StateRel (source.withEVM sourceFinal) tokens targetFinal

end Terminal

/--
Compiled `break` satisfies the uniform abrupt-outcome certificate whenever the
source permission is realized by a compiler continuation.
-/
theorem outcome_brk_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {source : RunState} {tokens : List Word}
    (hTarget : ctx.breakLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .brk ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source (Structured.Outcome.brk source) tokens := by
  apply OutcomeSimulation.Preserves.of_path_of_nonregular
    (by simp)
  intro targetState hRel
  refine ⟨.jump target targetState, ?_, ?_⟩
  · simpa [RunState.withEVM] using
      (eventually_brk_of_compileStmtFuel?
        (state := source.withEVM targetState)
        hTarget hCompile hBlocks)
  · exact OutcomeSimulation.Rel.brk_iff.mpr ⟨hTarget, hRel⟩

/--
Compiled `continue` satisfies the uniform abrupt-outcome certificate whenever
the source permission is realized by a compiler continuation.
-/
theorem outcome_cont_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {source : RunState} {tokens : List Word}
    (hTarget : ctx.continueLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .cont ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source (Structured.Outcome.cont source) tokens := by
  apply OutcomeSimulation.Preserves.of_path_of_nonregular
    (by simp)
  intro targetState hRel
  refine ⟨.jump target targetState, ?_, ?_⟩
  · simpa [RunState.withEVM] using
      (eventually_cont_of_compileStmtFuel?
        (state := source.withEVM targetState)
        hTarget hCompile hBlocks)
  · exact OutcomeSimulation.Rel.cont_iff.mpr ⟨hTarget, hRel⟩

/--
Compiled `leave` satisfies the uniform abrupt-outcome certificate whenever the
source permission is realized by a compiler continuation.
-/
theorem outcome_leave_of_compileStmtFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry target regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {source : RunState} {tokens : List Word}
    (hTarget : ctx.leaveLabel? = some target)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) .leave ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source (Structured.Outcome.leave source) tokens := by
  apply OutcomeSimulation.Preserves.of_path_of_nonregular
    (by simp)
  intro targetState hRel
  refine ⟨.jump target targetState, ?_, ?_⟩
  · simpa [RunState.withEVM] using
      (eventually_leave_of_compileStmtFuel?
        (state := source.withEVM targetState)
        hTarget hCompile hBlocks)
  · exact OutcomeSimulation.Rel.leave_iff.mpr ⟨hTarget, hRel⟩

/--
Compiled terminal statements satisfy the uniform halt certificate under the
local return-token frame-safety contract.
-/
theorem outcome_terminal_of_compileStmtFuel?
    {fuel : Nat} {kind : Assembly.HaltKind}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {sourceFinal : EVMState}
    {tokens : List Word}
    (hSafe : Terminal.RelSafe kind)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (fuel + 1) (.terminal kind) ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hStep :
      Structured.Terminal.step kind source.evm = .ok sourceFinal) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source
      (Structured.Outcome.halt kind (source.withEVM sourceFinal))
      tokens := by
  apply OutcomeSimulation.Preserves.of_path_of_nonregular
    (by simp)
  intro target hRel
  rcases hSafe hRel hStep with
    ⟨targetFinal, hTargetStep, hFinalRel⟩
  refine ⟨.halt kind target, ?_, ?_⟩
  · simpa [RunState.withEVM] using
      (eventually_terminal_of_compileStmtFuel?
        (state := source.withEVM target) hCompile hBlocks)
  · exact
      OutcomeSimulation.Rel.halt_iff.mpr
        ⟨rfl, targetFinal, hTargetStep, tokens, hFinalRel⟩

end Stmt

namespace Switch

def testOutput (valueShape : TypedCfg.Shape) : TypedCfg.Shape :=
  { valueShape with slots := .word :: valueShape.slots }

def casesEntryLabel (base idx : Nat) :
    List (Word × Structured.Block) → Assembly.Label
  | [] => LabelSupply.label base 1
  | _ => TypedCfgCompiler.switchTestLabel base idx

def nextTestLabel (base idx : Nat)
    (rest : List (Word × Structured.Block)) : Assembly.Label :=
  casesEntryLabel base (idx + 1) rest

theorem testBody_type
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue : Word}
    (hHead : valueShape.slots.head? = some slot) :
    TypedCfg.Block.bodyType?
        [.dup 0, .push caseValue, .prim .eq] valueShape =
      some (testOutput valueShape) := by
  cases valueShape with
  | mk slots tail =>
      cases slots with
      | nil =>
          simp at hHead
      | cons head rest =>
          simp [TypedCfg.Block.bodyType?, TypedCfg.Instr.type?,
            TypedCfg.Shape.get?, TypedCfg.Shape.length,
            TypedCfg.Shape.pop, TypedCfg.Shape.pushWords,
            Assembly.PrimOp.stackArity?, Assembly.PrimOp.toEVM,
            EvmYul.EVM.δ, EvmYul.EVM.α, testOutput]

/--
One generated switch test preserves the retained scrutinee and chooses the
case-entry or next-test label according to the source value comparison.
-/
theorem eventually_test
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {testLabel caseLabel nextTest : Assembly.Label}
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue value : Word}
    {source : RunState} {tokens : List Word} {target : EVMState}
    {stack : EvmYul.Stack Word}
    (hBlocks : BlocksInProgram result cfg)
    (hMem :
      { label := testLabel
        input := valueShape
        body := [.dup 0, .push caseValue, .prim .eq]
        output := testOutput valueShape
        term := .jumpi caseLabel nextTest } ∈ result.blocks)
    (hHead : valueShape.slots.head? = some slot)
    (hRel : StateRel source tokens target)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    ∃ targetFinal,
      cfg.Eventually testLabel target
          (.jump
            (if caseValue = value then caseLabel else nextTest)
            targetFinal) ∧
        StateRel source tokens targetFinal := by
  let dupShape : TypedCfg.Shape :=
    { valueShape with slots := slot :: valueShape.slots }
  let pushShape : TypedCfg.Shape :=
    { dupShape with slots := .literal caseValue :: dupShape.slots }
  have hGet :
      valueShape.get? 0 = some slot := by
    rw [TypedCfg.Shape.get?, ← List.head?_eq_getElem?]
    exact hHead
  have hDupType :
      TypedCfg.Instr.type? (.dup 0) valueShape = some dupShape := by
    simp [TypedCfg.Instr.type?, hGet, dupShape]
  have hPushType :
      TypedCfg.Instr.type? (.push caseValue) dupShape =
        some pushShape := by
    rfl
  have hEqType :
      TypedCfg.Instr.type? (.prim .eq) pushShape =
        some (testOutput valueShape) := by
    have hTestType :=
      testBody_type (caseValue := caseValue) hHead
    simp [TypedCfg.Block.bodyType?, hDupType, hPushType] at hTestType
    exact hTestType
  rcases StateRel.stackView_of_pop hRel hPop with
    ⟨realizedTail, _hTailRealize, hTargetStack⟩
  let afterDup :=
    target.replaceStackAndIncrPC
      (value :: value :: realizedTail)
  let afterPush :=
    afterDup.replaceStackAndIncrPC
      (caseValue :: value :: value :: realizedTail) (pcΔ := 33)
  let afterEq :=
    afterPush.replaceStackAndIncrPC
      (EvmYul.UInt256.eq caseValue value :: value :: realizedTail)
  let targetFinal : EVMState :=
    { afterEq with stack := value :: realizedTail }
  have hFinalSame :
      SameRuntimeData targetFinal target := by
    cases target
    simp [targetFinal, afterEq, afterPush, afterDup,
      SameRuntimeData, eraseCfgControl,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC] at hTargetStack ⊢
    exact hTargetStack.symm
  have hDupRun :
      TypedCfg.Instr.runAt (.dup 0) valueShape target =
        .ok (afterDup, dupShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hDupType]
    simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.dup, hTargetStack, afterDup,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
  have hPushRun :
      TypedCfg.Instr.runAt (.push caseValue) dupShape afterDup =
        .ok (afterPush, pushShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hPushType]
    simp [TypedCfg.Instr.runState, afterPush, afterDup, EvmYul.Stack.push,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
  have hEqRun :
      TypedCfg.Instr.runAt (.prim .eq) pushShape afterPush =
        .ok (afterEq, testOutput valueShape) := by
    unfold TypedCfg.Instr.runAt
    rw [hEqType]
    simp [TypedCfg.Instr.runState, Assembly.PrimOp.step,
      Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2, EvmYul.Stack.push,
      afterPush, afterDup, afterEq,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Bind.bind, Except.bind]
  have hBodyRun :
      TypedCfg.Block.runBody
          [.dup 0, .push caseValue, .prim .eq] valueShape target =
        .ok (afterEq, testOutput valueShape) := by
    simp only [TypedCfg.Block.runBody]
    rw [hDupRun]
    simp only [Bind.bind, Except.bind]
    rw [hPushRun]
    simp only [Bind.bind, Except.bind]
    rw [hEqRun]
  refine
    ⟨targetFinal, ?_,
      StateRel.targetCongr hFinalSame hRel⟩
  apply BlocksInProgram.eventually_of_run hBlocks hMem
  simp only [TypedCfg.Block.run, hBodyRun, Bind.bind, Except.bind,
    if_pos rfl]
  have hOneNeZero :
      EvmYul.UInt256.ofNat 1 ≠ EvmYul.UInt256.ofNat 0 := by
    decide
  by_cases hEq : caseValue = value
  · simp [TypedCfg.Block.runTerm, EvmYul.Stack.pop,
      EvmYul.UInt256.eq, hEq, hOneNeZero,
      targetFinal, afterEq,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · simp [TypedCfg.Block.runTerm, EvmYul.Stack.pop,
      EvmYul.UInt256.eq, hEq,
      targetFinal, afterEq,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]

/--
When the first case matches, the generated test selects that case, its entry
removes the retained scrutinee, and execution continues through the compiled
case body.
-/
theorem regular_cases_head_of_compileCasesFuel?
    {compilerFuel : Nat} {caseValue value : Word}
    {body : Structured.Block} {rest : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
          ((caseValue, body) :: rest) ctx base supply idx valueShape
            bodyShape regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hEq : caseValue = value)
    (hBodyPreserves :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx supply
            (.generated base (2000 + idx)) bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg
          (.generated base (2000 + idx)) regular
          (source.withEVM { source.evm with stack := stack }) final tokens) :
    RegularPreserves result cfg
      (TypedCfgCompiler.switchTestLabel base idx) regular
      source final tokens := by
  have hPopBodyType :
      TypedCfg.Block.bodyType? [.pop] valueShape = some bodyShape := by
    simp [TypedCfg.Block.bodyType?, hPopType]
  unfold TypedCfgCompiler.compileCasesFuel? at hCompile
  simp only at hCompile
  simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
    hPopBodyType, Bind.bind, Option.bind] at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx supply
        (.generated base (2000 + idx)) bodyShape regular with
  | none =>
      simp [hBody] at hCompile
  | some bodyResult =>
      simp only [hBody] at hCompile
      cases hTail :
          TypedCfgCompiler.compileCasesFuel? compilerFuel rest ctx base
            bodyResult.next (idx + 1) valueShape bodyShape regular with
      | none =>
          simp [hTail] at hCompile
      | some tail =>
          simp only [hTail] at hCompile
          cases hCompile
          have hBodyBlocks : BlocksInProgram bodyResult cfg := by
            intro block hMem
            apply hBlocks block
            simp [hMem]
          intro target hRel
          rcases
              eventually_test
                (testLabel := TypedCfgCompiler.switchTestLabel base idx)
                (caseLabel := LabelSupply.label base (idx + 2))
                (nextTest := nextTestLabel base idx rest)
                (caseValue := caseValue) (value := value)
                hBlocks
                (by
                  left)
                hHead hRel hPop with
            ⟨targetAfterTest, hTestEventually, hAfterTestRel⟩
          have hSelected :
              cfg.Eventually (TypedCfgCompiler.switchTestLabel base idx)
                target
                (.jump (LabelSupply.label base (idx + 2))
                  targetAfterTest) := by
            simpa [hEq] using hTestEventually
          rcases
              BlocksInProgram.eventually_pop_jump
                (entry := LabelSupply.label base (idx + 2))
                (regular := .generated base (2000 + idx))
                (input := valueShape) (output := bodyShape)
                hBlocks (by simp) hPopType hAfterTestRel hPop with
            ⟨targetAfterPop, hEntryEventually, hAfterPopRel⟩
          rcases
              hBodyPreserves hBody hBodyBlocks
                targetAfterPop hAfterPopRel with
            ⟨targetFinal, hBodyExecution, hFinalRel⟩
          rcases hBodyExecution with
            ⟨_bodyOutput, _hBodyFallthrough, hBodyEventually⟩
          refine ⟨targetFinal, ?_, hFinalRel⟩
          refine ⟨bodyShape, rfl, ?_⟩
          exact
            TypedCfg.Program.Eventually.bind_jump hSelected
              (TypedCfg.Program.Eventually.bind_jump
                hEntryEventually hBodyEventually)

/--
When the first case does not match, its test preserves the retained scrutinee
and delegates to a supplied proof for the next test or the default entry.
-/
theorem regular_cases_tail_of_compileCasesFuel?
    {compilerFuel : Nat} {caseValue value : Word}
    {body : Structured.Block} {rest : List (Word × Structured.Block)}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
          ((caseValue, body) :: rest) ctx base supply idx valueShape
            bodyShape regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hNe : caseValue ≠ value)
    (hNextPreserves :
      ∀ target,
        StateRel source tokens target →
          ∃ targetFinal,
            cfg.Eventually (nextTestLabel base idx rest) target
                (.jump regular targetFinal) ∧
              StateRel final tokens targetFinal) :
    RegularPreserves result cfg
      (TypedCfgCompiler.switchTestLabel base idx) regular
      source final tokens := by
  have hPopBodyType :
      TypedCfg.Block.bodyType? [.pop] valueShape = some bodyShape := by
    simp [TypedCfg.Block.bodyType?, hPopType]
  unfold TypedCfgCompiler.compileCasesFuel? at hCompile
  simp only at hCompile
  simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
    hPopBodyType, Bind.bind, Option.bind] at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx supply
        (.generated base (2000 + idx)) bodyShape regular with
  | none =>
      simp [hBody] at hCompile
  | some bodyResult =>
      simp only [hBody] at hCompile
      cases hTail :
          TypedCfgCompiler.compileCasesFuel? compilerFuel rest ctx base
            bodyResult.next (idx + 1) valueShape bodyShape regular with
      | none =>
          simp [hTail] at hCompile
      | some tail =>
          simp only [hTail] at hCompile
          cases hCompile
          intro target hRel
          rcases
              eventually_test
                (testLabel := TypedCfgCompiler.switchTestLabel base idx)
                (caseLabel := LabelSupply.label base (idx + 2))
                (nextTest := nextTestLabel base idx rest)
                (caseValue := caseValue) (value := value)
                hBlocks
                (by
                  left)
                hHead hRel hPop with
            ⟨targetAfterTest, hTestEventually, hAfterTestRel⟩
          have hSkipped :
              cfg.Eventually (TypedCfgCompiler.switchTestLabel base idx)
                target
                (.jump (nextTestLabel base idx rest)
                  targetAfterTest) := by
            simpa [hNe] using hTestEventually
          rcases hNextPreserves targetAfterTest hAfterTestRel with
            ⟨targetFinal, hNextEventually, hFinalRel⟩
          refine ⟨targetFinal, ?_, hFinalRel⟩
          refine ⟨bodyShape, rfl, ?_⟩
          exact
            TypedCfg.Program.Eventually.bind_jump
              hSkipped hNextEventually

/--
Case-chain preservation follows the independent source selector. A matching
case executes the selected compiled body; misses recurse through generated test
labels; exhausting the list delegates to the default-entry certificate.
-/
theorem path_cases_some_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx base supply idx
        valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = some selected)
    (hCasePreserves :
      ∀ {bodyCompilerFuel caseSupply caseIdx : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            caseSupply (.generated base (2000 + caseIdx))
            bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg
          (.generated base (2000 + caseIdx)) regular
          (source.withEVM { source.evm with stack := stack }) final tokens)
    (hDefaultPreserves :
      defaultBody = some selected →
        PathPreserves cfg (LabelSupply.label base 1) regular
          source final tokens) :
    PathPreserves cfg (casesEntryLabel base idx cases) regular
      source final tokens := by
  induction cases generalizing compilerFuel supply idx result selected with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = some selected := by
            simpa [Switch.select] using hSelect
          simpa [casesEntryLabel] using hDefaultPreserves hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          have hCompileFull := hCompile
          have hPopBodyType :
              TypedCfg.Block.bodyType? [.pop] valueShape =
                some bodyShape := by
            simp [TypedCfg.Block.bodyType?, hPopType]
          unfold TypedCfgCompiler.compileCasesFuel? at hCompile
          simp only at hCompile
          simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
            hPopBodyType, Bind.bind, Option.bind] at hCompile
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body ctx
                supply (.generated base (2000 + idx))
                bodyShape regular with
          | none =>
              simp [hBody] at hCompile
          | some bodyResult =>
              simp only [hBody] at hCompile
              cases hTail :
                  TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest ctx
                    base bodyResult.next (idx + 1) valueShape bodyShape
                    regular with
              | none =>
                  simp [hTail] at hCompile
              | some tail =>
                  simp only [hTail] at hCompile
                  cases hCompile
                  have hBodyBlocks : BlocksInProgram bodyResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hTailBlocks : BlocksInProgram tail cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  by_cases hEq : caseValue = value
                  · have hSelected : body = selected := by
                      simpa [Switch.select, hEq] using hSelect
                    subst selected
                    have hRegular :=
                      regular_cases_head_of_compileCasesFuel?
                        hCompileFull hBlocks hHead hPopType hPop hEq
                        (fun hBodyCompile hCompiledBodyBlocks =>
                          hCasePreserves
                            hBodyCompile hCompiledBodyBlocks)
                    simpa [casesEntryLabel] using
                      PathPreserves.of_regular hRegular
                  · have hTailSelect :
                        Switch.select value rest defaultBody =
                          some selected := by
                      simpa [Switch.select, hEq] using hSelect
                    have hTailPreserves :=
                      ih hTail hTailBlocks hTailSelect
                        hCasePreserves hDefaultPreserves
                    have hRegular :=
                      regular_cases_tail_of_compileCasesFuel?
                        hCompileFull hBlocks hHead hPopType hPop hEq
                        hTailPreserves
                    simpa [casesEntryLabel] using
                      PathPreserves.of_regular hRegular

/--
Outcome-indexed case-chain preservation.

A matching case removes the retained scrutinee and delegates to the selected
body's shared outcome path. A miss preserves the retained scrutinee and
recurses through the generated test chain.
-/
theorem outcome_cases_some_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {outcome : Structured.Outcome}
    {tokens : List Word} {continuations : OutcomeSimulation.Continuations}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx base supply idx
        valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCalls : CallsInProgram result globalCalls)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = some selected)
    (hCasePath :
      ∀ {bodyCompilerFuel caseSupply caseIdx : Nat}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            caseSupply (.generated base (2000 + caseIdx))
            bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        CallsInProgram bodyResult globalCalls →
        OutcomeSimulation.Path cfg
          (.generated base (2000 + caseIdx)) continuations
          (source.withEVM { source.evm with stack := stack })
          outcome tokens)
    (hDefaultPath :
      defaultBody = some selected →
        OutcomeSimulation.Path cfg (LabelSupply.label base 1)
          continuations source outcome tokens) :
    OutcomeSimulation.Path cfg (casesEntryLabel base idx cases)
      continuations source outcome tokens := by
  induction cases generalizing compilerFuel supply idx result selected with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = some selected := by
            simpa [Switch.select] using hSelect
          simpa [casesEntryLabel] using hDefaultPath hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          have hPopBodyType :
              TypedCfg.Block.bodyType? [.pop] valueShape =
                some bodyShape := by
            simp [TypedCfg.Block.bodyType?, hPopType]
          unfold TypedCfgCompiler.compileCasesFuel? at hCompile
          simp only at hCompile
          simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
            hPopBodyType, Bind.bind, Option.bind] at hCompile
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body ctx
                supply (.generated base (2000 + idx))
                bodyShape regular with
          | none =>
              simp [hBody] at hCompile
          | some bodyResult =>
              simp only [hBody] at hCompile
              cases hTail :
                  TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest ctx
                    base bodyResult.next (idx + 1) valueShape bodyShape
                    regular with
              | none =>
                  simp [hTail] at hCompile
              | some tail =>
                  simp only [hTail] at hCompile
                  cases hCompile
                  have hBodyBlocks : BlocksInProgram bodyResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hTailBlocks : BlocksInProgram tail cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hBodyCalls :
                      CallsInProgram bodyResult globalCalls := by
                    intro site hMem
                    apply hCalls site
                    simp [hMem]
                  have hTailCalls :
                      CallsInProgram tail globalCalls := by
                    intro site hMem
                    apply hCalls site
                    simp [hMem]
                  by_cases hEq : caseValue = value
                  · have hSelected : body = selected := by
                      simpa [Switch.select, hEq] using hSelect
                    subst selected
                    intro target hRel
                    rcases
                        eventually_test
                          (testLabel :=
                            TypedCfgCompiler.switchTestLabel base idx)
                          (caseLabel := LabelSupply.label base (idx + 2))
                          (nextTest := nextTestLabel base idx rest)
                          (caseValue := caseValue) (value := value)
                          hBlocks (by left) hHead hRel hPop with
                      ⟨targetAfterTest, hTestEventually, hAfterTestRel⟩
                    have hSelectedTest :
                        cfg.Eventually
                          (TypedCfgCompiler.switchTestLabel base idx)
                          target
                          (.jump (LabelSupply.label base (idx + 2))
                            targetAfterTest) := by
                      simpa [hEq] using hTestEventually
                    rcases
                        BlocksInProgram.eventually_pop_jump
                          (entry := LabelSupply.label base (idx + 2))
                          (regular := .generated base (2000 + idx))
                          (input := valueShape) (output := bodyShape)
                          hBlocks (by simp) hPopType hAfterTestRel hPop with
                      ⟨targetAfterPop, hEntryEventually, hAfterPopRel⟩
                    rcases
                        hCasePath hBody hBodyBlocks hBodyCalls
                          targetAfterPop hAfterPopRel with
                      ⟨targetOutcome, hBodyEventually, hOutcomeRel⟩
                    refine ⟨targetOutcome, ?_, hOutcomeRel⟩
                    exact
                      TypedCfg.Program.Eventually.bind_jump hSelectedTest
                        (TypedCfg.Program.Eventually.bind_jump
                          hEntryEventually hBodyEventually)
                  · have hTailSelect :
                        Switch.select value rest defaultBody =
                          some selected := by
                      simpa [Switch.select, hEq] using hSelect
                    have hTailPath :=
                      ih hTail hTailBlocks hTailCalls hTailSelect
                        hCasePath hDefaultPath
                    intro target hRel
                    rcases
                        eventually_test
                          (testLabel :=
                            TypedCfgCompiler.switchTestLabel base idx)
                          (caseLabel := LabelSupply.label base (idx + 2))
                          (nextTest := nextTestLabel base idx rest)
                          (caseValue := caseValue) (value := value)
                          hBlocks (by left) hHead hRel hPop with
                      ⟨targetAfterTest, hTestEventually, hAfterTestRel⟩
                    have hSkipped :
                        cfg.Eventually
                          (TypedCfgCompiler.switchTestLabel base idx)
                          target
                          (.jump (nextTestLabel base idx rest)
                            targetAfterTest) := by
                      simpa [hEq] using hTestEventually
                    rcases hTailPath targetAfterTest hAfterTestRel with
                      ⟨targetOutcome, hTailEventually, hOutcomeRel⟩
                    exact
                      ⟨targetOutcome,
                        TypedCfg.Program.Eventually.bind_jump
                          hSkipped hTailEventually,
                        hOutcomeRel⟩

/--
If source selection finds no body, every generated case test misses and the
chain eventually delegates to the no-body default entry.
-/
theorem path_cases_none_of_compileCasesFuel?
    {compilerFuel : Nat}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {base supply idx : Nat} {regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileCasesFuel? compilerFuel cases ctx base supply idx
        valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead : valueShape.slots.head? = some slot)
    (hPopType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = none)
    (hDefaultPreserves :
      defaultBody = none →
        PathPreserves cfg (LabelSupply.label base 1) regular
          source final tokens) :
    PathPreserves cfg (casesEntryLabel base idx cases) regular
      source final tokens := by
  induction cases generalizing compilerFuel supply idx result with
  | nil =>
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ compilerFuel =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
          cases hCompile
          have hDefault : defaultBody = none := by
            simpa [Switch.select] using hSelect
          simpa [casesEntryLabel] using hDefaultPreserves hDefault
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      cases compilerFuel with
      | zero =>
          simp [TypedCfgCompiler.compileCasesFuel?] at hCompile
      | succ bodyCompilerFuel =>
          have hCompileFull := hCompile
          have hPopBodyType :
              TypedCfg.Block.bodyType? [.pop] valueShape =
                some bodyShape := by
            simp [TypedCfg.Block.bodyType?, hPopType]
          unfold TypedCfgCompiler.compileCasesFuel? at hCompile
          simp only at hCompile
          simp only [TypedCfgCompiler.mkBlock?, testBody_type hHead,
            hPopBodyType, Bind.bind, Option.bind] at hCompile
          cases hBody :
              TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel body ctx
                supply (.generated base (2000 + idx))
                bodyShape regular with
          | none =>
              simp [hBody] at hCompile
          | some bodyResult =>
              simp only [hBody] at hCompile
              cases hTail :
                  TypedCfgCompiler.compileCasesFuel? bodyCompilerFuel rest ctx
                    base bodyResult.next (idx + 1) valueShape bodyShape
                    regular with
              | none =>
                  simp [hTail] at hCompile
              | some tail =>
                  simp only [hTail] at hCompile
                  cases hCompile
                  have hTailBlocks : BlocksInProgram tail cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  by_cases hEq : caseValue = value
                  · simp [Switch.select, hEq] at hSelect
                  · have hTailSelect :
                        Switch.select value rest defaultBody = none := by
                      simpa [Switch.select, hEq] using hSelect
                    have hTailPreserves :=
                      ih hTail hTailBlocks hTailSelect
                    have hRegular :=
                      regular_cases_tail_of_compileCasesFuel?
                        hCompileFull hBlocks hHead hPopType hPop hEq
                        hTailPreserves
                    simpa [casesEntryLabel] using
                      PathPreserves.of_regular hRegular

/--
When a switch has no default body, the generated default block removes the
retained scrutinee and reaches the regular continuation.
-/
theorem regular_default_none_of_compileDefaultFuel?
    {compilerFuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1) none ctx
        supply entry valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value)) :
    RegularPreserves result cfg entry regular source
      (source.withEVM { source.evm with stack := stack }) tokens := by
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?, hType] at hCompile
  cases hCompile
  apply RegularPreserves.pop_jump
    (input := valueShape) (output := bodyShape) hBlocks
  · simp
  · rfl
  · exact hType
  · exact hPop

/--
A generated nonempty default first removes the retained scrutinee, then
delegates to the compiled default body.
-/
theorem regular_default_some_of_compileDefaultFuel?
    {compilerFuel : Nat} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1) (some body) ctx
        supply entry valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyPreserves :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (.generated supply 2000) bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg (.generated supply 2000) regular
          (source.withEVM { source.evm with stack := stack }) final tokens) :
    RegularPreserves result cfg entry regular source final tokens := by
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
        (supply + 1) (.generated supply 2000) bodyShape regular with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?, hType,
        hBody] at hCompile
  | some bodyResult =>
      simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?, hType,
        hBody] at hCompile
      cases hCompile
      have hBodyBlocks : BlocksInProgram bodyResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hMem]
      intro target hRel
      rcases
          BlocksInProgram.eventually_pop_jump
            (entry := entry) (regular := .generated supply 2000)
            (input := valueShape) (output := bodyShape)
            hBlocks (by simp) hType hRel hPop with
        ⟨targetAfterPop, hEntryEventually, hAfterPopRel⟩
      rcases
          hBodyPreserves hBody hBodyBlocks targetAfterPop hAfterPopRel with
        ⟨targetFinal, hBodyExecution, hFinalRel⟩
      rcases hBodyExecution with
        ⟨_bodyOutput, _hBodyFallthrough, hBodyEventually⟩
      refine ⟨targetFinal, ?_, hFinalRel⟩
      refine ⟨bodyShape, rfl, ?_⟩
      exact
        TypedCfg.Program.Eventually.bind_jump
          hEntryEventually hBodyEventually

/--
Outcome-indexed nonempty default preservation.
-/
theorem outcome_default_some_of_compileDefaultFuel?
    {compilerFuel : Nat} {body : Structured.Block}
    {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {valueShape bodyShape : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {outcome : Structured.Outcome}
    {tokens : List Word} {continuations : OutcomeSimulation.Continuations}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1) (some body) ctx
        supply entry valueShape bodyShape regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCalls : CallsInProgram result globalCalls)
    (hType : TypedCfg.Instr.type? .pop valueShape = some bodyShape)
    (hPop : source.evm.stack.pop = some (stack, value))
    (hBodyPath :
      ∀ {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
            (supply + 1) (.generated supply 2000) bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        CallsInProgram bodyResult globalCalls →
        OutcomeSimulation.Path cfg (.generated supply 2000)
          continuations
          (source.withEVM { source.evm with stack := stack })
          outcome tokens) :
    OutcomeSimulation.Path cfg entry continuations source outcome tokens := by
  unfold TypedCfgCompiler.compileDefaultFuel? at hCompile
  cases hBody :
      TypedCfgCompiler.compileBlockFuel? compilerFuel body ctx
        (supply + 1) (.generated supply 2000) bodyShape regular with
  | none =>
      simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?, hType,
        hBody] at hCompile
  | some bodyResult =>
      simp [TypedCfgCompiler.mkBlock?, TypedCfg.Block.bodyType?, hType,
        hBody] at hCompile
      cases hCompile
      have hBodyBlocks : BlocksInProgram bodyResult cfg := by
        intro block hMem
        apply hBlocks block
        simp [hMem]
      have hBodyCalls : CallsInProgram bodyResult globalCalls := by
        intro site hMem
        apply hCalls site
        simpa using hMem
      intro target hRel
      rcases
          BlocksInProgram.eventually_pop_jump
            (entry := entry) (regular := .generated supply 2000)
            (input := valueShape) (output := bodyShape)
            hBlocks (by simp) hType hRel hPop with
        ⟨targetAfterPop, hEntryEventually, hAfterPopRel⟩
      rcases
          hBodyPath hBody hBodyBlocks hBodyCalls
            targetAfterPop hAfterPopRel with
        ⟨targetOutcome, hBodyEventually, hOutcomeRel⟩
      exact
        ⟨targetOutcome,
          TypedCfg.Program.Eventually.bind_jump
            hEntryEventually hBodyEventually,
          hOutcomeRel⟩

/--
Every successfully compiled switch exposes its static fallthrough shape.
-/
theorem fallthrough_of_compileStmtFuel?_switch
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result) :
    ∃ output, result.fallthrough? = some output := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input with
  | none =>
      simp [hType] at hCompile
  | some valueShape =>
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [hType, hValue] at hCompile
      | some valueSlot =>
          simp only [TypedCfgCompiler.mkBlock?, hType, hValue,
            Bind.bind, Option.bind] at hCompile
          cases hCases :
              TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                cases ctx supply (supply + 1) 0 valueShape
                { valueShape with slots := valueShape.slots.tail }
                regular with
          | none =>
              simp [hCases] at hCompile
          | some caseResult =>
              simp only [hCases] at hCompile
              cases hDefault :
                  TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
                    defaultBody ctx caseResult.next
                    (LabelSupply.label supply 1) valueShape
                    { valueShape with slots := valueShape.slots.tail }
                    regular with
              | none =>
                  simp [hDefault] at hCompile
              | some defaultResult =>
                  simp only [hDefault] at hCompile
                  cases hCompile
                  exact
                    ⟨{ valueShape with slots := valueShape.slots.tail },
                      rfl⟩

/--
One unit of compiler fuel cannot compile a switch because case generation
requires a recursive compiler step.
-/
theorem compileStmtFuel?_switch_one_eq_none
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape} :
    TypedCfgCompiler.compileStmtFuel? 1
        (.switch scrutinee cases defaultBody) ctx
        supply entry input regular =
      none := by
  unfold TypedCfgCompiler.compileStmtFuel?
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input <;>
    simp [hType, TypedCfgCompiler.mkBlock?,
      TypedCfgCompiler.compileCasesFuel?]

/--
Outcome-indexed preservation for a switch that selects a source body.
-/
theorem outcome_some_of_compileStmtFuel?
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee : RunState} {outcome : Structured.Outcome}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCalls : CallsInProgram result globalCalls)
    (hFrameSafe : scrutinee.FrameSafe)
    (hScrutinee :
      Structured.Code.runState scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.evm.stack.pop = some (stack, value))
    (hSelect :
      Switch.select value cases defaultBody = some selected)
    (hSelectedPath :
      ∀ {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label}
        {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        CallsInProgram bodyResult globalCalls →
        OutcomeSimulation.Path cfg bodyEntry
          (OutcomeSimulation.Continuations.ofContext ctx regular)
          (afterScrutinee.withEVM
            { afterScrutinee.evm with stack := stack })
          outcome tokens) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source outcome tokens := by
  have hFallthrough :=
    fallthrough_of_compileStmtFuel?_switch hCompile
  refine ⟨?_, fun _hRegular => hFallthrough⟩
  intro target hRel
  rcases StateRel.runCode hFrameSafe hScrutinee hRel with
    ⟨targetAfterScrutinee, hTargetScrutinee, hAfterScrutineeRel⟩
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input with
  | none =>
      simp [hType] at hCompile
  | some valueShape =>
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [hType, hValue] at hCompile
      | some valueSlot =>
          let bodyShape : TypedCfg.Shape :=
            { valueShape with slots := valueShape.slots.tail }
          have hPopType :
              TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
            cases valueShape with
            | mk slots tail =>
                cases slots with
                | nil =>
                    simp at hValue
                | cons slot rest =>
                    simp [bodyShape, TypedCfg.Instr.type?]
          simp only [TypedCfgCompiler.mkBlock?, hType, hValue,
            Bind.bind, Option.bind] at hCompile
          cases hCasesCompileRaw :
              TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                cases ctx supply (supply + 1) 0 valueShape
                { valueShape with slots := valueShape.slots.tail }
                regular with
          | none =>
              simp [hCasesCompileRaw] at hCompile
          | some caseResult =>
              simp only [hCasesCompileRaw] at hCompile
              have hCasesCompile :
                  TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                      cases ctx supply (supply + 1) 0 valueShape bodyShape
                      regular =
                    some caseResult := by
                simpa [bodyShape] using hCasesCompileRaw
              cases hDefaultCompileRaw :
                  TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
                    defaultBody ctx caseResult.next
                    (LabelSupply.label supply 1)
                    valueShape
                    { valueShape with slots := valueShape.slots.tail }
                    regular with
              | none =>
                  simp [hDefaultCompileRaw] at hCompile
              | some defaultResult =>
                  simp only [hDefaultCompileRaw] at hCompile
                  have hDefaultCompile :
                      TypedCfgCompiler.compileDefaultFuel?
                          (compilerFuel + 1) defaultBody ctx
                          caseResult.next
                          (LabelSupply.label supply 1)
                          valueShape bodyShape regular =
                        some defaultResult := by
                    simpa [bodyShape] using hDefaultCompileRaw
                  cases hCompile
                  have hCaseBlocks : BlocksInProgram caseResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDefaultBlocks :
                      BlocksInProgram defaultResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hCaseCalls :
                      CallsInProgram caseResult globalCalls := by
                    intro site hMem
                    apply hCalls site
                    simp [hMem]
                  have hDefaultCalls :
                      CallsInProgram defaultResult globalCalls := by
                    intro site hMem
                    apply hCalls site
                    simp [hMem]
                  have hDispatch :
                      OutcomeSimulation.Path cfg
                        (casesEntryLabel supply 0 cases)
                        (OutcomeSimulation.Continuations.ofContext ctx regular)
                        afterScrutinee outcome tokens := by
                    apply outcome_cases_some_of_compileCasesFuel?
                      hCasesCompile hCaseBlocks hCaseCalls
                      hValue hPopType hPop hSelect
                    · intro bodyCompilerFuel caseSupply caseIdx bodyResult
                        hBodyCompile hBodyBlocks hBodyCalls
                      exact
                        hSelectedPath hBodyCompile hBodyBlocks hBodyCalls
                    · intro hDefault
                      have hDefaultSelected :
                          TypedCfgCompiler.compileDefaultFuel?
                              (compilerFuel + 1) (some selected) ctx
                              caseResult.next
                              (LabelSupply.label supply 1)
                              valueShape bodyShape regular =
                            some defaultResult := by
                        simpa [hDefault] using hDefaultCompile
                      apply outcome_default_some_of_compileDefaultFuel?
                        hDefaultSelected hDefaultBlocks hDefaultCalls
                        hPopType hPop
                      intro bodyResult hBodyCompile hBodyBlocks hBodyCalls
                      exact
                        hSelectedPath hBodyCompile hBodyBlocks hBodyCalls
                  let firstTest := casesEntryLabel supply 0 cases
                  let head : TypedCfg.Block :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term := .jump firstTest }
                  have hHeadEventually :
                      cfg.Eventually entry target
                        (.jump firstTest targetAfterScrutinee) := by
                    apply BlocksInProgram.eventually_of_run hBlocks
                      (block := head)
                    · simp only [head, firstTest, casesEntryLabel,
                        List.mem_cons]
                      left
                    · simp [head, TypedCfg.Block.run,
                        Code.runBody_toCfg hType, hTargetScrutinee,
                        Except.map, Bind.bind, Except.bind,
                        TypedCfg.Block.runTerm]
                  rcases hDispatch targetAfterScrutinee
                      hAfterScrutineeRel with
                    ⟨targetOutcome, hDispatchEventually, hOutcomeRel⟩
                  exact
                    ⟨targetOutcome,
                      TypedCfg.Program.Eventually.bind_jump
                        hHeadEventually hDispatchEventually,
                      hOutcomeRel⟩

/--
A source switch that selects a body executes the scrutinee, follows the
generated case/default dispatch, and delegates only the selected source body to
the recursive preservation proof.
-/
theorem preserves_some_of_compileStmtFuel?
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee final : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : scrutinee.FrameSafe)
    (hScrutinee :
      Structured.Code.runState scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.evm.stack.pop = some (stack, value))
    (hSelect :
      Switch.select value cases defaultBody = some selected)
    (hSelectedPreserves :
      ∀ {bodyCompilerFuel bodySupply : Nat}
        {bodyEntry : Assembly.Label}
        {bodyShape : TypedCfg.Shape}
        {bodyResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileBlockFuel? bodyCompilerFuel selected ctx
            bodySupply bodyEntry bodyShape regular =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        RegularPreserves bodyResult cfg bodyEntry regular
          (afterScrutinee.withEVM
            { afterScrutinee.evm with stack := stack })
          final tokens) :
    RegularPreserves result cfg entry regular source final tokens := by
  intro target hRel
  rcases StateRel.runCode hFrameSafe hScrutinee hRel with
    ⟨targetAfterScrutinee, hTargetScrutinee, hAfterScrutineeRel⟩
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input with
  | none =>
      simp [hType] at hCompile
  | some valueShape =>
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [hType, hValue] at hCompile
      | some valueSlot =>
          let bodyShape : TypedCfg.Shape :=
            { valueShape with slots := valueShape.slots.tail }
          have hPopType :
              TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
            cases valueShape with
            | mk slots tail =>
                cases slots with
                | nil =>
                    simp at hValue
                | cons slot rest =>
                    simp [bodyShape, TypedCfg.Instr.type?]
          simp only [TypedCfgCompiler.mkBlock?, hType, hValue,
            Bind.bind, Option.bind] at hCompile
          cases hCasesCompileRaw :
              TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                cases ctx supply (supply + 1) 0 valueShape
                { valueShape with slots := valueShape.slots.tail }
                regular with
          | none =>
              simp [hCasesCompileRaw] at hCompile
          | some caseResult =>
              simp only [hCasesCompileRaw] at hCompile
              have hCasesCompile :
                  TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                      cases ctx supply (supply + 1) 0 valueShape bodyShape
                      regular =
                    some caseResult := by
                simpa [bodyShape] using hCasesCompileRaw
              cases hDefaultCompileRaw :
                  TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
                    defaultBody ctx caseResult.next
                    (LabelSupply.label supply 1)
                    valueShape
                    { valueShape with slots := valueShape.slots.tail }
                    regular with
              | none =>
                  simp [hDefaultCompileRaw] at hCompile
              | some defaultResult =>
                  simp only [hDefaultCompileRaw] at hCompile
                  have hDefaultCompile :
                      TypedCfgCompiler.compileDefaultFuel?
                          (compilerFuel + 1) defaultBody ctx
                          caseResult.next
                          (LabelSupply.label supply 1)
                          valueShape bodyShape regular =
                        some defaultResult := by
                    simpa [bodyShape] using hDefaultCompileRaw
                  cases hCompile
                  have hCaseBlocks : BlocksInProgram caseResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDefaultBlocks :
                      BlocksInProgram defaultResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDispatch :
                      PathPreserves cfg
                        (casesEntryLabel supply 0 cases) regular
                        afterScrutinee final tokens := by
                    apply path_cases_some_of_compileCasesFuel?
                      hCasesCompile hCaseBlocks hValue hPopType hPop hSelect
                    · intro bodyCompilerFuel caseSupply caseIdx bodyResult
                        hBodyCompile hBodyBlocks
                      exact
                        hSelectedPreserves
                          hBodyCompile hBodyBlocks
                    · intro hDefault
                      have hDefaultSelected :
                          TypedCfgCompiler.compileDefaultFuel?
                              (compilerFuel + 1) (some selected) ctx
                              caseResult.next
                              (LabelSupply.label supply 1)
                              valueShape bodyShape regular =
                            some defaultResult := by
                        simpa [hDefault] using hDefaultCompile
                      apply PathPreserves.of_regular
                      apply regular_default_some_of_compileDefaultFuel?
                        hDefaultSelected hDefaultBlocks hPopType hPop
                      intro bodyResult hBodyCompile hBodyBlocks
                      exact
                        hSelectedPreserves
                          hBodyCompile hBodyBlocks
                  let firstTest := casesEntryLabel supply 0 cases
                  let head : TypedCfg.Block :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term := .jump firstTest }
                  have hHeadEventually :
                      cfg.Eventually entry target
                        (.jump firstTest targetAfterScrutinee) := by
                    apply BlocksInProgram.eventually_of_run hBlocks
                      (block := head)
                    · simp only [head, firstTest, casesEntryLabel,
                        List.mem_cons]
                      left
                    · simp [head, TypedCfg.Block.run,
                        Code.runBody_toCfg hType, hTargetScrutinee,
                        Except.map, Bind.bind, Except.bind,
                        TypedCfg.Block.runTerm]
                  rcases hDispatch targetAfterScrutinee
                      hAfterScrutineeRel with
                    ⟨targetFinal, hDispatchEventually, hFinalRel⟩
                  refine ⟨targetFinal, ?_, hFinalRel⟩
                  refine ⟨bodyShape, rfl, ?_⟩
                  exact
                    TypedCfg.Program.Eventually.bind_jump
                      hHeadEventually hDispatchEventually

/--
A source switch that selects no body executes the scrutinee, misses every
generated case test, removes the retained value in the no-body default block,
and reaches the regular continuation.
-/
theorem preserves_none_of_compileStmtFuel?
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : scrutinee.FrameSafe)
    (hScrutinee :
      Structured.Code.runState scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = none) :
    RegularPreserves result cfg entry regular source
      (afterScrutinee.withEVM
        { afterScrutinee.evm with stack := stack }) tokens := by
  intro target hRel
  rcases StateRel.runCode hFrameSafe hScrutinee hRel with
    ⟨targetAfterScrutinee, hTargetScrutinee, hAfterScrutineeRel⟩
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input with
  | none =>
      simp [hType] at hCompile
  | some valueShape =>
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [hType, hValue] at hCompile
      | some valueSlot =>
          let bodyShape : TypedCfg.Shape :=
            { valueShape with slots := valueShape.slots.tail }
          have hPopType :
              TypedCfg.Instr.type? .pop valueShape = some bodyShape := by
            cases valueShape with
            | mk slots tail =>
                cases slots with
                | nil =>
                    simp at hValue
                | cons slot rest =>
                    simp [bodyShape, TypedCfg.Instr.type?]
          simp only [TypedCfgCompiler.mkBlock?, hType, hValue,
            Bind.bind, Option.bind] at hCompile
          cases hCasesCompileRaw :
              TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                cases ctx supply (supply + 1) 0 valueShape
                { valueShape with slots := valueShape.slots.tail }
                regular with
          | none =>
              simp [hCasesCompileRaw] at hCompile
          | some caseResult =>
              simp only [hCasesCompileRaw] at hCompile
              have hCasesCompile :
                  TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                      cases ctx supply (supply + 1) 0 valueShape bodyShape
                      regular =
                    some caseResult := by
                simpa [bodyShape] using hCasesCompileRaw
              cases hDefaultCompileRaw :
                  TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
                    defaultBody ctx caseResult.next
                    (LabelSupply.label supply 1)
                    valueShape
                    { valueShape with slots := valueShape.slots.tail }
                    regular with
              | none =>
                  simp [hDefaultCompileRaw] at hCompile
              | some defaultResult =>
                  simp only [hDefaultCompileRaw] at hCompile
                  have hDefaultCompile :
                      TypedCfgCompiler.compileDefaultFuel?
                          (compilerFuel + 1) defaultBody ctx
                          caseResult.next
                          (LabelSupply.label supply 1)
                          valueShape bodyShape regular =
                        some defaultResult := by
                    simpa [bodyShape] using hDefaultCompileRaw
                  cases hCompile
                  have hCaseBlocks : BlocksInProgram caseResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDefaultBlocks :
                      BlocksInProgram defaultResult cfg := by
                    intro block hMem
                    apply hBlocks block
                    simp [hMem]
                  have hDispatch :
                      PathPreserves cfg
                        (casesEntryLabel supply 0 cases) regular
                        afterScrutinee
                        (afterScrutinee.withEVM
                          { afterScrutinee.evm with stack := stack })
                        tokens := by
                    apply path_cases_none_of_compileCasesFuel?
                      hCasesCompile hCaseBlocks hValue hPopType hPop hSelect
                    intro hDefault
                    have hDefaultNone :
                        TypedCfgCompiler.compileDefaultFuel?
                            (compilerFuel + 1) none ctx caseResult.next
                            (LabelSupply.label supply 1)
                            valueShape bodyShape regular =
                          some defaultResult := by
                      simpa [hDefault] using hDefaultCompile
                    apply PathPreserves.of_regular
                    exact
                      regular_default_none_of_compileDefaultFuel?
                        hDefaultNone hDefaultBlocks hPopType hPop
                  let firstTest := casesEntryLabel supply 0 cases
                  let head : TypedCfg.Block :=
                    { label := entry
                      input := input
                      body := TypedCfgCompiler.Code.toCfg scrutinee
                      output := valueShape
                      term := .jump firstTest }
                  have hHeadEventually :
                      cfg.Eventually entry target
                        (.jump firstTest targetAfterScrutinee) := by
                    apply BlocksInProgram.eventually_of_run hBlocks
                      (block := head)
                    · simp only [head, firstTest, casesEntryLabel,
                        List.mem_cons]
                      left
                    · simp [head, TypedCfg.Block.run,
                        Code.runBody_toCfg hType, hTargetScrutinee,
                        Except.map, Bind.bind, Except.bind,
                        TypedCfg.Block.runTerm]
                  rcases hDispatch targetAfterScrutinee
                      hAfterScrutineeRel with
                    ⟨targetFinal, hDispatchEventually, hFinalRel⟩
                  refine ⟨targetFinal, ?_, ?_⟩
                  · refine ⟨bodyShape, rfl, ?_⟩
                    exact
                      TypedCfg.Program.Eventually.bind_jump
                        hHeadEventually hDispatchEventually
                  · simpa [RunState.withEVM] using hFinalRel

/--
The no-selection switch branch satisfies the uniform outcome certificate.
-/
theorem outcome_none_of_compileStmtFuel?
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : scrutinee.FrameSafe)
    (hScrutinee :
      Structured.Code.runState scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = none) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source
      (Structured.Outcome.regular
        (afterScrutinee.withEVM
          { afterScrutinee.evm with stack := stack }))
      tokens := by
  apply OutcomeSimulation.Preserves.of_regular rfl
  · exact fallthrough_of_compileStmtFuel?_switch hCompile
  · exact
      preserves_none_of_compileStmtFuel?
        hCompile hBlocks hFrameSafe hScrutinee hPop hSelect

/--
An empty switch without a default body executes the scrutinee, removes its
value in the generated default block, and reaches the regular continuation.
-/
theorem preserves_empty_none_of_compileStmtFuel?
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source afterScrutinee : RunState} {tokens : List Word}
    {stack : EvmYul.Stack Word} {value : Word}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
        (.switch scrutinee [] none) ctx supply entry input regular =
          some result)
    (hBlocks : BlocksInProgram result cfg)
    (hFrameSafe : scrutinee.FrameSafe)
    (hScrutinee :
      Structured.Code.runState scrutinee source =
        .ok afterScrutinee)
    (hPop :
      afterScrutinee.evm.stack.pop = some (stack, value)) :
    RegularPreserves result cfg entry regular source
      (afterScrutinee.withEVM
        { afterScrutinee.evm with stack := stack }) tokens := by
  exact
    preserves_none_of_compileStmtFuel?
      hCompile hBlocks hFrameSafe hScrutinee hPop rfl

end Switch

namespace Loop

def bodyContinuations (endLabel postLabel : Assembly.Label)
    (outer : OutcomeSimulation.Continuations) :
    OutcomeSimulation.Continuations where
  regular := postLabel
  breakLabel? := some endLabel
  continueLabel? := some postLabel
  leaveLabel? := outer.leaveLabel?

def postContinuations (loopLabel : Assembly.Label)
    (outer : OutcomeSimulation.Continuations) :
    OutcomeSimulation.Continuations where
  regular := loopLabel
  leaveLabel? := outer.leaveLabel?

/--
Canonical decomposition of a successfully compiled `for` statement.

Downstream semantic proofs consume these named fragments instead of unfolding
the recursive compiler independently.
-/
theorem components_of_compileStmtFuel?_for
    {compilerFuel : Nat} {init post body : Structured.Block}
    {cond : Structured.Code} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.for_ init cond post body) ctx supply entry input regular =
          some result) :
    ∃ initResult loopInput condOutput condition bodyResult postResult,
      TypedCfgCompiler.compileBlockFuel? compilerFuel init
          { ctx with breakLabel? := none, continueLabel? := none }
          (supply + 1) entry input (LabelSupply.label supply 0) =
        some initResult ∧
      initResult.fallthrough? = some loopInput ∧
      TypedCfg.Block.bodyType?
          (TypedCfgCompiler.Code.toCfg cond) loopInput =
        some condOutput ∧
      condOutput.slots.head? = some condition ∧
      TypedCfgCompiler.compileBlockFuel? compilerFuel body
          { ctx with
            breakLabel? := some regular
            continueLabel? := some (LabelSupply.label supply 2) }
          initResult.next (LabelSupply.label supply 1)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 2) =
        some bodyResult ∧
      TypedCfgCompiler.compileBlockFuel? compilerFuel post
          { ctx with breakLabel? := none, continueLabel? := none }
          bodyResult.next (LabelSupply.label supply 2)
          (bodyResult.fallthrough?.getD
            { condOutput with slots := condOutput.slots.tail })
          (LabelSupply.label supply 0) =
        some postResult ∧
      result =
        { blocks :=
            initResult.blocks ++
              [{ label := LabelSupply.label supply 0
                 input := loopInput
                 body := TypedCfgCompiler.Code.toCfg cond
                 output := condOutput
                 term :=
                   .jumpi (LabelSupply.label supply 1) regular }] ++
              bodyResult.blocks ++ postResult.blocks
          next := postResult.next
          calls :=
            initResult.calls ++ bodyResult.calls ++ postResult.calls
          fallthrough? :=
            some { condOutput with slots := condOutput.slots.tail } } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hInit :
      TypedCfgCompiler.compileBlockFuel? compilerFuel init
        { ctx with breakLabel? := none, continueLabel? := none }
        (supply + 1) entry input (LabelSupply.label supply 0) with
  | none =>
      simp [hInit] at hCompile
  | some initResult =>
      cases hLoopInput : initResult.fallthrough? with
      | none =>
          simp [hInit, hLoopInput] at hCompile
      | some loopInput =>
          cases hType :
              TypedCfg.Block.bodyType?
                (TypedCfgCompiler.Code.toCfg cond) loopInput with
          | none =>
              simp [hInit, hLoopInput, hType] at hCompile
          | some condOutput =>
              cases hHead : condOutput.slots.head? with
              | none =>
                  simp [hInit, hLoopInput, hType, hHead] at hCompile
              | some condition =>
                  cases hBody :
                      TypedCfgCompiler.compileBlockFuel? compilerFuel body
                        { ctx with
                          breakLabel? := some regular
                          continueLabel? :=
                            some (LabelSupply.label supply 2) }
                        initResult.next (LabelSupply.label supply 1)
                        { condOutput with
                          slots := condOutput.slots.tail }
                        (LabelSupply.label supply 2) with
                  | none =>
                      simp [hInit, hLoopInput, hType, hHead,
                        TypedCfgCompiler.mkBlock?, hBody] at hCompile
                  | some bodyResult =>
                      cases hPost :
                          TypedCfgCompiler.compileBlockFuel? compilerFuel post
                            { ctx with
                              breakLabel? := none
                              continueLabel? := none }
                            bodyResult.next
                            (LabelSupply.label supply 2)
                            (bodyResult.fallthrough?.getD
                              { condOutput with
                                slots := condOutput.slots.tail })
                            (LabelSupply.label supply 0) with
                      | none =>
                          simp [hInit, hLoopInput, hType, hHead,
                            TypedCfgCompiler.mkBlock?, hBody, hPost] at hCompile
                      | some postResult =>
                          simp [hInit, hLoopInput, hType, hHead,
                            TypedCfgCompiler.mkBlock?, hBody, hPost] at hCompile
                          cases hCompile
                          refine
                            ⟨initResult, loopInput, condOutput, condition,
                              bodyResult, postResult, ?_⟩
                          simp [hInit, hLoopInput, hType, hHead, hBody, hPost,
                            List.append_assoc]

/--
The generated loop-condition block follows the independent source condition
and preserves the concrete procedure-frame relation.
-/
theorem eventually_condition
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {cond : Structured.Code} {condValue : Bool}
    {source afterCond : RunState} {tokens : List Word}
    {target : EVMState}
    (hBlocks : BlocksInProgram result cfg)
    (hMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfg.Block.bodyType?
          (TypedCfgCompiler.Code.toCfg cond) loopInput =
        some condOutput)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (afterCond, condValue))
    (hRel : StateRel source tokens target) :
    ∃ targetAfterCond,
      cfg.Eventually loopLabel target
          (.jump (if condValue then bodyLabel else endLabel)
            targetAfterCond) ∧
        StateRel afterCond tokens targetAfterCond := by
  rcases StateRel.runCondition hFrameSafe hCond hRel with
    ⟨targetAfterCond, hTargetCond, hAfterCondRel⟩
  refine ⟨targetAfterCond, ?_, hAfterCondRel⟩
  apply BlocksInProgram.eventually_of_run hBlocks hMem
  simpa [RunState.withEVM] using
    (Code.run_jumpi_toCfg
      (target := bodyLabel) (fallthrough := endLabel)
      hType hTargetCond)

/--
Path form of generated loop-condition preservation.
-/
theorem preserves_condition
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {cond : Structured.Code} {condValue : Bool}
    {source afterCond : RunState} {tokens : List Word}
    (hBlocks : BlocksInProgram result cfg)
    (hMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfg.Block.bodyType?
          (TypedCfgCompiler.Code.toCfg cond) loopInput =
        some condOutput)
    (hFrameSafe : cond.FrameSafe)
    (hCond :
      Structured.Code.runConditionState cond source =
        .ok (afterCond, condValue)) :
    PathPreserves cfg loopLabel
      (if condValue then bodyLabel else endLabel)
      source afterCond tokens := by
  intro target hRel
  exact
    eventually_condition hBlocks hMem hType hFrameSafe hCond hRel

/--
Compositional loop preservation over the independent `For.Eval` relation.

Recursive body and post obligations use the shared outcome path interface.
Every source loop constructor then reduces to label-path composition; break is
caught at the loop exit, continue selects the post entry, and leave/halt are
transported through the inherited procedure continuation.
-/
theorem path_of_eval
    {program : Structured.Program} {fuel bound : Nat}
    {cond : Structured.Code} {post body : Structured.Block}
    {source : RunState} {outcome : Structured.Outcome}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {loopLabel bodyLabel postLabel endLabel : Assembly.Label}
    {loopInput condOutput : TypedCfg.Shape}
    {tokens : List Word}
    {outer : OutcomeSimulation.Continuations}
    (hBlocks : BlocksInProgram result cfg)
    (hMem :
      { label := loopLabel
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi bodyLabel endLabel } ∈ result.blocks)
    (hType :
      TypedCfg.Block.bodyType?
          (TypedCfgCompiler.Code.toCfg cond) loopInput =
        some condOutput)
    (hFrameSafe : cond.FrameSafe)
    (hOuterRegular : outer.regular = endLabel)
    (hFuelLt : fuel < bound)
    (hEval :
      Structured.For.Eval program fuel cond post body source outcome)
    (hBodyPath :
      ∀ {bodyFuel : Nat} {bodySource : RunState}
        {bodyOutcome : Structured.Outcome},
        Structured.Block.Eval program bodyFuel body
            bodySource bodyOutcome →
        bodyFuel < bound →
          OutcomeSimulation.Path cfg bodyLabel
            (bodyContinuations endLabel postLabel outer)
            bodySource bodyOutcome tokens)
    (hPostPath :
      ∀ {postFuel : Nat} {postSource : RunState}
        {postOutcome : Structured.Outcome},
        Structured.Block.Eval program postFuel post
            postSource postOutcome →
        postFuel < bound →
          OutcomeSimulation.Path cfg postLabel
            (postContinuations loopLabel outer)
            postSource postOutcome tokens) :
    OutcomeSimulation.Path cfg loopLabel outer source outcome tokens := by
  cases hEval with
  | false hCond =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.regular_of_path hOuterRegular
      simpa using hCondition
  | body_brk hCond hBody =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      have hBodyBreak :=
        OutcomeSimulation.Path.to_brk
          (by rfl) (hBodyPath hBody (by omega))
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      exact
        OutcomeSimulation.Path.regular_of_path
          hOuterRegular hBodyBreak
  | body_leave hCond hBody =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      exact
        OutcomeSimulation.Path.transport_leave
          (by rfl) (hBodyPath hBody (by omega))
  | body_halt hCond hBody =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      exact
        OutcomeSimulation.Path.transport_halt
          (hBodyPath hBody (by omega))
  | regular_post_regular hCond hBody hPost hLoop =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular (hBodyPath hBody (by omega)))
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular (hPostPath hPost (by omega)))
      exact
        path_of_eval hBlocks hMem hType hFrameSafe hOuterRegular
          (by omega) hLoop hBodyPath hPostPath
  | cont_post_regular hCond hBody hPost hLoop =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_cont
          (by rfl) (hBodyPath hBody (by omega)))
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular (hPostPath hPost (by omega)))
      exact
        path_of_eval hBlocks hMem hType hFrameSafe hOuterRegular
          (by omega) hLoop hBodyPath hPostPath
  | regular_post_leave hCond hBody hPost =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular (hBodyPath hBody (by omega)))
      exact
        OutcomeSimulation.Path.transport_leave
          (by rfl) (hPostPath hPost (by omega))
  | cont_post_leave hCond hBody hPost =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_cont
          (by rfl) (hBodyPath hBody (by omega)))
      exact
        OutcomeSimulation.Path.transport_leave
          (by rfl) (hPostPath hPost (by omega))
  | regular_post_halt hCond hBody hPost =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular (hBodyPath hBody (by omega)))
      exact
        OutcomeSimulation.Path.transport_halt
          (hPostPath hPost (by omega))
  | cont_post_halt hCond hBody hPost =>
      have hCondition :=
        preserves_condition (tokens := tokens)
          hBlocks hMem hType hFrameSafe hCond
      apply OutcomeSimulation.Path.bind_jump
        (by simpa using hCondition)
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_cont
          (by rfl) (hBodyPath hBody (by omega)))
      exact
        OutcomeSimulation.Path.transport_halt
          (hPostPath hPost (by omega))
termination_by fuel

/--
Compiler-facing `for` preservation.

The compiler decomposition supplies the exact init/body/post fragments and
generated condition block. Recursive block proofs remain abstracted behind the
uniform outcome path interface.
-/
theorem path_of_compileStmtFuel?_and_eval
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {init post body : Structured.Block} {cond : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {outcome : Structured.Outcome}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.for_ init cond post body) ctx supply entry input regular =
          some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCalls : CallsInProgram result globalCalls)
    (hCondSafe : cond.FrameSafe)
    (hEval :
      Structured.Stmt.Eval program sourceFuel
        (.for_ init cond post body) source outcome)
    (hInitPath :
      ∀ {initResult : TypedCfgCompiler.Result}
        {loopInput : TypedCfg.Shape}
        {initFuel : Nat} {initSource : RunState}
        {initOutcome : Structured.Outcome},
        TypedCfgCompiler.compileBlockFuel? compilerFuel init
            { ctx with breakLabel? := none, continueLabel? := none }
            (supply + 1) entry input (LabelSupply.label supply 0) =
          some initResult →
        initResult.fallthrough? = some loopInput →
        BlocksInProgram initResult cfg →
        CallsInProgram initResult globalCalls →
        Structured.Block.Eval program initFuel init
            initSource initOutcome →
        initFuel < sourceFuel →
        OutcomeSimulation.Path cfg entry
          (postContinuations (LabelSupply.label supply 0)
            (OutcomeSimulation.Continuations.ofContext ctx regular))
          initSource initOutcome tokens)
    (hBodyPath :
      ∀ {initResult bodyResult : TypedCfgCompiler.Result}
        {condOutput : TypedCfg.Shape}
        {bodyFuel : Nat} {bodySource : RunState}
        {bodyOutcome : Structured.Outcome},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            { ctx with
              breakLabel? := some regular
              continueLabel? := some (LabelSupply.label supply 2) }
            initResult.next (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 2) =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        CallsInProgram bodyResult globalCalls →
        Structured.Block.Eval program bodyFuel body
            bodySource bodyOutcome →
        bodyFuel < sourceFuel →
        OutcomeSimulation.Path cfg (LabelSupply.label supply 1)
          (bodyContinuations regular (LabelSupply.label supply 2)
            (OutcomeSimulation.Continuations.ofContext ctx regular))
          bodySource bodyOutcome tokens)
    (hPostPath :
      ∀ {bodyResult postResult : TypedCfgCompiler.Result}
        {condOutput : TypedCfg.Shape}
        {postFuel : Nat} {postSource : RunState}
        {postOutcome : Structured.Outcome},
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            { ctx with breakLabel? := none, continueLabel? := none }
            bodyResult.next (LabelSupply.label supply 2)
            (bodyResult.fallthrough?.getD
              { condOutput with slots := condOutput.slots.tail })
            (LabelSupply.label supply 0) =
          some postResult →
        BlocksInProgram postResult cfg →
        CallsInProgram postResult globalCalls →
        Structured.Block.Eval program postFuel post
            postSource postOutcome →
        postFuel < sourceFuel →
        OutcomeSimulation.Path cfg (LabelSupply.label supply 2)
          (postContinuations (LabelSupply.label supply 0)
            (OutcomeSimulation.Continuations.ofContext ctx regular))
          postSource postOutcome tokens) :
    OutcomeSimulation.Path cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source outcome tokens := by
  rcases components_of_compileStmtFuel?_for hCompile with
    ⟨initResult, loopInput, condOutput, _condition, bodyResult,
      postResult, hInitCompile, hInitFallthrough, hType, _hHead,
      hBodyCompile, hPostCompile, rfl⟩
  have hInitBlocks : BlocksInProgram initResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hBodyBlocks : BlocksInProgram bodyResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hPostBlocks : BlocksInProgram postResult cfg := by
    intro block hMem
    apply hBlocks block
    simp [hMem]
  have hInitCalls : CallsInProgram initResult globalCalls := by
    intro site hMem
    apply hCalls site
    simp [hMem]
  have hBodyCalls : CallsInProgram bodyResult globalCalls := by
    intro site hMem
    apply hCalls site
    simp [hMem]
  have hPostCalls : CallsInProgram postResult globalCalls := by
    intro site hMem
    apply hCalls site
    simp [hMem]
  have hLoopMem :
      { label := LabelSupply.label supply 0
        input := loopInput
        body := TypedCfgCompiler.Code.toCfg cond
        output := condOutput
        term := .jumpi (LabelSupply.label supply 1) regular } ∈
        (initResult.blocks ++
          [{ label := LabelSupply.label supply 0
             input := loopInput
             body := TypedCfgCompiler.Code.toCfg cond
             output := condOutput
             term := .jumpi (LabelSupply.label supply 1) regular }] ++
          bodyResult.blocks ++ postResult.blocks) := by
    simp
  cases hEval with
  | @for_init_regular fuel _ _ _ _ _ _ _ hInit hLoop =>
      apply OutcomeSimulation.Path.bind_jump
        (OutcomeSimulation.Path.to_regular
          (hInitPath hInitCompile hInitFallthrough hInitBlocks hInitCalls hInit
            (by omega)))
      apply path_of_eval (bound := fuel + 1)
        hBlocks hLoopMem hType hCondSafe rfl
        (by omega) hLoop
      · intro bodyFuel bodySource bodyOutcome hBody hBodyFuel
        exact
          hBodyPath hBodyCompile hBodyBlocks hBodyCalls hBody hBodyFuel
      · intro postFuel postSource postOutcome hPost hPostFuel
        exact
          hPostPath hPostCompile hPostBlocks hPostCalls hPost hPostFuel
  | for_init_leave hInit =>
      exact
        OutcomeSimulation.Path.transport_leave
          (by rfl)
          (hInitPath hInitCompile hInitFallthrough hInitBlocks hInitCalls hInit
            (by omega))
  | for_init_halt hInit =>
      exact
        OutcomeSimulation.Path.transport_halt
          (hInitPath hInitCompile hInitFallthrough hInitBlocks hInitCalls hInit
            (by omega))

/--
Compiler-facing loop preservation in the uniform fragment certificate.

Loop compilation always carries a regular fallthrough shape, while the
semantic path itself may end in any source outcome.
-/
theorem outcome_of_compileStmtFuel?_and_eval
    {compilerFuel sourceFuel : Nat}
    {program : Structured.Program}
    {init post body : Structured.Block} {cond : Structured.Code}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {outcome : Structured.Outcome}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.for_ init cond post body) ctx supply entry input regular =
          some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCalls : CallsInProgram result globalCalls)
    (hCondSafe : cond.FrameSafe)
    (hEval :
      Structured.Stmt.Eval program sourceFuel
        (.for_ init cond post body) source outcome)
    (hInitPath :
      ∀ {initResult : TypedCfgCompiler.Result}
        {loopInput : TypedCfg.Shape}
        {initFuel : Nat} {initSource : RunState}
        {initOutcome : Structured.Outcome},
        TypedCfgCompiler.compileBlockFuel? compilerFuel init
            { ctx with breakLabel? := none, continueLabel? := none }
            (supply + 1) entry input (LabelSupply.label supply 0) =
          some initResult →
        initResult.fallthrough? = some loopInput →
        BlocksInProgram initResult cfg →
        CallsInProgram initResult globalCalls →
        Structured.Block.Eval program initFuel init
            initSource initOutcome →
        initFuel < sourceFuel →
        OutcomeSimulation.Path cfg entry
          (postContinuations (LabelSupply.label supply 0)
            (OutcomeSimulation.Continuations.ofContext ctx regular))
          initSource initOutcome tokens)
    (hBodyPath :
      ∀ {initResult bodyResult : TypedCfgCompiler.Result}
        {condOutput : TypedCfg.Shape}
        {bodyFuel : Nat} {bodySource : RunState}
        {bodyOutcome : Structured.Outcome},
        TypedCfgCompiler.compileBlockFuel? compilerFuel body
            { ctx with
              breakLabel? := some regular
              continueLabel? := some (LabelSupply.label supply 2) }
            initResult.next (LabelSupply.label supply 1)
            { condOutput with slots := condOutput.slots.tail }
            (LabelSupply.label supply 2) =
          some bodyResult →
        BlocksInProgram bodyResult cfg →
        CallsInProgram bodyResult globalCalls →
        Structured.Block.Eval program bodyFuel body
            bodySource bodyOutcome →
        bodyFuel < sourceFuel →
        OutcomeSimulation.Path cfg (LabelSupply.label supply 1)
          (bodyContinuations regular (LabelSupply.label supply 2)
            (OutcomeSimulation.Continuations.ofContext ctx regular))
          bodySource bodyOutcome tokens)
    (hPostPath :
      ∀ {bodyResult postResult : TypedCfgCompiler.Result}
        {condOutput : TypedCfg.Shape}
        {postFuel : Nat} {postSource : RunState}
        {postOutcome : Structured.Outcome},
        TypedCfgCompiler.compileBlockFuel? compilerFuel post
            { ctx with breakLabel? := none, continueLabel? := none }
            bodyResult.next (LabelSupply.label supply 2)
            (bodyResult.fallthrough?.getD
              { condOutput with slots := condOutput.slots.tail })
            (LabelSupply.label supply 0) =
          some postResult →
        BlocksInProgram postResult cfg →
        CallsInProgram postResult globalCalls →
        Structured.Block.Eval program postFuel post
            postSource postOutcome →
        postFuel < sourceFuel →
        OutcomeSimulation.Path cfg (LabelSupply.label supply 2)
          (postContinuations (LabelSupply.label supply 0)
            (OutcomeSimulation.Continuations.ofContext ctx regular))
          postSource postOutcome tokens) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source outcome tokens := by
  refine
    ⟨path_of_compileStmtFuel?_and_eval
      hCompile hBlocks hCalls hCondSafe hEval
      hInitPath hBodyPath hPostPath, ?_⟩
  intro _hRegular
  rcases components_of_compileStmtFuel?_for hCompile with
    ⟨_initResult, _loopInput, condOutput, _condition, _bodyResult,
      _postResult, _hInitCompile, _hInitFallthrough, _hType, _hHead,
      _hBodyCompile, _hPostCompile, hResult⟩
  subst result
  exact
    ⟨{ condOutput with slots := condOutput.slots.tail }, rfl⟩

end Loop

namespace Block

/--
Canonical decomposition of a successful nonempty statement-list compilation.
-/
theorem components_of_compileStmtListFuel?_cons
    {compilerFuel : Nat} {stmt : Structured.Stmt}
    {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
        (stmt :: rest) ctx supply entry input regular = some result) :
    ∃ headResult,
      TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
          entry input (TypedCfgCompiler.restLabel supply) =
        some headResult ∧
      ((headResult.fallthrough? = none ∧ result = headResult) ∨
        ∃ tailInput tailResult,
          headResult.fallthrough? = some tailInput ∧
          TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
              headResult.next (TypedCfgCompiler.restLabel supply)
              tailInput regular =
            some tailResult ∧
          result = headResult.append tailResult) := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  cases hHead :
      TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
        entry input (TypedCfgCompiler.restLabel supply) with
  | none =>
      simp [hHead] at hCompile
  | some headResult =>
      cases hFallthrough : headResult.fallthrough? with
      | none =>
          have hEq : headResult = result := by
            simpa [hHead, hFallthrough] using hCompile
          have hResult : result = headResult := by
            exact hEq.symm
          exact
            ⟨headResult, rfl,
              Or.inl ⟨hFallthrough, hResult⟩⟩
      | some tailInput =>
          cases hTail :
              TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
                headResult.next (TypedCfgCompiler.restLabel supply)
                tailInput regular with
          | none =>
              simp [hHead, hFallthrough, hTail] at hCompile
          | some tailResult =>
              have hEq : headResult.append tailResult = result := by
                simpa [hHead, hFallthrough, hTail] using hCompile
              have hResult : result = headResult.append tailResult := by
                exact hEq.symm
              exact
                ⟨headResult, rfl,
                  Or.inr
                    ⟨tailInput, tailResult, hFallthrough, hTail, hResult⟩⟩

/--
Ambient-program form of empty statement-list preservation.
-/
theorem eventually_nil_of_compileStmtListFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (fuel + 1) [] ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    cfg.Eventually entry state.evm
      (TypedCfg.Outcome.jump regular state.evm) := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  let generated : TypedCfg.Block :=
    { label := entry
      input := input
      body := []
      output := input
      term := .jump regular }
  have hFind :
      cfg.findBlock? entry = some generated := by
    exact hBlocks generated (by simp [generated])
  refine ⟨1, ?_⟩
  simp [TypedCfg.Program.runN, TypedCfg.Program.step, hFind,
    generated, TypedCfg.Block.run, TypedCfg.Block.runBody,
    TypedCfg.Block.runTerm, Bind.bind, Except.bind]

/--
The empty statement-list compiler produces a regular execution certificate.
-/
theorem regular_nil_of_compileStmtListFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (fuel + 1) [] ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    RegularExecution result cfg entry regular state.evm state.evm := by
  have hEventually :=
    eventually_nil_of_compileStmtListFuel?
      (state := state) hCompile hBlocks
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  exact ⟨input, rfl, hEventually⟩

/--
Empty statement-list preservation in the uniform outcome certificate.
-/
theorem preserves_nil_of_compileStmtListFuel?
    {compilerFuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {state : RunState} {tokens : List Word}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1) [] ctx
        supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      state (Structured.Outcome.regular state) tokens := by
  refine ⟨?_, ?_⟩
  · intro target hRel
    have hEventually :=
      eventually_nil_of_compileStmtListFuel?
        (state := state.withEVM target) hCompile hBlocks
    refine ⟨.jump regular target, ?_, ?_⟩
    · simpa [RunState.withEVM] using hEventually
    · exact OutcomeSimulation.Rel.regular_iff.mpr ⟨rfl, hRel⟩
  · intro _hMode
    unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
    simp [TypedCfgCompiler.mkBlock?] at hCompile
    cases hCompile
    exact ⟨input, rfl⟩

/--
Outcome-indexed statement-list composition.

The head certificate supplies semantic execution for every mode and a
fallthrough shape exactly when the source head is regular. This rules out a
regular source result when the compiler statically terminated the list and
composes the tail only in the compiler's fallthrough branch.
-/
theorem preserves_cons_of_compileStmtListFuel?_and_eval
    {compilerFuel sourceFuel : Nat} {program : Structured.Program}
    {stmt : Structured.Stmt} {rest : List Structured.Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {source : RunState} {outcome : Structured.Outcome}
    {tokens : List Word}
    {globalCalls : List TypedCfgCompiler.DispatchSite}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
        (stmt :: rest) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hCalls : CallsInProgram result globalCalls)
    (hEval :
      Structured.Block.Eval program sourceFuel
        { stmts := stmt :: rest } source outcome)
    (hHead :
      ∀ {headResult : TypedCfgCompiler.Result}
        {stmtFuel : Nat} {stmtSource : RunState}
        {stmtOutcome : Structured.Outcome},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        BlocksInProgram headResult cfg →
        CallsInProgram headResult globalCalls →
        Structured.Stmt.Eval program stmtFuel stmt
            stmtSource stmtOutcome →
        stmtFuel < sourceFuel →
        OutcomeSimulation.Preserves headResult cfg entry
          (OutcomeSimulation.Continuations.ofContext ctx
            (TypedCfgCompiler.restLabel supply))
          stmtSource stmtOutcome tokens)
    (hTail :
      ∀ {headResult tailResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape}
        {tailFuel : Nat} {tailSource : RunState}
        {tailOutcome : Structured.Outcome},
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        BlocksInProgram tailResult cfg →
        CallsInProgram tailResult globalCalls →
        Structured.Block.Eval program tailFuel { stmts := rest }
            tailSource tailOutcome →
        tailFuel < sourceFuel →
        OutcomeSimulation.Preserves tailResult cfg
          (TypedCfgCompiler.restLabel supply)
          (OutcomeSimulation.Continuations.ofContext ctx regular)
          tailSource tailOutcome tokens) :
    OutcomeSimulation.Preserves result cfg entry
      (OutcomeSimulation.Continuations.ofContext ctx regular)
      source outcome tokens := by
  rcases components_of_compileStmtListFuel?_cons hCompile with
    ⟨headResult, hHeadCompile, hNoTail | hWithTail⟩
  · rcases hNoTail with ⟨hFallthrough, rfl⟩
    cases hEval with
    | cons_regular hStmt _hRest =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt (Nat.lt_succ_self _)
        rcases
            OutcomeSimulation.Preserves.fallthrough_of_regular
              hHeadPreserves with
          ⟨output, hOutput⟩
        rw [hFallthrough] at hOutput
        cases hOutput
    | cons_brk hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt (Nat.lt_succ_self _)
        apply OutcomeSimulation.Preserves.of_path_of_nonregular
          (by simp)
        exact
          OutcomeSimulation.Path.transport_brk
            (by rfl) hHeadPreserves.path
    | cons_cont hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt (Nat.lt_succ_self _)
        apply OutcomeSimulation.Preserves.of_path_of_nonregular
          (by simp)
        exact
          OutcomeSimulation.Path.transport_cont
            (by rfl) hHeadPreserves.path
    | cons_leave hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt (Nat.lt_succ_self _)
        apply OutcomeSimulation.Preserves.of_path_of_nonregular
          (by simp)
        exact
          OutcomeSimulation.Path.transport_leave
            (by rfl) hHeadPreserves.path
    | cons_halt hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hBlocks hCalls hStmt (Nat.lt_succ_self _)
        apply OutcomeSimulation.Preserves.of_path_of_nonregular
          (by simp)
        exact
          OutcomeSimulation.Path.transport_halt hHeadPreserves.path
  · rcases hWithTail with
      ⟨tailInput, tailResult, hFallthrough, hTailCompile, rfl⟩
    have hHeadBlocks :=
      BlocksInProgram.left_of_append hBlocks
    have hTailBlocks :=
      BlocksInProgram.right_of_append hBlocks
    have hHeadCalls :=
      CallsInProgram.left_of_append hCalls
    have hTailCalls :=
      CallsInProgram.right_of_append hCalls
    cases hEval with
    | cons_regular hStmt hRest =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        have hTailPreserves :=
          hTail hFallthrough hTailCompile hTailBlocks hTailCalls hRest
            (Nat.lt_succ_self _)
        refine ⟨?_, ?_⟩
        · exact
            OutcomeSimulation.Path.bind_jump
              hHeadPreserves.to_regular_path hTailPreserves.path
        · intro hMode
          rcases hTailPreserves.2 hMode with
            ⟨output, hOutput⟩
          exact
            ⟨output,
              by
                simpa [TypedCfgCompiler.Result.append] using hOutput⟩
    | cons_brk hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        apply OutcomeSimulation.Preserves.of_path_of_nonregular
          (by simp)
        exact
          OutcomeSimulation.Path.transport_brk
            (by rfl) hHeadPreserves.path
    | cons_cont hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        apply OutcomeSimulation.Preserves.of_path_of_nonregular
          (by simp)
        exact
          OutcomeSimulation.Path.transport_cont
            (by rfl) hHeadPreserves.path
    | cons_leave hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        apply OutcomeSimulation.Preserves.of_path_of_nonregular
          (by simp)
        exact
          OutcomeSimulation.Path.transport_leave
            (by rfl) hHeadPreserves.path
    | cons_halt hStmt =>
        have hHeadPreserves :=
          hHead hHeadCompile hHeadBlocks hHeadCalls hStmt
            (Nat.lt_succ_self _)
        apply OutcomeSimulation.Preserves.of_path_of_nonregular
          (by simp)
        exact
          OutcomeSimulation.Path.transport_halt hHeadPreserves.path

/--
Generic regular statement-list composition.

The two premises are exactly the recursive obligations of a source-evaluation
induction. Compiler result decomposition, fallthrough consistency, ambient
block containment, and execution fuel composition are discharged here once.
-/
theorem regular_cons_of_compileStmtListFuel?
    {compilerFuel : Nat} {stmt : Stmt} {rest : List Stmt}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
    {state middle final : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (compilerFuel + 1)
        (stmt :: rest) ctx supply entry input regular = some result)
    (hBlocks : BlocksInProgram result cfg)
    (hHead :
      ∀ {headResult : TypedCfgCompiler.Result},
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
            entry input (TypedCfgCompiler.restLabel supply) =
          some headResult →
        BlocksInProgram headResult cfg →
        RegularExecution headResult cfg entry
          (TypedCfgCompiler.restLabel supply) state.evm middle.evm)
    (hTail :
      ∀ {headResult : TypedCfgCompiler.Result}
        {tailInput : TypedCfg.Shape}
        {tailResult : TypedCfgCompiler.Result},
        headResult.fallthrough? = some tailInput →
        TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
            headResult.next (TypedCfgCompiler.restLabel supply)
            tailInput regular =
          some tailResult →
        BlocksInProgram tailResult cfg →
        RegularExecution tailResult cfg
          (TypedCfgCompiler.restLabel supply) regular
          middle.evm final.evm) :
    RegularExecution result cfg entry regular state.evm final.evm := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  cases hHeadCompile :
      TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx supply
        entry input (TypedCfgCompiler.restLabel supply) with
  | none =>
      simp [hHeadCompile] at hCompile
  | some headResult =>
      cases hFallthrough : headResult.fallthrough? with
      | none =>
          simp [hHeadCompile, hFallthrough] at hCompile
          cases hCompile
          rcases hHead hHeadCompile hBlocks with
            ⟨output, hOutput, hEventually⟩
          rw [hFallthrough] at hOutput
          cases hOutput
      | some tailInput =>
          cases hTailCompile :
              TypedCfgCompiler.compileStmtListFuel? compilerFuel rest ctx
                headResult.next (TypedCfgCompiler.restLabel supply)
                tailInput regular with
          | none =>
              simp [hHeadCompile, hFallthrough, hTailCompile] at hCompile
          | some tailResult =>
              simp [hHeadCompile, hFallthrough, hTailCompile] at hCompile
              cases hCompile
              have hHeadBlocks :=
                BlocksInProgram.left_of_append hBlocks
              have hTailBlocks :=
                BlocksInProgram.right_of_append hBlocks
              exact
                RegularExecution.append
                  (hHead hHeadCompile hHeadBlocks)
                  (hTail hFallthrough hTailCompile hTailBlocks)

/--
An empty compiled statement list reaches its supplied regular continuation
without changing the source EVM state.
-/
theorem runN_nil_of_compileStmtListFuel?
    {fuel : Nat} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {state : RunState}
    (hCompile :
      TypedCfgCompiler.compileStmtListFuel? (fuel + 1) [] ctx
        supply entry input regular = some result) :
    (resultProgram result entry).runN 1 entry state.evm =
      Except.ok (TypedCfg.Outcome.jump regular state.evm) := by
  unfold TypedCfgCompiler.compileStmtListFuel? at hCompile
  simp [TypedCfgCompiler.mkBlock?] at hCompile
  cases hCompile
  simp [TypedCfg.Program.runN, TypedCfg.Program.step,
    resultProgram, TypedCfg.Program.findBlock?, TypedCfg.Block.run,
    TypedCfg.Block.runBody, TypedCfg.Block.runTerm, Bind.bind, Except.bind]

end Block

/--
Any block property inherited by every case body and the default is inherited
by the body selected by the source switch semantics.
-/
theorem switch_property_of_select
    {property : Structured.Block → Prop}
    {scrutinee : Word} {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    (hCases :
      ∀ value body, (value, body) ∈ cases → property body)
    (hDefault :
      ∀ body, defaultBody = some body → property body)
    (hSelect :
      Structured.Switch.select scrutinee cases defaultBody =
        some selected) :
    property selected := by
  revert selected
  induction cases with
  | nil =>
      intro selected hSelect
      exact hDefault selected hSelect
  | cons head rest ih =>
      intro selected hSelect
      rcases head with ⟨value, body⟩
      by_cases hEq : value = scrutinee
      · have hBodyEq : body = selected := by
          simpa [Structured.Switch.select, hEq] using hSelect
        subst selected
        exact hCases value body (by simp)
      · apply ih
        · intro caseValue caseBody hMem
          exact hCases caseValue caseBody (by simp [hMem])
        · simpa [Structured.Switch.select, hEq] using hSelect

namespace Call

/-- The procedure-exit shape places its return token beneath all results. -/
theorem returnTokenDepth?_procExit (proc : Structured.Proc) :
    (TypedCfgCompiler.Shape.procExit proc).returnTokenDepth? =
      some proc.retc := by
  unfold TypedCfgCompiler.Shape.procExit TypedCfg.Shape.returnTokenDepth?
  induction proc.retc with
  | zero =>
      simp [TypedCfg.Shape.returnTokenDepthList?]
  | succ retc ih =>
      simp [List.replicate_succ, TypedCfg.Shape.returnTokenDepthList?, ih]

/--
Global token uniqueness makes every generated dispatch site select its own
return label after filtering to the callee's exit block.
-/
theorem findTarget?_returnSitesFor_of_mem
    {calls : List TypedCfgCompiler.DispatchSite}
    {site : TypedCfgCompiler.DispatchSite}
    (hUnique :
      (calls.map TypedCfgCompiler.DispatchSite.token).Nodup)
    (hMem : site ∈ calls) :
    TypedCfg.Block.ReturnSite.findTarget? site.token
        (TypedCfgCompiler.returnSitesFor site.procName calls) =
      some site.returnLabel := by
  induction calls with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      have hHeadNot :
          head.token ∉
            tail.map TypedCfgCompiler.DispatchSite.token := by
        exact (List.nodup_cons.mp hUnique).1
      have hTailUnique :
          (tail.map TypedCfgCompiler.DispatchSite.token).Nodup :=
        (List.nodup_cons.mp hUnique).2
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl hHead =>
          subst site
          simp [TypedCfgCompiler.returnSitesFor,
            TypedCfg.Block.ReturnSite.findTarget?]
      | inr hTail =>
          have hTokenNe : head.token ≠ site.token := by
            intro hEq
            apply hHeadNot
            exact List.mem_map.mpr ⟨site, hTail, hEq.symm⟩
          have hFound := ih hTailUnique hTail
          by_cases hName : head.procName = site.procName
          · unfold TypedCfgCompiler.returnSitesFor
            simp [hName, TypedCfg.Block.ReturnSite.findTarget?, hTokenNe]
            simpa [TypedCfgCompiler.returnSitesFor] using hFound
          · unfold TypedCfgCompiler.returnSitesFor
            simp [hName]
            simpa [TypedCfgCompiler.returnSitesFor] using hFound

/--
The generated procedure-exit block selects a registered call site, removes its
return token, and restores the source caller state.
-/
theorem dispatch_eventually
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context : Program.GeneratedContext sourceProgram entryShapes cfg)
    {name : Structured.Name} {proc : Structured.Proc}
    {site : TypedCfgCompiler.DispatchSite}
    {bodyState returned : RunState} {frame : ReturnDest}
    {stack : EvmYul.Stack Word} {tokens : List Word}
    {target : EVMState}
    (hLookup :
      Structured.ProcList.lookup? name sourceProgram.procs = some proc)
    (hSiteProc : site.procName = proc.name)
    (hSiteMem : site ∈ context.calls)
    (hRel : StateRel bodyState (site.token :: tokens) target)
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      Structured.StackFrame.attachReturns? frame bodyState.evm.stack =
        some stack)
    (hRetc : frame.retc = proc.retc) :
    ∃ targetFinal,
      cfg.Eventually (ProcLabel.exit proc.name) target
          (.jump site.returnLabel targetFinal) ∧
      StateRel
        (returned.withEVM { bodyState.evm with stack := stack })
        tokens targetFinal := by
  rcases
      CallStack.eraseReturnToken_preserves
        hRel hPop hAttach with
    ⟨hToken, hFinalRel⟩
  have hFind :
      TypedCfg.Block.ReturnSite.findTarget? site.token
          (TypedCfgCompiler.returnSitesFor proc.name context.calls) =
        some site.returnLabel := by
    simpa [hSiteProc] using
      findTarget?_returnSitesFor_of_mem context.tokensUnique hSiteMem
  have hSitesNonempty :
      (TypedCfgCompiler.returnSitesFor proc.name context.calls).isEmpty =
        false := by
    cases hSites :
        TypedCfgCompiler.returnSitesFor proc.name context.calls with
    | nil =>
        simp [hSites, TypedCfg.Block.ReturnSite.findTarget?] at hFind
    | cons head rest =>
        rfl
  have hBlock := context.dispatchBlock hLookup
  let targetFinal : EVMState :=
    { target with stack := target.stack.eraseIdx proc.retc }
  refine ⟨targetFinal, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    rw [hRetc] at hToken hFinalRel
    simp [TypedCfg.Program.runN, TypedCfg.Program.step, hBlock,
      TypedCfgCompiler.dispatchBlock, hSitesNonempty,
      TypedCfg.Block.run, TypedCfg.Block.runBody,
      TypedCfg.Block.runTerm, returnTokenDepth?_procExit,
      hToken, hFind, targetFinal, Bind.bind, Except.bind]
  · rw [hRetc] at hFinalRel
    exact hFinalRel

/--
Canonical decomposition of successful call-statement compilation.
-/
theorem components_of_compileStmtFuel?_call
    {compilerFuel : Nat} {name : Structured.Name}
    {proc : Structured.Proc} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result) :
    ∃ returnShape output,
      TypedCfgCompiler.Shape.afterCall input proc.argc proc.retc =
          some returnShape ∧
      TypedCfg.Block.bodyType?
          (.returnToken (Structured.Stmt.callToken supply) ::
            TypedCfgCompiler.sinkTopUnder proc.argc) input =
        some output ∧
      result =
        { blocks :=
            [{ label := entry
               input := input
               body :=
                 .returnToken (Structured.Stmt.callToken supply) ::
                   TypedCfgCompiler.sinkTopUnder proc.argc
               output := output
               term := .jump (ProcLabel.entry name) }]
          next := supply + 1
          calls :=
            [{ procName := name
               token := Structured.Stmt.callToken supply
               returnLabel := regular
               caseLabel := .generated supply 10000 }]
          fallthrough? := some returnShape } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [hLookup] at hCompile
  cases hReturnShape :
      TypedCfgCompiler.Shape.afterCall input proc.argc proc.retc with
  | none =>
      simp [hReturnShape] at hCompile
  | some returnShape =>
      cases hType :
          TypedCfg.Block.bodyType?
            (.returnToken (Structured.Stmt.callToken supply) ::
              TypedCfgCompiler.sinkTopUnder proc.argc) input with
      | none =>
          simp [hReturnShape, TypedCfgCompiler.mkBlock?, hType] at hCompile
      | some output =>
          simp [hReturnShape, TypedCfgCompiler.mkBlock?, hType] at hCompile
          cases hCompile
          exact ⟨returnShape, output, rfl, rfl, rfl⟩

/--
The generated call block reaches the procedure entry with the source call
frame realized by its compiler-generated return token.
-/
theorem entry_eventually_of_compileStmtFuel?
    {compilerFuel : Nat} {name : Structured.Name}
    {proc : Structured.Proc} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    {cfg : TypedCfg.Program} {source : RunState}
    {tokens : List Word} {target : EVMState}
    {args callerStack : EvmYul.Stack Word}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result)
    (hBlocks : BlocksInProgram result cfg)
    (hRel : StateRel source tokens target)
    (hSplit :
      Structured.StackFrame.splitArgs? proc.argc source.evm.stack =
        some (args, callerStack))
    (hProcWF : proc.WF) :
    ∃ targetFinal,
      cfg.Eventually entry target
          (.jump (ProcLabel.entry name) targetFinal) ∧
      StateRel
        ((source.withEVM { source.evm with stack := args }).pushReturn
          callerStack proc.retc)
        (Structured.Stmt.callToken supply :: tokens) targetFinal := by
  rcases components_of_compileStmtFuel?_call hLookup hCompile with
    ⟨returnShape, output, hReturnShape, hType, rfl⟩
  rcases
      CallStack.runBody_callEntry_preserves hRel hSplit hType hProcWF.1 with
    ⟨targetFinal, hRunBody, hFinalRel⟩
  refine ⟨targetFinal, ?_, hFinalRel⟩
  refine
    BlocksInProgram.eventually_of_run
      (block :=
        { label := entry
          input := input
          body :=
            .returnToken (Structured.Stmt.callToken supply) ::
              TypedCfgCompiler.sinkTopUnder proc.argc
          output := output
          term := .jump (ProcLabel.entry name) })
      hBlocks ?_ ?_
  · simp
  · simp [TypedCfg.Block.run, hRunBody, TypedCfg.Block.runTerm,
      Bind.bind, Except.bind]

end Call

mutual

  /--
  Uniform preservation for a compiled Structured block in a checked generated
  whole-program context.
  -/
  theorem outcome_block_of_compileFuel?_and_eval_with_calls
      {compilerFuel sourceFuel : Nat}
      {program : Structured.Program} {block : Structured.Block}
      {entryShapes : TypedCfgCompiler.ProcEntryShapes}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {entry regular : Assembly.Label} {input : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
      {source : RunState} {outcome : Structured.Outcome}
      {tokens : List Word}
      {canBreak canContinue canLeave : Bool}
      (generated :
        Program.GeneratedContext program entryShapes cfg)
      (hCompile :
        TypedCfgCompiler.compileBlockFuel? compilerFuel block ctx
            supply entry input regular =
          some result)
      (hBlocks : BlocksInProgram result cfg)
      (hResultCalls : CallsInProgram result generated.calls)
      (hEval :
        Structured.Block.Eval program sourceFuel block source outcome)
      (hWF :
        Structured.Block.WF canBreak canContinue canLeave block)
      (hFrameSafe : block.FrameSafe)
      (hCalls :
        Structured.ProcList.BlockCallsResolved program.procs block)
      (hSupports :
        OutcomeSimulation.ContextSupports ctx
          canBreak canContinue canLeave)
      (hProcs : ctx.procs = program.procs)
      (hTerminal :
        ∀ kind, Stmt.Terminal.RelSafe kind)
      (hProgramWF : program.WF)
      (hProgramFrameSafe : program.FrameSafe) :
      OutcomeSimulation.Preserves result cfg entry
        (OutcomeSimulation.Continuations.ofContext ctx regular)
        source outcome tokens := by
    cases compilerFuel with
    | zero =>
        simp [TypedCfgCompiler.compileBlockFuel?] at hCompile
    | succ blockFuel =>
        unfold TypedCfgCompiler.compileBlockFuel? at hCompile
        cases blockFuel with
        | zero =>
            simp [TypedCfgCompiler.compileStmtListFuel?] at hCompile
        | succ listFuel =>
            cases hEval with
            | nil =>
                exact
                  Block.preserves_nil_of_compileStmtListFuel?
                    hCompile hBlocks
            | @cons_regular fuel stmt rest state mid blockOutcome
                hStmt hRest =>
                cases hWF with
                | cons hStmtWF hRestWF =>
                    cases hFrameSafe with
                    | cons hStmtFrameSafe hRestFrameSafe =>
                        cases hCalls with
                        | mk hStmtListCalls =>
                            cases hStmtListCalls with
                            | cons hStmtCalls hRestCalls =>
                                apply
                                  Block.preserves_cons_of_compileStmtListFuel?_and_eval
                                    hCompile hBlocks hResultCalls
                                    (.cons_regular hStmt hRest)
                                · intro headResult stmtFuel stmtSource
                                    stmtOutcome hHeadCompile hHeadBlocks
                                    hHeadCalls hHeadEval hFuelLt
                                  exact
                                    outcome_stmt_of_compileFuel?_and_eval_with_calls
                                      generated hHeadCompile hHeadBlocks hHeadCalls
                                      hHeadEval
                                      hStmtWF hStmtFrameSafe hStmtCalls
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
                                · intro headResult tailResult tailInput
                                    tailFuel tailSource tailOutcome
                                    hFallthrough hTailCompile hTailBlocks
                                    hTailCalls hTailEval hFuelLt
                                  have hTailBlockCompile :
                                      TypedCfgCompiler.compileBlockFuel?
                                          (listFuel + 1)
                                          { stmts := rest } ctx headResult.next
                                          (TypedCfgCompiler.restLabel supply)
                                          tailInput regular =
                                        some tailResult := by
                                    simpa [TypedCfgCompiler.compileBlockFuel?]
                                      using hTailCompile
                                  exact
                                    outcome_block_of_compileFuel?_and_eval_with_calls
                                      generated hTailBlockCompile hTailBlocks
                                      hTailCalls
                                      hTailEval
                                      hRestWF hRestFrameSafe
                                      (.mk hRestCalls)
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
            | @cons_brk fuel stmt rest state outState hStmt =>
                cases hWF with
                | cons hStmtWF hRestWF =>
                    cases hFrameSafe with
                    | cons hStmtFrameSafe hRestFrameSafe =>
                        cases hCalls with
                        | mk hStmtListCalls =>
                            cases hStmtListCalls with
                            | cons hStmtCalls hRestCalls =>
                                apply
                                  Block.preserves_cons_of_compileStmtListFuel?_and_eval
                                    hCompile hBlocks hResultCalls
                                    (.cons_brk hStmt)
                                · intro headResult stmtFuel stmtSource
                                    stmtOutcome hHeadCompile hHeadBlocks
                                    hHeadCalls hHeadEval hFuelLt
                                  exact
                                    outcome_stmt_of_compileFuel?_and_eval_with_calls
                                      generated hHeadCompile hHeadBlocks hHeadCalls
                                      hHeadEval
                                      hStmtWF hStmtFrameSafe hStmtCalls
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
                                · intro headResult tailResult tailInput
                                    tailFuel tailSource tailOutcome
                                    hFallthrough hTailCompile hTailBlocks
                                    hTailCalls hTailEval hFuelLt
                                  have hTailBlockCompile :
                                      TypedCfgCompiler.compileBlockFuel?
                                          (listFuel + 1)
                                          { stmts := rest } ctx headResult.next
                                          (TypedCfgCompiler.restLabel supply)
                                          tailInput regular =
                                        some tailResult := by
                                    simpa [TypedCfgCompiler.compileBlockFuel?]
                                      using hTailCompile
                                  exact
                                    outcome_block_of_compileFuel?_and_eval_with_calls
                                      generated hTailBlockCompile hTailBlocks
                                      hTailCalls
                                      hTailEval
                                      hRestWF hRestFrameSafe
                                      (.mk hRestCalls)
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
            | @cons_cont fuel stmt rest state outState hStmt =>
                cases hWF with
                | cons hStmtWF hRestWF =>
                    cases hFrameSafe with
                    | cons hStmtFrameSafe hRestFrameSafe =>
                        cases hCalls with
                        | mk hStmtListCalls =>
                            cases hStmtListCalls with
                            | cons hStmtCalls hRestCalls =>
                                apply
                                  Block.preserves_cons_of_compileStmtListFuel?_and_eval
                                    hCompile hBlocks hResultCalls
                                    (.cons_cont hStmt)
                                · intro headResult stmtFuel stmtSource
                                    stmtOutcome hHeadCompile hHeadBlocks
                                    hHeadCalls hHeadEval hFuelLt
                                  exact
                                    outcome_stmt_of_compileFuel?_and_eval_with_calls
                                      generated hHeadCompile hHeadBlocks hHeadCalls
                                      hHeadEval
                                      hStmtWF hStmtFrameSafe hStmtCalls
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
                                · intro headResult tailResult tailInput
                                    tailFuel tailSource tailOutcome
                                    hFallthrough hTailCompile hTailBlocks
                                    hTailCalls hTailEval hFuelLt
                                  have hTailBlockCompile :
                                      TypedCfgCompiler.compileBlockFuel?
                                          (listFuel + 1)
                                          { stmts := rest } ctx headResult.next
                                          (TypedCfgCompiler.restLabel supply)
                                          tailInput regular =
                                        some tailResult := by
                                    simpa [TypedCfgCompiler.compileBlockFuel?]
                                      using hTailCompile
                                  exact
                                    outcome_block_of_compileFuel?_and_eval_with_calls
                                      generated hTailBlockCompile hTailBlocks
                                      hTailCalls
                                      hTailEval
                                      hRestWF hRestFrameSafe
                                      (.mk hRestCalls)
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
            | @cons_leave fuel stmt rest state outState hStmt =>
                cases hWF with
                | cons hStmtWF hRestWF =>
                    cases hFrameSafe with
                    | cons hStmtFrameSafe hRestFrameSafe =>
                        cases hCalls with
                        | mk hStmtListCalls =>
                            cases hStmtListCalls with
                            | cons hStmtCalls hRestCalls =>
                                apply
                                  Block.preserves_cons_of_compileStmtListFuel?_and_eval
                                    hCompile hBlocks hResultCalls
                                    (.cons_leave hStmt)
                                · intro headResult stmtFuel stmtSource
                                    stmtOutcome hHeadCompile hHeadBlocks
                                    hHeadCalls hHeadEval hFuelLt
                                  exact
                                    outcome_stmt_of_compileFuel?_and_eval_with_calls
                                      generated hHeadCompile hHeadBlocks hHeadCalls
                                      hHeadEval
                                      hStmtWF hStmtFrameSafe hStmtCalls
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
                                · intro headResult tailResult tailInput
                                    tailFuel tailSource tailOutcome
                                    hFallthrough hTailCompile hTailBlocks
                                    hTailCalls hTailEval hFuelLt
                                  have hTailBlockCompile :
                                      TypedCfgCompiler.compileBlockFuel?
                                          (listFuel + 1)
                                          { stmts := rest } ctx headResult.next
                                          (TypedCfgCompiler.restLabel supply)
                                          tailInput regular =
                                        some tailResult := by
                                    simpa [TypedCfgCompiler.compileBlockFuel?]
                                      using hTailCompile
                                  exact
                                    outcome_block_of_compileFuel?_and_eval_with_calls
                                      generated hTailBlockCompile hTailBlocks
                                      hTailCalls
                                      hTailEval
                                      hRestWF hRestFrameSafe
                                      (.mk hRestCalls)
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
            | @cons_halt fuel stmt rest state outState kind hStmt =>
                cases hWF with
                | cons hStmtWF hRestWF =>
                    cases hFrameSafe with
                    | cons hStmtFrameSafe hRestFrameSafe =>
                        cases hCalls with
                        | mk hStmtListCalls =>
                            cases hStmtListCalls with
                            | cons hStmtCalls hRestCalls =>
                                apply
                                  Block.preserves_cons_of_compileStmtListFuel?_and_eval
                                    hCompile hBlocks hResultCalls
                                    (.cons_halt hStmt)
                                · intro headResult stmtFuel stmtSource
                                    stmtOutcome hHeadCompile hHeadBlocks
                                    hHeadCalls hHeadEval hFuelLt
                                  exact
                                    outcome_stmt_of_compileFuel?_and_eval_with_calls
                                      generated hHeadCompile hHeadBlocks hHeadCalls
                                      hHeadEval
                                      hStmtWF hStmtFrameSafe hStmtCalls
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
                                · intro headResult tailResult tailInput
                                    tailFuel tailSource tailOutcome
                                    hFallthrough hTailCompile hTailBlocks
                                    hTailCalls hTailEval hFuelLt
                                  have hTailBlockCompile :
                                      TypedCfgCompiler.compileBlockFuel?
                                          (listFuel + 1)
                                          { stmts := rest } ctx headResult.next
                                          (TypedCfgCompiler.restLabel supply)
                                          tailInput regular =
                                        some tailResult := by
                                    simpa [TypedCfgCompiler.compileBlockFuel?]
                                      using hTailCompile
                                  exact
                                    outcome_block_of_compileFuel?_and_eval_with_calls
                                      generated hTailBlockCompile hTailBlocks
                                      hTailCalls
                                      hTailEval
                                      hRestWF hRestFrameSafe
                                      (.mk hRestCalls)
                                      hSupports hProcs hTerminal
                                      hProgramWF hProgramFrameSafe
  termination_by sourceFuel

  /--
  Uniform preservation for every Structured statement, including concrete
  generated procedure calls and return dispatch.
  -/
  theorem outcome_stmt_of_compileFuel?_and_eval_with_calls
      {compilerFuel sourceFuel : Nat}
      {program : Structured.Program} {stmt : Structured.Stmt}
      {entryShapes : TypedCfgCompiler.ProcEntryShapes}
      {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
      {entry regular : Assembly.Label} {input : TypedCfg.Shape}
      {result : TypedCfgCompiler.Result} {cfg : TypedCfg.Program}
      {source : RunState} {outcome : Structured.Outcome}
      {tokens : List Word}
      {canBreak canContinue canLeave : Bool}
      (generated :
        Program.GeneratedContext program entryShapes cfg)
      (hCompile :
        TypedCfgCompiler.compileStmtFuel? compilerFuel stmt ctx
            supply entry input regular =
          some result)
      (hBlocks : BlocksInProgram result cfg)
      (hResultCalls : CallsInProgram result generated.calls)
      (hEval :
        Structured.Stmt.Eval program sourceFuel stmt source outcome)
      (hWF :
        Structured.Stmt.WF canBreak canContinue canLeave stmt)
      (hFrameSafe : stmt.FrameSafe)
      (hCalls :
        Structured.ProcList.StmtCallsResolved program.procs stmt)
      (hSupports :
        OutcomeSimulation.ContextSupports ctx
          canBreak canContinue canLeave)
      (hProcs : ctx.procs = program.procs)
      (hTerminal :
        ∀ kind, Stmt.Terminal.RelSafe kind)
      (hProgramWF : program.WF)
      (hProgramFrameSafe : program.FrameSafe) :
      OutcomeSimulation.Preserves result cfg entry
        (OutcomeSimulation.Continuations.ofContext ctx regular)
        source outcome tokens := by
    cases compilerFuel with
    | zero =>
        simp [TypedCfgCompiler.compileStmtFuel?] at hCompile
    | succ compilerFuel =>
        cases hEval with
        | code hRun =>
            cases hFrameSafe with
            | code hCodeSafe =>
                exact
                  Stmt.outcome_code_of_compileStmtFuel?
                    hCompile hBlocks hCodeSafe hRun
        | if_false hCond =>
            cases hFrameSafe with
            | if_ hCondSafe hBodySafe =>
                exact
                  Stmt.outcome_if_false_of_compileStmtFuel?
                    hCompile hBlocks hCondSafe hCond
        | @if_true fuel _ _ _ _ _ hCond hBodyEval =>
            cases hWF with
            | if_ hBodyWF =>
                cases hFrameSafe with
                | if_ hCondSafe hBodyFrameSafe =>
                    cases hCalls with
                    | if_ hBodyCalls =>
                        apply
                          Stmt.outcome_if_true_of_compileStmtFuel?
                            hCompile hBlocks hResultCalls hCondSafe hCond
                        intro bodyInput bodyResult hBodyCompile hBodyBlocks
                          hBodyResultCalls
                        exact
                          (outcome_block_of_compileFuel?_and_eval_with_calls
                            generated hBodyCompile hBodyBlocks hBodyResultCalls
                            hBodyEval hBodyWF
                            hBodyFrameSafe hBodyCalls hSupports hProcs
                            hTerminal hProgramWF hProgramFrameSafe).path
        | switch_none hScrutinee hPop hSelect =>
            cases hFrameSafe with
            | switch hScrutineeSafe hCaseSafe hDefaultSafe =>
                cases compilerFuel with
                | zero =>
                    rw [Switch.compileStmtFuel?_switch_one_eq_none]
                      at hCompile
                    cases hCompile
                | succ switchFuel =>
                    exact
                      Switch.outcome_none_of_compileStmtFuel?
                        hCompile hBlocks hScrutineeSafe
                        hScrutinee hPop hSelect
        | @switch_some fuel _ _ _ _ _ _ _ _ _ _ hScrutinee hPop
            hStateAfterPop hSelect hBodyEval =>
            subst hStateAfterPop
            cases hWF with
            | switch hCaseWF hDefaultWF =>
                cases hFrameSafe with
                | switch hScrutineeSafe hCaseSafe hDefaultSafe =>
                    cases hCalls with
                    | switch hCaseCalls hDefaultCalls =>
                        cases compilerFuel with
                        | zero =>
                            rw [Switch.compileStmtFuel?_switch_one_eq_none]
                              at hCompile
                            cases hCompile
                        | succ switchFuel =>
                            apply
                              Switch.outcome_some_of_compileStmtFuel?
                                hCompile hBlocks hResultCalls hScrutineeSafe
                                hScrutinee hPop hSelect
                            intro bodyCompilerFuel bodySupply bodyEntry
                              bodyShape bodyResult hBodyCompile hBodyBlocks
                              hBodyResultCalls
                            have hSelectedWF :=
                              Structured.Switch.wf_of_select
                                hCaseWF hDefaultWF hSelect
                            have hSelectedFrameSafe :=
                              switch_property_of_select
                                hCaseSafe hDefaultSafe hSelect
                            have hSelectedCalls :=
                              switch_property_of_select
                                hCaseCalls hDefaultCalls hSelect
                            exact
                              (outcome_block_of_compileFuel?_and_eval_with_calls
                                generated hBodyCompile hBodyBlocks
                                hBodyResultCalls
                                hBodyEval
                                hSelectedWF hSelectedFrameSafe hSelectedCalls
                                hSupports hProcs hTerminal
                                hProgramWF hProgramFrameSafe).path
        | @for_init_regular fuel _ _ _ _ _ _ _ hInitEval hLoopEval =>
            cases hWF with
            | for_ hInitWF hPostWF hBodyWF =>
                cases hFrameSafe with
                | for_ hInitSafe hCondSafe hPostSafe hBodySafe =>
                    cases hCalls with
                    | for_ hInitCalls hPostCalls hBodyCalls =>
                        apply
                          Loop.outcome_of_compileStmtFuel?_and_eval
                            hCompile hBlocks hResultCalls hCondSafe
                            (.for_init_regular hInitEval hLoopEval)
                        · intro initResult loopInput initFuel initSource
                            initOutcome hInitCompile hInitFallthrough
                            hInitBlocks hInitResultCalls hInitEval' hFuelLt
                          simpa [Loop.postContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hInitCompile hInitBlocks
                              hInitResultCalls hInitEval'
                              hInitWF hInitSafe hInitCalls
                              (OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
                        · intro initResult bodyResult condOutput bodyFuel
                            bodySource bodyOutcome hBodyCompile hBodyBlocks
                            hBodyResultCalls hBodyEval' hFuelLt
                          simpa [Loop.bodyContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hBodyCompile hBodyBlocks hBodyResultCalls
                              hBodyEval'
                              hBodyWF hBodySafe hBodyCalls
                              (OutcomeSimulation.ContextSupports.loopBody
                                hSupports regular
                                (LabelSupply.label supply 2))
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
                        · intro bodyResult postResult condOutput postFuel
                            postSource postOutcome hPostCompile hPostBlocks
                            hPostResultCalls hPostEval' hFuelLt
                          simpa [Loop.postContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hPostCompile hPostBlocks
                              hPostResultCalls
                              hPostEval'
                              hPostWF hPostSafe hPostCalls
                              (OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
        | @for_init_leave fuel _ _ _ _ _ _ hInitEval =>
            cases hWF with
            | for_ hInitWF hPostWF hBodyWF =>
                cases hFrameSafe with
                | for_ hInitSafe hCondSafe hPostSafe hBodySafe =>
                    cases hCalls with
                    | for_ hInitCalls hPostCalls hBodyCalls =>
                        apply
                          Loop.outcome_of_compileStmtFuel?_and_eval
                            hCompile hBlocks hResultCalls hCondSafe
                            (.for_init_leave hInitEval)
                        · intro initResult loopInput initFuel initSource
                            initOutcome hInitCompile hInitFallthrough
                            hInitBlocks hInitResultCalls hInitEval' hFuelLt
                          simpa [Loop.postContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hInitCompile hInitBlocks hInitResultCalls
                              hInitEval'
                              hInitWF hInitSafe hInitCalls
                              (OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
                        · intro initResult bodyResult condOutput bodyFuel
                            bodySource bodyOutcome hBodyCompile hBodyBlocks
                            hBodyResultCalls hBodyEval' hFuelLt
                          simpa [Loop.bodyContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hBodyCompile hBodyBlocks hBodyResultCalls
                              hBodyEval'
                              hBodyWF hBodySafe hBodyCalls
                              (OutcomeSimulation.ContextSupports.loopBody
                                hSupports regular
                                (LabelSupply.label supply 2))
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
                        · intro bodyResult postResult condOutput postFuel
                            postSource postOutcome hPostCompile hPostBlocks
                            hPostResultCalls hPostEval' hFuelLt
                          simpa [Loop.postContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hPostCompile hPostBlocks
                              hPostResultCalls
                              hPostEval'
                              hPostWF hPostSafe hPostCalls
                              (OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
        | @for_init_halt fuel _ _ _ _ _ _ _ hInitEval =>
            cases hWF with
            | for_ hInitWF hPostWF hBodyWF =>
                cases hFrameSafe with
                | for_ hInitSafe hCondSafe hPostSafe hBodySafe =>
                    cases hCalls with
                    | for_ hInitCalls hPostCalls hBodyCalls =>
                        apply
                          Loop.outcome_of_compileStmtFuel?_and_eval
                            hCompile hBlocks hResultCalls hCondSafe
                            (.for_init_halt hInitEval)
                        · intro initResult loopInput initFuel initSource
                            initOutcome hInitCompile hInitFallthrough
                            hInitBlocks hInitResultCalls hInitEval' hFuelLt
                          simpa [Loop.postContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hInitCompile hInitBlocks hInitResultCalls
                              hInitEval'
                              hInitWF hInitSafe hInitCalls
                              (OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
                        · intro initResult bodyResult condOutput bodyFuel
                            bodySource bodyOutcome hBodyCompile hBodyBlocks
                            hBodyResultCalls hBodyEval' hFuelLt
                          simpa [Loop.bodyContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hBodyCompile hBodyBlocks hBodyResultCalls
                              hBodyEval'
                              hBodyWF hBodySafe hBodyCalls
                              (OutcomeSimulation.ContextSupports.loopBody
                                hSupports regular
                                (LabelSupply.label supply 2))
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
                        · intro bodyResult postResult condOutput postFuel
                            postSource postOutcome hPostCompile hPostBlocks
                            hPostResultCalls hPostEval' hFuelLt
                          simpa [Loop.postContinuations,
                            OutcomeSimulation.Continuations.ofContext] using
                            (outcome_block_of_compileFuel?_and_eval_with_calls
                              generated hPostCompile hPostBlocks
                              hPostResultCalls
                              hPostEval'
                              hPostWF hPostSafe hPostCalls
                              (OutcomeSimulation.ContextSupports.withoutLoop
                                hSupports)
                              hProcs hTerminal
                              hProgramWF hProgramFrameSafe).path
        | brk =>
            cases hWF with
            | brk hAllowed =>
                rcases hSupports.breakLabel hAllowed with
                  ⟨target, hTarget⟩
                exact
                  Stmt.outcome_brk_of_compileStmtFuel?
                    hTarget hCompile hBlocks
        | cont =>
            cases hWF with
            | cont hAllowed =>
                rcases hSupports.continueLabel hAllowed with
                  ⟨target, hTarget⟩
                exact
                  Stmt.outcome_cont_of_compileStmtFuel?
                    hTarget hCompile hBlocks
        | leave hReturns =>
            cases hWF with
            | leave hAllowed =>
                rcases hSupports.leaveLabel hAllowed with
                  ⟨target, hTarget⟩
                exact
                  Stmt.outcome_leave_of_compileStmtFuel?
                    hTarget hCompile hBlocks
        | @call_regular fuel name state proc args callerStack stack
            bodyState returned frame hLookup hSplit hBody hPop hAttach =>
            have hCompilerLookup :
                Structured.ProcList.lookup? name ctx.procs = some proc := by
              simpa [hProcs] using hLookup
            have hProcWF :=
              Structured.Program.procWF_of_lookup? hProgramWF hLookup
            have hProcFrameSafe :=
              Structured.Program.procFrameSafe_of_lookup?
                hProgramFrameSafe hLookup
            have hProcCalls :=
              Structured.Program.procCallsResolved_of_lookup?
                hProgramWF hLookup
            rcases
                Call.components_of_compileStmtFuel?_call
                  hCompilerLookup hCompile with
              ⟨returnShape, output, hReturnShape, hCallType, hResult⟩
            subst result
            let site : TypedCfgCompiler.DispatchSite :=
              { procName := name
                token := Structured.Stmt.callToken supply
                returnLabel := regular
                caseLabel := .generated supply 10000 }
            have hSiteMem : site ∈ generated.calls := by
              apply hResultCalls site
              simp [site]
            rcases generated.procFragment_of_lookup? hLookup with
              ⟨fragment, hFragmentBlocks, hFragmentCalls⟩
            let procCtx : TypedCfgCompiler.Context :=
              { procs := program.procs
                leaveLabel? := some (ProcLabel.exit proc.name) }
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body procCtx fragment.supply fragment.entry
                    fragment.input (ProcLabel.exit proc.name) =
                  some fragment.result := by
              simpa [TypedCfgCompiler.compileBlock?, procCtx] using
                fragment.compile
            have hProcSupports :
                OutcomeSimulation.ContextSupports procCtx
                  false false true := by
              exact
                { breakLabel := by simp
                  continueLabel := by simp
                  leaveLabel := by
                    intro _hAllowed
                    exact ⟨ProcLabel.exit proc.name, rfl⟩ }
            have hBodyPreserves :=
              outcome_block_of_compileFuel?_and_eval_with_calls
                (tokens := Structured.Stmt.callToken supply :: tokens)
                generated hFragmentCompile hFragmentBlocks hFragmentCalls
                hBody hProcWF.2.2 hProcFrameSafe hProcCalls
                hProcSupports (by rfl) hTerminal
                hProgramWF hProgramFrameSafe
            have hName :=
              Structured.ProcList.name_of_lookup? hLookup
            have hFrameEq :=
              CallStack.poppedFrame_eq_of_regular_eval hBody hPop
            refine ⟨?_, ?_⟩
            · intro target hRel
              rcases
                  Call.entry_eventually_of_compileStmtFuel?
                    hCompilerLookup hCompile hBlocks hRel hSplit hProcWF with
                ⟨targetAtEntry, hCallEntry, hCallRel⟩
              have hAdapter :
                  cfg.Eventually (ProcLabel.entry name) targetAtEntry
                    (.jump fragment.entry targetAtEntry) := by
                simpa [hName] using
                  generated.eventually_procEntry
                    (fragment := fragment) targetAtEntry
              rcases
                  hBodyPreserves.to_regular_path
                    targetAtEntry hCallRel with
                ⟨targetAtExit, hBodyEventually, hBodyRel⟩
              have hSiteProc : site.procName = proc.name := by
                simp [site, hName]
              have hRetc : frame.retc = proc.retc := by
                rw [hFrameEq]
              rcases
                  Call.dispatch_eventually generated hLookup hSiteProc
                    hSiteMem hBodyRel hPop hAttach hRetc with
                ⟨targetFinal, hDispatchEventually, hFinalRel⟩
              refine ⟨.jump regular targetFinal, ?_, ?_⟩
              · exact
                  TypedCfg.Program.Eventually.bind_jump hCallEntry
                    (TypedCfg.Program.Eventually.bind_jump hAdapter
                      (TypedCfg.Program.Eventually.bind_jump
                        hBodyEventually hDispatchEventually))
              · exact
                  OutcomeSimulation.Rel.regular_iff.mpr
                    ⟨rfl, hFinalRel⟩
            · intro _hRegular
              exact ⟨returnShape, rfl⟩
        | @call_leave fuel name state proc args callerStack stack
            bodyState returned frame hLookup hSplit hBody hPop hAttach =>
            have hCompilerLookup :
                Structured.ProcList.lookup? name ctx.procs = some proc := by
              simpa [hProcs] using hLookup
            have hProcWF :=
              Structured.Program.procWF_of_lookup? hProgramWF hLookup
            have hProcFrameSafe :=
              Structured.Program.procFrameSafe_of_lookup?
                hProgramFrameSafe hLookup
            have hProcCalls :=
              Structured.Program.procCallsResolved_of_lookup?
                hProgramWF hLookup
            rcases
                Call.components_of_compileStmtFuel?_call
                  hCompilerLookup hCompile with
              ⟨returnShape, output, hReturnShape, hCallType, hResult⟩
            subst result
            let site : TypedCfgCompiler.DispatchSite :=
              { procName := name
                token := Structured.Stmt.callToken supply
                returnLabel := regular
                caseLabel := .generated supply 10000 }
            have hSiteMem : site ∈ generated.calls := by
              apply hResultCalls site
              simp [site]
            rcases generated.procFragment_of_lookup? hLookup with
              ⟨fragment, hFragmentBlocks, hFragmentCalls⟩
            let procCtx : TypedCfgCompiler.Context :=
              { procs := program.procs
                leaveLabel? := some (ProcLabel.exit proc.name) }
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body procCtx fragment.supply fragment.entry
                    fragment.input (ProcLabel.exit proc.name) =
                  some fragment.result := by
              simpa [TypedCfgCompiler.compileBlock?, procCtx] using
                fragment.compile
            have hProcSupports :
                OutcomeSimulation.ContextSupports procCtx
                  false false true := by
              exact
                { breakLabel := by simp
                  continueLabel := by simp
                  leaveLabel := by
                    intro _hAllowed
                    exact ⟨ProcLabel.exit proc.name, rfl⟩ }
            have hBodyPreserves :=
              outcome_block_of_compileFuel?_and_eval_with_calls
                (tokens := Structured.Stmt.callToken supply :: tokens)
                generated hFragmentCompile hFragmentBlocks hFragmentCalls
                hBody hProcWF.2.2 hProcFrameSafe hProcCalls
                hProcSupports (by rfl) hTerminal
                hProgramWF hProgramFrameSafe
            have hName :=
              Structured.ProcList.name_of_lookup? hLookup
            have hFrameEq :=
              CallStack.poppedFrame_eq_of_leave_eval hBody hPop
            refine ⟨?_, ?_⟩
            · intro target hRel
              rcases
                  Call.entry_eventually_of_compileStmtFuel?
                    hCompilerLookup hCompile hBlocks hRel hSplit hProcWF with
                ⟨targetAtEntry, hCallEntry, hCallRel⟩
              have hAdapter :
                  cfg.Eventually (ProcLabel.entry name) targetAtEntry
                    (.jump fragment.entry targetAtEntry) := by
                simpa [hName] using
                  generated.eventually_procEntry
                    (fragment := fragment) targetAtEntry
              have hBodyPath :=
                OutcomeSimulation.Path.to_leave
                  (program := cfg)
                  (targetLabel := ProcLabel.exit proc.name)
                  (by rfl) hBodyPreserves.path
              rcases hBodyPath targetAtEntry hCallRel with
                ⟨targetAtExit, hBodyEventually, hBodyRel⟩
              have hSiteProc : site.procName = proc.name := by
                simp [site, hName]
              have hRetc : frame.retc = proc.retc := by
                rw [hFrameEq]
              rcases
                  Call.dispatch_eventually generated hLookup hSiteProc
                    hSiteMem hBodyRel hPop hAttach hRetc with
                ⟨targetFinal, hDispatchEventually, hFinalRel⟩
              refine ⟨.jump regular targetFinal, ?_, ?_⟩
              · exact
                  TypedCfg.Program.Eventually.bind_jump hCallEntry
                    (TypedCfg.Program.Eventually.bind_jump hAdapter
                      (TypedCfg.Program.Eventually.bind_jump
                        hBodyEventually hDispatchEventually))
              · exact
                  OutcomeSimulation.Rel.regular_iff.mpr
                    ⟨rfl, hFinalRel⟩
            · intro _hRegular
              exact ⟨returnShape, rfl⟩
        | @call_halt fuel name state proc args callerStack bodyState kind
            hLookup hSplit hBody =>
            have hCompilerLookup :
                Structured.ProcList.lookup? name ctx.procs = some proc := by
              simpa [hProcs] using hLookup
            have hProcWF :=
              Structured.Program.procWF_of_lookup? hProgramWF hLookup
            have hProcFrameSafe :=
              Structured.Program.procFrameSafe_of_lookup?
                hProgramFrameSafe hLookup
            have hProcCalls :=
              Structured.Program.procCallsResolved_of_lookup?
                hProgramWF hLookup
            rcases generated.procFragment_of_lookup? hLookup with
              ⟨fragment, hFragmentBlocks, hFragmentCalls⟩
            let procCtx : TypedCfgCompiler.Context :=
              { procs := program.procs
                leaveLabel? := some (ProcLabel.exit proc.name) }
            have hFragmentCompile :
                TypedCfgCompiler.compileBlockFuel?
                    (TypedCfgCompiler.blockFuel proc.body + 1)
                    proc.body procCtx fragment.supply fragment.entry
                    fragment.input (ProcLabel.exit proc.name) =
                  some fragment.result := by
              simpa [TypedCfgCompiler.compileBlock?, procCtx] using
                fragment.compile
            have hProcSupports :
                OutcomeSimulation.ContextSupports procCtx
                  false false true := by
              exact
                { breakLabel := by simp
                  continueLabel := by simp
                  leaveLabel := by
                    intro _hAllowed
                    exact ⟨ProcLabel.exit proc.name, rfl⟩ }
            have hBodyPreserves :=
              outcome_block_of_compileFuel?_and_eval_with_calls
                (tokens := Structured.Stmt.callToken supply :: tokens)
                generated hFragmentCompile hFragmentBlocks hFragmentCalls
                hBody hProcWF.2.2 hProcFrameSafe hProcCalls
                hProcSupports (by rfl) hTerminal
                hProgramWF hProgramFrameSafe
            have hName :=
              Structured.ProcList.name_of_lookup? hLookup
            apply OutcomeSimulation.Preserves.of_path_of_nonregular
              (by simp)
            intro target hRel
            rcases
                Call.entry_eventually_of_compileStmtFuel?
                  hCompilerLookup hCompile hBlocks hRel hSplit hProcWF with
              ⟨targetAtEntry, hCallEntry, hCallRel⟩
            have hAdapter :
                cfg.Eventually (ProcLabel.entry name) targetAtEntry
                  (.jump fragment.entry targetAtEntry) := by
              simpa [hName] using
                generated.eventually_procEntry
                  (fragment := fragment) targetAtEntry
            rcases hBodyPreserves.path targetAtEntry hCallRel with
              ⟨targetOutcome, hBodyEventually, hOutcomeRel⟩
            rcases OutcomeSimulation.Rel.halt_elim hOutcomeRel with
              ⟨targetBefore, targetFinal, rfl, hTargetStep, hFinalRel⟩
            refine ⟨.halt kind targetBefore, ?_, ?_⟩
            · exact
                TypedCfg.Program.Eventually.bind_jump hCallEntry
                  (TypedCfg.Program.Eventually.bind_jump
                    hAdapter hBodyEventually)
            · exact
                OutcomeSimulation.Rel.halt_iff.mpr
                  ⟨rfl, targetFinal, hTargetStep, hFinalRel⟩
        | terminal hStep =>
            exact
              Stmt.outcome_terminal_of_compileStmtFuel?
                (hTerminal _) hCompile hBlocks hStep
  termination_by sourceFuel
  decreasing_by
    all_goals simp_wf
    all_goals omega

end

namespace Program

/--
Successful checked generation preserves a complete Structured main-block
evaluation through the generated TypedCfg, with all procedure-call evidence
constructed internally.
-/
theorem path_of_generateWithProcEntryShapes?_and_eval
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    {source : RunState} {outcome : Structured.Outcome}
    {sourceFuel : Nat}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes?
          sourceProgram entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped)
    (hWF : sourceProgram.WF)
    (hFrameSafe : sourceProgram.FrameSafe)
    (hTerminal : ∀ kind, Stmt.Terminal.RelSafe kind)
    (hEval :
      Structured.Block.Eval sourceProgram sourceFuel
        sourceProgram.body source outcome) :
    OutcomeSimulation.Path cfg TypedCfgCompiler.entryLabel
      (OutcomeSimulation.Continuations.ofContext
        { procs := sourceProgram.procs } ProcLabel.programEnd)
      source outcome [] := by
  let generated :=
    GeneratedContext.of_generate hGenerate hWellTyped
  have hMainCompile :
      TypedCfgCompiler.compileBlockFuel?
          (TypedCfgCompiler.blockFuel sourceProgram.body + 1)
          sourceProgram.body { procs := sourceProgram.procs }
          0 TypedCfgCompiler.entryLabel TypedCfg.Shape.caller
          ProcLabel.programEnd =
        some generated.main := by
    simpa [TypedCfgCompiler.compileBlock?] using generated.mainCompile
  have hSupports :
      OutcomeSimulation.ContextSupports
        { procs := sourceProgram.procs } false false false := by
    exact
      { breakLabel := by simp
        continueLabel := by simp
        leaveLabel := by simp }
  exact
    (outcome_block_of_compileFuel?_and_eval_with_calls
      (tokens := []) generated hMainCompile generated.mainBlocks
      generated.mainCalls hEval hWF.2.2.2.2 hFrameSafe.2
      hWF.2.2.2.1 hSupports (by rfl) hTerminal hWF hFrameSafe).path

/--
Artifact-facing form of whole-program Structured-to-TypedCfg preservation.
-/
theorem path_of_artifactWithProcEntryShapes?_and_eval
    {sourceProgram : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {artifact : TypedCfgCompiler.CompileArtifact}
    {source : RunState} {outcome : Structured.Outcome}
    {sourceFuel : Nat}
    (hArtifact :
      TypedCfgCompiler.artifactWithProcEntryShapes?
          sourceProgram entryShapes =
        some artifact)
    (hWF : sourceProgram.WF)
    (hFrameSafe : sourceProgram.FrameSafe)
    (hTerminal : ∀ kind, Stmt.Terminal.RelSafe kind)
    (hEval :
      Structured.Block.Eval sourceProgram sourceFuel
        sourceProgram.body source outcome) :
    OutcomeSimulation.Path artifact.cfg TypedCfgCompiler.entryLabel
      (OutcomeSimulation.Continuations.ofContext
        { procs := sourceProgram.procs } ProcLabel.programEnd)
      source outcome [] := by
  unfold TypedCfgCompiler.artifactWithProcEntryShapes? at hArtifact
  cases hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes?
        sourceProgram entryShapes with
  | none =>
      simp [hGenerate] at hArtifact
  | some cfg =>
      by_cases hCheck : cfg.wellTyped? = true
      · simp [hGenerate, hCheck] at hArtifact
        cases hArtifact
        exact
          path_of_generateWithProcEntryShapes?_and_eval
            hGenerate
            (TypedCfg.Program.wellTyped_of_check hCheck)
            hWF hFrameSafe hTerminal hEval
      · simp [hGenerate, hCheck] at hArtifact

end Program

end TypedCfgPreservation
end Structured
end EvmCompiler
