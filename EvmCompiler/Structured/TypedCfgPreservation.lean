import EvmCompiler.Structured.TypedCfgCompiler
import EvmCompiler.TypedCfg.Preservation

namespace EvmCompiler
namespace Structured
namespace TypedCfgPreservation

/--
Realize Structured's ghost return frames as the concrete return-token and
caller-stack suffix carried by TypedCfg procedure execution.
-/
def realizeStack : EvmYul.Stack Word → List ReturnDest → List Word →
    Option (EvmYul.Stack Word)
  | stack, [], [] => some stack
  | stack, frame :: returns, token :: tokens =>
      realizeStack
        (stack ++ [token] ++ frame.callerStack) returns tokens
  | _stack, _returns, _tokens => none

/--
Source-to-CFG state relation.

The stack is related through concrete realization of ghost return frames.
Control position and lowering-only resource counters are compared through the
shared `Assembly.SameData` observation boundary, while available gas remains
equal so the Structured `gas` primitive has the same CFG-level meaning.
-/
def SameRuntimeData (target source : EVMState) : Prop :=
  Assembly.SameData target source ∧
    target.gasAvailable = source.gasAvailable

def StateRel (source : RunState) (tokens : List Word)
    (target : EVMState) : Prop :=
  ∃ stack,
    realizeStack source.evm.stack source.returns tokens = some stack ∧
      SameRuntimeData target { source.evm with stack := stack }

namespace StateRel

theorem initial (state : EVMState) :
    StateRel (RunState.initial state) [] state :=
  ⟨state.stack, rfl, Assembly.SameData.refl state, rfl⟩

theorem pushReturn
    {source : RunState} {tokens : List Word} {target : EVMState}
    {args callerStack realized : EvmYul.Stack Word}
    {retc : Nat} {token : Word}
    (hRealize :
      realizeStack
          (args ++ [token] ++ callerStack)
          source.returns tokens =
        some realized)
    (hSame :
      SameRuntimeData target { source.evm with stack := realized }) :
    StateRel
      ((source.withEVM { source.evm with stack := args }).pushReturn
        callerStack retc)
      (token :: tokens) target := by
  refine ⟨realized, ?_, ?_⟩
  · simpa [realizeStack, RunState.pushReturn, RunState.withEVM,
      List.append_assoc] using hRealize
  · simpa [RunState.pushReturn, RunState.withEVM] using hSame

end StateRel

namespace BasicInstr

theorem runAt_toCfg
    {instr : Structured.BasicInstr} {input output : TypedCfg.Shape}
    {state : EVMState}
    (hType :
      TypedCfg.Instr.type?
        (TypedCfgCompiler.BasicInstr.toCfg instr) input =
        some output) :
    TypedCfg.Instr.runAt
        (TypedCfgCompiler.BasicInstr.toCfg instr) input state =
      (instr.step state).map fun final => (final, output) := by
  unfold TypedCfg.Instr.runAt
  rw [hType]
  cases instr <;>
    rfl

end BasicInstr

namespace Code

/--
Straight-line Structured code and the generated TypedCfg body have identical
runtime behavior. The TypedCfg side additionally returns the symbolic output
shape already computed by the checked body typer.
-/
theorem runBody_toCfg
    {code : Structured.Code} {input output : TypedCfg.Shape}
    {state : EVMState}
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    TypedCfg.Block.runBody (TypedCfgCompiler.Code.toCfg code) input state =
      (Structured.Code.run code state).map fun final => (final, output) := by
  induction code generalizing input output state with
  | nil =>
      simp [TypedCfgCompiler.Code.type?, TypedCfgCompiler.Code.toCfg,
        TypedCfg.Block.bodyType?, TypedCfg.Block.runBody,
        Structured.Code.run] at hType ⊢
      cases hType
      rfl
  | cons instr rest ih =>
      unfold TypedCfgCompiler.Code.type? at hType
      simp only [TypedCfgCompiler.Code.toCfg, List.map_cons,
        TypedCfg.Block.bodyType?] at hType
      cases hHeadType :
          TypedCfg.Instr.type?
            (TypedCfgCompiler.BasicInstr.toCfg instr) input with
      | none =>
          simp [hHeadType] at hType
      | some middle =>
          simp [hHeadType] at hType
          have hTailType :
              TypedCfgCompiler.Code.type? rest middle = some output := by
            simpa [TypedCfgCompiler.Code.type?,
              TypedCfgCompiler.Code.toCfg] using hType
          simp only [TypedCfgCompiler.Code.toCfg, List.map_cons]
          unfold TypedCfg.Block.runBody
          rw [BasicInstr.runAt_toCfg hHeadType]
          cases hStep : instr.step state with
          | error err =>
              simp only [hStep, Except.map, Bind.bind, Except.bind,
                Structured.Code.run]
          | ok state' =>
              simp only [hStep, Except.map, Bind.bind, Except.bind,
                Structured.Code.run]
              exact ih hTailType

theorem runState_toCfg
    {code : Structured.Code} {input output : TypedCfg.Shape}
    {state : RunState}
    (hType : TypedCfgCompiler.Code.type? code input = some output) :
    TypedCfg.Block.runBody (TypedCfgCompiler.Code.toCfg code) input
        state.evm =
      (Structured.Code.runState code state).map fun final =>
        (final.evm, output) := by
  rw [runBody_toCfg hType]
  unfold Structured.Code.runState
  cases hRun : Structured.Code.run code state.evm with
  | error err =>
      simp only [Bind.bind, Except.bind, Except.map]
  | ok final =>
      simp only [Bind.bind, Except.bind, Except.map]
      rfl

/--
A generated conditional block follows the same branch and produces the same
post-pop EVM state as the independent Structured condition evaluator.
-/
theorem run_jumpi_toCfg
    {code : Structured.Code} {input output : TypedCfg.Shape}
    {state final : RunState} {cond : Bool}
    {target fallthrough : Assembly.Label}
    (hType : TypedCfgCompiler.Code.type? code input = some output)
    (hCond :
      Structured.Code.runConditionState code state = .ok (final, cond)) :
    TypedCfg.Block.run
        { label := target
          input := input
          body := TypedCfgCompiler.Code.toCfg code
          output := output
          term := .jumpi target fallthrough }
        state.evm =
      .ok
        (.jump (if cond then target else fallthrough) final.evm) := by
  unfold Structured.Code.runConditionState at hCond
  unfold Structured.Code.runCondition at hCond
  cases hCode : Structured.Code.run code state.evm with
  | error err =>
      simp [hCode, Bind.bind, Except.bind] at hCond
  | ok afterCode =>
      cases hPop : afterCode.stack.pop with
      | none =>
          simp [hCode, Structured.Code.popCondition, hPop,
            Bind.bind, Except.bind] at hCond
      | some popped =>
          rcases popped with ⟨stack, value⟩
          simp [hCode, Structured.Code.popCondition, hPop,
            Bind.bind, Except.bind] at hCond
          rcases hCond with ⟨hFinal, hBool⟩
          subst final
          by_cases hZero : value = EvmYul.UInt256.ofNat 0
          · have hBne :
                (value != EvmYul.UInt256.ofNat 0) = false := by
              subst value
              exact TypedCfg.Preservation.uint256_bne_zero_self
            have hCondFalse : cond = false := by
              calc
                cond = (value != EvmYul.UInt256.ofNat 0) := hBool.symm
                _ = false := hBne
            rw [hCondFalse]
            simp [TypedCfg.Block.run, runBody_toCfg hType, hCode,
              Except.map, Bind.bind, Except.bind, TypedCfg.Block.runTerm,
              hPop, hZero, hBne]
          · have hBne :
                (value != EvmYul.UInt256.ofNat 0) = true :=
              TypedCfg.Preservation.uint256_bne_zero_of_ne value hZero
            have hCondTrue : cond = true := by
              calc
                cond = (value != EvmYul.UInt256.ofNat 0) := hBool.symm
                _ = true := hBne
            rw [hCondTrue]
            simp [TypedCfg.Block.run, runBody_toCfg hType, hCode,
              Except.map, Bind.bind, Except.bind, TypedCfg.Block.runTerm,
              hPop, hZero, hBne]

end Code

/--
View a compiled fragment as an independently executable CFG. The continuation
label need not occur in `blocks`: `TypedCfg.Program.runN` can expose reaching it
as a residual jump.
-/
def resultProgram (result : TypedCfgCompiler.Result)
    (entry : Assembly.Label) : TypedCfg.Program where
  entry := entry
  blocks := result.blocks

/--
Every block emitted for a compiler result is available through the ambient
program's lookup function.

Fragment compilers accept arbitrary symbolic entries, so this property is
derived from the final certified CFG instead of being assumed from a fragment
in isolation.
-/
def BlocksInProgram (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) : Prop :=
  ∀ block, block ∈ result.blocks →
    program.findBlock? block.label = some block

namespace BlocksInProgram

theorem of_subset
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    (hUnique : program.LabelsUnique)
    (hSubset :
      ∀ block, block ∈ result.blocks → block ∈ program.blocks) :
    BlocksInProgram result program := by
  intro block hMem
  exact
    TypedCfg.Program.findBlock?_eq_some_of_mem hUnique
      (hSubset block hMem)

theorem of_subset_of_wellTyped
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    (hWellTyped : program.WellTyped)
    (hSubset :
      ∀ block, block ∈ result.blocks → block ∈ program.blocks) :
    BlocksInProgram result program :=
  of_subset hWellTyped.1 hSubset

theorem eventually_of_run
    {result : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {block : TypedCfg.Block} {state : EVMState}
    {outcome : TypedCfg.Outcome}
    (hBlocks : BlocksInProgram result program)
    (hMem : block ∈ result.blocks)
    (hRun : block.run state = .ok outcome) :
    program.Eventually block.label state outcome := by
  have hFind := hBlocks block hMem
  refine ⟨1, ?_⟩
  cases outcome <;>
    simp [TypedCfg.Program.runN, TypedCfg.Program.step, hFind, hRun,
      Bind.bind, Except.bind]

theorem left_of_append
    {left right : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    (hBlocks : BlocksInProgram (left.append right) program) :
    BlocksInProgram left program := by
  intro block hMem
  apply hBlocks block
  simp [TypedCfgCompiler.Result.append, hMem]

theorem right_of_append
    {left right : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    (hBlocks : BlocksInProgram (left.append right) program) :
    BlocksInProgram right program := by
  intro block hMem
  apply hBlocks block
  simp [TypedCfgCompiler.Result.append, hMem]

end BlocksInProgram

/--
Semantic certificate for a compiler result that completes normally.

The output shape is compiler metadata; the execution witness is stated in the
ambient certified CFG. This is the unit composed by statement-list proofs.
-/
def RegularExecution (result : TypedCfgCompiler.Result)
    (program : TypedCfg.Program) (entry regular : Assembly.Label)
    (initial final : EVMState) : Prop :=
  ∃ output : TypedCfg.Shape,
    result.fallthrough? = some output ∧
      program.Eventually entry initial
        (TypedCfg.Outcome.jump regular final)

namespace RegularExecution

theorem append
    {left right : TypedCfgCompiler.Result} {program : TypedCfg.Program}
    {entry middle regular : Assembly.Label}
    {initial afterLeft final : EVMState}
    (hLeft :
      RegularExecution left program entry middle initial afterLeft)
    (hRight :
      RegularExecution right program middle regular afterLeft final) :
    RegularExecution (left.append right) program entry regular initial final := by
  rcases hLeft with ⟨leftOutput, hLeftFallthrough, hLeftEventually⟩
  rcases hRight with ⟨rightOutput, hRightFallthrough, hRightEventually⟩
  refine ⟨rightOutput, ?_, ?_⟩
  · simp [TypedCfgCompiler.Result.append, hRightFallthrough]
  · exact
      TypedCfg.Program.Eventually.bind_jump
        hLeftEventually hRightEventually

end RegularExecution

namespace Program

/--
Successful whole-program generation exposes the exact main-fragment compiler
result, and TypedCfg well-typedness turns its obvious block-list inclusion into
ambient lookup containment.
-/
theorem main_result_of_generateWithProcEntryShapes?
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? source entryShapes =
        some cfg)
    (hWellTyped : cfg.WellTyped) :
    ∃ main : TypedCfgCompiler.Result,
      TypedCfgCompiler.compileBlock? source.body
          { procs := source.procs } 0 TypedCfgCompiler.entryLabel
          TypedCfg.Shape.caller ProcLabel.programEnd =
        some main ∧
      BlocksInProgram main cfg := by
  unfold TypedCfgCompiler.generateWithProcEntryShapes? at hGenerate
  cases hMain :
      TypedCfgCompiler.compileBlock? source.body
        { procs := source.procs } 0 TypedCfgCompiler.entryLabel
        TypedCfg.Shape.caller ProcLabel.programEnd with
  | none =>
      simp [hMain] at hGenerate
  | some main =>
      cases hProcs :
          TypedCfgCompiler.lowerProcBodiesWithShapes? entryShapes
            source.procs source.procs main.next with
      | none =>
          simp [hMain, hProcs] at hGenerate
      | some procResult =>
          rcases procResult with ⟨procBlocks, next, procCalls⟩
          simp [hMain, hProcs] at hGenerate
          cases hGenerate
          refine ⟨main, by simpa using hMain, ?_⟩
          apply BlocksInProgram.of_subset_of_wellTyped hWellTyped
          intro block hMem
          simp [hMem]

theorem main_result_of_artifactWithProcEntryShapes?
    {source : Structured.Program}
    {entryShapes : TypedCfgCompiler.ProcEntryShapes}
    {artifact : TypedCfgCompiler.CompileArtifact}
    (hArtifact :
      TypedCfgCompiler.artifactWithProcEntryShapes? source entryShapes =
        some artifact) :
    ∃ main : TypedCfgCompiler.Result,
      TypedCfgCompiler.compileBlock? source.body
          { procs := source.procs } 0 TypedCfgCompiler.entryLabel
          TypedCfg.Shape.caller ProcLabel.programEnd =
        some main ∧
      BlocksInProgram main artifact.cfg := by
  unfold TypedCfgCompiler.artifactWithProcEntryShapes? at hArtifact
  cases hGenerate :
      TypedCfgCompiler.generateWithProcEntryShapes? source entryShapes with
  | none =>
      simp [hGenerate] at hArtifact
  | some cfg =>
      by_cases hCheck : cfg.wellTyped? = true
      · simp [hGenerate, hCheck] at hArtifact
        cases hArtifact
        exact
          main_result_of_generateWithProcEntryShapes? hGenerate
            (TypedCfg.Program.wellTyped_of_check hCheck)
      · simp [hGenerate, hCheck] at hArtifact

end Program

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

end Stmt

namespace Block

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

end TypedCfgPreservation
end Structured
end EvmCompiler
