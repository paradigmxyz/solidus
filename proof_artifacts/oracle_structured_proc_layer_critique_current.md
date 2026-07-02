# Oracle request: critique current procedure-aware Structured layer approach

Mode requested: hostile architecture critique and repair advice, not just a
single Lean syntax fix.

Repository: `/Users/dan/Projects/evm-compiler`

Relevant module:
`EvmCompiler/Structured/Preservation.lean`

Lean version/package:
`lean-toolchain` uses Lean `v4.22.0`; project depends on Nethermind
`EVMYulLean`.

## Goal

We are refactoring the `Structured` control layer into a procedure-aware layer
above labeled assembly:

- source syntax has structured control (`if`, `switch`, `for`, `break`,
  `continue`) plus procedure control (`call`, procedure-delimited `leave`) and
  EVM terminal opcodes.
- source machine has ghost return-destination state:
  `RunState.returns : List ReturnDest`.
- compiled assembly realizes returns using concrete hidden stack tokens and a
  generated static return-dispatch block.
- public `leaveScope` is gone; `leave` is an abrupt outcome caught only at
  procedure boundaries.
- desired adjacent theorem: checked Structured-to-labeled-assembly preservation.
- higher layers/top theorem may be disabled temporarily, but the core layer
  should be rebuilt cleanly.

The user asked specifically for a critique of my current approach to this
layer, then to continue locally. Please judge whether the proof architecture is
good, whether it will scale to calls/returns, and what changes would reduce
Lean proof blowup without weakening the theorem.

## Source syntax and semantics

`EvmCompiler/Structured/Syntax.lean`:

```lean
structure ReturnDest where
  callerStack : EvmYul.Stack Word
  retc : Nat

structure RunState where
  evm : EVMState
  returns : List ReturnDest

mutual
  structure Block where
    stmts : List Stmt

  inductive Stmt where
    | code (code : Code)
    | if_ (cond : Code) (body : Block)
    | switch (scrutinee : Code) (cases : List (Word × Block))
        (defaultBody : Option Block)
    | for_ (init : Block) (cond : Code) (post : Block) (body : Block)
    | brk
    | cont
    | leave
    | call (name : Name)
    | terminal (kind : Assembly.HaltKind)
end

structure Proc where
  name : Name
  argc : Nat
  retc : Nat
  body : Block

structure Program where
  procs : List Proc
  body : Block
```

`Stmt.Eval` includes:

```lean
| switch_none
    (hScrutinee : Code.runState scrutinee state = .ok stateAfterScrutinee)
    (hPop : stateAfterScrutinee.evm.stack.pop = some (stack, value))
    (hSelect : Switch.select value cases defaultBody = none) :
    Stmt.Eval program (fuel + 1)
      (.switch scrutinee cases defaultBody) state
      (Outcome.regular
        (stateAfterScrutinee.withEVM
          { stateAfterScrutinee.evm with stack := stack }))

| switch_some
    (hScrutinee : Code.runState scrutinee state = .ok stateAfterScrutinee)
    (hPop : stateAfterScrutinee.evm.stack.pop = some (stack, value))
    (hStateAfterPop :
      stateAfterPop =
        stateAfterScrutinee.withEVM
          { stateAfterScrutinee.evm with stack := stack })
    (hSelect : Switch.select value cases defaultBody = some body)
    (hBody : Block.Eval program fuel body stateAfterPop outcome) :
    Stmt.Eval program (fuel + 1)
      (.switch scrutinee cases defaultBody) state outcome

| leave (hReturns : state.returns ≠ []) :
    Stmt.Eval program fuel .leave state (Outcome.leave state)

| call_regular ...
| call_leave ...
| call_halt ...
```

Calls:

- lookup proc
- split `argc` arguments off the visible stack
- push ghost return frame `{ callerStack, retc }`
- run proc body
- on regular or `leave`, pop ghost return, check `retc`, attach return values
  to caller stack
- on halt, propagate halt
- `brk`/`cont` from proc body are invalid.

## Compiler shape

`EvmCompiler/Structured/Compiler.lean`:

```lean
def Stmt.switchTestCode (value : Word) : Code :=
  [BasicInstr.op .dup1, BasicInstr.push value, BasicInstr.op .eq]

def Stmt.switchTest (base : LabelSupply) (idx : Nat) (value : Word) :
    Assembly.Program :=
  (switchTestCode value).toAssembly ++
    [Assembly.Instr.jumpi (LabelSupply.label base (idx + 2))]

def Stmt.switchTests (base : LabelSupply) : Nat → List (Word × Block) →
    Assembly.Program
  | _idx, [] => []
  | idx, (value, _body) :: rest =>
      switchTest base idx value ++ switchTests base (idx + 1) rest
```

Switch compilation:

```lean
| .switch scrutinee cases defaultBody =>
  let endLabel := LabelSupply.label supply 0
  let defaultLabel := LabelSupply.label supply 1
  let compiledCases :=
    SwitchCases.compileFromCtx cases ctx endLabel supply
      (LabelSupply.next supply) 0
  let compiledDefault :=
    SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
      compiledCases.next
  { code :=
      scrutinee.toAssembly ++
        Stmt.switchTests supply 0 cases ++
        [Assembly.Instr.jump defaultLabel] ++
        compiledCases.code ++
        compiledDefault.code ++
        [Assembly.Instr.label endLabel]
    next := compiledDefault.next
    calls := compiledCases.calls ++ compiledDefault.calls }
```

Case bodies compile as:

```lean
| (_value, body) :: rest =>
    let caseLabel := LabelSupply.label base (idx + 2)
    let compiledBody := Block.compileFromCtx body ctx supply
    let compiledHead : CompileResult :=
      { code :=
          [ Assembly.Instr.label caseLabel
          , Assembly.Instr.prim .pop
          ] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel]
        next := compiledBody.next
        calls := compiledBody.calls }
    let compiledTail :=
      SwitchCases.compileFromCtx rest ctx endLabel base compiledHead.next
        (idx + 1)
    compiledHead.append compiledTail
```

Default body compiles as label/pop/body/jump end, or label/pop/jump end when
absent.

Procedure calls compile as:

```lean
| .call name =>
  let returnLabel := LabelSupply.label supply 0
  let token := Stmt.callToken supply
  match ProcList.lookup? name ctx.procs with
  | none => invalid
  | some proc =>
      [push token] ++ StackShuffle.sinkTopUnder proc.argc ++
      [jump (ProcLabel.entry name), label returnLabel]
```

Procedure bodies compile as:

```lean
[label (ProcLabel.entry proc.name)] ++ compiledBody.code ++
[label (ProcLabel.exit proc.name)]
```

Then dispatch blocks test hidden return token against call sites:
`dup (retc+1); push token; eq; jumpi returnCase`; return cases remove the
buried token and jump to the call site's static return label.

## Current preservation interfaces

Current adjacent theorem contracts:

```lean
def CompiledOutcomeRel (asm : Assembly.Program) (ctx : CompileContext)
    (fallthroughPc : Word) (source : Outcome)
    (target : Assembly.StepResult) (tokens : List Word) : Prop :=
  match source.mode, target with
  | .regular, .running targetState =>
      Frame.StateRel source.state targetState tokens ∧
        targetState.pc = fallthroughPc
  | .brk, .running targetState => -- jumped to ctx.breakLabel?
  | .cont, .running targetState => -- jumped to ctx.continueLabel?
  | .leave, .running targetState => -- jumped to ctx.leaveLabel?
  | .halt sourceKind, .halted targetHalt =>
      sourceKind = targetHalt.kind ∧
        Frame.StateRel source.state targetHalt.state tokens
  | _, _ => False

def StmtPreserves (program : Program) (ctx : CompileContext)
    (supply : LabelSupply) (stmt : Stmt) : Prop :=
  ∀ {pre post : Assembly.Program} {fuel : Nat}
    {source : RunState} {outcome : Outcome} {target : EVMState}
    {tokens : List Word},
    AssemblyProgram.PCFitsFrom pre (Stmt.compileFromCtxCore stmt ctx supply).code →
      ContextLabelsResolve
        (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++ post) ctx →
      ExactLabels
        (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++ post) →
      target.pc = Assembly.Program.pcAfter pre →
      Frame.StateRel source target tokens →
      Stmt.Eval program fuel stmt source outcome →
      ARunResult
        (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++ post)
        target
        (fun result =>
          CompiledOutcomeRel
            (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code ++ post)
            ctx
            (Assembly.Program.pcAfter
              (pre ++ (Stmt.compileFromCtxCore stmt ctx supply).code))
            outcome result tokens)
```

`BlockPreserves` is analogous for `Block.compileFromCtx`.

The state relation:

```lean
def materializeStack :
    EvmYul.Stack Word → List ReturnDest → List Word →
      Option (EvmYul.Stack Word)
  | visible, [], [] => some visible
  | visible, frame :: rest, token :: tokens => do
      let outer ← materializeStack frame.callerStack rest tokens
      some (visible ++ [token] ++ outer)
  | _, _, _ => none

structure Frame.StateRel (source : RunState) (target : EVMState)
    (tokens : List Word) : Prop where
  stackRel :
    materializeStack source.evm.stack source.returns tokens =
      some target.stack
  dataRel :
    eraseControl target =
      eraseControl { source.evm with stack := target.stack }
```

There is also a more precise but currently underused static frame relation:

```lean
structure StaticReturnFrame where
  procName : Name
  token : Word
  returnLabel : Assembly.Label
  retc : Nat

inductive ReturnContextRel (program : Program) :
    List StaticReturnFrame → List ReturnDest → List Word → Prop
```

## Current checked switch helpers

Already green:

- `test_runConditionState`
- `test_true_result_ctx`
- `test_false_result_ctx`
- `tests_fallthrough_result_ctx`
- `switch_none_result_ctx`
- `default_some_tail_result_ctx`
- `switch_default_some_result_ctx`
- `labeled_body_tail_result_ctx`
- selector facts:
  `no_match_of_select_none`, `default_none_of_select_none`,
  `default_some_of_select_nil`,
  `select_tail_of_head_ne`,
  `select_head_body_of_head_eq`

I introduced:

```lean
def CasesPreserves (program : Program) (ctx : CompileContext)
    (endLabel : Assembly.Label) (base : LabelSupply) :
    LabelSupply → Nat → List (Word × Block) → Prop
  | _supply, _idx, [] => True
  | supply, idx, (_value, body) :: rest =>
      let compiledBody := Block.compileFromCtx body ctx supply
      BlockPreserves program ctx supply body ∧
        CasesPreserves program ctx endLabel base compiledBody.next (idx + 1)
          rest

def DefaultPreserves (program : Program) (ctx : CompileContext)
    (supply : LabelSupply) : Option Block → Prop
  | none => True
  | some body => BlockPreserves program ctx supply body
```

The local theorem `labeled_body_tail_result_ctx` says: if the target PC is at a
case label, then execute label, pop scrutinee, run body, and if body returns
regularly jump over the remaining case/default code to the end label; abrupt
body outcomes are forwarded through `CompiledOutcomeRel`.

## Current WIP and failure

I tried to prove a theorem:

`SwitchPreservation.head_case_from_tests_result_ctx`

Intended meaning:

- starting before the current switch test
- current case value matches the scrutinee
- run test (`dup1; push probe; eq; jumpi caseLabel`)
- jump to the matching case label in the compiled cases section
- use `labeled_body_tail_result_ctx`

The theorem statement is very large because it spells out:

```lean
Stmt.switchTest base idx probe ++
Stmt.switchTests base (idx + 1) rest ++
[jump defaultLabel] ++
casePrefix ++
[label caseLabel, pop] ++
compiledBody.code ++
[jump endLabel] ++
compiledTail.code ++
compiledDefault.code ++
[label endLabel]
```

Current Lean failure after adding this theorem:

```text
error: EvmCompiler/Structured/Preservation.lean:8638:8:
Application type mismatch: In the application
  AssemblyProgram.PCFitsFrom.left hAfterPop
the argument hAfterPop has type
  AssemblyProgram.PCFitsFrom
    (preCase ++ [label caseLabel, prim pop])
    (compiledBody.code ++ [jump endLabel] ++ compiledTail.code ++
      compiledDefault.code ++ [label endLabel])
but is expected to have type
  AssemblyProgram.PCFitsFrom
    (preCase ++ [label caseLabel, prim pop])
    (compiledBody.code ++
      ([jump endLabel] ++ compiledTail.code ++ compiledDefault.code ++
       [label endLabel]))
```

This specific error is just append-association cleanup, but the theorem smell is
the real question: the statement is too explicit and likely brittle. It may be a
symptom that I need a bundled `SwitchLayout` / `SwitchCasesLayout` record rather
than threading raw `pre`, `post`, `casePrefix`, `compiledTail`, and
`compiledDefault`.

## Current top-level status

The module was green before the WIP `head_case_from_tests_result_ctx`. Last green
commands:

```text
/Users/dan/.elan/bin/lake build EvmCompiler.Structured.Preservation
git diff --check
rg -n "^[^/-]*\\b(sorry|admit|axiom|unsafe|partial|sorryAx)\\b" \
  EvmCompiler/Structured EvmCompiler.lean
```

There is still a public boundary:

```lean
structure ReturnRealization
    (program : Program) (sourceFuel : Nat) (initial : EVMState)
    (sourceOutcome : Outcome) where
  targetFuel : Nat
  targetOutcome : Assembly.StepResult
  targetRun :
    Assembly.Source.runNResult program.compile targetFuel initial =
      .ok targetOutcome
  outcomeRel : WholeProgramOutcomeRel sourceOutcome targetOutcome

theorem compile_preserves_with_return_realization
    (_hWF : program.WF)
    (_hFrame : program.FrameSafe)
    (_hRunner : Program.RunnerSafe program)
    (_hTokens : program.CallTokensUnique)
    (_hSource : program.run sourceFuel initial = .ok sourceOutcome)
    (hRealization :
      ReturnRealization program sourceFuel initial sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult program.compile targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome := ...
```

This is temporary. The goal is to remove it by proving call/return dispatch.

## Questions for critique

1. Is the current layer design sound?
   - ghost return stack in source;
   - concrete hidden return tokens in target;
   - `Frame.StateRel` as materialization relation;
   - static dispatch over call-site tokens.

2. Is `CompiledOutcomeRel` with context labels the right adjacent theorem
   boundary, or should I change the theorem to a continuation/layout record?

3. For switch preservation, should I continue with:
   - explicit compositional helpers (`tests_fallthrough`, default tail,
     labeled body tail, recursive `CasesPreserves`), or
   - introduce a `SwitchLayout`/`CompiledSwitch` record that owns the generated
     labels, code pieces, `PCFits`, `ExactLabels`, and body-preservation facts?

   Please be concrete: what should the record fields/theorem shape be?

4. For procedure call/return, should I prove it in the same `StmtPreserves`
   relation, or introduce a separate `TargetRel`/static-frame-indexed
   preservation theorem first and then project down to `Frame.StateRel`?

5. Is the `ReturnRealization` boundary acceptable as a temporary scaffold, and
   what is the cleanest theorem that should replace it?

6. Would a monadic semantics/proof interface materially improve this layer, or
   should I keep the current relational big-step plus `ARunResult` composition?

7. What is the biggest proof-debt risk you see in the current approach, and what
   single refactor should I do now before the proof grows further?

Please assume no `sorry`, no new axioms, and that theorem statements should stay
compositional and source-language complete.
