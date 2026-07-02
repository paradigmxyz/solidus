# Oracle Request: Procedure-aware Structured-to-Assembly Frame Safety

## Mode

Proof architecture / theorem-shape critique. Please be hostile to theorem
statements that merely assume the conclusion.

## Project Context

Lean project: `/Users/dan/Projects/evm-compiler`.

We have a verified compiler tower over Nethermind `EVMYulLean`. The current
active refactor is only the lower `Structured` layer and labeled assembly.
Root `EvmCompiler.lean` is temporarily slimmed to:

```lean
import EvmCompiler.Assembly
import EvmCompiler.Structured
```

The new `Structured` source layer has:

```lean
structure ReturnDest where
  token : Nat
  callerStack : EvmYul.Stack Word
  retc : Nat

structure RunState where
  evm : EVMState
  returns : List ReturnDest

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

structure Proc where
  name : Name
  argc : Nat
  retc : Nat
  body : Block

structure Program where
  procs : List Proc
  body : Block
```

`Proc.WF` currently includes `argc ≤ 16`, `retc < 16`, and
`Block.WF false false true proc.body`.

## Source Semantics

The source machine keeps return destinations as ghost control state.
Primitive code mutates only `RunState.evm`.

For `Stmt.call name`:

1. Lookup the proc.
2. Split exactly `proc.argc` top stack items from `state.evm.stack`.
3. Store the caller stack prefix plus expected `proc.retc` in `ReturnDest`.
4. Run the callee body with `evm.stack := args`.
5. On regular fallthrough or `leave`, pop the return frame.
6. Require the callee final visible stack length to equal `retc`.
7. Reattach `returnValues ++ callerStack`.

For `leave`: valid only if `state.returns` is nonempty. It returns
`Outcome.leave`; the procedure boundary catches it.

## Compiler

The target is existing labeled assembly:

```lean
inductive Assembly.Instr where
  | label (name : Label)
  | prim (op : PrimOp)
  | push (value : Word)
  | jump (target : Label)
  | jumpi (target : Label)
```

Procedure labels:

```lean
ProcLabel.entry name = named ("proc:" ++ name ++ ":entry")
ProcLabel.exit name = named ("proc:" ++ name ++ ":exit")
```

Call lowering for a call to `proc`:

```lean
[push token] ++
StackShuffle.sinkTopUnder proc.argc ++
[jump (ProcLabel.entry name), label returnLabel]
```

`sinkTopUnder argc` is `swap argc; swap (argc-1); ...; swap1`, which should
move the just-pushed token under the visible arg frame while preserving arg
order.

Procedure body lowering:

```lean
[label entry] ++ compiledBody ++ [label exit] ++ dispatch
```

`leave` lowers to `jump exit`.

Exit dispatch for `retc` return values and a list of static call sites:

```lean
tests:
  dup (retc+1); push token; eq; jumpi caseLabel

case:
  label caseLabel
  StackShuffle.removeBuriedUnder retc
  jump returnLabel
```

`removeBuriedUnder retc` is `swap1; swap2; ...; swap retc; pop`, which should
remove the hidden token under the visible return frame while preserving return
order.

## Current Preservation Boundary

Current placeholder-like theorem:

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
    (hWF : program.WF)
    (hSource : program.run sourceFuel initial = .ok sourceOutcome)
    (hRealization : ReturnRealization program sourceFuel initial sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult program.compile targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome
```

This is too close to assuming the conclusion. We need replace it with a real
checked preservation path.

## Question

What theorem structure should we use to discharge this without blowing up Lean?

I suspect we need:

1. A recursive stack-frame relation materializing `RunState.returns` as hidden
   concrete stack tokens:
   `visibleStack ++ [token] ++ callerStack ++ outerFrame...`.
2. Local checked stack-shuffle lemmas for:
   - `sinkTopUnder argc`
   - `dup (retc+1)` dispatch tests
   - `removeBuriedUnder retc`
3. A frame-safety assumption or judgment for `Code`, because arbitrary
   `dup/swap/pop` can otherwise touch the hidden token. But we need the right
   shape: semantic `Code.FrameSafe`, syntactic stack effect, or both?
4. A contextual preservation theorem parameterized by continuations/labels,
   rather than trying to reason only from whole-program `run`.

Please recommend the smallest robust proof architecture:

- exact state relation;
- exact public theorem statement;
- which assumptions are acceptable and which would be cheating;
- how to handle recursion/fuel;
- whether to first prove the theorem for a frame-safe subset of `Code`;
- how to keep the old structured `if`/`switch`/`for` preservation lemmas from
  exploding under the added frame relation.

Constraints:

- No `sorry`, `admit`, or new axioms.
- The source language should keep ghost return destinations.
- Raw jumps/labels stay only in labeled assembly.
- Higher layers are disabled for now; focus only on Structured to Assembly.
