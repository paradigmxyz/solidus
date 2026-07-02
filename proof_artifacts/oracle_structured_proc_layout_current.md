# Oracle request: critique current procedure-aware Structured layer and layout proof

Mode requested: hostile architecture critique plus concrete repair advice. I do
not primarily need Lean syntax help unless it exposes a theorem-boundary problem.

Repository: `/Users/dan/Projects/evm-compiler`

Main module: `EvmCompiler/Structured/Preservation.lean`

Lean/project: Lean `v4.22.0`, project depends on Nethermind `EVMYulLean`.

## Goal in this thread

Refactor the `Structured` control layer into a procedure-aware control layer
with:

- structured control (`if`, `switch`, `for`, `break`, `continue`);
- procedure control (`proc` bodies, `call`, procedure-delimited `leave`);
- terminal EVM outcomes (`STOP`, `RETURN`, `REVERT`, `SELFDESTRUCT`);
- no public arbitrary `leaveScope`;
- source semantics equal to EVM state semantics except gas/PC/jumps are
  abstracted by structured control;
- source calls represented by ghost return-destination state;
- target assembly realizes calls using hidden concrete stack tokens and static
  return-dispatch code;
- a checked Structured-to-labeled-assembly preservation theorem.

Higher layers and the previous top theorem may be disabled while this core layer
is rebuilt. The important standard is a compositional, source-language-complete
adjacent theorem, not a replay certificate or hand-written realization witness.

## Current source design

Syntax:

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

Semantics:

- `call` looks up a proc, splits `argc` arguments from the visible EVM stack,
  pushes a ghost return frame `{ callerStack, retc }`, evaluates the proc body,
  then on regular or `leave` pops that ghost frame and attaches exactly `retc`
  return values to the caller stack.
- `leave` is valid only when `returns ≠ []`, produces `Outcome.leave`, and is
  caught at procedure-call boundaries exactly like a procedure return.
- `brk`/`cont` escaping a procedure call are invalid.
- `halt` propagates without dispatch/return.

## Current compiler shape

Call sites compile to:

```lean
[push token] ++ StackShuffle.sinkTopUnder proc.argc ++
  [jump (ProcLabel.entry name), label returnLabel]
```

Procedure segment shape:

```lean
[label (ProcLabel.entry proc.name)] ++ compiledBody.code ++
  [label (ProcLabel.exit proc.name)] ++
  Dispatch.forProc proc sites dispatchSupply
```

`Dispatch.forProc` filters call sites by `CallSite.forProc proc.name`, and
generates a static token dispatch using `proc.retc` for the hidden-token depth.
This avoids one prior concern about heterogeneous `retc` in a shared dispatch.

## Current target/source state relation

Source ghost return frames are materialized into hidden target stack words:

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

There is an older, more precise static return-frame relation that is currently
underused. I have not yet refactored the public proof through it:

```lean
structure StaticReturnFrame where
  procName : Name
  token : Word
  returnLabel : Assembly.Label
  retc : Nat

inductive ReturnContextRel (program : Program) :
    List StaticReturnFrame → List ReturnDest → List Word → Prop
```

## Current layout abstraction

I added a small `CodeSegment` record to avoid tying call proofs to a single
append order:

```lean
structure CodeSegment (asm : Assembly.Program) (code : Assembly.Program) where
  pre : Assembly.Program
  post : Assembly.Program
  hAsm : asm = pre ++ code ++ post
  hFits : AssemblyProgram.PCFitsFrom pre code

namespace CodeSegment

def startPc {asm code : Assembly.Program} (segment : CodeSegment asm code) :
    Word :=
  Assembly.Program.pcAfter segment.pre

def fallthroughPc {asm code : Assembly.Program}
    (segment : CodeSegment asm code) : Word :=
  Assembly.Program.pcAfter (segment.pre ++ code)

def left {asm first second : Assembly.Program}
    (segment : CodeSegment asm (first ++ second)) :
    CodeSegment asm first

def right {asm first second : Assembly.Program}
    (segment : CodeSegment asm (first ++ second)) :
    CodeSegment asm second
```

I am currently trying to lift already-checked call proofs from "call site before
the procedure segment in one append expression" to arbitrary same-program
segments:

```lean
theorem ProcedurePreservation.call_regular_segments
    {program : Program} {ctx : CompileContext}
    {proc : Proc} {bodySupply dispatchSupply : LabelSupply}
    {sites : List CallSite} {site : CallSite} {fuel : Nat}
    {state bodyState returned : RunState}
    {args callerStack stack : EvmYul.Stack Word} {frame : ReturnDest}
    {target : EVMState} {tokens : List Word} {token : Word}
    {asm : Assembly.Program}
    (callSeg :
      CodeSegment asm (callSiteCode proc args token site.returnLabel))
    (procSeg :
      CodeSegment asm
        (procSegment program proc bodySupply dispatchSupply sites))
    ...
    (hPc : target.pc = callSeg.startPc)
    (hRel : Frame.StateRel state target tokens)
    (hExact : ExactLabels asm) :
    ARunResult asm target
      (fun result =>
        CompiledOutcomeRel asm ctx callSeg.fallthroughPc
          (Outcome.regular
            (returned.withEVM { bodyState.evm with stack := stack }))
          result tokens)
```

The currently checked specialized siblings are:

- `ProcedurePreservation.call_regular_in_layout`
- `ProcedurePreservation.call_leave_in_layout`
- `ProcedurePreservation.call_halt_in_layout`

They assume the program shape:

```lean
pre ++ callSiteCode ... ++ between ++ procSegment ... ++ post
```

Those theorem statements are too restrictive for recursive calls or calls inside
later procedure segments, because a call site may not textually precede the
callee procedure segment. `call_regular_segments` is the first attempt to fix
that by requiring two `CodeSegment`s in the same `asm`.

## Current Lean failure

The build currently fails only inside the new `call_regular_segments`; the
module was green before adding it.

Command:

```text
/Users/dan/.elan/bin/lake build EvmCompiler.Structured.Preservation
```

Failure shape:

```text
tactic 'rewrite' failed, did not find instance of the pattern
  callSeg.pre ++ callSiteCode proc args token site.returnLabel ++ callSeg.post
⊢ (callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post).labelPc ... = ...
```

This is probably a local normalization issue: `callSiteCode` is definitionally
`callJumpCode ++ [label returnLabel]`, but I need a stable rewrite lemma like:

```lean
have hCallAsm :
  asm = callSeg.pre ++ jumpCode ++ returnCode ++ callSeg.post := by ...
```

The bigger question is whether `CodeSegment` is the right abstraction or whether
I should introduce a richer whole-program layout object before proving more
segment theorems.

## Current public boundary still needing replacement

The older source-compositional theorem has a call hole:

```lean
def StmtPreserves (program : Program) (ctx : CompileContext)
    (supply : LabelSupply) (stmt : Stmt) : Prop := ...

def CompilerPreservation.CallObligation ... := ...

theorem CompilerPreservation.main_block :
  ... → CallObligation program ctx → ...
```

This is now understood to be the wrong final boundary for calls: `.call` cannot
be proved in an arbitrary local `pre ++ compiledCall ++ post` because the jump
target, proc body, exit label, and return dispatch live in the whole program.
The intended replacement is a whole-program/layout preservation theorem that
still uses local compositional statement/block lemmas where they are valid.

There is also a temporary scaffold:

```lean
structure ReturnRealization ... where
  targetRun : Assembly.Source.runNResult program.compile targetFuel initial =
    .ok targetOutcome
  outcomeRel : WholeProgramOutcomeRel sourceOutcome targetOutcome

theorem compile_preserves_with_return_realization ... (hRealization : ReturnRealization ...) : ...
```

This must not be the final theorem.

## Already-green call proof pieces

The following low-level pieces are checked:

- call prologue: push token, sink under arguments, static jump to proc entry;
- dispatch condition: duplicate buried token, compare against site token, `jumpi`;
- dispatch table recursion: skip mismatching tokens, run selected case;
- selected case: remove buried return token, attach return values, jump back to
  call-site return label;
- procedure body from entry through exit label and dispatch for regular and
  `leave`;
- procedure body from entry for halt, with existential target-token
  materialization for halted outcomes.

I changed halted `CompiledOutcomeRel` from fixed input tokens to existential
halted tokens, because abortive halt may happen with a deeper materialized
return stack:

```lean
| .halt sourceKind, .halted targetHalt =>
    sourceKind = targetHalt.kind ∧
      ∃ haltedTokens,
        Frame.StateRel source.state targetHalt.state haltedTokens
```

## Questions

1. Is the current semantic design sound: ghost return stack in source, concrete
   hidden stack tokens in target, static token dispatch per procedure?

2. Is `CodeSegment asm code` enough for whole-program call preservation, or
   should I stop and introduce a richer `ProgramLayout`/`CompiledProgram`
   record now? If richer, what should the fields be?

3. Should the adjacent public theorem be stated as:

   - a source big-step `Program.Eval` to target `Assembly.Source.runNResult`
     whole-program theorem;
   - a block/stmt theorem indexed by a whole-program layout and PC segment;
   - or a static-frame-indexed relation theorem, later projected to the simpler
     `Frame.StateRel` observation?

4. How should recursive calls and calls inside procedure bodies be handled
   compositionally without making every `BlockPreserves` theorem know the full
   procedure layout?

5. Is it acceptable to keep `Frame.StateRel` for the main theorem and use
   static frame information only as proof-local obligations, or is that likely
   to create false theorems / proof blowup?

6. What is the single best refactor to do next before continuing to prove
   `call_leave_segments`, `call_halt_segments`, and then replacing
   `CallObligation`?

Constraints: no `sorry`, no new axioms, no source-language fragmenting, and
theorem statements should stay compositional. Useful failure would be a route
rejection or a smaller theorem boundary that avoids proof blowup.
