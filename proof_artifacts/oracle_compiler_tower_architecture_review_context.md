# Oracle request: architecture review for a Lean verified compiler tower to EVM

## What I need from you

Please give a broad, critical architecture review and proof strategy.  Do not
focus only on the current local proof subgoal.  I want to know whether the whole
compiler tower is shaped correctly, what abstraction boundaries should be
tightened before continuing, and how to finish the bridge from the imported
Nethermind/Solidity-style Yul semantics to the compiler tower without proof
blowup.

Useful answer shape:

1. Identify the intended compiler tower and whether the layer ordering is good.
2. Point out abstraction leaks or theorem interfaces that will keep causing
   non-compositional Lean proofs.
3. Propose the right public theorem shape for each layer and for the whole
   imported-Yul-to-EVM theorem.
4. Explain where assumptions should live: gas, PC, outside-world effects,
   code-image/codecopy, call/create, out-of-gas, verbatim, and acceptedness.
5. Give a concrete strategy for the imported Yul bridge, including how to avoid
   exposing stack/layout/return-token details above the layers that introduced
   them.
6. If a current partial theorem is the wrong abstraction, say so directly and
   suggest the replacement.

Constraints:

- Lean proofs must be checked.  No `sorry`, `admit`, or new axioms.
- Every source layer should have its own independent interpreter.  A layer is
  not allowed to define its semantics merely by lowering to the next layer.
- The semantics of a layer should fully abstract the feature it introduced.
  For example, above locals the source semantics should be named environments
  and lexical scopes, not stack slots; above structured/procedure control the
  source semantics should be Yul-like control outcomes/handlers, not raw labels
  or PCs.
- Pure/shared primitives may intentionally pass through the tower, but this
  should be explicit and compositional.
- The final theorem is allowed to have fundamental premises for gas,
  out-of-gas, PC/gas opcodes, jumpdest scanner correctness, external
  call/create/world agreement, and target code image assumptions.  But
  proof-convenience witnesses should be discharged into checked compiler or
  bridge theorems.
- Avoid monolithic unfolding proofs and ad hoc special cases.  We need a model
  for later compiler layers.

## Repository and key files

Repository: `/Users/dan/Projects/evm-compiler`

Important files:

- `EvmCompiler/Assembly/*`: labeled assembly, assembler, gas-aware bridge.
- `EvmCompiler/Structured/*`: structured control/procedure layer, typed
  continuation facade, preservation to assembly.
- `EvmCompiler/Expressions/*`: expression/literal layer.
- `EvmCompiler/Locals/*`: locals/scopes; includes both older direct semantics
  and newer stack-free source semantics.
- `EvmCompiler/Functions/*`: functions/calls/leave; includes both direct
  backend semantics and newer stack-free source semantics.
- `EvmCompiler/Objects/*`: object wrapper; newer source semantics over
  function source semantics.
- `EvmCompiler/Yul/*`: compiler-facing Yul adapter and bridge to imported
  `EvmYul.Yul` semantics.
- `EvmCompiler/LayerAudit.lean`: checked aliases to public theorem boundaries.

The project currently builds with `lake build EvmCompiler`.  A recent hole scan
over the newly touched bridge/audit files found no `sorry`/`admit`/`axiom` in
those files.

## Current high-level compiler tower

Intended public spine:

```text
Imported Nethermind/Solidity-style Yul semantics
  -> compiler-facing Yul source bridge
  -> objects/data
  -> functions
  -> locals/scopes
  -> expressions/literals
  -> structured control/procedure control
  -> labeled assembly
  -> resolved assembly / EVM bytecode
  -> gas-aware EVMYulLean runner
```

The design principle is that each layer removes one source feature:

- Assembly abstracts exact byte PCs into symbolic labels and mostly erases gas
  from the source side.
- Structured abstracts raw jumps/labels into structured control/procedure
  outcomes, but still legitimately has an EVM-like stack because no locals
  abstraction exists yet.
- Expressions abstract small expression trees/literals over shared primitive
  semantics.
- Locals abstract stack slots into named variables and lexical scopes.
- Functions abstract procedure return tokens/call frames into user functions,
  parameters, return variables, and `leave`.
- Objects abstract code/data object structure.
- The final Yul bridge should connect imported Yul AST/interpreter semantics to
  this source tower.

## Layer audit / theorem spine

`EvmCompiler/LayerAudit.lean` is an audit tripwire with checked aliases.  The
most relevant public names are:

```lean
namespace EvmCompiler.LayerAudit.Interpreters
abbrev assemblySourceRun := @Assembly.Source.runNResult
abbrev assemblyTargetRun := @Assembly.Target.runNResult
abbrev structuredRun := @Structured.Program.run
abbrev expressionsRun := @Expressions.Program.run
abbrev localsRun := @Locals.Program.run
abbrev localsSourceRunState := @Locals.Source.Program.runState
abbrev localsDirectRun := @Locals.Direct.Program.run
abbrev functionsRun := @Functions.Program.run
abbrev functionsSourceRunState := @Functions.Source.Program.runState
abbrev functionsDirectRun := @Functions.Direct.Program.run
abbrev objectsRun := @Objects.Program.run
abbrev objectsSourceRunState := @Objects.Source.Program.runState
abbrev importedYulRun := @Yul.Program.run
noncomputable abbrev yulLoweredRun := @Yul.Lowered.run
noncomputable abbrev yulSourceLoweredRunState := @Yul.SourceLowered.runState
end

namespace EvmCompiler.LayerAudit.Adjacent
abbrev assemblyToBytecode := @Assembly.compile_whole_program_result_sound
abbrev structuredToAssembly := @Structured.Preservation.compile_preserves
abbrev expressionsToStructured := @Expressions.Program.compile_preserves
abbrev localsToExpressions := @Locals.Program.compile_preserves
abbrev functionsToLocals := @Functions.Program.compile_preserves
abbrev functionsSourceToAssembly := @Functions.Source.Program.compile_preserves
abbrev objectsToFunctions := @Objects.Program.compile_preserves
abbrev objectsSourceToAssembly := @Objects.Source.Program.compile_preserves
abbrev yulLoweredToObjects := @Yul.Program.compile_preserves_checked
abbrev yulSourceLoweredToAssembly :=
  @Yul.Program.compile_source_preserves_checked
end
```

Important interpretation:

- `Yul.Lowered.run` is quarantined as an old lowering-defined semantics.  It is
  not supposed to be treated as the independent imported source proof.
- `Yul.SourceLowered.runState` is the intended compiler-facing target for the
  imported-Yul bridge.  It runs through the repaired source tower:
  `Objects.Source -> Functions.Source -> Locals.Source -> ...`.
- `Functions.Source.Program.compile_preserves` and
  `Objects.Source.Program.compile_preserves` are meant to hide direct
  procedure/stack backend details from higher layers.

## Assembly and final EVM boundary

Assembly is a labeled, gasless-ish EVM-like language.  It compiles to concrete
EVM bytecode / EVMYulLean execution.  The assembly layer is expected to support
all relevant EVM primitive semantics except that:

- gas is not modeled in the source language;
- exact PC is not a source concept;
- symbolic labels replace byte offsets;
- dynamic jumpdest/bytecode scanner obligations are isolated at the final
  assembler/gas-aware bridge.

Fundamental final-boundary assumptions are intended to be explicit:

- sufficient gas / no out-of-gas for the target run, or a theorem of the form
  "there exists a gas bound such that any greater gas preserves the source run";
- gas-related opcodes such as `GAS` agree with a source oracle;
- source PC oracle, if any, agrees with target byte offsets;
- external call/create/world effects agree between the source oracle and the
  EVM runner;
- code-image assumptions for code-inspection operations;
- EVMYulLean jumpdest scanner correctness.

## Structured/procedure layer

This layer has structured control plus procedure control.  It is the layer where
raw jumps should disappear from the public source interface.  It still has
stack-shaped values because locals have not been introduced yet.

Current intended architecture follows a typed continuation/CFG discipline:

- continuations/labels have declared stack shapes;
- every control transfer conforms to the target shape;
- break/continue/leave/regular outcomes map to continuations;
- each procedure has one epilogue;
- `leave` is a static jump to the procedure epilogue, not a dynamic return;
- dynamic procedure return uses generated symbolic return continuations/tokens;
- concrete token/offset encoding is separated into lower assembly/assembler
  evidence.

There is an acceptance checker for generated label/token uniqueness.  The
public theorem is `Structured.Preservation.compile_preserves`.  The intent is
that public callers do not need a replay certificate, arbitrary
`ReturnRealization`, or local call-layout witnesses.

Concern to review: is a typed-continuation facade around a structured compiler
enough, or should we introduce a proper continuation/block-parameter CFG IR
between structured source and assembly before continuing?  The current proof
has accumulated many layout/frame lemmas, although we have tried to keep them
behind the structured boundary.

## Expressions layer

This layer adds expression/literal syntax over shared primitive semantics and
compiles to structured statements.  It should be fairly thin.  Primitive
semantics are intended to be shared/pass-through where possible, so arithmetic,
comparison, memory/storage/logs, and terminal primitive behavior do not get
re-proved semantically at every layer except through small wrapper lemmas.

Concern to review: the expression lowering order matters for Yul.  Imported Yul
evaluates call arguments in the order implemented by Solidity/Nethermind.  The
compiler-facing expression list lowering has to preserve that order and stack
result order.  We found and fixed a primitive argument stack-order issue for
terminal calls.

## Locals/scopes layer

This layer introduces named variables and lexical scopes.  The user explicitly
wants the source semantics above this point to stop talking about target stack
layout.  We added `Locals.SourceSemantics` for a stack-free named-store
interpreter.

Important properties:

- source state has a named store/environment plus shared EVM state;
- scoped blocks drop variables declared inside the block on regular exit;
- nonregular outcomes such as break/continue/leave/terminal halt should not do
  the wrong cleanup; cleanup should match Yul block semantics;
- source-level facts such as
  `Block.runScoped_regular_eq_restrict` and
  `Block.runScoped_regular_drops_not_mem` expose block cleanup without
  revealing target stack layout.

The older direct locals interpreter and stack lowering still exist below the
source boundary.  `Locals.SourceLowering` owns the source-to-direct/lower proof
obligations.

Concern to review: `Locals.Source.Program.SourceOwned` currently rejects some
lower-only constructs such as raw procedure calls/assignment-top/code snippets.
That seems right if those constructs are not source language constructs, but
we want to know how to keep "accepted source language" complete rather than
proof-convenient.

## Functions layer

This layer introduces user functions, calls, parameters, return variables,
multi-return behavior, and Yul `leave`.

We have both:

- a direct/backend interpreter that still sees procedure frames/return tokens;
- a newer `Functions.SourceSemantics` interpreter with stack-free function
  source meaning over named stores, fresh function-local environments, return
  variables, and Yul-like `leave`.

Important intended semantics:

- `leave` exits the current Yul function, not the whole EVM execution context.
- EVM terminal builtins such as `return`, `revert`, `stop`, and
  `selfdestruct` are terminal halts distinct from `leave`.
- function parameters are bound in a fresh function-local state;
- return variables are initialized, then returned on regular fallthrough or
  `leave`;
- duplicate assignment targets are rejected for source calls;
- stack frames, hidden return tokens, and caller-stack reconstruction belong in
  the lowering/preservation proof, not the source semantics.

There is significant proof machinery in `Functions.SourceDirect`:

- source/direct state relations;
- scope and cleanup relations;
- outcome relations for regular/break/continue/leave/halt;
- primitive soundness contracts;
- source-shaped frame bounds for EVM stack-width obligations;
- recursive callback interfaces for loops and function calls.

Concern to review: the function source-to-direct proof has been hard.  Are
recursive callbacks/fuel-indexed source-run induction the right public proof
architecture, or should we add another IR or shift more procedure-control
semantics down/up?

## Objects layer

Objects are currently mostly a transparent root-object wrapper over
`Functions.Source`.

Current state:

- object/data syntax and recursive object WF exist;
- source semantics is `Objects.SourceSemantics` over the function source
  interpreter;
- data sections and nested objects are structurally checked but not yet fully
  addressable from code;
- object pseudo-builtins such as `datasize`, `dataoffset`, and `datacopy` are
  currently rejected by the Yul accepted-fragment predicate or named as future
  work.

Concern to review: should object/data layout be introduced before trying to
make the Yul bridge source-complete, because imported Yul has object-level
pseudo-builtins and code/data lookup behavior?

## Imported Yul reference semantics and target branch

The imported source boundary is Nethermind's `EvmYul.Yul` semantics:

- `EvmYul.Yul.exec`
- `EvmYul.Yul.eval`
- `EvmYul.Yul.call`
- `EvmYul.Yul.primCall`
- state type `EvmYul.Yul.State`

We found that upstream semantics differed from Solidity behavior for switch
selected-branch execution and omitted default.  We prepared a branch/fork of
`EvmYulLean` with:

- selected-branch switch semantics;
- omitted default translated as empty block rather than `break`;
- selected terminal/halt behavior updates for `STOP`, `RETURN`, `REVERT`,
  `SELFDESTRUCT`.

This project pins the fork branch in Lake for the current bridge work.

## Current imported-Yul acceptedness

`EvmCompiler/Yul/Reference.lean` defines a conservative acceptedness layer:

```lean
namespace EvmCompiler.Yul.Reference.Safe
def primitive : EvmYul.Operation .Yul -> Prop
  | .Env .CODESIZE => False
  | .Env .CODECOPY => False
  | .Env .EXTCODESIZE => False
  | .Env .EXTCODECOPY => False
  | .Env .EXTCODEHASH => False
  | .System .CREATE => False
  | .System .CALL => False
  | .System .CALLCODE => False
  | .System .DELEGATECALL => False
  | .System .CREATE2 => False
  | .System .STATICCALL => False
  | _ => True
```

It also has recursive safety predicates for expressions/statements/functions
and a no-shadowing predicate:

```lean
noncomputable def Accepted (program : Program) : Prop :=
  Program.Accepted program /\ Safe.program program /\
    Safe.NoShadowing.program program
```

Concern to review: which exclusions are fundamental for the top theorem, which
should be moved into explicit semantic assumptions, and which are
proof-convenience fragments that should be eliminated?  We eventually want
"complete Yul semantics except explicit assumptions", not a fragment chosen
because the proof is easier.

## Current source-owned bridge in `Yul/Reference.lean`

The newer bridge target is source-owned and stack-free at the public boundary.
Key definitions:

```lean
namespace Reference.SourceBridgeFacts

def SourceStoreRel (layout : List Name)
    (sourceStore : EvmYul.Yul.VarStore)
    (compilerStore : Locals.Source.Store) : Prop := ...

def SourceStateRel (cfg : StateRelConfig) (layout : List Name)
    (source : State) (compiler : Objects.Source.State) : Prop := ...

def SourceBlockRunBridge
    (prim : Objects.Source.PrimitiveSemantics)
    (program : Functions.Program) (ctx : Functions.Source.Ctx)
    (sourceFuel : Nat) (sourceStmts : List AstStmt)
    (codeOverride : Option AstContract) (source : State)
    (compiler : Objects.Source.State) (lowerBlock : Functions.Block) : Prop :=
  exists sourceResult : Except Exception State,
  exists sourceOutcome : Objects.Source.Outcome,
  exists targetFuel : Nat,
    EvmYul.Yul.exec sourceFuel (.Block sourceStmts) codeOverride source =
      sourceResult /\
    Functions.Source.Block.runScoped prim program ctx lowerBlock targetFuel
        compiler =
      .ok sourceOutcome
```

There are constructors such as:

- `sourceBlockRunBridge_of_runs`
- `sourceBlockRunBridge_of_regular`
- `sourceBlockRunBridge_stop_of_exec`
- `sourceBlockRunBridge_terminalArgs_of_exec`
- `sourceBlockRunBridge_stop_call`

Root/dispatcher composition:

- `Yul.Program.sourceLowered_runState_of_root_source_block_bridge`
- `Yul.Program.sourceBridge_of_dispatcher_source_block_bridge`
- `compile_preserves_of_dispatcher_source_block_bridge`
- `compile_whole_program_result_sound_of_dispatcher_source_block_bridge`

This is intended to be the route from imported Yul semantics into
`Yul.SourceLowered.runState`, then into
`Yul.Program.compile_source_preserves_checked`.

Concern to review: `SourceBlockRunBridge` is currently result-shaped but weak:
it says both source and target run to some results/outcomes, but the exact
relation is sometimes in side conditions or bridge configs.  Should this be
replaced by a stronger result relation at this boundary?  If yes, what exact
shape should it have so block/scoped cleanup, terminal errors, exceptions, and
halts compose cleanly?

## Current direct/result-shaped bridge machinery

There is older/direct bridge machinery in `Yul/Reference.lean` that still talks
about `Functions.Direct.Block.runOpen`, stack layouts, and slot values.  It has
many useful checked components:

- strict varstore/local layout relations;
- first bridges for literal and variable expressions;
- `let` and assignment bridges for literal/variable initializers;
- empty block and scoped-block cleanup facts;
- result-shaped sequence/block interfaces for regular, break, continue, leave,
  terminal, revert/error;
- terminal bridges for `stop`, `return`, `revert`, `selfdestruct`;
- primitive argument order fixes and literal-pair terminal-call tests.

But these direct bridges are too low-level for the public imported-Yul proof.
They mention stack slots, layout depths, direct function frames, and concrete
cleanup.  We want to mine them as backend evidence while moving the public
bridge into the source tower.

Concern to review: should we first complete the source/direct function theorem
and then prove imported Yul only against `Functions.Source`, or is it better to
continue using direct low-level bridges temporarily and later wrap them?

## Example of the current local bottleneck, for diagnosis only

This is not the only thing I want advice on, but it illustrates the abstraction
problem.

For terminal Yul calls like `return(a, b)` or `revert(a, b)`, the actual
compiler lowering does not emit only:

```lean
[Functions.Stmt.terminalArgs kind seq]
```

Instead `Expr.List.lowerBound1?` evaluates/binds arguments into generated
temporary locals and then emits the terminal statement:

```lean
Expr.List.lowerBound1? state args = some (preArgs, lowerArgs, stateAfterArgs)
Expr.List.toStackSeq? lowerArgs kind.argCount = some seq
lowerPrefix = preArgs ++ [Functions.Stmt.terminalArgs kind seq]
```

The recursive definition is essentially:

```lean
Expr.List.lowerBound1? state [] = some ([], [], state)

Expr.List.lowerBound1? state (expr :: rest) = do
  let (preRest, lowerRest, state') <- Expr.List.lowerBound1? state rest
  let (preHead, lowerHead, state'') <- Expr.lower? 1 state' expr
  let (tmp, state''') <- Fresh.fresh? state''
  some (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead],
        .var tmp :: lowerRest,
        state''')
```

The source `Functions.Source` terminal statement runs like:

```lean
| _fuel, .terminalArgs kind args, state => do
    let (stateAfterArgs, values) <-
      Locals.Source.Expr.ExprSeq.eval prim args state
    let shared <- prim.terminal kind stateAfterArgs.shared values
    .ok (Outcome.halt kind (stateAfterArgs.withShared shared), ctx)
```

So the bridge needs a source-owned theorem saying the generated prelude
`preArgs` plus final `terminalArgs kind seq` has exactly the same source
meaning as imported Yul argument evaluation plus terminal primitive execution,
without exposing stack layouts.  The immediate temptation is to prove many
special cases such as `return(lit,lit)`, but that is the smell we want to avoid.

The broader question: what is the right reusable expression-list/lowering
theorem and where should it live?

## Known semantic details we care about

- Yul `switch` evaluates the selector once and executes only the selected case
  or default; there is no fallthrough.
- A switch without default should behave as if default is an empty block.
- Yul block scoping drops locals declared in the block at block end.
- `break` and `continue` are structured loop modes.
- `leave` exits the current function and goes through function epilogue/return
  variables; it is not EVM `return`.
- EVM terminal builtins (`stop`, `return`, `revert`, `selfdestruct`, invalid)
  halt the execution context and must be kept distinct from `leave`.
- Function-call argument evaluation order must match Solidity/Nethermind Yul
  exactly.
- For source layers above locals/functions, stack cleanup and return-token
  mechanics should appear only in compiler preservation proofs.

## What has gone wrong in proof style before

Several proof attempts became non-compositional:

- too many theorem names that bundle particular stack layouts or exact hidden
  argument shapes;
- witnesses for "one successful structured run" instead of source-parametric
  preservation;
- direct use of backend stack concepts in high-level Yul bridge statements;
- special-case terminal-call proofs before proving generic expression-list
  lowering;
- very broad searches and build logs consuming context without improving the
  proof.

We are trying to correct this by:

- keeping `LayerAudit.lean` as a small checked theorem-spine audit;
- adding independent source interpreters for each layer;
- quarantining older lowering-defined semantics;
- moving public bridge targets to source-owned interpreters;
- leaving lower machine facts inside adjacent compiler theorems.

## Questions for Pro

1. Is the current tower order sound, or should we introduce another IR such as
   normalized YulCore or continuation/block-parameter CFG before finishing the
   imported Yul bridge?
2. Are the abstraction boundaries right?  In particular:
   - structured/procedure may expose stack shapes internally, but should higher
     layers ever mention them?
   - locals source semantics should be a varstore/env; is any stack concept
     acceptable above it?
   - functions source semantics should hide return tokens; what public relation
     should replace any remaining direct-frame theorem?
3. What should the imported Yul bridge theorem be?  Should it be a mutual
   induction over `exec/eval/call/primCall`, a set of per-construct bridge
   combinators, or a normalized-source translation theorem?
4. What should the result relation between imported Yul and compiler source be
   for regular states, checkpoints, Yul exceptions, terminal halts, revert, and
   EVM-level shared-state effects?
5. How should target fuel be handled?  Current style often uses existential
   target fuel.  Is that enough, and where should monotonicity/fuel lemmas be
   bundled?
6. How should acceptedness be structured so it is source-complete rather than a
   proof-convenience fragment?  Which restrictions should be compile failure,
   which should be explicit assumptions, and which are genuine unsupported
   source features?
7. How should full EVM primitive coverage flow upward?  We want primitive
   semantics to match EVM/Yul exactly except gas/PC/jumps and explicit external
   assumptions.  What is the clean primitive-soundness interface?
8. For code-inspection and object data pseudo-builtins (`codesize`, `codecopy`,
   `extcode*`, `datasize`, `dataoffset`, `datacopy`), should we implement
   object/code-image layout now, or isolate them behind assumptions until the
   rest of Yul is bridged?
9. For call/create/staticcall/delegatecall, should the source layers use an
   outside-world oracle identical to the EVM external semantics, or should these
   stay rejected until a global-state relation is proved?
10. What are the minimum changes you would make before continuing the proof,
    and what would you explicitly avoid doing?

Please be blunt if you think we are proving the wrong theorem or if a layer
should be restructured before more Lean grinding.
