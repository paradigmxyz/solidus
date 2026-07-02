# Oracle Request: Critique Semantics Placement In a Lean Verified Compiler Tower

## Mode

Critique / architecture review. Please be direct and adversarial. I am not asking for routine Lean syntax help; I want to know whether the proof obligations are at the right layer of the compiler tower and whether some semantics should be proved lower before we continue.

## Project Context

Repository: `/Users/dan/Projects/evm-compiler`

We are building a verified compiler tower in Lean targeting Nethermind's `EVMYulLean` EVM/Yul semantics. The current public spine is:

```text
Nethermind Yul reference semantics
  -> compiler-facing Yul
  -> objects/data
  -> functions
  -> locals/scopes
  -> expressions/literals
  -> structured control/procedures
  -> labeled assembly
  -> resolved EVM assembly
  -> encoded bytecode
  -> gas-aware EVMYulLean X
```

The active goal is to eliminate the explicit `Reference.SourceBridge.sourceRun` assumption and prove a checked bridge from imported Nethermind Yul execution to the compiler-facing source semantics, then compose that into the bytecode theorem.

The user nudged: maybe some of these semantics should be proved lower in the tower rather than in the imported-Yul bridge.

## Current Status

Lower layers have independent interpreters. Examples:

- `Expressions.Expr.run`, `Expressions.Block.run`, etc. interpret expression-aware syntax directly over `EVMState`.
- `Locals.Direct.*` interprets local variables/scopes directly using a `Ctx`/layout over the target stack.
- `Functions.Direct.*` interprets functions, returns, `leave`, and calls directly over function syntax.
- `Objects.Object.run` currently runs the root object's code through `Functions.Program.run`; object data/nested object semantics are still thin.
- `Yul.Program.run` is imported Nethermind Yul execution through `EvmYul.Yul.callDispatcher`.
- `Yul.Lowered.run` is quarantined compiler-facing execution through object lowering.

`Yul.Reference.lean` is currently very large and contains:

- imported Yul safe/accepted predicates;
- state/result relation config from imported Yul state to compiler EVM state;
- exact/source-visible/full-layout stack relations;
- source-side imported `evalArgs`, `primCall`, switch, block, terminal reductions;
- target-side replay facts for generated compiler temporaries and terminal arguments;
- many compositional `ResultSeqRunBridgeWithLayoutSlots` / block / prefix interfaces;
- top bridge theorem wrappers that still take `Reference.SourceBridge`.

Some recent refactors started moving target-only proof facts lower:

1. `EvmCompiler.Yul.ArgSlots` now owns target-only generated argument slot replay:

```lean
namespace EvmCompiler.Yul.ArgSlots

def LayoutSlotValue (fullLayout : List Name) (stack : EvmYul.Stack Word)
    (name : Name) (value : Word) : Prop :=
  ∃ idx : Nat, fullLayout[idx]? = some name ∧ stack[idx]? = some value

inductive Values (layout : List Name) (stack : EvmYul.Stack Word) :
    List (Locals.Expr 1) → List Word → Prop where
  | nil : Values layout stack [] []
  | cons_var {name : Name} {rest : List (Locals.Expr 1)}
      {value : Word} {values : List Word}
      (hSlot : LayoutSlotValue layout stack name value)
      (hTail : Values layout stack rest values) :
      Values layout stack (.var name :: rest) (value :: values)

theorem Values.runCode_toStackSeq
    (ctx : Locals.Ctx) (baseState currentState : EVMState)
    (layout : List Name) (offset : Nat) (pushed : List Word)
    {exprs : List (Locals.Expr 1)} {values : List Word}
    {results : Nat} {seq : Locals.ExprSeq results}
    (hCtxLayout : ctx.layout = layout)
    (hNoDup : layout.Nodup)
    (hCurrentStack : currentState.stack = pushed ++ baseState.stack)
    (hPushedLen : pushed.length = offset)
    (hSlots : Values layout baseState.stack exprs values)
    (hSeq : Expr.List.toStackSeq? exprs results = some seq)
    (hBound :
      ∀ {pos : Nat} {name : Name} {idx : Nat},
        exprs.reverse[pos]? = some (.var name) →
          layout[idx]? = some name →
            offset + pos + idx + 1 ≤ 16) :
    ∃ finalState : EVMState,
      Locals.Direct.Expr.ExprSeq.runCode ctx offset seq currentState =
        .ok finalState ∧
      finalState.stack = values ++ pushed ++ baseState.stack ∧
      finalState.toSharedState = currentState.toSharedState
```

This module imports the compiler and locals preservation, but not the large `Yul.Reference` bridge.

2. `EvmCompiler.Yul.PrimSemantics` now owns primitive facts below `Yul.Reference`:

```lean
namespace EvmCompiler.Yul.PrimSemantics

theorem primCall_add_ok
    (fuel : Nat) (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore) (left right : Word) :
    EvmYul.Yul.primCall fuel.succ (.Ok shared store)
        ((.StopArith .ADD : EvmYul.Operation .Yul)) [left, right] =
      .ok (.Ok shared store, [EvmYul.UInt256.add left right])

theorem basicOp_step_add_of_stack
    (state : EVMState) (left right : Word) (stack : EvmYul.Stack Word)
    (hStack : state.stack = left :: right :: stack) :
    Structured.BasicOp.step .add state =
      .ok (state.replaceStackAndIncrPC
        (EvmYul.UInt256.add left right :: stack))
```

Analogous facts exist for `iszero`, `not`, `add`, `mul`, `sub`.

3. `Yul.Reference` now has a generic binary primitive bridge:

```lean
theorem exprValueBridgeWithLayoutSlots_binary_of_bound_args_target
  -- Parameters include:
  -- imported primCall fact;
  -- Expr.List.toStackSeq? evidence;
  -- target run fact from generic argument replay;
  -- StateRel / layout-slot relation;
  -- then yields an expression bridge for a one-result binary primitive.
```

This allowed `ADD` and `SUB` to avoid bespoke two-hidden-args proofs. `MUL` is being added on the same route.

## Important Current Definitions

Imported source run boundary:

```lean
def Yul.Program.run (fuel : Nat) (program : Program) (state : ReferenceState) :
    Except ReferenceException ReferenceResult :=
  match
      EvmYul.Yul.callDispatcher fuel (some program.contract)
        (installContract program state) with
  | .ok (state', _rets) => .ok (.regular state')
  | .error (.YulHalt state' value) => .ok (.yulHalt state' value)
  | .error (.Revert stateBeforeRevert) => .ok (.revert stateBeforeRevert)
  | .error exception => .error exception
```

Quarantined lowering-defined compiler-facing Yul:

```lean
noncomputable def Yul.Lowered.run (fuel : Nat) (program : Program)
    (state : EVMState) : Except EVMException Outcome :=
  match program.toObjects? with
  | none => .error .InvalidInstruction
  | some lower => lower.run fuel state
```

Explicit unfinished bridge:

```lean
structure SourceBridge (stateRel : StateRel) (outcomeRel : OutcomeRel)
    (program : Program) (referenceFuel : Nat)
    (referenceInitial : State) (referenceResult : Result) where
  accepted : Accepted program
  sourceFuel : Nat
  compilerInitial : EVMState
  outcome : Outcome
  referenceRun :
    runResult referenceFuel program referenceInitial = .ok referenceResult
  initialRel : stateRel (installContract program referenceInitial)
    compilerInitial
  sourceRun :
    Lowered.run sourceFuel program compilerInitial = .ok outcome
  outcomeRel : outcomeRel referenceResult outcome
```

Public theorem still consumes this:

```lean
theorem compile_preserves_of_source_bridge
    (bridge :
      Reference.SourceBridge stateRel outcomeRel program referenceFuel
        referenceInitial referenceResult)
    (hCompile : compileChecked? program = some asm)
    (hInitialPc :
      bridge.compilerInitial.pc = Assembly.Program.pcAfter []) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult asm targetFuel bridge.compilerInitial =
        .ok targetOutcome ∧
      Structured.Preservation.WholeProgramOutcomeRel
        bridge.outcome targetOutcome :=
  compile_preserves_checked hCompile hInitialPc bridge.sourceRun
```

State/layout relation in `Yul.Reference`:

```lean
structure StateRelConfig where
  accountMapRel : AccountMapRel
  codeRel : CodeImageRel
  varStackRel : VarStackRel
  terminalRel : Assembly.HaltKind → Word → State → EVMState → Prop
  revertRel : State → EVMState → Prop
  gasAvailableRel : Word → Word → Prop
  totalGasRel : Nat → Nat → Prop

inductive CompilerStateRelWithLayoutSlots (cfg : StateRelConfig)
    (sourceLayout fullLayout : List Name) : State → EVMState → Prop where
  | ok {shared : EvmYul.SharedState .Yul} {store : EvmYul.Yul.VarStore}
      {compiler : EVMState}
      (hShared : SharedStateRel cfg shared compiler.toSharedState)
      (hVars : VisibleVarSlotRel sourceLayout fullLayout store compiler.stack)
      (hCover : fullLayout.length ≤ compiler.stack.length) :
      CompilerStateRelWithLayoutSlots cfg sourceLayout fullLayout
        (.Ok shared store) compiler
```

Structured typed-continuation facade currently exists but is not the public proof boundary:

```lean
namespace Structured.TypedContinuations

inductive Shape where
  | any
  | unreachable
  | named (name : String)
  | join (scope tag : Nat)
  | loop (scope tag : Nat)
  | afterCode (input : Shape) (code : Code)
  | afterCondition (input : Shape) (cond : Code)
  | afterSwitchPop (input : Shape) (scrutinee : Code)
  | procEntry (name : Name) (argc : Nat)
  | procExit (name : Name) (retc : Nat)
  | callReturn (name : Name) (token : Word)
  | programEnd

structure Kont where
  target : Target
  shape : Shape

structure Context where
  procs : List Proc := []
  regular : Kont
  break? : Option Kont := none
  continue? : Option Kont := none
  leave? : Option Kont := none

structure Result where
  compiled : CompileResult
  entryShape : Shape
  fallthroughShape : Shape
  labels : LabelMap
  transfers : List TransferObligation
  returnKonts : List ReturnKont

def Program.TypedBoundary (program : Program) : Prop :=
  (Program.typedInterface program).TargetsDeclared []
```

This is currently more of a typed facade / acceptance evidence around the existing structured compiler, not a full block-parameter CFG IR.

## My Concern

The recursive imported-Yul bridge is becoming hard because many proof obligations are happening in `Yul.Reference`:

- source Yul evaluation order;
- target compiler-generated temp replay;
- locals stack layout;
- scoped cleanup;
- switch body/default selection;
- primitive opcode facts;
- terminal/revert/selfdestruct result relations;
- recursive sequence/block composition.

Recent lower-splitting helped: `ArgSlots` and `PrimSemantics` clearly do not need full imported-reference context. But I suspect there are more obligations being proved at the wrong semantic floor. The user specifically wonders whether some semantics should be proved lower in the compiler tower.

## Questions

1. Which theorem families currently in `Yul.Reference` should definitely move lower, and to which layer?

2. Should primitive equivalence be proved at the assembly/structured boundary once for all EVM opcodes, then merely imported by higher layers, rather than rebuilding source/target primitive bridges in the Yul bridge?

3. Should locals/scopes own the exact varstore-to-stack relation and cleanup theorem in a source-independent way, with `Yul.Reference` only adapting Nethermind's `VarStore`/`restrictStoreTo` into that generic locals relation?

4. Should argument evaluation order and temporary binding be part of the expression layer semantics/proof, rather than a Yul.Reference-specific bridge around `evalArgs`?

5. Should the typed-continuation/CFG facade become a real public lower interface now, or is it reasonable to defer until after this bridge?

6. What is the recommended smallest refactor that reduces proof blowup without forcing a total rewrite?

7. What should remain in `Yul.Reference` no matter what?

## Constraints

- No `sorry`, `admit`, or new axioms.
- Do not make compiler-generated certificates public assumptions.
- Every layer must keep an independent interpreter.
- Public theorem should eventually quantify over imported `EvmYul.Yul` execution, not over `Yul.Lowered.run`.
- Gas and PC remain explicit top/theorem boundary assumptions where appropriate.
- Avoid a large new IR unless clearly worth it now.
- Existing checked work should be preserved if possible.

Please answer with a concrete recommended boundary map: theorem family -> layer/module, and identify any current design smell that would make the final theorem fragile.
