# Oracle request: critique the Yul bridge architecture

## Requested mode

Please critique the proof architecture, not just a local Lean error.

We are building a formally verified compiler pipeline in Lean for a Yul-like
language down to the Nethermind `EvmYul` EVM model. The current active goal is:

> Make the Yul/reference-boundary changes needed for a Nethermind Yul bridge,
> then implement and prove the checked bridge from the imported `EvmYul.Yul`
> semantics to the compiler-facing Yul semantics, composing it into the existing
> verified compiler theorem and auditing any semantic blockers.

I want hostile/constructive critique:

1. Is the current staged architecture right?
2. Is the current bridge interface compositional enough?
3. Are we accidentally rebuilding arity-specific proof packages instead of a
   reusable theorem schema?
4. What is the best next theorem shape for argument-list evaluation and
   primitive calls?
5. What should the public theorem boundary ultimately look like?
6. What should be demoted to private compatibility plumbing?

Assume no `sorry`, no new axioms, and no public theorem that takes
compiler-generated evidence as trusted input. Fundamental semantic/resource
premises are allowed, but compiler artifacts should be constructed by checked
Lean functions/theorems.

## Project/file context

Repo: `/Users/dan/Projects/evm-compiler`

Main file currently being worked:

```text
EvmCompiler/Yul/Reference.lean
```

Audit alias file:

```text
EvmCompiler/LayerAudit.lean
```

The current full build passed immediately before the latest attempted
`evalArgs` helper. After that helper, `lake build EvmCompiler.Yul.Reference`
fails in the helper only. The rest of this architecture was previously green.

## Compiler tower, high level

Lower layers already exist and have checked theorem spines:

```text
Assembly / labeled EVM-ish language
  -> gas-aware Nethermind EVM runner, with explicit gas/out-of-gas assumptions

Structured control/procedure layer
  -> Assembly

Expressions / Locals / Functions
  -> lower layers

Objects
  -> audited transparent adapter over Functions

Yul source boundary
  -> currently imports Nethermind `EvmYul.Yul` for public source semantics
```

Important current fact:

The compiler-facing Yul lowering/preservation tower exists, but the true
imported-Nethermind-Yul bridge is incomplete. The old/public route still has an
explicit `Reference.SourceBridge.sourceRun` style boundary: a field/premise that
says the imported Yul run corresponds to compiler-facing `Yul.Lowered.run`.
That is intentionally quarantined as incomplete. The goal is to replace it with
recursive per-construct bridge theorems from the imported interpreter.

## Source semantics and targeted imported Yul

The public source interpreter is the imported `EvmYul.Yul` semantics:

```lean
import EvmYul.Yul.Interpreter
```

In `EvmCompiler/Yul/Reference.lean`:

```lean
abbrev State := ReferenceState
abbrev Exception := ReferenceException
```

The current bridge is not intended to reimplement Yul semantics. It should prove
from imported `EvmYul.Yul.exec`, `eval`, `evalValues`, `evalArgs`,
`callDispatcher`/`runResult`, etc. to the compiler-facing language semantics.

We have also identified/fixed target semantic issues in the Nethermind Yul fork
used by this project, including selected-branch switch behavior, omitted
default notation, and halting `SELFDESTRUCT`; the PR to upstream semantics is
separate context.

## Current safe/reference boundary

At the imported Yul bridge boundary, some primitives are temporarily excluded
because they need code-image or external-call relations:

```lean
namespace Safe

def primitive : EvmYul.Operation .Yul → Prop
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

mutual
  def expr : AstExpr → Prop
    | .Lit _value => True
    | .Var _name => True
    | .Call (.inl prim) args => primitive prim ∧ exprs args
    | .Call (.inr functionName) args =>
        ObjectBuiltin.unsupported? functionName = false ∧ exprs args

  def exprs : List AstExpr → Prop
    | [] => True
    | head :: rest => expr head ∧ exprs rest

  ...
end
```

This is not meant to be the final source-complete theorem; it is a checked
accepted boundary while building bridge pieces.

## Central state/layout relations

The imported Yul varstore is source-visible. The compiled target stack also has
compiler-generated locals/temporaries. We moved from “hidden temps are a stack
prefix” to slot-addressed relations.

Definitions in `BridgeFacts`:

```lean
def VisibleVarSlotRel (sourceLayout fullLayout : List Name)
    (store : EvmYul.Yul.VarStore) (stack : EvmYul.Stack Word) : Prop :=
  ∀ {sourceIdx : Nat} {name : Name},
    sourceLayout[sourceIdx]? = some name →
      ∃ fullIdx : Nat, ∃ value : Word,
        fullLayout[fullIdx]? = some name ∧
        stack[fullIdx]? = some value ∧
        store.lookup name = some value

def LayoutSlotValue (fullLayout : List Name) (stack : EvmYul.Stack Word)
    (name : Name) (value : Word) : Prop :=
  ∃ idx : Nat, fullLayout[idx]? = some name ∧ stack[idx]? = some value

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

For expression results above a full layout:

```lean
inductive CompilerStateRelWithTempsAndLayoutSlots ...
```

This records a result/temp stack prefix plus a base stack satisfying the full
layout relation.

## Expression bridge interfaces

Existing one-result expression bridge:

```lean
def ExprValueBridgeWithLayoutSlots {cfg : StateRelConfig}
    (sourceLayout fullLayout fullLayoutAfter : List Name)
    (program : Functions.Program)
    (returns : List Name) (ctx : Locals.Ctx)
    (sourceFuel : Nat) (expr : AstExpr)
    (codeOverride : Option AstContract) (source : State)
    (compiler : RunState)
    (pre : List Functions.Stmt) (lower : Functions.Expr 1) : Prop :=
  ∃ sourceAfter : State, ∃ value : Word,
  ∃ compilerAfterPre : RunState, ∃ compilerAfterExpr : RunState,
  ∃ ctxAfter : Locals.Ctx, ∃ preFuel : Nat,
    EvmYul.Yul.evalValues sourceFuel expr codeOverride source =
      .ok (sourceAfter, [value]) ∧
    Functions.Direct.Block.runOpen program returns ctx preFuel
        { stmts := pre } compiler =
      .ok (Structured.Outcome.regular compilerAfterPre, ctxAfter) ∧
    ctx.layout = fullLayout ∧
    ctxAfter.layout = fullLayoutAfter ∧
    LayoutSuffix fullLayout fullLayoutAfter ∧
    Locals.Direct.Expr.runState ctxAfter lower compilerAfterPre =
      .ok compilerAfterExpr ∧
    CompilerStateRelWithTempsAndLayoutSlots cfg sourceLayout fullLayoutAfter
      [value] sourceAfter compilerAfterExpr.evm ∧
    compilerAfterPre.returns = compiler.returns ∧
    compilerAfterExpr.returns = compilerAfterPre.returns
```

Strengthened preserving-base bridge:

```lean
def ExprValueBridgeWithLayoutSlotsPreservingBase ... : Prop :=
  ∃ sourceAfter : State, ∃ value : Word,
  ∃ compilerAfterPre : RunState, ∃ compilerAfterExpr : RunState,
  ∃ ctxAfter : Locals.Ctx, ∃ preFuel : Nat,
  ∃ baseStack : EvmYul.Stack Word,
    ... ∧
    compilerAfterExpr.evm.stack = value :: baseStack ∧
    (∀ {name : Name} {slotValue : Word},
      LayoutSlotValue fullLayout compiler.evm.stack name slotValue →
        LayoutSlotValue fullLayoutAfter baseStack name slotValue) ∧
    ...
```

There are constructors for literals, variables, `iszero(e)`, `not(e)`, etc.
The preserving-base bridge is used so argument preludes can bind one expression
to a hidden local while preserving previously generated argument slots.

The hidden bind theorem:

```lean
theorem exprValueBridgeWithLayoutSlotsPreservingBase_bind_hidden
    ...
    (hiddenName : Name)
    (hExpr : ExprValueBridgeWithLayoutSlotsPreservingBase ...) :
    ∃ sourceAfter value compilerAfter ctxAfter targetFuel baseStack,
      EvmYul.Yul.evalValues sourceFuel expr codeOverride source =
        .ok (sourceAfter, [value]) ∧
      Functions.Direct.Block.runOpen program returns ctx targetFuel
          { stmts := pre ++ [Functions.Stmt.let_ hiddenName lower] }
          compiler =
        .ok (Structured.Outcome.regular compilerAfter,
          ctxAfter.withLayout (hiddenName :: ctxAfter.layout)) ∧
      ...
      LayoutSlotValue (hiddenName :: fullLayoutAfter)
        compilerAfter.evm.stack hiddenName value ∧
      (∀ {name slotValue},
        LayoutSlotValue fullLayout compiler.evm.stack name slotValue →
          LayoutSlotValue (hiddenName :: fullLayoutAfter)
            compilerAfter.evm.stack name slotValue) ∧
      compilerAfter.returns = compiler.returns
```

## The argument-order bug and compiler fix

Imported Yul evaluates function/primitive arguments right-to-left. In the
imported interpreter, primitive calls use:

```lean
EvmYul.Yul.evalArgs fuel args.reverse codeOverride state
```

The compiler previously lowered all argument expressions and then evaluated the
lowered expression sequence later. That delayed reads across later argument
effects, which is semantically wrong.

We changed the compiler to use:

```lean
def Expr.List.lowerBound1? (state : Fresh.State) :
    List AstExpr →
      Option (List Functions.Stmt × List (Locals.Expr 1) × Fresh.State)
  | [] => some ([], [], state)
  | expr :: rest => do
      let (preRest, lowerRest, state') ← List.lowerBound1? state rest
      let (preHead, lowerHead, state'') ← lower? 1 state' expr
      let (tmp, state''') ← Fresh.fresh? state''
      some
        (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead],
          .var tmp :: lowerRest, state''')
```

So for source-order `[a, b]`, it lowers/binds `b` first, then `a`, returning
source-order lowered vars `[tmpA, tmpB]`. `toStackSeq?` reverses the lowered var
list to match EVM pop order.

## Smell we are trying to remove

We previously introduced arity-specific packages:

```lean
def TwoHiddenArgsBridgeWithLayoutSlotValues ...
def TwoHiddenArgsPreludeBridgeWithLayoutSlotValues ...
```

These were useful for proving `ADD` after the argument-order fix, but they are
exactly the sort of non-compositional smell we want to retire. They bake in
binary arity and the shape `[left, right]`.

We recently introduced a generic replacement surface:

```lean
inductive ArgSlotValues (fullLayout : List Name)
    (stack : EvmYul.Stack Word) :
    List (Locals.Expr 1) → List Word → Prop where
  | nil : ArgSlotValues fullLayout stack [] []
  | cons_var {name : Name} {rest : List (Locals.Expr 1)}
      {value : Word} {values : List Word}
      (hSlot : LayoutSlotValue fullLayout stack name value)
      (hTail : ArgSlotValues fullLayout stack rest values) :
      ArgSlotValues fullLayout stack (.var name :: rest) (value :: values)

def BoundArgsBridgeWithLayoutSlotValues {cfg : StateRelConfig}
    (sourceLayout fullLayout fullLayoutAfter : List Name)
    (program : Functions.Program)
    (returns : List Name) (ctx : Locals.Ctx)
    (argFuel : Nat) (args : List AstExpr)
    (codeOverride : Option AstContract) (source : State)
    (compiler : RunState) (pre : List Functions.Stmt)
    (lowerArgs : List (Locals.Expr 1)) : Prop :=
  ∃ sourceAfter : State, ∃ values : List Word,
  ∃ compilerAfterArgs : RunState, ∃ ctxAfter : Locals.Ctx,
  ∃ preFuel : Nat,
    EvmYul.Yul.evalArgs argFuel args.reverse codeOverride source =
      .ok (sourceAfter, values.reverse) ∧
    Functions.Direct.Block.runOpen program returns ctx preFuel
        { stmts := pre } compiler =
      .ok (Structured.Outcome.regular compilerAfterArgs, ctxAfter) ∧
    ctx.layout = fullLayout ∧
    ctxAfter.layout = fullLayoutAfter ∧
    LayoutSuffix fullLayout fullLayoutAfter ∧
    CompilerStateRelWithLayoutSlots cfg sourceLayout fullLayoutAfter
      sourceAfter compilerAfterArgs.evm ∧
    ArgSlotValues fullLayoutAfter compilerAfterArgs.evm.stack lowerArgs
      values ∧
    compilerAfterArgs.returns = compiler.returns
```

This is source-order: `lowerArgs` and `values` are in the original source order.
The imported `evalArgs` returns `values.reverse` because it evaluates
`args.reverse`.

Checked base:

```lean
theorem boundArgsBridgeWithLayoutSlotValues_nil
    ...
    BoundArgsBridgeWithLayoutSlotValues ... argFuel.succ [] ... [] []
```

Checked helper:

```lean
namespace ArgSlotValues
theorem map_slots
    (hMap : ∀ {name value},
      LayoutSlotValue layout stack name value →
        LayoutSlotValue layout' stack' name value)
    (hArgs : ArgSlotValues layout stack exprs values) :
    ArgSlotValues layout' stack' exprs values
```

New cons component theorem, currently checked before I attempted the next
source-helper:

```lean
theorem boundArgsBridgeWithLayoutSlotValues_cons_components
    {sourceLayout fullLayout tailLayout headLayout : List Name}
    ...
    (hTailEval :
      EvmYul.Yul.evalArgs tailFuel rest.reverse codeOverride source =
        .ok (sourceAfterTail, valuesTail.reverse))
    (hTailRun :
      Functions.Direct.Block.runOpen program returns ctx tailPreFuel
          { stmts := preTail } compiler =
        .ok (Structured.Outcome.regular compilerAfterTail, ctxAfterTail))
    ...
    (hTailSlots :
      ArgSlotValues tailLayout compilerAfterTail.evm.stack lowerTail
        valuesTail)
    ...
    (hHead :
      ExprValueBridgeWithLayoutSlotsPreservingBase ...
        headFuel head codeOverride sourceAfterTail compilerAfterTail
        preHead lowerHead)
    (hFullEval :
      ∀ {sourceAfterHead : State} {headValue : Word},
        EvmYul.Yul.evalValues headFuel head codeOverride sourceAfterTail =
          .ok (sourceAfterHead, [headValue]) →
        EvmYul.Yul.evalArgs argFuel (head :: rest).reverse codeOverride
            source =
          .ok (sourceAfterHead, (headValue :: valuesTail).reverse)) :
    BoundArgsBridgeWithLayoutSlotValues ... argFuel (head :: rest)
      ... (preTail ++ (preHead ++ [let hiddenName lowerHead]))
      (.var hiddenName :: lowerTail)
```

Notice `hFullEval` is still explicit. The theorem composes the target/slot side
but does not yet prove the imported `evalArgs` source-side append-singleton fact.

## Current `ADD` routing

`ADD` now has a generic boundary theorem:

```lean
theorem exprValueBridgeWithLayoutSlots_add_of_bound_args
    ...
    (hArgs :
      BoundArgsBridgeWithLayoutSlotValues ... argFuel [left, right]
        ... [.var leftTmp, .var rightTmp]) :
    ExprValueBridgeWithLayoutSlots ... argFuel.succ
      (.Call (.inl ADD) [left, right]) ...
      (.prim .add (cons (.var rightTmp) (cons (.var leftTmp) nil)))
```

For now it delegates to the old two-arg theorem via:

```lean
boundArgsBridgeWithLayoutSlotValues_two_to_legacy
```

So `ADD` is public-facing generic, but internally still uses a binary
compatibility proof. This is acceptable only temporarily.

## Desired next proof shape

I think we need:

1. A general imported source helper for `evalArgs prefix ++ [head]`, scheduled
   with the same fuel as imported Yul.
2. Then a theorem deriving `BoundArgsBridgeWithLayoutSlotValues` directly from
   recursive `Expr.List.lowerBound1?` evidence, using nil+cons and a recursive
   expression bridge for each head.
3. Then a generic theorem from:
   - `ArgSlotValues fullLayout stack lowerArgs values`
   - `Expr.List.toStackSeq? lowerArgs n = some seq`
   - `values.length = n` or similar
   - DUP bounds / `layout.Nodup`
   to:
   - `Locals.Direct.Expr.ExprSeq.runCode ctx 0 seq state`
     pushes `values` in EVM pop order.
4. Then a `PrimSpec` for each primitive:
   - imported Yul `primCall` behavior
   - target `Structured.BasicOp.step` behavior
   - arity/input/output facts
   - excluded effects/resource contracts as explicit obligations.

Question: is this the right decomposition, or should the generic target theorem
be phrased differently?

## Local Lean error in the attempted source helper

I tried to add:

```lean
def evalArgsAppendFuel (base : Nat) : List AstExpr → Nat
  | [] => base.succ.succ.succ
  | _head :: tail => (evalArgsAppendFuel base tail).succ.succ

theorem evalArgs_append_singleton_scheduled
    (base : Nat) (argsPrefix : List AstExpr) (head : AstExpr)
    (codeOverride : Option AstContract)
    {source sourceAfterPrefix sourceAfterHead : State}
    {valuesPrefix : List Word} {headValue : Word}
    (hPrefix :
      EvmYul.Yul.evalArgs (evalArgsAppendFuel base argsPrefix) argsPrefix
          codeOverride source =
        .ok (sourceAfterPrefix, valuesPrefix))
    (hHead :
      EvmYul.Yul.eval base.succ.succ head codeOverride sourceAfterPrefix =
        .ok (sourceAfterHead, headValue)) :
    EvmYul.Yul.evalArgs (evalArgsAppendFuel base argsPrefix)
        (argsPrefix ++ [head]) codeOverride source =
      .ok (sourceAfterHead, valuesPrefix ++ [headValue])
```

The proof is not finished. Current error after a small naming fix:

```text
error: EvmCompiler/Yul/Reference.lean:678:10: tactic 'rewrite' failed,
did not find instance of the pattern in the target expression
  EvmYul.Yul.evalArgs (Nat.succ ?fuel) (?head :: ?tail) ?codeOverride ?state

case nil.intro
base : ℕ
head : AstExpr
codeOverride : Option AstContract
sourceAfterHead : State
headValue : Word
source sourceAfterPrefix : State
valuesPrefix : List Word
hHead : eval base.succ.succ head codeOverride sourceAfterPrefix =
  Except.ok (sourceAfterHead, headValue)
left✝ : source = sourceAfterPrefix
right✝ : valuesPrefix = []
⊢ EvmYul.Yul.evalArgs (evalArgsAppendFuel base []) ([] ++ [head])
    codeOverride source =
  Except.ok (sourceAfterHead, valuesPrefix ++ [headValue])

error: unsolved goals in cons/error case:
hRest : evalArgs (evalArgsAppendFuel base rest) rest ... = error err
hPrefix : cons' firstValue (error err) = ok (...)
⊢ evalArgs ... (first :: rest ++ [head]) ... = ok (...)

error: in cons/ok case:
ih hRest hHead
but hHead is about sourceAfterPrefix, expected sourceAfterRest
```

These local errors are probably fixable, but I am more interested in whether the
scheduled helper and the entire decomposition are architecturally right.

## Specific questions for critique

1. Should `BoundArgsBridgeWithLayoutSlotValues` quantify over `values` in source
   order while imported `evalArgs args.reverse` returns `values.reverse`, or is
   that an avoidable proof tax?

2. Should we instead define the bridge in evaluation order and only convert to
   source/EVM order at the primitive boundary?

3. Is `ArgSlotValues lowerArgs values` too weak? Should it include:
   - `lowerArgs.length = values.length`;
   - `lowerArgs` are all `.var generatedName`;
   - `fullLayout.Nodup`;
   - DUP accessibility bounds;
   - freshness/disjointness from source layout?

4. Is `ExprValueBridgeWithLayoutSlotsPreservingBase` the right invariant for
   expression preludes, or should there be a more explicit frame/continuation
   object, maybe a small typed-stack layout record?

5. Is `hFullEval` as a premise in the cons component theorem a good factoring,
   or should the cons theorem itself own the imported `evalArgs` append proof?

6. What is the best final generic theorem for primitives?
   I am imagining:

   ```lean
   theorem exprValueBridgeWithLayoutSlots_prim_of_bound_args
     (hLower : Expr.lower1? freshState (.Call (.inl prim) args) = ...)
     (hArgs : BoundArgsBridgeWithLayoutSlotValues ... args ... lowerArgs)
     (hSeq : Expr.List.toStackSeq? lowerArgs (BasicOp.inputs op) = some seq)
     (hPrimSpec : PrimSpec prim op)
     ...
   ```

   Is this good, or should `PrimSpec` include the `toStackSeq?`/target-run
   theorem?

7. How should we avoid proof blowup when supporting the full primitive table,
   including zero-result terminal effects and stateful/environmental opcodes?

8. What should be the public theorem boundary after this work?
   The desired end state is no public `SourceBridge.sourceRun`; instead a
   theorem from imported `EvmYul.Yul` run/eval plus checked compiler lowering
   to compiler-facing `Yul.Lowered.run`, then composed into existing assembly
   and gas-aware EVM preservation.

Useful answer format:

- Say whether the current architecture is basically right, wrong, or only
  locally patched.
- Identify the smallest changes that would improve compositionality.
- Give recommended theorem statements/invariants for argument lists and
  primitives.
- Call out any hidden false assumption around Yul argument order, stack layout,
  source varstore/block scoping, terminal halts, `leave`, or external effects.

