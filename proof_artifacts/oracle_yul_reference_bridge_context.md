# Oracle request: Nethermind Yul to compiler-facing Yul bridge

We are in `/Users/dan/Projects/evm-compiler`, a Lean project building a verified compiler tower:

```
Nethermind EvmYul.Yul AST/reference semantics
  -> EvmCompiler.Yul compiler-facing semantics
  -> Objects -> Functions -> Locals -> Expressions -> Structured
  -> labeled assembly -> resolved assembly/bytecode -> EvmYul EVM X
```

The user asks to make all necessary changes and prove the bridge from Nethermind's Yul to our compiler-facing Yul.

Important current files:

- `EvmCompiler/Yul/Syntax.lean`:
  - `Program` wraps `EvmYul.Yul.Ast.YulContract`.
  - `Word := EvmYul.UInt256`
  - `EVMState := Objects.EVMState := ... := EvmYul.EVM.State`
  - `Outcome := Objects.Outcome := Structured.Outcome`

- `EvmCompiler/Yul/Compiler.lean`:
  - Lowers imported `AstExpr`/`AstStmt` to `Objects.Program`.
  - `Prim.toBasicOp? : EvmYul.Operation .Yul -> Option Structured.BasicOp`.
  - Currently maps many primitives directly to EVM-like `Structured.BasicOp`, including `CODESIZE`, `CODECOPY`, `EXTCODESIZE`, `EXTCODECOPY`, `EXTCODEHASH`.
  - I just fixed `Expr.List.lower1?` so it evaluates expression-call preludes right-to-left while preserving final argument list order:
    ```lean
      def List.lower1? (state : Fresh.State) :
          List AstExpr →
            Option (List Functions.Stmt × List (Locals.Expr 1) × Fresh.State)
        | [] => some ([], [], state)
        | expr :: rest => do
            let (preRest, lowerRest, state') ← List.lower1? state rest
            let (preHead, lowerHead, state'') ← lower? 1 state' expr
            some (preRest ++ preHead, lowerHead :: lowerRest, state'')
    ```

- `EvmCompiler/Yul/Semantics.lean`:
  ```lean
  noncomputable def Program.run (fuel : Nat) (program : Program) (state : EVMState) :
      Except EVMException Outcome :=
    match program.toObjects? with
    | none => .error .InvalidInstruction
    | some lower => lower.run fuel state
  ```

- `EvmCompiler/Yul/Reference.lean` now uses imported dispatcher entry:
  ```lean
  namespace Reference
  abbrev State := EvmYul.Yul.State
  abbrev Exception := EvmYul.Yul.Exception

  def installContract (program : Program) : State → State
    | .Ok shared store =>
        .Ok
          { shared with
            executionEnv :=
              { shared.executionEnv with code := program.contract } }
          store
    | .OutOfFuel => .OutOfFuel
    | .Checkpoint jump => .Checkpoint jump

  def run (fuel : Nat) (program : Program) (state : State) :
      Except Exception State :=
    match
        EvmYul.Yul.callDispatcher fuel (some program.contract)
          (installContract program state) with
    | .ok (state', _rets) => .ok state'
    | .error exception => .error exception

  abbrev StateRel := State → EVMState → Prop
  abbrev OutcomeRel := State → Outcome → Prop

  structure SourceBridge (stateRel : StateRel) (outcomeRel : OutcomeRel)
      (program : Program) (referenceFuel : Nat)
      (referenceInitial referenceFinal : State) where
    sourceFuel : Nat
    compilerInitial : EVMState
    outcome : Outcome
    referenceRun :
      run referenceFuel program referenceInitial = .ok referenceFinal
    initialRel : stateRel referenceInitial compilerInitial
    sourceRun :
      program.run sourceFuel compilerInitial = .ok outcome
    outcomeRel : outcomeRel referenceFinal outcome
  end Reference
  ```

Existing theorem after that composes `SourceBridge.sourceRun` through checked compiler/bytecode preservation. The remaining blocker is replacing `sourceRun` with a real theorem from `Reference.run`.

Imported EvmYul Yul semantics facts:

- `EvmYul.Yul.State`:
  ```lean
  inductive Jump where
    | Continue : EvmYul.SharedState .Yul → VarStore → Jump
    | Break    : EvmYul.SharedState .Yul → VarStore → Jump
    | Leave    : EvmYul.SharedState .Yul → VarStore → Jump

  inductive State where
    | Ok         : EvmYul.SharedState .Yul → VarStore → State
    | OutOfFuel  : State
    | Checkpoint : Jump → State
  ```

- `EvmYul.Yul.eval` evaluates call args by `args.reverse`, hence last-to-first side effects.
- `EvmYul.Yul.exec Switch` evaluates all cases from the same post-scrutinee state and also evaluates default before selecting:
  ```lean
  | .Switch cond cases' default' =>
    match eval fuel' cond codeOverride s with
    | .error e => .error e
    | .ok (s₁, cond) =>
      match execSwitchCases fuel' codeOverride s₁ cases' with
      | .error e => .error e
      | .ok branches =>
        match exec fuel' (.Block default') codeOverride s₁ with
        | .error e => .error e
        | .ok s₂ =>
          (List.foldr
             (λ (valᵢ, sᵢ) s ↦ if valᵢ = cond then sᵢ else s)
             (.ok s₂) branches)
  ```
  This is unusual but may still be one-direction-preservable for successful reference runs, since non-selected side effects are discarded; default errors/fuel failures can make reference have no successful run.

- `EvmYul.Semantics.step` for `.Yul` has operation-specific behavior. Many primitives share the same transformers with `.EVM`, but code-image primitives are tricky:
  - `ExecutionEnv .Yul.code` is a `YulContract`.
  - `ExecutionEnv .EVM.code` is a `ByteArray`.
  - `CODESIZE`/`CODECOPY`/`EXTCODECOPY`/`EXTCODEHASH` are EVM-bytecode-shaped.
  - `EXTCODESIZE` for `.Yul` explicitly returns `.YulEXTCODESIZENotImplemented`.

Downstream primitive threading:

- `Structured.BasicOp.step op state := Assembly.Target.stepInstr (Assembly.TargetInstr.prim op.toPrimOp) state`.
- `Assembly.PrimOp.step` uses `EvmYul` EVM primitives/helpers directly.

Question/request:

Please give a hostile design/proof critique and a concrete plan for proving the bridge. In particular:

1. Is a full theorem from imported `EvmYul.Yul.callDispatcher` successful runs to `Yul.Program.run` feasible with current target semantics, or must we introduce a `ReferenceAccepted` subset/restriction?
2. How should we define the state relation between `EvmYul.Yul.State.Ok (SharedState .Yul) VarStore` and `EvmYul.EVM.State`, given that the code fields and account maps are typed differently?
3. Should code-image primitives (`codesize`, `codecopy`, `extcodesize`, `extcodecopy`, `extcodehash`) be rejected for the Nethermind-Yul bridge until there is an explicit code-image/account-code relation, or can they be related cleanly?
4. Is the switch semantics mismatch a fatal problem for a one-way successful-run preservation theorem?
5. What is the smallest good theorem shape to implement first in Lean without lying or exploding proof search?

Constraints:

- No `sorry`, `admit`, new `axiom`, or unsafe.
- Do not hide compiler-generated evidence as public assumptions.
- It is acceptable to expose genuine semantic/resource premises like acceptedness, initial state relation, successful source run, and explicit gas/code-image/external-interaction boundaries.
- The user ultimately wants a source-complete verified compiler, but if exact imported Nethermind Yul semantics makes a construct impossible, identify the construct and the necessary repair.
