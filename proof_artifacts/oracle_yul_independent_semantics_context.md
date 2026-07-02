# Oracle Request: Yul Independent Semantics Bridge

We are in `/Users/dan/Projects/evm-compiler`, a Lean 4 project building a verified compiler tower:

`Yul -> Objects -> Functions -> Locals -> Expressions -> Structured -> Assembly -> EVMYulLean EVM`.

Constraint from the local `verifiable-compiler` skill: every semantic layer must have an independent interpreter/evaluation relation over its own syntax. Defining `run := lower then run lower` is invalid except for transparent adapter boundaries with no new source constructs.

Current state:

- `Structured`, `Expressions`, `Locals`, and `Functions` now have independent executable interpreters and checked adjacent preservation theorems.
- `Objects` now has a direct root-object interpreter:
  - `Object.run fuel (.mk _ code _ _) state := Functions.Program.run fuel code state`
  - `Program.run fuel program state := program.root.run fuel state`
  - checked bridge `Objects.Program.run_toFunctions` / `eval_toFunctions`.
- Remaining offender:
  - `EvmCompiler/Yul/Semantics.lean` still has:
    ```lean
    noncomputable def Program.run (fuel : Nat) (program : Program) (state : EVMState) :
        Except EVMException Outcome :=
      match program.toObjects? with
      | none => .error .InvalidInstruction
      | some lower => lower.run fuel state
    ```
  - `EvmCompiler/Yul/Reference.lean` imports `EvmYul.Yul.Interpreter` and defines the independent Nethermind-reference run:
    ```lean
    def runResult (fuel : Nat) (program : Program) (state : EvmYul.Yul.State) :
        Except EvmYul.Yul.Exception Result :=
      match EvmYul.Yul.callDispatcher fuel (some program.contract)
          (installContract program state) with
      | .ok (state', _rets) => .ok (.regular state')
      | .error (.YulHalt state' value) => .ok (.yulHalt state' value)
      | .error .Revert => .ok (.revert (installContract program state))
      | .error exception => .error exception
    ```
  - But the only current bridge is a proof-carrying assumption structure:
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
      initialRel : stateRel referenceInitial compilerInitial
      sourceRun :
        program.run sourceFuel compilerInitial = .ok outcome
      outcomeRel : outcomeRel referenceResult outcome
    ```

The compiler-facing Yul AST is `EvmYul.Yul.Ast`:

```lean
inductive Expr where
  | Call : (PrimOp ⊕ YulFunctionName) → List Expr → Expr
  | Var : Identifier → Expr
  | Lit : Literal → Expr

inductive Stmt where
  | Block : List Stmt → Stmt
  | Let : List Identifier → Option Expr → Stmt
  | ExprStmtCall : Expr → Stmt
  | Switch : Expr → List (Literal × List Stmt) → List Stmt → Stmt
  | For : Expr → List Stmt → List Stmt → Stmt
  | If : Expr → List Stmt → Stmt
  | Continue | Break | Leave
```

`Yul/Compiler.lean` lowers accepted Yul to Functions:

- literals/vars/primitive calls to `Locals.Expr`;
- primitive terminals `STOP`, `RETURN`, `REVERT`, `SELFDESTRUCT` to `Functions.Stmt.terminalArgs`;
- user calls in expressions are hoisted to fresh temporaries;
- `Let names (some userCall)` handles multi-return call assignment;
- `For cond post body` lowers to a `Functions.Stmt.for_` with no init, literal true condition, and a body prefix that evaluates `cond` and breaks on `iszero(cond)`;
- function definitions lower to `Functions.FunDef`.

Question:

What is the best Lean architecture to replace `Yul.Program.run := toObjects? >>= Objects.run` with an honest independent Yul interpreter and prove preservation to Objects/Functions without blowing up?

Please be concrete:

1. Should the compiler-facing Yul interpreter be a new direct interpreter over `EVMState`/`Functions.RunState` mirroring `Functions.Direct`, or should `Program.run` become the imported Nethermind `callDispatcher` semantics with a state/outcome relation to the compiler tower?
2. What theorem boundaries should be used for the adjacent Yul-to-Objects/Functions preservation theorem?
3. How should expression user calls, fresh temporaries, and Yul argument evaluation order be handled compositionally?
4. What should remain an explicit assumption versus what must be checked before calling the Yul layer complete?

Constraints:

- No `sorry`, `admit`, or axioms.
- Public compiler theorem should not take compiler-generated replay/source-bridge evidence.
- It is acceptable for `Accepted` to reject malformed/unsupported constructs, but not merely proof-inconvenient implemented constructs.
- We want the shortest honest route to get an independent Yul source semantics connected by checked proofs to the existing compiler tower.
