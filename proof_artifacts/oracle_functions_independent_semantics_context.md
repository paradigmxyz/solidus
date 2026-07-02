We are in a Lean verified compiler project at /Users/dan/Projects/evm-compiler. User asked to ensure every layer has an independent interpreter connected by proofs.

Current tower:
- Assembly, Structured, Expressions already have independent interpreters and preservation.
- Locals now has a public direct interpreter (`Locals.Program.run := Locals.Direct.Program.run`) and a built proof in `EvmCompiler/Locals/Preservation.lean`:
  `Locals.Direct.Program.run_toExpressions_exists` and public `Locals.Program.run_toExpressions_exists`, using an existential lower fuel theorem.
- I intentionally did NOT prove eventual all-large-fuel theorem yet; only `∃ lowerFuel`.

Now working on Functions layer.
Existing lowering in `EvmCompiler/Functions/Compiler.lean`:
- `Functions.Stmt.toLocals returns : Functions.Stmt -> List Locals.Stmt`
- `leave` lowers to `Lower.pushReturns returns ++ [.leave]`
- `call targets f args` lowers to `Lower.evalArgs args ++ [Locals.Stmt.call f] ++ Lower.assignReturnedTops targets`
- function defs lower to a Locals proc:
  `argc := fn.params.length`, `retc := fn.returns.length`, `entryLayout := fn.params.reverse`, and body is
  `Lower.initReturns fn.returns ++ StmtList.toLocals fn.returns fn.body.stmts ++ Lower.pushReturns fn.returns`.
- Program body lowers with returns `[]`.

I added an independent direct interpreter in `EvmCompiler/Functions/Semantics.lean` under `namespace Functions.Direct` that builds. It pattern matches on `Functions.Block`/`Functions.Stmt`, uses shared `Locals.Direct.Expr` and cleanup helpers, and implements:
- direct eval args, pushReturns, initReturns, assignTop/assignReturnedTops;
- direct structured control over Functions syntax;
- direct `FunDef.runBody`; direct `Stmt.call` evaluates args, finds the source function, splits args, pushes hidden return frame, runs direct `FunDef.runBody`, then popReturn/attachReturns and assigns return tops to targets.

Current public `Functions.Program.run` is still lowering-defined:
```
def run fuel program state := program.toLocals.run fuel state
```
Public theorem `Functions.Program.compile_preserves` just calls `Locals.Program.compile_preserves`.

Goal: flip public `Functions.Program.run` to `Functions.Direct.Program.run`, and prove an adjacent bridge:
```
theorem Functions.Direct.Program.run_toLocals_exists
  (hRun : Functions.Direct.Program.run fuel program initial = .ok outcome) :
  ∃ lowerFuel, program.toLocals.run lowerFuel initial = .ok outcome
```
or better if needed. Then public Functions preservation can use Locals preservation.

Important constraints:
- no public proof-carrying assumptions or call oracle;
- use source fuel induction for recursion;
- proof should be compositional and not blow up;
- we may define proof-local lower relations if helpful.

Question: What is the cleanest theorem architecture for Functions->Locals? In particular, how should we handle source `Stmt.call` vs its lowered multi-statement sequence, source `FunDef.runBody` vs lowered proc body, and fuel mismatch? Is it better to define a proof-local `LocalsRuns` relation over `List Locals.Stmt` analogous to the oracle's suggested `Lower.Runs` for Locals->Expressions? Please give concrete theorem shapes and Lean-proof strategy, including induction measures/order and helper lemmas.
