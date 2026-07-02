We are in the Lean project at: /Users/dan/Projects/evm-compiler

Task: extend the bounded Structured preservation proof for `for` loops without weakening theorem statements and without using sorry, admit, unsafe, partial, or axioms.

File: /Users/dan/Projects/evm-compiler/EvmCompiler/Structured/Preservation.lean

Current context:
- Module already builds with `lake build EvmCompiler.Structured.Preservation`.
- The file defines unbounded `ProcedurePreservation.preserves_for_in_programLayout` and a bounded interface:
  * `ProcedurePreservation.StmtPreservesInProgramLayoutUpTo`
  * `ProcedurePreservation.BlockPreservesInProgramLayoutUpTo`
  * `ProcedurePreservation.preserves_cons_in_programLayout_upTo`
  * `ProcedurePreservation.preserves_if_in_programLayout_upTo`
- The goal is to discharge recursive call assumptions by source-fuel induction. For this, for-loop preservation must have a fuel-bounded version.

Theorem to add/prove, in namespace `EvmCompiler.Structured.Preservation.ProcedurePreservation` near the existing bounded helpers:

```
set_option maxHeartbeats 1200000 in
theorem preserves_for_in_programLayout_upTo {program : Program}
    {layout : ProgramLayout program} {maxFuel : Nat}
    {ctx : CompileContext} {supply : LabelSupply}
    {init post body : Block} {cond : Code}
    (hCondSafe : Code.RunnerSafe cond)
    (hCondFrame : Code.FrameSafe cond)
    (hInit :
      BlockPreservesInProgramLayoutUpTo layout maxFuel
        { ctx with breakLabel? := none, continueLabel? := none }
        (LabelSupply.next supply) init)
    (hBody :
      BlockPreservesInProgramLayoutUpTo layout maxFuel
        { ctx with
          breakLabel? := some (LabelSupply.label supply 3)
          continueLabel? := some (LabelSupply.label supply 2) }
        (Block.compileFromCtx init
          { ctx with breakLabel? := none, continueLabel? := none }
          (LabelSupply.next supply)).next
        body)
    (hPost :
      BlockPreservesInProgramLayoutUpTo layout maxFuel
        { ctx with breakLabel? := none, continueLabel? := none }
        (Block.compileFromCtx body
          { ctx with
            breakLabel? := some (LabelSupply.label supply 3)
            continueLabel? := some (LabelSupply.label supply 2) }
          (Block.compileFromCtx init
            { ctx with breakLabel? := none, continueLabel? := none }
            (LabelSupply.next supply)).next).next
        post) :
    StmtPreservesInProgramLayoutUpTo layout maxFuel ctx supply
      (.for_ init cond post body) := by
  ...
```

Informal proof / guidance:
PROVIDED SOLUTION:
Copy the structure of `preserves_for_in_programLayout`, but each use of `hInit`, `hBody`, or `hPost` must pass a fuel bound derived from the current `hLt : fuel < maxFuel`. In all `Stmt.Eval.for_*` cases the nested init/body/post/loop fuel is structurally smaller than the outer statement fuel, so `omega` should discharge bounds like `innerFuel < maxFuel`.

If the existing helper `for_eval_in_programLayout` blocks because it expects unbounded `BlockPreservesInProgramLayout`, add a bounded variant of the smallest necessary helper(s), preferably `for_eval_in_programLayout_upTo`, by copying the unbounded proof and threading fuel bounds into the body/post calls and recursive loop call. Avoid duplicating unrelated switch/call code. Keep theorem statements strong and compositional.

Constraints:
- Do not weaken any existing theorem or definition.
- Do not add axiom/sorry/admit/unsafe/partial.
- Do not hide the call obligation in `Program.Accepted` or another certificate.
- Use source-fuel inequalities explicitly; `omega` is acceptable.
- Return a patch or complete replacement code.

Validation command:
lake build EvmCompiler.Structured.Preservation
