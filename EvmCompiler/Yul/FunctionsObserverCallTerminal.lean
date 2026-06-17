import EvmCompiler.Yul.FunctionsObserverCall
import EvmCompiler.Yul.FunctionsObserverTerminal

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCallTerminal

/-!
Terminal function-call composition owned by the adjacent Yul-to-Functions call
boundary. The ordinary compiler selects the function and argument lowering;
this module only composes their canonical semantics.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

structure BodyResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (body : Functions.Block)
    (failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript))
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx) where
  kind : Assembly.HaltKind
  finalTarget : Functions.ObserverSemantics.State transcript
  finalCtx : Functions.Source.Ctx
  run :
    ∃ fuel,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel body target =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind finalTarget,
            finalCtx)
  relation :
    FunctionsObserverOutcome.TerminalFailureRel codeRel failure
      (Functions.Source.Effectful.Outcome.halt kind finalTarget)

namespace BodyResult

noncomputable def requiredFuel
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (result :
      BodyResult contract codeRel program body failure target ctx) : Nat := by
  classical
  exact Nat.find result.run

theorem run_requiredFuel
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (result :
      BodyResult contract codeRel program body failure target ctx) :
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program ctx result.requiredFuel body target =
      .ok
        (Functions.Source.Effectful.Outcome.halt
          result.kind result.finalTarget,
          result.finalCtx) := by
  classical
  simpa [requiredFuel] using Nat.find_spec result.run

theorem requiredFuel_le_of_run
    {transcript : Trace}
    {contract : MemoryContract.Contract}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (result :
      BodyResult contract codeRel program body failure target ctx)
    {fuel : Nat}
    (hRun :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel body target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            result.kind result.finalTarget,
            result.finalCtx)) :
    result.requiredFuel ≤ fuel := by
  classical
  simpa [requiredFuel] using Nat.find_min' result.run hRun

def ofStatement
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {body : Functions.Block}
    {lower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (hBody : body = { stmts := lower })
    (result :
      FunctionsObserverTerminal.StatementResult
        contract codeRel program lower failure target ctx) :
    BodyResult contract codeRel program body failure target ctx := by
  subst body
  exact
    { kind := result.kind
      finalTarget := result.finalTarget
      finalCtx := result.finalCtx
      run := result.run
      relation := result.relation }

end BodyResult

theorem statementOfPreparedArgs
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName : Name}
    {targets : List Name}
    {fn : Functions.FunDef}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {fresh : Fresh.State}
    {layout : List Name}
    {argValues : List Word}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {sourceAfterArgs :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {paramStore : Locals.Source.Store}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs fresh
        layout sourceAfterArgs target ctx argValues)
    (hTargets : targets.Nodup)
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (hParams :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (body :
      BodyResult contract codeRel program fn.body failure
        (argsPrepared.prepared.prepared.finalTarget.withSource
          { shared :=
              argsPrepared.prepared.prepared.finalTarget.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore })
        (Functions.Source.Effectful.FunDef.bodyCtx fn)) :
    Nonempty
      (FunctionsObserverTerminal.StatementResult
        contract codeRel program
        (preArgs ++
          [Functions.Stmt.call targets functionName lowerArgs])
        failure target ctx) := by
  let targetAfterArgs := argsPrepared.prepared.prepared.finalTarget
  have hArgsEval :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs targetAfterArgs =
        .ok (targetAfterArgs, argValues) :=
    argsPrepared.prepared.stable targetAfterArgs
      (StateRelation.Vars.TargetExtends.refl _)
  obtain ⟨bodyFuel, hBodyRun⟩ := body.run
  have hRunBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn argValues (bodyFuel + 1) targetAfterArgs =
        .ok
          (Functions.Source.Effectful.CallResult.halted
            body.kind body.finalTarget) := by
    apply
      Functions.Source.Effectful.FunDef.runBody_halted_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hParams
    simpa [targetAfterArgs] using hBodyRun
  have hCallStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program argsPrepared.prepared.prepared.finalCtx
          (bodyFuel + 2)
          (.call targets functionName lowerArgs) targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            argsPrepared.prepared.prepared.finalCtx) := by
    apply
      Functions.Source.Effectful.Stmt.call_halted_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hTargets hArgsEval hFind
    simpa [Nat.add_assoc] using hRunBody
  have hCallBlock :=
    Functions.Source.Effectful.Block.runOpen_singleton_of_run
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hCallStmt
  have hFullRun :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program preArgs
      [Functions.Stmt.call targets functionName lowerArgs]
      ctx argsPrepared.prepared.prepared.finalCtx target targetAfterArgs
      (Functions.Source.Effectful.Outcome.halt
        body.kind body.finalTarget)
      argsPrepared.prepared.prepared.finalCtx
      argsPrepared.prepared.prepared.run hCallBlock
  exact
    ⟨body.kind, body.finalTarget,
      argsPrepared.prepared.prepared.finalCtx,
      hFullRun, body.relation⟩

theorem expressionOfPreparedArgs
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {functionName tmp : Name}
    {fn : Functions.FunDef}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {argsFresh finalFresh : Fresh.State}
    {layout : List Name}
    {argValues : List Word}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {sourceAfterArgs :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {paramStore : Locals.Source.Store}
    (argsPrepared :
      FunctionsObserverExpression.ScopedPreparedArgs
        contract transcript codeRel program preArgs lowerArgs argsFresh
        layout sourceAfterArgs target ctx argValues)
    (hFresh : Fresh.fresh? argsFresh = some (tmp, finalFresh))
    (hFind :
      Functions.Source.FunList.find? functionName program.functions =
        some fn)
    (hParams :
      Functions.Source.Store.insertMany fn.params argValues
          Locals.Source.Store.empty =
        some paramStore)
    (body :
      BodyResult contract codeRel program fn.body failure
        ((argsPrepared.prepared.prepared.finalTarget.withSource
          (argsPrepared.prepared.prepared.finalTarget.source.insert
            tmp Functions.Source.zero)).withSource
          { shared :=
              argsPrepared.prepared.prepared.finalTarget.source.shared,
            vars :=
              Functions.Source.Store.initReturns
                fn.returns paramStore })
        (Functions.Source.Effectful.FunDef.bodyCtx fn)) :
    Nonempty
      (FunctionsObserverTerminal.StatementResult
        contract codeRel program
        (preArgs ++
          [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
            Functions.Stmt.call [tmp] functionName lowerArgs])
        failure target ctx) := by
  let targetAfterArgs := argsPrepared.prepared.prepared.finalTarget
  have hZeroEval :
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.lit Functions.Source.zero : Locals.Expr 1) targetAfterArgs =
        .ok (targetAfterArgs, [Functions.Source.zero]) := by
    rfl
  let zeroPrepared :=
    FunctionsObserverExpression.Prepared.generated
      (contract := contract) (transcript := transcript)
      (codeRel := codeRel) (program := program)
      (ctx := argsPrepared.prepared.prepared.finalCtx)
      hFresh hZeroEval argsPrepared.prepared.prepared.rel
      argsPrepared.prepared.prepared.domain
      argsPrepared.prepared.prepared.scope
  have hArgsEval :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs zeroPrepared.finalTarget =
        .ok (zeroPrepared.finalTarget, argValues) := by
    apply argsPrepared.prepared.stable
    exact
      StateRelation.Vars.TargetExtends.trans
        (StateRelation.Vars.TargetExtends.refl _)
        zeroPrepared.varsExtends
  obtain ⟨bodyFuel, hBodyRun⟩ := body.run
  have hRunBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn argValues (bodyFuel + 1) zeroPrepared.finalTarget =
        .ok
          (Functions.Source.Effectful.CallResult.halted
            body.kind body.finalTarget) := by
    apply
      Functions.Source.Effectful.FunDef.runBody_halted_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hParams
    simpa [zeroPrepared, targetAfterArgs] using hBodyRun
  have hCallStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program zeroPrepared.finalCtx (bodyFuel + 2)
          (.call [tmp] functionName lowerArgs) zeroPrepared.finalTarget =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            body.kind body.finalTarget,
            zeroPrepared.finalCtx) := by
    apply
      Functions.Source.Effectful.Stmt.call_halted_of_parts
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program (by simp) hArgsEval hFind
    simpa [Nat.add_assoc] using hRunBody
  have hCallBlock :=
    Functions.Source.Effectful.Block.runOpen_singleton_of_run
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hCallStmt
  have hSuffixRun :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program
      [Functions.Stmt.let_ tmp (.lit Functions.Source.zero)]
      [Functions.Stmt.call [tmp] functionName lowerArgs]
      argsPrepared.prepared.prepared.finalCtx zeroPrepared.finalCtx
      targetAfterArgs zeroPrepared.finalTarget
      (Functions.Source.Effectful.Outcome.halt
        body.kind body.finalTarget)
      zeroPrepared.finalCtx zeroPrepared.run hCallBlock
  have hFullRun :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program preArgs
      [Functions.Stmt.let_ tmp (.lit Functions.Source.zero),
        Functions.Stmt.call [tmp] functionName lowerArgs]
      ctx argsPrepared.prepared.prepared.finalCtx target targetAfterArgs
      (Functions.Source.Effectful.Outcome.halt
        body.kind body.finalTarget)
      zeroPrepared.finalCtx
      argsPrepared.prepared.prepared.run
      (by simpa using hSuffixRun)
  exact
    ⟨body.kind, body.finalTarget, zeroPrepared.finalCtx,
      hFullRun, body.relation⟩

end FunctionsObserverCallTerminal
end Yul
end EvmCompiler
