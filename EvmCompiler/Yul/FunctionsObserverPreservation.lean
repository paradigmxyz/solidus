import EvmCompiler.Yul.FunctionsObserverCompiler
import EvmCompiler.Yul.FunctionsObserverExpression

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPreservation

/-!
Observer-aware preservation owned by the adjacent Yul-to-Functions pass.

The target semantics in every public statement is
`Functions.Source.Effectful`. Lower Locals, allocation, CFG, Assembly, and
bytecode details are deliberately absent from this boundary.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

export FunctionsObserverPrimitive
  (observerPrim gas msize safeObserverPrim gasSafe msizeSafe)

theorem lowerEvalGas
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat} {fresh : Fresh.State}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverSemantics.SourceReplay.evalValues fuel.succ.succ
          (.Call
            (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])
          codeOverride source =
        .ok (source', values)) :
    Expr.lower1Unchecked? fresh
        (.Call
          (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []) =
      some ([], (.prim .gas .nil : Functions.Expr 1), fresh) ∧
    ∃ target' : Functions.ObserverSemantics.State transcript,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .gas .nil : Functions.Expr 1) target =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' := by
  refine ⟨Expr.lower1Unchecked?_gas fresh, ?_⟩
  have hPrim :
      ObserverSemantics.SourceReplay.primCall fuel.succ source
          (.StackMemFlow .GAS) [] =
        .ok (source', values) := by
    simpa [ObserverSemantics.SourceReplay.evalValues,
      ObserverSemantics.SourceReplay.stateModel,
      ObserverSemantics.SourceReplay.primitiveSemantics,
      Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs] using hRun
  obtain ⟨target', hTarget, hTargetRel, _hStore⟩ := gas hRel hPrim
  refine ⟨target', ?_, hTargetRel⟩
  simpa [Functions.Source.Effectful.Expr.eval] using hTarget

theorem lowerEvalMsize
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat} {fresh : Fresh.State}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverSemantics.SourceReplay.evalValues fuel.succ.succ
          (.Call
            (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])
          codeOverride source =
        .ok (source', values)) :
    Expr.lower1Unchecked? fresh
        (.Call
          (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []) =
      some ([], (.prim .msize .nil : Functions.Expr 1), fresh) ∧
    ∃ target' : Functions.ObserverSemantics.State transcript,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          (.prim .msize .nil : Functions.Expr 1) target =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' := by
  refine ⟨Expr.lower1Unchecked?_msize fresh, ?_⟩
  have hPrim :
      ObserverSemantics.SourceReplay.primCall fuel.succ source
          (.StackMemFlow .MSIZE) [] =
        .ok (source', values) := by
    simpa [ObserverSemantics.SourceReplay.evalValues,
      ObserverSemantics.SourceReplay.stateModel,
      ObserverSemantics.SourceReplay.primitiveSemantics,
      Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs] using hRun
  obtain ⟨target', hTarget, hTargetRel, _hStore⟩ := msize hRel hPrim
  refine ⟨target', ?_, hTargetRel⟩
  simpa [Functions.Source.Effectful.Expr.eval] using hTarget

theorem lowerEvalGasSafe
    {contract : MemoryContract.Contract}
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat} {fresh : Fresh.State}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel.succ.succ
          (.Call
            (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])
          codeOverride source =
        .ok (source', values)) :
    Expr.lower1Unchecked? fresh
        (.Call
          (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []) =
      some ([], (.prim .gas .nil : Functions.Expr 1), fresh) ∧
    ∃ target' : Functions.ObserverSemantics.State transcript,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.prim .gas .nil : Functions.Expr 1) target =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' := by
  refine ⟨Expr.lower1Unchecked?_gas fresh, ?_⟩
  have hPrim :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .GAS) [] =
        .ok (source', values) := by
    simpa [Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs] using hRun
  obtain ⟨target', hTarget, hTargetRel, _hStore⟩ :=
    gasSafe hRel hPrim
  refine ⟨target', ?_, hTargetRel⟩
  simpa [Functions.Source.Effectful.Expr.eval] using hTarget

theorem lowerEvalMsizeSafe
    {contract : MemoryContract.Contract}
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat} {fresh : Fresh.State}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {values : List Word}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      Yul.Source.Effectful.evalValues
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          fuel.succ.succ
          (.Call
            (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])
          codeOverride source =
        .ok (source', values)) :
    Expr.lower1Unchecked? fresh
        (.Call
          (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []) =
      some ([], (.prim .msize .nil : Functions.Expr 1), fresh) ∧
    ∃ target' : Functions.ObserverSemantics.State transcript,
      Functions.Source.Effectful.Expr.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.prim .msize .nil : Functions.Expr 1) target =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' := by
  refine ⟨Expr.lower1Unchecked?_msize fresh, ?_⟩
  have hPrim :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source
          (.StackMemFlow .MSIZE) [] =
        .ok (source', values) := by
    simpa [Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs] using hRun
  obtain ⟨target', hTarget, hTargetRel, _hStore⟩ :=
    msizeSafe hRel hPrim
  refine ⟨target', ?_, hTargetRel⟩
  simpa [Functions.Source.Effectful.Expr.eval] using hTarget

private theorem lowerExecLetObserver
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    (lowerFuel yulFuel targetFuel : Nat) (fresh : Fresh.State)
    (targetProgram : Functions.Program) (ctx : Functions.Source.Ctx)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (name : EvmYul.Identifier) (value : Word)
    (kind : Assembly.ResourceObserver) (targetExpr : Functions.Expr 1)
    (prim : EvmYul.Operation .Yul)
    (hYulObserver : ObserverSemantics.yulPrimObserver? prim = some kind)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? lowerFuel.succ fresh
          (.Let [name] (some (.Call (.inl prim) []))) =
        some
          ([Functions.Stmt.let_ (identName name)
            targetExpr], fresh))
    (hTargetRun :
      ∀ {targetObserved : Functions.ObserverSemantics.State transcript},
        Simulation.ResourceReplay.consume? kind target =
            some (value, targetObserved) →
          Functions.Source.Effectful.Stmt.run
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSemantics.primitiveSemantics transcript)
              targetProgram ctx targetFuel
              (.let_ (identName name) targetExpr) target =
            .ok
              (Functions.Source.Effectful.Outcome.regular
                (targetObserved.withSource
                  (targetObserved.source.insert (identName name) value)),
                { ctx with scope := identName name :: ctx.scope }))
    (hDecl :
      EvmYul.Yul.checkDeclaration source.source [name] = .ok ())
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hConsume :
      Simulation.ResourceReplay.consume? kind source =
        some (value, { source with cursor := source.cursor + 1 })) :
    ∃ sourceAfter targetAfter,
      ObserverSemantics.SourceReplay.exec yulFuel.succ.succ.succ
          (.Let [name] (some (.Call (.inl prim) [])))
          codeOverride source =
        .ok sourceAfter ∧
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          targetProgram ctx targetFuel
          (.let_ (identName name) targetExpr)
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfter,
            { ctx with scope := identName name :: ctx.scope }) ∧
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
  obtain ⟨targetObserved, hTargetConsume, hCursor, hSourceRel⟩ :=
    Simulation.ResourceReplay.consume?_rel
      hRel.1 hRel.2 hConsume
  let sourceObserved : ObserverSemantics.SourceReplay.State transcript :=
    { source with cursor := source.cursor + 1 }
  let sourceAfter :=
    sourceObserved.withSource
      (sourceObserved.source.multifill [name] [value])
  let targetAfter :=
    targetObserved.withSource
      (targetObserved.source.insert (identName name) value)
  have hObservedRel :
      StateRelation.Replay.Rel codeRel sourceObserved targetObserved :=
    ⟨hCursor, hSourceRel⟩
  have hAfterRel :
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter :=
    StateRelation.Replay.multifill_single hObservedRel name value
  refine ⟨sourceAfter, targetAfter, ?_, ?_, hAfterRel⟩
  · simp [ObserverSemantics.SourceReplay.exec,
      ObserverSemantics.SourceReplay.evalValues,
      ObserverSemantics.SourceReplay.primitiveSemantics,
      ObserverSemantics.SourceReplay.stateModel,
      ObserverSemantics.SourceReplay.primCall,
      Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
      Yul.Source.Effectful.StateModel.multifill,
      ObserverSemantics.SourceReplay.State.withSource,
      Simulation.ResourceReplay.State.withSource,
      hDecl, hYulObserver, hConsume, sourceObserved, sourceAfter]
  · simpa [targetAfter] using
      (hTargetRun hTargetConsume)

theorem lowerExecLetGas
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    (lowerFuel yulFuel targetFuel : Nat) (fresh : Fresh.State)
    (targetProgram : Functions.Program) (ctx : Functions.Source.Ctx)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (name : EvmYul.Identifier) (value : Word)
    (hDecl :
      EvmYul.Yul.checkDeclaration source.source [name] = .ok ())
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .gas source =
        some (value, { source with cursor := source.cursor + 1 })) :
    Stmt.toFunctionsListUncheckedFuel? lowerFuel.succ fresh
        (.Let [name]
          (some
            (.Call
              (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []))) =
      some
        ([Functions.Stmt.let_ (identName name)
          (.prim .gas .nil : Functions.Expr 1)], fresh) ∧
    ∃ sourceAfter targetAfter,
      ObserverSemantics.SourceReplay.exec yulFuel.succ.succ.succ
          (.Let [name]
            (some
              (.Call
                (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])))
          codeOverride source =
        .ok sourceAfter ∧
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          targetProgram ctx targetFuel
          (.let_ (identName name) (.prim .gas .nil : Functions.Expr 1))
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfter,
            { ctx with scope := identName name :: ctx.scope }) ∧
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
  have hLower :=
    Stmt.toFunctionsListUncheckedFuel?_let_gas lowerFuel fresh name
  exact
    ⟨hLower,
      lowerExecLetObserver lowerFuel yulFuel targetFuel fresh targetProgram ctx
        codeOverride name value .gas
        (.prim .gas .nil : Functions.Expr 1)
        (.StackMemFlow .GAS) ObserverSemantics.yulPrimObserver?_gas
        hLower
        (fun hTargetConsume =>
          Functions.ObserverSemantics.stmt_run_let_gas
            targetProgram ctx targetFuel (identName name) hTargetConsume)
        hDecl hRel hConsume⟩

theorem lowerExecLetMsize
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    (lowerFuel yulFuel targetFuel : Nat) (fresh : Fresh.State)
    (targetProgram : Functions.Program) (ctx : Functions.Source.Ctx)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (name : EvmYul.Identifier) (value : Word)
    (hDecl :
      EvmYul.Yul.checkDeclaration source.source [name] = .ok ())
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .msize source =
        some (value, { source with cursor := source.cursor + 1 })) :
    Stmt.toFunctionsListUncheckedFuel? lowerFuel.succ fresh
        (.Let [name]
          (some
            (.Call
              (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []))) =
      some
        ([Functions.Stmt.let_ (identName name)
          (.prim .msize .nil : Functions.Expr 1)], fresh) ∧
    ∃ sourceAfter targetAfter,
      ObserverSemantics.SourceReplay.exec yulFuel.succ.succ.succ
          (.Let [name]
            (some
              (.Call
                (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])))
          codeOverride source =
        .ok sourceAfter ∧
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          targetProgram ctx targetFuel
          (.let_ (identName name) (.prim .msize .nil : Functions.Expr 1))
          target =
        .ok
          (Functions.Source.Effectful.Outcome.regular targetAfter,
            { ctx with scope := identName name :: ctx.scope }) ∧
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
  have hLower :=
    Stmt.toFunctionsListUncheckedFuel?_let_msize lowerFuel fresh name
  exact
    ⟨hLower,
      lowerExecLetObserver lowerFuel yulFuel targetFuel fresh targetProgram ctx
        codeOverride name value .msize
        (.prim .msize .nil : Functions.Expr 1)
        (.StackMemFlow .MSIZE) ObserverSemantics.yulPrimObserver?_msize
        hLower
        (fun hTargetConsume =>
          Functions.ObserverSemantics.stmt_run_let_msize
            targetProgram ctx targetFuel (identName name) hTargetConsume)
        hDecl hRel hConsume⟩

end FunctionsObserverPreservation
end Yul
end EvmCompiler
