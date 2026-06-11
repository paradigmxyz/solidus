import EvmCompiler.Functions.ObserverSemantics
import EvmCompiler.Locals.ObserverSemantics
import EvmCompiler.Yul.Compiler
import EvmCompiler.Yul.ObserverOracle
import EvmCompiler.Yul.StateRelation

namespace EvmCompiler
namespace Yul
namespace ObserverPreservation

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

/--
One resource-observing Yul primitive step is simulated by the corresponding
Locals primitive step. The proof is independent of the particular relation
between the underlying source states; here it is instantiated with the
compiler's concrete Yul-to-Locals state relation.
-/
theorem observerPrim
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverOracle.SourceReplay.State transcript}
    {target : Locals.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {kind : Assembly.ResourceObserver} {values : List Word}
    (hYulObserver :
      ObserverOracle.yulPrimObserver? prim = some kind)
    (hLocalsObserver :
      Locals.ObserverSemantics.basicOpObserver? op = some kind)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverOracle.SourceReplay.primCall fuel.succ source prim [] =
        .ok (source', values)) :
    ∃ target' : Locals.ObserverSemantics.State transcript,
      (Locals.ObserverSemantics.primitiveSemantics transcript).eval
          op target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' := by
  unfold ObserverOracle.SourceReplay.primCall at hRun
  rw [hYulObserver] at hRun
  cases hConsume :
      Simulation.ResourceReplay.consume? kind source with
  | none =>
      simp [hConsume, Yul.Source.Effectful.fail] at hRun
  | some result =>
      rcases result with ⟨value, sourceAfter⟩
      simp [hConsume] at hRun
      rcases hRun with ⟨hSource, hValues⟩
      subst source'
      subst values
      obtain ⟨targetAfter, hTargetConsume, hCursor, hSourceRel⟩ :=
        Simulation.ResourceReplay.consume?_rel
          hRel.1 hRel.2 hConsume
      refine ⟨targetAfter, ?_, hCursor, hSourceRel⟩
      simp [Locals.ObserverSemantics.primitiveSemantics,
        hLocalsObserver, hTargetConsume]

theorem gas
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverOracle.SourceReplay.State transcript}
    {target : Locals.ObserverSemantics.State transcript}
    {values : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverOracle.SourceReplay.primCall fuel.succ source
          (.StackMemFlow .GAS) [] =
        .ok (source', values)) :
    ∃ target' : Locals.ObserverSemantics.State transcript,
      (Locals.ObserverSemantics.primitiveSemantics transcript).eval
          .gas target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' :=
  observerPrim ObserverOracle.yulPrimObserver?_gas
    (by rfl) hRel hRun

theorem msize
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverOracle.SourceReplay.State transcript}
    {target : Locals.ObserverSemantics.State transcript}
    {values : List Word}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverOracle.SourceReplay.primCall fuel.succ source
          (.StackMemFlow .MSIZE) [] =
        .ok (source', values)) :
    ∃ target' : Locals.ObserverSemantics.State transcript,
      (Locals.ObserverSemantics.primitiveSemantics transcript).eval
          .msize target [] =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' :=
  observerPrim ObserverOracle.yulPrimObserver?_msize
    (by rfl) hRel hRun

/--
The observer-aware Yul expression lowering and its semantic simulation are
checked together. This is the leaf contract used by statement and block
preservation, rather than a detached opcode-specific execution fact.
-/
theorem lowerEvalGas
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat} {fresh : Fresh.State}
    {source source' : ObserverOracle.SourceReplay.State transcript}
    {target : Locals.ObserverSemantics.State transcript}
    {values : List Word}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverOracle.SourceReplay.evalValues fuel.succ.succ
          (.Call
            (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])
          codeOverride source =
        .ok (source', values)) :
    Expr.lower1Unchecked? fresh
        (.Call
          (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []) =
      some ([], (.prim .gas .nil : Locals.Expr 1), fresh) ∧
    ∃ target' : Locals.ObserverSemantics.State transcript,
      Locals.Source.Effectful.Expr.eval
          (Locals.ObserverSemantics.stateModel transcript)
          (Locals.ObserverSemantics.primitiveSemantics transcript)
          (.prim .gas .nil : Locals.Expr 1) target =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' := by
  refine ⟨Expr.lower1Unchecked?_gas fresh, ?_⟩
  have hPrim :
      ObserverOracle.SourceReplay.primCall fuel.succ source
          (.StackMemFlow .GAS) [] =
        .ok (source', values) := by
    simpa [ObserverOracle.SourceReplay.evalValues,
      ObserverOracle.SourceReplay.stateModel,
      ObserverOracle.SourceReplay.primitiveSemantics,
      Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs] using hRun
  obtain ⟨target', hTarget, hTargetRel⟩ := gas hRel hPrim
  refine ⟨target', ?_, hTargetRel⟩
  simpa [Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval] using hTarget

theorem lowerEvalMsize
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    {fuel : Nat} {fresh : Fresh.State}
    {source source' : ObserverOracle.SourceReplay.State transcript}
    {target : Locals.ObserverSemantics.State transcript}
    {values : List Word}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      ObserverOracle.SourceReplay.evalValues fuel.succ.succ
          (.Call
            (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])
          codeOverride source =
        .ok (source', values)) :
    Expr.lower1Unchecked? fresh
        (.Call
          (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []) =
      some ([], (.prim .msize .nil : Locals.Expr 1), fresh) ∧
    ∃ target' : Locals.ObserverSemantics.State transcript,
      Locals.Source.Effectful.Expr.eval
          (Locals.ObserverSemantics.stateModel transcript)
          (Locals.ObserverSemantics.primitiveSemantics transcript)
          (.prim .msize .nil : Locals.Expr 1) target =
        .ok (target', values) ∧
      StateRelation.Replay.Rel codeRel source' target' := by
  refine ⟨Expr.lower1Unchecked?_msize fresh, ?_⟩
  have hPrim :
      ObserverOracle.SourceReplay.primCall fuel.succ source
          (.StackMemFlow .MSIZE) [] =
        .ok (source', values) := by
    simpa [ObserverOracle.SourceReplay.evalValues,
      ObserverOracle.SourceReplay.stateModel,
      ObserverOracle.SourceReplay.primitiveSemantics,
      Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs] using hRun
  obtain ⟨target', hTarget, hTargetRel⟩ := msize hRel hPrim
  refine ⟨target', ?_, hTargetRel⟩
  simpa [Locals.Source.Effectful.Expr.eval,
    Locals.Source.Effectful.Expr.ExprSeq.eval] using hTarget

theorem lowerExecLetGas
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    (lowerFuel yulFuel targetFuel : Nat) (fresh : Fresh.State)
    (targetProgram : Locals.Program) (ctx : Locals.Source.Ctx)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {source : ObserverOracle.SourceReplay.State transcript}
    {target : Locals.ObserverSemantics.State transcript}
    (name : EvmYul.Identifier) (value : Word)
    (hDecl :
      EvmYul.Yul.checkDeclaration source.source [name] = .ok ())
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .gas source =
        some (value,
          { source with cursor := source.cursor + 1 })) :
    Stmt.toFunctionsListUncheckedFuel? lowerFuel.succ fresh
        (.Let [name]
          (some
            (.Call
              (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []))) =
      some
        ([Functions.Stmt.let_ (identName name)
          (.prim .gas .nil : Locals.Expr 1)], fresh) ∧
    ∃ sourceAfter targetAfter,
      ObserverOracle.SourceReplay.exec yulFuel.succ.succ.succ
          (.Let [name]
            (some
              (.Call
                (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])))
          codeOverride source =
        .ok sourceAfter ∧
      Locals.Source.Effectful.Stmt.run
          (Locals.ObserverSemantics.stateModel transcript)
          (Locals.ObserverSemantics.primitiveSemantics transcript)
          targetProgram ctx targetFuel
          (.let_ (identName name) (.prim .gas .nil : Locals.Expr 1))
          target =
        .ok
          (Locals.Source.Effectful.Outcome.regular targetAfter,
            { ctx with scope := identName name :: ctx.scope }) ∧
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
  refine
    ⟨Stmt.toFunctionsListUncheckedFuel?_let_gas lowerFuel fresh name, ?_⟩
  obtain ⟨targetObserved, hTargetConsume, hCursor, hSourceRel⟩ :=
    Simulation.ResourceReplay.consume?_rel
      hRel.1 hRel.2 hConsume
  let sourceObserved : ObserverOracle.SourceReplay.State transcript :=
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
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
    exact StateRelation.Replay.multifill_single hObservedRel name value
  refine ⟨sourceAfter, targetAfter, ?_, ?_, hAfterRel⟩
  · simp [ObserverOracle.SourceReplay.exec,
      ObserverOracle.SourceReplay.evalValues,
      ObserverOracle.SourceReplay.primitiveSemantics,
      ObserverOracle.SourceReplay.stateModel,
      ObserverOracle.SourceReplay.primCall,
      Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
      Yul.Source.Effectful.StateModel.multifill,
      ObserverOracle.SourceReplay.State.withSource,
      Simulation.ResourceReplay.State.withSource,
      hDecl, hConsume, sourceObserved, sourceAfter]
  · simp [Locals.Source.Effectful.Stmt.run,
      Locals.Source.Effectful.Expr.evalOne,
      Locals.Source.Effectful.Expr.eval,
      Locals.Source.Effectful.Expr.ExprSeq.eval,
      Locals.ObserverSemantics.primitiveSemantics,
      Locals.ObserverSemantics.basicOpObserver?,
      Locals.Source.Effectful.StateModel.insert,
      Locals.ObserverSemantics.stateModel,
      Simulation.ResourceReplay.State.withSource,
      hTargetConsume, targetAfter]

theorem lowerExecLetMsize
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    (lowerFuel yulFuel targetFuel : Nat) (fresh : Fresh.State)
    (targetProgram : Locals.Program) (ctx : Locals.Source.Ctx)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {source : ObserverOracle.SourceReplay.State transcript}
    {target : Locals.ObserverSemantics.State transcript}
    (name : EvmYul.Identifier) (value : Word)
    (hDecl :
      EvmYul.Yul.checkDeclaration source.source [name] = .ok ())
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .msize source =
        some (value,
          { source with cursor := source.cursor + 1 })) :
    Stmt.toFunctionsListUncheckedFuel? lowerFuel.succ fresh
        (.Let [name]
          (some
            (.Call
              (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []))) =
      some
        ([Functions.Stmt.let_ (identName name)
          (.prim .msize .nil : Locals.Expr 1)], fresh) ∧
    ∃ sourceAfter targetAfter,
      ObserverOracle.SourceReplay.exec yulFuel.succ.succ.succ
          (.Let [name]
            (some
              (.Call
                (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])))
          codeOverride source =
        .ok sourceAfter ∧
      Locals.Source.Effectful.Stmt.run
          (Locals.ObserverSemantics.stateModel transcript)
          (Locals.ObserverSemantics.primitiveSemantics transcript)
          targetProgram ctx targetFuel
          (.let_ (identName name) (.prim .msize .nil : Locals.Expr 1))
          target =
        .ok
          (Locals.Source.Effectful.Outcome.regular targetAfter,
            { ctx with scope := identName name :: ctx.scope }) ∧
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
  refine
    ⟨Stmt.toFunctionsListUncheckedFuel?_let_msize lowerFuel fresh name, ?_⟩
  obtain ⟨targetObserved, hTargetConsume, hCursor, hSourceRel⟩ :=
    Simulation.ResourceReplay.consume?_rel
      hRel.1 hRel.2 hConsume
  let sourceObserved : ObserverOracle.SourceReplay.State transcript :=
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
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
    exact StateRelation.Replay.multifill_single hObservedRel name value
  refine ⟨sourceAfter, targetAfter, ?_, ?_, hAfterRel⟩
  · simp [ObserverOracle.SourceReplay.exec,
      ObserverOracle.SourceReplay.evalValues,
      ObserverOracle.SourceReplay.primitiveSemantics,
      ObserverOracle.SourceReplay.stateModel,
      ObserverOracle.SourceReplay.primCall,
      Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
      Yul.Source.Effectful.StateModel.multifill,
      ObserverOracle.SourceReplay.State.withSource,
      Simulation.ResourceReplay.State.withSource,
      hDecl, hConsume, sourceObserved, sourceAfter]
  · simp [Locals.Source.Effectful.Stmt.run,
      Locals.Source.Effectful.Expr.evalOne,
      Locals.Source.Effectful.Expr.eval,
      Locals.Source.Effectful.Expr.ExprSeq.eval,
      Locals.ObserverSemantics.primitiveSemantics,
      Locals.ObserverSemantics.basicOpObserver?,
      Locals.Source.Effectful.StateModel.insert,
      Locals.ObserverSemantics.stateModel,
      Simulation.ResourceReplay.State.withSource,
      hTargetConsume, targetAfter]

theorem lowerExecLetGasFunctions
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    (lowerFuel yulFuel targetFuel : Nat) (fresh : Fresh.State)
    (targetProgram : Functions.Program) (ctx : Functions.Source.Ctx)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {source : ObserverOracle.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (name : EvmYul.Identifier) (value : Word)
    (hDecl :
      EvmYul.Yul.checkDeclaration source.source [name] = .ok ())
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .gas source =
        some (value,
          { source with cursor := source.cursor + 1 })) :
    Stmt.toFunctionsListUncheckedFuel? lowerFuel.succ fresh
        (.Let [name]
          (some
            (.Call
              (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []))) =
      some
        ([Functions.Stmt.let_ (identName name)
          (.prim .gas .nil : Functions.Expr 1)], fresh) ∧
    ∃ sourceAfter targetAfter,
      ObserverOracle.SourceReplay.exec yulFuel.succ.succ.succ
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
  refine
    ⟨Stmt.toFunctionsListUncheckedFuel?_let_gas lowerFuel fresh name, ?_⟩
  obtain ⟨targetObserved, hTargetConsume, hCursor, hSourceRel⟩ :=
    Simulation.ResourceReplay.consume?_rel
      hRel.1 hRel.2 hConsume
  let sourceObserved : ObserverOracle.SourceReplay.State transcript :=
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
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
    exact StateRelation.Replay.multifill_single hObservedRel name value
  refine ⟨sourceAfter, targetAfter, ?_, ?_, hAfterRel⟩
  · simp [ObserverOracle.SourceReplay.exec,
      ObserverOracle.SourceReplay.evalValues,
      ObserverOracle.SourceReplay.primitiveSemantics,
      ObserverOracle.SourceReplay.stateModel,
      ObserverOracle.SourceReplay.primCall,
      Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
      Yul.Source.Effectful.StateModel.multifill,
      ObserverOracle.SourceReplay.State.withSource,
      Simulation.ResourceReplay.State.withSource,
      hDecl, hConsume, sourceObserved, sourceAfter]
  · simp [Functions.Source.Effectful.Stmt.run,
      Functions.Source.Effectful.Expr.evalOne,
      Functions.Source.Effectful.Expr.eval,
      Locals.Source.Effectful.Expr.evalOne,
      Locals.Source.Effectful.Expr.eval,
      Locals.Source.Effectful.Expr.ExprSeq.eval,
      Functions.ObserverSemantics.primitiveSemantics,
      Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.primitiveSemantics,
      Locals.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.basicOpObserver?,
      Structured.BasicOp.toPrimOp,
      Assembly.ResourceObserver.ofPrimOp?,
      Functions.Source.Effectful.Outcome.regular,
      Locals.Source.Effectful.Outcome.regular,
      Locals.Source.Effectful.StateModel.insert,
      Locals.Source.State.insert,
      Simulation.ResourceReplay.State.withSource,
      hTargetConsume, targetAfter]

theorem lowerExecLetMsizeFunctions
    {transcript : Trace} {codeRel : StateRelation.CodeRel}
    (lowerFuel yulFuel targetFuel : Nat) (fresh : Fresh.State)
    (targetProgram : Functions.Program) (ctx : Functions.Source.Ctx)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    {source : ObserverOracle.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    (name : EvmYul.Identifier) (value : Word)
    (hDecl :
      EvmYul.Yul.checkDeclaration source.source [name] = .ok ())
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hConsume :
      Simulation.ResourceReplay.consume? .msize source =
        some (value,
          { source with cursor := source.cursor + 1 })) :
    Stmt.toFunctionsListUncheckedFuel? lowerFuel.succ fresh
        (.Let [name]
          (some
            (.Call
              (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []))) =
      some
        ([Functions.Stmt.let_ (identName name)
          (.prim .msize .nil : Functions.Expr 1)], fresh) ∧
    ∃ sourceAfter targetAfter,
      ObserverOracle.SourceReplay.exec yulFuel.succ.succ.succ
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
  refine
    ⟨Stmt.toFunctionsListUncheckedFuel?_let_msize lowerFuel fresh name, ?_⟩
  obtain ⟨targetObserved, hTargetConsume, hCursor, hSourceRel⟩ :=
    Simulation.ResourceReplay.consume?_rel
      hRel.1 hRel.2 hConsume
  let sourceObserved : ObserverOracle.SourceReplay.State transcript :=
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
      StateRelation.Replay.Rel codeRel sourceAfter targetAfter := by
    exact StateRelation.Replay.multifill_single hObservedRel name value
  refine ⟨sourceAfter, targetAfter, ?_, ?_, hAfterRel⟩
  · simp [ObserverOracle.SourceReplay.exec,
      ObserverOracle.SourceReplay.evalValues,
      ObserverOracle.SourceReplay.primitiveSemantics,
      ObserverOracle.SourceReplay.stateModel,
      ObserverOracle.SourceReplay.primCall,
      Yul.Source.Effectful.exec, Yul.Source.Effectful.evalValues,
      Yul.Source.Effectful.evalArgs, Yul.Source.Effectful.multifill,
      Yul.Source.Effectful.StateModel.multifill,
      ObserverOracle.SourceReplay.State.withSource,
      Simulation.ResourceReplay.State.withSource,
      hDecl, hConsume, sourceObserved, sourceAfter]
  · simp [Functions.Source.Effectful.Stmt.run,
      Functions.Source.Effectful.Expr.evalOne,
      Functions.Source.Effectful.Expr.eval,
      Locals.Source.Effectful.Expr.evalOne,
      Locals.Source.Effectful.Expr.eval,
      Locals.Source.Effectful.Expr.ExprSeq.eval,
      Functions.ObserverSemantics.primitiveSemantics,
      Functions.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.primitiveSemantics,
      Locals.ObserverSemantics.stateModel,
      Locals.ObserverSemantics.basicOpObserver?,
      Structured.BasicOp.toPrimOp,
      Assembly.ResourceObserver.ofPrimOp?,
      Functions.Source.Effectful.Outcome.regular,
      Locals.Source.Effectful.Outcome.regular,
      Locals.Source.Effectful.StateModel.insert,
      Locals.Source.State.insert,
      Simulation.ResourceReplay.State.withSource,
      hTargetConsume, targetAfter]

end ObserverPreservation
end Yul
end EvmCompiler
