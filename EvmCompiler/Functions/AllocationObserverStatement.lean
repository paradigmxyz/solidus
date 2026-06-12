import EvmCompiler.Functions.AllocationObserverPrimitive
import EvmCompiler.Functions.AllocationObserverTerminal

namespace EvmCompiler
namespace Functions
namespace AllocationObserverStatement

open AllocationObserverRelation

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

namespace ExprLeaf

/--
Successful execution of the real statement lowerer and Locals block compiler
for an expression statement exposes exactly one Structured code statement.
-/
theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ lowered code,
      AllocationLowering.lowerExpr lowerCtx lowerState expr = some lowered ∧
      Locals.Expr.compileCode localsCtx 0 lowered = some code ∧
      loweredStmts = [.expr lowered] ∧
      lowerFinal = lowerState ∧
      compiledStmts = [Expressions.Stmt.code code] ∧
      localsFinal = localsCtx := by
  cases hLowerExpr :
      AllocationLowering.lowerExpr lowerCtx lowerState expr with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
  | some lowered =>
      simp [AllocationLowering.lowerStmt, hLowerExpr] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      cases hCode :
          Locals.Expr.compileCode localsCtx 0 lowered with
      | none =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile, hCode] at hCompile
      | some code =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile,
            Locals.codeStmt, hCode] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact ⟨lowered, code, rfl, hCode, rfl, rfl, rfl, rfl⟩

/--
Forward preservation for a Functions expression statement through the actual
allocation expression lowerer and Locals expression compiler.

The statement introduces no new local, so the same allocation context and live
set relate the regular outcomes.
-/
theorem forward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {lowered : Locals.Expr 0} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel (.expr expr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx) ∧
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram targetFuel (.code code) target
          (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      ActivationOutcomeRel contract plan live stackOffset frameBase mode
        (Functions.Source.Effectful.Outcome.regular sourceFinal)
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  obtain ⟨targetFinal, hTargetRun, hResultRel⟩ :=
    AllocationObserverExpression.forwardExpr
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hSafe hCtx hScoped hLower hCompile hRel
  have hSourceRun :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.expr
      (program := sourceProgram) (ctx := sourceCtx) (fuel := sourceFuel)
      hSafe).run_eq
  exact
    ⟨targetFinal, hSourceRun,
      Structured.EffectSemantics.Stmt.Eval.code hTargetRun,
      ActivationOutcomeRel.regular (by simpa using hResultRel.state)⟩

/--
Backward adequacy for a compiled expression statement.

Determinism of the canonical Structured code runner identifies the target
state constructed by the forward theorem, yielding the same source statement
run and outcome relation.
-/
theorem backward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {stackOffset frameBase : Nat}
    {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {lowered : Locals.Expr 0} {code : Structured.Code}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerExpr lowerCtx lowerState expr =
        some lowered)
    (hCompile :
      Locals.Expr.compileCode localsCtx stackOffset lowered = some code)
    (hRel :
      ActivationStateRel contract plan live
        stackOffset frameBase mode source target)
    (hTarget :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram targetFuel (.code code) target
          (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx sourceFuel (.expr expr) source =
      .ok
        (Functions.Source.Effectful.Outcome.regular sourceFinal,
          sourceCtx) ∧
    ActivationOutcomeRel contract plan live stackOffset frameBase mode
      (Functions.Source.Effectful.Outcome.regular sourceFinal)
      (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  cases hTarget with
  | code hTargetRun =>
      obtain ⟨_hSourceEval, hResultRel⟩ :=
        AllocationObserverExpression.Expr.backward_of_safeEval
          (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
            contract)
          hCtx hSafe hScoped hLower hCompile hRel hTargetRun
      have hSourceRun :=
        (AllocationObserverSafety.Stmt.LeafMemorySafeRun.expr
          (program := sourceProgram) (ctx := sourceCtx) (fuel := sourceFuel)
          hSafe).run_eq
      exact
        ⟨hSourceRun,
          ActivationOutcomeRel.regular (by simpa using hResultRel.state)⟩

/--
Forward preservation stated over the actual expanded statement block produced
by `lowerStmt` followed by `Locals.Block.compileOpen`.
-/
theorem forward_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live
        0 frameBase mode source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel (.expr expr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      ActivationOutcomeRel contract plan live 0 frameBase mode
        (Functions.Source.Effectful.Outcome.regular sourceFinal)
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  obtain
      ⟨lowered, code, hLowerExpr, hCompileCode,
        rfl, rfl, rfl, rfl⟩ :=
    compiler_shape hLower hCompile
  obtain ⟨targetFinal, hSourceRun, hTargetStmt, hOutcome⟩ :=
    forward
      (targetFuel := targetFuel + 1)
      hSafe hCtx hScoped hLowerExpr hCompileCode hRel
  refine ⟨targetFinal, hSourceRun, ?_, hOutcome⟩
  simpa [Expressions.StmtList.toStructured, Expressions.Stmt.toStructured] using
    (Structured.EffectSemantics.Block.Eval.cons_regular
      hTargetStmt Structured.EffectSemantics.Block.Eval.nil)

/--
Backward adequacy over the real expanded statement block.
-/
theorem backward_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live
        0 frameBase mode source target)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx sourceFuel (.expr expr) source =
      .ok
        (Functions.Source.Effectful.Outcome.regular sourceFinal,
          sourceCtx) ∧
    ActivationOutcomeRel contract plan live 0 frameBase mode
      (Functions.Source.Effectful.Outcome.regular sourceFinal)
      (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  obtain
      ⟨lowered, code, hLowerExpr, hCompileCode,
        rfl, rfl, rfl, rfl⟩ :=
    compiler_shape hLower hCompile
  simp only [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] at hTarget
  cases hTarget with
  | cons_regular hTargetStmt hTail =>
      cases hTail
      exact
        backward hSafe hCtx hScoped hLowerExpr hCompileCode hRel hTargetStmt

end ExprLeaf

namespace LetLeaf

/--
The regular result of a singleton code block is unique because its statement
semantics is exactly the executable Structured code runner.
-/
theorem singleton_code_regular_unique
    {transcript : Trace}
    {program : Structured.Program} {fuel : Nat}
    {code : Structured.Code}
    {initial left right : Structured.ObserverSemantics.State transcript}
    (hLeft :
      Structured.ObserverSemantics.Block.Eval
        program (fuel + 2) { stmts := [.code code] }
        initial (Structured.EffectSemantics.Outcome.regular left))
    (hRight :
      Structured.ObserverSemantics.Block.Eval
        program (fuel + 2) { stmts := [.code code] }
        initial (Structured.EffectSemantics.Outcome.regular right)) :
    left = right := by
  cases hLeft with
  | cons_regular hLeftStmt hLeftTail =>
      cases hLeftTail
      cases hLeftStmt with
      | code hLeftRun =>
          cases hRight with
          | cons_regular hRightStmt hRightTail =>
              cases hRightTail
              cases hRightStmt with
              | code hRightRun =>
                  rw [hLeftRun] at hRightRun
                  cases hRightRun
                  rfl

/--
Runtime-representation transition induced by declaring one allocated local.

A stack declaration adds one visible stack local and therefore shifts a
scratch frame pointer when present. A scratch declaration keeps the activation
mode unchanged. The relation mentions only the canonical allocation plan, not
emitted code.
-/
inductive ModeTransition
    (plan : Locals.Allocation.Plan) (name : Locals.Name) :
    ActivationMode → ActivationMode → Prop where
  | stack
      {before : ActivationMode} (planDepth : Nat)
      (hLocation : plan.location? name = some (.stack planDepth)) :
      ModeTransition plan name before before.afterStackDeclaration
  | scratch
      (frameDepth frameWords slot : Nat)
      (hLocation : plan.location? name = some (.scratch slot)) :
      ModeTransition plan name
        (.scratch frameDepth frameWords)
        (.scratch frameDepth frameWords)

/--
Exact compiler shape for one declaration, classified by the placement chosen
by the checked allocation plan.
-/
inductive CompilerShape
    (lowerCtx : AllocationLowering.Ctx)
    (beforeState afterState : AllocationLowering.State)
    (beforeLocals afterLocals : Locals.Ctx)
    (plan : Locals.Allocation.Plan)
    (beforeLive afterLive : List Locals.Name)
    (beforeFrameDepth afterFrameDepth : Nat)
    (name : Locals.Name) (value : Functions.Expr 1)
    (loweredStmts : List Locals.Stmt)
    (compiledStmts : List Expressions.Stmt) : Prop where
  | stack
      (slot planDepth : Nat)
      (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code)
      (hLowerValue :
        AllocationLowering.lowerExpr lowerCtx beforeState value =
          some loweredValue)
      (hCompileValue :
        Locals.Expr.compileCode beforeLocals 0 loweredValue =
          some valueCode)
      (hLocation :
        plan.location? name = some (.stack planDepth))
      (hStackOrder :
        currentStackOrder plan afterLive =
          name :: currentStackOrder plan beforeLive)
      (hFrameDepth : afterFrameDepth = beforeFrameDepth + 1)
      (hLowered :
        loweredStmts = [.let_ name loweredValue])
      (hAfterState :
        afterState =
          { allocation :=
              (AllocationSupport.allocateName
                name beforeState.allocation).2
            layout := name :: beforeState.layout })
      (hCompiled :
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              Locals.bindLocals 0 (name :: beforeLocals.layout))])
      (hAfterLocals :
        afterLocals =
          beforeLocals.withLayout (name :: beforeLocals.layout)) :
      CompilerShape lowerCtx beforeState afterState
        beforeLocals afterLocals plan beforeLive afterLive
        beforeFrameDepth afterFrameDepth name value
        loweredStmts compiledStmts
  | scratch
      (slot : Nat) (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code) (op : Structured.BasicOp)
      (hLowerValue :
        AllocationLowering.lowerExpr lowerCtx beforeState value =
          some loweredValue)
      (hCompileValue :
        Locals.Expr.compileCode beforeLocals 0 loweredValue =
          some valueCode)
      (hLocation :
        plan.location? name = some (.scratch slot))
      (hDup :
        Locals.StackOp.dup? (beforeFrameDepth + 2) = some op)
      (hStackOrder :
        currentStackOrder plan afterLive =
          currentStackOrder plan beforeLive)
      (hFrameDepth : afterFrameDepth = beforeFrameDepth)
      (hLowered :
        loweredStmts =
          [.expr
            (AllocationLowering.scratchStoreExpr
              lowerCtx.frameName slot loweredValue)])
      (hAfterState :
        afterState =
          { beforeState with
            allocation :=
              (AllocationSupport.allocateName
                name beforeState.allocation).2 })
      (hCompiled :
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              [ .op op,
                .push (AllocationSupport.slotOffset slot),
                .op .add,
                .op .mstore ])])
      (hAfterLocals : afterLocals = beforeLocals) :
      CompilerShape lowerCtx beforeState afterState
        beforeLocals afterLocals plan beforeLive afterLive
        beforeFrameDepth afterFrameDepth name value
        loweredStmts compiledStmts

theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {beforeFrameDepth afterFrameDepth : Nat}
    {name : Locals.Name} {value : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hBefore :
      AllocationObserverContext.ExprContext
        lowerCtx beforeState beforeLocals plan beforeLive
          beforeFrameDepth)
    (hAfter :
      AllocationObserverContext.ExprContext
        lowerCtx afterState afterLocals plan afterLive
          afterFrameDepth)
    (hNameAfter : name ∈ afterLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name value) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals)) :
    CompilerShape lowerCtx beforeState afterState
      beforeLocals afterLocals plan beforeLive afterLive
      beforeFrameDepth afterFrameDepth name value
      loweredStmts compiledStmts := by
  have hTransition :=
    AllocationObserverContext.classify_let_transition
      hBefore hAfter hNameAfter hNameFrame hLower
  cases hTransition with
  | stack slot planDepth hSlot hStack hLocation hStackOrder hFrameDepth =>
      subst slot
      cases hLowerValue :
          AllocationLowering.lowerExpr lowerCtx beforeState value with
      | none =>
          simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
      | some loweredValue =>
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          cases hValueCode :
              Locals.Expr.compileCode beforeLocals 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hValueCode] at hCompile
          | some valueCode =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.codeStmt, hValueCode] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              exact
                .stack beforeState.allocation.nextSlot planDepth
                  loweredValue valueCode
                  hLowerValue hValueCode hLocation hStackOrder
                  hFrameDepth rfl rfl rfl rfl
  | scratch slot hSlot hStack hLocation hStackOrder hFrameDepth =>
      subst slot
      cases hLowerValue :
          AllocationLowering.lowerExpr lowerCtx beforeState value with
      | none =>
          simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
      | some loweredValue =>
          have hFrameMember :
              lowerCtx.frameName ∈ beforeState.layout := by
            exact Locals.Layout.mem_of_lookupDepth?_eq_some hBefore.frame
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack,
            hFrameMember] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          cases hValueCode :
              Locals.Expr.compileCode beforeLocals 0 loweredValue with
          | none =>
              have hFrameLocals :
                  Locals.Layout.lookupDepth?
                      lowerCtx.frameName beforeLocals.layout =
                    some (beforeFrameDepth + 1) := by
                rw [hBefore.layout]
                exact hBefore.frame
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                AllocationLowering.scratchStoreExpr,
                AllocationLowering.scratchAddressExpr,
                AllocationLowering.exprSeqTwo,
                Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                hValueCode, hFrameLocals] at hCompile
          | some valueCode =>
              have hFrameLocals :
                  Locals.Layout.lookupDepth?
                      lowerCtx.frameName beforeLocals.layout =
                    some (beforeFrameDepth + 1) := by
                rw [hBefore.layout]
                exact hBefore.frame
              cases hDup :
                  Locals.StackOp.dup? (beforeFrameDepth + 2) with
              | none =>
                  have hDup' :
                      Locals.StackOp.dup?
                          (1 + (beforeFrameDepth + 1)) =
                        none := by
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hDup
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    AllocationLowering.scratchStoreExpr,
                    AllocationLowering.scratchAddressExpr,
                    AllocationLowering.exprSeqTwo,
                    Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                    hValueCode, hFrameLocals, hDup',
                    Nat.add_assoc] at hCompile
              | some op =>
                  have hDup' :
                      Locals.StackOp.dup?
                          (1 + (beforeFrameDepth + 1)) =
                        some op := by
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hDup
                  have hStoreCode :=
                    AllocationLowering.scratchStoreExpr_compileCode
                      (frameName := lowerCtx.frameName)
                      (slot := beforeState.allocation.nextSlot)
                      (offset := 0) hValueCode hFrameLocals
                      hDup'
                  simp only [Locals.Block.compileOpen,
                    Locals.Stmt.compile] at hCompile
                  rw [hStoreCode] at hCompile
                  simp [Locals.codeStmt] at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  exact
                    .scratch beforeState.allocation.nextSlot
                      loweredValue valueCode op
                      hLowerValue hValueCode hLocation hDup
                      hStackOrder hFrameDepth rfl rfl rfl rfl

/--
Exact declaration compiler shape for a genuinely stack-only activation.
-/
theorem stack_let_compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {name : Locals.Name} {value : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {planDepth : Nat}
    (hBefore :
      AllocationObserverContext.StackExprContext
        lowerCtx beforeState beforeLocals plan beforeLive)
    (hAfter :
      AllocationObserverContext.StackExprContext
        lowerCtx afterState afterLocals plan afterLive)
    (hAfterLive : afterLive = name :: beforeLive)
    (hLocation : plan.location? name = some (.stack planDepth))
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name value) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals)) :
    ∃ (slot : Nat) (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code),
      slot = beforeState.allocation.nextSlot ∧
      AllocationLowering.lowerExpr lowerCtx beforeState value =
        some loweredValue ∧
      Locals.Expr.compileCode beforeLocals 0 loweredValue =
        some valueCode ∧
      currentStackOrder plan afterLive =
        name :: currentStackOrder plan beforeLive ∧
      loweredStmts = [.let_ name loweredValue] ∧
      afterState =
        { allocation :=
            (AllocationSupport.allocateName
              name beforeState.allocation).2
          layout := name :: beforeState.layout } ∧
      compiledStmts =
        [Expressions.Stmt.code
          (valueCode ++
            Locals.bindLocals 0 (name :: beforeLocals.layout))] ∧
      afterLocals =
        beforeLocals.withLayout (name :: beforeLocals.layout) := by
  cases hLowerValue :
      AllocationLowering.lowerExpr lowerCtx beforeState value with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerValue] at hLower
  | some loweredValue =>
      let slot := beforeState.allocation.nextSlot
      cases hStack :
          AllocationLowering.isStackSlot lowerCtx slot with
      | false =>
          change
            AllocationLowering.isStackSlot lowerCtx
                beforeState.allocation.nextSlot =
              false at hStack
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack,
            hBefore.frameAbsent] at hLower
      | true =>
          change
            AllocationLowering.isStackSlot lowerCtx
                beforeState.allocation.nextSlot =
              true at hStack
          simp [AllocationLowering.lowerStmt, hLowerValue,
            AllocationSupport.allocateName, hStack] at hLower
          rcases hLower with ⟨hLowered, hAfterState⟩
          subst loweredStmts
          subst afterState
          have hStackOrder :
              currentStackOrder plan afterLive =
                name :: currentStackOrder plan beforeLive := by
            rw [hAfter.stackOrder, hBefore.stackOrder]
          cases hValueCode :
              Locals.Expr.compileCode beforeLocals 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hValueCode] at hCompile
          | some valueCode =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                Locals.codeStmt, hValueCode] at hCompile
              rcases hCompile with ⟨rfl, rfl⟩
              exact
                ⟨slot, loweredValue, valueCode, rfl, rfl, hValueCode,
                  hStackOrder, rfl, rfl, rfl, rfl⟩

/--
Forward preservation for a declaration through the real allocation lowerer
and Locals compiler.

Both placement cases share the canonical source evaluation. Stack placement
turns the produced value into the new top local; scratch placement stores it
in the current activation frame. The result retains the full scratch-frame
relation needed by the following statement.
-/
theorem forward_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {beforeFrameDepth afterFrameDepth frameBase frameWords : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hBefore :
      AllocationObserverContext.ExprContext
        lowerCtx beforeState beforeLocals plan beforeLive
          beforeFrameDepth)
    (hAfter :
      AllocationObserverContext.ExprContext
        lowerCtx afterState afterLocals plan afterLive
          afterFrameDepth)
    (hScoped : Functions.Scope.ExprScoped beforeLive valueExpr)
    (hAfterLive : afterLive = name :: beforeLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hWF : plan.WellFormed)
    (hScratchBound :
      ∀ slot,
        plan.location? name = some (.scratch slot) →
        slot < frameWords)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hRel :
      ScratchStateRel contract plan beforeLive 0 frameBase
        beforeFrameDepth frameWords source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel
          (.let_ name valueExpr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            ((Functions.ObserverSemantics.stateModel transcript).insert
              sourceAfterValue name value),
            { sourceCtx with scope := name :: sourceCtx.scope }) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      ScratchStateRel contract plan afterLive 0 frameBase
        afterFrameDepth frameWords
        ((Functions.ObserverSemantics.stateModel transcript).insert
          sourceAfterValue name value)
        targetFinal := by
  have hNameAfter : name ∈ afterLive := by
    simp [hAfterLive]
  have hShape :=
    compiler_shape hBefore hAfter hNameAfter hNameFrame hLower hCompile
  have hSourceRun :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.let_
      (program := sourceProgram) (ctx := sourceCtx) (fuel := sourceFuel)
      (name := name)
      hSafe).run_eq
  cases hShape with
  | stack slot planDepth loweredValue valueCode
      hLowerValue hCompileValue hLocation hStackOrder hFrameDepth
      hLowered hAfterState hCompiled hAfterLocals =>
      subst loweredStmts
      subst afterState
      subst compiledStmts
      subst afterLocals
      subst afterLive
      subst afterFrameDepth
      obtain ⟨targetAfterValue, hValueRun, hValueRel⟩ :=
        AllocationObserverExpression.forwardExpr
          (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
            contract)
          hSafe (.scratch hBefore) hScoped hLowerValue hCompileValue
          (.scratch hRel)
      have hValueScratch :
          ScratchStateRel contract plan beforeLive 1 frameBase
            beforeFrameDepth frameWords sourceAfterValue targetAfterValue := by
        cases hValueRel.state with
        | scratch state => simpa using state
      have hValueStack :
          targetAfterValue.source.evm.stack =
            value :: target.source.evm.stack := by
        simpa using hValueRel.stack
      have hFinalRel :
          ScratchStateRel contract plan (name :: beforeLive) 0 frameBase
            (beforeFrameDepth + 1) frameWords
            ((Functions.ObserverSemantics.stateModel transcript).insert
              sourceAfterValue name value)
            targetAfterValue := by
        exact
          hValueScratch.declare_stack_live hValueStack
            (by
              intro other hOther
              simpa using hOther)
            (by simp) hLocation hStackOrder
      have hBindRun :
          Structured.ObserverSemantics.Code.run
              (Locals.bindLocals 0 (name :: beforeLocals.layout))
              targetAfterValue =
            .ok targetAfterValue := by
        rfl
      have hCodeRun :
          Structured.ObserverSemantics.Code.run
              (valueCode ++
                Locals.bindLocals 0 (name :: beforeLocals.layout))
              target =
            .ok targetAfterValue := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hValueRun]
        exact hBindRun
      refine ⟨targetAfterValue, hSourceRun, ?_, hFinalRel⟩
      simpa [Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] using
        (Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hCodeRun)
          Structured.EffectSemantics.Block.Eval.nil)
  | scratch slot loweredValue valueCode op
      hLowerValue hCompileValue hLocation hDup hStackOrder hFrameDepth
      hLowered hAfterState hCompiled hAfterLocals =>
      subst loweredStmts
      subst afterState
      subst compiledStmts
      subst afterLocals
      subst afterLive
      subst afterFrameDepth
      obtain ⟨targetAfterValue, hValueRun, hValueRel⟩ :=
        AllocationObserverExpression.forwardExpr
          (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
            contract)
          hSafe (.scratch hBefore) hScoped hLowerValue hCompileValue
          (.scratch hRel)
      have hValueScratch :
          ScratchStateRel contract plan beforeLive 1 frameBase
            beforeFrameDepth frameWords sourceAfterValue targetAfterValue := by
        cases hValueRel.state with
        | scratch state => simpa using state
      have hValueStack :
          targetAfterValue.source.evm.stack =
            value :: target.source.evm.stack := by
        simpa using hValueRel.stack
      have hBound := hScratchBound slot hLocation
      obtain ⟨reservation, hReservation, _hFrameRegion⟩ :=
        hValueScratch.frameReserved
      have hRegion :=
        hValueScratch.scratchAddress_reserved_of_bound
          hBound hReservation
      obtain ⟨targetFinal, hStoreRun, hFinalRel⟩ :=
        AllocationObserverPreservation.Expr.scratchAssignTop_forward_live
          hValueScratch hValueStack hWF
          (by
            intro other hOther
            simpa using hOther)
          hStackOrder (by simp) hLocation hBound
          hReservation hRegion
          (by simpa [Nat.add_assoc] using hDup)
      have hCodeRun :
          Structured.ObserverSemantics.Code.run
              (valueCode ++
                [ .op op,
                  .push (AllocationSupport.slotOffset slot),
                  .op .add,
                  .op .mstore ]) target =
            .ok targetFinal := by
        rw [AllocationObserverPreservation.ObserverCode.run_append,
          hValueRun]
        exact hStoreRun
      refine ⟨targetFinal, hSourceRun, ?_, hFinalRel⟩
      simpa [Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] using
        (Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hCodeRun)
          Structured.EffectSemantics.Block.Eval.nil)

/--
Backward adequacy for a declaration through the real allocation lowerer and
Locals compiler.

The forward theorem computes the unique target execution of the emitted
one-statement block. Inverting the supplied target derivation and comparing the
underlying code-run equations identifies its final state without adding a
generated-code or replay premise.
-/
theorem backward_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {beforeFrameDepth afterFrameDepth frameBase frameWords : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hBefore :
      AllocationObserverContext.ExprContext
        lowerCtx beforeState beforeLocals plan beforeLive
          beforeFrameDepth)
    (hAfter :
      AllocationObserverContext.ExprContext
        lowerCtx afterState afterLocals plan afterLive
          afterFrameDepth)
    (hScoped : Functions.Scope.ExprScoped beforeLive valueExpr)
    (hAfterLive : afterLive = name :: beforeLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hWF : plan.WellFormed)
    (hScratchBound :
      ∀ slot,
        plan.location? name = some (.scratch slot) →
        slot < frameWords)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hRel :
      ScratchStateRel contract plan beforeLive 0 frameBase
        beforeFrameDepth frameWords source target)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx sourceFuel
        (.let_ name valueExpr) source =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          ((Functions.ObserverSemantics.stateModel transcript).insert
            sourceAfterValue name value),
          { sourceCtx with scope := name :: sourceCtx.scope }) ∧
    ScratchStateRel contract plan afterLive 0 frameBase
      afterFrameDepth frameWords
      ((Functions.ObserverSemantics.stateModel transcript).insert
        sourceAfterValue name value)
      targetFinal := by
  obtain ⟨expected, hSourceRun, hExpected, hExpectedRel⟩ :=
    forward_of_compilers
      (targetFuel := targetFuel)
      hSafe hBefore hAfter hScoped hAfterLive hNameFrame hWF
      hScratchBound hLower hCompile hRel
  have hShape :=
    compiler_shape hBefore hAfter
      (by simp [hAfterLive]) hNameFrame hLower hCompile
  obtain ⟨code, hCompiled⟩ : ∃ code,
      compiledStmts = [Expressions.Stmt.code code] := by
    cases hShape with
    | stack _ _ _ valueCode _ _ _ _ _ _ _ hCompiled _ =>
        exact ⟨_, hCompiled⟩
    | scratch _ _ valueCode op _ _ _ _ _ _ _ _ hCompiled _ =>
        exact ⟨_, hCompiled⟩
  rw [hCompiled] at hExpected hTarget
  simp only [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] at hExpected hTarget
  have hFinal : expected = targetFinal :=
    singleton_code_regular_unique hExpected hTarget
  subst targetFinal
  exact ⟨hSourceRun, hExpectedRel⟩

/--
Representation-neutral declaration preservation through the actual allocation
lowerer and Locals compiler.

`ModeTransition` is the only representation change exposed to recursive
statement composition. It is allocation-owned and contains no generated code.
-/
theorem forward_activation_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase : Nat} {beforeMode afterMode : ActivationMode}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hBefore :
      AllocationObserverContext.ActivationExprContext
        lowerCtx beforeState beforeLocals plan beforeLive beforeMode)
    (hAfter :
      AllocationObserverContext.ActivationExprContext
        lowerCtx afterState afterLocals plan afterLive afterMode)
    (hMode : ModeTransition plan name beforeMode afterMode)
    (hScoped : Functions.Scope.ExprScoped beforeLive valueExpr)
    (hAfterLive : afterLive = name :: beforeLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hWF : plan.WellFormed)
    (hScratchBound :
      ∀ frameDepth frameWords slot,
        beforeMode = .scratch frameDepth frameWords →
        plan.location? name = some (.scratch slot) →
        slot < frameWords)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel
          (.let_ name valueExpr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            ((Functions.ObserverSemantics.stateModel transcript).insert
              sourceAfterValue name value),
            { sourceCtx with scope := name :: sourceCtx.scope }) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      ActivationOutcomeRel contract plan afterLive 0 frameBase afterMode
        (Functions.Source.Effectful.Outcome.regular
          ((Functions.ObserverSemantics.stateModel transcript).insert
            sourceAfterValue name value))
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  cases hMode with
  | @stack beforeMode planDepth hLocation =>
      cases hBefore with
      | stack hBeforeStack =>
          cases hAfter with
          | stack hAfterStack =>
              obtain
                  ⟨slot, loweredValue, valueCode, hSlot, hLowerValue,
                    hCompileValue, hStackOrder, hLowered, hAfterState,
                    hCompiled, hAfterLocals⟩ :=
                stack_let_compiler_shape hBeforeStack hAfterStack
                  hAfterLive hLocation hLower hCompile
              subst loweredStmts
              subst afterState
              subst compiledStmts
              subst afterLocals
              subst afterLive
              obtain ⟨targetAfterValue, hValueRun, hValueRel⟩ :=
                AllocationObserverExpression.forwardExpr
                  (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
                    contract)
                  hSafe (.stack hBeforeStack) hScoped
                  hLowerValue hCompileValue hRel
              have hValueStack :
                  targetAfterValue.source.evm.stack =
                    value :: target.source.evm.stack := by
                simpa using hValueRel.stack
              have hFinalRel :
                  ActivationStateRel contract plan (name :: beforeLive)
                    0 frameBase .stack
                    ((Functions.ObserverSemantics.stateModel transcript).insert
                      sourceAfterValue name value)
                    targetAfterValue := by
                exact
                  hValueRel.state.declare_stack_live hValueStack
                    (by
                      intro other hOther
                      simpa using hOther)
                    (by simp) hLocation hStackOrder
              have hBindRun :
                  Structured.ObserverSemantics.Code.run
                      (Locals.bindLocals 0
                        (name :: beforeLocals.layout))
                      targetAfterValue =
                    .ok targetAfterValue := by
                rfl
              have hCodeRun :
                  Structured.ObserverSemantics.Code.run
                      (valueCode ++
                        Locals.bindLocals 0
                          (name :: beforeLocals.layout))
                      target =
                    .ok targetAfterValue := by
                rw [AllocationObserverPreservation.ObserverCode.run_append,
                  hValueRun]
                exact hBindRun
              have hSourceRun :=
                (AllocationObserverSafety.Stmt.LeafMemorySafeRun.let_
                  (program := sourceProgram) (ctx := sourceCtx)
                  (fuel := sourceFuel) (name := name) hSafe).run_eq
              refine
                ⟨targetAfterValue, hSourceRun, ?_,
                  ActivationOutcomeRel.regular hFinalRel⟩
              simpa [Expressions.StmtList.toStructured,
                Expressions.Stmt.toStructured] using
                (Structured.EffectSemantics.Block.Eval.cons_regular
                  (Structured.EffectSemantics.Stmt.Eval.code hCodeRun)
                  Structured.EffectSemantics.Block.Eval.nil)
      | @scratch frameDepth frameWords hBeforeScratch =>
          cases hAfter with
          | scratch hAfterScratch =>
              cases hRel with
              | scratch hScratchRel =>
                  obtain
                      ⟨targetFinal, hSourceRun, hTargetRun, hFinalRel⟩ :=
                    forward_of_compilers
                      (targetFuel := targetFuel)
                      hSafe hBeforeScratch hAfterScratch hScoped
                      hAfterLive hNameFrame hWF
                      (fun slot hSlotLocation =>
                        hScratchBound frameDepth frameWords slot rfl
                          hSlotLocation)
                      hLower hCompile hScratchRel
                  exact
                    ⟨targetFinal, hSourceRun, hTargetRun,
                      ActivationOutcomeRel.regular (.scratch hFinalRel)⟩
  | scratch frameDepth frameWords slot hLocation =>
      cases hBefore with
      | scratch hBeforeScratch =>
          cases hAfter with
          | scratch hAfterScratch =>
              cases hRel with
              | scratch hScratchRel =>
                  obtain
                      ⟨targetFinal, hSourceRun, hTargetRun, hFinalRel⟩ :=
                    forward_of_compilers
                      (targetFuel := targetFuel)
                      hSafe hBeforeScratch hAfterScratch hScoped
                      hAfterLive hNameFrame hWF
                      (fun candidate hCandidateLocation =>
                        hScratchBound frameDepth frameWords candidate rfl
                          hCandidateLocation)
                      hLower hCompile hScratchRel
                  exact
                    ⟨targetFinal, hSourceRun, hTargetRun,
                      ActivationOutcomeRel.regular (.scratch hFinalRel)⟩

/--
Backward adequacy for the representation-neutral declaration boundary.
-/
theorem backward_activation_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase : Nat} {beforeMode afterMode : ActivationMode}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hBefore :
      AllocationObserverContext.ActivationExprContext
        lowerCtx beforeState beforeLocals plan beforeLive beforeMode)
    (hAfter :
      AllocationObserverContext.ActivationExprContext
        lowerCtx afterState afterLocals plan afterLive afterMode)
    (hMode : ModeTransition plan name beforeMode afterMode)
    (hScoped : Functions.Scope.ExprScoped beforeLive valueExpr)
    (hAfterLive : afterLive = name :: beforeLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hWF : plan.WellFormed)
    (hScratchBound :
      ∀ frameDepth frameWords slot,
        beforeMode = .scratch frameDepth frameWords →
        plan.location? name = some (.scratch slot) →
        slot < frameWords)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx sourceFuel
        (.let_ name valueExpr) source =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          ((Functions.ObserverSemantics.stateModel transcript).insert
            sourceAfterValue name value),
          { sourceCtx with scope := name :: sourceCtx.scope }) ∧
    ActivationOutcomeRel contract plan afterLive 0 frameBase afterMode
      (Functions.Source.Effectful.Outcome.regular
        ((Functions.ObserverSemantics.stateModel transcript).insert
          sourceAfterValue name value))
      (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  obtain ⟨expected, hSourceRun, hExpected, hExpectedRel⟩ :=
    forward_activation_of_compilers
      (targetFuel := targetFuel)
      hSafe hBefore hAfter hMode hScoped hAfterLive hNameFrame hWF
      hScratchBound hLower hCompile hRel
  obtain ⟨code, hCompiled⟩ : ∃ code,
      compiledStmts = [Expressions.Stmt.code code] := by
    cases hMode with
    | stack planDepth hLocation =>
        cases hBefore with
        | stack hBeforeStack =>
            cases hAfter with
            | stack hAfterStack =>
                obtain
                    ⟨_slot, _loweredValue, valueCode, _hSlot,
                      _hLowerValue, _hCompileValue, _hStackOrder,
                      _hLowered, _hAfterState, hCompiled, _hAfterLocals⟩ :=
                  stack_let_compiler_shape hBeforeStack hAfterStack
                    hAfterLive hLocation hLower hCompile
                exact ⟨_, hCompiled⟩
        | scratch hBeforeScratch =>
            cases hAfter with
            | scratch hAfterScratch =>
                have hShape :=
                  compiler_shape hBeforeScratch hAfterScratch
                    (by simp [hAfterLive]) hNameFrame hLower hCompile
                cases hShape with
                | stack _ _ _ valueCode _ _ _ _ _ _ _ hCompiled _ =>
                    exact ⟨_, hCompiled⟩
                | scratch _ _ valueCode op _ _ _ _ _ _ _ _ hCompiled _ =>
                    exact ⟨_, hCompiled⟩
    | scratch frameDepth frameWords slot hLocation =>
        cases hBefore with
        | scratch hBeforeScratch =>
            cases hAfter with
            | scratch hAfterScratch =>
                have hShape :=
                  compiler_shape hBeforeScratch hAfterScratch
                    (by simp [hAfterLive]) hNameFrame hLower hCompile
                cases hShape with
                | stack _ _ _ valueCode _ _ _ _ _ _ _ hCompiled _ =>
                    exact ⟨_, hCompiled⟩
                | scratch _ _ valueCode op _ _ _ _ _ _ _ _ hCompiled _ =>
                    exact ⟨_, hCompiled⟩
  rw [hCompiled] at hExpected hTarget
  simp only [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] at hExpected hTarget
  have hFinal : expected = targetFinal :=
    singleton_code_regular_unique hExpected hTarget
  subst targetFinal
  exact ⟨hSourceRun, hExpectedRel⟩

end LetLeaf

namespace AssignLeaf

/--
Exact compiler shape for one assignment, classified by the existing allocation
plan. Both constructors are derived from the real Functions lowerer and Locals
compiler.
-/
inductive CompilerShape
    (lowerCtx : AllocationLowering.Ctx)
    (lowerState : AllocationLowering.State)
    (localsCtx : Locals.Ctx)
    (plan : Locals.Allocation.Plan) (live : List Locals.Name)
    (frameDepth : Nat)
    (name : Locals.Name) (value : Functions.Expr 1)
    (loweredStmts : List Locals.Stmt)
    (compiledStmts : List Expressions.Stmt) : Prop where
  | stack
      (slot planDepth depth : Nat)
      (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code)
      (op : Structured.BasicOp)
      (hLowerValue :
        AllocationLowering.lowerExpr lowerCtx lowerState value =
          some loweredValue)
      (hCompileValue :
        Locals.Expr.compileCode localsCtx 0 loweredValue =
          some valueCode)
      (hLocation :
        plan.location? name = some (.stack planDepth))
      (hCurrentDepth :
        Locals.Layout.lookupDepth? name
            (currentStackOrder plan live) =
          some (depth + 1))
      (hDepthFrame : depth < frameDepth)
      (hSwap : Locals.StackOp.swap? (depth + 1) = some op)
      (hLowered :
        loweredStmts = [.assign name loweredValue])
      (hCompiled :
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              (.op op :: .op .pop ::
                Locals.bindLocals 0 localsCtx.layout))]) :
      CompilerShape lowerCtx lowerState localsCtx plan live frameDepth
        name value loweredStmts compiledStmts
  | scratch
      (slot : Nat)
      (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code)
      (op : Structured.BasicOp)
      (hLowerValue :
        AllocationLowering.lowerExpr lowerCtx lowerState value =
          some loweredValue)
      (hCompileValue :
        Locals.Expr.compileCode localsCtx 0 loweredValue =
          some valueCode)
      (hLocation :
        plan.location? name = some (.scratch slot))
      (hDup :
        Locals.StackOp.dup? (frameDepth + 2) = some op)
      (hLowered :
        loweredStmts =
          [.expr
            (AllocationLowering.scratchStoreExpr
              lowerCtx.frameName slot loweredValue)])
      (hCompiled :
        compiledStmts =
          [Expressions.Stmt.code
            (valueCode ++
              [ .op op,
                .push (AllocationSupport.slotOffset slot),
                .op .add,
                .op .mstore ])]) :
      CompilerShape lowerCtx lowerState localsCtx plan live frameDepth
        name value loweredStmts compiledStmts

theorem compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameDepth : Nat}
    {name : Locals.Name} {value : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name value) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    CompilerShape lowerCtx lowerState localsCtx plan live frameDepth
      name value loweredStmts compiledStmts ∧
      lowerFinal = lowerState ∧ localsFinal = localsCtx := by
  obtain ⟨slot, hSlot⟩ := hCtx.slot name hLive
  cases hLowerValue :
      AllocationLowering.lowerExpr lowerCtx lowerState value with
  | none =>
      simp [AllocationLowering.lowerStmt, hSlot, hLowerValue] at hLower
  | some loweredValue =>
      cases hStack :
          AllocationLowering.isStackSlot lowerCtx slot with
      | true =>
          simp [AllocationLowering.lowerStmt, hSlot, hLowerValue,
            hStack] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          obtain
            ⟨planDepth, depth, hLocation, hCurrentDepth, hLayoutDepth⟩ :=
            hCtx.stack name slot hLive hSlot hStack
          have hLocalsDepth :
              Locals.Layout.lookupDepth? name localsCtx.layout =
                some (depth + 1) := by
            rw [hCtx.layout]
            exact hLayoutDepth
          cases hValueCode :
              Locals.Expr.compileCode localsCtx 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hLocalsDepth, hValueCode] at hCompile
          | some valueCode =>
              cases hSwap :
                  Locals.StackOp.swap? (depth + 1) with
              | none =>
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    hLocalsDepth, hValueCode, hSwap] at hCompile
              | some op =>
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    Locals.codeStmt, hLocalsDepth, hValueCode, hSwap]
                    at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  exact
                    ⟨.stack slot planDepth depth loweredValue valueCode op
                        hLowerValue hValueCode hLocation hCurrentDepth
                        (hCtx.stack_depth_lt_frame hCurrentDepth)
                        hSwap rfl rfl,
                      rfl, rfl⟩
      | false =>
          obtain ⟨hLocation, hFrameDepth⟩ :=
            hCtx.scratch name slot hLive hSlot hStack
          have hFrameMember :
              lowerCtx.frameName ∈ lowerState.layout :=
            Locals.Layout.mem_of_lookupDepth?_eq_some hFrameDepth
          simp [AllocationLowering.lowerStmt, hSlot, hLowerValue,
            hStack, hFrameMember] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          have hFrameLocals :
              Locals.Layout.lookupDepth?
                  lowerCtx.frameName localsCtx.layout =
                some (frameDepth + 1) := by
            rw [hCtx.layout]
            exact hFrameDepth
          cases hValueCode :
              Locals.Expr.compileCode localsCtx 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                AllocationLowering.scratchStoreExpr,
                AllocationLowering.scratchAddressExpr,
                AllocationLowering.exprSeqTwo,
                Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                hValueCode, hFrameLocals] at hCompile
          | some valueCode =>
              cases hDup :
                  Locals.StackOp.dup? (frameDepth + 2) with
              | none =>
                  have hDup' :
                      Locals.StackOp.dup? (1 + (frameDepth + 1)) =
                        none := by
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hDup
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    AllocationLowering.scratchStoreExpr,
                    AllocationLowering.scratchAddressExpr,
                    AllocationLowering.exprSeqTwo,
                    Locals.Expr.compileCode, Locals.ExprSeq.compileCode,
                    hValueCode, hFrameLocals, hDup',
                    Nat.add_assoc] at hCompile
              | some op =>
                  have hDup' :
                      Locals.StackOp.dup? (1 + (frameDepth + 1)) =
                        some op := by
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hDup
                  have hStoreCode :=
                    AllocationLowering.scratchStoreExpr_compileCode
                      (frameName := lowerCtx.frameName)
                      (slot := slot) (offset := 0)
                      hValueCode hFrameLocals hDup'
                  simp only [Locals.Block.compileOpen,
                    Locals.Stmt.compile] at hCompile
                  rw [hStoreCode] at hCompile
                  simp [Locals.codeStmt] at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  exact
                    ⟨.scratch slot loweredValue valueCode op
                        hLowerValue hValueCode hLocation hDup rfl rfl,
                      rfl, rfl⟩

/--
Exact assignment compiler shape for a genuinely stack-only activation.

This is the missing stack counterpart of `compiler_shape`. A successful
lowering cannot select a scratch location because the reserved frame name is
absent from the real lowering layout.
-/
theorem stack_compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {name : Locals.Name} {value : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hCtx :
      AllocationObserverContext.StackExprContext
        lowerCtx lowerState localsCtx plan live)
    (hLive : name ∈ live)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name value) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ (slot planDepth depth : Nat)
      (loweredValue : Locals.Expr 1)
      (valueCode : Structured.Code) (op : Structured.BasicOp),
      AllocationLowering.lowerExpr lowerCtx lowerState value =
        some loweredValue ∧
      Locals.Expr.compileCode localsCtx 0 loweredValue =
        some valueCode ∧
      plan.location? name = some (.stack planDepth) ∧
      Locals.Layout.lookupDepth? name
          (currentStackOrder plan live) =
        some (depth + 1) ∧
      Locals.StackOp.swap? (depth + 1) = some op ∧
      loweredStmts = [.assign name loweredValue] ∧
      compiledStmts =
        [Expressions.Stmt.code
          (valueCode ++
            (.op op :: .op .pop ::
              Locals.bindLocals 0 localsCtx.layout))] ∧
      lowerFinal = lowerState ∧
      localsFinal = localsCtx := by
  obtain ⟨slot, hSlot⟩ := hCtx.slot name hLive
  cases hLowerValue :
      AllocationLowering.lowerExpr lowerCtx lowerState value with
  | none =>
      simp [AllocationLowering.lowerStmt, hSlot, hLowerValue] at hLower
  | some loweredValue =>
      cases hStack :
          AllocationLowering.isStackSlot lowerCtx slot with
      | false =>
          simp [AllocationLowering.lowerStmt, hSlot, hLowerValue,
            hStack, hCtx.frameAbsent] at hLower
      | true =>
          simp [AllocationLowering.lowerStmt, hSlot, hLowerValue,
            hStack] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          obtain
            ⟨planDepth, depth, hLocation, hCurrentDepth, hLayoutDepth⟩ :=
            hCtx.stack name slot hLive hSlot hStack
          have hLocalsDepth :
              Locals.Layout.lookupDepth? name localsCtx.layout =
                some (depth + 1) := by
            rw [hCtx.layout]
            exact hLayoutDepth
          cases hValueCode :
              Locals.Expr.compileCode localsCtx 0 loweredValue with
          | none =>
              simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                hLocalsDepth, hValueCode] at hCompile
          | some valueCode =>
              cases hSwap :
                  Locals.StackOp.swap? (depth + 1) with
              | none =>
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    hLocalsDepth, hValueCode, hSwap] at hCompile
              | some op =>
                  simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                    Locals.codeStmt, hLocalsDepth, hValueCode, hSwap]
                    at hCompile
                  rcases hCompile with ⟨rfl, rfl⟩
                  exact
                    ⟨slot, planDepth, depth, loweredValue, valueCode, op,
                      rfl, hValueCode, hLocation, hCurrentDepth,
                      hSwap, rfl, rfl, rfl, rfl⟩

/--
Forward preservation for assignment through the actual allocation lowerer and
Locals compiler.

Stack placement executes the compiler's `SWAP`/`POP` update. Scratch placement
executes the canonical frame store. Both retain the same live set and
activation frame.
-/
theorem forward_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameDepth frameBase frameWords : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hContains :
      Locals.Source.Store.contains
          ((Functions.ObserverSemantics.stateModel transcript).vars source)
          name =
        true)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hWF : plan.WellFormed)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ScratchStateRel contract plan live 0 frameBase
        frameDepth frameWords source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel
          (.assign name valueExpr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            ((Functions.ObserverSemantics.stateModel transcript).withVars
              sourceAfterValue
              (Locals.Source.Store.insert
                ((Functions.ObserverSemantics.stateModel transcript).vars
                  sourceAfterValue)
                name value)),
            sourceCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      ScratchStateRel contract plan live 0 frameBase
        frameDepth frameWords
        ((Functions.ObserverSemantics.stateModel transcript).withVars
          sourceAfterValue
          (Locals.Source.Store.insert
            ((Functions.ObserverSemantics.stateModel transcript).vars
              sourceAfterValue)
            name value))
        targetFinal := by
  obtain ⟨hShape, hLowerFinal, hLocalsFinal⟩ :=
    compiler_shape hCtx hLive hLower hCompile
  subst lowerFinal
  subst localsFinal
  have hSourceRun :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.assign
      (program := sourceProgram) (ctx := sourceCtx) (fuel := sourceFuel)
      hContains hSafe).run_eq
  change
    Locals.Source.Store.contains source.source.vars name = true
      at hContains
  cases hOld : source.source.vars name with
  | none =>
      simp [Locals.Source.Store.contains, hOld] at hContains
  | some old =>
      have hOldAfter :
          sourceAfterValue.source.vars name = some old := by
        rw [hSafe.vars_eq, hOld]
      cases hShape with
      | stack slot planDepth depth loweredValue valueCode op
          hLowerValue hCompileValue hLocation hCurrentDepth hDepthFrame
          hSwap hLowered hCompiled =>
          subst loweredStmts
          subst compiledStmts
          obtain ⟨targetAfterValue, hValueRun, hValueRel⟩ :=
            AllocationObserverExpression.forwardExpr
              (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
                contract)
              hSafe (.scratch hCtx) hScoped hLowerValue hCompileValue
              (.scratch hRel)
          have hValueScratch :
              ScratchStateRel contract plan live 1 frameBase
                frameDepth frameWords sourceAfterValue targetAfterValue := by
            cases hValueRel.state with
            | scratch state => simpa using state
          have hValueStack :
              targetAfterValue.source.evm.stack =
                value :: target.source.evm.stack := by
            simpa using hValueRel.stack
          have hOldTarget :=
            hValueScratch.base.core.store.stack_at
              hLive hLocation hCurrentDepth
          rw [hValueStack, hOldAfter] at hOldTarget
          have hRestGet :
              target.source.evm.stack[depth]? = some old := by
            simpa [show 1 + depth = depth + 1 by omega] using hOldTarget
          let targetFinal :=
            StateRel.replaceStackBy 2
              (target.source.evm.stack.set depth value)
              targetAfterValue
          have hAssignRun :
              Structured.ObserverSemantics.Code.run
                  [.op op, .op .pop] targetAfterValue =
                .ok targetFinal := by
            simpa [targetFinal] using
              (AllocationObserverPreservation.ObserverCode.run_swap_pop
                hSwap hRestGet hValueStack)
          have hFinalRel :
              ScratchStateRel contract plan live 0 frameBase
                frameDepth frameWords
                (sourceAfterValue.withSource
                  (sourceAfterValue.source.insert name value))
                targetFinal := by
            exact
              hValueScratch.assign_stack_live hValueStack hLive
                hLocation hCurrentDepth hDepthFrame hOldAfter
          have hBindRun :
              Structured.ObserverSemantics.Code.run
                  (Locals.bindLocals 0 localsCtx.layout) targetFinal =
                .ok targetFinal := by
            rfl
          have hTailRun :
              Structured.ObserverSemantics.Code.run
                  (.op op :: .op .pop ::
                    Locals.bindLocals 0 localsCtx.layout)
                  targetAfterValue =
                .ok targetFinal := by
            change
              Structured.ObserverSemantics.Code.run
                  ([.op op, .op .pop] ++
                    Locals.bindLocals 0 localsCtx.layout)
                  targetAfterValue =
                .ok targetFinal
            rw [AllocationObserverPreservation.ObserverCode.run_append,
              hAssignRun]
            exact hBindRun
          have hCodeRun :
              Structured.ObserverSemantics.Code.run
                  (valueCode ++
                    (.op op :: .op .pop ::
                      Locals.bindLocals 0 localsCtx.layout))
                  target =
                .ok targetFinal := by
            rw [AllocationObserverPreservation.ObserverCode.run_append,
              hValueRun]
            exact hTailRun
          refine ⟨targetFinal, hSourceRun, ?_, ?_⟩
          · simpa [Expressions.StmtList.toStructured,
              Expressions.Stmt.toStructured] using
              (Structured.EffectSemantics.Block.Eval.cons_regular
                (Structured.EffectSemantics.Stmt.Eval.code hCodeRun)
                Structured.EffectSemantics.Block.Eval.nil)
          · simpa [Functions.ObserverSemantics.stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.withVars,
              Locals.Source.State.withVars,
              Locals.Source.State.insert] using hFinalRel
      | scratch slot loweredValue valueCode op
          hLowerValue hCompileValue hLocation hDup hLowered hCompiled =>
          subst loweredStmts
          subst compiledStmts
          obtain ⟨targetAfterValue, hValueRun, hValueRel⟩ :=
            AllocationObserverExpression.forwardExpr
              (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
                contract)
              hSafe (.scratch hCtx) hScoped hLowerValue hCompileValue
              (.scratch hRel)
          have hValueScratch :
              ScratchStateRel contract plan live 1 frameBase
                frameDepth frameWords sourceAfterValue targetAfterValue := by
            cases hValueRel.state with
            | scratch state => simpa using state
          have hValueStack :
              targetAfterValue.source.evm.stack =
                value :: target.source.evm.stack := by
            simpa using hValueRel.stack
          have hBound :=
            hValueScratch.scratchBound name slot hLive hLocation
          obtain ⟨reservation, hReservation, _hFrameRegion⟩ :=
            hValueScratch.frameReserved
          have hRegion :=
            hValueScratch.scratchAddress_reserved_of_bound
              hBound hReservation
          obtain ⟨targetFinal, hStoreRun, hFinalRel⟩ :=
            AllocationObserverPreservation.Expr.scratchAssignTop_forward_live
              hValueScratch hValueStack hWF
              (fun other hOther => Or.inr hOther)
              rfl hLive hLocation hBound
              hReservation hRegion
              (by simpa [Nat.add_assoc] using hDup)
          have hCodeRun :
              Structured.ObserverSemantics.Code.run
                  (valueCode ++
                    [ .op op,
                      .push (AllocationSupport.slotOffset slot),
                      .op .add,
                      .op .mstore ]) target =
                .ok targetFinal := by
            rw [AllocationObserverPreservation.ObserverCode.run_append,
              hValueRun]
            exact hStoreRun
          refine ⟨targetFinal, hSourceRun, ?_, ?_⟩
          · simpa [Expressions.StmtList.toStructured,
              Expressions.Stmt.toStructured] using
              (Structured.EffectSemantics.Block.Eval.cons_regular
                (Structured.EffectSemantics.Stmt.Eval.code hCodeRun)
                Structured.EffectSemantics.Block.Eval.nil)
          · simpa [Functions.ObserverSemantics.stateModel,
              Locals.ObserverSemantics.stateModel,
              Locals.Source.Effectful.StateModel.withVars,
              Locals.Source.State.withVars,
              Locals.Source.State.insert] using hFinalRel

/--
Backward adequacy for assignment through the real allocation lowerer and
Locals compiler.
-/
theorem backward_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameDepth frameBase frameWords : Nat}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hContains :
      Locals.Source.Store.contains
          ((Functions.ObserverSemantics.stateModel transcript).vars source)
          name =
        true)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hCtx :
      AllocationObserverContext.ExprContext
        lowerCtx lowerState localsCtx plan live frameDepth)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hWF : plan.WellFormed)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ScratchStateRel contract plan live 0 frameBase
        frameDepth frameWords source target)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx sourceFuel
        (.assign name valueExpr) source =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          ((Functions.ObserverSemantics.stateModel transcript).withVars
            sourceAfterValue
            (Locals.Source.Store.insert
              ((Functions.ObserverSemantics.stateModel transcript).vars
                sourceAfterValue)
              name value)),
          sourceCtx) ∧
    ScratchStateRel contract plan live 0 frameBase
      frameDepth frameWords
      ((Functions.ObserverSemantics.stateModel transcript).withVars
        sourceAfterValue
        (Locals.Source.Store.insert
          ((Functions.ObserverSemantics.stateModel transcript).vars
            sourceAfterValue)
          name value))
      targetFinal := by
  obtain ⟨expected, hSourceRun, hExpected, hExpectedRel⟩ :=
    forward_of_compilers
      (targetFuel := targetFuel)
      hContains hSafe hCtx hScoped hLive hWF hLower hCompile hRel
  obtain ⟨hShape, _hLowerFinal, _hLocalsFinal⟩ :=
    compiler_shape hCtx hLive hLower hCompile
  obtain ⟨code, hCompiled⟩ : ∃ code,
      compiledStmts = [Expressions.Stmt.code code] := by
    cases hShape with
    | stack _ _ _ _ valueCode op _ _ _ _ _ _ _ hCompiled =>
        exact ⟨_, hCompiled⟩
    | scratch _ _ valueCode op _ _ _ _ _ hCompiled =>
        exact ⟨_, hCompiled⟩
  rw [hCompiled] at hExpected hTarget
  simp only [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] at hExpected hTarget
  have hFinal : expected = targetFinal :=
    LetLeaf.singleton_code_regular_unique hExpected hTarget
  subst targetFinal
  exact ⟨hSourceRun, hExpectedRel⟩

/--
Representation-neutral assignment preservation through the actual allocation
lowerer and Locals compiler.

Stack-only artifacts use their real layout directly. Scratch artifacts reuse
the stronger frame theorem above. Both branches expose the same recursive
`ActivationOutcomeRel` interface.
-/
theorem forward_activation_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hContains :
      Locals.Source.Store.contains
          ((Functions.ObserverSemantics.stateModel transcript).vars source)
          name =
        true)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hWF : plan.WellFormed)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live 0 frameBase
        mode source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel
          (.assign name valueExpr) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular
            ((Functions.ObserverSemantics.stateModel transcript).withVars
              sourceAfterValue
              (Locals.Source.Store.insert
                ((Functions.ObserverSemantics.stateModel transcript).vars
                  sourceAfterValue)
                name value)),
            sourceCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      ActivationOutcomeRel contract plan live 0 frameBase mode
        (Functions.Source.Effectful.Outcome.regular
          ((Functions.ObserverSemantics.stateModel transcript).withVars
            sourceAfterValue
            (Locals.Source.Store.insert
              ((Functions.ObserverSemantics.stateModel transcript).vars
                sourceAfterValue)
              name value)))
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  cases hCtx with
  | stack hStackCtx =>
      obtain
          ⟨slot, planDepth, depth, loweredValue, valueCode, op,
            hLowerValue, hCompileValue, hLocation, hCurrentDepth,
            hSwap, hLowered, hCompiled, hLowerFinal, hLocalsFinal⟩ :=
        stack_compiler_shape hStackCtx hLive hLower hCompile
      subst loweredStmts
      subst compiledStmts
      subst lowerFinal
      subst localsFinal
      have hSourceRun :=
        (AllocationObserverSafety.Stmt.LeafMemorySafeRun.assign
          (program := sourceProgram) (ctx := sourceCtx) (fuel := sourceFuel)
          hContains hSafe).run_eq
      change
        Locals.Source.Store.contains source.source.vars name = true
          at hContains
      cases hOld : source.source.vars name with
      | none =>
          simp [Locals.Source.Store.contains, hOld] at hContains
      | some old =>
          have hOldAfter :
              sourceAfterValue.source.vars name = some old := by
            rw [hSafe.vars_eq, hOld]
          obtain ⟨targetAfterValue, hValueRun, hValueRel⟩ :=
            AllocationObserverExpression.forwardExpr
              (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
                contract)
              hSafe (.stack hStackCtx) hScoped hLowerValue hCompileValue hRel
          have hValueStack :
              targetAfterValue.source.evm.stack =
                value :: target.source.evm.stack := by
            simpa using hValueRel.stack
          have hOldTarget :=
            hValueRel.state.base.core.store.stack_at
              hLive hLocation hCurrentDepth
          rw [hValueStack, hOldAfter] at hOldTarget
          have hRestGet :
              target.source.evm.stack[depth]? = some old := by
            simpa [show 1 + depth = depth + 1 by omega] using hOldTarget
          let targetFinal :=
            StateRel.replaceStackBy 2
              (target.source.evm.stack.set depth value)
              targetAfterValue
          have hAssignRun :
              Structured.ObserverSemantics.Code.run
                  [.op op, .op .pop] targetAfterValue =
                .ok targetFinal := by
            simpa [targetFinal] using
              (AllocationObserverPreservation.ObserverCode.run_swap_pop
                hSwap hRestGet hValueStack)
          have hFinalRel :
              ActivationStateRel contract plan live 0 frameBase
                .stack
                (sourceAfterValue.withSource
                  (sourceAfterValue.source.insert name value))
                targetFinal := by
            exact
              hValueRel.state.assign_stack_live hValueStack hLive
                hLocation hCurrentDepth trivial hOldAfter
          have hBindRun :
              Structured.ObserverSemantics.Code.run
                  (Locals.bindLocals 0 localsCtx.layout) targetFinal =
                .ok targetFinal := by
            rfl
          have hTailRun :
              Structured.ObserverSemantics.Code.run
                  (.op op :: .op .pop ::
                    Locals.bindLocals 0 localsCtx.layout)
                  targetAfterValue =
                .ok targetFinal := by
            change
              Structured.ObserverSemantics.Code.run
                  ([.op op, .op .pop] ++
                    Locals.bindLocals 0 localsCtx.layout)
                  targetAfterValue =
                .ok targetFinal
            rw [AllocationObserverPreservation.ObserverCode.run_append,
              hAssignRun]
            exact hBindRun
          have hCodeRun :
              Structured.ObserverSemantics.Code.run
                  (valueCode ++
                    (.op op :: .op .pop ::
                      Locals.bindLocals 0 localsCtx.layout))
                  target =
                .ok targetFinal := by
            rw [AllocationObserverPreservation.ObserverCode.run_append,
              hValueRun]
            exact hTailRun
          refine ⟨targetFinal, hSourceRun, ?_, ?_⟩
          · simpa [Expressions.StmtList.toStructured,
              Expressions.Stmt.toStructured] using
              (Structured.EffectSemantics.Block.Eval.cons_regular
                (Structured.EffectSemantics.Stmt.Eval.code hCodeRun)
                Structured.EffectSemantics.Block.Eval.nil)
          · exact
              ActivationOutcomeRel.regular
                (by
                  simpa [Functions.ObserverSemantics.stateModel,
                    Locals.ObserverSemantics.stateModel,
                    Locals.Source.Effectful.StateModel.withVars,
                    Locals.Source.State.withVars,
                    Locals.Source.State.insert] using hFinalRel)
  | @scratch frameDepth frameWords hScratchCtx =>
      cases hRel with
      | scratch hScratchRel =>
          obtain ⟨targetFinal, hSourceRun, hTargetRun, hFinalRel⟩ :=
            forward_of_compilers
              (targetFuel := targetFuel)
              hContains hSafe hScratchCtx hScoped hLive hWF
              hLower hCompile hScratchRel
          exact
            ⟨targetFinal, hSourceRun, hTargetRun,
              ActivationOutcomeRel.regular (.scratch hFinalRel)⟩

/--
Backward adequacy for the representation-neutral assignment boundary.
-/
theorem backward_activation_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hContains :
      Locals.Source.Store.contains
          ((Functions.ObserverSemantics.stateModel transcript).vars source)
          name =
        true)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hWF : plan.WellFormed)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live 0 frameBase
        mode source target)
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram (targetFuel + 2)
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    Functions.Source.Effectful.Stmt.run
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram sourceCtx sourceFuel
        (.assign name valueExpr) source =
      .ok
        (Functions.Source.Effectful.Outcome.regular
          ((Functions.ObserverSemantics.stateModel transcript).withVars
            sourceAfterValue
            (Locals.Source.Store.insert
              ((Functions.ObserverSemantics.stateModel transcript).vars
                sourceAfterValue)
              name value)),
          sourceCtx) ∧
    ActivationOutcomeRel contract plan live 0 frameBase mode
      (Functions.Source.Effectful.Outcome.regular
        ((Functions.ObserverSemantics.stateModel transcript).withVars
          sourceAfterValue
          (Locals.Source.Store.insert
            ((Functions.ObserverSemantics.stateModel transcript).vars
              sourceAfterValue)
            name value)))
      (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  obtain ⟨expected, hSourceRun, hExpected, hExpectedRel⟩ :=
    forward_activation_of_compilers
      (targetFuel := targetFuel)
      hContains hSafe hCtx hScoped hLive hWF hLower hCompile hRel
  obtain ⟨code, hCompiled⟩ : ∃ code,
      compiledStmts = [Expressions.Stmt.code code] := by
    cases hCtx with
    | stack hStackCtx =>
        obtain
            ⟨_slot, _planDepth, _depth, _loweredValue, valueCode, op,
              _hLowerValue, _hCompileValue, _hLocation, _hCurrentDepth,
              _hSwap, _hLowered, hCompiled, _hLowerFinal, _hLocalsFinal⟩ :=
          stack_compiler_shape hStackCtx hLive hLower hCompile
        exact ⟨_, hCompiled⟩
    | scratch hScratchCtx =>
        obtain ⟨hShape, _hLowerFinal, _hLocalsFinal⟩ :=
          compiler_shape hScratchCtx hLive hLower hCompile
        cases hShape with
        | stack _ _ _ _ valueCode op _ _ _ _ _ _ _ hCompiled =>
            exact ⟨_, hCompiled⟩
        | scratch _ _ valueCode op _ _ _ _ _ hCompiled =>
            exact ⟨_, hCompiled⟩
  rw [hCompiled] at hExpected hTarget
  simp only [Expressions.StmtList.toStructured,
    Expressions.Stmt.toStructured] at hExpected hTarget
  have hFinal : expected = targetFinal :=
    LetLeaf.singleton_code_regular_unique hExpected hTarget
  subst targetFinal
  exact ⟨hSourceRun, hExpectedRel⟩

end AssignLeaf

namespace TerminalLeaf

/--
Successful lowering and Locals compilation of a terminal-with-arguments
statement emits exactly the argument code followed by the terminal statement.
-/
theorem args_compiler_shape
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminalArgs kind args) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ lowered code,
      AllocationLowering.lowerExprSeq lowerCtx lowerState args =
          some lowered ∧
      Locals.ExprSeq.compileCode localsCtx 0 lowered = some code ∧
      loweredStmts = [.terminalArgs kind lowered] ∧
      lowerFinal = lowerState ∧
      compiledStmts =
        [Expressions.Stmt.code code, Expressions.Stmt.terminal kind] ∧
      localsFinal = localsCtx := by
  cases hLowerArgs :
      AllocationLowering.lowerExprSeq lowerCtx lowerState args with
  | none =>
      simp [AllocationLowering.lowerStmt, hLowerArgs] at hLower
  | some lowered =>
      simp [AllocationLowering.lowerStmt, hLowerArgs] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      cases hCode :
          Locals.ExprSeq.compileCode localsCtx 0 lowered with
      | none =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile,
            hCode] at hCompile
      | some code =>
          simp [Locals.Block.compileOpen, Locals.Stmt.compile,
            Locals.codeStmt, hCode] at hCompile
          rcases hCompile with ⟨rfl, rfl⟩
          exact ⟨lowered, code, rfl, hCode, rfl, rfl, rfl, rfl⟩

/--
Terminal-with-arguments preservation through the real allocation lowerer and
Locals compiler.

The argument expression sequence preserves the active allocation relation.
The terminal-owned theorem then erases dead local realization and returns the
shared halt relation used by recursive nonregular sequencing.
-/
theorem forward_args_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source afterArgs sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hArgs :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        contract transcript args source afterArgs values)
    (hMemory :
      AllocationObserverSafety.TerminalMemorySafe contract kind values)
    (hTerminal :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind afterArgs values =
        .ok sourceFinal)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprSeqScoped live args)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminalArgs kind args) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode source target) :
    ∃ targetFinal,
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx 0 (.terminalArgs kind args) source =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            sourceCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts := Expressions.StmtList.toStructured compiledStmts }
        target
        (Structured.EffectSemantics.Outcome.halt kind targetFinal) ∧
      ActivationOutcomeRel contract plan live 0 frameBase mode
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal) := by
  obtain
      ⟨lowered, code, hLowerArgs, hCompileCode,
        rfl, rfl, rfl, rfl⟩ :=
    args_compiler_shape hLower hCompile
  obtain ⟨targetAfterArgs, hArgsRun, hArgsRel⟩ :=
    AllocationObserverExpression.forwardExprSeq
      (AllocationObserverPrimitive.canonicalActivationPrimitiveForward
        contract)
      hArgs hCtx hScoped hLowerArgs hCompileCode hRel
  obtain ⟨evmFinal, hStep, hHaltRel⟩ :=
    (AllocationObserverTerminal.Invocation.of_memorySafe hMemory).forward_observer
      hArgsRel.state hTerminal hArgsRel.stack
  let targetFinal : Structured.ObserverSemantics.State transcript :=
    targetAfterArgs.withSource (targetAfterArgs.source.withEVM evmFinal)
  have hTerminalStmt :
      Structured.ObserverSemantics.Stmt.Eval
        targetProgram 0 (.terminal kind) targetAfterArgs
          (Structured.EffectSemantics.Outcome.halt kind targetFinal) := by
    simpa [targetFinal,
      Structured.ObserverSemantics.stateModel_withEVM] using
        (Structured.EffectSemantics.Stmt.Eval.terminal
          (model := Structured.ObserverSemantics.stateModel transcript)
          (handler := Structured.ObserverSemantics.handler transcript)
          (program := targetProgram) (fuel := 0) hStep)
  have hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram 2
        { stmts :=
            [Structured.Stmt.code code, Structured.Stmt.terminal kind] }
        target
        (Structured.EffectSemantics.Outcome.halt kind targetFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code
        (fuel := 1) hArgsRun)
      (Structured.EffectSemantics.Block.Eval.cons_halt hTerminalStmt)
  have hSource :=
    (AllocationObserverSafety.Stmt.LeafMemorySafeRun.terminalArgs
      (program := sourceProgram) (ctx := sourceCtx) (fuel := 0)
      hArgs hMemory hTerminal).run_eq
  refine ⟨targetFinal, hSource, ?_, ?_⟩
  · simpa [Expressions.StmtList.toStructured,
      Expressions.Stmt.toStructured] using hTarget
  · exact ActivationOutcomeRel.halt kind hHaltRel

end TerminalLeaf

namespace Sequence

/--
One source statement that finishes regularly after lowering to an arbitrary
Structured statement prefix.

Fuel is existential proof data. The semantic boundary contains only the
canonical source run, canonical target evaluation, and the adjacent allocation
state relation.
-/
def RegularStmtForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (afterLive : List Locals.Name) (frameBase : Nat)
    (afterMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (stmt : Functions.Stmt)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (target : Structured.ObserverSemantics.State transcript)
    (compiled : List Structured.Stmt)
    (sourceFinal : Functions.ObserverSemantics.State transcript)
    (targetFinal : Structured.ObserverSemantics.State transcript)
    (finalCtx : Functions.Source.Ctx) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel stmt source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            finalCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel { stmts := compiled } target
          (Structured.EffectSemantics.Outcome.regular targetFinal) ∧
      ActivationStateRel contract plan afterLive 0 frameBase afterMode
        sourceFinal targetFinal

namespace RegularStmtForward

theorem expr_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {expr : Functions.Expr 0}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript expr source sourceFinal values)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live expr)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState (.expr expr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode source target) :
    ∃ targetFinal,
      RegularStmtForward contract transcript plan live frameBase mode
        sourceProgram sourceCtx (.expr expr) source targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceFinal targetFinal sourceCtx := by
  obtain ⟨targetFinal, hSource, hTarget, hOutcome⟩ :=
    ExprLeaf.forward_of_compilers
      (sourceFuel := 0) (targetFuel := 0)
      hSafe hCtx hScoped hLower hCompile hRel
  cases hOutcome with
  | regular hFinalRel =>
      exact
        ⟨targetFinal, 0, 2, hSource, hTarget, hFinalRel⟩

theorem let_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {plan : Locals.Allocation.Plan}
    {beforeLive afterLive : List Locals.Name}
    {frameBase : Nat} {beforeMode afterMode : ActivationMode}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hBefore :
      AllocationObserverContext.ActivationExprContext
        lowerCtx beforeState beforeLocals plan beforeLive beforeMode)
    (hAfter :
      AllocationObserverContext.ActivationExprContext
        lowerCtx afterState afterLocals plan afterLive afterMode)
    (hMode : LetLeaf.ModeTransition plan name beforeMode afterMode)
    (hScoped : Functions.Scope.ExprScoped beforeLive valueExpr)
    (hAfterLive : afterLive = name :: beforeLive)
    (hNameFrame : name ≠ lowerCtx.frameName)
    (hWF : plan.WellFormed)
    (hScratchBound :
      ∀ frameDepth frameWords slot,
        beforeMode = .scratch frameDepth frameWords →
        plan.location? name = some (.scratch slot) →
        slot < frameWords)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns beforeState
          (.let_ name valueExpr) =
        some (loweredStmts, afterState))
    (hCompile :
      Locals.Block.compileOpen beforeLocals { stmts := loweredStmts } =
        some (compiledStmts, afterLocals))
    (hRel :
      ActivationStateRel contract plan beforeLive 0 frameBase
        beforeMode source target) :
    ∃ targetFinal,
      RegularStmtForward contract transcript plan afterLive frameBase afterMode
        sourceProgram sourceCtx (.let_ name valueExpr) source
        targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        ((Functions.ObserverSemantics.stateModel transcript).insert
          sourceAfterValue name value)
        targetFinal
        { sourceCtx with scope := name :: sourceCtx.scope } := by
  obtain ⟨targetFinal, hSource, hTarget, hOutcome⟩ :=
    LetLeaf.forward_activation_of_compilers
      (sourceFuel := 0) (targetFuel := 0)
      hSafe hBefore hAfter hMode hScoped hAfterLive hNameFrame hWF
      hScratchBound hLower hCompile hRel
  cases hOutcome with
  | regular hFinalRel =>
      exact
        ⟨targetFinal, 0, 2, hSource, hTarget, hFinalRel⟩

theorem assign_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {name : Locals.Name} {valueExpr : Functions.Expr 1}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source sourceAfterValue :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {value : Word}
    (hContains :
      Locals.Source.Store.contains
          ((Functions.ObserverSemantics.stateModel transcript).vars source)
          name =
        true)
    (hSafe :
      AllocationObserverSafety.Expr.MemorySafeEval
        contract transcript valueExpr source sourceAfterValue [value])
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprScoped live valueExpr)
    (hLive : name ∈ live)
    (hWF : plan.WellFormed)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.assign name valueExpr) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live 0 frameBase
        mode source target) :
    ∃ targetFinal,
      RegularStmtForward contract transcript plan live frameBase mode
        sourceProgram sourceCtx (.assign name valueExpr) source
        targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        ((Functions.ObserverSemantics.stateModel transcript).withVars
          sourceAfterValue
          (Locals.Source.Store.insert
            ((Functions.ObserverSemantics.stateModel transcript).vars
              sourceAfterValue)
            name value))
        targetFinal sourceCtx := by
  obtain ⟨targetFinal, hSource, hTarget, hOutcome⟩ :=
    AssignLeaf.forward_activation_of_compilers
      (sourceFuel := 0) (targetFuel := 0)
      hContains hSafe hCtx hScoped hLive hWF hLower hCompile hRel
  cases hOutcome with
  | regular hFinalRel =>
      exact
        ⟨targetFinal, 0, 2, hSource, hTarget, hFinalRel⟩

end RegularStmtForward

/--
One source statement that exits nonregularly after lowering to an arbitrary
Structured statement prefix.

The source statement context is retained only to state the canonical statement
run. Open-block semantics restores the incoming context when the abrupt result
skips the remaining statement list.
-/
def NonregularStmtForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (finalLive : List Locals.Name) (frameBase : Nat)
    (finalMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (stmt : Functions.Stmt)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (target : Structured.ObserverSemantics.State transcript)
    (compiled : List Structured.Stmt)
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript))
    (stmtCtx : Functions.Source.Ctx) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel stmt source =
        .ok (sourceOutcome, stmtCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel { stmts := compiled } target
          targetOutcome ∧
      sourceOutcome.mode ≠ .regular ∧
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome

namespace NonregularStmtForward

theorem of_runs
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {finalLive : List Locals.Name} {frameBase : Nat}
    {finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {stmt : Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    {compiled : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel stmt source =
        .ok (sourceOutcome, stmtCtx))
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel { stmts := compiled } target
          targetOutcome)
    (hMode : sourceOutcome.mode ≠ .regular)
    (hRel :
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome) :
    NonregularStmtForward contract transcript plan finalLive frameBase
      finalMode sourceProgram sourceCtx stmt source targetProgram target
      compiled sourceOutcome targetOutcome stmtCtx :=
  ⟨sourceFuel, targetFuel, hSource, hTarget, hMode, hRel⟩

theorem of_halt_runs
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {finalLive : List Locals.Name} {frameBase : Nat}
    {finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {sourceFuel targetFuel : Nat}
    {stmt : Functions.Stmt}
    {source sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target targetFinal :
      Structured.ObserverSemantics.State transcript}
    {compiled : List Structured.Stmt}
    {kind : Assembly.HaltKind}
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel stmt source =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind sourceFinal,
            stmtCtx))
    (hTarget :
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel { stmts := compiled } target
          (Structured.EffectSemantics.Outcome.halt kind targetFinal))
    (hRel :
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)) :
    NonregularStmtForward contract transcript plan finalLive frameBase
      finalMode sourceProgram sourceCtx stmt source targetProgram target
      compiled
      (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
      (Structured.EffectSemantics.Outcome.halt kind targetFinal)
      stmtCtx :=
  of_runs hSource hTarget
    (by
      intro hMode
      cases hMode)
    hRel

theorem terminalArgs_of_compilers
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {targetProgram : Structured.Program}
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {plan : Locals.Allocation.Plan} {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {source afterArgs sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {values : List Word}
    (hArgs :
      AllocationObserverSafety.ExprSeq.MemorySafeEval
        contract transcript args source afterArgs values)
    (hMemory :
      AllocationObserverSafety.TerminalMemorySafe contract kind values)
    (hTerminal :
      (Functions.ObserverSemantics.primitiveSemantics transcript).terminal
          kind afterArgs values =
        .ok sourceFinal)
    (hCtx :
      AllocationObserverContext.ActivationExprContext
        lowerCtx lowerState localsCtx plan live mode)
    (hScoped : Functions.Scope.ExprSeqScoped live args)
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.terminalArgs kind args) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal))
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode source target) :
    ∃ targetFinal,
      NonregularStmtForward contract transcript plan live frameBase mode
        sourceProgram sourceCtx (.terminalArgs kind args) source
        targetProgram target
        (Expressions.StmtList.toStructured compiledStmts)
        (Functions.Source.Effectful.Outcome.halt kind sourceFinal)
        (Structured.EffectSemantics.Outcome.halt kind targetFinal)
        sourceCtx := by
  obtain ⟨targetFinal, hSource, hTarget, hOutcome⟩ :=
    TerminalLeaf.forward_args_of_compilers
      hArgs hMemory hTerminal hCtx hScoped hLower hCompile hRel
  exact
    ⟨targetFinal,
      of_halt_runs hSource hTarget hOutcome⟩

end NonregularStmtForward

/--
Forward simulation package for one open source block and its lowered
Structured block.
-/
def BlockForward
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (plan : Locals.Allocation.Plan)
    (finalLive : List Locals.Name) (frameBase : Nat)
    (finalMode : ActivationMode)
    (sourceProgram : Functions.Program)
    (sourceCtx : Functions.Source.Ctx)
    (sourceBlock : Functions.Block)
    (source : Functions.ObserverSemantics.State transcript)
    (targetProgram : Structured.Program)
    (targetBlock : Structured.Block)
    (target : Structured.ObserverSemantics.State transcript)
    (sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript))
    (targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript))
    (finalCtx : Functions.Source.Ctx) : Prop :=
  ∃ sourceFuel targetFuel,
    Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSemantics.primitiveSemantics transcript)
          sourceProgram sourceCtx sourceFuel sourceBlock source =
        .ok (sourceOutcome, finalCtx) ∧
      Structured.ObserverSemantics.Block.Eval
        targetProgram targetFuel targetBlock target targetOutcome ∧
      ActivationOutcomeRel contract plan finalLive 0 frameBase finalMode
        sourceOutcome targetOutcome

/--
Empty source and target blocks preserve the incoming activation relation.
-/
theorem BlockForward.nil
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {live : List Locals.Name}
    {frameBase : Nat} {mode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    (hRel :
      ActivationStateRel contract plan live 0 frameBase mode source target) :
    BlockForward contract transcript plan live frameBase mode
      sourceProgram sourceCtx { stmts := [] } source
      targetProgram { stmts := [] } target
      (Functions.Source.Effectful.Outcome.regular source)
      (Structured.EffectSemantics.Outcome.regular target)
      sourceCtx := by
  exact
    ⟨1, 1,
      by simp [Functions.Source.Effectful.Block.runOpen],
      Structured.EffectSemantics.Block.Eval.nil,
      ActivationOutcomeRel.regular hRel⟩

/--
Horizontal regular-head composition.

This is the recursive statement-list seam: a source statement may lower to
many target statements, but sequencing is composed only through adjacent
semantic evaluations and the activation relation.
-/
theorem BlockForward.cons_regular
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {afterLive finalLive : List Locals.Name}
    {frameBase : Nat} {afterMode finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx midCtx finalCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {source sourceMid : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target targetMid : Structured.ObserverSemantics.State transcript}
    {compiledHead compiledTail : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hHead :
      RegularStmtForward contract transcript plan afterLive frameBase afterMode
        sourceProgram sourceCtx stmt source targetProgram target
        compiledHead sourceMid targetMid midCtx)
    (hTail :
      BlockForward contract transcript plan finalLive frameBase finalMode
        sourceProgram midCtx { stmts := rest } sourceMid
        targetProgram { stmts := compiledTail } targetMid
        sourceOutcome targetOutcome finalCtx) :
    BlockForward contract transcript plan finalLive frameBase finalMode
      sourceProgram sourceCtx { stmts := stmt :: rest } source
      targetProgram { stmts := compiledHead ++ compiledTail } target
      sourceOutcome targetOutcome finalCtx := by
  rcases hHead with
    ⟨headSourceFuel, headTargetFuel,
      hHeadSource, hHeadTarget, hHeadRel⟩
  rcases hTail with
    ⟨tailSourceFuel, tailTargetFuel,
      hTailSource, hTailTarget, hTailRel⟩
  obtain ⟨sourceFuel, hSourceRun⟩ :=
    Functions.Source.Effectful.Block.runOpen_cons_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSemantics.primitiveSemantics transcript)
      sourceProgram hHeadSource hTailSource
  obtain ⟨targetFuel, hTargetRun⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hHeadTarget hTailTarget
  exact ⟨sourceFuel, targetFuel, hSourceRun, hTargetRun, hTailRel⟩

/--
Horizontal abrupt-head composition.

Both semantic owners prove that a nonregular head makes its tail unreachable.
The allocation outcome relation supplies the matching target control mode.
-/
theorem BlockForward.cons_nonregular
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {plan : Locals.Allocation.Plan}
    {finalLive : List Locals.Name}
    {frameBase : Nat} {finalMode : ActivationMode}
    {sourceProgram : Functions.Program}
    {sourceCtx stmtCtx : Functions.Source.Ctx}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {source : Functions.ObserverSemantics.State transcript}
    {targetProgram : Structured.Program}
    {target : Structured.ObserverSemantics.State transcript}
    {compiledHead compiledTail : List Structured.Stmt}
    {sourceOutcome :
      Functions.ObserverSemantics.Outcome
        (Functions.ObserverSemantics.State transcript)}
    {targetOutcome :
      Structured.ObserverSemantics.Outcome
        (transcript := transcript)}
    (hHead :
      NonregularStmtForward contract transcript plan finalLive
        frameBase finalMode sourceProgram sourceCtx stmt source
        targetProgram target compiledHead sourceOutcome targetOutcome
        stmtCtx) :
    BlockForward contract transcript plan finalLive frameBase finalMode
      sourceProgram sourceCtx { stmts := stmt :: rest } source
      targetProgram { stmts := compiledHead ++ compiledTail } target
      sourceOutcome targetOutcome sourceCtx := by
  rcases hHead with
    ⟨sourceFuel, targetFuel,
      hSource, hTarget, hSourceMode, hRel⟩
  have hTargetMode : targetOutcome.mode ≠ .regular :=
    hRel.target_nonregular hSourceMode
  exact
    ⟨sourceFuel + 1, targetFuel,
      Functions.Source.Effectful.Block.runOpen_cons_nonregular
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSemantics.primitiveSemantics transcript)
        sourceProgram hSource hSourceMode,
      Structured.EffectSemantics.Block.Eval.append_nonregular
        hTarget hTargetMode,
      hRel⟩

end Sequence

end AllocationObserverStatement
end Functions
end EvmCompiler
