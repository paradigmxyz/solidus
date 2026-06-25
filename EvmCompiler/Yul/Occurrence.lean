import EvmCompiler.Yul.InteractionSemantics

namespace EvmCompiler
namespace Yul
namespace YulOccurrence

inductive ExprUserCall (functionName : Name) (args : List AstExpr) :
    AstExpr → Prop where
  | here :
      ExprUserCall functionName args (.Call (.inr functionName) args)
  | callArg
      {callee : EvmYul.Operation .Yul ⊕ Name}
      {outerArgs : List AstExpr} {arg : AstExpr} :
      arg ∈ outerArgs →
        ExprUserCall functionName args arg →
          ExprUserCall functionName args (.Call callee outerArgs)

namespace ExprUserCall

private theorem list_reverse_split_of_mem
    {α : Type} {value : α} {values : List α}
    (hMem : value ∈ values) :
    ∃ (before after : List α),
      values.reverse = before ++ value :: after := by
  induction values with
  | nil =>
      cases hMem
  | cons head tail ih =>
      simp only [List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · subst head
        exact ⟨tail.reverse, [], by simp⟩
      · rcases ih hTail with ⟨before, after, hSplit⟩
        refine ⟨before, after ++ [head], ?_⟩
        simp [List.reverse_cons, hSplit, List.append_assoc]

inductive EvalArgContext (functionName : Name) (args : List AstExpr) :
    AstExpr → Prop where
  | here :
      EvalArgContext functionName args (.Call (.inr functionName) args)
  | callArg
      {callee : EvmYul.Operation .Yul ⊕ Name}
      {outerArgs : List AstExpr} {arg : AstExpr}
      {before after : List AstExpr} :
      outerArgs.reverse = before ++ arg :: after →
        EvalArgContext functionName args arg →
          EvalArgContext functionName args (.Call callee outerArgs)

theorem evalArgContext
    {functionName : Name} {args : List AstExpr} {expr : AstExpr}
    (hOccurrence : ExprUserCall functionName args expr) :
    EvalArgContext functionName args expr := by
  induction hOccurrence with
  | here =>
      exact EvalArgContext.here
  | @callArg callee outerArgs arg hMem _ ih =>
      rcases list_reverse_split_of_mem hMem with
        ⟨before, after, hSplit⟩
      exact EvalArgContext.callArg hSplit ih

theorem evalArgs_prefix_cons_succ
    (fuel : Nat) (before : List AstExpr) (arg : AstExpr)
    (after : List AstExpr) (code : Option AstContract)
    (state : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.evalArgs
        (fuel + 2 * before.length + 2)
        (before ++ arg :: after) code state =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs
          (fuel + 2 * before.length + 2) before code state)
        (fun beforeResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.evalValues (fuel + 1)
              arg code beforeResult.1)
            (fun argResult =>
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.evalArgs fuel after code
                  argResult.1)
                (fun afterResult =>
                  pure
                    (afterResult.1,
                      beforeResult.2 ++
                        argResult.2.head! :: afterResult.2)))) := by
  rw [Yul.InteractionSemantics.EvalArgs.append before (arg :: after)]
  have hResidual :
      fuel + 2 * before.length + 2 - 2 * before.length =
        fuel + 2 := by
    omega
  rw [hResidual]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs
        (fuel + 2 * before.length + 2) before code state))
  intro beforeResult _hBefore
  rw [Yul.InteractionSemantics.EvalArgs.succ_succ_cons]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalValues (fuel + 1)
        arg code beforeResult.1))
  intro argResult _hArg
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs fuel after code argResult.1))
  intro afterResult _hAfter
  change
    Simulation.Interaction.bind
      (Simulation.Interaction.done
        (.ok (afterResult.1, argResult.2.head! :: afterResult.2)))
      (fun rightResult =>
        pure (rightResult.1, beforeResult.2 ++ rightResult.2)) =
      pure
        (afterResult.1,
          beforeResult.2 ++ argResult.2.head! :: afterResult.2)
  rw [Simulation.Interaction.bind_done_ok]

theorem evalValues_callArgPrefix_succ
    (fuel : Nat)
    (callee : EvmYul.Operation .Yul ⊕ Name)
    (outerArgs before : List AstExpr) (arg : AstExpr)
    (after : List AstExpr) (code : Option AstContract)
    (state : Yul.InteractionSemantics.State)
    (hSplit : outerArgs.reverse = before ++ arg :: after) :
    Yul.InteractionSemantics.evalValues
        (fuel + 2 * before.length + 3)
        (.Call callee outerArgs) code state =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.evalArgs
          (fuel + 2 * before.length + 2) before code state)
        (fun beforeResult =>
          Simulation.Interaction.bind
            (Yul.InteractionSemantics.evalValues (fuel + 1)
              arg code beforeResult.1)
            (fun argResult =>
              Simulation.Interaction.bind
                (Yul.InteractionSemantics.evalArgs fuel after code
                  argResult.1)
                (fun afterResult =>
                  let evaluatedArgs :=
                    beforeResult.2 ++ argResult.2.head! :: afterResult.2
                  match callee with
                  | .inl prim =>
                      Yul.InteractionSemantics.primitiveSemantics.eval
                        (fuel + 2 * before.length + 2)
                        afterResult.1 prim evaluatedArgs.reverse
                  | .inr functionName =>
                      Yul.InteractionSemantics.call
                        (fuel + 2 * before.length + 2)
                        evaluatedArgs.reverse (some functionName)
                        code afterResult.1))) := by
  rw [show fuel + 2 * before.length + 3 =
      (fuel + 2 * before.length + 2) + 1 by omega]
  rw [Yul.InteractionSemantics.EvalValues.call_succ]
  rw [hSplit]
  rw [evalArgs_prefix_cons_succ fuel before arg after code state]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs
        (fuel + 2 * before.length + 2) before code state))
  intro beforeResult _hBefore
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalValues (fuel + 1)
        arg code beforeResult.1))
  intro argResult _hArg
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial
      (Yul.InteractionSemantics.evalArgs fuel after code argResult.1))
  intro afterResult _hAfter
  rfl

end ExprUserCall

mutual
  inductive StmtUserCall (functionName : Name) (args : List AstExpr) :
      AstStmt → Prop where
    | block {body : List AstStmt} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args (.Block body)
    | letValue {names : List Name} {value : AstExpr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args (.Let names (some value))
    | assignValue {names : List Name} {value : AstExpr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args (.Assign names value)
    | exprStmt {value : AstExpr} :
        ExprUserCall functionName args value →
          StmtUserCall functionName args (.ExprStmtCall value)
    | switchScrutinee
        {scrutinee : AstExpr} {cases : List (Word × List AstStmt)}
        {defaultBody : List AstStmt} :
        ExprUserCall functionName args scrutinee →
          StmtUserCall functionName args
            (.Switch scrutinee cases defaultBody)
    | switchCase
        {scrutinee : AstExpr} {cases : List (Word × List AstStmt)}
        {defaultBody : List AstStmt} :
        CaseListUserCall functionName args cases →
          StmtUserCall functionName args
            (.Switch scrutinee cases defaultBody)
    | switchDefault
        {scrutinee : AstExpr} {cases : List (Word × List AstStmt)}
        {defaultBody : List AstStmt} :
        StmtListUserCall functionName args defaultBody →
          StmtUserCall functionName args
            (.Switch scrutinee cases defaultBody)
    | forCondition
        {condition : AstExpr} {post body : List AstStmt} :
        ExprUserCall functionName args condition →
          StmtUserCall functionName args (.For condition post body)
    | forPost
        {condition : AstExpr} {post body : List AstStmt} :
        StmtListUserCall functionName args post →
          StmtUserCall functionName args (.For condition post body)
    | forBody
        {condition : AstExpr} {post body : List AstStmt} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args (.For condition post body)
    | ifCondition {condition : AstExpr} {body : List AstStmt} :
        ExprUserCall functionName args condition →
          StmtUserCall functionName args (.If condition body)
    | ifBody {condition : AstExpr} {body : List AstStmt} :
        StmtListUserCall functionName args body →
          StmtUserCall functionName args (.If condition body)

  inductive StmtListUserCall (functionName : Name) (args : List AstExpr) :
      List AstStmt → Prop where
    | head {stmt : AstStmt} {rest : List AstStmt} :
        StmtUserCall functionName args stmt →
          StmtListUserCall functionName args (stmt :: rest)
    | tail {stmt : AstStmt} {rest : List AstStmt} :
        StmtListUserCall functionName args rest →
          StmtListUserCall functionName args (stmt :: rest)

  inductive CaseListUserCall (functionName : Name) (args : List AstExpr) :
      List (Word × List AstStmt) → Prop where
    | head {value : Word} {body : List AstStmt}
        {rest : List (Word × List AstStmt)} :
        StmtListUserCall functionName args body →
          CaseListUserCall functionName args ((value, body) :: rest)
    | tail {head : Word × List AstStmt}
        {rest : List (Word × List AstStmt)} :
        CaseListUserCall functionName args rest →
          CaseListUserCall functionName args (head :: rest)
end

namespace StmtListUserCall

def continueAfterPrefix
    (fuel : Nat) (rest : List AstStmt)
    (code : Option AstContract)
    (state : Yul.InteractionSemantics.State) :
    Yul.InteractionSemantics.Open Yul.InteractionSemantics.State :=
  match state with
  | .Ok _ _ => Yul.InteractionSemantics.execSeq fuel rest code state
  | .OutOfFuel | .Checkpoint _ => pure state

theorem exists_split_stmt
    {functionName : Name} {args : List AstExpr} {stmts : List AstStmt}
    (hOccurrence : StmtListUserCall functionName args stmts) :
    ∃ (pre : List AstStmt) (stmt : AstStmt) (suffix : List AstStmt),
      stmts = pre ++ stmt :: suffix ∧
        StmtUserCall functionName args stmt := by
  induction stmts with
  | nil =>
      cases hOccurrence
  | cons head rest ih =>
      cases hOccurrence with
      | head hStmt =>
          exact ⟨[], head, rest, rfl, hStmt⟩
      | tail hTail =>
          rcases ih hTail with ⟨pre, stmt, suffix, hSplit, hStmt⟩
          exact ⟨head :: pre, stmt, suffix, by simp [hSplit], hStmt⟩

theorem of_split_stmt
    {functionName : Name} {args : List AstExpr}
    {pre suffix : List AstStmt} {stmt : AstStmt}
    (hStmt : StmtUserCall functionName args stmt) :
    StmtListUserCall functionName args (pre ++ stmt :: suffix) := by
  induction pre with
  | nil =>
      exact StmtListUserCall.head hStmt
  | cons head rest ih =>
      exact StmtListUserCall.tail ih

theorem append_right
    {functionName : Name} {args : List AstExpr}
    {pre : List AstStmt} (suffix : List AstStmt)
    (hOccurrence : StmtListUserCall functionName args pre) :
    StmtListUserCall functionName args (pre ++ suffix) := by
  induction pre with
  | nil =>
      cases hOccurrence
  | cons head rest ih =>
      cases hOccurrence with
      | head hStmt =>
          exact StmtListUserCall.head hStmt
      | tail hTail =>
          exact StmtListUserCall.tail (ih hTail)

theorem execSeq_prefix_cons_succ
    (fuel : Nat) (pre : List AstStmt) (stmt : AstStmt)
    (suffix : List AstStmt) (code : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) :
    Yul.InteractionSemantics.execSeq (fuel + pre.length + 1)
        (pre ++ stmt :: suffix) code (.Ok shared vars) =
      Simulation.Interaction.bind
        (Yul.InteractionSemantics.execSeq (fuel + pre.length + 1)
          pre code (.Ok shared vars))
        (fun stateAfterPre =>
          continueAfterPrefix (fuel + 1) (stmt :: suffix)
            code stateAfterPre) := by
  induction pre generalizing shared vars with
  | nil =>
      rw [List.nil_append, List.length_nil, Nat.add_zero]
      rw [Yul.InteractionSemantics.ExecSeq.nil_succ]
      rfl
  | cons head rest ih =>
      rw [List.cons_append, List.length_cons]
      rw [show fuel + (rest.length + 1) + 1 =
          (fuel + rest.length + 1) + 1 by omega]
      rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
      rw [Yul.InteractionSemantics.ExecSeq.cons_succ]
      rw [Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Yul.InteractionSemantics.exec (fuel + rest.length + 1)
            head code (.Ok shared vars)))
      intro stateAfterHead _hDone
      cases stateAfterHead with
      | Ok sharedAfter varsAfter =>
          exact ih sharedAfter varsAfter
      | OutOfFuel =>
          rfl
      | Checkpoint jump =>
          cases jump <;> rfl

theorem exists_split_stmt_execSeq_prefix
    {functionName : Name} {args : List AstExpr} {stmts : List AstStmt}
    (hOccurrence : StmtListUserCall functionName args stmts)
    (fuel : Nat) (code : Option AstContract)
    (shared : EvmYul.SharedState .Yul)
    (vars : EvmYul.Yul.VarStore) :
    ∃ (pre : List AstStmt) (stmt : AstStmt) (suffix : List AstStmt),
      stmts = pre ++ stmt :: suffix ∧
        StmtUserCall functionName args stmt ∧
          Yul.InteractionSemantics.execSeq
              (fuel + pre.length + 1) stmts code (.Ok shared vars) =
            Simulation.Interaction.bind
              (Yul.InteractionSemantics.execSeq
                (fuel + pre.length + 1) pre code (.Ok shared vars))
              (fun stateAfterPre =>
                continueAfterPrefix (fuel + 1) (stmt :: suffix)
                  code stateAfterPre) := by
  rcases exists_split_stmt hOccurrence with
    ⟨pre, stmt, suffix, hSplit, hStmt⟩
  subst stmts
  exact
    ⟨pre, stmt, suffix, rfl, hStmt,
      execSeq_prefix_cons_succ fuel pre stmt suffix code shared vars⟩

end StmtListUserCall

end YulOccurrence
end Yul
end EvmCompiler
