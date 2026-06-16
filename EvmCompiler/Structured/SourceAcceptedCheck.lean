import EvmCompiler.Structured.Syntax

namespace EvmCompiler
namespace Structured
namespace SourceAcceptedCheck

namespace ProcList

def namesUnique? (procs : List Proc) : Bool :=
  decide (procs.map Proc.name).Nodup

def contains? (procs : List Proc) (name : Name) : Bool :=
  procs.any fun proc => proc.name == name

theorem namesUnique_of_check {procs : List Proc}
    (hCheck : namesUnique? procs = true) :
    Structured.ProcList.NamesUnique procs := by
  simpa [namesUnique?, Structured.ProcList.NamesUnique] using
    (of_decide_eq_true hCheck)

theorem contains_of_check {procs : List Proc} {name : Name}
    (hCheck : contains? procs name = true) :
    Structured.ProcList.contains procs name := by
  obtain ⟨proc, hMem, hName⟩ :=
    List.any_eq_true.mp hCheck
  exact ⟨proc, hMem, beq_iff_eq.mp hName⟩

end ProcList

mutual
  def Block.wf? (canBreak canContinue canLeave : Bool) :
      Block → Bool
    | ⟨stmts⟩ => StmtList.wf? canBreak canContinue canLeave stmts

  def Stmt.wf? (canBreak canContinue canLeave : Bool) :
      Stmt → Bool
    | .code _ => true
    | .if_ _ body => Block.wf? canBreak canContinue canLeave body
    | .switch _ cases defaultBody =>
        CaseList.wf? canBreak canContinue canLeave cases &&
          Default.wf? canBreak canContinue canLeave defaultBody
    | .for_ init _ post body =>
        Block.wf? false false canLeave init &&
          (Block.wf? false false canLeave post &&
            Block.wf? true true canLeave body)
    | .brk => canBreak
    | .cont => canContinue
    | .leave => canLeave
    | .call _ => true
    | .terminal _ => true

  def StmtList.wf? (canBreak canContinue canLeave : Bool) :
      List Stmt → Bool
    | [] => true
    | stmt :: rest =>
        Stmt.wf? canBreak canContinue canLeave stmt &&
          StmtList.wf? canBreak canContinue canLeave rest

  def CaseList.wf? (canBreak canContinue canLeave : Bool) :
      List (Word × Block) → Bool
    | [] => true
    | (_, body) :: rest =>
        Block.wf? canBreak canContinue canLeave body &&
          CaseList.wf? canBreak canContinue canLeave rest

  def Default.wf? (canBreak canContinue canLeave : Bool) :
      Option Block → Bool
    | none => true
    | some body => Block.wf? canBreak canContinue canLeave body
end

namespace Proc

def wf? (proc : Proc) : Bool :=
  decide (proc.argc ≤ 16) &&
    (decide (proc.retc < 16) && Block.wf? false false true proc.body)

end Proc

namespace ProcList

def wf? : List Proc → Bool
  | [] => true
  | proc :: rest => Proc.wf? proc && wf? rest

end ProcList

mutual
  def Block.callsResolved? (procs : List Proc) : Block → Bool
    | ⟨stmts⟩ => StmtList.callsResolved? procs stmts

  def Stmt.callsResolved? (procs : List Proc) : Stmt → Bool
    | .code _ => true
    | .if_ _ body => Block.callsResolved? procs body
    | .switch _ cases defaultBody =>
        CaseList.callsResolved? procs cases &&
          Default.callsResolved? procs defaultBody
    | .for_ init _ post body =>
        Block.callsResolved? procs init &&
          (Block.callsResolved? procs post &&
            Block.callsResolved? procs body)
    | .brk | .cont | .leave | .terminal _ => true
    | .call name => ProcList.contains? procs name

  def StmtList.callsResolved? (procs : List Proc) : List Stmt → Bool
    | [] => true
    | stmt :: rest =>
        Stmt.callsResolved? procs stmt &&
          StmtList.callsResolved? procs rest

  def CaseList.callsResolved? (procs : List Proc) :
      List (Word × Block) → Bool
    | [] => true
    | (_, body) :: rest =>
        Block.callsResolved? procs body &&
          CaseList.callsResolved? procs rest

  def Default.callsResolved? (procs : List Proc) :
      Option Block → Bool
    | none => true
    | some body => Block.callsResolved? procs body
end

namespace ProcList

def callsResolved? (procs : List Proc) : Bool :=
  procs.all fun proc => Block.callsResolved? procs proc.body

end ProcList

namespace Program

def wf? (program : Program) : Bool :=
  ProcList.namesUnique? program.procs &&
    (ProcList.wf? program.procs &&
      (ProcList.callsResolved? program.procs &&
        (Block.callsResolved? program.procs program.body &&
          Block.wf? false false false program.body)))

end Program

theorem Block.wf_of_check {canBreak canContinue canLeave : Bool}
    {block : Block}
    (hCheck : Block.wf? canBreak canContinue canLeave block = true) :
    block.WF canBreak canContinue canLeave := by
  exact
    Block.rec
      (motive_1 := fun block =>
        ∀ canBreak canContinue canLeave,
          Block.wf? canBreak canContinue canLeave block = true →
            block.WF canBreak canContinue canLeave)
      (motive_2 := fun stmt =>
        ∀ canBreak canContinue canLeave,
          Stmt.wf? canBreak canContinue canLeave stmt = true →
            stmt.WF canBreak canContinue canLeave)
      (motive_3 := fun stmts =>
        ∀ canBreak canContinue canLeave,
          StmtList.wf? canBreak canContinue canLeave stmts = true →
            Block.WF canBreak canContinue canLeave { stmts := stmts })
      (motive_4 := fun cases =>
        ∀ canBreak canContinue canLeave,
          CaseList.wf? canBreak canContinue canLeave cases = true →
            ∀ value body, (value, body) ∈ cases →
              body.WF canBreak canContinue canLeave)
      (motive_5 := fun defaultBody =>
        ∀ canBreak canContinue canLeave,
          Default.wf? canBreak canContinue canLeave defaultBody = true →
            ∀ body, defaultBody = some body →
              body.WF canBreak canContinue canLeave)
      (motive_6 := fun pair =>
        ∀ canBreak canContinue canLeave,
          Block.wf? canBreak canContinue canLeave pair.2 = true →
            pair.2.WF canBreak canContinue canLeave)
      (fun _ hStmts _ _ _ h => hStmts _ _ _ h)
      (fun _ _ _ _ _ => .code)
      (fun _ _ hBody _ _ _ h => .if_ (hBody _ _ _ h))
      (fun _ cases defaultBody hCases hDefault
          canBreak canContinue canLeave h => by
        have hParts :
            CaseList.wf? canBreak canContinue canLeave cases = true ∧
              Default.wf? canBreak canContinue canLeave defaultBody = true :=
          by simpa [Stmt.wf?] using h
        exact
          .switch
            (hCases canBreak canContinue canLeave hParts.1)
            (hDefault canBreak canContinue canLeave hParts.2))
      (fun init _ post body hInit hPost hBody _ _ canLeave h => by
        have hParts :
            Block.wf? false false canLeave init = true ∧
              (Block.wf? false false canLeave post &&
                Block.wf? true true canLeave body) = true :=
          by simpa [Stmt.wf?] using h
        have hRest :
            Block.wf? false false canLeave post = true ∧
              Block.wf? true true canLeave body = true :=
          by simpa using hParts.2
        exact
          .for_
            (hInit false false canLeave hParts.1)
            (hPost false false canLeave hRest.1)
            (hBody true true canLeave hRest.2))
      (fun canBreak _ _ h => .brk (by simpa using h))
      (fun _ canContinue _ h => .cont (by simpa using h))
      (fun _ _ canLeave h => .leave (by simpa using h))
      (fun _ _ _ _ _ => .call)
      (fun _ _ _ _ _ => .terminal)
      (fun _ _ _ _ => .nil)
      (fun head tail hHead hTail canBreak canContinue canLeave h => by
        have hParts :
            Stmt.wf? canBreak canContinue canLeave head = true ∧
              StmtList.wf? canBreak canContinue canLeave tail = true :=
          by simpa [StmtList.wf?] using h
        exact
          .cons
            (hHead canBreak canContinue canLeave hParts.1)
            (hTail canBreak canContinue canLeave hParts.2))
      (fun _ _ _ _ _ _ hMem => by simp at hMem)
      (fun head rest hHead hRest canBreak canContinue canLeave h
          value body hMem => by
        have hParts :
            Block.wf? canBreak canContinue canLeave head.2 = true ∧
              CaseList.wf? canBreak canContinue canLeave rest = true :=
          by simpa [CaseList.wf?] using h
        rcases List.mem_cons.mp hMem with hFirst | hTail
        · cases hFirst
          exact hHead canBreak canContinue canLeave hParts.1
        · exact
            hRest canBreak canContinue canLeave hParts.2
              value body hTail)
      (fun _ _ _ _ _ hBody => by simp at hBody)
      (fun _ hBody canBreak canContinue canLeave h _ hEq => by
        cases hEq
        exact hBody canBreak canContinue canLeave h)
      (fun _ _ hBody canBreak canContinue canLeave h =>
        hBody canBreak canContinue canLeave h)
      block canBreak canContinue canLeave hCheck

theorem Proc.wf_of_check {proc : Proc}
    (hCheck : Proc.wf? proc = true) :
    proc.WF := by
  have hParts :
      decide (proc.argc ≤ 16) = true ∧
        (decide (proc.retc < 16) &&
          Block.wf? false false true proc.body) = true :=
    by simpa [Proc.wf?] using hCheck
  have hRest :
      decide (proc.retc < 16) = true ∧
        Block.wf? false false true proc.body = true :=
    by simpa using hParts.2
  exact
    ⟨of_decide_eq_true hParts.1,
      of_decide_eq_true hRest.1,
      Block.wf_of_check hRest.2⟩

theorem ProcList.wf_of_check :
    ∀ {procs : List Proc},
      ProcList.wf? procs = true → Structured.ProcList.WF procs
  | [], _ => by trivial
  | proc :: rest, hCheck => by
      have hParts :
          Proc.wf? proc = true ∧ ProcList.wf? rest = true :=
        by simpa [ProcList.wf?] using hCheck
      exact
        ⟨Proc.wf_of_check hParts.1,
          ProcList.wf_of_check hParts.2⟩

theorem Block.callsResolved_of_check {procs : List Proc}
    {block : Block}
    (hCheck : Block.callsResolved? procs block = true) :
    Structured.ProcList.BlockCallsResolved procs block := by
  exact
    Block.rec
      (motive_1 := fun block =>
        Block.callsResolved? procs block = true →
          Structured.ProcList.BlockCallsResolved procs block)
      (motive_2 := fun stmt =>
        Stmt.callsResolved? procs stmt = true →
          Structured.ProcList.StmtCallsResolved procs stmt)
      (motive_3 := fun stmts =>
        StmtList.callsResolved? procs stmts = true →
          Structured.ProcList.StmtListCallsResolved procs stmts)
      (motive_4 := fun cases =>
        CaseList.callsResolved? procs cases = true →
          ∀ value body, (value, body) ∈ cases →
            Structured.ProcList.BlockCallsResolved procs body)
      (motive_5 := fun defaultBody =>
        Default.callsResolved? procs defaultBody = true →
          ∀ body, defaultBody = some body →
            Structured.ProcList.BlockCallsResolved procs body)
      (motive_6 := fun pair =>
        Block.callsResolved? procs pair.2 = true →
          Structured.ProcList.BlockCallsResolved procs pair.2)
      (fun _ hStmts h => .mk (hStmts h))
      (fun _ _ => .code)
      (fun _ _ hBody h => .if_ (hBody h))
      (fun _ cases defaultBody hCases hDefault h => by
        have hParts :
            CaseList.callsResolved? procs cases = true ∧
              Default.callsResolved? procs defaultBody = true :=
          by simpa [Stmt.callsResolved?] using h
        exact .switch (hCases hParts.1) (hDefault hParts.2))
      (fun init _ post body hInit hPost hBody h => by
        have hParts :
            Block.callsResolved? procs init = true ∧
              (Block.callsResolved? procs post &&
                Block.callsResolved? procs body) = true :=
          by simpa [Stmt.callsResolved?] using h
        have hRest :
            Block.callsResolved? procs post = true ∧
              Block.callsResolved? procs body = true :=
          by simpa using hParts.2
        exact .for_ (hInit hParts.1) (hPost hRest.1) (hBody hRest.2))
      (fun _ => .brk)
      (fun _ => .cont)
      (fun _ => .leave)
      (fun _ h => .call (ProcList.contains_of_check h))
      (fun _ _ => .terminal)
      (fun _ => .nil)
      (fun head tail hHead hTail h => by
        have hParts :
            Stmt.callsResolved? procs head = true ∧
              StmtList.callsResolved? procs tail = true :=
          by simpa [StmtList.callsResolved?] using h
        exact .cons (hHead hParts.1) (hTail hParts.2))
      (fun _ _ _ hMem => by simp at hMem)
      (fun head rest hHead hRest h value body hMem => by
        have hParts :
            Block.callsResolved? procs head.2 = true ∧
              CaseList.callsResolved? procs rest = true :=
          by simpa [CaseList.callsResolved?] using h
        rcases List.mem_cons.mp hMem with hFirst | hTail
        · cases hFirst
          exact hHead hParts.1
        · exact hRest hParts.2 value body hTail)
      (fun _ _ hBody => by simp at hBody)
      (fun _ hBody h _ hEq => by cases hEq; exact hBody h)
      (fun _ _ hBody h => hBody h)
      block hCheck

theorem ProcList.callsResolved_of_check {procs : List Proc}
    (hCheck : ProcList.callsResolved? procs = true) :
    Structured.ProcList.CallsResolved procs := by
  intro proc hMem
  exact
    Block.callsResolved_of_check
      ((List.all_eq_true.mp hCheck) proc hMem)

theorem Program.wf_of_check {program : Program}
    (hCheck : Program.wf? program = true) :
    program.WF := by
  have hParts :
      ProcList.namesUnique? program.procs = true ∧
        (ProcList.wf? program.procs &&
          (ProcList.callsResolved? program.procs &&
            (Block.callsResolved? program.procs program.body &&
              Block.wf? false false false program.body))) = true :=
    by simpa [Program.wf?] using hCheck
  have hRest :
      ProcList.wf? program.procs = true ∧
        (ProcList.callsResolved? program.procs &&
          (Block.callsResolved? program.procs program.body &&
            Block.wf? false false false program.body)) = true :=
    by simpa using hParts.2
  have hCalls :
      ProcList.callsResolved? program.procs = true ∧
        (Block.callsResolved? program.procs program.body &&
          Block.wf? false false false program.body) = true :=
    by simpa using hRest.2
  have hBody :
      Block.callsResolved? program.procs program.body = true ∧
        Block.wf? false false false program.body = true :=
    by simpa using hCalls.2
  exact
    ⟨ProcList.namesUnique_of_check hParts.1,
      ProcList.wf_of_check hRest.1,
      ProcList.callsResolved_of_check hCalls.1,
      Block.callsResolved_of_check hBody.1,
      Block.wf_of_check hBody.2⟩

end SourceAcceptedCheck
end Structured
end EvmCompiler
