import EvmCompiler.Functions.Syntax

/-!
Backward liveness for the Functions-to-allocated-Locals boundary.

This module owns only source-level dataflow.  It does not choose stack slots,
emit shuffles, inspect lower-layer code, or interpret observer effects.
`Valid` is the stable relational interface; `analyzeBlock?` is one checked
implementation of it.
-/

namespace EvmCompiler
namespace Functions
namespace AllocationLiveness

abbrev LiveSet := Finset Name

namespace LiveSet

def eraseMany (names : List Name) (live : LiveSet) : LiveSet :=
  names.foldl (fun current name => current.erase name) live

theorem mem_eraseMany_iff
    {name : Name} {names : List Name} {live : LiveSet} :
    name ∈ eraseMany names live ↔ name ∈ live ∧ name ∉ names := by
  induction names generalizing live with
  | nil => simp [eraseMany]
  | cons head tail ih =>
      change
        name ∈ eraseMany tail (live.erase head) ↔
          name ∈ live ∧ name ∉ head :: tail
      rw [ih]
      simp only [Finset.mem_erase, List.mem_cons, not_or]
      aesop

end LiveSet

mutual
  def Expr.uses {results : Nat} : Functions.Expr results → LiveSet
    | .lit _ => ∅
    | .var name => {name}
    | .code _ => ∅
    | .prim _ args => ExprSeq.uses args

  def ExprSeq.uses {results : Nat} : Locals.ExprSeq results → LiveSet
    | .nil => ∅
    | .cons head tail => Expr.uses head ∪ ExprSeq.uses tail
end

def ExprList.uses (args : List (Functions.Expr 1)) : LiveSet :=
  args.foldl (fun live arg => live ∪ Expr.uses arg) ∅

/-- Live values demanded by each possible source-level continuation. -/
structure Demand where
  normal : LiveSet
  brk : LiveSet := ∅
  cont : LiveSet := ∅
  leave : LiveSet := ∅
  deriving DecidableEq

namespace Demand

def withNormal (demand : Demand) (normal : LiveSet) : Demand :=
  { demand with normal := normal }

end Demand

set_option autoImplicit true in
mutual
  inductive Block.Valid : Demand → Block → LiveSet → Prop where
    | mk
        (hStmts : StmtList.Valid demand stmts liveIn) :
        Block.Valid demand { stmts := stmts } liveIn

  inductive StmtList.Valid : Demand → List Stmt → LiveSet → Prop where
    | nil : StmtList.Valid demand [] demand.normal
    | cons
        (hRest : StmtList.Valid demand rest restLive)
        (hStmt : Stmt.Valid (demand.withNormal restLive) stmt liveIn) :
        StmtList.Valid demand (stmt :: rest) liveIn

  inductive CaseList.Valid :
      Demand → List (Word × Block) → LiveSet → Prop where
    | nil : CaseList.Valid demand [] ∅
    | cons
        (hBody : Block.Valid demand body bodyLive)
        (hRest : CaseList.Valid demand rest restLive) :
        CaseList.Valid demand ((value, body) :: rest) (bodyLive ∪ restLive)

  inductive Default.Valid : Demand → Option Block → LiveSet → Prop where
    | none : Default.Valid demand none demand.normal
    | some
        (hBody : Block.Valid demand body liveIn) :
        Default.Valid demand (some body) liveIn

  inductive Stmt.Valid : Demand → Stmt → LiveSet → Prop where
    | expr :
        Stmt.Valid demand (.expr expr) (Expr.uses expr ∪ demand.normal)
    | let_ :
        Stmt.Valid demand (.let_ name value)
          (Expr.uses value ∪ demand.normal.erase name)
    | assign :
        Stmt.Valid demand (.assign name value)
          ((Expr.uses value ∪ demand.normal.erase name) ∪ {name})
    | block
        (hBody : Block.Valid demand body liveIn) :
        Stmt.Valid demand (.block body) liveIn
    | if_
        (hBody : Block.Valid demand body bodyLive) :
        Stmt.Valid demand (.if_ condition body)
          (Expr.uses condition ∪ (demand.normal ∪ bodyLive))
    | switch
        (hCases : CaseList.Valid demand cases caseLive)
        (hDefault : Default.Valid demand defaultBody defaultLive) :
        Stmt.Valid demand (.switch scrutinee cases defaultBody)
          (Expr.uses scrutinee ∪ (caseLive ∪ defaultLive))
    | for_
        (hPost : Block.Valid (demand.withNormal headLive) post postLive)
        (hBody :
          Block.Valid
            { normal := postLive
              brk := demand.normal
              cont := postLive
              leave := demand.leave }
            body bodyLive)
        (hClosed :
          Expr.uses condition ∪ (demand.normal ∪ bodyLive) ⊆ headLive)
        (hInit : Block.Valid (demand.withNormal headLive) init liveIn) :
        Stmt.Valid demand (.for_ init condition post body) liveIn
    | brk : Stmt.Valid demand .brk demand.brk
    | cont : Stmt.Valid demand .cont demand.cont
    | leave : Stmt.Valid demand .leave demand.leave
    | call :
        Stmt.Valid demand (.call targets functionName args)
          ((ExprList.uses args ∪
              LiveSet.eraseMany targets demand.normal) ∪
            targets.toFinset)
    | terminal : Stmt.Valid demand (.terminal kind) ∅
    | terminalArgs :
        Stmt.Valid demand (.terminalArgs kind args) (ExprSeq.uses args)
end

namespace Close

/--
Grow a candidate until `step candidate` is included in it.  Returning `none`
is an honest analysis failure; generated fixed-point evidence is never a
caller-supplied premise.
-/
def run (fuel : Nat) (step : LiveSet → Option LiveSet)
    (current : LiveSet) : Option LiveSet :=
  match step current with
  | none => none
  | some next =>
      let grown := current ∪ next
      if next ⊆ current then
        some current
      else
        match fuel with
        | 0 => none
        | fuel + 1 => run fuel step grown

theorem run_sound
    {fuel : Nat} {step : LiveSet → Option LiveSet}
    {initial result : LiveSet}
    (hRun : run fuel step initial = some result) :
    ∃ next, step result = some next ∧ next ⊆ result := by
  induction fuel generalizing initial with
  | zero =>
      cases hStep : step initial with
      | none => simp [run, hStep] at hRun
      | some next =>
          by_cases hStable : next ⊆ initial
          · have hEq : initial = result := by
              simpa [run, hStep, hStable] using hRun
            subst result
            exact ⟨next, hStep, hStable⟩
          · simp [run, hStep, hStable] at hRun
  | succ fuel ih =>
      cases hStep : step initial with
      | none => simp [run, hStep] at hRun
      | some next =>
          by_cases hStable : next ⊆ initial
          · have hEq : initial = result := by
              simpa [run, hStep, hStable] using hRun
            subst result
            exact ⟨next, hStep, hStable⟩
          · have hRecur :
                run fuel step (initial ∪ next) = some result := by
              rw [run] at hRun
              simpa only [hStep, hStable, ↓reduceIte] using hRun
            exact ih hRecur

end Close

structure LoopResult where
  liveIn : LiveSet
  headLive : LiveSet
  postLive : LiveSet
  bodyLive : LiveSet
  deriving DecidableEq

mutual
  def analyzeBlockFuel
      (fuel : Nat) (demand : Demand) (block : Block) : Option LiveSet :=
    match fuel with
    | 0 => none
    | fuel + 1 => analyzeStmtListFuel fuel demand block.stmts

  def analyzeStmtListFuel
      (fuel : Nat) (demand : Demand) (stmts : List Stmt) : Option LiveSet :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match stmts with
        | [] => some demand.normal
        | stmt :: rest =>
            (analyzeStmtListFuel fuel demand rest).bind fun restLive =>
              analyzeStmtFuel fuel (demand.withNormal restLive) stmt

  def analyzeCasesFuel
      (fuel : Nat) (demand : Demand)
      (cases : List (Word × Block)) : Option LiveSet :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match cases with
        | [] => some ∅
        | (_, body) :: rest =>
            (analyzeBlockFuel fuel demand body).bind fun bodyLive =>
              (analyzeCasesFuel fuel demand rest).bind fun restLive =>
                some (bodyLive ∪ restLive)

  def analyzeDefaultFuel
      (fuel : Nat) (demand : Demand)
      (body? : Option Block) : Option LiveSet :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match body? with
        | none => some demand.normal
        | some body => analyzeBlockFuel fuel demand body

  def analyzeStmtFuel
      (fuel : Nat) (demand : Demand) (stmt : Stmt) : Option LiveSet :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match stmt with
        | .expr expr => some (Expr.uses expr ∪ demand.normal)
        | .let_ name value =>
            some (Expr.uses value ∪ demand.normal.erase name)
        | .assign name value =>
            some ((Expr.uses value ∪ demand.normal.erase name) ∪ {name})
        | .block body => analyzeBlockFuel fuel demand body
        | .if_ cond body =>
            (analyzeBlockFuel fuel demand body).bind fun bodyLive =>
              some (Expr.uses cond ∪ (demand.normal ∪ bodyLive))
        | .switch scrutinee cases defaultBody =>
            (analyzeCasesFuel fuel demand cases).bind fun caseLive =>
              (analyzeDefaultFuel fuel demand defaultBody).bind
                fun defaultLive =>
                  some (Expr.uses scrutinee ∪ (caseLive ∪ defaultLive))
        | .for_ init cond post body =>
            (analyzeLoopFuel fuel demand init cond post body).map
              LoopResult.liveIn
        | .brk => some demand.brk
        | .cont => some demand.cont
        | .leave => some demand.leave
        | .call targets _ args =>
            some
              ((ExprList.uses args ∪
                  LiveSet.eraseMany targets demand.normal) ∪
                targets.toFinset)
        | .terminal _ => some ∅
        | .terminalArgs _ args => some (ExprSeq.uses args)

  def analyzeLoopFuel
      (fuel : Nat) (demand : Demand)
      (init : Block) (cond : Expr 1) (post body : Block) :
      Option LoopResult :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        let step := fun headLive =>
          (analyzeBlockFuel fuel
              (demand.withNormal headLive) post).bind fun postLive =>
            (analyzeBlockFuel fuel
                { normal := postLive
                  brk := demand.normal
                  cont := postLive
                  leave := demand.leave }
                body).bind fun bodyLive =>
              some (Expr.uses cond ∪ (demand.normal ∪ bodyLive))
        let seed := Expr.uses cond ∪ demand.normal
        (Close.run fuel step seed).bind fun headLive =>
          (analyzeBlockFuel fuel
              (demand.withNormal headLive) post).bind fun postLive =>
            (analyzeBlockFuel fuel
                { normal := postLive
                  brk := demand.normal
                  cont := postLive
                  leave := demand.leave }
                body).bind fun bodyLive =>
              (analyzeBlockFuel fuel
                  (demand.withNormal headLive) init).bind fun liveIn =>
                some { liveIn, headLive, postLive, bodyLive }
end

mutual
  theorem analyzeBlockFuel_sound
      {fuel : Nat} {demand : Demand} {block : Block} {liveIn : LiveSet}
      (hAnalyze : analyzeBlockFuel fuel demand block = some liveIn) :
      Block.Valid demand block liveIn := by
    cases fuel with
    | zero => simp [analyzeBlockFuel] at hAnalyze
    | succ fuel =>
        rcases block with ⟨stmts⟩
        apply Block.Valid.mk
        apply analyzeStmtListFuel_sound
        simpa only [analyzeBlockFuel] using hAnalyze

  theorem analyzeStmtListFuel_sound
      {fuel : Nat} {demand : Demand} {stmts : List Stmt} {liveIn : LiveSet}
      (hAnalyze : analyzeStmtListFuel fuel demand stmts = some liveIn) :
      StmtList.Valid demand stmts liveIn := by
    cases fuel with
    | zero => simp [analyzeStmtListFuel] at hAnalyze
    | succ fuel =>
        cases stmts with
        | nil =>
            have hEq : demand.normal = liveIn := by
              simpa only [analyzeStmtListFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .nil
        | cons stmt rest =>
            simp only [analyzeStmtListFuel] at hAnalyze
            obtain ⟨restLive, hRest, hStmt⟩ :=
              Option.bind_eq_some_iff.mp hAnalyze
            exact
              .cons
                (analyzeStmtListFuel_sound hRest)
                (analyzeStmtFuel_sound hStmt)

  theorem analyzeCasesFuel_sound
      {fuel : Nat} {demand : Demand} {cases : List (Word × Block)}
      {liveIn : LiveSet}
      (hAnalyze : analyzeCasesFuel fuel demand cases = some liveIn) :
      CaseList.Valid demand cases liveIn := by
    cases fuel with
    | zero => simp [analyzeCasesFuel] at hAnalyze
    | succ fuel =>
        cases cases with
        | nil =>
            have hEq : (∅ : LiveSet) = liveIn := by
              simpa only [analyzeCasesFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .nil
        | cons entry rest =>
            rcases entry with ⟨value, body⟩
            simp only [analyzeCasesFuel] at hAnalyze
            obtain ⟨bodyLive, hBody, hTail⟩ :=
              Option.bind_eq_some_iff.mp hAnalyze
            obtain ⟨restLive, hRest, hResult⟩ :=
              Option.bind_eq_some_iff.mp hTail
            have hEq : bodyLive ∪ restLive = liveIn := by
              simpa only [Option.some.injEq] using hResult
            subst liveIn
            exact
              .cons
                (analyzeBlockFuel_sound hBody)
                (analyzeCasesFuel_sound hRest)

  theorem analyzeDefaultFuel_sound
      {fuel : Nat} {demand : Demand} {body? : Option Block}
      {liveIn : LiveSet}
      (hAnalyze : analyzeDefaultFuel fuel demand body? = some liveIn) :
      Default.Valid demand body? liveIn := by
    cases fuel with
    | zero => simp [analyzeDefaultFuel] at hAnalyze
    | succ fuel =>
        cases body? with
        | none =>
            have hEq : demand.normal = liveIn := by
              simpa only [analyzeDefaultFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .none
        | some body =>
            apply Default.Valid.some
            apply analyzeBlockFuel_sound
            simpa only [analyzeDefaultFuel] using hAnalyze

  theorem analyzeStmtFuel_sound
      {fuel : Nat} {demand : Demand} {stmt : Stmt} {liveIn : LiveSet}
      (hAnalyze : analyzeStmtFuel fuel demand stmt = some liveIn) :
      Stmt.Valid demand stmt liveIn := by
    cases fuel with
    | zero => simp [analyzeStmtFuel] at hAnalyze
    | succ fuel =>
        cases stmt with
        | expr expr =>
            have hEq : Expr.uses expr ∪ demand.normal = liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .expr
        | let_ name value =>
            have hEq :
                Expr.uses value ∪ demand.normal.erase name = liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .let_
        | assign name value =>
            have hEq :
                (Expr.uses value ∪ demand.normal.erase name) ∪ {name} =
                  liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .assign
        | block body =>
            apply Stmt.Valid.block
            apply analyzeBlockFuel_sound
            simpa only [analyzeStmtFuel] using hAnalyze
        | if_ cond body =>
            simp only [analyzeStmtFuel] at hAnalyze
            obtain ⟨bodyLive, hBody, hResult⟩ :=
              Option.bind_eq_some_iff.mp hAnalyze
            have hEq :
                Expr.uses cond ∪ (demand.normal ∪ bodyLive) = liveIn := by
              simpa only [Option.some.injEq] using hResult
            subst liveIn
            exact .if_ (analyzeBlockFuel_sound hBody)
        | switch scrutinee cases defaultBody =>
            simp only [analyzeStmtFuel] at hAnalyze
            obtain ⟨caseLive, hCases, hTail⟩ :=
              Option.bind_eq_some_iff.mp hAnalyze
            obtain ⟨defaultLive, hDefault, hResult⟩ :=
              Option.bind_eq_some_iff.mp hTail
            have hEq :
                Expr.uses scrutinee ∪ (caseLive ∪ defaultLive) = liveIn := by
              simpa only [Option.some.injEq] using hResult
            subst liveIn
            exact
              .switch
                (analyzeCasesFuel_sound hCases)
                (analyzeDefaultFuel_sound hDefault)
        | for_ init cond post body =>
            simp only [analyzeStmtFuel] at hAnalyze
            cases hLoop :
                analyzeLoopFuel fuel demand init cond post body with
            | none => simp [hLoop] at hAnalyze
            | some result =>
                have hEq : result.liveIn = liveIn := by
                  simpa [hLoop] using hAnalyze
                subst liveIn
                exact analyzeLoopFuel_sound hLoop
        | brk =>
            have hEq : demand.brk = liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .brk
        | cont =>
            have hEq : demand.cont = liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .cont
        | leave =>
            have hEq : demand.leave = liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .leave
        | call targets functionName args =>
            have hEq :
                (ExprList.uses args ∪
                    LiveSet.eraseMany targets demand.normal) ∪
                  targets.toFinset = liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .call
        | terminal kind =>
            have hEq : (∅ : LiveSet) = liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            subst liveIn
            exact .terminal
        | terminalArgs kind args =>
            have hEq : ExprSeq.uses args = liveIn := by
              simpa only [analyzeStmtFuel, Option.some.injEq] using hAnalyze
            cases hEq
            exact .terminalArgs

  theorem analyzeLoopFuel_sound
      {fuel : Nat} {demand : Demand}
      {init : Block} {cond : Expr 1} {post body : Block}
      {result : LoopResult}
      (hAnalyze :
        analyzeLoopFuel fuel demand init cond post body = some result) :
      Stmt.Valid demand (.for_ init cond post body) result.liveIn := by
    cases fuel with
    | zero => simp [analyzeLoopFuel] at hAnalyze
    | succ fuel =>
        simp only [analyzeLoopFuel] at hAnalyze
        obtain ⟨headLive, hClose, hAfterClose⟩ :=
          Option.bind_eq_some_iff.mp hAnalyze
        obtain ⟨postLive, hPost, hAfterPost⟩ :=
          Option.bind_eq_some_iff.mp hAfterClose
        obtain ⟨bodyLive, hBody, hAfterBody⟩ :=
          Option.bind_eq_some_iff.mp hAfterPost
        obtain ⟨liveIn, hInit, hResult⟩ :=
          Option.bind_eq_some_iff.mp hAfterBody
        have hResultEq :
            ({ liveIn := liveIn
               headLive := headLive
               postLive := postLive
               bodyLive := bodyLive } : LoopResult) = result := by
          simpa only [Option.some.injEq] using hResult
        subst result
        obtain ⟨loopStepLive, hStep, hSubset⟩ := Close.run_sound hClose
        rw [hPost] at hStep
        simp only [Option.bind_some] at hStep
        rw [hBody] at hStep
        have hStepEq :
            Expr.uses cond ∪ (demand.normal ∪ bodyLive) =
              loopStepLive := by
          simpa only [Option.bind_some, Option.some.injEq] using hStep
        subst loopStepLive
        exact
          .for_
            (analyzeBlockFuel_sound hPost)
            (analyzeBlockFuel_sound hBody)
            hSubset
            (analyzeBlockFuel_sound hInit)
end

mutual
  private def blockAnalysisSize : Block → Nat
    | ⟨stmts⟩ => stmtListAnalysisSize stmts + 1

  private def stmtListAnalysisSize : List Stmt → Nat
    | [] => 1
    | stmt :: rest =>
        stmtAnalysisSize stmt + stmtListAnalysisSize rest + 1

  private def caseListAnalysisSize : List (Word × Block) → Nat
    | [] => 1
    | (_, body) :: rest =>
        blockAnalysisSize body + caseListAnalysisSize rest + 1

  private def defaultAnalysisSize : Option Block → Nat
    | none => 1
    | some body => blockAnalysisSize body + 1

  private def stmtAnalysisSize : Stmt → Nat
    | .block body => blockAnalysisSize body + 1
    | .if_ _ body => blockAnalysisSize body + 1
    | .switch _ cases defaultBody =>
        caseListAnalysisSize cases + defaultAnalysisSize defaultBody + 1
    | .for_ init _ post body =>
        blockAnalysisSize init + blockAnalysisSize post +
          blockAnalysisSize body + 1
    | _ => 1
end


def analysisFuel (block : Block) : Nat :=
  blockAnalysisSize block + 1

def analyzeBlock? (demand : Demand) (block : Block) : Option LiveSet :=
  analyzeBlockFuel (analysisFuel block) demand block

theorem analyzeBlock?_sound
    {demand : Demand} {block : Block} {liveIn : LiveSet}
    (hAnalyze : analyzeBlock? demand block = some liveIn) :
    Block.Valid demand block liveIn :=
  analyzeBlockFuel_sound hAnalyze

namespace Examples

def deadDeclaration : Block :=
  { stmts :=
      [ .let_ "dead" (.lit (EvmYul.UInt256.ofNat 1)) ] }

theorem deadDeclaration_result :
    analyzeBlock? { normal := ∅ } deadDeclaration = some ∅ := by
  decide

def callWithDormantValue : Block :=
  { stmts :=
      [ .call ["result"] "callee" [],
        .assign "sink" (.var "callerLive") ] }

theorem callWithDormantValue_result :
    analyzeBlock? { normal := ∅ } callWithDormantValue =
      some {"callerLive", "result", "sink"} := by
  decide

def loopWithContinue : Block :=
  { stmts :=
      [ .for_ { stmts := [] } (.var "condition")
          { stmts := [] } { stmts := [.cont] } ] }

theorem loopWithContinue_result :
    analyzeBlock? { normal := ∅ } loopWithContinue =
      some {"condition"} := by
  decide

def terminalCutsOffTail : Block :=
  { stmts :=
      [ .terminal .stop,
        .assign "sink" (.var "unreachable") ] }

theorem terminalCutsOffTail_result :
    analyzeBlock? { normal := ∅ } terminalCutsOffTail = some ∅ := by
  decide

end Examples

end AllocationLiveness
end Functions
end EvmCompiler
