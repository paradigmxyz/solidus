import EvmCompiler.Functions.AllocationLiveness

/-!
Compiler-owned liveness facts attached to the structured Functions syntax.

The canonical transfer semantics remains `AllocationLiveness`.  This module
only retains its computed boundary values and recursively associates them with
the source regions that a forward layout scheduler will visit.
-/

namespace EvmCompiler
namespace Functions
namespace AllocationLivenessFacts

open AllocationLiveness

structure CallFacts where
  targets : List Name
  functionName : Name
  liveAcross : LiveSet
  deriving DecidableEq

structure LoopFacts where
  headLive : LiveSet
  postLive : LiveSet
  bodyLive : LiveSet
  deriving DecidableEq

mutual
  structure Region where
    liveIn : LiveSet
    points : List Point

  structure Point where
    liveBefore : LiveSet
    liveAfter : LiveSet
    regions : List Region := []
    call? : Option CallFacts := none
    loop? : Option LoopFacts := none
end

mutual
  def annotateBlockFuel
      (fuel : Nat) (demand : Demand) (block : Block) : Option Region :=
    match fuel with
    | 0 => none
    | fuel + 1 => annotateStmtListFuel fuel demand block.stmts

  def annotateStmtListFuel
      (fuel : Nat) (demand : Demand) (stmts : List Stmt) : Option Region :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match stmts with
        | [] => some { liveIn := demand.normal, points := [] }
        | stmt :: rest => do
            let tail ← annotateStmtListFuel fuel demand rest
            let point ←
              annotateStmtFuel fuel (demand.withNormal tail.liveIn) stmt
            some
              { liveIn := point.liveBefore
                points := point :: tail.points }

  def annotateCasesFuel
      (fuel : Nat) (demand : Demand)
      (cases : List (Word × Block)) : Option (List Region) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match cases with
        | [] => some []
        | (_, body) :: rest => do
            let head ← annotateBlockFuel fuel demand body
            let tail ← annotateCasesFuel fuel demand rest
            some (head :: tail)

  def annotateDefaultFuel
      (fuel : Nat) (demand : Demand)
      (body? : Option Block) : Option (List Region) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match body? with
        | none => some []
        | some body => do
            let region ← annotateBlockFuel fuel demand body
            some [region]

  def annotateStmtFuel
      (fuel : Nat) (demand : Demand) (stmt : Stmt) : Option Point :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match stmt with
        | .block body => do
            let before ← analyzeStmtFuel (fuel + 1) demand stmt
            let region ← annotateBlockFuel fuel demand body
            some
              { liveBefore := before
                liveAfter := demand.normal
                regions := [region] }
        | .if_ _ body => do
            let before ← analyzeStmtFuel (fuel + 1) demand stmt
            let region ← annotateBlockFuel fuel demand body
            some
              { liveBefore := before
                liveAfter := demand.normal
                regions := [region] }
        | .switch _ cases defaultBody => do
            let before ← analyzeStmtFuel (fuel + 1) demand stmt
            let caseRegions ← annotateCasesFuel fuel demand cases
            let defaultRegions ←
              annotateDefaultFuel fuel demand defaultBody
            some
              { liveBefore := before
                liveAfter := demand.normal
                regions := caseRegions ++ defaultRegions }
        | .for_ init cond post body => do
            annotateLoopPointFuel fuel demand init cond post body
        | .call targets functionName _ => do
            let before ← analyzeStmtFuel (fuel + 1) demand stmt
            some
              { liveBefore := before
                liveAfter := demand.normal
                call? :=
                  some
                    { targets
                      functionName
                      liveAcross :=
                        LiveSet.eraseMany targets demand.normal } }
        | _ => do
            let before ← analyzeStmtFuel (fuel + 1) demand stmt
            some
              { liveBefore := before
                liveAfter := demand.normal }

  def annotateLoopPointFuel
      (fuel : Nat) (demand : Demand)
      (init : Block) (cond : Expr 1) (post body : Block) : Option Point :=
    match fuel with
    | 0 => none
    | childFuel + 1 => do
        let loop ←
          analyzeLoopFuel (childFuel + 1) demand init cond post body
        let initRegion ←
          annotateBlockFuel childFuel
            (demand.withNormal loop.headLive) init
        let postRegion ←
          annotateBlockFuel childFuel
            (demand.withNormal loop.headLive) post
        let bodyRegion ←
          annotateBlockFuel childFuel
            { normal := loop.postLive
              brk := demand.normal
              cont := loop.postLive
              leave := demand.leave }
            body
        some
          { liveBefore := loop.liveIn
            liveAfter := demand.normal
            regions := [initRegion, postRegion, bodyRegion]
            loop? :=
              some
                { headLive := loop.headLive
                  postLive := loop.postLive
                  bodyLive := loop.bodyLive } }
end

def annotateBlock? (demand : Demand) (block : Block) : Option Region :=
  annotateBlockFuel (analysisFuel block) demand block

mutual
theorem annotateBlockFuel_liveIn
    {fuel : Nat} {demand : Demand} {block : Block} {facts : Region}
    (hFacts : annotateBlockFuel fuel demand block = some facts) :
    analyzeBlockFuel fuel demand block = some facts.liveIn := by
  cases fuel with
  | zero => simp [annotateBlockFuel] at hFacts
  | succ fuel =>
      rcases block with ⟨stmts⟩
      apply annotateStmtListFuel_liveIn hFacts

theorem annotateStmtListFuel_liveIn
    {fuel : Nat} {demand : Demand} {stmts : List Stmt} {facts : Region}
    (hFacts : annotateStmtListFuel fuel demand stmts = some facts) :
    analyzeStmtListFuel fuel demand stmts = some facts.liveIn := by
  cases fuel with
  | zero => simp [annotateStmtListFuel] at hFacts
  | succ fuel =>
      cases stmts with
      | nil =>
          simp [annotateStmtListFuel] at hFacts
          subst facts
          rfl
      | cons stmt rest =>
          simp only [annotateStmtListFuel] at hFacts
          obtain ⟨tail, hTail, hAfterTail⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          obtain ⟨point, hPoint, hResult⟩ :=
            Option.bind_eq_some_iff.mp hAfterTail
          have hFactsEq :
              ({ liveIn := point.liveBefore
                 points := point :: tail.points } : Region) = facts := by
            simpa only [Option.some.injEq] using hResult
          subst facts
          have hTailLive := annotateStmtListFuel_liveIn hTail
          have hPointLive := annotateStmtFuel_liveBefore hPoint
          simp only [analyzeStmtListFuel]
          rw [hTailLive]
          exact hPointLive

theorem annotateStmtFuel_liveBefore
    {fuel : Nat} {demand : Demand} {stmt : Stmt} {facts : Point}
    (hFacts : annotateStmtFuel fuel demand stmt = some facts) :
    analyzeStmtFuel fuel demand stmt = some facts.liveBefore := by
  cases fuel with
  | zero => simp [annotateStmtFuel] at hFacts
  | succ fuel =>
      cases stmt with
      | block body | if_ _ body =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hTail⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          obtain ⟨region, _hRegion, hResult⟩ :=
            Option.bind_eq_some_iff.mp hTail
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | switch scrutinee cases defaultBody =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hTail⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          obtain ⟨caseRegions, _hCases, hAfterCases⟩ :=
            Option.bind_eq_some_iff.mp hTail
          obtain ⟨defaultRegions, _hDefault, hResult⟩ :=
            Option.bind_eq_some_iff.mp hAfterCases
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | for_ init cond post body =>
          apply annotateLoopPointFuel_liveBefore
          simpa only [annotateStmtFuel] using hFacts
      | call targets functionName args =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | expr expr =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | let_ name value =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | assign name value =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | brk =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | cont =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | leave =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | terminal kind =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore
      | terminalArgs kind args =>
          simp only [annotateStmtFuel] at hFacts
          obtain ⟨before, hBefore, hResult⟩ :=
            Option.bind_eq_some_iff.mp hFacts
          have hEq : before = facts.liveBefore := by
            simpa only [Option.some.injEq] using
              congrArg Point.liveBefore (Option.some.inj hResult)
          rw [← hEq]
          exact hBefore

theorem annotateLoopPointFuel_liveBefore
    {fuel : Nat} {demand : Demand}
    {init : Block} {cond : Expr 1} {post body : Block} {facts : Point}
    (hFacts :
      annotateLoopPointFuel fuel demand init cond post body = some facts) :
    (analyzeLoopFuel fuel demand init cond post body).map
        LoopResult.liveIn = some facts.liveBefore := by
  cases fuel with
  | zero => simp [annotateLoopPointFuel] at hFacts
  | succ childFuel =>
      simp only [annotateLoopPointFuel] at hFacts
      obtain ⟨loop, hLoop, hAfterLoop⟩ :=
        Option.bind_eq_some_iff.mp hFacts
      obtain ⟨initRegion, _hInit, hAfterInit⟩ :=
        Option.bind_eq_some_iff.mp hAfterLoop
      obtain ⟨postRegion, _hPost, hAfterPost⟩ :=
        Option.bind_eq_some_iff.mp hAfterInit
      obtain ⟨bodyRegion, _hBody, hResult⟩ :=
        Option.bind_eq_some_iff.mp hAfterPost
      have hEq : loop.liveIn = facts.liveBefore := by
        simpa only [Option.some.injEq] using
          congrArg Point.liveBefore (Option.some.inj hResult)
      rw [hLoop]
      exact congrArg some hEq

end

theorem annotateBlock?_sound
    {demand : Demand} {block : Block} {facts : Region}
    (hFacts : annotateBlock? demand block = some facts) :
    Block.Valid demand block facts.liveIn :=
  analyzeBlockFuel_sound (annotateBlockFuel_liveIn hFacts)

namespace Examples

def dormantCallLiveAcross? : Option LiveSet := do
  let region ←
    annotateBlock? { normal := ∅ }
      AllocationLiveness.Examples.callWithDormantValue
  let point ← region.points[0]?
  let call ← point.call?
  some call.liveAcross

theorem dormantCallLiveAcross_result :
    dormantCallLiveAcross? = some {"callerLive"} := by
  decide

def loopHead? : Option LiveSet := do
  let region ←
    annotateBlock? { normal := ∅ }
      AllocationLiveness.Examples.loopWithContinue
  let point ← region.points[0]?
  let loop ← point.loop?
  some loop.headLive

theorem loopHead_result : loopHead? = some {"condition"} := by
  decide

end Examples

end AllocationLivenessFacts
end Functions
end EvmCompiler
