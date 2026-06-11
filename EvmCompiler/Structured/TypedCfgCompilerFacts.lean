import EvmCompiler.Structured.TypedCfgCompiler

namespace EvmCompiler
namespace Structured
namespace TypedCfgCompilerFacts

open Assembly

/--
Any block property inherited by every case body and the default is inherited
by the body selected by the source switch semantics.
-/
theorem switch_property_of_select
    {property : Structured.Block → Prop}
    {scrutinee : Word} {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block} {selected : Structured.Block}
    (hCases :
      ∀ value body, (value, body) ∈ cases → property body)
    (hDefault :
      ∀ body, defaultBody = some body → property body)
    (hSelect :
      Structured.Switch.select scrutinee cases defaultBody =
        some selected) :
    property selected := by
  revert selected
  induction cases with
  | nil =>
      intro selected hSelect
      exact hDefault selected hSelect
  | cons head rest ih =>
      intro selected hSelect
      rcases head with ⟨value, body⟩
      by_cases hEq : value = scrutinee
      · have hBodyEq : body = selected := by
          simpa [Structured.Switch.select, hEq] using hSelect
        subst selected
        exact hCases value body (by simp)
      · apply ih
        · intro caseValue caseBody hMem
          exact hCases caseValue caseBody (by simp [hMem])
        · simpa [Structured.Switch.select, hEq] using hSelect

namespace Switch

def testOutput (valueShape : TypedCfg.Shape) : TypedCfg.Shape :=
  { valueShape with slots := .word :: valueShape.slots }

def casesEntryLabel (base idx : Nat) :
    List (Word × Structured.Block) → Assembly.Label
  | [] => LabelSupply.label base 1
  | _ => TypedCfgCompiler.switchTestLabel base idx

def nextTestLabel (base idx : Nat)
    (rest : List (Word × Structured.Block)) : Assembly.Label :=
  casesEntryLabel base (idx + 1) rest

theorem testBody_type
    {valueShape : TypedCfg.Shape} {slot : TypedCfg.Slot}
    {caseValue : Word}
    (hHead : valueShape.slots.head? = some slot) :
    TypedCfg.Block.bodyType?
        [.dup 0, .push caseValue, .prim .eq] valueShape =
      some (testOutput valueShape) := by
  cases valueShape with
  | mk slots tail =>
      cases slots with
      | nil =>
          simp at hHead
      | cons head rest =>
          simp [TypedCfg.Block.bodyType?, TypedCfg.Instr.type?,
            TypedCfg.Shape.get?, TypedCfg.Shape.length,
            TypedCfg.Shape.pop, TypedCfg.Shape.pushWords,
            Assembly.PrimOp.stackArity?, Assembly.PrimOp.toEVM,
            EvmYul.EVM.δ, EvmYul.EVM.α, testOutput]

theorem fallthrough_of_compileStmtFuel?_switch
    {compilerFuel : Nat} {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape}
    {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 2)
          (.switch scrutinee cases defaultBody) ctx
          supply entry input regular =
        some result) :
    ∃ output, result.fallthrough? = some output := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input with
  | none =>
      simp [hType] at hCompile
  | some valueShape =>
      cases hValue : valueShape.slots.head? with
      | none =>
          simp [hType, hValue] at hCompile
      | some valueSlot =>
          simp only [TypedCfgCompiler.mkBlock?, hType, hValue,
            Bind.bind, Option.bind] at hCompile
          cases hCases :
              TypedCfgCompiler.compileCasesFuel? (compilerFuel + 1)
                cases ctx supply (supply + 1) 0 valueShape
                { valueShape with slots := valueShape.slots.tail }
                regular with
          | none =>
              simp [hCases] at hCompile
          | some caseResult =>
              simp only [hCases] at hCompile
              cases hDefault :
                  TypedCfgCompiler.compileDefaultFuel? (compilerFuel + 1)
                    defaultBody ctx caseResult.next
                    (LabelSupply.label supply 1) valueShape
                    { valueShape with slots := valueShape.slots.tail }
                    regular with
              | none =>
                  simp [hDefault] at hCompile
              | some defaultResult =>
                  simp only [hDefault] at hCompile
                  cases hCompile
                  exact
                    ⟨{ valueShape with slots := valueShape.slots.tail },
                      rfl⟩

theorem compileStmtFuel?_switch_one_eq_none
    {scrutinee : Structured.Code}
    {cases : List (Word × Structured.Block)}
    {defaultBody : Option Structured.Block}
    {ctx : TypedCfgCompiler.Context} {supply : LabelSupply}
    {entry regular : Assembly.Label} {input : TypedCfg.Shape} :
    TypedCfgCompiler.compileStmtFuel? 1
        (.switch scrutinee cases defaultBody) ctx
        supply entry input regular =
      none := by
  unfold TypedCfgCompiler.compileStmtFuel?
  cases hType :
      TypedCfg.Block.bodyType?
        (TypedCfgCompiler.Code.toCfg scrutinee) input <;>
    simp [hType, TypedCfgCompiler.mkBlock?,
      TypedCfgCompiler.compileCasesFuel?]

end Switch

namespace Loop

theorem components_of_compileStmtFuel?_for
    {compilerFuel : Nat} {init post body : Structured.Block}
    {cond : Structured.Code} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1)
        (.for_ init cond post body) ctx supply entry input regular =
          some result) :
    ∃ initResult loopInput condOutput condition bodyResult postResult,
      TypedCfgCompiler.compileBlockFuel? compilerFuel init
          { ctx with breakLabel? := none, continueLabel? := none }
          (supply + 1) entry input (LabelSupply.label supply 0) =
        some initResult ∧
      initResult.fallthrough? = some loopInput ∧
      TypedCfg.Block.bodyType?
          (TypedCfgCompiler.Code.toCfg cond) loopInput =
        some condOutput ∧
      condOutput.slots.head? = some condition ∧
      TypedCfgCompiler.compileBlockFuel? compilerFuel body
          { ctx with
            breakLabel? := some regular
            continueLabel? := some (LabelSupply.label supply 2) }
          initResult.next (LabelSupply.label supply 1)
          { condOutput with slots := condOutput.slots.tail }
          (LabelSupply.label supply 2) =
        some bodyResult ∧
      TypedCfgCompiler.compileBlockFuel? compilerFuel post
          { ctx with breakLabel? := none, continueLabel? := none }
          bodyResult.next (LabelSupply.label supply 2)
          (bodyResult.fallthrough?.getD
            { condOutput with slots := condOutput.slots.tail })
          (LabelSupply.label supply 0) =
        some postResult ∧
      result =
        { blocks :=
            initResult.blocks ++
              [{ label := LabelSupply.label supply 0
                 input := loopInput
                 body := TypedCfgCompiler.Code.toCfg cond
                 output := condOutput
                 term :=
                   .jumpi (LabelSupply.label supply 1) regular }] ++
              bodyResult.blocks ++ postResult.blocks
          next := postResult.next
          calls :=
            initResult.calls ++ bodyResult.calls ++ postResult.calls
          fallthrough? :=
            some { condOutput with slots := condOutput.slots.tail } } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  cases hInit :
      TypedCfgCompiler.compileBlockFuel? compilerFuel init
        { ctx with breakLabel? := none, continueLabel? := none }
        (supply + 1) entry input (LabelSupply.label supply 0) with
  | none =>
      simp [hInit] at hCompile
  | some initResult =>
      cases hLoopInput : initResult.fallthrough? with
      | none =>
          simp [hInit, hLoopInput] at hCompile
      | some loopInput =>
          cases hType :
              TypedCfg.Block.bodyType?
                (TypedCfgCompiler.Code.toCfg cond) loopInput with
          | none =>
              simp [hInit, hLoopInput, hType] at hCompile
          | some condOutput =>
              cases hHead : condOutput.slots.head? with
              | none =>
                  simp [hInit, hLoopInput, hType, hHead] at hCompile
              | some condition =>
                  cases hBody :
                      TypedCfgCompiler.compileBlockFuel? compilerFuel body
                        { ctx with
                          breakLabel? := some regular
                          continueLabel? :=
                            some (LabelSupply.label supply 2) }
                        initResult.next (LabelSupply.label supply 1)
                        { condOutput with
                          slots := condOutput.slots.tail }
                        (LabelSupply.label supply 2) with
                  | none =>
                      simp [hInit, hLoopInput, hType, hHead,
                        TypedCfgCompiler.mkBlock?, hBody] at hCompile
                  | some bodyResult =>
                      cases hPost :
                          TypedCfgCompiler.compileBlockFuel? compilerFuel post
                            { ctx with
                              breakLabel? := none
                              continueLabel? := none }
                            bodyResult.next
                            (LabelSupply.label supply 2)
                            (bodyResult.fallthrough?.getD
                              { condOutput with
                                slots := condOutput.slots.tail })
                            (LabelSupply.label supply 0) with
                      | none =>
                          simp [hInit, hLoopInput, hType, hHead,
                            TypedCfgCompiler.mkBlock?, hBody, hPost] at hCompile
                      | some postResult =>
                          simp [hInit, hLoopInput, hType, hHead,
                            TypedCfgCompiler.mkBlock?, hBody, hPost] at hCompile
                          cases hCompile
                          refine
                            ⟨initResult, loopInput, condOutput, condition,
                              bodyResult, postResult, ?_⟩
                          simp [hInit, hLoopInput, hType, hHead, hBody, hPost,
                            List.append_assoc]

end Loop

namespace Call

theorem returnTokenDepth?_procExit (proc : Structured.Proc) :
    (TypedCfgCompiler.Shape.procExit proc).returnTokenDepth? =
      some proc.retc := by
  unfold TypedCfgCompiler.Shape.procExit TypedCfg.Shape.returnTokenDepth?
  induction proc.retc with
  | zero =>
      simp [TypedCfg.Shape.returnTokenDepthList?]
  | succ retc ih =>
      simp [List.replicate_succ, TypedCfg.Shape.returnTokenDepthList?, ih]

theorem findTarget?_returnSitesFor_of_mem
    {calls : List TypedCfgCompiler.DispatchSite}
    {site : TypedCfgCompiler.DispatchSite}
    (hUnique :
      (calls.map TypedCfgCompiler.DispatchSite.token).Nodup)
    (hMem : site ∈ calls) :
    TypedCfg.Block.ReturnSite.findTarget? site.token
        (TypedCfgCompiler.returnSitesFor site.procName calls) =
      some site.returnLabel := by
  induction calls with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      have hHeadNot :
          head.token ∉
            tail.map TypedCfgCompiler.DispatchSite.token := by
        exact (List.nodup_cons.mp hUnique).1
      have hTailUnique :
          (tail.map TypedCfgCompiler.DispatchSite.token).Nodup :=
        (List.nodup_cons.mp hUnique).2
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl hHead =>
          subst site
          simp [TypedCfgCompiler.returnSitesFor,
            TypedCfg.Block.ReturnSite.findTarget?]
      | inr hTail =>
          have hTokenNe : head.token ≠ site.token := by
            intro hEq
            apply hHeadNot
            exact List.mem_map.mpr ⟨site, hTail, hEq.symm⟩
          have hFound := ih hTailUnique hTail
          by_cases hName : head.procName = site.procName
          · unfold TypedCfgCompiler.returnSitesFor
            simp [hName, TypedCfg.Block.ReturnSite.findTarget?, hTokenNe]
            simpa [TypedCfgCompiler.returnSitesFor] using hFound
          · unfold TypedCfgCompiler.returnSitesFor
            simp [hName]
            simpa [TypedCfgCompiler.returnSitesFor] using hFound

theorem components_of_compileStmtFuel?_call
    {compilerFuel : Nat} {name : Structured.Name}
    {proc : Structured.Proc} {ctx : TypedCfgCompiler.Context}
    {supply : LabelSupply} {entry regular : Assembly.Label}
    {input : TypedCfg.Shape} {result : TypedCfgCompiler.Result}
    (hLookup : Structured.ProcList.lookup? name ctx.procs = some proc)
    (hCompile :
      TypedCfgCompiler.compileStmtFuel? (compilerFuel + 1) (.call name)
          ctx supply entry input regular =
        some result) :
    ∃ returnShape output,
      TypedCfgCompiler.Shape.afterCall input proc.argc proc.retc =
          some returnShape ∧
      TypedCfg.Block.bodyType?
          (.returnToken (Structured.Stmt.callToken supply) ::
            TypedCfgCompiler.sinkTopUnder proc.argc) input =
        some output ∧
      result =
        { blocks :=
            [{ label := entry
               input := input
               body :=
                 .returnToken (Structured.Stmt.callToken supply) ::
                   TypedCfgCompiler.sinkTopUnder proc.argc
               output := output
               term := .jump (ProcLabel.entry name) }]
          next := supply + 1
          calls :=
            [{ procName := name
               token := Structured.Stmt.callToken supply
               returnLabel := regular
               caseLabel := .generated supply 10000 }]
          fallthrough? := some returnShape } := by
  unfold TypedCfgCompiler.compileStmtFuel? at hCompile
  simp [hLookup] at hCompile
  cases hReturnShape :
      TypedCfgCompiler.Shape.afterCall input proc.argc proc.retc with
  | none =>
      simp [hReturnShape] at hCompile
  | some returnShape =>
      cases hType :
          TypedCfg.Block.bodyType?
            (.returnToken (Structured.Stmt.callToken supply) ::
              TypedCfgCompiler.sinkTopUnder proc.argc) input with
      | none =>
          simp [hReturnShape, TypedCfgCompiler.mkBlock?, hType] at hCompile
      | some output =>
          simp [hReturnShape, TypedCfgCompiler.mkBlock?, hType] at hCompile
          cases hCompile
          exact ⟨returnShape, output, rfl, rfl, rfl⟩

end Call

end TypedCfgCompilerFacts
end Structured
end EvmCompiler
