import EvmCompiler.Functions.AllocationInteractionCursor

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall

open AllocationInteractionCursor
open AllocationInteractionRelation

namespace CallCompiler

/-- Decompose the existing call compiler into its adjacent runtime phases. -/
theorem components
    {lowerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {lowerState lowerFinal : AllocationLowering.State}
    {localsCtx localsFinal : Locals.Ctx}
    {targets : List Functions.Name}
    {functionName : Functions.Name}
    {args : List (Functions.Expr 1)}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    (hLower :
      AllocationLowering.lowerStmt lowerCtx returns lowerState
          (.call targets functionName args) =
        some (loweredStmts, lowerFinal))
    (hCompile :
      Locals.Block.compileOpen localsCtx { stmts := loweredStmts } =
        some (compiledStmts, localsFinal)) :
    ∃ fn loweredArgs callArgs stores release argsCode releaseCode,
      AllocationSupport.lookupFun? functionName lowerCtx.functions = some fn ∧
        args.length = fn.params.length ∧
        targets.length = fn.returns.length ∧
        targets.Nodup ∧
        AllocationLowering.lowerExprList lowerCtx lowerState args =
          some loweredArgs ∧
        (if functionName ∈ lowerCtx.frameFunctions then do
            let frameConfig ← lowerCtx.frameConfig?
            some (AllocationLowering.frameExpr frameConfig :: loweredArgs)
          else
            some loweredArgs) =
          some callArgs ∧
        AllocationLowering.lowerCallTargetsCode?
            lowerCtx lowerState targets.reverse targets.length =
          some stores ∧
        (if functionName ∈ lowerCtx.frameFunctions then do
            let frameConfig ← lowerCtx.frameConfig?
            some
              [.expr
                (Locals.Expr.code (results := 0)
                  (AllocationSupport.scratchFrameReleaseCode frameConfig))]
          else
            some []) =
          some release ∧
        Locals.ExprSeq.compileCode localsCtx 0
            (AllocationLowering.exprSeqOfList callArgs) =
          some argsCode ∧
        Locals.Block.compileOpen localsCtx { stmts := release } =
          some (releaseCode, localsCtx) ∧
        compiledStmts =
          Locals.codeStmt argsCode ++
            [.call functionName] ++
            Locals.codeStmt stores ++ releaseCode ∧
        lowerFinal = lowerState ∧
        localsFinal = localsCtx := by
  obtain
      ⟨fn, loweredArgs, callArgs, stores, release,
        hLookup, hArgsLength, hTargetsLength, hTargets,
        hLowerArgs, hCallArgs, hStores, hRelease, rfl, rfl⟩ :=
    AllocationLowering.lowerStmt_call_components hLower
  cases hArgsCode :
      Locals.ExprSeq.compileCode localsCtx 0
        (AllocationLowering.exprSeqOfList callArgs) with
  | none =>
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        Locals.Expr.compileCode, hArgsCode] at hCompile
  | some argsCode =>
      obtain ⟨releaseCode, hReleaseCode⟩ :
          ∃ releaseCode,
            Locals.Block.compileOpen localsCtx { stmts := release } =
              some (releaseCode, localsCtx) := by
        by_cases hFrame : functionName ∈ lowerCtx.frameFunctions
        · cases hConfig : lowerCtx.frameConfig? with
          | none =>
              simp [hFrame, hConfig] at hRelease
          | some frameConfig =>
              have hReleaseEq :
                  release =
                    [.expr
                      (Locals.Expr.code (results := 0)
                        (AllocationSupport.scratchFrameReleaseCode
                          frameConfig))] := by
                simpa [hFrame, hConfig] using hRelease.symm
              subst release
              exact
                ⟨Locals.codeStmt
                    (AllocationSupport.scratchFrameReleaseCode frameConfig),
                  by
                    simp [Locals.Block.compileOpen, Locals.Stmt.compile,
                      Locals.Expr.compileCode]⟩
        · have hReleaseEq : release = [] := by
            simpa [hFrame] using hRelease.symm
          subst release
          exact ⟨[], by simp [Locals.Block.compileOpen]⟩
      simp [Locals.Block.compileOpen, Locals.Stmt.compile,
        Locals.Expr.compileCode, Locals.codeStmt,
        hArgsCode, hReleaseCode] at hCompile
      rcases hCompile with ⟨rfl, rfl⟩
      exact
        ⟨fn, loweredArgs, callArgs, stores, release,
          argsCode, releaseCode, hLookup, hArgsLength,
          hTargetsLength, hTargets, hLowerArgs, hCallArgs,
          hStores, hRelease, hArgsCode, hReleaseCode, rfl, rfl, rfl⟩

end CallCompiler

namespace SelectedCallee

/-- Compiler-owned artifact for the source function selected by one call. -/
structure Artifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    (name : Functions.Name) (fn : Functions.FunDef) where
  startState : AllocationSupport.CompileState
  finalState : AllocationSupport.CompileState
  proc : Locals.Proc
  lowerProc : Expressions.Proc
  slots : AllocationSupport.FunSlots
  planEntry : AllocationSupport.ScopedAllocation
  lower :
    AllocationLowering.lowerFunction? compilation.recipe
        compilation.stackSlots compilation.frameName
        (AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords)
        startState fn =
      some (proc, finalState)
  compile : proc.toExpressions? = some lowerProc
  targetLookup :
    Structured.ProcList.lookup? name expressions.toStructured.procs =
      some lowerProc.toStructured
  slotsLookup :
    AllocationSupport.lookupFun? fn.name
        compilation.recipe.functionSlots =
      some slots
  slotsMatch : slots.Matches fn
  planEntryMem : planEntry ∈ compilation.recipe.functions
  planEntryScope : planEntry.scope = .function fn.name
  planEntryState :
    planEntry.state =
      (AllocationSupport.planBlockOpen (.function fn.name)
        { allocation :=
            { env := AllocationSupport.functionEnv slots
              nextSlot := startState.nextSlot }
          nextScope := 0
          scopes := [] }
        fn.body).allocation
  bodyScopesMem :
    ∀ entry,
      entry ∈
          (AllocationSupport.planBlockOpen (.function fn.name)
            { allocation :=
                { env := AllocationSupport.functionEnv slots
                  nextSlot := startState.nextSlot }
              nextScope := 0
              scopes := [] }
            fn.body).scopes →
        entry ∈ compilation.recipe.lexicalScopes
  sourceName : fn.name = name
  sourceMem : fn ∈ program.functions

/-- Construct a selected callee solely from source lookup and real lowering. -/
theorem Artifact.of_find
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (hFind :
      Functions.Source.FunList.find? name program.functions = some fn) :
    Nonempty (Artifact compilation name fn) := by
  obtain
      ⟨recipe, stackSlots, frameName, before, after, proc, lowerProc,
        selectedSlots, planEntry, hValidate, hFresh, hSelected, hCompile,
        hLookup, hSelectedSlots, hPlanEntryMem, hPlanEntryScope,
        hPlanEntryState, hBodyScopesMem⟩ :=
    AllocationLowering.lowerExpressionsFromAllocation?_find_compiled_function
      compilation.lower hFind
  have hValidated :
      (recipe, stackSlots) =
        (compilation.recipe, compilation.stackSlots) := by
    exact Option.some.inj (hValidate.symm.trans compilation.validate)
  cases hValidated
  have hFrame : frameName = compilation.frameName := by
    exact Option.some.inj (hFresh.symm.trans compilation.fresh)
  subst frameName
  have hMem : fn ∈ program.functions :=
    Functions.Source.FunList.mem_of_find?_eq_some hFind
  obtain
      ⟨slots, _entry, _added, hSlotsLookup, hSlotsMatch,
        _hEntry, _hScope, _hEnv, _hPlan⟩ :=
    AllocationLowering.validatePlan?_function_components
      compilation.validate hMem
  have hSlotsEq : slots = selectedSlots := by
    rw [hSelectedSlots] at hSlotsLookup
    exact (Option.some.inj hSlotsLookup).symm
  subst slots
  exact
    ⟨{ startState := before
       finalState := after
       proc := proc
       lowerProc := lowerProc
       slots := selectedSlots
       planEntry := planEntry
       lower := hSelected
       compile := hCompile
       targetLookup := hLookup
       slotsLookup := hSelectedSlots
       slotsMatch := hSlotsMatch
       planEntryMem := hPlanEntryMem
       planEntryScope := hPlanEntryScope
       planEntryState := hPlanEntryState
       bodyScopesMem := hBodyScopesMem
       sourceName :=
         Functions.Source.FunList.name_eq_of_find?_eq_some hFind
       sourceMem := hMem }⟩

def Artifact.root
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (_artifact : Artifact compilation name fn) :
    Locals.Allocation.ScopeId :=
  .function fn.name

def Artifact.scratchBindings
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    List (Locals.Name × Nat) :=
  AllocationLowering.scratchBindingsForRoot
    compilation.recipe compilation.stackSlots artifact.root

def Artifact.needsFrame
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : Bool :=
  !artifact.scratchBindings.isEmpty

def Artifact.lowerCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    AllocationLowering.Ctx :=
  compilation.lowerCtx artifact.root artifact.scratchBindings

theorem Artifact.lowerCtxShared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    compilation.CtxShared artifact.lowerCtx :=
  compilation.lowerCtx_shared artifact.root artifact.scratchBindings

theorem Artifact.planEntry_env_extension
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    ∃ added,
      artifact.planEntry.state.env =
        added ++ AllocationSupport.functionEnv artifact.slots := by
  obtain ⟨added, hEnv⟩ :=
    AllocationSupport.planBlockOpen_env_extension
      (.function fn.name)
      { allocation :=
          { env := AllocationSupport.functionEnv artifact.slots
            nextSlot := artifact.startState.nextSlot }
        nextScope := 0
        scopes := [] }
      fn.body
  refine ⟨added, ?_⟩
  rw [artifact.planEntryState]
  simpa using hEnv

theorem Artifact.frameName_not_mem_planEntry_env
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    compilation.frameName ∉ artifact.planEntry.state.env.map Prod.fst := by
  have hFresh :=
    AllocationLowering.freshFrameName_not_mem_allSourceNames
      compilation.fresh
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  intro hFrame
  apply hFresh
  simp only [AllocationLowering.allSourceNames, List.mem_append,
    List.mem_flatMap]
  apply Or.inr
  refine
    ⟨compilation.recipe, by simp [hRecipe], artifact.planEntry, ?_, hFrame⟩
  simp only [AllocationLowering.scopedStates, List.mem_cons,
    List.mem_append]
  exact Or.inl (Or.inr artifact.planEntryMem)

theorem Artifact.frameName_not_mem_lexical_entry_env
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    {entry : AllocationSupport.ScopedAllocation}
    (hEntry : entry ∈ compilation.recipe.lexicalScopes) :
    compilation.frameName ∉ entry.state.env.map Prod.fst := by
  have hFresh :=
    AllocationLowering.freshFrameName_not_mem_allSourceNames
      compilation.fresh
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  intro hFrame
  apply hFresh
  simp only [AllocationLowering.allSourceNames, List.mem_append,
    List.mem_flatMap]
  apply Or.inr
  refine
    ⟨compilation.recipe, by simp [hRecipe], entry, ?_, hFrame⟩
  simp only [AllocationLowering.scopedStates, List.mem_cons,
    List.mem_append]
  exact Or.inr hEntry

def Artifact.entryLayout
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : Locals.Layout :=
  fn.params.reverse ++
    if artifact.needsFrame then [compilation.frameName] else []

def Artifact.entryCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : Locals.Ctx :=
  Locals.Ctx.procEntryWithLayoutAndRetc
    artifact.entryLayout fn.returns.length

def Artifact.bodyStart
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    AllocationLowering.State :=
  let paramResult :=
    AllocationLowering.lowerParams artifact.lowerCtx
      artifact.slots.params artifact.entryLayout
  let returnResult :=
    AllocationLowering.lowerReturns artifact.lowerCtx
      artifact.slots.returns paramResult.2
  { allocation :=
      { env := AllocationSupport.functionEnv artifact.slots
        nextSlot := artifact.startState.nextSlot }
    layout := returnResult.2 }

def Artifact.markers
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : List Locals.Stmt :=
  [AllocationLowering.bindEntryLayout artifact.entryLayout] ++
    if artifact.needsFrame then
      [AllocationLowering.bindScratchBindings
        fn.params.length artifact.scratchBindings]
    else
      []

def Artifact.mode
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) : ActivationMode :=
  if artifact.needsFrame then
    .scratch 0 compilation.recipe.frameWords
  else
    .stack

/-- Minimal compiler-prepared view needed by call and body preservation. -/
structure Prepared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) where
  plan : Locals.Allocation.Plan
  paramCtx : Locals.Ctx
  returnCtx : Locals.Ctx
  body : Locals.Block
  bodyFinal : AllocationLowering.State
  returnValues : Locals.ExprSeq fn.returns.length
  markerCode : List Expressions.Stmt
  paramCode : List Expressions.Stmt
  returnCode : List Expressions.Stmt
  bodyCode : List Expressions.Stmt
  bodyCtx : Locals.Ctx
  returnValueCode : Structured.Code
  cleanup : Structured.Code
  planLookup : allocation.find? (.function fn.name) = some plan
  planEq :
    plan =
      MixedAllocation.allocationOfState
        program.memoryContract compilation.recipe.frameWords
        (MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots artifact.planEntry.scope
          artifact.planEntry.state)
        artifact.planEntry.state
  planWF : plan.WellFormed
  bodyPlan : artifact.planEntry.state = bodyFinal.allocation
  signatureNodup :
    ((artifact.slots.returns ++ artifact.slots.params).map Prod.fst).Nodup
  frameFresh :
    compilation.frameName ∉
      (artifact.slots.returns ++ artifact.slots.params).map Prod.fst
  bodyLayout :
    returnCtx.layout =
      AllocationInteractionRelation.currentStackOrder plan
          ((artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse) ++
        if artifact.needsFrame then [compilation.frameName] else []
  lowerBody :
    AllocationLowering.lowerBlockOpen artifact.lowerCtx fn.returns
        artifact.bodyStart fn.body =
      some (body, bodyFinal)
  lowerReturnValues :
    AllocationLowering.lowerReturnExprs artifact.lowerCtx bodyFinal
        fn.returns =
      some returnValues
  compileMarkers :
    Locals.Block.compileOpen artifact.entryCtx
        { stmts := artifact.markers } =
      some (markerCode, artifact.entryCtx)
  compileParams :
    Locals.Block.compileOpen artifact.entryCtx
        { stmts :=
            (AllocationLowering.lowerParams artifact.lowerCtx
              artifact.slots.params artifact.entryCtx.layout).1 } =
      some (paramCode, paramCtx)
  compileReturns :
    Locals.Block.compileOpen paramCtx
        { stmts :=
            (AllocationLowering.lowerReturns artifact.lowerCtx
              artifact.slots.returns paramCtx.layout).1 } =
      some (returnCode, returnCtx)
  compileBody :
    Locals.Block.compileOpen returnCtx body = some (bodyCode, bodyCtx)
  compileReturnValues :
    Locals.ExprSeq.compileCode bodyCtx 0 returnValues =
      some returnValueCode
  compileCleanup :
    bodyCtx.cleanupToPreserving? fn.returns.length 0 = some cleanup
  procName : artifact.lowerProc.name = fn.name
  procArgc :
    artifact.lowerProc.argc =
      fn.params.length + (if artifact.needsFrame then 1 else 0)
  procRetc : artifact.lowerProc.retc = fn.returns.length
  procBody :
    artifact.lowerProc.body.stmts =
      markerCode ++ paramCode ++ returnCode ++ bodyCode ++
        Locals.codeStmt returnValueCode ++ Locals.codeStmt cleanup

def Prepared.bodyMode
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) : ActivationMode :=
  artifact.mode.atStackDepth
    (currentStackOrder prepared.plan
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)).length

theorem Artifact.prepare
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn) :
    Nonempty (Prepared artifact) := by
  obtain
      ⟨slots, body, bodyFinal, returnValues,
        markerCode, paramCode, paramCtx, returnCode, returnCtx,
        bodyCode, bodyCtx, returnValueCode, cleanup,
        hSlots, hComponents⟩ :=
    AllocationLowering.lowerFunction?_toExpressions?_body_components
      artifact.lower artifact.compile
  have hSlotsEq : slots = artifact.slots := by
    rw [artifact.slotsLookup] at hSlots
    exact (Option.some.inj hSlots).symm
  subst slots
  dsimp only at hComponents
  rcases hComponents with
    ⟨hLowerBody, hLowerReturnValues, hCompileMarkers,
      hCompileParams, hCompileReturns, hCompileBody,
      hCompileReturnValues, hCompileCleanup, hProcName,
      hProcArgc, hProcRetc, hProcBody⟩
  let plan :=
    MixedAllocation.allocationOfState
      program.memoryContract compilation.recipe.frameWords
      (MixedAllocation.AllocationRecipe.stackEntriesForScope
        compilation.recipe compilation.stackSlots artifact.planEntry.scope
        artifact.planEntry.state)
      artifact.planEntry.state
  have hEntryPlan :=
    AllocationLowering.validatePlan?_function_entry_plan
      compilation.validate artifact.planEntryMem
  have hPlanLookup :
      allocation.find? (.function fn.name) = some plan := by
    simpa [plan, artifact.planEntryScope] using hEntryPlan
  have hPlanWF : plan.WellFormed :=
    Locals.Allocation.ProgramPlan.wellFormed_of_find?_eq_some
      (AllocationLowering.validatePlan?_sound compilation.validate).1
      hPlanLookup
  have hCompileParams' :
      Locals.Block.compileOpen artifact.entryCtx
          { stmts :=
              (AllocationLowering.lowerParams artifact.lowerCtx
                artifact.slots.params artifact.entryCtx.layout).1 } =
        some (paramCode, paramCtx) := by
    simpa [Artifact.lowerCtx, Artifact.entryCtx, Artifact.entryLayout,
      Artifact.root, Artifact.scratchBindings, Artifact.needsFrame] using
      hCompileParams
  have hCompileReturns' :
      Locals.Block.compileOpen paramCtx
          { stmts :=
              (AllocationLowering.lowerReturns artifact.lowerCtx
                artifact.slots.returns paramCtx.layout).1 } =
        some (returnCode, returnCtx) := by
    simpa [Artifact.lowerCtx, Artifact.root,
      Artifact.scratchBindings, Artifact.needsFrame] using hCompileReturns
  have hParamActualLayout :
      paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryCtx.layout).2 :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      hCompileParams'
  have hReturnActualLayout :
      returnCtx.layout =
        (AllocationLowering.lowerReturns artifact.lowerCtx
          artifact.slots.returns paramCtx.layout).2 :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      hCompileReturns'
  have hRecipe :
      AllocationSupport.planRecipeCore? program =
        some compilation.recipe :=
    (AllocationLowering.validatePlan?_eq_some_exact
      compilation.validate).2.2.1
  have hSourceSignature :=
    AllocationSupport.planRecipeCore?_function_signature_valid
      hRecipe artifact.sourceMem
  have hSignatureNodup :
      ((artifact.slots.returns ++ artifact.slots.params).map Prod.fst).Nodup := by
    simpa [List.map_append, artifact.slotsMatch.2.1,
      artifact.slotsMatch.2.2] using hSourceSignature.1
  have hSignatureParts :=
    List.nodup_append.mp (by
      simpa [List.map_append] using hSignatureNodup)
  have hParamsNodup :
      (artifact.slots.params.map Prod.fst).Nodup := hSignatureParts.2.1
  have hFrameFreshParams :
      compilation.frameName ∉ artifact.slots.params.map Prod.fst := by
    intro hFrame
    apply AllocationLowering.freshFrameName_not_mem_params
      compilation.fresh artifact.sourceMem
    rw [← artifact.slotsMatch.2.1]
    exact hFrame
  have hFrameFreshReturns :
      compilation.frameName ∉ artifact.slots.returns.map Prod.fst := by
    intro hFrame
    apply AllocationLowering.freshFrameName_not_mem_returns
      compilation.fresh artifact.sourceMem
    rw [← artifact.slotsMatch.2.2]
    exact hFrame
  have hFrameFresh :
      compilation.frameName ∉
        (artifact.slots.returns ++ artifact.slots.params).map Prod.fst := by
    simpa [List.map_append, hFrameFreshReturns, hFrameFreshParams]
  obtain ⟨added, hEntryEnv⟩ := artifact.planEntry_env_extension
  have hEntryEnv' :
      artifact.planEntry.state.env =
        added ++ artifact.slots.returns ++ artifact.slots.params := by
    simpa [AllocationSupport.functionEnv, List.append_assoc] using hEntryEnv
  have hStateNodup :
      (artifact.planEntry.state.env.map Prod.fst).Nodup := by
    simpa [plan, MixedAllocation.allocationOfState] using hPlanWF.2.1
  have hEntries :
      MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots artifact.planEntry.scope
          artifact.planEntry.state =
        MixedAllocation.stackEntries compilation.stackSlots added ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.returns.reverse ++
          MixedAllocation.stackEntries compilation.stackSlots
            artifact.slots.params.reverse := by
    rw [artifact.planEntryScope]
    exact
      MixedAllocation.AllocationRecipe.stackEntriesForScope_function_of_env_extension
        artifact.slotsLookup hEntryEnv
  have hParameterOrder :
      currentStackOrder plan
          (artifact.slots.params.map Prod.fst).reverse =
        MixedAllocation.stackOrder compilation.stackSlots
          artifact.slots.params.reverse := by
    have hOrder :=
      MixedAllocation.allocationOfState_parameter_stack_filter
        (contract := program.memoryContract)
        (frameWords := compilation.recipe.frameWords)
        (stackSlots := compilation.stackSlots)
        (state := artifact.planEntry.state)
        (added := added) (returns := artifact.slots.returns)
        (params := artifact.slots.params)
        (processed := artifact.slots.params) (pending := [])
        hEntryEnv' hStateNodup (by simp)
    simpa [plan, currentStackOrder, hEntries] using hOrder
  have hBodyOrder :
      currentStackOrder plan
          ((artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse) =
        MixedAllocation.stackOrder compilation.stackSlots
            artifact.slots.returns.reverse ++
          MixedAllocation.stackOrder compilation.stackSlots
            artifact.slots.params.reverse := by
    have hOrder :=
      MixedAllocation.allocationOfState_return_stack_filter
        (contract := program.memoryContract)
        (frameWords := compilation.recipe.frameWords)
        (stackSlots := compilation.stackSlots)
        (state := artifact.planEntry.state)
        (added := added) (returns := artifact.slots.returns)
        (params := artifact.slots.params)
        (processed := artifact.slots.returns) (pending := [])
        hEntryEnv' hStateNodup (by simp)
    simpa [plan, currentStackOrder, hEntries] using hOrder
  have hBodyLayout :
      returnCtx.layout =
        currentStackOrder plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse) ++
          if artifact.needsFrame then [compilation.frameName] else [] := by
    by_cases hNeedsFrame : artifact.needsFrame = true
    · have hEntryLayout :
          artifact.entryCtx.layout =
            (artifact.slots.params.map Prod.fst).reverse ++
              [compilation.frameName] := by
        change artifact.entryLayout = _
        rw [show artifact.entryLayout =
            fn.params.reverse ++ [compilation.frameName] by
          simp [Artifact.entryLayout, hNeedsFrame]]
        rw [artifact.slotsMatch.2.1]
      have hParamPure :=
        AllocationLowering.lowerParams_layout_eq_stackOrder
          (ctx := artifact.lowerCtx) (params := artifact.slots.params)
          (suffix := [compilation.frameName]) hParamsNodup
          (by
            intro localName hParam hFrame
            simp only [List.mem_singleton] at hFrame
            subst localName
            exact hFrameFreshParams hParam)
      have hParamLayout :
          paramCtx.layout =
            currentStackOrder plan
                (artifact.slots.params.map Prod.fst).reverse ++
              [compilation.frameName] := by
        calc
          paramCtx.layout =
              (AllocationLowering.lowerParams artifact.lowerCtx
                artifact.slots.params artifact.entryCtx.layout).2 :=
            hParamActualLayout
          _ =
              MixedAllocation.stackOrder compilation.stackSlots
                  artifact.slots.params.reverse ++
                [compilation.frameName] := by
            simpa [hEntryLayout, Artifact.lowerCtx] using hParamPure
          _ =
              currentStackOrder plan
                  (artifact.slots.params.map Prod.fst).reverse ++
                [compilation.frameName] := by rw [hParameterOrder]
      have hReturnPure :=
        AllocationLowering.lowerReturns_layout_eq_stackOrder
          artifact.lowerCtx artifact.slots.returns paramCtx.layout
      rw [if_pos hNeedsFrame]
      calc
        returnCtx.layout =
            (AllocationLowering.lowerReturns artifact.lowerCtx
              artifact.slots.returns paramCtx.layout).2 :=
          hReturnActualLayout
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.returns.reverse ++
              paramCtx.layout := by
          simpa [Artifact.lowerCtx] using hReturnPure
        _ =
            (MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.params.reverse) ++
              [compilation.frameName] := by
          rw [hParamLayout, hParameterOrder, List.append_assoc]
        _ =
            currentStackOrder plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse) ++
              [compilation.frameName] := by rw [hBodyOrder]
    · have hNeedsFrameFalse : artifact.needsFrame = false :=
        Bool.eq_false_of_not_eq_true hNeedsFrame
      have hEntryLayout :
          artifact.entryCtx.layout =
            (artifact.slots.params.map Prod.fst).reverse := by
        change artifact.entryLayout = _
        rw [show artifact.entryLayout = fn.params.reverse by
          simp [Artifact.entryLayout, hNeedsFrameFalse]]
        rw [artifact.slotsMatch.2.1]
      have hParamPure :=
        AllocationLowering.lowerParams_layout_eq_stackOrder
          (ctx := artifact.lowerCtx) (params := artifact.slots.params)
          (suffix := []) hParamsNodup (by simp)
      have hParamLayout :
          paramCtx.layout =
            currentStackOrder plan
              (artifact.slots.params.map Prod.fst).reverse := by
        calc
          paramCtx.layout =
              (AllocationLowering.lowerParams artifact.lowerCtx
                artifact.slots.params artifact.entryCtx.layout).2 :=
            hParamActualLayout
          _ =
              MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.params.reverse := by
            simpa [hEntryLayout, Artifact.lowerCtx] using hParamPure
          _ =
              currentStackOrder plan
                (artifact.slots.params.map Prod.fst).reverse :=
            hParameterOrder.symm
      have hReturnPure :=
        AllocationLowering.lowerReturns_layout_eq_stackOrder
          artifact.lowerCtx artifact.slots.returns paramCtx.layout
      rw [if_neg hNeedsFrame]
      calc
        returnCtx.layout =
            (AllocationLowering.lowerReturns artifact.lowerCtx
              artifact.slots.returns paramCtx.layout).2 :=
          hReturnActualLayout
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.returns.reverse ++
              paramCtx.layout := by
          simpa [Artifact.lowerCtx] using hReturnPure
        _ =
            MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.returns.reverse ++
              MixedAllocation.stackOrder compilation.stackSlots
                artifact.slots.params.reverse := by
          rw [hParamLayout, hParameterOrder]
        _ =
            currentStackOrder plan
              ((artifact.slots.returns.map Prod.fst).reverse ++
                (artifact.slots.params.map Prod.fst).reverse) :=
          hBodyOrder.symm
        _ = _ ++ [] := by simp
  let planning : AllocationSupport.PlanningState :=
    { allocation := artifact.bodyStart.allocation
      nextScope := 0
      scopes := [] }
  have hBodyAgreement :=
    AllocationLowering.lowerBlockOpen_allocation_eq_planBlockOpen
      fn.body (.function fn.name) planning artifact.lowerCtx fn.returns
      artifact.bodyStart bodyFinal body rfl hLowerBody
  have hBodyPlan :
      artifact.planEntry.state = bodyFinal.allocation := by
    rw [artifact.planEntryState]
    simpa [planning, Artifact.bodyStart] using hBodyAgreement
  refine
    ⟨{ plan := plan
       paramCtx := paramCtx
       returnCtx := returnCtx
       body := body
       bodyFinal := bodyFinal
       returnValues := returnValues
       markerCode := markerCode
       paramCode := paramCode
       returnCode := returnCode
       bodyCode := bodyCode
       bodyCtx := bodyCtx
       returnValueCode := returnValueCode
       cleanup := cleanup
       planLookup := hPlanLookup
       planEq := rfl
       planWF := hPlanWF
       bodyPlan := hBodyPlan
       signatureNodup := hSignatureNodup
       frameFresh := hFrameFresh
       bodyLayout := hBodyLayout
       lowerBody := ?_
       lowerReturnValues := ?_
       compileMarkers := ?_
       compileParams := hCompileParams'
       compileReturns := hCompileReturns'
       compileBody := hCompileBody
       compileReturnValues := hCompileReturnValues
       compileCleanup := hCompileCleanup
       procName := hProcName
       procArgc := ?_
       procRetc := hProcRetc
       procBody := hProcBody }⟩
  · simpa [Artifact.lowerCtx, Artifact.bodyStart, Artifact.entryLayout,
      Artifact.root, Artifact.scratchBindings, Artifact.needsFrame] using
      hLowerBody
  · simpa [Artifact.lowerCtx, Artifact.root,
      Artifact.scratchBindings, Artifact.needsFrame] using
      hLowerReturnValues
  · simpa [Artifact.markers, Artifact.entryCtx, Artifact.entryLayout,
      Artifact.needsFrame, Artifact.scratchBindings] using hCompileMarkers
  · simpa [Artifact.needsFrame, Artifact.scratchBindings,
      Artifact.root] using hProcArgc

theorem Prepared.bodyStartLayout
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact) :
    artifact.bodyStart.layout = prepared.returnCtx.layout := by
  have hParam :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      prepared.compileParams
  have hReturn :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      prepared.compileReturns
  change
    (AllocationLowering.lowerReturns artifact.lowerCtx
      artifact.slots.returns
      (AllocationLowering.lowerParams artifact.lowerCtx
        artifact.slots.params artifact.entryLayout).2).2 =
      prepared.returnCtx.layout
  have hEntryLayout : artifact.entryCtx.layout = artifact.entryLayout := rfl
  rw [← hEntryLayout, ← hParam]
  exact hReturn.symm

theorem Prepared.location_stack_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {calleeName : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation calleeName fn}
    (prepared : Prepared artifact)
    {name : Locals.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          name artifact.bodyStart.allocation.env =
        some slot)
    (hStack :
      AllocationLowering.isStackSlot artifact.lowerCtx slot = true) :
    ∃ depth,
      prepared.plan.location? name = some (.stack depth) := by
  have hMemBody :
      (name, slot) ∈ artifact.bodyStart.allocation.env :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hMemEntry : (name, slot) ∈ artifact.planEntry.state.env := by
    rw [hEnv]
    exact List.mem_append_right added hMemBody
  have hSlot : slot ∈ compilation.stackSlots := by
    have hSlotCtx :=
      (AllocationLowering.isStackSlot_eq_true_iff
        artifact.lowerCtx slot).mp hStack
    rwa [artifact.lowerCtxShared.stackSlots] at hSlotCtx
  have hEntry :
      (name, slot) ∈
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots
          artifact.planEntry.scope artifact.planEntry.state := by
    rw [artifact.planEntryScope]
    exact
      MixedAllocation.AllocationRecipe.mem_stackEntriesForScope_function_of_mem_of_slot_mem
        artifact.slotsLookup hEnv hMemEntry hSlot
  have hNodup :
      (artifact.planEntry.state.env.map Prod.fst).Nodup := by
    have hScopeNodup := prepared.planWF.2.1
    simpa [prepared.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  rw [prepared.planEq]
  exact
    MixedAllocation.allocationOfState_location_stack_of_entry
      hNodup hMemEntry hEntry

theorem Prepared.location_scratch_of_lookup
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {calleeName : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation calleeName fn}
    (prepared : Prepared artifact)
    {name : Locals.Name} {slot : Nat}
    (hLookup :
      AllocationSupport.lookupSlot?
          name artifact.bodyStart.allocation.env =
        some slot)
    (hScratch :
      AllocationLowering.isStackSlot artifact.lowerCtx slot = false) :
    prepared.plan.location? name = some (.scratch slot) := by
  have hMemBody :
      (name, slot) ∈ artifact.bodyStart.allocation.env :=
    AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
  obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
  have hMemEntry : (name, slot) ∈ artifact.planEntry.state.env := by
    rw [hEnv]
    exact List.mem_append_right added hMemBody
  have hSlot : slot ∉ compilation.stackSlots := by
    have hSlotCtx :=
      (AllocationLowering.isStackSlot_eq_false_iff
        artifact.lowerCtx slot).mp hScratch
    rwa [artifact.lowerCtxShared.stackSlots] at hSlotCtx
  have hNotEntry :
      (name, slot) ∉
        MixedAllocation.AllocationRecipe.stackEntriesForScope
          compilation.recipe compilation.stackSlots
          artifact.planEntry.scope artifact.planEntry.state :=
    MixedAllocation.AllocationRecipe.not_mem_stackEntriesForScope_of_slot_not_mem
      hSlot
  have hNodup :
      (artifact.planEntry.state.env.map Prod.fst).Nodup := by
    have hScopeNodup := prepared.planWF.2.1
    simpa [prepared.planEq, MixedAllocation.allocationOfState] using
      hScopeNodup
  rw [prepared.planEq]
  exact
    MixedAllocation.allocationOfState_location_scratch_of_not_entry
      hNodup hMemEntry hNotEntry

theorem Prepared.bodyCompiler
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {calleeName : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation calleeName fn}
    (prepared : Prepared artifact) :
    AllocationContext.ActivationExprContext artifact.lowerCtx
      artifact.bodyStart prepared.returnCtx prepared.plan
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      prepared.bodyMode := by
  let live :=
    (artifact.slots.returns.map Prod.fst).reverse ++
      (artifact.slots.params.map Prod.fst).reverse
  have hLayout :
      prepared.returnCtx.layout = artifact.bodyStart.layout :=
    prepared.bodyStartLayout.symm
  have bindingOfLive :
      ∀ localName, localName ∈ live →
        ∃ slot,
          (localName, slot) ∈
            artifact.slots.returns ++ artifact.slots.params := by
    intro localName hLive
    have hName :
        localName ∈
          (artifact.slots.returns ++ artifact.slots.params).map Prod.fst := by
      simpa [live, List.map_append] using hLive
    rcases List.mem_map.mp hName with ⟨binding, hBinding, hEq⟩
    rcases binding with ⟨candidate, slot⟩
    simp only at hEq
    subst candidate
    exact ⟨slot, hBinding⟩
  have slotLookup :
      ∀ localName, localName ∈ live →
        ∃ slot,
          AllocationSupport.lookupSlot?
              localName artifact.bodyStart.allocation.env =
            some slot := by
    intro localName hLive
    obtain ⟨slot, hBinding⟩ := bindingOfLive localName hLive
    refine ⟨slot, ?_⟩
    exact
      AllocationSupport.lookupSlot?_eq_some_of_mem
        prepared.signatureNodup hBinding
  have hFrameFresh :
      compilation.frameName ∉ currentStackOrder prepared.plan live := by
    intro hFrame
    have hFrameLive := mem_live_of_mem_currentStackOrder hFrame
    apply prepared.frameFresh
    simpa [live, List.map_append] using hFrameLive
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hBodyLayout :
        artifact.bodyStart.layout =
          currentStackOrder prepared.plan live ++
            [compilation.frameName] := by
      rw [prepared.bodyStartLayout, prepared.bodyLayout,
        if_pos hNeedsFrame]
    have hBodyMode :
        prepared.bodyMode =
          .scratch (currentStackOrder prepared.plan live).length
            compilation.recipe.frameWords := by
      simp [Prepared.bodyMode, Artifact.mode, hNeedsFrame,
        ActivationMode.atStackDepth, live]
    rw [hBodyMode]
    apply AllocationContext.ActivationExprContext.scratch_of_layout
      prepared.planWF hLayout hBodyLayout
      (by simpa only [live]) hFrameFresh
    · exact slotLookup
    · intro localName slot hLive hLookup hStack
      exact prepared.location_stack_of_lookup hLookup hStack
    · intro localName slot hLive hLookup hScratch
      exact prepared.location_scratch_of_lookup hLookup hScratch
  · have hNeedsFrameFalse : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hBodyLayout :
        artifact.bodyStart.layout =
          currentStackOrder prepared.plan live := by
      rw [prepared.bodyStartLayout, prepared.bodyLayout,
        if_neg hNeedsFrame]
      simpa only [live, List.append_nil]
    have hRootNoFrame :
        AllocationLowering.rootNeedsFrame compilation.recipe
            compilation.stackSlots (.function fn.name) = false := by
      simpa [Artifact.needsFrame, Artifact.scratchBindings, Artifact.root,
        AllocationLowering.rootNeedsFrame] using hNeedsFrameFalse
    have allStack :
        ∀ localName slot,
          localName ∈ live →
          AllocationSupport.lookupSlot?
              localName artifact.bodyStart.allocation.env =
            some slot →
          AllocationLowering.isStackSlot artifact.lowerCtx slot = true := by
      intro localName slot hLive hLookup
      have hMemBody :=
        AllocationSupport.mem_of_lookupSlot?_eq_some hLookup
      obtain ⟨added, hEnv⟩ := artifact.planEntry_env_extension
      have hMemEntry :
          (localName, slot) ∈ artifact.planEntry.state.env := by
        rw [hEnv]
        exact List.mem_append_right added hMemBody
      have hSlot :=
        AllocationLowering.slot_mem_of_function_rootNeedsFrame_eq_false
          artifact.planEntryMem artifact.planEntryScope hMemEntry hRootNoFrame
      simpa [AllocationLowering.isStackSlot, Artifact.lowerCtx,
        Compilation.lowerCtx] using hSlot
    have stackLocation :
        ∀ localName, localName ∈ live →
          ∃ planDepth,
            prepared.plan.location? localName = some (.stack planDepth) := by
      intro localName hLive
      obtain ⟨slot, hLookup⟩ := slotLookup localName hLive
      exact prepared.location_stack_of_lookup hLookup
        (allStack localName slot hLive hLookup)
    have stackOnly : LiveStackOnly prepared.plan live := by
      intro localName slot hLive hScratchLocation
      obtain ⟨planDepth, hStackLocation⟩ :=
        stackLocation localName hLive
      rw [hStackLocation] at hScratchLocation
      simp at hScratchLocation
    have hFrameAbsent :
        artifact.lowerCtx.frameName ∉ artifact.bodyStart.layout := by
      rw [hBodyLayout]
      simpa [Artifact.lowerCtx, Compilation.lowerCtx] using hFrameFresh
    have hBodyMode : prepared.bodyMode = .stack := by
      simp [Prepared.bodyMode, Artifact.mode, hNeedsFrameFalse,
        ActivationMode.atStackDepth]
    rw [hBodyMode]
    apply AllocationContext.ActivationExprContext.stack_of_layout
      prepared.planWF hLayout hBodyLayout.symm hFrameAbsent stackOnly
      stackLocation slotLookup

theorem Artifact.bodyScoped
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    (artifact : Artifact compilation name fn)
    (hProgramScoped : program.Scoped) :
    Functions.Scope.Block.Scoped
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      fn.body := by
  have hFnScoped : fn.Scoped :=
    Functions.FunList.scoped_of_mem hProgramScoped.1 artifact.sourceMem
  exact
    Functions.Scope.Block.Scoped.of_env_equiv
      (before := fn.returns ++ fn.params)
      (after :=
        (artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
      (by
        intro localName
        simp [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2])
      (Functions.FunDef.bodyScoped hFnScoped)

/-- Package a compiler-selected function body as an ordinary recursive root. -/
def Prepared.rootArtifact
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    (hProgramScoped : program.Scoped) :
    RootArtifact compilation :=
  { functionRoot? := some fn.name
    rootScope := .function fn.name
    slots := artifact.slots
    returns := fn.returns
    sourceBlock := fn.body
    startState := artifact.bodyStart
    startLocals := prepared.returnCtx
    planning :=
      { allocation := artifact.bodyStart.allocation
        nextScope := 0
        scopes := [] }
    planningAllocation := rfl
    rootScopeOwner := rfl
    plan := prepared.plan
    planWF := prepared.planWF
    finalState := prepared.bodyFinal
    finalLocals := prepared.bodyCtx
    planEq := by
      rw [prepared.planEq, artifact.planEntryScope, prepared.bodyPlan]
    finalFrameFresh := by
      rw [← prepared.bodyPlan]
      exact artifact.frameName_not_mem_planEntry_env
    lexicalFrameFresh := by
      intro entry hEntry
      exact artifact.frameName_not_mem_lexical_entry_env hEntry
    scopeStackEntries := by
      intro scope state added hRoot hEnv
      exact
        MixedAllocation.AllocationRecipe.stackEntriesForScope_of_functionRoot_env_extension
          hRoot artifact.slotsLookup hEnv
    plannedFinal := by
      calc
        (AllocationSupport.planBlockOpen (.function fn.name)
            { allocation := artifact.bodyStart.allocation
              nextScope := 0
              scopes := [] }
            fn.body).allocation =
            artifact.planEntry.state := by
          simpa [Artifact.bodyStart] using artifact.planEntryState.symm
        _ = prepared.bodyFinal.allocation := prepared.bodyPlan
    plannedScopes := by
      simpa [Artifact.bodyStart] using artifact.bodyScopesMem
    lowered := prepared.body
    compiled := prepared.bodyCode
    lowerCtx := artifact.lowerCtx
    lowerCtxShared := artifact.lowerCtxShared
    lower := prepared.lowerBody
    compile := prepared.compileBody
    sourceScoped := artifact.bodyScoped hProgramScoped
    activeEnv := by
      refine ⟨[], ?_, ?_⟩
      · simp [Artifact.bodyStart]
      · simp }

/-- The selected callee body enters the shared recursive cursor interface. -/
def Prepared.rootCursor
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : Artifact compilation name fn}
    (prepared : Prepared artifact)
    (hProgramScoped : program.Scoped) :
    CoreCursor (prepared.rootArtifact hProgramScoped)
      (.function fn.name)
      ((artifact.slots.returns.map Prod.fst).reverse ++
        (artifact.slots.params.map Prod.fst).reverse)
      fn.body artifact.bodyStart prepared.returnCtx :=
  (prepared.rootArtifact hProgramScoped).cursor

end SelectedCallee

end AllocationInteractionCall
end Functions
end EvmCompiler
