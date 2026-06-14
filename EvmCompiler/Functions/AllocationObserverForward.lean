import EvmCompiler.Functions.AllocationObserverCall
import EvmCompiler.Functions.AllocationObserverLoop
import EvmCompiler.Functions.AllocationObserverSwitch

namespace EvmCompiler
namespace Functions
namespace AllocationObserverForward

open AllocationObserverRelation

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

/--
The compiler-owned global data shared by the main body and every function
activation in one allocation lowering.

This structure contains only deterministic outputs of the existing validator
and compiler. It is constructed from the public lowering equation below and
is never a caller-supplied certificate at the eventual public boundary.
-/
structure Compilation
    (allocation : Locals.Allocation.ProgramPlan)
    (program : Functions.Program)
    (expressions : Expressions.Program) where
  recipe : AllocationSupport.AllocationRecipe
  stackSlots : MixedAllocation.SlotSet
  frameName : Locals.Name
  validate :
    AllocationLowering.validatePlan? allocation program =
      some (recipe, stackSlots)
  fresh :
    AllocationLowering.freshFrameName program = some frameName
  lower :
    AllocationLowering.lowerExpressionsFromAllocation?
        allocation program =
      some expressions

theorem Compilation.of_lowering
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (hLower :
      AllocationLowering.lowerExpressionsFromAllocation?
          allocation program =
        some expressions) :
    Nonempty (Compilation allocation program expressions) := by
  have hWhole := hLower
  unfold AllocationLowering.lowerExpressionsFromAllocation? at hLower
  cases hLocals :
      AllocationLowering.lowerLocalsFromAllocation? allocation program with
  | none =>
      simp [hLocals] at hLower
  | some locals =>
      unfold AllocationLowering.lowerLocalsFromAllocation? at hLocals
      cases hValidate :
          AllocationLowering.validatePlan? allocation program with
      | none =>
          simp [hValidate] at hLocals
      | some validated =>
          rcases validated with ⟨recipe, stackSlots⟩
          cases hFresh :
              AllocationLowering.freshFrameName program with
          | none =>
              simp [hValidate, hFresh] at hLocals
          | some frameName =>
              exact
                ⟨{ recipe := recipe
                   stackSlots := stackSlots
                   frameName := frameName
                   validate := hValidate
                   fresh := hFresh
                   lower := hWhole }⟩

def Compilation.frameConfig?
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions) :
    Option AllocationSupport.ScratchFrameConfig :=
  AllocationSupport.scratchFrameConfig?
    program.memoryContract compilation.recipe.frameWords

def Compilation.lowerCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    (root : Locals.Allocation.ScopeId)
    (scratchBindings : List (Locals.Name × Nat)) :
    AllocationLowering.Ctx :=
  { functions := compilation.recipe.functionSlots
    frameConfig? := compilation.frameConfig?
    frameName := compilation.frameName
    stackSlots := compilation.stackSlots
    root := root
    scratchBindings := scratchBindings
    frameFunctions :=
      AllocationLowering.frameFunctions
        compilation.recipe compilation.stackSlots }

/--
The global portion of an allocation-lowering context. Roots and scratch
bindings vary by activation; these fields must remain identical throughout one
whole-program lowering.
-/
structure Compilation.CtxShared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    (ctx : AllocationLowering.Ctx) : Prop where
  functions : ctx.functions = compilation.recipe.functionSlots
  frameConfig : ctx.frameConfig? = compilation.frameConfig?
  frameName : ctx.frameName = compilation.frameName
  stackSlots : ctx.stackSlots = compilation.stackSlots
  frameFunctions :
    ctx.frameFunctions =
      AllocationLowering.frameFunctions
        compilation.recipe compilation.stackSlots

theorem Compilation.lowerCtx_shared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    (root : Locals.Allocation.ScopeId)
    (scratchBindings : List (Locals.Name × Nat)) :
    compilation.CtxShared
      (compilation.lowerCtx root scratchBindings) := by
  constructor <;> rfl

theorem Compilation.selectedCallee
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (hFind :
      Functions.Source.FunList.find? name program.functions = some fn) :
    Nonempty
      (AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :=
  AllocationObserverCall.SelectedCallee.of_lowering
    compilation.lower hFind

theorem Compilation.selected_agrees
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    artifact.recipe = compilation.recipe ∧
      artifact.stackSlots = compilation.stackSlots ∧
      artifact.frameName = compilation.frameName := by
  have hValidated :
      (artifact.recipe, artifact.stackSlots) =
        (compilation.recipe, compilation.stackSlots) :=
    Option.some.inj (artifact.validate.symm.trans compilation.validate)
  have hFrameName :
      artifact.frameName = compilation.frameName :=
    Option.some.inj (artifact.fresh.symm.trans compilation.fresh)
  exact
    ⟨congrArg Prod.fst hValidated,
      congrArg Prod.snd hValidated, hFrameName⟩

theorem Compilation.selected_lowerCtx
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    artifact.lowerCtx =
      compilation.lowerCtx artifact.root artifact.scratchBindings := by
  obtain ⟨hRecipe, hSlots, hFrameName⟩ :=
    compilation.selected_agrees artifact
  simp [AllocationObserverCall.SelectedCallee.Artifact.lowerCtx,
    Compilation.lowerCtx, Compilation.frameConfig?,
    hRecipe, hSlots, hFrameName]

theorem Compilation.selected_shared
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    compilation.CtxShared artifact.lowerCtx := by
  rw [compilation.selected_lowerCtx artifact]
  exact
    compilation.lowerCtx_shared artifact.root artifact.scratchBindings

theorem Compilation.call_needsFrame_iff
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {callerCtx : AllocationLowering.Ctx}
    (hCaller : compilation.CtxShared callerCtx)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn) :
    name ∈ callerCtx.frameFunctions ↔ artifact.needsFrame = true := by
  obtain ⟨hRecipe, hSlots, _hFrameName⟩ :=
    compilation.selected_agrees artifact
  rw [hCaller.frameFunctions]
  simpa [hRecipe, hSlots] using artifact.mem_frameFunctions_iff

theorem Compilation.selected_frameWords_pos
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn)
    (hNeedsFrame : artifact.needsFrame = true) :
    0 < compilation.recipe.frameWords := by
  obtain ⟨hRecipe, hSlots, _hFrameName⟩ :=
    compilation.selected_agrees artifact
  have hBindings :
      artifact.scratchBindings =
        AllocationLowering.scratchBindingsForRoot
          compilation.recipe compilation.stackSlots artifact.root := by
    simp [AllocationObserverCall.SelectedCallee.Artifact.scratchBindings,
      hRecipe, hSlots]
  have hRootNeeds :
      AllocationLowering.rootNeedsFrame
          compilation.recipe compilation.stackSlots artifact.root =
        true := by
    unfold AllocationLowering.rootNeedsFrame
    rw [← hBindings]
    exact hNeedsFrame
  exact
    AllocationLowering.frameWords_pos_of_validate_of_rootNeedsFrame
      compilation.validate hRootNeeds

theorem Compilation.selected_config_frameWords_pos
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    (artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn)
    {config : Frame.Config}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hNeedsFrame : artifact.needsFrame = true) :
    0 < config.frameWords := by
  obtain
      ⟨_reservation, _hReservation, _hAllocator, _hFirst, _hLimit,
        hWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
    AllocationSupport.scratchFrameConfig?_sound hConfig
  rw [hWords]
  exact compilation.selected_frameWords_pos artifact hNeedsFrame

namespace Callee

/--
Construct the complete regular target execution of one compiler-selected
callee from its checked artifact and one recursive body-preservation result.

The recursive callback is private proof plumbing for the forthcoming
source-fuel theorem. All generated code, layouts, procedure lookup, preludes,
and return epilogues are supplied by `SelectedCallee.Prepared`.
-/
theorem prepared_regular
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {callerDepth calleeDepth frameBase : Nat}
    {transcript : Trace}
    {sourceBodyStart sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    {returnValues : List Word}
    {finalSourceCtx : Functions.Source.Ctx}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase prepared.mode sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source)
    (hReady : Frame.AllocatorReady config calleeDepth targetEntry)
    (hOwned :
      Frame.ActivationOwned config calleeDepth frameBase prepared.mode)
    (hBody :
      ∀ {targetBodyStart : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        ∃ targetBodyFinal finalMode,
          AllocationObserverStatement.Sequence.RegularBlockRuntimeInvariantForward
            program.memoryContract config calleeDepth transcript
            artifact.lowerCtx prepared.bodyFinal prepared.bodyCtx
            prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            finalMode program (Functions.Source.Effectful.FunDef.bodyCtx fn)
            fn.body sourceBodyStart expressions.toStructured
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart sourceBodyFinal targetBodyFinal finalSourceCtx)
    (hReturns :
      Functions.Source.Store.lookupMany fn.returns
          sourceBodyFinal.source.vars =
        some returnValues)
    (hProtectedBound :
      AllocationObserverCall.RegularCallee.protectedBound
          calleeDepth prepared.mode =
        callerDepth + 1) :
    ∃ calleeFinal fuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured fuel artifact.lowerProc.toStructured.body
        targetEntry
        (Structured.EffectSemantics.Outcome.regular calleeFinal) ∧
      calleeFinal.source.evm.stack = returnValues.reverse ∧
      sourceBodyFinal.cursor = calleeFinal.cursor ∧
      Compiler.MemoryRelation.MachineRel program.memoryContract
        sourceBodyFinal.source.shared.toMachineState
        calleeFinal.source.evm.toMachineState ∧
      sourceBodyFinal.source.shared.toState =
        calleeFinal.source.evm.toSharedState.toState ∧
      Frame.BoundedEffect config calleeDepth (callerDepth + 1)
        targetEntry calleeFinal := by
  have hBodyEnv :
      artifact.bodyStart.allocation.env =
        AllocationSupport.functionEnv artifact.slots := by
    rfl
  have hParamLayout :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      prepared.compileParams
  have hReturnLayout :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      prepared.compileReturns
  have hParamLayout' :
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryLayout).2 := by
    simpa [
      AllocationObserverCall.SelectedCallee.Artifact.entryCtx] using
      hParamLayout
  have hBodyLayout :
      artifact.bodyStart.layout = prepared.returnCtx.layout := by
    simp only [
      AllocationObserverCall.SelectedCallee.Artifact.bodyStart]
    rw [← hParamLayout', ← hReturnLayout]
  obtain
      ⟨preludeCode, targetBodyStart, preludeFuel,
        hPreludeCompile, hPreludeEval, hPreludeInvariant,
        hPreludeSame, hPreludeEffect⟩ :=
    AllocationObserverCall.FunctionPrelude.forward_invariant
      (targetProgram := expressions.toStructured)
      prepared.prelude hEntry hEntryStackLength hZero prepared.planWF
      (AllocationObserverCall.FunctionPrelude.SelectedCallee.Prepared.scratchAuthorized
        prepared hConfig)
      hConfig hReady hOwned
      hBodyEnv hBodyLayout hDefined
  have hExpectedPreludeCompile :=
    Locals.Block.compileOpen_append
      prepared.compileParams prepared.compileReturns
  have hPreludeCode :
      preludeCode = prepared.paramCode ++ prepared.returnCode := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (hPreludeCompile.symm.trans hExpectedPreludeCompile))
  subst preludeCode
  obtain ⟨targetBodyFinal, finalMode, hBodyForward⟩ :=
    hBody hPreludeInvariant
  rcases hBodyForward with
    ⟨_sourceFuel, bodyFuel, _hSourceBody, hTargetBody,
      hBodyInvariant, hBodySame, hBodyEffect⟩
  have hReturnsLive :
      ∀ returnName, returnName ∈ fn.returns →
        returnName ∈
          (artifact.slots.returns.map Prod.fst).reverse ++
            (artifact.slots.params.map Prod.fst).reverse := by
    intro returnName hReturn
    apply List.mem_append_left
    rw [List.mem_reverse, artifact.slotsMatch.2.2]
    exact hReturn
  obtain
      ⟨_afterValues, calleeFinal, _hValuesRun, _hCleanupRun,
        hReturnEval, hReturnedStack, hCursor, hMachine, hWorld,
        hReturnEffect⟩ :=
    AllocationObserverCall.FunctionReturn.forward_regular
      hConfig hBodyInvariant hReturnsLive hReturns
      prepared.lowerReturnValues prepared.compileReturnValues
      prepared.compileCleanup
  have hExpectedMarkers :=
    AllocationObserverCall.EntryMarkers.compileOpen
      (localsCtx := artifact.entryCtx)
      (entryLayout := artifact.entryLayout)
      (baseDepth := fn.params.length)
      (scratchBindings := artifact.scratchBindings)
      (needsFrame := artifact.needsFrame)
  have hMarkerCode :
      prepared.markerCode =
        [Expressions.Stmt.code
          [Structured.BasicInstr.bindLocals 0 artifact.entryLayout]] ++
        if artifact.needsFrame then
          [Expressions.Stmt.code
            (AllocationSupport.bindScratchBindingsCode
              fn.params.length artifact.scratchBindings)]
        else
          [] := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (prepared.compileMarkers.symm.trans hExpectedMarkers))
  obtain ⟨markerFuel, hMarkerEvalRaw⟩ :=
    AllocationObserverCall.EntryMarkers.eval expressions.toStructured
      artifact.entryLayout fn.params.length artifact.scratchBindings
      artifact.needsFrame targetEntry
  have hMarkerEval :
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured markerFuel
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode }
        targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry) := by
    rw [hMarkerCode]
    cases hNeedsFrame : artifact.needsFrame <;>
      simp [hNeedsFrame, Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] at hMarkerEvalRaw ⊢
    · exact hMarkerEvalRaw
    · exact hMarkerEvalRaw
  have hProcShape :
      artifact.lowerProc.toStructured.body.stmts =
        (Expressions.StmtList.toStructured prepared.markerCode ++
          Expressions.StmtList.toStructured
            (prepared.paramCode ++ prepared.returnCode)) ++
          Expressions.StmtList.toStructured prepared.bodyCode ++
        Expressions.StmtList.toStructured
            (Locals.codeStmt prepared.returnValueCode ++
              Locals.codeStmt prepared.cleanup) := by
    have hShape :=
      congrArg Expressions.StmtList.toStructured prepared.procBody
    have hBodyStructured :
        artifact.lowerProc.body.toStructured.stmts =
          Expressions.StmtList.toStructured
            artifact.lowerProc.body.stmts := by
      cases artifact.lowerProc.body
      rfl
    change artifact.lowerProc.body.toStructured.stmts = _
    rw [hBodyStructured]
    simpa only [Expressions.StmtList.toStructured_append,
      List.append_assoc] using hShape
  have hBodyEffect' :
      Frame.ActivationEffect config calleeDepth finalMode
        targetBodyStart targetBodyFinal :=
    hBodyEffect.mode_of_sameFrame hBodySame
  have hEntryFinalSame :
      SameFrame prepared.mode finalMode :=
    hPreludeSame.trans hBodySame
  obtain ⟨fuel, hEval, hEffect⟩ :=
    AllocationObserverCall.RegularCallee.compose
      (callerDepth := callerDepth)
      (calleeDepth := calleeDepth)
      (entryMode := prepared.mode)
      (bodyMode := finalMode)
      (proc := artifact.lowerProc.toStructured)
      (markerBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode })
      (preludeBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) })
      (bodyBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.bodyCode })
      (returnBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (Locals.codeStmt prepared.returnValueCode ++
                Locals.codeStmt prepared.cleanup) })
      hProcShape hMarkerEval
      (by
        simpa only [Expressions.Block.toStructured] using hPreludeEval)
      hTargetBody hReturnEval
      hEntryFinalSame
      hPreludeEffect hBodyEffect' hReturnEffect hProtectedBound
  exact
    ⟨calleeFinal, fuel, hEval, hReturnedStack, hCursor, hMachine,
      hWorld, hEffect⟩

/--
Construct the complete target execution of a compiler-selected callee whose
source body reaches `leave`. The callback supplies the recursively preserved
body exit; the compiler-owned regular epilogue is then proved unreachable by
`RegularCallee.compose_leave`.
-/
theorem prepared_leave
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {callerDepth calleeDepth frameBase : Nat}
    {transcript : Trace}
    {sourceBodyStart sourceBodyFinal :
      Functions.ObserverSemantics.State transcript}
    {targetEntry : Structured.ObserverSemantics.State transcript}
    {returnValues : List Word}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config)
    (hEntry :
      ActivationCalleeEntryRel
        program.memoryContract prepared.plan [] artifact.slots.params
        frameBase prepared.mode sourceBodyStart targetEntry)
    (hEntryStackLength :
      targetEntry.source.evm.stack.length =
        artifact.entryCtx.layout.length)
    (hZero :
      ∀ returnName, returnName ∈ artifact.slots.returns.map Prod.fst →
        sourceBodyStart.source.vars returnName =
          some AllocationSupport.zeroWord)
    (hDefined :
      LiveDefined
        ((artifact.slots.returns.map Prod.fst).reverse ++
          (artifact.slots.params.map Prod.fst).reverse)
        sourceBodyStart.source)
    (hReady : Frame.AllocatorReady config calleeDepth targetEntry)
    (hOwned :
      Frame.ActivationOwned config calleeDepth frameBase prepared.mode)
    (hBody :
      ∀ {targetBodyStart : Structured.ObserverSemantics.State transcript},
        AllocationObserverContext.ActivationRuntimeInvariant
            program.memoryContract config calleeDepth artifact.lowerCtx
            artifact.bodyStart prepared.returnCtx prepared.plan
            ((artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse)
            frameBase
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            sourceBodyStart targetBodyStart →
        ∃ targetBodyFinal finalMode bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            { stmts :=
                Expressions.StmtList.toStructured prepared.bodyCode }
            targetBodyStart
            (Structured.EffectSemantics.Outcome.leave targetBodyFinal) ∧
          SameFrame
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            finalMode ∧
          Frame.ActivationEffect config calleeDepth
            (prepared.mode.atStackDepth
              (currentStackOrder prepared.plan
                ((artifact.slots.returns.map Prod.fst).reverse ++
                  (artifact.slots.params.map Prod.fst).reverse)).length)
            targetBodyStart targetBodyFinal ∧
          targetBodyFinal.source.evm.stack = returnValues.reverse ∧
          sourceBodyFinal.cursor = targetBodyFinal.cursor ∧
          Compiler.MemoryRelation.MachineRel program.memoryContract
            sourceBodyFinal.source.shared.toMachineState
            targetBodyFinal.source.evm.toMachineState ∧
          sourceBodyFinal.source.shared.toState =
            targetBodyFinal.source.evm.toSharedState.toState)
    (hProtectedBound :
      AllocationObserverCall.RegularCallee.protectedBound
          calleeDepth prepared.mode =
        callerDepth + 1) :
    ∃ calleeFinal fuel,
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured fuel artifact.lowerProc.toStructured.body
        targetEntry
        (Structured.EffectSemantics.Outcome.leave calleeFinal) ∧
      calleeFinal.source.evm.stack = returnValues.reverse ∧
      sourceBodyFinal.cursor = calleeFinal.cursor ∧
      Compiler.MemoryRelation.MachineRel program.memoryContract
        sourceBodyFinal.source.shared.toMachineState
        calleeFinal.source.evm.toMachineState ∧
      sourceBodyFinal.source.shared.toState =
        calleeFinal.source.evm.toSharedState.toState ∧
      Frame.BoundedEffect config calleeDepth (callerDepth + 1)
        targetEntry calleeFinal := by
  have hBodyEnv :
      artifact.bodyStart.allocation.env =
        AllocationSupport.functionEnv artifact.slots := by
    rfl
  have hParamLayout :=
    AllocationLowering.lowerParams_compileOpen_final_layout
      prepared.compileParams
  have hReturnLayout :=
    AllocationLowering.lowerReturns_compileOpen_final_layout
      prepared.compileReturns
  have hParamLayout' :
      prepared.paramCtx.layout =
        (AllocationLowering.lowerParams artifact.lowerCtx
          artifact.slots.params artifact.entryLayout).2 := by
    simpa [
      AllocationObserverCall.SelectedCallee.Artifact.entryCtx] using
      hParamLayout
  have hBodyLayout :
      artifact.bodyStart.layout = prepared.returnCtx.layout := by
    simp only [
      AllocationObserverCall.SelectedCallee.Artifact.bodyStart]
    rw [← hParamLayout', ← hReturnLayout]
  obtain
      ⟨preludeCode, targetBodyStart, preludeFuel,
        hPreludeCompile, hPreludeEval, hPreludeInvariant,
        hPreludeSame, hPreludeEffect⟩ :=
    AllocationObserverCall.FunctionPrelude.forward_invariant
      (targetProgram := expressions.toStructured)
      prepared.prelude hEntry hEntryStackLength hZero prepared.planWF
      (AllocationObserverCall.FunctionPrelude.SelectedCallee.Prepared.scratchAuthorized
        prepared hConfig)
      hConfig hReady hOwned hBodyEnv hBodyLayout hDefined
  have hExpectedPreludeCompile :=
    Locals.Block.compileOpen_append
      prepared.compileParams prepared.compileReturns
  have hPreludeCode :
      preludeCode = prepared.paramCode ++ prepared.returnCode := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (hPreludeCompile.symm.trans hExpectedPreludeCompile))
  subst preludeCode
  obtain
      ⟨targetBodyFinal, finalMode, bodyFuel, hTargetBody,
        hBodySame, hBodyEffect, hReturnedStack, hCursor, hMachine,
        hWorld⟩ :=
    hBody hPreludeInvariant
  have hExpectedMarkers :=
    AllocationObserverCall.EntryMarkers.compileOpen
      (localsCtx := artifact.entryCtx)
      (entryLayout := artifact.entryLayout)
      (baseDepth := fn.params.length)
      (scratchBindings := artifact.scratchBindings)
      (needsFrame := artifact.needsFrame)
  have hMarkerCode :
      prepared.markerCode =
        [Expressions.Stmt.code
          [Structured.BasicInstr.bindLocals 0 artifact.entryLayout]] ++
        if artifact.needsFrame then
          [Expressions.Stmt.code
            (AllocationSupport.bindScratchBindingsCode
              fn.params.length artifact.scratchBindings)]
        else
          [] := by
    exact
      congrArg Prod.fst
        (Option.some.inj
          (prepared.compileMarkers.symm.trans hExpectedMarkers))
  obtain ⟨markerFuel, hMarkerEvalRaw⟩ :=
    AllocationObserverCall.EntryMarkers.eval expressions.toStructured
      artifact.entryLayout fn.params.length artifact.scratchBindings
      artifact.needsFrame targetEntry
  have hMarkerEval :
      Structured.ObserverSemantics.Block.Eval
        expressions.toStructured markerFuel
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode }
        targetEntry
        (Structured.EffectSemantics.Outcome.regular targetEntry) := by
    rw [hMarkerCode]
    cases hNeedsFrame : artifact.needsFrame <;>
      simp [hNeedsFrame, Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured] at hMarkerEvalRaw ⊢
    · exact hMarkerEvalRaw
    · exact hMarkerEvalRaw
  have hProcShape :
      artifact.lowerProc.toStructured.body.stmts =
        (Expressions.StmtList.toStructured prepared.markerCode ++
          Expressions.StmtList.toStructured
            (prepared.paramCode ++ prepared.returnCode)) ++
          Expressions.StmtList.toStructured prepared.bodyCode ++
          Expressions.StmtList.toStructured
            (Locals.codeStmt prepared.returnValueCode ++
              Locals.codeStmt prepared.cleanup) := by
    have hShape :=
      congrArg Expressions.StmtList.toStructured prepared.procBody
    have hBodyStructured :
        artifact.lowerProc.body.toStructured.stmts =
          Expressions.StmtList.toStructured
            artifact.lowerProc.body.stmts := by
      cases artifact.lowerProc.body
      rfl
    change artifact.lowerProc.body.toStructured.stmts = _
    rw [hBodyStructured]
    simpa only [Expressions.StmtList.toStructured_append,
      List.append_assoc] using hShape
  have hBodyEffect' :
      Frame.ActivationEffect config calleeDepth finalMode
        targetBodyStart targetBodyFinal :=
    hBodyEffect.mode_of_sameFrame hBodySame
  have hEntryFinalSame :
      SameFrame prepared.mode finalMode :=
    hPreludeSame.trans hBodySame
  obtain ⟨fuel, hEval, hEffect⟩ :=
    AllocationObserverCall.RegularCallee.compose_leave
      (callerDepth := callerDepth)
      (calleeDepth := calleeDepth)
      (entryMode := prepared.mode)
      (bodyMode := finalMode)
      (proc := artifact.lowerProc.toStructured)
      (markerBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.markerCode })
      (preludeBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (prepared.paramCode ++ prepared.returnCode) })
      (bodyBlock :=
        { stmts :=
            Expressions.StmtList.toStructured prepared.bodyCode })
      (returnBlock :=
        { stmts :=
            Expressions.StmtList.toStructured
              (Locals.codeStmt prepared.returnValueCode ++
                Locals.codeStmt prepared.cleanup) })
      hProcShape hMarkerEval
      (by
        simpa only [Expressions.Block.toStructured] using hPreludeEval)
      hTargetBody hEntryFinalSame hPreludeEffect hBodyEffect'
      hProtectedBound
  exact
    ⟨targetBodyFinal, fuel, hEval, hReturnedStack, hCursor, hMachine,
      hWorld, hEffect⟩

end Callee

namespace Call

private theorem eval_phases
    {transcript : Trace}
    {targetProgram : Structured.Program}
    {name : Structured.Name}
    {argsCode stores : Structured.Code}
    {releaseCode : List Structured.Stmt}
    {target targetAfterArgs callFinal targetAssigned targetFinal :
      Structured.ObserverSemantics.State transcript}
    {bodyFuel releaseFuel : Nat}
    (hArgs :
      Structured.ObserverSemantics.Code.run argsCode target =
        .ok targetAfterArgs)
    (hCall :
      Structured.ObserverSemantics.Stmt.Eval targetProgram (bodyFuel + 1)
        (.call name) targetAfterArgs
        (Structured.EffectSemantics.Outcome.regular callFinal))
    (hStores :
      Structured.ObserverSemantics.Code.run stores callFinal =
        .ok targetAssigned)
    (hRelease :
      Structured.ObserverSemantics.Block.Eval targetProgram releaseFuel
        { stmts := releaseCode } targetAssigned
        (Structured.EffectSemantics.Outcome.regular targetFinal)) :
    ∃ fuel,
      Structured.ObserverSemantics.Block.Eval targetProgram fuel
        { stmts :=
            [Structured.Stmt.code argsCode] ++
              [Structured.Stmt.call name] ++
              [Structured.Stmt.code stores] ++ releaseCode }
        target
        (Structured.EffectSemantics.Outcome.regular targetFinal) := by
  have hArgsBlock :
      Structured.ObserverSemantics.Block.Eval targetProgram 2
        { stmts := [Structured.Stmt.code argsCode] } target
        (Structured.EffectSemantics.Outcome.regular targetAfterArgs) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hArgs)
      Structured.EffectSemantics.Block.Eval.nil
  have hCallBlock :
      Structured.ObserverSemantics.Block.Eval targetProgram (bodyFuel + 2)
        { stmts := [Structured.Stmt.call name] } targetAfterArgs
        (Structured.EffectSemantics.Outcome.regular callFinal) :=
    Structured.EffectSemantics.Block.Eval.cons_regular hCall
      Structured.EffectSemantics.Block.Eval.nil
  have hStoresBlock :
      Structured.ObserverSemantics.Block.Eval targetProgram 2
        { stmts := [Structured.Stmt.code stores] } callFinal
        (Structured.EffectSemantics.Outcome.regular targetAssigned) :=
    Structured.EffectSemantics.Block.Eval.cons_regular
      (Structured.EffectSemantics.Stmt.Eval.code hStores)
      Structured.EffectSemantics.Block.Eval.nil
  obtain ⟨prefixFuel, hPrefix⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hArgsBlock hCallBlock
  obtain ⟨assignedFuel, hAssigned⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hPrefix hStoresBlock
  obtain ⟨fuel, hEval⟩ :=
    Structured.EffectSemantics.Block.Eval.append_regular_exists
      hAssigned hRelease
  exact ⟨fuel, by simpa [List.append_assoc] using hEval⟩

/--
Compose one selected source call after source semantics has exposed its
argument, callee-entry, return, and caller-writeback data.

The callee callback is for this one selected activation only. The forthcoming
source-fuel theorem constructs it recursively; it is not retained by any
public adjacent-pass theorem.
-/
theorem regular_of_selected
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    (compilation : Compilation allocation program expressions)
    {name : Functions.Name}
    {fn : Functions.FunDef}
    {artifact :
      AllocationObserverCall.SelectedCallee.Artifact
        allocation program expressions name fn}
    (prepared : AllocationObserverCall.SelectedCallee.Prepared artifact)
    {config : Frame.Config}
    {allocatorDepth sourceFuel : Nat}
    {transcript : Trace}
    {sourceCtx : Functions.Source.Ctx}
    {callerCtx : AllocationLowering.Ctx}
    {returns : List Functions.Name}
    {callerState callerFinalState : AllocationLowering.State}
    {callerLocals callerFinalLocals : Locals.Ctx}
    {callerPlan : Locals.Allocation.Plan}
    {callerLive : List Locals.Name}
    {callerFrameBase : Nat}
    {callerMode : ActivationMode}
    {source sourceAfterArgs sourceBodyStart sourceReturned sourceFinal :
      Functions.ObserverSemantics.State transcript}
    {target : Structured.ObserverSemantics.State transcript}
    {targets : List Functions.Name}
    {args : List (Functions.Expr 1)}
    {argValues returnValues : List Word}
    {bodyStore returnStore : Locals.Source.Store}
    {loweredStmts : List Locals.Stmt}
    {compiledStmts : List Expressions.Stmt}
    {bodyMode : AllocationObserverCall.StructuredCall.ReturnMode}
    (hConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract compilation.recipe.frameWords =
        some config)
    (hCallerShared : compilation.CtxShared callerCtx)
    (hSource :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (AllocationObserverSafety.SafeSemantics.primitiveSemantics
            program.memoryContract transcript)
          program sourceCtx sourceFuel (.call targets name args) source =
        .ok
          (Functions.Source.Effectful.Outcome.regular sourceFinal,
            sourceCtx))
    (hSafeArgs :
      AllocationObserverSafety.ArgList.MemorySafeEval
        program.memoryContract transcript args source sourceAfterArgs
        argValues)
    (hParamLookup :
      Functions.Source.Store.lookupMany
          (artifact.slots.params.map Prod.fst)
          bodyStore =
        some argValues)
    (hBodyStart :
      sourceBodyStart =
        (Functions.ObserverSemantics.stateModel transcript).withSource
          sourceAfterArgs
          { shared := sourceAfterArgs.source.shared
            vars := bodyStore })
    (hAssign :
      Functions.Source.Store.assignMany targets returnValues
          sourceAfterArgs.source.vars =
        some returnStore)
    (hFinal :
      sourceFinal =
        (Functions.ObserverSemantics.stateModel transcript).withSource
          sourceReturned
          { shared := sourceReturned.source.shared
            vars := returnStore })
    (hScoped :
      Functions.Scope.Stmt.Scoped callerLive
        (.call targets name args))
    (hInvariant :
      AllocationObserverContext.ActivationRuntimeInvariant
        program.memoryContract config allocatorDepth callerCtx callerState
        callerLocals callerPlan callerLive callerFrameBase callerMode
        source target)
    (hBudget : Frame.Budget config allocatorDepth)
    (hLower :
      AllocationLowering.lowerStmt callerCtx returns callerState
          (.call targets name args) =
        some (loweredStmts, callerFinalState))
    (hCompile :
      Locals.Block.compileOpen callerLocals { stmts := loweredStmts } =
        some (compiledStmts, callerFinalLocals))
    (hCallee :
      ∀ {targetEntry : Structured.ObserverSemantics.State transcript}
        {calleeDepth calleeFrameBase : Nat},
        ActivationCalleeEntryRel
            program.memoryContract prepared.plan []
            artifact.slots.params calleeFrameBase prepared.mode
            sourceBodyStart targetEntry →
        targetEntry.source.evm.stack.length =
            artifact.entryCtx.layout.length →
        Frame.AllocatorReady config calleeDepth targetEntry →
        Frame.ActivationOwned config calleeDepth calleeFrameBase
            prepared.mode →
        AllocationObserverCall.RegularCallee.protectedBound
            calleeDepth prepared.mode =
          allocatorDepth + 1 →
        ∃ calleeFinal bodyFuel,
          Structured.ObserverSemantics.Block.Eval
            expressions.toStructured bodyFuel
            artifact.lowerProc.toStructured.body targetEntry
            (bodyMode.outcome calleeFinal) ∧
          calleeFinal.source.evm.stack = returnValues.reverse ∧
          sourceReturned.cursor = calleeFinal.cursor ∧
          Compiler.MemoryRelation.MachineRel program.memoryContract
            sourceReturned.source.shared.toMachineState
            calleeFinal.source.evm.toMachineState ∧
          sourceReturned.source.shared.toState =
            calleeFinal.source.evm.toSharedState.toState ∧
          Frame.BoundedEffect config calleeDepth (allocatorDepth + 1)
            targetEntry calleeFinal) :
    ∃ targetFinal,
      AllocationObserverStatement.Sequence.RegularStmtRuntimeInvariantForward
        program.memoryContract config allocatorDepth transcript
        callerCtx callerFinalState callerFinalLocals callerPlan callerLive
        callerFrameBase callerMode callerMode program sourceCtx
        (.call targets name args) source expressions.toStructured target
        (Expressions.StmtList.toStructured compiledStmts)
        sourceFinal targetFinal sourceCtx := by
  obtain
      ⟨slotInfo, loweredArgs, callArgs, stores, release,
        argsCode, releaseCode, hSlotLookup, hArgsLength,
        hTargetsLength, hTargetsNodup, hLowerArgs, hCallArgs,
        hStores, hRelease, hArgsCode, hReleaseCode,
        hCompiledShape, hCallerState, hCallerLocals⟩ :=
    AllocationObserverCall.CallCompiler.components hLower hCompile
  subst callerFinalState
  subst callerFinalLocals
  obtain ⟨hRecipeEq, _hSlotsEq, _hFrameNameEq⟩ :=
    compilation.selected_agrees artifact
  have hArtifactSlotLookup :
      AllocationSupport.lookupFun? name callerCtx.functions =
        some artifact.slots := by
    rw [hCallerShared.functions, ← hRecipeEq]
    simpa [artifact.sourceName] using artifact.slotsLookup
  have hSlotInfo : slotInfo = artifact.slots := by
    rw [hArtifactSlotLookup] at hSlotLookup
    exact (Option.some.inj hSlotLookup).symm
  subst slotInfo
  have hArtifactConfig :
      AllocationSupport.scratchFrameConfig?
          program.memoryContract artifact.recipe.frameWords =
        some config := by
    obtain ⟨hRecipe, _hSlots, _hFrameName⟩ :=
      compilation.selected_agrees artifact
    simpa [hRecipe] using hConfig
  have hSourceOrdinary :=
    AllocationObserverSafety.SafeSemantics.stmt_run_eq hSource
  have hArgsScoped :
      ∀ arg, arg ∈ args →
        Functions.Scope.ExprScoped callerLive arg :=
    hScoped.2.2
  have hTargetsLive :
      ∀ targetName, targetName ∈ targets →
        targetName ∈ callerLive :=
    hScoped.2.1
  have hReturnLength :
      returnValues.length = artifact.lowerProc.retc := by
    rw [prepared.procRetc]
    calc
      returnValues.length = targets.length :=
        Functions.Source.Store.assignMany_length hAssign
      _ = artifact.slots.returns.length := hTargetsLength
      _ = (artifact.slots.returns.map Prod.fst).length := by simp
      _ = fn.returns.length :=
        congrArg List.length artifact.slotsMatch.2.2
  have hParamLength :
      artifact.slots.params.length = fn.params.length := by
    simpa using congrArg List.length artifact.slotsMatch.2.1
  have hCallerStackLength :
      target.source.evm.stack.length = callerLocals.layout.length :=
    hInvariant.activation.stackLength
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hFrame :
        name ∈ callerCtx.frameFunctions :=
      (compilation.call_needsFrame_iff hCallerShared artifact).2 hNeedsFrame
    have hCallerFrameConfig :
        callerCtx.frameConfig? = some config := by
      rw [hCallerShared.frameConfig]
      simpa [Compilation.frameConfig?] using hConfig
    have hCallArgsShape :
        callArgs =
          AllocationLowering.frameExpr config :: loweredArgs := by
      simpa [hFrame, hCallerFrameConfig] using hCallArgs.symm
    subst callArgs
    obtain ⟨ordinaryArgsCode, hOrdinaryArgsCode, hArgsCodeShape⟩ :=
      AllocationLowering.frameExpr_cons_compileCode_components hArgsCode
    have hPositive :
        0 < config.frameWords :=
      compilation.selected_config_frameWords_pos artifact hConfig hNeedsFrame
    obtain
        ⟨targetAfterAcquire, targetAfterArgs, callerBase,
          hAcquireRun, hOrdinaryArgsRun, hArgsResult, hCallerRel,
          hCallStack, hCallerBaseStack, hCallerBaseMachine,
          hAcquireStack,
          hFrameActive, hFrameAllocated, hGrowth, hArgsEffect⟩ :=
      AllocationObserverCall.PreparedArguments.scratch
        hConfig hPositive hBudget hSafeArgs hArgsScoped hLowerArgs
        hOrdinaryArgsCode hInvariant
    have hArgsRun :
        Structured.ObserverSemantics.Code.run argsCode target =
          .ok targetAfterArgs := by
      rw [hArgsCodeShape,
        Structured.ObserverSemantics.Code.run_append]
      rw [hAcquireRun]
      exact hOrdinaryArgsRun
    let callVector :=
      argValues.reverse ++
        [EvmYul.UInt256.ofNat
          (Frame.baseAt config allocatorDepth)]
    let targetEntry :=
      AllocationObserverCall.CalleeEntry.structuredState
        targetAfterArgs callVector target.source.evm.stack
        artifact.lowerProc.retc
    have hEntry :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params
          (Frame.baseAt config allocatorDepth)
          (.scratch 0 config.frameWords)
          sourceBodyStart targetEntry := by
      rw [hBodyStart]
      have hArgsResult' :
          ActivationExprResultRel program.memoryContract callerPlan
            callerLive 1 callerFrameBase argValues.length callerMode
            sourceAfterArgs targetAfterAcquire targetAfterArgs argValues := by
        simpa [hSafeArgs.values_length] using hArgsResult
      apply AllocationObserverCall.CalleeEntry.scratch_of_arguments
        hConfig hBudget hArgsResult' hAcquireStack
          hFrameActive hFrameAllocated hGrowth hParamLookup
    have hPreparedMode :
        prepared.mode = .scratch 0 config.frameWords := by
      rw [prepared.mode_eq_scratch_of_needsFrame hNeedsFrame]
      obtain
          ⟨_reservation, _hReservation, _hAllocator, _hFirst, _hLimit,
            hWords, _hWF, _hHost, _hReservationPositive, _hFits⟩ :=
        AllocationSupport.scratchFrameConfig?_sound hArtifactConfig
      rw [hWords]
    have hEntry' :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params
          (Frame.baseAt config allocatorDepth) prepared.mode
          sourceBodyStart targetEntry := by
      simpa [hPreparedMode] using hEntry
    have hEntryStackLength :
        targetEntry.source.evm.stack.length =
          artifact.entryCtx.layout.length := by
      change callVector.length = artifact.entryLayout.length
      simp [callVector,
        AllocationObserverCall.SelectedCallee.Artifact.entryLayout,
        hNeedsFrame, hArgsResult.valuesLength, hArgsLength,
        hParamLength]
    have hEntryReady :
        Frame.AllocatorReady config (allocatorDepth + 1) targetEntry := by
      apply hArgsEffect.ready.of_machine_eq
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryOwned :
        Frame.ActivationOwned config (allocatorDepth + 1)
          (Frame.baseAt config allocatorDepth) prepared.mode := by
      rw [hPreparedMode]
      exact .scratch rfl rfl
    have hProtectedBound :
        AllocationObserverCall.RegularCallee.protectedBound
            (allocatorDepth + 1) prepared.mode =
          allocatorDepth + 1 := by
      simp [hPreparedMode,
        AllocationObserverCall.RegularCallee.protectedBound]
    obtain
        ⟨calleeFinal, bodyFuel, hCalleeEval, hReturnedStack,
          hCursor, hMachine, hWorld, hCalleeEffect⟩ :=
      hCallee hEntry' hEntryStackLength hEntryReady hEntryOwned
        hProtectedBound
    have hCallerReady :
        Frame.AllocatorReady config (allocatorDepth + 1) callerBase := by
      apply hArgsEffect.ready.of_machine_eq
      exact hCallerBaseMachine
    have hEntryMachine :
        targetEntry.source.evm.toMachineState =
          callerBase.source.evm.toMachineState := by
      calc
        targetEntry.source.evm.toMachineState =
            targetAfterArgs.source.evm.toMachineState := by
          simp [targetEntry,
            AllocationObserverCall.CalleeEntry.structuredState,
            Structured.ObserverSemantics.stateModel,
            Structured.EffectSemantics.StateModel.withEVM,
            Structured.RunState.withEVM, Structured.RunState.pushReturn]
        _ = callerBase.source.evm.toMachineState :=
          hCallerBaseMachine.symm
    have hEntryEffect :
        Frame.BoundedEffect config (allocatorDepth + 1)
          (allocatorDepth + 1) callerBase targetEntry :=
      Frame.BoundedEffect.of_machine_eq hCallerReady hEntryMachine
    have hCallEffect :
        Frame.BoundedEffect config (allocatorDepth + 1)
          (allocatorDepth + 1) callerBase calleeFinal :=
      hEntryEffect.trans hCalleeEffect
    obtain
        ⟨callFinal, targetAssigned, hCallEval, hStoresRun,
          hAssignedRel, hAssignedStackLength, hAssignedEffect⟩ :=
      AllocationObserverCall.RegularCall.resume_and_writeback
        hConfig hCallerRel hInvariant.frame (by omega) hBudget
        hCallerBaseStack artifact.targetLookup
        (by simpa [callVector] using hCallStack)
        (by
          change callVector.length = artifact.lowerProc.argc
          rw [prepared.procArgc]
          simp [callVector, hNeedsFrame, hArgsResult.valuesLength,
            hArgsLength, hParamLength])
        hCalleeEval hReturnedStack hReturnLength hCursor hMachine hWorld
        hCallEffect hInvariant.activation.compiler
        hInvariant.activation.planWF hTargetsLive hTargetsNodup
        hAssign hStores
    have hAssignedDefined :
        LiveDefined callerLive
          ((Functions.ObserverSemantics.stateModel transcript).withSource
            sourceReturned
            { shared := sourceReturned.source.shared
              vars := returnStore }).source := by
      have hAfterArgsDefined :
          LiveDefined callerLive sourceAfterArgs.source :=
        hInvariant.activation.defined.congr_vars hSafeArgs.vars_eq
      simpa [Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.withSource,
        Locals.Source.State.withVars] using
        hAfterArgsDefined.assignMany_preserves hAssign
    have hAssignedInvariant :
        AllocationObserverContext.ActivationInvariant
          program.memoryContract callerCtx callerState callerLocals
          callerPlan callerLive callerFrameBase callerMode sourceFinal
          targetAssigned := by
      refine
        { compiler := hInvariant.activation.compiler
          planWF := hInvariant.activation.planWF
          defined := ?_
          state := ?_
          stackLength := ?_ }
      · simpa [hFinal] using hAssignedDefined
      · simpa [hFinal] using hAssignedRel
      · exact hAssignedStackLength.trans hCallerStackLength
    have hWholeAssignedEffect :
        Frame.BoundedEffect config (allocatorDepth + 1)
          (AllocationObserverCall.CallTargets.protectedBound
            allocatorDepth callerMode)
          target targetAssigned := by
      have hArgsToBase :
          Frame.BoundedEffect config (allocatorDepth + 1)
            (allocatorDepth + 1) target callerBase := by
        exact
          hArgsEffect.trans
            (Frame.BoundedEffect.of_machine_eq hArgsEffect.ready
              hCallerBaseMachine)
      have hBound :
          AllocationObserverCall.CallTargets.protectedBound
              allocatorDepth callerMode ≤
            allocatorDepth + 1 := by
        cases callerMode <;>
          simp [AllocationObserverCall.CallTargets.protectedBound]
      exact
        (Frame.BoundedEffect.weaken hBound hArgsToBase).trans
          hAssignedEffect
    have hReleaseShape :
        release =
          [.expr
            (Locals.Expr.code (results := 0)
              (AllocationSupport.scratchFrameReleaseCode config))] := by
      simpa [hFrame, hCallerFrameConfig] using hRelease.symm
    subst release
    have hReleaseCodeShape :
        releaseCode =
          Locals.codeStmt
            (AllocationSupport.scratchFrameReleaseCode config) := by
      have hSingle :=
        Locals.Block.compileOpen_single_components hReleaseCode
      simpa [Locals.Stmt.compile, Locals.Expr.compileCode] using hSingle.symm
    obtain
        ⟨targetFinal, hReleaseRun, hFinalInvariant, hFinalEffect⟩ :=
      AllocationObserverCall.RegularCall.complete_with_release
        hConfig hBudget hAssignedInvariant hInvariant.frame
        hWholeAssignedEffect
    have hReleaseEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured 2
          { stmts :=
              Expressions.StmtList.toStructured releaseCode }
          targetAssigned
          (Structured.EffectSemantics.Outcome.regular targetFinal) := by
      rw [hReleaseCodeShape]
      exact
        Structured.EffectSemantics.Block.Eval.cons_regular
          (Structured.EffectSemantics.Stmt.Eval.code hReleaseRun)
          Structured.EffectSemantics.Block.Eval.nil
    obtain ⟨targetFuel, hTargetEvalRaw⟩ :=
      eval_phases hArgsRun hCallEval hStoresRun
        (by
          simpa [hReleaseCodeShape,
            Expressions.StmtList.toStructured,
            Expressions.Stmt.toStructured] using hReleaseEval)
    have hTargetEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured
          targetFuel
          { stmts :=
              Expressions.StmtList.toStructured compiledStmts }
          target
          (Structured.EffectSemantics.Outcome.regular targetFinal) := by
      rw [hCompiledShape,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append]
      simpa [Locals.codeStmt,
        Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured,
        hReleaseCodeShape] using hTargetEvalRaw
    exact
      ⟨targetFinal, sourceFuel, targetFuel, hSourceOrdinary, hTargetEval,
        hFinalInvariant, SameFrame.refl callerMode, hFinalEffect⟩
  · have hNoFrame : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hFrame :
        name ∉ callerCtx.frameFunctions := by
      intro hMem
      exact hNeedsFrame
        ((compilation.call_needsFrame_iff hCallerShared artifact).1 hMem)
    have hCallArgsShape : callArgs = loweredArgs := by
      simpa [hFrame] using hCallArgs.symm
    subst callArgs
    obtain
        ⟨targetAfterArgs, callerBase, hArgsRun, hArgsResult,
          hCallerRel, hCallStack, hCallerBaseStack,
          hCallerBaseMachine, hArgsEffect⟩ :=
      AllocationObserverCall.PreparedArguments.stack
        hConfig hSafeArgs hArgsScoped hLowerArgs hArgsCode hInvariant
    let targetEntry :=
      AllocationObserverCall.CalleeEntry.structuredState
        targetAfterArgs argValues.reverse target.source.evm.stack
        artifact.lowerProc.retc
    have hEntry :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params 0 .stack sourceBodyStart targetEntry := by
      rw [hBodyStart]
      have hArgsResult' :
          ActivationExprResultRel program.memoryContract callerPlan
            callerLive 0 callerFrameBase argValues.length callerMode
            sourceAfterArgs target targetAfterArgs argValues := by
        simpa [hSafeArgs.values_length] using hArgsResult
      exact
        AllocationObserverCall.CalleeEntry.stack_of_arguments
          hArgsResult' hParamLookup
    have hPreparedMode : prepared.mode = .stack :=
      prepared.mode_eq_stack_of_noFrame hNoFrame
    have hEntry' :
        ActivationCalleeEntryRel program.memoryContract prepared.plan []
          artifact.slots.params 0 prepared.mode sourceBodyStart
          targetEntry := by
      simpa [hPreparedMode] using hEntry
    have hEntryStackLength :
        targetEntry.source.evm.stack.length =
          artifact.entryCtx.layout.length := by
      change argValues.reverse.length = artifact.entryLayout.length
      simp [
        AllocationObserverCall.SelectedCallee.Artifact.entryLayout,
        hNoFrame, hArgsResult.valuesLength, hArgsLength,
        hParamLength]
    have hEntryReady :
        Frame.AllocatorReady config allocatorDepth targetEntry := by
      apply hArgsEffect.ready.of_machine_eq
      simp [targetEntry,
        AllocationObserverCall.CalleeEntry.structuredState,
        Structured.ObserverSemantics.stateModel,
        Structured.EffectSemantics.StateModel.withEVM,
        Structured.RunState.withEVM, Structured.RunState.pushReturn]
    have hEntryOwned :
        Frame.ActivationOwned config allocatorDepth 0 prepared.mode := by
      rw [hPreparedMode]
      exact .stack
    have hProtectedBound :
        AllocationObserverCall.RegularCallee.protectedBound
            allocatorDepth prepared.mode =
          allocatorDepth + 1 := by
      simp [hPreparedMode,
        AllocationObserverCall.RegularCallee.protectedBound]
    obtain
        ⟨calleeFinal, bodyFuel, hCalleeEval, hReturnedStack,
          hCursor, hMachine, hWorld, hCalleeEffect⟩ :=
      hCallee hEntry' hEntryStackLength hEntryReady hEntryOwned
        hProtectedBound
    have hCallerReady :
        Frame.AllocatorReady config allocatorDepth callerBase := by
      apply hArgsEffect.ready.of_machine_eq
      exact hCallerBaseMachine
    have hEntryMachine :
        targetEntry.source.evm.toMachineState =
          callerBase.source.evm.toMachineState := by
      calc
        targetEntry.source.evm.toMachineState =
            targetAfterArgs.source.evm.toMachineState := by
          simp [targetEntry,
            AllocationObserverCall.CalleeEntry.structuredState,
            Structured.ObserverSemantics.stateModel,
            Structured.EffectSemantics.StateModel.withEVM,
            Structured.RunState.withEVM, Structured.RunState.pushReturn]
        _ = callerBase.source.evm.toMachineState :=
          hCallerBaseMachine.symm
    have hEntryEffect :
        Frame.BoundedEffect config allocatorDepth (allocatorDepth + 1)
          callerBase targetEntry :=
      Frame.BoundedEffect.of_machine_eq hCallerReady hEntryMachine
    have hCallEffect :
        Frame.BoundedEffect config allocatorDepth (allocatorDepth + 1)
          callerBase calleeFinal :=
      hEntryEffect.trans hCalleeEffect
    obtain
        ⟨callFinal, targetAssigned, hCallEval, hStoresRun,
          hAssignedRel, hAssignedStackLength, hAssignedEffect⟩ :=
      AllocationObserverCall.RegularCall.resume_and_writeback
        hConfig hCallerRel hInvariant.frame (by omega) hBudget
        hCallerBaseStack artifact.targetLookup
        (by simpa using hCallStack)
        (by
          change argValues.reverse.length = artifact.lowerProc.argc
          rw [prepared.procArgc]
          simp [hNoFrame, hArgsResult.valuesLength,
            hArgsLength, hParamLength])
        hCalleeEval hReturnedStack hReturnLength hCursor hMachine hWorld
        hCallEffect hInvariant.activation.compiler
        hInvariant.activation.planWF hTargetsLive hTargetsNodup
        hAssign hStores
    have hAssignedDefined :
        LiveDefined callerLive
          ((Functions.ObserverSemantics.stateModel transcript).withSource
            sourceReturned
            { shared := sourceReturned.source.shared
              vars := returnStore }).source := by
      have hAfterArgsDefined :
          LiveDefined callerLive sourceAfterArgs.source :=
        hInvariant.activation.defined.congr_vars hSafeArgs.vars_eq
      simpa [Functions.ObserverSemantics.stateModel,
        Locals.ObserverSemantics.stateModel,
        Locals.Source.Effectful.StateModel.withSource,
        Locals.Source.State.withVars] using
        hAfterArgsDefined.assignMany_preserves hAssign
    have hAssignedInvariant :
        AllocationObserverContext.ActivationInvariant
          program.memoryContract callerCtx callerState callerLocals
          callerPlan callerLive callerFrameBase callerMode sourceFinal
          targetAssigned := by
      refine
        { compiler := hInvariant.activation.compiler
          planWF := hInvariant.activation.planWF
          defined := ?_
          state := ?_
          stackLength := ?_ }
      · simpa [hFinal] using hAssignedDefined
      · simpa [hFinal] using hAssignedRel
      · exact hAssignedStackLength.trans hCallerStackLength
    have hArgsToBase :
        Frame.BoundedEffect config allocatorDepth (allocatorDepth + 1)
          target callerBase :=
      hArgsEffect.trans
        (Frame.BoundedEffect.of_machine_eq hArgsEffect.ready
          hCallerBaseMachine)
    have hBound :
        AllocationObserverCall.CallTargets.protectedBound
            allocatorDepth callerMode ≤
          allocatorDepth + 1 := by
      cases callerMode <;>
        simp [AllocationObserverCall.CallTargets.protectedBound]
    have hWholeAssignedEffect :
        Frame.BoundedEffect config allocatorDepth
          (AllocationObserverCall.CallTargets.protectedBound
            allocatorDepth callerMode)
          target targetAssigned :=
      (Frame.BoundedEffect.weaken hBound hArgsToBase).trans
        hAssignedEffect
    obtain ⟨hFinalInvariant, hFinalEffect⟩ :=
      AllocationObserverCall.RegularCall.complete_without_release
        hAssignedInvariant hInvariant.frame hWholeAssignedEffect
    have hReleaseShape : release = [] := by
      simpa [hFrame] using hRelease.symm
    subst release
    have hReleaseCodeShape : releaseCode = [] := by
      simpa [Locals.Block.compileOpen] using
        hReleaseCode
    have hReleaseEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured 1
          { stmts := Expressions.StmtList.toStructured releaseCode }
          targetAssigned
          (Structured.EffectSemantics.Outcome.regular targetAssigned) := by
      rw [hReleaseCodeShape]
      exact Structured.EffectSemantics.Block.Eval.nil
    obtain ⟨targetFuel, hTargetEvalRaw⟩ :=
      eval_phases hArgsRun hCallEval hStoresRun
        (by simpa [hReleaseCodeShape] using hReleaseEval)
    have hTargetEval :
        Structured.ObserverSemantics.Block.Eval expressions.toStructured
          targetFuel
          { stmts :=
              Expressions.StmtList.toStructured compiledStmts }
          target
          (Structured.EffectSemantics.Outcome.regular targetAssigned) := by
      rw [hCompiledShape,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append,
        Expressions.StmtList.toStructured_append]
      simpa [Locals.codeStmt,
        Expressions.StmtList.toStructured,
        Expressions.Stmt.toStructured,
        hReleaseCodeShape] using hTargetEvalRaw
    exact
      ⟨targetAssigned, sourceFuel, targetFuel, hSourceOrdinary,
        hTargetEval, hFinalInvariant, SameFrame.refl callerMode,
        hFinalEffect⟩

end Call

end AllocationObserverForward
end Functions
end EvmCompiler
