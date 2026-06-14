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

end AllocationObserverForward
end Functions
end EvmCompiler
