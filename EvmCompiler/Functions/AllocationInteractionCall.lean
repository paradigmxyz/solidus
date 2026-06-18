import EvmCompiler.Functions.AllocationInteractionCursor

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionCall

open AllocationInteractionCursor

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

end SelectedCallee

end AllocationInteractionCall
end Functions
end EvmCompiler
