import EvmCompiler.Core.MemoryContract
import EvmCompiler.Locals.Syntax

namespace EvmCompiler
namespace Locals
namespace Allocation

inductive RegionBase where
  | absolute (byteOffset : Nat)
  | freeMemoryPointer
  deriving DecidableEq, Repr

structure ScratchRegion where
  base : RegionBase
  words : Nat
  deriving DecidableEq, Repr

inductive LocalLocation where
  | stack (depth : Nat)
  | scratch (slot : Nat)
  deriving DecidableEq, Repr

abbrev Binding := Name × LocalLocation

structure LiveInterval where
  name : Name
  firstUse : Nat
  lastUse : Nat
  deriving DecidableEq, Repr

structure CallBoundary where
  site : Nat
  liveAcross : List Name
  deriving DecidableEq, Repr

structure ReturnLayout where
  functionName : Name
  locations : List LocalLocation
  deriving DecidableEq, Repr

structure Plan where
  sourceScope : List Name
  stackOrder : List Name
  bindings : List Binding
  scratchRegion? : Option ScratchRegion
  liveIntervals : List LiveInterval := []
  callBoundaries : List CallBoundary := []
  returnLayouts : List ReturnLayout := []
  deriving DecidableEq, Repr

def ScratchRegion.AuthorizedBy
    (region : ScratchRegion)
    (contract : MemoryContract.Contract) : Prop :=
  match region.base with
  | .absolute byteOffset =>
      MemoryContract.authorizesRegion contract byteOffset region.words
  | .freeMemoryPointer =>
      False

instance scratchRegionAuthorizedByDecidable
    (region : ScratchRegion)
    (contract : MemoryContract.Contract) :
    Decidable (region.AuthorizedBy contract) := by
  rcases region with ⟨base, words⟩
  cases base with
  | absolute byteOffset =>
      simp only [ScratchRegion.AuthorizedBy]
      infer_instance
  | freeMemoryPointer =>
      simp only [ScratchRegion.AuthorizedBy]
      infer_instance

namespace Plan

def MemoryAuthorized (plan : Plan)
    (contract : MemoryContract.Contract) : Prop :=
  match plan.scratchRegion? with
  | none => True
  | some region => region.AuthorizedBy contract

instance memoryAuthorizedDecidable (plan : Plan)
    (contract : MemoryContract.Contract) :
    Decidable (plan.MemoryAuthorized contract) := by
  unfold MemoryAuthorized
  cases plan.scratchRegion? <;> infer_instance

def scratchSlots (plan : Plan) : List Nat :=
  plan.bindings.filterMap fun binding =>
    match binding.2 with
    | .stack _ => none
    | .scratch slot => some slot

def location? (plan : Plan) (name : Name) : Option LocalLocation :=
  (plan.bindings.find? fun binding =>
    decide (binding.1 = name)).map Prod.snd

theorem binding_mem_of_location?_eq_some
    {plan : Plan} {name : Name} {location : LocalLocation}
    (hLocation : plan.location? name = some location) :
    (name, location) ∈ plan.bindings := by
  unfold location? at hLocation
  cases hFind :
      plan.bindings.find? fun binding =>
        decide (binding.1 = name) with
  | none =>
      simp [hFind] at hLocation
  | some binding =>
      have hMem := List.mem_of_find?_eq_some hFind
      have hName := List.find?_some hFind
      rcases binding with ⟨candidate, candidateLocation⟩
      rw [hFind] at hLocation
      cases hLocation
      simp only [decide_eq_true_eq] at hName
      subst candidate
      exact hMem

def BindingValid (plan : Plan) (binding : Binding) : Prop :=
  match binding.2 with
  | .stack depth => plan.stackOrder[depth]? = some binding.1
  | .scratch slot =>
      match plan.scratchRegion? with
      | none => False
      | some region => slot < region.words

def LocationValid (plan : Plan) : LocalLocation → Prop
  | .stack depth => depth < plan.stackOrder.length
  | .scratch slot =>
      match plan.scratchRegion? with
      | none => False
      | some region => slot < region.words

instance bindingValidDecidable (plan : Plan) (binding : Binding) :
    Decidable (plan.BindingValid binding) := by
  rcases binding with ⟨name, location⟩
  cases location with
  | stack depth =>
      simp [BindingValid]
      infer_instance
  | scratch slot =>
      cases hRegion : plan.scratchRegion? with
      | none =>
          exact isFalse (by simp [BindingValid, hRegion])
      | some region =>
          simp [BindingValid, hRegion]
          infer_instance

instance locationValidDecidable (plan : Plan) (location : LocalLocation) :
    Decidable (plan.LocationValid location) := by
  cases location with
  | stack depth =>
      simp [LocationValid]
      infer_instance
  | scratch slot =>
      cases hRegion : plan.scratchRegion? with
      | none =>
          exact isFalse (by simp [LocationValid, hRegion])
      | some region =>
          simp [LocationValid, hRegion]
          infer_instance

def LiveIntervalValid (plan : Plan) (interval : LiveInterval) : Prop :=
  interval.name ∈ plan.sourceScope ∧ interval.firstUse ≤ interval.lastUse

def CallBoundaryValid (plan : Plan) (boundary : CallBoundary) : Prop :=
  boundary.liveAcross.Nodup ∧
    ∀ name, name ∈ boundary.liveAcross → name ∈ plan.sourceScope

def ReturnLayoutValid (plan : Plan) (layout : ReturnLayout) : Prop :=
  layout.locations.Forall plan.LocationValid

def StackOrderValid (plan : Plan) : Prop :=
  plan.stackOrder.Nodup ∧
    ∀ name, name ∈ plan.stackOrder → name ∈ plan.sourceScope

def AnalysisKeysUnique (plan : Plan) : Prop :=
  (plan.liveIntervals.map LiveInterval.name).Nodup ∧
    (plan.callBoundaries.map CallBoundary.site).Nodup ∧
    (plan.returnLayouts.map ReturnLayout.functionName).Nodup

instance liveIntervalValidDecidable (plan : Plan)
    (interval : LiveInterval) : Decidable (LiveIntervalValid plan interval) := by
  unfold LiveIntervalValid
  infer_instance

instance callBoundaryValidDecidable (plan : Plan)
    (boundary : CallBoundary) : Decidable (CallBoundaryValid plan boundary) := by
  unfold CallBoundaryValid
  infer_instance

instance returnLayoutValidDecidable (plan : Plan)
    (layout : ReturnLayout) : Decidable (ReturnLayoutValid plan layout) := by
  unfold ReturnLayoutValid
  infer_instance

instance stackOrderValidDecidable (plan : Plan) :
    Decidable (StackOrderValid plan) := by
  unfold StackOrderValid
  infer_instance

instance analysisKeysUniqueDecidable (plan : Plan) :
    Decidable (AnalysisKeysUnique plan) := by
  unfold AnalysisKeysUnique
  infer_instance

def WellFormed (plan : Plan) : Prop :=
  plan.bindings.map Prod.fst = plan.sourceScope ∧
    plan.sourceScope.Nodup ∧
    plan.stackOrder.length ≤ 16 ∧
    StackOrderValid plan ∧
    plan.bindings.Forall plan.BindingValid ∧
    plan.scratchSlots.Nodup ∧
    AnalysisKeysUnique plan ∧
    plan.liveIntervals.Forall (LiveIntervalValid plan) ∧
    plan.callBoundaries.Forall (CallBoundaryValid plan) ∧
    plan.returnLayouts.Forall (ReturnLayoutValid plan)

theorem bindingValid_of_wellFormed_of_location?_eq_some
    {plan : Plan} {name : Name} {location : LocalLocation}
    (hWF : plan.WellFormed)
    (hLocation : plan.location? name = some location) :
    plan.BindingValid (name, location) := by
  rcases hWF with
    ⟨_hBindings, _hScope, _hStackLength, _hStackOrder,
      hValid, _hScratch, _hKeys, _hIntervals, _hCalls, _hReturns⟩
  exact
    (List.forall_iff_forall_mem.mp hValid)
      (name, location)
      (binding_mem_of_location?_eq_some hLocation)

theorem scratch_bound_of_wellFormed
    {plan : Plan} {name : Name} {slot words : Nat}
    {base : RegionBase}
    (hWF : plan.WellFormed)
    (hLocation : plan.location? name = some (.scratch slot))
    (hRegion :
      plan.scratchRegion? = some { base := base, words := words }) :
    slot < words := by
  have hValid :=
    bindingValid_of_wellFormed_of_location?_eq_some hWF hLocation
  simpa [BindingValid, hRegion] using hValid

instance wellFormedDecidable (plan : Plan) :
    Decidable plan.WellFormed := by
  unfold WellFormed
  infer_instance

def wellFormed? (plan : Plan) : Bool :=
  decide plan.WellFormed

theorem wellFormed_of_check {plan : Plan}
    (hCheck : plan.wellFormed? = true) :
    plan.WellFormed := by
  simpa [wellFormed?] using hCheck

theorem check_of_wellFormed {plan : Plan}
    (hWF : plan.WellFormed) :
    plan.wellFormed? = true := by
  simpa [wellFormed?] using hWF

end Plan

inductive ScopeId where
  | main
  | function (name : Name)
  | lexical (parent : ScopeId) (ordinal : Nat)
  deriving DecidableEq, Repr

namespace ScopeId

def child (parent : ScopeId) (ordinal : Nat) : ScopeId :=
  .lexical parent ordinal

end ScopeId

structure ScopePlan where
  scope : ScopeId
  allocation : Plan
  deriving DecidableEq, Repr

structure ProgramPlan where
  scopes : List ScopePlan
  deriving DecidableEq, Repr

namespace ProgramPlan

def MemoryAuthorized (plan : ProgramPlan)
    (contract : MemoryContract.Contract) : Prop :=
  plan.scopes.Forall fun scope =>
    scope.allocation.MemoryAuthorized contract

instance memoryAuthorizedDecidable (plan : ProgramPlan)
    (contract : MemoryContract.Contract) :
    Decidable (plan.MemoryAuthorized contract) := by
  unfold MemoryAuthorized
  infer_instance

def singleton (scope : ScopeId) (allocation : Plan) : ProgramPlan :=
  { scopes := [{ scope := scope, allocation := allocation }] }

def main (allocation : Plan) : ProgramPlan :=
  singleton .main allocation

def scopeIds (plan : ProgramPlan) : List ScopeId :=
  plan.scopes.map ScopePlan.scope

def find? (plan : ProgramPlan) (scope : ScopeId) : Option Plan :=
  (plan.scopes.find? fun candidate => decide (candidate.scope = scope)).map
    ScopePlan.allocation

def WellFormed (plan : ProgramPlan) : Prop :=
  plan.scopeIds.Nodup ∧
    plan.scopes.Forall (fun scopePlan => scopePlan.allocation.WellFormed)

instance wellFormedDecidable (plan : ProgramPlan) :
    Decidable plan.WellFormed := by
  unfold WellFormed
  infer_instance

def wellFormed? (plan : ProgramPlan) : Bool :=
  decide plan.WellFormed

theorem wellFormed_of_check {plan : ProgramPlan}
    (hCheck : plan.wellFormed? = true) :
    plan.WellFormed := by
  simpa [wellFormed?] using hCheck

theorem check_of_wellFormed {plan : ProgramPlan}
    (hWF : plan.WellFormed) :
    plan.wellFormed? = true := by
  simpa [wellFormed?] using hWF

theorem main_find? (allocation : Plan) :
    (main allocation).find? .main = some allocation := by
  simp [main, singleton, find?]

theorem wellFormed_main {allocation : Plan}
    (hWF : allocation.WellFormed) :
    (main allocation).WellFormed := by
  exact ⟨by simp [main, singleton, scopeIds], by simp [main, singleton, hWF]⟩

end ProgramPlan

structure Planner (Source : Type) where
  plan? : Source → Option ProgramPlan

structure Lowerer (Source Target : Type) where
  lower? : Source → ProgramPlan → Option Target

structure Pipeline (Source Target : Type) where
  planners : List (Planner Source)
  lowerer : Lowerer Source Target

namespace Pipeline

def compile? {Source Target : Type} (pipeline : Pipeline Source Target)
    (source : Source) : Option (Target × ProgramPlan) :=
  go pipeline.planners
  where
    go : List (Planner Source) → Option (Target × ProgramPlan)
      | [] => none
      | planner :: rest =>
          match planner.plan? source with
          | none => go rest
          | some plan =>
              if plan.wellFormed? then
                match pipeline.lowerer.lower? source plan with
                | some target => some (target, plan)
                | none => go rest
              else
                go rest

theorem compile?_go_plan_wellFormed {Source Target : Type}
    (pipeline : Pipeline Source Target) (source : Source)
    {planners : List (Planner Source)} {target : Target}
    {plan : ProgramPlan}
    (hCompile :
      compile?.go pipeline source planners = some (target, plan)) :
    plan.WellFormed := by
  induction planners with
  | nil =>
      simp [compile?.go] at hCompile
  | cons planner rest ih =>
      cases hPlan : planner.plan? source with
      | none =>
          simp [compile?.go, hPlan] at hCompile
          exact ih hCompile
      | some candidate =>
          by_cases hValid : candidate.wellFormed? = true
          · cases hLower : pipeline.lowerer.lower? source candidate with
            | none =>
                simp [compile?.go, hPlan, hValid, hLower] at hCompile
                exact ih hCompile
            | some candidateTarget =>
                simp [compile?.go, hPlan, hValid, hLower] at hCompile
                rcases hCompile with ⟨_hTargetEq, hPlanEq⟩
                subst plan
                exact ProgramPlan.wellFormed_of_check hValid
          · simp [compile?.go, hPlan, hValid] at hCompile
            exact ih hCompile

theorem compile?_plan_wellFormed {Source Target : Type}
    {pipeline : Pipeline Source Target} {source : Source}
    {target : Target} {plan : ProgramPlan}
    (hCompile : pipeline.compile? source = some (target, plan)) :
    plan.WellFormed := by
  exact compile?_go_plan_wellFormed pipeline source hCompile

end Pipeline

end Allocation
end Locals
end EvmCompiler
