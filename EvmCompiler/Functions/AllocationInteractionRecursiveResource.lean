import EvmCompiler.Functions.AllocationInteractionResourceComposition
import EvmCompiler.Functions.AllocationInteractionRecursive
import EvmCompiler.Functions.AllocationInteractionControlAgreement
import EvmCompiler.Functions.AllocationInteractionStatementResource
import EvmCompiler.Functions.AllocationInteractionAbruptResource
import EvmCompiler.Functions.AllocationInteractionControlResource
import EvmCompiler.Functions.AllocationInteractionCallReturnResource
import EvmCompiler.Functions.AllocationInteractionCallPreludeResource
import EvmCompiler.Functions.AllocationInteractionForResource
import EvmCompiler.Functions.AllocationInteractionFunctionReturnResource
import EvmCompiler.Functions.AllocationInteractionLeaveResource
import EvmCompiler.Functions.AllocationInteractionLoopResource
import EvmCompiler.Functions.AllocationInteractionTerminalResource

namespace EvmCompiler
namespace Functions
namespace AllocationInteractionRecursiveResource

open AllocationInteractionRelation
open AllocationInteractionComposition
open AllocationInteractionCursor
open AllocationInteractionFrame
open AllocationInteractionRecursive
open AllocationInteractionResource
open AllocationInteractionResourceComposition

/-- Orthogonal allocator theorem for one canonical allocation cursor. -/
def CursorResourceAt
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (config : Config) (allocatorDepth sourceFuel targetExtra : Nat)
    (entryMode : ActivationMode) (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop :=
  Simulation.Interaction.Rel
    (OpenResultRel config allocatorDepth entryMode target)
    (Functions.InteractionSemantics.Block.openRun program sourceCtx
      sourceFuel sourceBlock source)
    (Expressions.InteractionSemantics.Block.openRun expressions
      (targetBudget cursor sourceFuel targetExtra)
      { stmts := cursor.compiled } target)

/-- Semantic and allocator preservation over one shared interaction tree. -/
def CursorRuntimeAt
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (contract : MemoryContract.Contract)
    (config : Config) (allocatorDepth frameBase sourceFuel targetExtra : Nat)
    (entryMode : ActivationMode) (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop :=
  let regularLive := Functions.Scope.Block.outEnv live sourceBlock
  let regularCtx := { sourceCtx with scope := regularLive }
  Simulation.Interaction.Rel
    (fun sourceDone targetDone =>
      OpenControlResultRel contract root.lowerCtx cursor.finalState
          cursor.finalLocals cursor.plan root.returns regularLive frameBase
          entryMode sourceCtx regularCtx sourceDone targetDone ∧
        OpenResultRel config allocatorDepth entryMode target
          sourceDone targetDone)
    (Functions.InteractionSemantics.Block.openRun program sourceCtx
      sourceFuel sourceBlock source)
    (Expressions.InteractionSemantics.Block.openRun expressions
      (targetBudget cursor sourceFuel targetExtra)
      { stmts := cursor.compiled } target)

namespace CursorRuntimeAt

theorem combine
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx}
    {contract : MemoryContract.Contract}
    {config : Config}
    {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {entryMode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hSemantic :
      CursorForwardAt cursor contract frameBase sourceFuel targetExtra
        entryMode sourceCtx source target)
    (hResource :
      CursorResourceAt cursor config allocatorDepth sourceFuel targetExtra
        entryMode sourceCtx source target) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra entryMode sourceCtx source target := by
  exact Simulation.Interaction.Rel.inter hSemantic hResource

theorem semantic
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx}
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {entryMode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hRuntime :
      CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
        targetExtra entryMode sourceCtx source target) :
    CursorForwardAt cursor contract frameBase sourceFuel targetExtra
      entryMode sourceCtx source target :=
  Simulation.Interaction.Rel.mono hRuntime (fun _ _ hDone => hDone.1)

theorem resource
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx}
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {entryMode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (hRuntime :
      CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
        targetExtra entryMode sourceCtx source target) :
    CursorResourceAt cursor config allocatorDepth sourceFuel targetExtra
      entryMode sourceCtx source target :=
  Simulation.Interaction.Rel.mono hRuntime (fun _ _ hDone => hDone.2)

/-- Compose one exact runtime cursor head with its recursive tail. -/
theorem cons_of_parts
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth childFuel targetExtra frameBase : Nat}
    {entryMode : ActivationMode}
    {sourceCtx midCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    {headCode : List Expressions.Stmt}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest } afterState afterLocals)
    (hTail : ExactTail cursor tail)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hMidCtx :
      midCtx =
        { sourceCtx with scope := Functions.Scope.Stmt.outEnv live stmt })
    (hHead :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (Functions.Scope.Stmt.outEnv live stmt)
          frameBase entryMode sourceCtx midCtx config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor (childFuel + 1) targetExtra)
          { stmts := headCode } target))
    (hTailForward :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState afterLocals tail.plan
            (Functions.Scope.Stmt.outEnv live stmt)
            frameBase mode sourceMid targetMid →
          AllocatorReady config allocatorDepth targetMid →
          SameFrame entryMode mode →
          CursorRuntimeAt tail contract config allocatorDepth frameBase
            childFuel (targetExtra + callStride expressions) mode midCtx
            sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase
      (childFuel + 1) targetExtra entryMode sourceCtx source target := by
  let finalLive :=
    Functions.Scope.Block.outEnv
      (Functions.Scope.Stmt.outEnv live stmt) { stmts := rest }
  rcases hTail with ⟨hPlan, hFinalState, hFinalLocals, _hCompiledTail⟩
  have hComposed :=
    AllocationInteractionResourceComposition.block_cons
      (rest := rest) (headCode := headCode) (tailCode := tail.compiled)
      (plan := cursor.plan)
      (finalLowerCtx := root.lowerCtx)
      (finalLowerState := cursor.finalState)
      (finalLocals := cursor.finalLocals)
      (finalLive := finalLive)
      (finalCtx := { sourceCtx with scope := finalLive })
      (sourceFuel := childFuel)
      (targetFuel := targetBudget cursor (childFuel + 1) targetExtra)
      hHead
      (fun {sourceMid targetMid mode} hInvariant hReady hSame => by
        have hInvariantTail :
            AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan
              (Functions.Scope.Stmt.outEnv live stmt)
              frameBase mode sourceMid targetMid := by
          simpa [hPlan] using hInvariant
        have hRecursive := hTailForward hInvariantTail hReady hSame
        unfold CursorRuntimeAt at hRecursive
        rw [hPlan, hFinalState, hFinalLocals] at hRecursive
        have hTargetFuel :
            targetBudget cursor (childFuel + 1) targetExtra -
                headCode.length =
              targetBudget tail childFuel
                (targetExtra + callStride expressions) := by
          simp [targetBudget, hCompiled, callStride, Nat.mul_succ]
          omega
        have hFinalCtx :
            { midCtx with scope := finalLive } =
              { sourceCtx with scope := finalLive } := by
          rw [hMidCtx]
        simpa [CursorRuntimeAt, finalLive,
          hTargetFuel, hFinalCtx] using hRecursive)
  unfold CursorRuntimeAt
  rw [hCompiled]
  simpa [finalLive] using hComposed

/-- Compose one exact runtime head with only the successful, reachable tail
branches. -/
theorem cons_of_parts_successful
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {contract : MemoryContract.Contract} {config : Config}
    {allocatorDepth childFuel targetExtra frameBase : Nat}
    {entryMode : ActivationMode}
    {sourceCtx midCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    {headCode : List Expressions.Stmt}
    (cursor : CoreCursor root scope live { stmts := stmt :: rest }
      beforeState beforeLocals)
    (tail : CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
      { stmts := rest } afterState afterLocals)
    (hTail : ExactTail cursor tail)
    (hCompiled : cursor.compiled = headCode ++ tail.compiled)
    (hMidCtx :
      midCtx = { sourceCtx with
        scope := Functions.Scope.Stmt.outEnv live stmt })
    (hHead :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (Functions.Scope.Stmt.outEnv live stmt)
          frameBase entryMode sourceCtx midCtx config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel stmt source)
        (Expressions.InteractionSemantics.Block.openRun expressions
          (targetBudget cursor (childFuel + 1) targetExtra)
          { stmts := headCode } target))
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          (childFuel + 1) { stmts := stmt :: rest } source))
    (hTailForward :
      ∀ {sourceMid targetMid mode},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState afterLocals tail.plan
            (Functions.Scope.Stmt.outEnv live stmt)
            frameBase mode sourceMid targetMid →
          AllocatorReady config allocatorDepth targetMid →
          SameFrame entryMode mode →
          targetMid.returns = target.returns →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program midCtx
              childFuel { stmts := rest } sourceMid) →
          CursorRuntimeAt tail contract config allocatorDepth frameBase
            childFuel (targetExtra + callStride expressions) mode midCtx
            sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase
      (childFuel + 1) targetExtra entryMode sourceCtx source target := by
  let finalLive :=
    Functions.Scope.Block.outEnv
      (Functions.Scope.Stmt.outEnv live stmt) { stmts := rest }
  rcases hTail with ⟨hPlan, hFinalState, hFinalLocals, _hCompiledTail⟩
  have hComposed :=
    AllocationInteractionResourceComposition.block_cons_successful
      (rest := rest) (headCode := headCode) (tailCode := tail.compiled)
      (plan := cursor.plan) (finalLowerCtx := root.lowerCtx)
      (finalLowerState := cursor.finalState)
      (finalLocals := cursor.finalLocals) (finalLive := finalLive)
      (finalCtx := { sourceCtx with scope := finalLive })
      (sourceFuel := childFuel)
      (targetFuel := targetBudget cursor (childFuel + 1) targetExtra)
      hHead hSuccessful
      (fun {sourceMid targetMid mode} hInvariant hReady hSame hReturns
          hTailSuccess => by
        have hInvariantTail :
            AllocationContext.ActivationInvariant contract root.lowerCtx
              afterState afterLocals tail.plan
              (Functions.Scope.Stmt.outEnv live stmt)
              frameBase mode sourceMid targetMid := by
          simpa [hPlan] using hInvariant
        have hRecursive :=
          hTailForward hInvariantTail hReady hSame hReturns hTailSuccess
        unfold CursorRuntimeAt at hRecursive
        rw [hPlan, hFinalState, hFinalLocals] at hRecursive
        have hTargetFuel :
            targetBudget cursor (childFuel + 1) targetExtra -
                headCode.length =
              targetBudget tail childFuel
                (targetExtra + callStride expressions) := by
          simp [targetBudget, hCompiled, callStride, Nat.mul_succ]
          omega
        have hFinalCtx :
            { midCtx with scope := finalLive } =
              { sourceCtx with scope := finalLive } := by
          rw [hMidCtx]
        simpa [CursorRuntimeAt, finalLive, hTargetFuel, hFinalCtx] using
          hRecursive)
  unfold CursorRuntimeAt
  rw [hCompiled]
  simpa [finalLive] using hComposed

end CursorRuntimeAt

/--
Dynamic allocator facts paired with the existing semantic recursive boundary.
This is internal proof state derived from the compiler's frame configuration;
it is not source semantics or public generated evidence.
-/
structure Boundary
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    (cursor : CoreCursor root scope live sourceBlock lowerState localsCtx)
    (contract : MemoryContract.Contract)
    (globalFrameWords : Nat) (config : Config) (allocatorDepth frameBase : Nat)
    (mode : ActivationMode) (sourceCtx : Functions.Source.Ctx)
    (source : SourceState) (target : TargetState) : Prop where
  semantic :
    AllocationInteractionRecursive.Boundary cursor contract frameBase mode
      sourceCtx source target
  controlAgreement :
    AllocationInteractionControlAgreement.Agreement cursor.plan root.returns
      live mode sourceCtx localsCtx target
  configEq :
    AllocationSupport.scratchFrameConfig? contract globalFrameWords =
      some config
  ready : AllocatorReady config allocatorDepth target
  owned : ActivationOwned config allocatorDepth frameBase mode
  budget : AllocationInteractionFrame.Budget config allocatorDepth

namespace Boundary

/-- Transport exact control destinations through an ordinary statement whose
source live set is unchanged. The cursor owner supplies Locals control
preservation; runtime preservation supplies the unchanged return stack. -/
def controlAgreement_same_live
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {stmt : Functions.Stmt} {rest : List Functions.Stmt}
    {beforeState afterState : AllocationLowering.State}
    {beforeLocals afterLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords : Nat} {config : Config}
    {allocatorDepth frameBase : Nat}
    {mode tailMode : ActivationMode}
    {sourceCtx nextCtx : Functions.Source.Ctx}
    {source sourceMid : SourceState} {target targetMid : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := stmt :: rest }
        beforeState beforeLocals)
    (tail :
      CoreCursor root scope (Functions.Scope.Stmt.outEnv live stmt)
        { stmts := rest }
        afterState afterLocals)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth
        frameBase mode sourceCtx source target)
    (hExact : ExactTail cursor tail)
    (hOut : Functions.Scope.Stmt.outEnv live stmt = live)
    (hInvariant :
      AllocationContext.ActivationInvariant contract root.lowerCtx afterState
        afterLocals tail.plan (Functions.Scope.Stmt.outEnv live stmt)
        frameBase tailMode sourceMid targetMid)
    (hSame : SameFrame mode tailMode)
    (hSource : Functions.Source.Ctx.SameControl sourceCtx nextCtx)
    (hReturns : targetMid.returns = target.returns) :
    AllocationInteractionControlAgreement.Agreement tail.plan root.returns
      live tailMode nextCtx afterLocals targetMid := by
  have hAfterMatches := hInvariant.compiler.mode_matches
  have hAfterMatchesLive : tailMode.Matches tail.plan live :=
    hAfterMatches.transport_live fun name => by rw [hOut]
  rw [hExact.plan] at hAfterMatchesLive
  have hModeEq := hSame.eq_of_matches
    hBoundary.semantic.invariant.compiler.mode_matches hAfterMatchesLive
  subst tailMode
  have hLocals := hExact.locals_sameControl cursor tail
  rw [hExact.plan]
  exact
    (hBoundary.controlAgreement.transport_context hSource hLocals)
      |>.transport_target hReturns

end Boundary

/--
Fuel-bounded recursive semantic/resource capability. Configuration, allocator
depth, and activation ownership remain quantified so internal callees may use
their compiler-selected frame without a public call oracle.
-/
def RecursiveOpenRuntime
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    (contract : MemoryContract.Contract)
    (globalFrameWords fuelBound : Nat) : Prop :=
  ∀ {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Config} {allocatorDepth frameBase : Nat}
    {sourceFuel targetExtra : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx),
    sourceFuel < fuelBound →
    Boundary cursor contract globalFrameWords config allocatorDepth frameBase
      mode sourceCtx source target →
    AllocationInteractionFrame.Budget config (allocatorDepth + sourceFuel) →
    AllocationInteractionTargetFuel.Reserve cursor targetExtra →
    Simulation.Interaction.Successful
      (Functions.InteractionSemantics.Block.openRun program sourceCtx
        sourceFuel sourceBlock source) →
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target

namespace RecursiveOpenRuntime

/-- Instantiate the recursive capability at a larger exact target budget. -/
theorem at_targetFuel
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {contract : MemoryContract.Contract}
    {globalFrameWords fuelBound : Nat}
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords fuelBound)
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {sourceBlock : Functions.Block}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Config} {allocatorDepth frameBase : Nat}
    {sourceFuel targetFuel : Nat}
    {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live sourceBlock lowerState localsCtx)
    (hFuel : sourceFuel < fuelBound)
    (hTargetFuel :
      targetBudget cursor sourceFuel
          (AllocationInteractionTargetFuel.stmtListNestedSize
            cursor.compiled) ≤
        targetFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config (allocatorDepth + sourceFuel))
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel sourceBlock source)) :
    Simulation.Interaction.Rel
      (RuntimeResultRel contract root.lowerCtx cursor.finalState
        cursor.finalLocals cursor.plan root.returns
        (Functions.Scope.Block.outEnv live sourceBlock) frameBase mode sourceCtx
        { sourceCtx with
          scope := Functions.Scope.Block.outEnv live sourceBlock }
        config allocatorDepth target)
      (Functions.InteractionSemantics.Block.openRun program sourceCtx
        sourceFuel sourceBlock source)
      (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
        { stmts := cursor.compiled } target) := by
  let targetExtra := targetFuel - targetBudget cursor sourceFuel 0
  have hReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra := by
    change
      AllocationInteractionTargetFuel.stmtListNestedSize cursor.compiled ≤
        targetExtra
    simp only [targetExtra, targetBudget] at hTargetFuel ⊢
    omega
  have hForward :=
    hRecursive cursor hFuel hBoundary hFuelBudget hReserve hSuccess
      (targetExtra := targetExtra)
  have hExact :
      targetBudget cursor sourceFuel targetExtra = targetFuel := by
    simp [targetBudget, targetExtra, callStride, Nat.mul_succ]
      at hTargetFuel ⊢
    omega
  simpa [CursorRuntimeAt, hExact] using hForward

end RecursiveOpenRuntime

namespace SelectedCallee

/-- The real selected procedure table bounds every nested statement in the
prepared callee body. -/
theorem bodyCode_size_le_callStride
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared :
      AllocationInteractionCall.SelectedCallee.Prepared artifact) :
    AllocationInteractionTargetFuel.stmtListSize prepared.bodyCode ≤
      callStride expressions := by
  apply selected_body_code_size_le_callStride
    (program := expressions) (name := name)
    (proc := artifact.lowerProc)
    (bodyPrefix :=
      prepared.markerCode ++ prepared.paramCode ++ prepared.returnCode)
    (bodySuffix :=
      Locals.codeStmt prepared.returnValueCode ++
        Locals.codeStmt prepared.cleanup)
    artifact.targetLookup
  simpa [List.append_assoc] using prepared.procBody

/--
Compose compiler-selected callee setup with the shared recursive runtime for
its canonical body root. The recursive capability is fuel-bounded proof state,
not a public call oracle or alternate compiler.
-/
theorem body_of_cursor
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared :
      AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel fuelBound
      targetExtra : Nat}
    {config : Config}
    {sourceLive : List Functions.Name}
    {sourceCtx : Functions.Source.Ctx}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase artifact.mode source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReturnFrame : target.returns ≠ [])
    (hReservation : contract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase artifact.mode)
    (hBudget : AllocationInteractionFrame.Budget config allocatorDepth)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config (allocatorDepth + sourceFuel))
    (hTargetReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode ≤
        targetExtra)
    (hSourceFuel : sourceFuel < fuelBound)
    (hLive :
      ∀ localName,
        localName ∈
            (artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse ↔
          localName ∈ sourceLive)
    (hSourceScope :
      sourceCtx.scope = sourceLive)
    (hControl :
      AllocationInteractionStatement.ControlScopesWithin fn.returns
        sourceLive sourceCtx)
    (hSourceBreak : sourceCtx.breakScope? = none)
    (hSourceContinue : sourceCtx.continueScope? = none)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel fn.body source))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords fuelBound) :
    ∃ targetFuel,
      0 < targetFuel ∧
      prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + prepared.bodyCode.length +
          targetExtra ≤ targetFuel ∧
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              callStride expressions * (sourceFuel + 1)) ∧
      Simulation.Interaction.Rel
        (RuntimeResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns
          (Functions.Scope.Block.outEnv sourceLive fn.body)
          frameBase artifact.mode sourceCtx
          { sourceCtx with
            scope := Functions.Scope.Block.outEnv sourceLive fn.body }
          config allocatorDepth target)
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel fn.body source)
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          { stmts :=
              prepared.markerCode ++ prepared.paramCode ++
                prepared.returnCode ++ prepared.bodyCode }
          target) := by
  let compilerLive :=
    (artifact.slots.returns.map Prod.fst).reverse ++
      (artifact.slots.params.map Prod.fst).reverse
  let live := sourceLive
  let bodyCursor :=
    (prepared.rootCursor hProgramScoped).transport_live hLive
  have hSetupFrame : SameFrame artifact.mode prepared.bodyMode := by
    exact SameFrame.atStackDepth artifact.mode
      (currentStackOrder prepared.plan compilerLive).length
  have hEntryToReturnControl :
      Locals.Ctx.SameControl artifact.entryCtx prepared.returnCtx :=
    (Locals.Block.compileOpen_sameControl prepared.compileParams).trans
      (Locals.Block.compileOpen_sameControl prepared.compileReturns)
  have hLeaveDepth : prepared.returnCtx.leaveDepth? = some 0 := by
    simpa [AllocationInteractionCall.SelectedCallee.Artifact.entryCtx,
      Locals.Ctx.procEntryWithLayoutAndRetc,
      Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
      Locals.Ctx.initial] using hEntryToReturnControl.leaveDepth.symm
  have hLeaveRetc : prepared.returnCtx.leaveRetc = fn.returns.length := by
    simpa [AllocationInteractionCall.SelectedCallee.Artifact.entryCtx,
      Locals.Ctx.procEntryWithLayoutAndRetc,
      Locals.Ctx.procEntryWithLayout, Locals.Ctx.procEntry,
      Locals.Ctx.initial] using hEntryToReturnControl.leaveRetc.symm
  by_cases hNeedsFrame : artifact.needsFrame = true
  · have hScratchEntry :
        ActivationCalleeEntryRel contract prepared.plan []
          artifact.slots.params frameBase
          (.scratch 0 compilation.recipe.frameWords) source target := by
      simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrame] using hEntry
    have hScratchOwned :
        ActivationOwned config allocatorDepth frameBase
          (.scratch 0 compilation.recipe.frameWords) := by
      simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrame] using hOwned
    have hCapacity :
        AllocationInteractionForward.FrameCapacity compilation
          prepared.bodyMode := by
      rw [show prepared.bodyMode =
          .scratch
            (currentStackOrder prepared.plan compilerLive).length
            compilation.recipe.frameWords by
        simp [AllocationInteractionCall.SelectedCallee.Prepared.bodyMode,
          AllocationInteractionCall.SelectedCallee.Artifact.mode,
          ActivationMode.atStackDepth, hNeedsFrame, compilerLive]]
      exact Nat.le_refl _
    obtain
        ⟨_afterParams, bodyTarget, _paramFuel, _returnFuel, _preludeFuel,
          _hParamFuel, _hReturnFuel, _hMarkers, _hParams, _hReturns,
          _hPreludeFuel, _hPreludeLength, _hPrelude, hPreludeAt,
          hInvariant, hSetupEffect⟩ :=
      AllocationInteractionCallPreludeResource.Prepared.body_entry_resource_scratch
        prepared hConfig hNeedsFrame hScratchEntry hZero hStackLength
        hReservation hReady hScratchOwned
    have hSetupEffect' :
        ActivationEffect config allocatorDepth artifact.mode target
          bodyTarget := by
      simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrame] using hSetupEffect
    have hBodyReturns : bodyTarget.returns = target.returns := by
      have hAll := Expressions.InteractionReturns.Block.openRun_returns
        expressions
        (prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + 1)
        { stmts :=
            prepared.markerCode ++
              (prepared.paramCode ++ prepared.returnCode) }
        target
      rw [hPreludeAt 1 (by omega)] at hAll
      cases hAll with
      | done hDone =>
          simpa [Structured.InteractionReturns.OutcomeReturnsEq] using hDone
    have hBodyReturnFrame : bodyTarget.returns ≠ [] := by
      intro hEmpty
      apply hReturnFrame
      rw [← hBodyReturns, hEmpty]
    have hBodyBoundary :
        Boundary bodyCursor contract
          globalFrameWords config allocatorDepth frameBase prepared.bodyMode
          sourceCtx source bodyTarget :=
      { semantic :=
          { invariant := hInvariant.transport_live hLive
            sourceScope := hSourceScope
            control := hControl
            capacity := hCapacity }
        controlAgreement :=
          AllocationInteractionControlAgreement.Agreement.functionBody
            hSourceBreak hSourceContinue hLeaveDepth hLeaveRetc
              hBodyReturnFrame
        configEq := hConfig
        ready := hSetupEffect.ready
        owned := hOwned.sameFrame hSetupFrame
        budget := hBudget }
    have hBodyRaw :=
      hRecursive bodyCursor hSourceFuel
        hBodyBoundary hFuelBudget
          (by
            simpa [AllocationInteractionTargetFuel.Reserve, bodyCursor] using
              hTargetReserve)
          hSuccess (targetExtra := targetExtra)
    let bodyFuel :=
      targetBudget bodyCursor sourceFuel targetExtra
    have hBodyFuel : 0 < bodyFuel := by
      simp [bodyFuel, targetBudget, callStride, Nat.mul_succ]
    have hBody :
        Simulation.Interaction.Rel
          (RuntimeResultRel contract artifact.lowerCtx prepared.bodyFinal
            prepared.bodyCtx prepared.plan fn.returns
            (Functions.Scope.Block.outEnv live fn.body)
            frameBase prepared.bodyMode sourceCtx
            { sourceCtx with
              scope := Functions.Scope.Block.outEnv live fn.body }
            config allocatorDepth bodyTarget)
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            sourceFuel fn.body source)
          (Expressions.InteractionSemantics.Block.openRun expressions bodyFuel
            { stmts := prepared.bodyCode } bodyTarget) := by
      simpa [CursorRuntimeAt, bodyFuel, bodyCursor, live] using hBodyRaw
    have hBodyFromEntry :
        Simulation.Interaction.Rel
          (RuntimeResultRel contract artifact.lowerCtx prepared.bodyFinal
            prepared.bodyCtx prepared.plan fn.returns
            (Functions.Scope.Block.outEnv live fn.body)
            frameBase artifact.mode sourceCtx
            { sourceCtx with
              scope := Functions.Scope.Block.outEnv live fn.body }
            config allocatorDepth target)
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            sourceFuel fn.body source)
          (Expressions.InteractionSemantics.Block.openRun expressions bodyFuel
            { stmts := prepared.bodyCode } bodyTarget) := by
      apply Simulation.Interaction.Rel.mono hBody
      intro sourceDone targetDone hDone
      exact RuntimeResultRel.prepend_frame hSetupFrame hSetupEffect' hDone
    let totalFuel :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + bodyFuel
    refine ⟨totalFuel, by simp [totalFuel]; omega, ?_, ?_, ?_⟩
    · change
        prepared.markerCode.length + prepared.paramCode.length +
            prepared.returnCode.length + prepared.bodyCode.length +
            targetExtra ≤
          prepared.markerCode.length + prepared.paramCode.length +
            prepared.returnCode.length +
              (targetExtra + prepared.bodyCode.length +
                callStride expressions * (sourceFuel + 1))
      omega
    · simp [totalFuel, bodyFuel, bodyCursor, targetBudget,
        AllocationInteractionCall.SelectedCallee.Prepared.rootCursor,
        AllocationInteractionCall.SelectedCallee.Prepared.rootArtifact,
        RootArtifact.cursor, CoreCursor.transport_live]
    simpa [totalFuel, live] using
      prepared.prelude_then_body hBodyFuel hPreludeAt hBodyFromEntry
  · have hNeedsFrameFalse : artifact.needsFrame = false :=
      Bool.eq_false_of_not_eq_true hNeedsFrame
    have hStackEntry :
        ActivationCalleeEntryRel contract prepared.plan []
          artifact.slots.params frameBase .stack source target := by
      simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrameFalse] using hEntry
    have hCapacity :
        AllocationInteractionForward.FrameCapacity compilation
          prepared.bodyMode := by
      rw [show prepared.bodyMode = .stack by
        simp [AllocationInteractionCall.SelectedCallee.Prepared.bodyMode,
          AllocationInteractionCall.SelectedCallee.Artifact.mode,
          ActivationMode.atStackDepth, hNeedsFrameFalse]]
      trivial
    obtain
        ⟨_afterParams, bodyTarget, _paramFuel, _returnFuel, _preludeFuel,
          _hParamFuel, _hReturnFuel, _hMarkers, _hParams, _hReturns,
          _hPreludeFuel, _hPreludeLength, _hPrelude, hPreludeAt,
          hInvariant, hSetupEffect⟩ :=
      AllocationInteractionCallPreludeResource.Prepared.body_entry_resource_stack
        prepared hNeedsFrameFalse hStackEntry hZero hStackLength hReady
    have hSetupEffect' :
        ActivationEffect config allocatorDepth artifact.mode target
          bodyTarget := by
      simpa [AllocationInteractionCall.SelectedCallee.Artifact.mode,
        hNeedsFrameFalse] using hSetupEffect
    have hBodyReturns : bodyTarget.returns = target.returns := by
      have hAll := Expressions.InteractionReturns.Block.openRun_returns
        expressions
        (prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + 1)
        { stmts :=
            prepared.markerCode ++
              (prepared.paramCode ++ prepared.returnCode) }
        target
      rw [hPreludeAt 1 (by omega)] at hAll
      cases hAll with
      | done hDone =>
          simpa [Structured.InteractionReturns.OutcomeReturnsEq] using hDone
    have hBodyReturnFrame : bodyTarget.returns ≠ [] := by
      intro hEmpty
      apply hReturnFrame
      rw [← hBodyReturns, hEmpty]
    have hBodyBoundary :
        Boundary bodyCursor contract
          globalFrameWords config allocatorDepth frameBase prepared.bodyMode
          sourceCtx source bodyTarget :=
      { semantic :=
          { invariant := hInvariant.transport_live hLive
            sourceScope := hSourceScope
            control := hControl
            capacity := hCapacity }
        controlAgreement :=
          AllocationInteractionControlAgreement.Agreement.functionBody
            hSourceBreak hSourceContinue hLeaveDepth hLeaveRetc
              hBodyReturnFrame
        configEq := hConfig
        ready := hSetupEffect.ready
        owned := hOwned.sameFrame hSetupFrame
        budget := hBudget }
    have hBodyRaw :=
      hRecursive bodyCursor hSourceFuel
        hBodyBoundary hFuelBudget
          (by
            simpa [AllocationInteractionTargetFuel.Reserve, bodyCursor] using
              hTargetReserve)
          hSuccess (targetExtra := targetExtra)
    let bodyFuel :=
      targetBudget bodyCursor sourceFuel targetExtra
    have hBodyFuel : 0 < bodyFuel := by
      simp [bodyFuel, targetBudget, callStride, Nat.mul_succ]
    have hBody :
        Simulation.Interaction.Rel
          (RuntimeResultRel contract artifact.lowerCtx prepared.bodyFinal
            prepared.bodyCtx prepared.plan fn.returns
            (Functions.Scope.Block.outEnv live fn.body)
            frameBase prepared.bodyMode sourceCtx
            { sourceCtx with
              scope := Functions.Scope.Block.outEnv live fn.body }
            config allocatorDepth bodyTarget)
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            sourceFuel fn.body source)
          (Expressions.InteractionSemantics.Block.openRun expressions bodyFuel
            { stmts := prepared.bodyCode } bodyTarget) := by
      simpa [CursorRuntimeAt, bodyFuel, bodyCursor, live] using hBodyRaw
    have hBodyFromEntry :
        Simulation.Interaction.Rel
          (RuntimeResultRel contract artifact.lowerCtx prepared.bodyFinal
            prepared.bodyCtx prepared.plan fn.returns
            (Functions.Scope.Block.outEnv live fn.body)
            frameBase artifact.mode sourceCtx
            { sourceCtx with
              scope := Functions.Scope.Block.outEnv live fn.body }
            config allocatorDepth target)
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            sourceFuel fn.body source)
          (Expressions.InteractionSemantics.Block.openRun expressions bodyFuel
            { stmts := prepared.bodyCode } bodyTarget) := by
      apply Simulation.Interaction.Rel.mono hBody
      intro sourceDone targetDone hDone
      exact RuntimeResultRel.prepend_frame hSetupFrame hSetupEffect' hDone
    let totalFuel :=
      prepared.markerCode.length + prepared.paramCode.length +
        prepared.returnCode.length + bodyFuel
    refine ⟨totalFuel, by simp [totalFuel]; omega, ?_, ?_, ?_⟩
    · change
        prepared.markerCode.length + prepared.paramCode.length +
            prepared.returnCode.length + prepared.bodyCode.length +
            targetExtra ≤
          prepared.markerCode.length + prepared.paramCode.length +
            prepared.returnCode.length +
              (targetExtra + prepared.bodyCode.length +
                callStride expressions * (sourceFuel + 1))
      omega
    · simp [totalFuel, bodyFuel, bodyCursor, targetBudget,
        AllocationInteractionCall.SelectedCallee.Prepared.rootCursor,
        AllocationInteractionCall.SelectedCallee.Prepared.rootArtifact,
        RootArtifact.cursor, CoreCursor.transport_live]
    simpa [totalFuel, live] using
      prepared.prelude_then_body hBodyFuel hPreludeAt hBodyFromEntry

/-- Canonical `runBody` context supplies the selected-callee scope boundary. -/
theorem body_of_function_context
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {name : Functions.Name} {fn : Functions.FunDef}
    {artifact : AllocationInteractionCall.SelectedCallee.Artifact
      compilation name fn}
    (prepared :
      AllocationInteractionCall.SelectedCallee.Prepared artifact)
    (hProgramScoped : program.Scoped)
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel fuelBound
      targetExtra : Nat}
    {config : Config}
    {source : Functions.InteractionSemantics.State}
    {target : Structured.RunState}
    {reservation : MemoryContract.ScratchReservation}
    (hEntry :
      ActivationCalleeEntryRel contract prepared.plan []
        artifact.slots.params frameBase artifact.mode source target)
    (hZero :
      ∀ localName,
        localName ∈ artifact.slots.returns.map Prod.fst →
        source.vars localName = some AllocationSupport.zeroWord)
    (hStackLength :
      target.evm.stack.length = artifact.entryCtx.layout.length)
    (hReturnFrame : target.returns ≠ [])
    (hReservation : contract.scratch? = some reservation)
    (hConfig :
      AllocationSupport.scratchFrameConfig? contract globalFrameWords =
        some config)
    (hReady : AllocatorReady config allocatorDepth target)
    (hOwned :
      ActivationOwned config allocatorDepth frameBase artifact.mode)
    (hBudget : AllocationInteractionFrame.Budget config allocatorDepth)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config (allocatorDepth + sourceFuel))
    (hTargetReserve :
      AllocationInteractionTargetFuel.stmtListNestedSize prepared.bodyCode ≤
        targetExtra)
    (hSourceFuel : sourceFuel < fuelBound)
    (hSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords fuelBound) :
    ∃ targetFuel,
      0 < targetFuel ∧
      prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length + prepared.bodyCode.length +
          targetExtra ≤ targetFuel ∧
      targetFuel =
        prepared.markerCode.length + prepared.paramCode.length +
          prepared.returnCode.length +
            (targetExtra + prepared.bodyCode.length +
              callStride expressions * (sourceFuel + 1)) ∧
      Simulation.Interaction.Rel
        (RuntimeResultRel contract artifact.lowerCtx prepared.bodyFinal
          prepared.bodyCtx prepared.plan fn.returns
          (Functions.Scope.Block.outEnv
            (fn.returns ++ fn.params)
            fn.body)
          frameBase artifact.mode
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          { Functions.Source.Effectful.FunDef.bodyCtx fn with
            scope :=
              Functions.Scope.Block.outEnv
                (fn.returns ++ fn.params)
                fn.body }
          config allocatorDepth target)
        (Functions.InteractionSemantics.Block.openRun program
          (Functions.Source.Effectful.FunDef.bodyCtx fn)
          sourceFuel fn.body source)
        (Expressions.InteractionSemantics.Block.openRun expressions targetFuel
          { stmts :=
              prepared.markerCode ++ prepared.paramCode ++
                prepared.returnCode ++ prepared.bodyCode }
          target) := by
  have hScope :
      (Functions.Source.Effectful.FunDef.bodyCtx fn).scope =
        fn.returns ++ fn.params := by
    rfl
  have hLive :
      ∀ localName,
        localName ∈
            (artifact.slots.returns.map Prod.fst).reverse ++
              (artifact.slots.params.map Prod.fst).reverse ↔
          localName ∈ fn.returns ++ fn.params := by
    intro localName
    simp [artifact.slotsMatch.2.1, artifact.slotsMatch.2.2]
  have hControl :
      AllocationInteractionStatement.ControlScopesWithin fn.returns
        (fn.returns ++ fn.params)
        (Functions.Source.Effectful.FunDef.bodyCtx fn) := by
    exact AllocationInteractionStatement.ControlScopesWithin.functionBody fn
  have hSourceBreak :
      (Functions.Source.Effectful.FunDef.bodyCtx fn).breakScope? = none := rfl
  have hSourceContinue :
      (Functions.Source.Effectful.FunDef.bodyCtx fn).continueScope? = none := rfl
  exact body_of_cursor prepared hProgramScoped hEntry hZero hStackLength
    hReturnFrame
    hReservation hConfig hReady hOwned hBudget hFuelBudget hTargetReserve
    hSourceFuel hLive hScope hControl hSourceBreak hSourceContinue hSuccess
    hRecursive

end SelectedCallee

/-- One compiler decomposition supplies both expression-head capabilities. -/
theorem CoreCursor.expr_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth sourceFuel targetExtra frameBase : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .expr expr :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.expr expr) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ := cursor.cons
  have hExprScoped : Functions.Scope.ExprScoped live expr := by
    simpa [Functions.Scope.Stmt.Scoped] using hScoped
  have hSemantic :=
    AllocationInteractionLeaf.expr_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSafe hExprScoped hLower hCompile hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionStatementResource.expr_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hBoundary.configEq hSafe hExprScoped hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- One compiler decomposition supplies both assignment-head capabilities. -/
theorem CoreCursor.assign_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth sourceFuel targetExtra frameBase : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .assign name value :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.assign name value) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ := cursor.cons
  have hSemantic :=
    AllocationInteractionLeaf.assign_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSafe hScoped.2 hScoped.1 hLower hCompile hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionStatementResource.assign_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hBoundary.configEq hSafe hScoped.2 hScoped.1 hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready hBoundary.owned
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- One compiler decomposition supplies both declaration-head capabilities. -/
theorem CoreCursor.let_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth sourceFuel targetExtra frameBase : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .let_ name value :: rest }
        beforeState beforeLocals)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope (name :: live) { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns (name :: live) frameBase mode
              sourceCtx { sourceCtx with scope := name :: sourceCtx.scope }
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.let_ name value) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 2) { stmts := headCode } target) ∧
          DeclarationPlacement root.lowerCtx beforeState cursor.plan live
            name ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ := cursor.cons
  have hPlacement := cursor.declarationPlacement tail hPlanning hPlan
  obtain ⟨afterMode, hAfter, hTransition⟩ :=
    cursor.letContext tail hPlanning hPlan
      hBoundary.semantic.invariant.compiler hLower hCompile
  have hNameFrame : name ≠ root.lowerCtx.frameName := by
    intro hEq
    apply tail.frameName_not_mem_live
    change compilation.frameName ∈ name :: live
    have hNameCompilation : name = compilation.frameName :=
      hEq.trans root.lowerCtxShared.frameName
    simp [hNameCompilation]
  have hScratchBound :
      ∀ {frameDepth frameWords slot},
        mode = .scratch frameDepth frameWords →
        cursor.plan.location? name = some (.scratch slot) →
        slot < frameWords := by
    intro frameDepth frameWords slot hMode hLocation
    have hCapacity := hBoundary.semantic.capacity
    rw [hMode] at hCapacity
    exact
      lt_of_lt_of_le
        (cursor.scratch_bound_of_location hLocation)
        hCapacity
  have hSemantic :
      Simulation.Interaction.Rel
        (OpenControlResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (name :: live) frameBase mode sourceCtx
          { sourceCtx with scope := name :: sourceCtx.scope })
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx sourceFuel (.let_ name value) source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions (targetExtra + 2) { stmts := headCode } target) := by
    cases mode with
    | stack =>
        cases hTransition with
        | stack planDepth hLocation =>
            cases hAfter with
            | stack hAfterStack =>
                exact
                  AllocationInteractionLeaf.stack_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hSafe hAfterStack hScoped.2 hLower hCompile
                    hBoundary.semantic.invariant
    | scratch frameDepth frameWords =>
        cases hTransition with
        | stack planDepth hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionLeaf.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hSafe hAfterScratch hScoped.2 rfl hNameFrame
                    (fun slot hLocation => hScratchBound rfl hLocation)
                    hLower hCompile hBoundary.semantic.invariant
        | scratch frameDepth frameWords slot hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionLeaf.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hSafe hAfterScratch hScoped.2 rfl hNameFrame
                    (fun slot hLocation => hScratchBound rfl hLocation)
                    hLower hCompile hBoundary.semantic.invariant
  have hResource :
      Simulation.Interaction.Rel
        (OpenResultRel config allocatorDepth mode target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx sourceFuel (.let_ name value) source)
        (Expressions.InteractionSemantics.Block.openRun
          expressions (targetExtra + 2) { stmts := headCode } target) := by
    cases mode with
    | stack =>
        cases hTransition with
        | stack planDepth hLocation =>
            cases hAfter with
            | stack hAfterStack =>
                exact
                  AllocationInteractionStatementResource.stack_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hBoundary.configEq hSafe hAfterStack hScoped.2 hLower
                    hCompile hBoundary.semantic.invariant hBoundary.ready
    | scratch frameDepth frameWords =>
        cases hTransition with
        | stack planDepth hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionStatementResource.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hBoundary.configEq hSafe hAfterScratch hScoped.2 rfl
                    hNameFrame
                    (fun slot hLocation => hScratchBound rfl hLocation)
                    hLower hCompile hBoundary.semantic.invariant
                    hBoundary.ready hBoundary.owned
        | scratch frameDepth frameWords slot hLocation =>
            cases hAfter with
            | scratch hAfterScratch =>
                exact
                  AllocationInteractionStatementResource.scratch_let_of_lower_compile
                    (sourceProgram := program) (sourceCtx := sourceCtx)
                    (targetProgram := expressions)
                    (sourceFuel := sourceFuel) (targetExtra := targetExtra)
                    hBoundary.configEq hSafe hAfterScratch hScoped.2 rfl
                    hNameFrame
                    (fun slot hLocation => hScratchBound rfl hLocation)
                    hLower hCompile hBoundary.semantic.invariant
                    hBoundary.ready hBoundary.owned
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      hPlacement,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- One cursor decomposition supplies both `break` head capabilities. -/
theorem CoreCursor.brk_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth sourceFuel targetExtra targetDepth
      frameBase : Nat}
    {config : Config} {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .brk :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : beforeLocals.breakDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        beforeMode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase beforeMode sourceCtx
              sourceCtx config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel .brk source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ := cursor.cons
  have hSemantic :=
    AllocationInteractionAbrupt.brk_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile
      hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionAbruptResource.brk_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- One cursor decomposition supplies both `continue` head capabilities. -/
theorem CoreCursor.cont_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth sourceFuel targetExtra targetDepth
      frameBase : Nat}
    {config : Config} {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .cont :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : beforeLocals.continueDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        beforeMode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase beforeMode sourceCtx
              sourceCtx config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel .cont source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ := cursor.cons
  have hSemantic :=
    AllocationInteractionAbrupt.cont_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile
      hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionAbruptResource.cont_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hTargetDepth hTransition hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- One cursor decomposition supplies both function-leave capabilities. -/
theorem CoreCursor.leave_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live functionScope : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth sourceFuel targetExtra frameBase : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .leave :: rest }
        beforeState beforeLocals)
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hReturnsLive : ∀ name, name ∈ root.returns → name ∈ live)
    (hReturnsScope : ∀ name, name ∈ root.returns → name ∈ functionScope)
    (hTargetDepth : beforeLocals.leaveDepth? = some 0)
    (hRetc : beforeLocals.leaveRetc = root.returns.length)
    (hReturnFrame : target.returns ≠ [])
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel .leave source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 4) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ := cursor.cons
  have hSemantic :=
    AllocationInteractionLeave.leave_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hSourceScope hReturnsLive hReturnsScope hTargetDepth hRetc
      hReturnFrame hLower hCompile hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionLeaveResource.leave_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hBoundary.configEq hSourceScope hReturnsLive hReturnsScope hTargetDepth
      hRetc hReturnFrame hLower hCompile hBoundary.semantic.invariant
      hBoundary.ready
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- One cursor decomposition supplies both plain-terminal capabilities. -/
theorem CoreCursor.terminal_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth sourceFuel targetExtra frameBase : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .terminal kind :: rest }
        beforeState beforeLocals)
    (hMemory : Simulation.MemorySafety.TerminalMemorySafe contract kind [])
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.terminal kind) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, _hScoped⟩ := cursor.cons
  have hSemantic :=
    AllocationInteractionTerminal.terminal_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hMemory hLower hCompile hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionTerminalResource.terminal_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hMemory hLower hCompile hBoundary.semantic.invariant hBoundary.ready
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

/-- One cursor decomposition supplies argument-terminal capabilities. -/
theorem CoreCursor.terminalArgs_runtime_head
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth sourceFuel targetExtra frameBase : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live
        { stmts := .terminalArgs kind args :: rest }
        beforeState beforeLocals)
    (hArgsSafe : AllocationInteractionSafety.ExprSeqSafe contract args source)
    (hTerminalSafe :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result =>
              Simulation.MemorySafety.TerminalMemorySafe
                contract kind result.2)
        (Functions.InteractionSemantics.ExprSeq.openEval args source))
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    ∃ afterState afterLocals headCode,
      ∃ tail :
        CoreCursor root scope live { stmts := rest }
          afterState afterLocals,
        cursor.compiled = headCode ++ tail.compiled ∧
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState afterLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth target)
            (Functions.InteractionSemantics.Stmt.openRun
              program sourceCtx sourceFuel (.terminalArgs kind args) source)
            (Expressions.InteractionSemantics.Block.openRun
              expressions (targetExtra + 3) { stmts := headCode } target) ∧
          ExactTail cursor tail := by
  obtain
      ⟨afterState, afterLocals, headLower, headCode, tail,
        _hPlanning, hPlan, hFinalState, hFinalLocals, hLower, hCompile,
        _hLowered, hCompiled, hScoped⟩ := cursor.cons
  have hArgsScoped : Functions.Scope.ExprSeqScoped live args := by
    simpa [Functions.Scope.Stmt.Scoped] using hScoped
  have hSemantic :=
    AllocationInteractionTerminal.terminalArgs_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hArgsSafe hTerminalSafe hArgsScoped hLower hCompile
      hBoundary.semantic.invariant
  have hResource :=
    AllocationInteractionTerminalResource.terminalArgs_of_lower_compile
      (sourceProgram := program) (sourceCtx := sourceCtx)
      (targetProgram := expressions)
      (sourceFuel := sourceFuel) (targetExtra := targetExtra)
      hBoundary.configEq hArgsSafe hTerminalSafe hArgsScoped hLower hCompile
      hBoundary.semantic.invariant hBoundary.ready
  exact
    ⟨afterState, afterLocals, headCode, tail, hCompiled,
      Simulation.Interaction.Rel.inter hSemantic hResource,
      ⟨hPlan, hFinalState, hFinalLocals, ⟨headCode, hCompiled⟩⟩⟩

namespace CursorRuntimeAt

/-- Recursive expression statement with semantic and allocator preservation. -/
theorem expr
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {expr : Functions.Expr 0} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .expr expr :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract expr source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .expr expr :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.expr_runtime_head cursor
      (sourceFuel := childFuel) (targetExtra := headExtra)
      hSafe hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.expr expr) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.expr expr) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement := by
              have hAfterMatches := hInvariant.compiler.mode_matches
              rw [hExact.plan] at hAfterMatches
              have hModeEq := hSame.eq_of_matches
                hBoundary.semantic.invariant.compiler.mode_matches
                hAfterMatches
              subst tailMode
              rw [hExact.plan]
              exact
                (hBoundary.controlAgreement.transport_context
                  (Functions.Source.Ctx.SameControl.refl sourceCtx)
                  (hExact.locals_sameControl cursor tail)).transport_target
                    hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive assignment with semantic and allocator preservation. -/
theorem assign
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .assign name value :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .assign name value :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.assign_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSafe hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.assign name value) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.assign name value) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement := by
              have hAfterMatches := hInvariant.compiler.mode_matches
              rw [hExact.plan] at hAfterMatches
              have hModeEq := hSame.eq_of_matches
                hBoundary.semantic.invariant.compiler.mode_matches
                hAfterMatches
              subst tailMode
              rw [hExact.plan]
              exact
                (hBoundary.controlAgreement.transport_context
                  (Functions.Source.Ctx.SameControl.refl sourceCtx)
                  (hExact.locals_sameControl cursor tail)).transport_target
                    hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive declaration with semantic and allocator preservation. -/
theorem let_
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {name : Functions.Name} {value : Functions.Expr 1}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .let_ name value :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSafe : AllocationInteractionSafety.ExprSafe contract value source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .let_ name value :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope (name :: live) { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode { sourceCtx with scope := name :: sourceCtx.scope }
              sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program
                { sourceCtx with scope := name :: sourceCtx.scope }
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions) tailMode
              { sourceCtx with scope := name :: sourceCtx.scope }
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 2
  let nextCtx := { sourceCtx with scope := name :: sourceCtx.scope }
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hHeadFuel : headExtra + 2 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hPlacement, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.let_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSafe hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns (name :: live) frameBase mode sourceCtx
          nextCtx config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.let_ name value) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [nextCtx, hHeadFuel] using hHead
  have hMidCtx :
      nextCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.let_ name value) } := by
    cases sourceCtx
    have hScope := hBoundary.semantic.sourceScope
    simp only at hScope
    cases hScope
    rfl
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := by
                  simp [nextCtx, hBoundary.semantic.sourceScope]
                control :=
                  (hBoundary.semantic.control.mono
                    (fun other hOther => by simp [hOther])).scopeUpdate
                    (name :: sourceCtx.scope)
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement := by
              have hAfterMatches := hInvariant.compiler.mode_matches
              rw [hExact.plan] at hAfterMatches
              have hSourceControl :
                  Functions.Source.Ctx.SameControl sourceCtx nextCtx := by
                simpa [nextCtx] using
                  Functions.Source.Ctx.SameControl.scopeUpdate sourceCtx
                    (name :: sourceCtx.scope)
              have hLocalsControl := hExact.locals_sameControl cursor tail
              cases hPlacement with
              | stack slot planDepth hSlot hStack hLocation hOrder =>
                  have hExpectedMatches :=
                    hBoundary.semantic.invariant.compiler.mode_matches
                      |>.after_stack_declaration hOrder
                  have hExpectedSame :
                      SameFrame mode.afterStackDeclaration tailMode :=
                    (SameFrame.afterStackDeclaration mode).symm.trans hSame
                  have hModeEq := hExpectedSame.eq_of_matches
                    hExpectedMatches hAfterMatches
                  subst tailMode
                  rw [hExact.plan]
                  exact
                    (hBoundary.controlAgreement.after_stack_declaration
                      hSourceControl hLocalsControl rfl hOrder)
                      |>.transport_target hReturns
              | scratch slot hSlot hStack hLocation hOrder =>
                  have hExpectedMatches :=
                    hBoundary.semantic.invariant.compiler.mode_matches
                      |>.after_scratch_declaration hOrder
                  have hModeEq := hSame.eq_of_matches
                    hExpectedMatches hAfterMatches
                  subst tailMode
                  rw [hExact.plan]
                  exact
                    (hBoundary.controlAgreement.after_scratch_declaration
                      hSourceControl hLocalsControl hOrder)
                      |>.transport_target hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive lexical block with exact cleanup and allocator preservation. -/
theorem block
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {body : Functions.Block} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .block body :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hTargetReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .block body :: rest } source))
    (hBodyForward :
      ∀ (bodyCursor :
          CoreCursor root (.lexical scope cursor.planning.nextScope)
            live body beforeState beforeLocals)
        (bodyExtra : Nat),
        AllocationInteractionTargetFuel.Reserve bodyCursor bodyExtra →
          Boundary bodyCursor contract globalFrameWords config allocatorDepth
            frameBase mode sourceCtx source target →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program sourceCtx
              (sourceFuel - 1) body source) →
          CursorRuntimeAt bodyCursor contract config allocatorDepth frameBase
            (sourceFuel - 1) bodyExtra mode sourceCtx source target)
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  obtain
      ⟨afterState, headCode, tail, targetBlock, bodyCursor,
        hCompiled, hHeadCode, hFinish, hAfterEnv, hAfterLayout,
        _hTransport, hExact⟩ := cursor.blockCursors
  have hBodyAgree :
      PlanAgreesOn bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  have hBodyInvariant :=
    hBoundary.semantic.invariant.transport_plan
      hBodyAgree.symm bodyCursor.planWF
  have hBodyBoundary :
      Boundary bodyCursor contract globalFrameWords config allocatorDepth
        frameBase mode sourceCtx source target :=
    { semantic :=
        { invariant := hBodyInvariant
          sourceScope := hBoundary.semantic.sourceScope
          control := hBoundary.semantic.control
          capacity := hBoundary.semantic.capacity }
      controlAgreement :=
        hBoundary.controlAgreement.transport_plan hBodyAgree.symm
      configEq := hBoundary.configEq
      ready := hBoundary.ready
      owned := hBoundary.owned
      budget := hBoundary.budget }
  have hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.block body) source) := by
    have hWhole :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            (childFuel + 1) { stmts := .block body :: rest } source) := by
      rw [hFuel]
      exact hSuccessful
    have hHead :=
      Functions.InteractionSemantics.Block.successful_openRun_cons_head
        hWhole
    simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead
  have hBodySuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          childFuel body source) := by
    rw [Functions.InteractionSemantics.Stmt.openRun_block] at hHeadSuccess
    exact Simulation.Interaction.Successful.bind_left hHeadSuccess
  obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
    AllocationInteractionCleanup.Plain.finishScoped_shape hFinish
  have hHeadLength :
      headCode.length = bodyCursor.compiled.length + 1 := by
    rw [hHeadCode, hTargetShape, List.length_append]
    simp
  have hCompiledLength := congrArg List.length hCompiled
  simp only [List.length_append] at hCompiledLength
  let bodyBase :=
    bodyCursor.compiled.length + callStride expressions * (childFuel + 1)
  let bodyExtra := totalFuel - bodyBase
  have hBodyBase : bodyBase ≤ totalFuel := by
    simp only [totalFuel]
    rw [← hFuel]
    simp [bodyBase, targetBudget, callStride, Nat.mul_succ]
    omega
  have hBodyBudget :
      targetBudget bodyCursor childFuel bodyExtra = totalFuel := by
    calc
      targetBudget bodyCursor childFuel bodyExtra = bodyExtra + bodyBase := by
        simp [targetBudget, bodyBase]
        omega
      _ = totalFuel := Nat.sub_add_cancel hBodyBase
  have hBodyNestedSize :
      Expressions.TargetFuel.stmtListNestedSize bodyCursor.compiled ≤
        Expressions.TargetFuel.stmtListNestedSize cursor.compiled := by
    rw [hCompiled,
      Expressions.TargetFuel.stmtListNestedSize_append,
      hHeadCode, hTargetShape,
      Expressions.TargetFuel.stmtListNestedSize_append]
    omega
  have hStrideFuel :
      callStride expressions * (sourceFuel + 1) =
        callStride expressions * (childFuel + 1) +
          callStride expressions := by
    rw [← hFuel, show childFuel + 1 + 1 = (childFuel + 1) + 1 by rfl,
      Nat.mul_add]
    simp
  have hExtraLe : targetExtra ≤ bodyExtra := by
    unfold bodyExtra bodyBase totalFuel targetBudget
    rw [hStrideFuel]
    omega
  have hBodyReserve :
      AllocationInteractionTargetFuel.Reserve bodyCursor bodyExtra := by
    unfold AllocationInteractionTargetFuel.Reserve at hTargetReserve ⊢
    change
      Expressions.TargetFuel.stmtListNestedSize cursor.compiled ≤ targetExtra
      at hTargetReserve
    change
      Expressions.TargetFuel.stmtListNestedSize bodyCursor.compiled ≤ bodyExtra
    omega
  have hBodyRecursive :=
    hBodyForward bodyCursor bodyExtra hBodyReserve hBodyBoundary
      (by simpa [childFuel] using hBodySuccess)
  have hBodyRel :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx bodyCursor.finalState
          bodyCursor.finalLocals bodyCursor.plan root.returns
          (Functions.Scope.Block.outEnv live body) frameBase mode sourceCtx
          { sourceCtx with scope := Functions.Scope.Block.outEnv live body }
          config allocatorDepth target)
        (Functions.InteractionSemantics.Block.openRun
          program sourceCtx childFuel body source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := bodyCursor.compiled } target) := by
    simpa [CursorRuntimeAt, childFuel, hBodyBudget] using hBodyRecursive
  have hAfterInvariant :=
    hBoundary.semantic.invariant.transport_state hAfterEnv hAfterLayout
  have hExtends :
      AllocationLowering.StateExtends live beforeState bodyCursor.finalState :=
    AllocationLowering.lowerBlockOpen_stateExtends
      bodyCursor.sourceScoped bodyCursor.lower
  have hExtendsAfter :
      AllocationLowering.StateExtends live afterState bodyCursor.finalState := by
    rcases hExtends with ⟨dropped, hLayout, hFresh, hSlots⟩
    refine ⟨dropped, ?_, hFresh, ?_⟩
    · rw [hLayout, hAfterLayout]
    · intro name hLive
      exact (hSlots name hLive).trans
        (congrArg (AllocationSupport.lookupSlot? name) hAfterEnv.symm)
  have hCleanupFuel :
      2 ≤ totalFuel - bodyCursor.compiled.length := by
    simp [totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  have hSemantic :=
    AllocationInteractionControl.block_of_components
      (bodyLive := Functions.Scope.Block.outEnv live body)
      hBoundary.semantic.sourceScope rfl rfl hBoundary.semantic.control
      hAfterInvariant hExtendsAfter hBodyAgree hFinish hCleanupFuel
      (Simulation.Interaction.Rel.mono hBodyRel
        (fun _ _ hDone => hDone.1))
  have hResource :=
    AllocationInteractionControlResource.block_of_components
      hBoundary.semantic.sourceScope hFinish hCleanupFuel hBodyRel
  have hHead :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.block body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          targetBlock target) :=
    Simulation.Interaction.Rel.inter hSemantic hResource
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.block body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    cases targetBlock
    simpa [hHeadCode] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.block body) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive conditional with selected-body allocator preservation. -/
theorem if_
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {cond : Functions.Expr 1} {body : Functions.Block}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .if_ cond body :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 1 < sourceFuel)
    (hTargetReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hCondSafe : AllocationInteractionSafety.ExprSafe contract cond source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .if_ cond body :: rest } source))
    (hBodyForward :
      ∀ (bodyCursor :
          CoreCursor root (.lexical scope cursor.planning.nextScope)
            live body beforeState beforeLocals)
        {sourceAfter targetAfter},
        targetBudget bodyCursor (sourceFuel - 2)
              (AllocationInteractionTargetFuel.stmtListNestedSize
                bodyCursor.compiled) ≤
            targetBudget cursor sourceFuel targetExtra - 2 →
          Boundary bodyCursor contract globalFrameWords config allocatorDepth
            frameBase mode sourceCtx sourceAfter targetAfter →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program sourceCtx
              (sourceFuel - 2) body sourceAfter) →
          2 ≤
              (targetBudget cursor sourceFuel targetExtra - 2) -
                bodyCursor.compiled.length ∧
            Simulation.Interaction.Rel
              (RuntimeResultRel contract root.lowerCtx
                bodyCursor.finalState bodyCursor.finalLocals bodyCursor.plan
                root.returns (Functions.Scope.Block.outEnv live body)
                frameBase mode sourceCtx
                { sourceCtx with
                  scope := Functions.Scope.Block.outEnv live body }
                config allocatorDepth targetAfter)
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 2) body sourceAfter)
              (Expressions.InteractionSemantics.Block.openRun expressions
                (targetBudget cursor sourceFuel targetExtra - 2)
                { stmts := bodyCursor.compiled } targetAfter))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let bodyFuel := sourceFuel - 2
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let targetBodyFuel := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hBodyFuel : bodyFuel + 1 = childFuel := by
    simp [bodyFuel, childFuel]
    omega
  have hTargetFuel : targetBodyFuel + 2 = totalFuel := by
    simp [targetBodyFuel, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  have hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.if_ cond body) source) := by
    have hWhole :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            (childFuel + 1) { stmts := .if_ cond body :: rest } source) := by
      rw [hFuel]
      exact hSuccessful
    have hHead :=
      Functions.InteractionSemantics.Block.successful_openRun_cons_head hWhole
    simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead
  obtain
      ⟨afterState, headLower, headCode, tail, loweredCond, condCode,
        targetBody, bodyCursor, hCompiled, _hLower, _hCompile,
        hHeadCode, hLowerCond, hCompileCond, hFinish, hAfterEnv,
        hAfterLayout, hCondScoped, hExact⟩ := cursor.ifCursors
  have hBodyAgree : PlanAgreesOn bodyCursor.plan cursor.plan live :=
    bodyCursor.planAgreesOn cursor rfl
  have hAfterInvariant :=
    hBoundary.semantic.invariant.transport_state hAfterEnv hAfterLayout
  have hCond :=
    AllocationInteractionExpressionResource.forwardCondition
      (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
        contract)
      hBoundary.configEq hCondSafe hBoundary.semantic.invariant.compiler
      hCondScoped hLowerCond hCompileCond hBoundary.semantic.invariant.state
      hBoundary.ready
  have hVars :=
    Locals.InteractionStatePreservation.expr_openEvalCondition_vars
      cond source
  have hExtendsBefore :
      AllocationLowering.StateExtends live beforeState bodyCursor.finalState :=
    AllocationLowering.lowerBlockOpen_stateExtends
      bodyCursor.sourceScoped bodyCursor.lower
  have hExtendsAfter :
      AllocationLowering.StateExtends live afterState bodyCursor.finalState := by
    rcases hExtendsBefore with ⟨dropped, hLayout, hFresh, hSlots⟩
    refine ⟨dropped, ?_, hFresh, ?_⟩
    · rw [hLayout, hAfterLayout]
    · intro name hLive
      exact (hSlots name hLive).trans
        (congrArg (AllocationSupport.lookupSlot? name) hAfterEnv.symm)
  have hBodyWithinTarget :
      Expressions.TargetFuel.stmtListSize bodyCursor.compiled ≤
        Expressions.TargetFuel.stmtListSize targetBody.stmts := by
    rcases Locals.finishScopedOrAbrupt_components hFinish with
      hRegular | ⟨_hNone, _hExit, hShape⟩
    · obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
        AllocationInteractionCleanup.Plain.finishScoped_shape hRegular
      rw [hTargetShape, Expressions.TargetFuel.stmtListSize_append]
      omega
    · subst targetBody
      exact Nat.le_refl _
  have hTargetBlockSize :
      Expressions.TargetFuel.blockSize targetBody =
        Expressions.TargetFuel.stmtListSize targetBody.stmts := by
    cases targetBody
    rfl
  have hBodyWithinParent :
      Expressions.TargetFuel.stmtListSize bodyCursor.compiled ≤
        Expressions.TargetFuel.stmtListNestedSize
          cursor.compiled := by
    rw [hCompiled,
      Expressions.TargetFuel.stmtListNestedSize_append,
      hHeadCode]
    simp only [AllocationInteractionTargetFuel.stmtListNestedSize,
      AllocationInteractionTargetFuel.stmtNestedSize,
      Expressions.TargetFuel.stmtListNestedSize,
      Expressions.TargetFuel.stmtNestedSize]
    rw [hTargetBlockSize]
    omega
  have hFuelGap : sourceFuel + 1 = (bodyFuel + 1) + 2 := by
    simp [bodyFuel]
    omega
  have hStrideFuel :
      callStride expressions * (sourceFuel + 1) =
        callStride expressions * (bodyFuel + 1) +
          callStride expressions * 2 := by
    rw [hFuelGap, Nat.mul_add]
  have hBodySizeEq :=
    Expressions.TargetFuel.stmtListSize_eq bodyCursor.compiled
  have hBodyTargetCapacity :
      targetBudget bodyCursor bodyFuel
            (Expressions.TargetFuel.stmtListNestedSize
              bodyCursor.compiled) ≤
        targetBodyFuel := by
    unfold AllocationInteractionTargetFuel.Reserve at hTargetReserve
    change
      Expressions.TargetFuel.stmtListNestedSize cursor.compiled ≤ targetExtra
      at hTargetReserve
    unfold targetBodyFuel totalFuel targetBudget
    rw [hStrideFuel]
    have hStride := eight_le_callStride expressions
    omega
  have hTrue :
      ∀ {sourceAfter targetAfter},
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState beforeLocals cursor.plan live frameBase mode
            sourceAfter targetAfter →
          AllocatorReady config allocatorDepth targetAfter →
          targetAfter.returns = target.returns →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              bodyFuel (.block body) sourceAfter) →
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState beforeLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth targetAfter)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              bodyFuel (.block body) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel targetBody targetAfter) := by
    intro sourceAfter targetAfter hAfter hReadyAfter hReturns
      hSelectedSuccess
    have hBefore :=
      hAfter.transport_state hAfterEnv.symm hAfterLayout.symm
    have hNestedInvariant :=
      hBefore.transport_plan hBodyAgree.symm bodyCursor.planWF
    have hNestedBoundary :
        Boundary bodyCursor contract globalFrameWords config allocatorDepth
          frameBase mode sourceCtx sourceAfter targetAfter :=
      { semantic :=
          { invariant := hNestedInvariant
            sourceScope := hBoundary.semantic.sourceScope
            control := hBoundary.semantic.control
            capacity := hBoundary.semantic.capacity }
        controlAgreement :=
          (hBoundary.controlAgreement.transport_plan hBodyAgree.symm)
            |>.transport_target hReturns
        configEq := hBoundary.configEq
        ready := hReadyAfter
        owned := hBoundary.owned
        budget := hBoundary.budget }
    have hBodySuccess :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            bodyFuel body sourceAfter) := by
      rw [Functions.InteractionSemantics.Stmt.openRun_block]
        at hSelectedSuccess
      exact Simulation.Interaction.Successful.bind_left hSelectedSuccess
    obtain ⟨hCleanupFuel, hBody⟩ :=
      hBodyForward bodyCursor hBodyTargetCapacity hNestedBoundary
        (by simpa [bodyFuel] using hBodySuccess)
    have hSemantic :=
      AllocationInteractionControl.block_of_components_or_abrupt
        (bodyLive := Functions.Scope.Block.outEnv live body)
        hBoundary.semantic.sourceScope rfl rfl hBoundary.semantic.control
        hAfter bodyCursor.lower hExtendsAfter hBodyAgree hFinish hCleanupFuel
        (Simulation.Interaction.Rel.mono hBody
          (fun _ _ hDone => hDone.1))
    have hResource :=
      AllocationInteractionControlResource.block_of_components_or_abrupt
        hBoundary.semantic.sourceScope bodyCursor.lower hFinish hCleanupFuel
        hBody
    exact Simulation.Interaction.Rel.inter hSemantic hResource
  have hHead :=
    AllocationInteractionControlResource.if_of_components
      (sourceBodyFuel := bodyFuel) (targetBodyFuel := targetBodyFuel)
      hAfterInvariant hCond hVars
      (by simpa [bodyFuel, hBodyFuel] using hHeadSuccess) hTrue
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.if_ cond body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hBodyFuel, hTargetFuel, hHeadCode] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.if_ cond body) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive switch with exact selected-branch allocator preservation. -/
theorem switch
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {scrutinee : Functions.Expr 1}
    {cases : List (Word × Functions.Block)}
    {defaultBody : Option Functions.Block}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live
        { stmts := .switch scrutinee cases defaultBody :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 1 < sourceFuel)
    (hTargetReserve :
      AllocationInteractionTargetFuel.Reserve cursor targetExtra)
    (hScrutineeSafe :
      AllocationInteractionSafety.ExprSafe contract scrutinee source)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel
          { stmts := .switch scrutinee cases defaultBody :: rest } source))
    (hBodyForward :
      ∀ {value} {selected : Functions.Block}
        {selectedStart : AllocationLowering.State}
        {selectedPlanning : AllocationSupport.PlanningState}
        (hSelect :
          Functions.Source.Switch.select value cases defaultBody =
            some selected)
        (bodyCursor :
          CoreCursor root (.lexical scope selectedPlanning.nextScope)
            live selected selectedStart beforeLocals)
        {sourceAfter targetAfter},
        targetBudget bodyCursor (sourceFuel - 2)
              (AllocationInteractionTargetFuel.stmtListNestedSize
                bodyCursor.compiled) ≤
            targetBudget cursor sourceFuel targetExtra - 2 →
          Boundary bodyCursor contract globalFrameWords config allocatorDepth
            frameBase mode sourceCtx sourceAfter targetAfter →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program sourceCtx
              (sourceFuel - 2) selected sourceAfter) →
          2 ≤
              (targetBudget cursor sourceFuel targetExtra - 2) -
                bodyCursor.compiled.length ∧
            Simulation.Interaction.Rel
              (RuntimeResultRel contract root.lowerCtx
                bodyCursor.finalState bodyCursor.finalLocals bodyCursor.plan
                root.returns (Functions.Scope.Block.outEnv live selected)
                frameBase mode sourceCtx
                { sourceCtx with
                  scope := Functions.Scope.Block.outEnv live selected }
                config allocatorDepth targetAfter)
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 2) selected sourceAfter)
              (Expressions.InteractionSemantics.Block.openRun expressions
                (targetBudget cursor sourceFuel targetExtra - 2)
                { stmts := bodyCursor.compiled } targetAfter))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let bodyFuel := sourceFuel - 2
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let targetBodyFuel := totalFuel - 2
  have hFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hBodyFuel : bodyFuel + 1 = childFuel := by
    simp [bodyFuel, childFuel]
    omega
  have hTargetFuel : targetBodyFuel + 2 = totalFuel := by
    simp [targetBodyFuel, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  have hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.switch scrutinee cases defaultBody) source) := by
    have hWhole :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            (childFuel + 1)
            { stmts := .switch scrutinee cases defaultBody :: rest }
            source) := by
      rw [hFuel]
      exact hSuccessful
    have hHead :=
      Functions.InteractionSemantics.Block.successful_openRun_cons_head hWhole
    simpa [Functions.InteractionSemantics.Stmt.openRun] using hHead
  obtain
      ⟨afterState, headLower, headCode, tail, loweredScrutinee,
        loweredCases, afterCases, loweredDefault, scrutineeCode,
        compiledCases, compiledDefault, components⟩ :=
    cursor.switchCursors
  have hAfterInvariant :=
    hBoundary.semantic.invariant.transport_state
      components.afterEnv components.afterLayout
  have hScrutinee :=
    AllocationInteractionExpressionResource.forwardOne
      (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
        contract)
      hBoundary.configEq hScrutineeSafe
      hBoundary.semantic.invariant.compiler components.scrutineeScoped
      components.lowerScrutinee components.compileScrutinee
      hBoundary.semantic.invariant.state hBoundary.ready
  have hVars :=
    Locals.InteractionStatePreservation.expr_openEvalOne_vars
      scrutinee source
  have hSelection :
      ∀ value,
        AllocationInteractionControl.SwitchSelection cases defaultBody
          compiledCases compiledDefault value := by
    intro value
    have hCompiledSelection :=
      Locals.InteractionPreservation.Stmt.SwitchCompile.selectedRel_of_compile
        beforeLocals value components.compileCases components.compileDefault
    cases hSourceSelect :
        Functions.Source.Switch.select value cases defaultBody with
    | none =>
        have hLowerSelect :=
          AllocationLowering.lowerSwitch_select_none components.lowerCases
            components.lowerDefault hSourceSelect
        rw [hLowerSelect] at hCompiledSelection
        exact .none hSourceSelect hCompiledSelection.none_target
    | some selected =>
        obtain
            ⟨selectedLowered, selectedStart, selectedFinal,
              hLowerSelect, _hLowerBody, _hSelectedEnv,
              _hSelectedLayout⟩ :=
          AllocationLowering.lowerSwitch_select_some
            components.lowerCases components.lowerDefault hSourceSelect
        rw [hLowerSelect] at hCompiledSelection
        obtain
            ⟨selectedTarget, _selectedCode, _selectedLocals,
              hTargetSelect, _hCompileSelected, _hFinishSelected⟩ :=
          hCompiledSelection.some_parts
        exact .some selected selectedTarget hSourceSelect hTargetSelect
  have hSelected :
      ∀ {value selected selectedTarget sourceAfter targetAfter},
        Functions.Source.Switch.select value cases defaultBody =
            some selected →
        Expressions.EffectSemantics.Switch.select value compiledCases
            compiledDefault = some selectedTarget →
        AllocationContext.ActivationInvariant contract root.lowerCtx
            afterState beforeLocals cursor.plan live frameBase mode
            sourceAfter targetAfter →
        AllocatorReady config allocatorDepth targetAfter →
        targetAfter.returns = target.returns →
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
            bodyFuel (.block selected) sourceAfter) →
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx afterState beforeLocals
              cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
              config allocatorDepth targetAfter)
            (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
              bodyFuel (.block selected) sourceAfter)
            (Expressions.InteractionSemantics.Block.openRun expressions
              targetBodyFuel selectedTarget targetAfter) := by
    intro value selected selectedTarget sourceAfter targetAfter
      hSourceSelect hTargetSelect hAfter hReadyAfter hReturns
      hSelectedSuccess
    obtain
        ⟨selectedAfter, selectedHeadLower, selectedHeadCode, selectedTail,
          selectedScrutineeCode, selectedCases, selectedDefault,
          selectedStart, selectedPlanning, actualTarget, bodyCursor,
          _hSelectedCompiled, hSelectedLower, hSelectedCompile,
          hSelectedHeadCode, hActualTargetSelect, hFinish,
          hSelectedEnv, hSelectedLayout, _hSelectedAfterEnv,
          _hSelectedAfterLayout, _hSelectedScrutineeScoped,
          _hSelectedScoped, _hSelectedExact⟩ :=
      cursor.switchSelectedCursors hSourceSelect
    rw [components.lower] at hSelectedLower
    cases hSelectedLower
    rw [components.compile] at hSelectedCompile
    cases hSelectedCompile
    rw [components.codeHead] at hSelectedHeadCode
    cases hSelectedHeadCode
    rw [hTargetSelect] at hActualTargetSelect
    cases hActualTargetSelect
    have hBefore :=
      hAfter.transport_state components.afterEnv.symm
        components.afterLayout.symm
    have hSelectedInvariant :=
      hBefore.transport_state hSelectedEnv hSelectedLayout
    have hBodyAgree : PlanAgreesOn bodyCursor.plan cursor.plan live :=
      bodyCursor.planAgreesOn cursor hSelectedEnv
    have hNestedInvariant :=
      hSelectedInvariant.transport_plan hBodyAgree.symm bodyCursor.planWF
    have hNestedBoundary :
        Boundary bodyCursor contract globalFrameWords config allocatorDepth
          frameBase mode sourceCtx sourceAfter targetAfter :=
      { semantic :=
          { invariant := hNestedInvariant
            sourceScope := hBoundary.semantic.sourceScope
            control := hBoundary.semantic.control
            capacity := hBoundary.semantic.capacity }
        controlAgreement :=
          (hBoundary.controlAgreement.transport_plan hBodyAgree.symm)
            |>.transport_target hReturns
        configEq := hBoundary.configEq
        ready := hReadyAfter
        owned := hBoundary.owned
        budget := hBoundary.budget }
    have hExtendsSelected :
        AllocationLowering.StateExtends live selectedStart
          bodyCursor.finalState :=
      AllocationLowering.lowerBlockOpen_stateExtends
        bodyCursor.sourceScoped bodyCursor.lower
    have hExtendsAfter :
        AllocationLowering.StateExtends live afterState
          bodyCursor.finalState := by
      rcases hExtendsSelected with ⟨dropped, hLayout, hFresh, hSlots⟩
      refine ⟨dropped, ?_, hFresh, ?_⟩
      · rw [hLayout, hSelectedLayout, components.afterLayout]
      · intro name hLive
        exact (hSlots name hLive).trans
          (congrArg (AllocationSupport.lookupSlot? name)
            (hSelectedEnv.trans components.afterEnv.symm))
    have hBodySuccess :
        Simulation.Interaction.Successful
          (Functions.InteractionSemantics.Block.openRun program sourceCtx
            bodyFuel selected sourceAfter) := by
      rw [Functions.InteractionSemantics.Stmt.openRun_block]
        at hSelectedSuccess
      exact Simulation.Interaction.Successful.bind_left hSelectedSuccess
    obtain ⟨cleanup, _hCleanup, hTargetShape⟩ :=
      AllocationInteractionCleanup.Plain.finishScoped_shape hFinish
    have hActualTargetSize :
        Expressions.TargetFuel.blockSize selectedTarget =
          Expressions.TargetFuel.stmtListSize selectedTarget.stmts := by
      cases selectedTarget
      rfl
    have hBodyWithinTarget :
        Expressions.TargetFuel.stmtListSize bodyCursor.compiled ≤
          Expressions.TargetFuel.blockSize selectedTarget := by
      rw [hActualTargetSize, hTargetShape,
        Expressions.TargetFuel.stmtListSize_append]
      omega
    have hTargetWithinSwitch :
        Expressions.TargetFuel.blockSize selectedTarget ≤
          Expressions.TargetFuel.caseListSize compiledCases +
            Expressions.TargetFuel.defaultSize compiledDefault :=
      Expressions.TargetFuel.selected_block_size_le hTargetSelect
    have hSwitchWithinParent :
        Expressions.TargetFuel.caseListSize compiledCases +
            Expressions.TargetFuel.defaultSize compiledDefault ≤
          Expressions.TargetFuel.stmtListNestedSize
            cursor.compiled := by
      rw [components.compiled,
        Expressions.TargetFuel.stmtListNestedSize_append,
        components.codeHead]
      simp only [AllocationInteractionTargetFuel.stmtListNestedSize,
        AllocationInteractionTargetFuel.stmtNestedSize,
        Expressions.TargetFuel.stmtListNestedSize,
        Expressions.TargetFuel.stmtNestedSize,
        Expressions.TargetFuel.caseListSize,
        Expressions.TargetFuel.defaultSize]
      omega
    have hBodyWithinParent :
        AllocationInteractionTargetFuel.stmtListSize bodyCursor.compiled ≤
          AllocationInteractionTargetFuel.stmtListNestedSize
            cursor.compiled :=
      hBodyWithinTarget.trans (hTargetWithinSwitch.trans hSwitchWithinParent)
    have hFuelGap : sourceFuel + 1 = (bodyFuel + 1) + 2 := by
      simp [bodyFuel]
      omega
    have hStrideFuel :
        callStride expressions * (sourceFuel + 1) =
          callStride expressions * (bodyFuel + 1) +
            callStride expressions * 2 := by
      rw [hFuelGap, Nat.mul_add]
    have hBodySizeEq :=
      AllocationInteractionTargetFuel.stmtListSize_eq
        bodyCursor.compiled
    have hBodyTargetCapacity :
        targetBudget bodyCursor bodyFuel
              (AllocationInteractionTargetFuel.stmtListNestedSize
                bodyCursor.compiled) ≤
          targetBodyFuel := by
      unfold AllocationInteractionTargetFuel.Reserve at hTargetReserve
      unfold targetBodyFuel totalFuel targetBudget
      rw [hStrideFuel]
      have hStride := eight_le_callStride expressions
      omega
    obtain ⟨hCleanupFuel, hBody⟩ :=
      hBodyForward hSourceSelect bodyCursor hBodyTargetCapacity hNestedBoundary
        (by simpa [bodyFuel] using hBodySuccess)
    have hSemantic :=
      AllocationInteractionControl.block_of_components
        (bodyLive := Functions.Scope.Block.outEnv live selected)
        hBoundary.semantic.sourceScope rfl rfl hBoundary.semantic.control
        hAfter hExtendsAfter hBodyAgree hFinish hCleanupFuel
        (Simulation.Interaction.Rel.mono hBody
          (fun _ _ hDone => hDone.1))
    have hResource :=
      AllocationInteractionControlResource.block_of_components
        hBoundary.semantic.sourceScope hFinish hCleanupFuel hBody
    exact Simulation.Interaction.Rel.inter hSemantic hResource
  have hHead :=
    AllocationInteractionControlResource.switch_of_components
      (sourceBodyFuel := bodyFuel) (targetBodyFuel := targetBodyFuel)
      hAfterInvariant hScrutinee hVars
      (by simpa [bodyFuel, hBodyFuel] using hHeadSuccess)
      hSelection hSelected
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState beforeLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.switch scrutinee cases defaultBody) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hBodyFuel, hTargetFuel, components.codeHead] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live
            (.switch scrutinee cases defaultBody) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail components.exactTail
      components.compiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail components.exactTail
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                components.exactTail
                (by simp [Functions.Scope.Stmt.outEnv]) hInvariant hSame
                (Functions.Source.Ctx.SameControl.refl sourceCtx) hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive `for` with one shared semantic/resource loop induction. -/
theorem for_
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {init : Functions.Block} {cond : Functions.Expr 1}
    {post body : Functions.Block} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live
        { stmts := .for_ init cond post body :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 2 < sourceFuel)
    (hCondSafe :
      ∀ sourceState,
        AllocationInteractionRelation.LiveDefined
            cursor.forArtifact.loopLive sourceState →
        Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Expr.openEvalCondition
              cond sourceState) →
        AllocationInteractionSafety.ExprSafe contract cond sourceState)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hFuelBudget :
      AllocationInteractionFrame.Budget config (allocatorDepth + sourceFuel))
    (hHeadSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (sourceFuel - 1) (.for_ init cond post body) source))
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel
          { stmts := .for_ init cond post body :: rest } source))
    (hRecursive :
      RecursiveOpenRuntime (compilation := compilation)
        contract globalFrameWords sourceFuel)
    (hCapacity :
      ForFuelCapacity cursor.forArtifact (sourceFuel - 2)
        ((targetBudget cursor sourceFuel targetExtra - 2) -
          (sourceFuel - 2)))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState beforeLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth
              frameBase tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx sourceMid
              targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  classical
  let components := cursor.forArtifact
  let childFuel := sourceFuel - 1
  let loopFuel := sourceFuel - 2
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let nestedFuel := totalFuel - 2
  let slack := nestedFuel - loopFuel
  have hChildFuel : childFuel + 1 = sourceFuel := by
    simp [childFuel]
    omega
  have hLoopFuel : loopFuel + 1 = childFuel := by
    simp [loopFuel, childFuel]
    omega
  have hSourceLeTotal : sourceFuel ≤ totalFuel := by
    have hStride : 1 ≤ callStride expressions := by
      exact le_trans (by omega) (eight_le_callStride expressions)
    have hMul :
        sourceFuel ≤ callStride expressions * sourceFuel := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right sourceFuel hStride
    simp [totalFuel, targetBudget, Nat.mul_succ]
    omega
  have hNestedFuel : loopFuel + slack = nestedFuel := by
    simp only [loopFuel, slack, nestedFuel]
    omega
  have hTotalFuel : nestedFuel + 2 = totalFuel := by
    simp only [nestedFuel]
    omega
  change ForFuelCapacity components loopFuel slack at hCapacity
  let initCtx := sourceCtx.withoutLoopControl
  let loopCtx : Functions.Source.Ctx :=
    { initCtx with scope := components.loopLive }
  let postCtx := loopCtx.withoutLoopControl
  let bodyCtx :=
    loopCtx.withLoopControl components.loopLive components.loopLive
  have hOuterSubset :
      ∀ name, name ∈ live → name ∈ components.loopLive := by
    rw [components.loopLive_eq]
    intro name hName
    exact Functions.Scope.Block.mem_outEnv hName
  have hOuterControl :
      AllocationInteractionStatement.ControlScopesWithin root.returns
        components.loopLive loopCtx := by
    have hLiveControl := hBoundary.semantic.control.mono hOuterSubset
    simpa [loopCtx, initCtx] using
      hLiveControl.withoutLoopControl.scopeUpdate components.loopLive
  have hInitSuccess :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program initCtx
          loopFuel init source) := by
    have hSuccess := hHeadSuccess
    have hFuelEq : loopFuel + 1 = sourceFuel - 1 := by
      simpa [childFuel] using hLoopFuel
    rw [← hFuelEq] at hSuccess
    unfold Functions.InteractionSemantics.Stmt.openRun
      Functions.Source.Canonical.Stmt.run at hSuccess
    simp only [Functions.Source.Effectful.Control.Stmt.run] at hSuccess
    have hInitDone := Simulation.Interaction.Successful.bind_inv hSuccess
    apply Simulation.Interaction.AllDone.mono hInitDone
    intro outcome hOutcome
    cases outcome with
    | error err => exact hOutcome
    | ok value => trivial
  have hInitBoundary :
      Boundary components.initCursor contract globalFrameWords config
        allocatorDepth frameBase mode initCtx source target :=
    { semantic :=
        { invariant := by
            have hTransported :=
              hBoundary.semantic.invariant.transport_plan
                (components.initCursor.planAgreesOn cursor rfl).symm
                components.initCursor.planWF
            exact hTransported.transport_locals rfl
          sourceScope := by
            simpa [initCtx, Functions.Source.Ctx.withoutLoopControl] using
              hBoundary.semantic.sourceScope
          control := by
            simpa [initCtx] using
              hBoundary.semantic.control.withoutLoopControl
          capacity := hBoundary.semantic.capacity }
      controlAgreement := by
        simpa [initCtx] using
          (hBoundary.controlAgreement.transport_plan
            (components.initCursor.planAgreesOn cursor rfl).symm)
            |>.withoutLoopControl
      configEq := hBoundary.configEq
      ready := hBoundary.ready
      owned := hBoundary.owned
      budget := hBoundary.budget }
  have hInitRaw :=
    RecursiveOpenRuntime.at_targetFuel hRecursive components.initCursor
      (sourceFuel := loopFuel) (targetFuel := nestedFuel)
      (by simp [loopFuel]; omega)
      (by simpa [hNestedFuel] using hCapacity.init)
      hInitBoundary (Budget.mono (by simp [loopFuel]) hFuelBudget)
      hInitSuccess
  have hInit :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx components.loopState
          components.initLocals components.initCursor.plan root.returns
          components.loopLive frameBase mode initCtx loopCtx config
          allocatorDepth target)
        (Functions.InteractionSemantics.Block.openRun program initCtx
          loopFuel init source)
        (Expressions.InteractionSemantics.Block.openRun expressions nestedFuel
          { stmts := components.initCursor.compiled } target) := by
    simpa [components.initFinalState, components.initFinalLocals,
      components.loopLive_eq, loopCtx, initCtx] using hInitRaw
  have hInitOuterAgree :
      PlanAgreesOn components.initCursor.plan cursor.plan live :=
    components.initCursor.planAgreesOn cursor rfl
  have hPostShape :=
    AllocationLowering.lowerBlockScoped_state_shape components.lowerPost
  have hPostAgree :
      PlanAgreesOn components.postCursor.plan
        components.initCursor.plan components.loopLive :=
    components.postPlanAgree
  have hBodyAgree :
      PlanAgreesOn components.bodyCursor.plan
        components.initCursor.plan components.loopLive :=
    components.bodyPlanAgree
  have hLoop :
      ∀ {loopMode sourceAfter targetAfter},
        ActivationOwned config allocatorDepth frameBase loopMode →
        SameFrame mode loopMode →
        OutcomeEffect config allocatorDepth mode target targetAfter .regular →
        targetAfter.returns = target.returns →
        AllocationContext.ActivationInvariant contract root.lowerCtx
            components.loopState components.initLocals
            components.initCursor.plan components.loopLive frameBase
            loopMode sourceAfter targetAfter →
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Stmt.openRunForLoop program
              loopCtx cond postCtx post bodyCtx body loopFuel sourceAfter) →
            Simulation.Interaction.Rel
              (AllocationInteractionLoop.OpenLoopEffectResultRel
                (OutcomeEffect config allocatorDepth) contract
                root.lowerCtx components.loopState components.initLocals
                components.initCursor.plan root.returns components.loopLive
                frameBase loopMode loopCtx targetAfter)
              (Functions.InteractionSemantics.Stmt.openRunForLoop program
                loopCtx cond postCtx post bodyCtx body loopFuel sourceAfter)
              (Expressions.InteractionSemantics.Stmt.openRunForLoop
                expressions (loopFuel + slack) (.code components.condCode)
                  components.compiledPost components.compiledBody
                  targetAfter) := by
    intro loopMode sourceAfter targetAfter hLoopOwned hLoopSame hPrefix
      hLoopReturns hInvariant hSuccess
    have hPrefixActivation :=
      hPrefix.activation_of_not_halt (by
        intro kind hEq
        cases hEq)
    have hInitAgreement :
        AllocationInteractionControlAgreement.Agreement
          components.initCursor.plan root.returns live mode initCtx
          beforeLocals.withoutLoopControl target := by
      simpa [initCtx] using
        (hBoundary.controlAgreement.transport_plan
          (components.initCursor.planAgreesOn cursor rfl).symm)
          |>.withoutLoopControl
    have hLoopAgreement :
        AllocationInteractionControlAgreement.Agreement
          components.initCursor.plan root.returns components.loopLive
          loopMode loopCtx components.initLocals targetAfter := by
      apply hInitAgreement.reindexNoLoop
      · exact Functions.Source.Ctx.SameControl.scopeUpdate initCtx
          components.loopLive
      · simpa only [components.initFinalLocals] using
          (Locals.Block.compileOpen_sameControl
            components.initCursor.compile)
      · rfl
      · rfl
      · exact hLoopReturns
    apply AllocationInteractionLoopResource.forward
      (program := program) (expressions := expressions)
      (returns := root.returns) (live := components.loopLive)
      (loopCtx := loopCtx) (postCtx := postCtx) (bodyCtx := bodyCtx)
      (cond := cond) (post := post) (body := body)
      (targetCond := .code components.condCode)
      (targetPost := components.compiledPost)
      (targetBody := components.compiledBody)
      (slack := slack) (fuelBound := loopFuel) (fuel := loopFuel)
      (hLoopScope := rfl) (hBodyBreak := rfl) (hBodyContinue := rfl)
      (hCond := ?_) (hBody := ?_) (hPost := ?_)
      (by rfl) hLoopReturns (SameFrame.refl loopMode) hInvariant
      hPrefixActivation.ready hLoopOwned hSuccess
    · intro nextMode nextSource nextTarget hNext hNextReady hCondSuccess
      exact AllocationInteractionExpressionResource.forwardCondition
        (AllocationInteractionPrimitiveResource.canonicalPrimitiveForward
          contract)
        hBoundary.configEq
        (hCondSafe nextSource hNext.defined hCondSuccess) hNext.compiler
        components.condScoped components.lowerCond components.compileCond
        hNext.state hNextReady
    · intro fuel nextMode nextSource nextTarget effectInitial hFuelLt
        hOwned hRootSame hCondEffect hCondReturns hNext hBodySuccess
      have hBodyOpenSuccess :
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program bodyCtx
              fuel body nextSource) := by
        unfold Functions.InteractionSemantics.Block.openRunScoped
          Functions.Source.Canonical.Block.runScoped
          Functions.Source.Effectful.Control.Block.runScoped at hBodySuccess
        have hDone := Simulation.Interaction.Successful.bind_inv hBodySuccess
        apply Simulation.Interaction.AllDone.mono hDone
        intro outcome hOutcome
        cases outcome with
        | error err => exact hOutcome
        | ok value => trivial
      have hAtBodyState := hNext.transport_state hPostShape.1 hPostShape.2
      have hBodyInvariant :=
        (by
          exact
            (hAtBodyState.transport_plan hBodyAgree.symm
              components.bodyCursor.planWF).transport_locals rfl :
          AllocationContext.ActivationInvariant contract root.lowerCtx
            components.afterPost
            (components.initLocals.withLoopControl
              components.initLocals.layout.length)
            components.bodyCursor.plan components.loopLive frameBase
            nextMode nextSource nextTarget)
      have hBodyBoundary :
          Boundary components.bodyCursor contract globalFrameWords config
            allocatorDepth frameBase nextMode bodyCtx nextSource nextTarget :=
        { semantic :=
            { invariant := hBodyInvariant
              sourceScope := rfl
              control := by
                simpa [bodyCtx] using hOuterControl.withLoopControl
              capacity := by
                have hEntrySame : SameFrame mode nextMode :=
                  hLoopSame.trans hRootSame
                cases hEntrySame <;> exact hBoundary.semantic.capacity }
          controlAgreement :=
            by
              have hModeEq := hRootSame.eq_of_matches
                hInvariant.compiler.mode_matches hNext.compiler.mode_matches
              subst nextMode
              simpa [bodyCtx] using
                ((hLoopAgreement.withLoopControl hInvariant).transport_plan
                  hBodyAgree.symm).transport_target
                    (hCondReturns.trans hLoopReturns.symm)
          configEq := hBoundary.configEq
          ready :=
            (hCondEffect.activation_of_not_halt (by
              intro kind hEq
              cases hEq)).ready
          owned := hOwned
          budget := hBoundary.budget }
      have hBodyRaw :=
        RecursiveOpenRuntime.at_targetFuel hRecursive components.bodyCursor
          (sourceFuel := fuel) (targetFuel := fuel + slack)
          (by simp [loopFuel] at *; omega)
          (hCapacity.body fuel hFuelLt) hBodyBoundary
          (Budget.mono (by simp [loopFuel] at *; omega) hFuelBudget)
          hBodyOpenSuccess
      have hBodyRel :
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx
              components.bodyCursor.finalState
              components.bodyCursor.finalLocals components.bodyCursor.plan
              root.returns
              (Functions.Scope.Block.outEnv components.loopLive body)
              frameBase nextMode bodyCtx
              { bodyCtx with
                scope := Functions.Scope.Block.outEnv components.loopLive body }
              config allocatorDepth nextTarget)
            (Functions.InteractionSemantics.Block.openRun program bodyCtx
              fuel body nextSource)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) { stmts := components.bodyCursor.compiled }
              nextTarget) := by
        simpa using hBodyRaw
      have hExtends :
          AllocationLowering.StateExtends components.loopLive
            components.afterPost components.bodyCursor.finalState :=
        AllocationLowering.lowerBlockOpen_stateExtends
          components.bodyCursor.sourceScoped components.bodyCursor.lower
      have hExtendsLoop :
          AllocationLowering.StateExtends components.loopLive
            components.loopState components.bodyCursor.finalState := by
        rcases hExtends with ⟨dropped, hLayout, hFresh, hSlots⟩
        refine ⟨dropped, ?_, hFresh, ?_⟩
        · rw [hLayout, hPostShape.2]
        · intro name hLive
          exact (hSlots name hLive).trans
            (congrArg (AllocationSupport.lookupSlot? name) hPostShape.1)
      have hCleanupFuel :
          2 ≤ fuel + slack - components.bodyCursor.compiled.length := by
        have hBudget := hCapacity.body fuel hFuelLt
        simp [targetBudget, callStride, Nat.mul_succ] at hBudget
        omega
      exact AllocationInteractionControlResource.blockScoped_of_components
        rfl rfl rfl hOuterControl.withLoopControl hNext hExtendsLoop
        hBodyAgree components.finishBody hCleanupFuel hBodyRel
    · intro fuel effectMode nextMode nextSource nextTarget effectInitial
        hFuelLt hOwned hRootSame hSame hBodyEffect hBodyReturns hNext
        hPostSuccess
      have hPostOpenSuccess :
          Simulation.Interaction.Successful
            (Functions.InteractionSemantics.Block.openRun program postCtx
              fuel post nextSource) := by
        unfold Functions.InteractionSemantics.Block.openRunScoped
          Functions.Source.Canonical.Block.runScoped
          Functions.Source.Effectful.Control.Block.runScoped at hPostSuccess
        have hDone := Simulation.Interaction.Successful.bind_inv hPostSuccess
        apply Simulation.Interaction.AllDone.mono hDone
        intro outcome hOutcome
        cases outcome with
        | error err => exact hOutcome
        | ok value => trivial
      have hPostInvariant :=
        (by
          exact
            (hNext.transport_plan hPostAgree.symm
              components.postCursor.planWF).transport_locals rfl :
          AllocationContext.ActivationInvariant contract root.lowerCtx
            components.loopState components.initLocals.withoutLoopControl
            components.postCursor.plan components.loopLive frameBase
            nextMode nextSource nextTarget)
      have hPostBoundary :
          Boundary components.postCursor contract globalFrameWords config
            allocatorDepth frameBase nextMode postCtx nextSource nextTarget :=
        { semantic :=
            { invariant := hPostInvariant
              sourceScope := rfl
              control := by
                simpa [postCtx] using hOuterControl.withoutLoopControl
              capacity := by
                have hEntrySame : SameFrame mode nextMode :=
                  hLoopSame.trans hRootSame
                cases hEntrySame <;> exact hBoundary.semantic.capacity }
          controlAgreement := by
            have hPostBase := hLoopAgreement.withoutLoopControl
            have hPostAtTarget :=
              AllocationInteractionControlAgreement.Agreement.reindexNoLoop
              (afterLive := components.loopLive) (afterMode := nextMode)
              hPostBase
              (Functions.Source.Ctx.SameControl.refl postCtx)
              (Locals.Ctx.SameControl.refl
                components.initLocals.withoutLoopControl)
              (by rfl) (by rfl) (hBodyReturns.trans hLoopReturns.symm)
            simpa [postCtx] using
              hPostAtTarget.transport_plan hPostAgree.symm
          configEq := hBoundary.configEq
          ready :=
            (hBodyEffect.activation_of_not_halt (by
              intro kind hEq
              cases hEq)).ready
          owned := hOwned
          budget := hBoundary.budget }
      have hPostRaw :=
        RecursiveOpenRuntime.at_targetFuel hRecursive components.postCursor
          (sourceFuel := fuel) (targetFuel := fuel + slack)
          (by simp [loopFuel] at *; omega)
          (hCapacity.post fuel hFuelLt) hPostBoundary
          (Budget.mono (by simp [loopFuel] at *; omega) hFuelBudget)
          hPostOpenSuccess
      have hPostRel :
          Simulation.Interaction.Rel
            (RuntimeResultRel contract root.lowerCtx
              components.postCursor.finalState
              components.postCursor.finalLocals components.postCursor.plan
              root.returns
              (Functions.Scope.Block.outEnv components.loopLive post)
              frameBase nextMode postCtx
              { postCtx with
                scope := Functions.Scope.Block.outEnv components.loopLive post }
              config allocatorDepth nextTarget)
            (Functions.InteractionSemantics.Block.openRun program postCtx
              fuel post nextSource)
            (Expressions.InteractionSemantics.Block.openRun expressions
              (fuel + slack) { stmts := components.postCursor.compiled }
              nextTarget) := by
        simpa using hPostRaw
      have hExtends :
          AllocationLowering.StateExtends components.loopLive
            components.loopState components.postCursor.finalState :=
        AllocationLowering.lowerBlockOpen_stateExtends
          components.postCursor.sourceScoped components.postCursor.lower
      have hCleanupFuel :
          2 ≤ fuel + slack - components.postCursor.compiled.length := by
        have hBudget := hCapacity.post fuel hFuelLt
        simp [targetBudget, callStride, Nat.mul_succ] at hBudget
        omega
      exact AllocationInteractionControlResource.blockScoped_of_components
        rfl rfl rfl hOuterControl.withoutLoopControl hNext hExtends
        hPostAgree components.finishPost hCleanupFuel hPostRel
  have hBeforeExtends :
      AllocationLowering.StateExtends live beforeState
        components.loopState := by
    have hExtends := AllocationLowering.lowerBlockOpen_stateExtends
      components.initCursor.sourceScoped components.initCursor.lower
    simpa [components.initFinalState] using hExtends
  have hAfterEnv :
      components.afterState.allocation.env = beforeState.allocation.env := by
    rw [components.afterState_eq]
  have hAfterLayout : components.afterState.layout = beforeState.layout := by
    rw [components.afterState_eq]
  have hAfterInvariant :=
    hBoundary.semantic.invariant.transport_state hAfterEnv hAfterLayout
  have hAfterExtends :
      AllocationLowering.StateExtends live components.afterState
        components.loopState := by
    rcases hBeforeExtends with ⟨dropped, hLayout, hFresh, hSlots⟩
    refine ⟨dropped, ?_, hFresh, ?_⟩
    · rw [hLayout, hAfterLayout]
    · intro name hLive
      exact (hSlots name hLive).trans
        (congrArg (AllocationSupport.lookupSlot? name) hAfterEnv.symm)
  have hHeadSuccess' :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          (loopFuel + 1) (.for_ init cond post body) source) := by
    rw [hLoopFuel]
    exact hHeadSuccess
  have hInit' := hInit
  rw [← hNestedFuel] at hInit'
  have hHead :=
    AllocationInteractionForResource.forward
      (sourceFuel := loopFuel) (slack := slack)
      (hSourceScope := hBoundary.semantic.sourceScope)
      (hLoopLive := components.loopLive_eq)
      (hInitCtx := rfl) (hLoopCtx := rfl)
      (hPostCtx := rfl) (hBodyCtx := rfl)
      hAfterInvariant hBoundary.owned hAfterExtends hInitOuterAgree
      components.cleanupTo
      (by
        have hPositive :
            0 < targetBudget components.initCursor loopFuel 0 := by
          simp [targetBudget, callStride, Nat.mul_succ]
        change 0 < loopFuel + slack
        exact lt_of_lt_of_le hPositive
          ((targetBudget_mono_extra components.initCursor loopFuel
            (Nat.zero_le _)).trans hCapacity.init))
      hInit' hLoop hHeadSuccess'
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx components.afterState
          beforeLocals cursor.plan root.returns live frameBase mode sourceCtx
          sourceCtx config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun program sourceCtx
          childFuel (.for_ init cond post body) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := components.headCode } target) := by
    simpa [childFuel, loopFuel, nestedFuel, slack, totalFuel,
      hLoopFuel, hNestedFuel, hTotalFuel, components.headCode_eq,
      Locals.codeStmt] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live
            (.for_ init cond post body) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor components.tail components.exactTail
      components.compiled hMidCtx
      (by simpa [childFuel, hChildFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hChildFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward components.tail components.exactTail
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor components.tail
                hBoundary components.exactTail
                (by simp [Functions.Scope.Stmt.outEnv]) hInvariant hSame
                (Functions.Source.Ctx.SameControl.refl sourceCtx) hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive `break` with semantic and allocator preservation. -/
theorem brk
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra
      targetDepth : Nat}
    {config : Config} {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .brk :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSourceScope : sourceCtx.breakScope? = some afterLive)
    (hTargetDepth : beforeLocals.breakDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        beforeMode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .brk :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra beforeMode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.brk_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSourceScope hTargetDepth hTransition hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase beforeMode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .brk source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx = { sourceCtx with
        scope := Functions.Scope.Stmt.outEnv live .brk } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive `continue` with semantic and allocator preservation. -/
theorem cont
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live afterLive : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra
      targetDepth : Nat}
    {config : Config} {beforeMode afterMode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .cont :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSourceScope : sourceCtx.continueScope? = some afterLive)
    (hTargetDepth : beforeLocals.continueDepth? = some targetDepth)
    (hTransition :
      AllocationInteractionCleanup.Transition cursor.plan live afterLive
        targetDepth beforeMode afterMode)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        beforeMode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .cont :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra beforeMode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.cont_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSourceScope hTargetDepth hTransition hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase beforeMode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .cont source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx = { sourceCtx with
        scope := Functions.Scope.Stmt.outEnv live .cont } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive function leave with ordered return-resource preservation. -/
theorem leave
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live functionScope : List Functions.Name}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .leave :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hSourceScope : sourceCtx.leaveScope? = some functionScope)
    (hReturnsLive : ∀ name, name ∈ root.returns → name ∈ live)
    (hReturnsScope : ∀ name, name ∈ root.returns → name ∈ functionScope)
    (hTargetDepth : beforeLocals.leaveDepth? = some 0)
    (hRetc : beforeLocals.leaveRetc = root.returns.length)
    (hReturnFrame : target.returns ≠ [])
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .leave :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 4
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 4 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.leave_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hSourceScope hReturnsLive hReturnsScope hTargetDepth hRetc
      hReturnFrame hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel .leave source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with scope := Functions.Scope.Stmt.outEnv live .leave } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive plain terminal with allocator-safe terminal growth. -/
theorem terminal
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind} {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live { stmts := .terminal kind :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hMemory : Simulation.MemorySafety.TerminalMemorySafe contract kind [])
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .terminal kind :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.terminal_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hMemory hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.terminal kind) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live (.terminal kind) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

/-- Recursive argument-bearing terminal with allocator-safe growth. -/
theorem terminalArgs
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {kind : Assembly.HaltKind}
    {args : Locals.ExprSeq kind.argCount}
    {rest : List Functions.Stmt}
    {beforeState : AllocationLowering.State}
    {beforeLocals : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor :
      CoreCursor root scope live
        { stmts := .terminalArgs kind args :: rest }
        beforeState beforeLocals)
    (hSourceFuel : 0 < sourceFuel)
    (hArgsSafe : AllocationInteractionSafety.ExprSeqSafe contract args source)
    (hTerminalSafe :
      Simulation.Interaction.AllDone
        (fun outcome =>
          match outcome with
          | .error _ => True
          | .ok result =>
              Simulation.MemorySafety.TerminalMemorySafe
                contract kind result.2)
        (Functions.InteractionSemantics.ExprSeq.openEval args source))
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target)
    (hSuccessful :
      Simulation.Interaction.Successful
        (Functions.InteractionSemantics.Block.openRun program sourceCtx
          sourceFuel { stmts := .terminalArgs kind args :: rest } source))
    (hTailForward :
      ∀ {afterState : AllocationLowering.State}
        {afterLocals : Locals.Ctx}
        (tail : CoreCursor root scope live { stmts := rest }
          afterState afterLocals),
        ExactTail cursor tail →
        ∀ {sourceMid targetMid tailMode},
          Boundary tail contract globalFrameWords config allocatorDepth frameBase
              tailMode sourceCtx sourceMid targetMid →
            Simulation.Interaction.Successful
              (Functions.InteractionSemantics.Block.openRun program sourceCtx
                (sourceFuel - 1) { stmts := rest } sourceMid) →
            CursorRuntimeAt tail contract config allocatorDepth frameBase
              (sourceFuel - 1) (targetExtra + callStride expressions)
              tailMode sourceCtx
              sourceMid targetMid) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  let childFuel := sourceFuel - 1
  let totalFuel := targetBudget cursor sourceFuel targetExtra
  let headExtra := totalFuel - 3
  have hFuel : childFuel + 1 = sourceFuel := by simp [childFuel]; omega
  have hHeadFuel : headExtra + 3 = totalFuel := by
    simp [headExtra, totalFuel, targetBudget, callStride, Nat.mul_succ]
    omega
  obtain
      ⟨afterState, afterLocals, headCode, tail,
        hCompiled, hHead, hExact⟩ :=
    AllocationInteractionRecursiveResource.CoreCursor.terminalArgs_runtime_head
      cursor (sourceFuel := childFuel) (targetExtra := headExtra)
      hArgsSafe hTerminalSafe hBoundary
  have hHead' :
      Simulation.Interaction.Rel
        (RuntimeResultRel contract root.lowerCtx afterState afterLocals
          cursor.plan root.returns live frameBase mode sourceCtx sourceCtx
          config allocatorDepth target)
        (Functions.InteractionSemantics.Stmt.openRun
          program sourceCtx childFuel (.terminalArgs kind args) source)
        (Expressions.InteractionSemantics.Block.openRun expressions totalFuel
          { stmts := headCode } target) := by
    simpa [hHeadFuel] using hHead
  have hMidCtx :
      sourceCtx =
        { sourceCtx with
          scope := Functions.Scope.Stmt.outEnv live
            (.terminalArgs kind args) } := by
    have hCtx : { sourceCtx with scope := live } = sourceCtx := by
      cases sourceCtx
      have hScope := hBoundary.semantic.sourceScope
      simp only at hScope
      cases hScope
      rfl
    simpa [Functions.Scope.Stmt.outEnv] using hCtx.symm
  have hResult :=
    cons_of_parts_successful cursor tail hExact hCompiled hMidCtx
      (by simpa [childFuel, hFuel, totalFuel,
        Functions.Scope.Stmt.outEnv] using hHead')
      (by simpa [childFuel, hFuel] using hSuccessful)
      (fun {sourceMid targetMid tailMode} hInvariant hReady hSame hReturns
          hTailSuccess =>
        hTailForward tail hExact
          { semantic :=
              { invariant := hInvariant
                sourceScope := hBoundary.semantic.sourceScope
                control := hBoundary.semantic.control
                capacity := by
                  cases hSame <;> exact hBoundary.semantic.capacity }
            controlAgreement :=
              Boundary.controlAgreement_same_live cursor tail hBoundary
                hExact (by simp [Functions.Scope.Stmt.outEnv]) hInvariant
                hSame (Functions.Source.Ctx.SameControl.refl sourceCtx)
                hReturns
            configEq := hBoundary.configEq
            ready := hReady
            owned := hBoundary.owned.sameFrame hSame
            budget := hBoundary.budget }
          hTailSuccess)
  have hFuel' : sourceFuel - 1 + 1 = sourceFuel := by omega
  rw [hFuel'] at hResult
  exact hResult

end CursorRuntimeAt

namespace CursorResourceAt

/-- The empty cursor is allocator-neutral. -/
theorem nil
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {config : Config} {allocatorDepth sourceFuel targetExtra : Nat}
    {mode : ActivationMode} {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := [] } lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hReady : AllocatorReady config allocatorDepth target) :
    CursorResourceAt cursor config allocatorDepth sourceFuel targetExtra mode
      sourceCtx source target := by
  have hLower := cursor.lower
  simp [AllocationLowering.lowerBlockOpen,
    AllocationLowering.lowerStmtList] at hLower
  obtain ⟨hLowered, _hFinalState⟩ := hLower
  have hCompile := cursor.compile
  rw [← hLowered] at hCompile
  simp [Locals.Block.compileOpen] at hCompile
  obtain ⟨hCompiled, _hFinalLocals⟩ := hCompile
  have hTargetFuel :
      0 < targetBudget cursor sourceFuel targetExtra := by
    simp [targetBudget, callStride, Nat.mul_succ]
  have hSourceEq : sourceFuel - 1 + 1 = sourceFuel := by omega
  have hTargetEq :
      targetBudget cursor sourceFuel targetExtra - 1 + 1 =
        targetBudget cursor sourceFuel targetExtra := by omega
  have hSourceRun :=
    Functions.InteractionSemantics.Block.openRun_nil
      program sourceCtx (sourceFuel - 1) source
  rw [hSourceEq] at hSourceRun
  have hTargetRun :=
    Expressions.InteractionSemantics.Block.openRun_nil
      expressions (targetBudget cursor sourceFuel targetExtra - 1) target
  rw [hTargetEq] at hTargetRun
  unfold CursorResourceAt
  rw [hSourceRun, hCompiled, hTargetRun]
  exact Simulation.Interaction.Rel.done
    (Simulation.Interaction.ExceptRel.ok
      (OutcomeEffect.of_activation (ActivationEffect.refl hReady)))

end CursorResourceAt

namespace CursorRuntimeAt

/-- The empty cursor combines the pass-owned semantic and allocator base
cases. -/
theorem nil
    {allocation : Locals.Allocation.ProgramPlan}
    {program : Functions.Program}
    {expressions : Expressions.Program}
    {compilation : Compilation allocation program expressions}
    {root : RootArtifact compilation}
    {scope : Locals.Allocation.ScopeId}
    {live : List Functions.Name}
    {lowerState : AllocationLowering.State}
    {localsCtx : Locals.Ctx}
    {contract : MemoryContract.Contract}
    {globalFrameWords allocatorDepth frameBase sourceFuel targetExtra : Nat}
    {config : Config} {mode : ActivationMode}
    {sourceCtx : Functions.Source.Ctx}
    {source : SourceState} {target : TargetState}
    (cursor : CoreCursor root scope live { stmts := [] } lowerState localsCtx)
    (hSourceFuel : 0 < sourceFuel)
    (hBoundary :
      Boundary cursor contract globalFrameWords config allocatorDepth frameBase
        mode sourceCtx source target) :
    CursorRuntimeAt cursor contract config allocatorDepth frameBase sourceFuel
      targetExtra mode sourceCtx source target := by
  have hSemantic :=
    AllocationInteractionRecursive.CursorForwardAt.nil
      (targetExtra := targetExtra) cursor hSourceFuel hBoundary.semantic
  have hResource :=
    CursorResourceAt.nil cursor hSourceFuel hBoundary.ready
      (targetExtra := targetExtra) (mode := mode) (sourceCtx := sourceCtx)
      (source := source)
  exact Simulation.Interaction.Rel.inter hSemantic hResource

end CursorRuntimeAt

end AllocationInteractionRecursiveResource
end Functions
end EvmCompiler
