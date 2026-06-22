import EvmCompiler.TypedCfg.ReturnAddressLower
import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.Assembly.InteractionPreservation
import EvmCompiler.Assembly.StackShufflePreservation

namespace EvmCompiler
namespace TypedCfg
namespace ReturnAddressPreservation

open ReturnAddressRelation

theorem returnToken_stepAt
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {token : Word} {site : ReturnSite} {targetPc currentPc : Nat}
    {shape : Shape} {target source : Assembly.EVMState}
    (hFind : ReturnAddressLower.Program.siteForToken? cfg token = some site)
    (hResolve : assembly.labelPc site.target = some targetPc)
    (hRel : RuntimeRel assembly.labelPc
      (ReturnAddressLower.Program.returnSites cfg) shape target source) :
    exists targetAfter sourceAfter,
      Assembly.Source.stepAt assembly currentPc (.pushLabel site.target) target =
          .ok targetAfter ∧
        TypedCfg.Instr.runState (.returnToken token) shape source =
          .ok sourceAfter ∧
        RuntimeRel assembly.labelPc
          (ReturnAddressLower.Program.returnSites cfg)
          { shape with slots := .returnPC token.toNat :: shape.slots }
          targetAfter sourceAfter := by
  have hSite := ReturnAddressLower.siteForToken?_mem hFind
  have hToken : site.token = token := hSite.2
  subst token
  let targetAfter :=
    target.replaceStackAndIncrPC
      (target.stack.push (EvmYul.UInt256.ofNat targetPc)) (pcΔ := 33)
  let sourceAfter :=
    source.replaceStackAndIncrPC (source.stack.push site.token) (pcΔ := 33)
  refine ⟨targetAfter, sourceAfter, ?_, ?_, ?_⟩
  · simp [Assembly.Source.stepAt, hResolve, targetAfter,
      Assembly.Target.stepInstr, Assembly.Target.stepInstrWith,
      Assembly.Target.stepPushWith]
  · rfl
  · apply runtimeRel_replaceStackAndIncrPC hRel
    exact shapeStackRel_push_returnPC hSite.1 hResolve hRel.2

theorem returnToken_openStepAt
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {token : Word} {site : ReturnSite} {targetPc currentPc : Nat}
    {shape : Shape} {target source : Assembly.EVMState}
    (hFind : ReturnAddressLower.Program.siteForToken? cfg token = some site)
    (hResolve : assembly.labelPc site.target = some targetPc)
    (hRel : RuntimeRel assembly.labelPc
      (ReturnAddressLower.Program.returnSites cfg) shape target source) :
    exists targetAfter sourceAfter,
      Assembly.InteractionSemantics.Source.openStepAt assembly currentPc
          (.pushLabel site.target) target =
          Simulation.Interaction.pure targetAfter ∧
        TypedCfg.Instr.runState (.returnToken token) shape source =
          .ok sourceAfter ∧
        RuntimeRel assembly.labelPc
          (ReturnAddressLower.Program.returnSites cfg)
          { shape with slots := .returnPC token.toNat :: shape.slots }
          targetAfter sourceAfter := by
  obtain ⟨targetAfter, sourceAfter, hTarget, hSource, hRelAfter⟩ :=
    returnToken_stepAt (currentPc := currentPc) hFind hResolve hRel
  exact
    ⟨targetAfter, sourceAfter,
      by
        simp [Assembly.InteractionSemantics.Source.openStepAt, hTarget]
        rfl,
      hSource, hRelAfter⟩

theorem jumpDynamic_eventually
    {pre post : Assembly.Program} {state : Assembly.EVMState}
    {destination : Word} {stack : List Word}
    (hFits : pre.PCFits)
    (hPc : state.pc = pre.pcAfter)
    (hStack : state.stack = destination :: stack) :
    Assembly.Source.Eventually
      (pre ++ [.jumpDynamic] ++ post) state
      (fun outcome =>
        outcome = .ok (.running { state with pc := destination, stack := stack })) := by
  refine ⟨1, .ok (.running { state with pc := destination, stack := stack }), ?_, rfl⟩
  rw [show pre ++ [.jumpDynamic] ++ post =
      pre ++ .jumpDynamic :: post by simp [List.append_assoc]]
  rw [Assembly.InteractionPreservation.source_runNResult_one_at_boundary
    hFits hPc]
  simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
    Assembly.Target.stepInstr, Assembly.Target.stepInstrWith, hStack,
    EvmYul.Stack.pop, Assembly.Instr.haltKind?]

theorem returnDispatch_eventually
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {block : Block} {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word} {targetLabel : Label}
    {targetWord : Word} {target source : Assembly.EVMState}
    {pre post : Assembly.Program}
    (hBlock : block ∈ cfg.blocks)
    (hTerm : block.term = .returnDispatch returnCount sites)
    (hUnique : ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hDepth : shape.returnTokenDepth? = some depth)
    (hSlot : shape.slots[depth]? = some (.returnPC token.toNat))
    (hCount : depth = returnCount)
    (hBound : depth < 16)
    (hTargetGet : target.stack[depth]? = some targetWord)
    (hSourceGet : source.stack[depth]? = some token)
    (hFind : Block.ReturnSite.findTarget? token sites = some targetLabel)
    (hAssembly : assembly =
      pre ++ ReturnAddressLower.Terminator.dynamicReturnCode depth ++ post)
    (hFits : Assembly.Program.PCFitsFrom pre
      (ReturnAddressLower.Terminator.dynamicReturnCode depth))
    (hPc : target.pc = pre.pcAfter)
    (hRel : RuntimeRel assembly.labelPc
      (ReturnAddressLower.Program.returnSites cfg) shape target source) :
    exists targetAfter targetPc,
      Assembly.Source.Eventually assembly target
        (fun outcome => outcome = .ok (.running targetAfter)) ∧
      assembly.labelPc targetLabel = some targetPc ∧
      targetAfter.pc = EvmYul.UInt256.ofNat targetPc ∧
      Block.runTerm shape (.returnDispatch returnCount sites) source =
        .jump targetLabel
          { source with stack := source.stack.eraseIdx depth } ∧
      RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        (shape.erase depth) targetAfter
        { source with stack := source.stack.eraseIdx depth } := by
  subst returnCount
  subst assembly
  obtain ⟨selected, hSelectedLocal, hSelectedToken, hSelectedTarget⟩ :=
    Block.ReturnSite.mem_token_of_findTarget?_eq_some hFind
  have hSelectedGlobal :
      selected ∈ ReturnAddressLower.Program.returnSites cfg := by
    apply ReturnAddressLower.term_site_mem_returnSites hBlock
    simp [ReturnAddressLower.Terminator.sites, hTerm, hSelectedLocal]
  have hUnique' := ReturnAddressLower.tokensUnique_of_check hUnique
  obtain ⟨targetPc, hResolve, hTargetWord, hErasedRel⟩ :=
    returnPC_target_of_unique hUnique' hSelectedGlobal hSelectedToken
      hRel.2 hSlot hTargetGet hSourceGet
  have hTargetStack :
      target.stack = target.stack.take depth ++
        targetWord :: target.stack.drop (depth + 1) :=
    list_eq_take_get_drop hTargetGet
  have hDepthLt : depth < target.stack.length :=
    (List.getElem?_eq_some_iff.mp hTargetGet).choose
  have hFrontLength : (target.stack.take depth).length = depth := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hDepthLt)]
  have hLiftFits : Assembly.Program.PCFitsFrom pre
      (Assembly.StackShuffle.liftBuriedToTop depth) := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [ReturnAddressLower.Terminator.dynamicReturnCode,
      List.append_assoc] using hFits
  have hJumpFits :
      Assembly.Program.PCFitsFrom
        (pre ++ Assembly.StackShuffle.liftBuriedToTop depth)
        [.jumpDynamic] := by
    have := Assembly.Program.PCFitsFrom.right hFits
    simpa [ReturnAddressLower.Terminator.dynamicReturnCode,
      List.append_assoc] using this
  have hLift :=
    Assembly.StackShuffle.liftBuriedToTop_source_exists
      (state := target)
      (front := target.stack.take depth)
      (suffix := target.stack.drop (depth + 1))
      (token := targetWord) (pre := pre)
      (post := [.jumpDynamic] ++ post)
      (by simpa [hFrontLength] using hLiftFits)
      (by simpa [hTargetStack] using hPc)
      (by omega)
  have hLift' :
      Assembly.Source.Eventually
        (pre ++ ReturnAddressLower.Terminator.dynamicReturnCode depth ++ post)
        target
        (fun outcome =>
          match outcome with
          | .ok (.running final) =>
              final.stack = targetWord :: target.stack.take depth ++
                  target.stack.drop (depth + 1) ∧
                Assembly.eraseRuntimeControl final =
                  Assembly.eraseRuntimeControl
                    { target with
                      stack := targetWord :: target.stack.take depth ++
                        target.stack.drop (depth + 1) } ∧
                final.pc =
                  (pre ++ Assembly.StackShuffle.liftBuriedToTop depth).pcAfter
          | _ => False) := by
    have hLiftNormalized := hLift
    rw [hFrontLength] at hLiftNormalized
    rw [← hTargetStack] at hLiftNormalized
    simpa only [ReturnAddressLower.Terminator.dynamicReturnCode,
      List.append_assoc] using hLiftNormalized
  have hErase :
      target.stack.eraseIdx depth =
        target.stack.take depth ++ target.stack.drop (depth + 1) :=
    eraseIdx_eq_take_drop_of_get? hTargetGet
  have hRunRel :
      Assembly.Source.Eventually
        (pre ++ ReturnAddressLower.Terminator.dynamicReturnCode depth ++ post)
        target
        (fun outcome =>
          match outcome with
          | .ok (.running final) =>
              final.pc = targetWord ∧
                RuntimeRel
                  (pre ++ ReturnAddressLower.Terminator.dynamicReturnCode depth ++
                    post).labelPc
                  (ReturnAddressLower.Program.returnSites cfg)
                  (shape.erase depth) final
                  { source with stack := source.stack.eraseIdx depth }
          | _ => False) := by
    apply Assembly.Source.Eventually.bind_running hLift'
    intro mid hMid
    have hJump := jumpDynamic_eventually
      (pre := pre ++ Assembly.StackShuffle.liftBuriedToTop depth)
      (post := post) (state := mid) (destination := targetWord)
      (stack := target.stack.take depth ++ target.stack.drop (depth + 1))
      (Assembly.Program.PCFitsFrom.start hJumpFits) hMid.2.2
      (by simpa [hFrontLength] using hMid.1)
    have hJump' := hJump
    rw [show
      pre ++ Assembly.StackShuffle.liftBuriedToTop depth ++
          [.jumpDynamic] ++ post =
        pre ++ ReturnAddressLower.Terminator.dynamicReturnCode depth ++ post by
      simp [ReturnAddressLower.Terminator.dynamicReturnCode,
        List.append_assoc]] at hJump'
    apply Assembly.Source.Eventually.mono hJump'
    intro outcome hOutcome
    rw [hOutcome]
    constructor
    · simp
    · constructor
      · have hShared := congrArg EvmYul.EVM.State.toSharedState hMid.2.1
        calc
          mid.toSharedState = target.toSharedState := by
            simpa [Assembly.eraseRuntimeControl] using hShared
          _ = source.toSharedState := hRel.1
      · simpa [ShapeStackRel, Shape.erase, hErase] using hErasedRel
  rcases hRunRel with ⟨fuel, outcome, hRun, hPost⟩
  cases outcome with
  | error err => cases hPost
  | ok result =>
    cases result with
    | halted halt => cases hPost
    | running targetAfter =>
      simp only at hPost
      refine ⟨targetAfter, targetPc, ⟨fuel, _, hRun, rfl⟩, ?_, ?_, ?_, ?_⟩
      · simpa [hSelectedTarget] using hResolve
      · exact hPost.1.trans hTargetWord
      · simp [Block.runTerm, hDepth, hSourceGet, hFind]
      · exact hPost.2

end ReturnAddressPreservation
end TypedCfg
end EvmCompiler
