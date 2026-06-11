import EvmCompiler.Assembly.StackShuffleObserverPreservation
import EvmCompiler.TypedCfg.ObserverSemantics
import EvmCompiler.TypedCfg.Preservation

namespace EvmCompiler
namespace TypedCfg

namespace ObserverSemantics
namespace Instr

theorem runState_pc_of_lowerAt
    {instr : TypedCfg.Instr} {shape output : Shape}
    {code : Assembly.Program} {state final : EVMState}
    {trace trace' : Assembly.ResourceTrace}
    (hLower : instr.lowerAt? shape = some (code, output))
    (hRun : runState instr shape state trace = .ok (final, trace')) :
    final.pc =
      state.pc + EvmYul.UInt256.ofNat code.byteLength := by
  rcases runState_plain_pc hRun with ⟨plain, hPlain, hPc⟩
  rw [hPc]
  exact Preservation.Instr.runState_pc_of_lowerAt hLower hPlain

end Instr
end ObserverSemantics

namespace ObserverPreservation

abbrev Trace := Assembly.ResourceTrace

def PositiveEventually (program : Assembly.Program) (state : EVMState)
    (trace : Trace)
    (post : Assembly.Source.OracleExecutionOutcome → Prop) : Prop :=
  ∃ fuel outcome,
    0 < fuel ∧
      Assembly.Source.runNResultWithOracle program fuel state trace = outcome ∧
      post outcome

namespace PositiveEventually

theorem eventually
    {program : Assembly.Program} {state : EVMState} {trace : Trace}
    {post : Assembly.Source.OracleExecutionOutcome → Prop}
    (hRun : PositiveEventually program state trace post) :
    Assembly.Source.EventuallyWithOracle program state trace post := by
  rcases hRun with ⟨fuel, outcome, _hPositive, hRun, hPost⟩
  exact ⟨fuel, outcome, hRun, hPost⟩

theorem against_halted
    {program : Assembly.Program} {state : EVMState}
    {trace traceOut : Trace} {post : Assembly.Source.OracleExecutionOutcome → Prop}
    {fullFuel : Nat} {halt : Assembly.Halt}
    (hRun : PositiveEventually program state trace post)
    (hFull :
      Assembly.Source.runNResultWithOracle
          program fullFuel state trace =
        .ok (.halted halt, traceOut)) :
    ∃ prefixFuel outcome,
      0 < prefixFuel ∧
        Assembly.Source.runNResultWithOracle
            program prefixFuel state trace = outcome ∧
        post outcome ∧
        match outcome with
        | .error _ => False
        | .ok (.running _, _) => prefixFuel < fullFuel
        | .ok (.halted prefixHalt, prefixTrace) =>
            prefixHalt = halt ∧ prefixTrace = traceOut := by
  rcases hRun with
    ⟨prefixFuel, outcome, hPositive, hPrefix, hPost⟩
  have hCompare :=
    Assembly.Source.runNResultWithOracle_compare_halted hFull hPrefix
  refine
    ⟨prefixFuel, outcome, hPositive, hPrefix, hPost, ?_⟩
  cases outcome with
  | error err =>
      exact hCompare
  | ok pair =>
      rcases pair with ⟨result, prefixTrace⟩
      cases result with
      | running mid =>
          exact hCompare
      | halted prefixHalt =>
          exact hCompare

end PositiveEventually

theorem runPops_source_runNResultWithOracle
    (count : Nat) {pre post : Assembly.Program} {state : EVMState}
    {trace : Trace}
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (List.replicate count (.prim .pop)))
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runNResultWithOracle
        (pre ++ List.replicate count (.prim .pop) ++ post)
        count state trace =
      (TypedCfg.Instr.runPops count state).map
        (fun final => (Assembly.StepResult.running final, trace)) := by
  induction count generalizing pre state with
  | zero =>
      rfl
  | succ count ih =>
      rcases hFits with ⟨hFitsHere, hFitsRest⟩
      rw [List.replicate_succ]
      simp only [List.append_assoc]
      change
        Assembly.Source.runNResultWithOracle
            (pre ++ Assembly.Instr.prim Assembly.PrimOp.pop ::
              (List.replicate count
                (Assembly.Instr.prim Assembly.PrimOp.pop) ++ post))
            (count + 1) state trace =
          (TypedCfg.Instr.runPops (count + 1) state).map
            (fun final => (Assembly.StepResult.running final, trace))
      unfold Assembly.Source.runNResultWithOracle TypedCfg.Instr.runPops
      rw [Assembly.Source.stepResultWithOracle_at_boundary hFitsHere hPc]
      cases hStep : Assembly.PrimOp.pop.step state with
      | error err =>
          simp [Assembly.Source.stepAtResultWithOracle,
            Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Target.stepInstr, hStep, Bind.bind, Except.bind,
            Except.map]
      | ok state' =>
          simp only [Assembly.Source.stepAtResultWithOracle,
            Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Target.stepInstr, hStep, Bind.bind, Except.bind,
            Assembly.Instr.haltKind?, Assembly.PrimOp.haltKind?,
            Assembly.ResourceObserver.ofInstr?,
            Assembly.ResourceObserver.ofPrimOp?, Except.map]
          have hPc' :
              state'.pc =
                (pre ++ [Assembly.Instr.prim Assembly.PrimOp.pop]).pcAfter := by
            calc
              state'.pc =
                  state.pc + EvmYul.UInt256.ofNat 1 :=
                    Preservation.pop_step_pc hStep
              _ = pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
                    rw [hPc]
              _ =
                  (pre ++
                    [Assembly.Instr.prim Assembly.PrimOp.pop]).pcAfter := by
                    simpa [Assembly.Instr.byteSize] using
                      (Assembly.Program.pcAfter_snoc pre
                        (Assembly.Instr.prim Assembly.PrimOp.pop)).symm
          have hTail :=
            ih (pre := pre ++ [Assembly.Instr.prim .pop]) (state := state')
              hFitsRest hPc'
          simpa [List.append_assoc] using hTail

theorem source_prim_stepAtResultWithOracle
    {program : Assembly.Program} {pc : Nat} {op : Assembly.PrimOp}
    {shape : Shape} {state : EVMState} {trace : Trace}
    (hNoHalt : op.haltKind? = none) :
    Assembly.Source.stepAtResultWithOracle
        program pc (.prim op) state trace =
      (ObserverSemantics.Instr.runState
        (.prim op) shape state trace).map
          (fun result =>
            (Assembly.StepResult.running result.1, result.2)) := by
  unfold Assembly.Source.stepAtResultWithOracle
  unfold Assembly.Source.stepAtResult Assembly.Source.stepAt
  unfold ObserverSemantics.Instr.runState TypedCfg.Instr.runState
  cases hStep : op.step state with
  | error err =>
      simp [Assembly.Target.stepInstr, hStep, hNoHalt,
        Assembly.Instr.haltKind?, Assembly.TargetInstr.haltKind?,
        Bind.bind, Except.bind, Except.map]
  | ok final =>
      cases hObserver :
          Assembly.ResourceObserver.ofPrimOp? op with
      | none =>
          simp [Assembly.Target.stepInstr, hStep, hNoHalt, hObserver,
            Assembly.Instr.haltKind?, Assembly.TargetInstr.haltKind?,
            Assembly.ResourceObserver.ofInstr?, Bind.bind, Except.bind,
            Except.map]
      | some kind =>
          cases hApply :
              Assembly.ResourceObserver.applyOracleFromPostState
                kind final trace <;>
            simp [Assembly.Target.stepInstr, hStep, hNoHalt, hObserver,
              Assembly.Instr.haltKind?, Assembly.TargetInstr.haltKind?,
              Assembly.ResourceObserver.ofInstr?,
              Assembly.StepResult.state, Assembly.StepResult.withState,
              hApply, Bind.bind, Except.bind, Except.map]

namespace Instr

theorem lowerAt_source_runNResultWithOracle
    {instr : TypedCfg.Instr} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    {trace : Trace}
    (hLower : instr.lowerAt? shape = some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runNResultWithOracle
        (pre ++ code ++ post) code.length state trace =
      (ObserverSemantics.Instr.runAt instr shape state trace).map
        (fun result =>
          (Assembly.StepResult.running result.1.1, result.2)) := by
  cases hType : instr.type? shape with
  | none =>
      simp [TypedCfg.Instr.lowerAt?, hType] at hLower
  | some typedOutput =>
      rw [ObserverSemantics.Instr.runAt_map_running hType]
      cases instr with
      | push value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          rw [Assembly.Source.runNResultWithOracle_one_at_boundary_append
            hFits.1 hPc]
          simp [ObserverSemantics.Instr.runAt,
            ObserverSemantics.Instr.runState, TypedCfg.Instr.runState,
            Assembly.Source.stepAtResultWithOracle,
            Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Target.stepInstr, Assembly.Instr.haltKind?,
            Assembly.TargetInstr.haltKind?,
            Assembly.ResourceObserver.ofInstr?, Bind.bind, Except.bind,
            Except.map]
      | returnToken value =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          rw [Assembly.Source.runNResultWithOracle_one_at_boundary_append
            hFits.1 hPc]
          simp [ObserverSemantics.Instr.runAt,
            ObserverSemantics.Instr.runState, TypedCfg.Instr.runState,
            Assembly.Source.stepAtResultWithOracle,
            Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Target.stepInstr, Assembly.Instr.haltKind?,
            Assembly.TargetInstr.haltKind?,
            Assembly.ResourceObserver.ofInstr?, Bind.bind, Except.bind,
            Except.map]
      | prim op =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          have hNoHalt : op.haltKind? = none := by
            cases hArity : op.stackArity? with
            | none =>
                simp [TypedCfg.Instr.type?, hArity] at hType
            | some arity =>
                cases op <;>
                  simp [Assembly.PrimOp.stackArity?,
                    Assembly.PrimOp.haltKind?] at hArity ⊢
          rw [Assembly.Source.runNResultWithOracle_one_at_boundary_append
            hFits.1 hPc]
          exact source_prim_stepAtResultWithOracle hNoHalt
      | pop =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp only [List.length_cons, List.length_nil, Nat.zero_add,
            List.append_assoc]
          rw [Assembly.Source.runNResultWithOracle_one_at_boundary_append
            hFits.1 hPc]
          simpa [ObserverSemantics.Instr.runState,
            TypedCfg.Instr.runState] using
              (source_prim_stepAtResultWithOracle
                (program :=
                  pre ++
                    ([Assembly.Instr.prim Assembly.PrimOp.pop] ++ post))
                (pc := pre.byteLength) (shape := shape)
                (state := state) (trace := trace)
                (op := Assembly.PrimOp.pop) (by rfl))
      | bindLocals offset names =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [Assembly.Source.runNResultWithOracle,
            ObserverSemantics.Instr.runAt,
            ObserverSemantics.Instr.runState, TypedCfg.Instr.runState,
            hType, Bind.bind, Except.bind, Except.map]
      | bindScratch baseDepth name slot =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [Assembly.Source.runNResultWithOracle,
            ObserverSemantics.Instr.runAt,
            ObserverSemantics.Instr.runState, TypedCfg.Instr.runState,
            hType, Bind.bind, Except.bind, Except.map]
      | relabel target =>
          simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
            at hLower
          rcases hLower with ⟨rfl, rfl⟩
          simp [Assembly.Source.runNResultWithOracle,
            ObserverSemantics.Instr.runAt,
            ObserverSemantics.Instr.runState, TypedCfg.Instr.runState,
            hType, Bind.bind, Except.bind, Except.map]
      | dup depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc] <;>
            rw [Assembly.Source.runNResultWithOracle_one_at_boundary_append
              hFits.1 hPc] <;>
            simpa [ObserverSemantics.Instr.runState,
              TypedCfg.Instr.runState] using
                (source_prim_stepAtResultWithOracle
                  (program := pre ++ ([Assembly.Instr.prim _] ++ post))
                  (pc := pre.byteLength) (shape := shape)
                  (state := state) (trace := trace) (by rfl))
      | swap depth =>
          have hDepth : depth < 16 := by
            by_contra hNot
            simp [TypedCfg.Instr.type?, hNot] at hType
          interval_cases depth <;>
            simp [TypedCfg.Instr.lowerAt?, TypedCfg.Instr.lower?, hType]
              at hLower <;>
            rcases hLower with ⟨rfl, rfl⟩ <;>
            simp only [List.length_cons, List.length_nil, Nat.zero_add,
              List.append_assoc] <;>
            rw [Assembly.Source.runNResultWithOracle_one_at_boundary_append
              hFits.1 hPc] <;>
            simpa [ObserverSemantics.Instr.runState,
              TypedCfg.Instr.runState] using
                (source_prim_stepAtResultWithOracle
                  (program := pre ++ ([Assembly.Instr.prim _] ++ post))
                  (pc := pre.byteLength) (shape := shape)
                  (state := state) (trace := trace) (by rfl))
      | unwind target =>
          simp [TypedCfg.Instr.lowerAt?, hType] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          cases hPops :
              TypedCfg.Instr.runPops
                (shape.length - target.length) state with
          | error err =>
              simpa [ObserverSemantics.Instr.runState,
                TypedCfg.Instr.runState, hPops, Except.map] using
                  runPops_source_runNResultWithOracle
                    (shape.length - target.length)
                    (post := post) (trace := trace) hFits hPc
          | ok final =>
              simpa [ObserverSemantics.Instr.runState,
                TypedCfg.Instr.runState, hPops, Except.map] using
                  runPops_source_runNResultWithOracle
                    (shape.length - target.length)
                    (post := post) (trace := trace) hFits hPc

end Instr

namespace Outcome

def Simulates (program : Assembly.Program)
    (source : TypedCfg.Outcome) (trace : Trace) :
    Assembly.Source.OracleExecutionOutcome → Prop
  | .error err =>
      Preservation.Outcome.Simulates program source (.error err)
  | .ok (result, trace') =>
      trace' = trace ∧
        Preservation.Outcome.Simulates program source (.ok result)

def RunningAt (dest : Nat) (expected : EVMState) (trace : Trace) :
    Assembly.Source.OracleExecutionOutcome → Prop
  | .ok (.running final, trace') =>
      trace' = trace ∧
        Preservation.Outcome.RunningAt dest expected (.ok (.running final))
  | _ => False

end Outcome

namespace Terminator

theorem returnDispatchTestCases_eventuallyWithOracle_of_all_ne
    {depth : Nat} {sites : List ReturnSite}
    {front suffix : List Word} {token : Word}
    {code pre post : Assembly.Program} {state : EVMState}
    {trace : Trace}
    (hCode :
      code = TypedCfg.Terminator.returnDispatchTestCases depth sites)
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hStack : state.stack = front ++ token :: suffix)
    (hNe : ∀ site, site ∈ sites → site.token ≠ token)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ code ++ post) sites) :
    Assembly.Source.EventuallyWithOracle
      (pre ++ code ++ post) state trace
      (fun outcome =>
        match outcome with
        | .ok (.running final, finalTrace) =>
            finalTrace = trace ∧
              final.stack = front ++ token :: suffix ∧
              Assembly.SameData final state ∧
              final.pc = (pre ++ code).pcAfter
        | _ => False) := by
  subst code
  induction sites generalizing pre state trace with
  | nil =>
      exact Assembly.Source.EventuallyWithOracle.pure
        (by
          simp [TypedCfg.Terminator.returnDispatchTestCases,
            Assembly.SameData.refl, hStack, hPc])
  | cons site rest ih =>
      let headCode := TypedCfg.Terminator.returnDispatchTest depth site
      let tailCode :=
        TypedCfg.Terminator.returnDispatchTestCases depth rest
      have hCodeEq :
          TypedCfg.Terminator.returnDispatchTestCases depth (site :: rest) =
            headCode ++ tailCode := by
        simp [TypedCfg.Terminator.returnDispatchTestCases, headCode, tailCode]
      have hFitsAppend :
          Assembly.Program.PCFitsFrom pre (headCode ++ tailCode) := by
        simpa [hCodeEq] using hFits
      have hHeadFits :
          Assembly.Program.PCFitsFrom pre headCode :=
        Assembly.Program.PCFitsFrom.left hFitsAppend
      have hTailFits :
          Assembly.Program.PCFitsFrom (pre ++ headCode) tailCode :=
        Assembly.Program.PCFitsFrom.right hFitsAppend
      have hSiteNe : site.token ≠ token :=
        hNe site (by simp)
      rcases hResolved site (by simp) with ⟨dest, hDest⟩
      have hDest' :
          (pre ++ headCode ++ (tailCode ++ post)).labelPc site.caseLabel =
            some dest := by
        simpa [hCodeEq, List.append_assoc] using hDest
      have hRecord :
          { state with stack := front ++ token :: suffix } = state := by
        rw [← hStack]
      have hHead :=
        Assembly.StackShuffle.dispatchTest_source_exists_withOracle
          (state := state) (front := front) (suffix := suffix)
          (token := token) (probe := site.token)
          (label := site.caseLabel) (dest := dest)
          (pre := pre) (post := tailCode ++ post) (trace := trace)
          (by
            simpa [headCode, TypedCfg.Terminator.returnDispatchTest,
              hFront] using hHeadFits)
          (by simpa [hRecord] using hPc)
          (by omega)
          (by
            simpa [headCode, TypedCfg.Terminator.returnDispatchTest,
              hFront, List.append_assoc] using hDest')
      rw [hRecord] at hHead
      refine
        Assembly.Source.EventuallyWithOracle.bind_running
          (program :=
            pre ++
              TypedCfg.Terminator.returnDispatchTestCases depth
                (site :: rest) ++ post)
          (middle := fun mid midTrace =>
            midTrace = trace ∧
              mid.stack = front ++ token :: suffix ∧
              Assembly.SameData mid state ∧
              mid.pc = (pre ++ headCode).pcAfter)
          ?_ ?_
      · exact Assembly.Source.EventuallyWithOracle.mono
          (by
            rw [hCodeEq]
            simpa [headCode, TypedCfg.Terminator.returnDispatchTest,
              hFront, List.append_assoc] using hHead)
          (by
            intro outcome hOutcome
            cases outcome with
            | error err => cases hOutcome
            | ok pair =>
                rcases pair with ⟨result, midTrace⟩
                cases result with
                | halted halt => cases hOutcome
                | running mid =>
                    rcases hOutcome with
                      ⟨hTrace, hStackMid, hData, hPcMid⟩
                    refine ⟨hTrace, hStackMid, ?_, ?_⟩
                    · simpa [Assembly.SameData, hRecord] using hData
                    · simpa [hSiteNe] using hPcMid)
      · intro mid midTrace hMid
        rcases hMid with ⟨hTrace, hStackMid, hDataMid, hPcMid⟩
        have hRestNe :
            ∀ restSite, restSite ∈ rest → restSite.token ≠ token := by
          intro restSite hMem
          exact hNe restSite (by simp [hMem])
        have hRestResolved :
            Preservation.Terminator.ResolvedCaseLabels
              ((pre ++ headCode) ++ tailCode ++ post) rest := by
          intro restSite hMem
          rcases hResolved restSite (by simp [hMem]) with
            ⟨restDest, hRestDest⟩
          exact
            ⟨restDest,
              by
                simpa [hCodeEq, List.append_assoc] using hRestDest⟩
        have hRest :=
          ih (pre := pre ++ headCode) (state := mid) (trace := midTrace)
            (hStack := hStackMid) (hNe := hRestNe)
            (hFits := hTailFits) (hPc := hPcMid)
            (hResolved := hRestResolved)
        exact Assembly.Source.EventuallyWithOracle.mono
          (by
            rw [hCodeEq]
            simpa [List.append_assoc] using hRest)
          (by
            intro outcome hOutcome
            cases outcome with
            | error err => cases hOutcome
            | ok pair =>
                rcases pair with ⟨result, finalTrace⟩
                cases result with
                | halted halt => cases hOutcome
                | running final =>
                    rcases hOutcome with
                      ⟨hFinalTrace, hStackFinal, hData, hPcFinal⟩
                    exact
                      ⟨hFinalTrace.trans hTrace,
                        hStackFinal,
                        Assembly.SameData.trans hData hDataMid,
                        by
                          simpa [hCodeEq, List.append_assoc] using hPcFinal⟩)

theorem returnDispatchTestCases_eventuallyWithOracle_of_selected
    {depth : Nat} {before after : List ReturnSite} {site : ReturnSite}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {state : EVMState} {trace : Trace}
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hStack : state.stack = front ++ token :: suffix)
    (hBefore :
      ∀ prior, prior ∈ before → prior.token ≠ token)
    (hToken : site.token = token)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchTestCases depth
          (before ++ site :: after)))
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++
          TypedCfg.Terminator.returnDispatchTestCases depth
            (before ++ site :: after) ++ post)
        (before ++ site :: after)) :
    ∃ caseDest,
      (pre ++
        TypedCfg.Terminator.returnDispatchTestCases depth
          (before ++ site :: after) ++ post).labelPc site.caseLabel =
        some caseDest ∧
      Assembly.Source.EventuallyWithOracle
        (pre ++
          TypedCfg.Terminator.returnDispatchTestCases depth
            (before ++ site :: after) ++ post)
        state trace
        (fun outcome =>
          match outcome with
          | .ok (.running final, finalTrace) =>
              finalTrace = trace ∧
                final.stack = front ++ token :: suffix ∧
                Assembly.SameData final state ∧
                final.pc = EvmYul.UInt256.ofNat caseDest
          | _ => False) := by
  let prefixCode :=
    TypedCfg.Terminator.returnDispatchTestCases depth before
  let siteCode := TypedCfg.Terminator.returnDispatchTest depth site
  let tailCode :=
    TypedCfg.Terminator.returnDispatchTestCases depth after
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchTestCases depth
          (before ++ site :: after) =
        prefixCode ++ siteCode ++ tailCode := by
    simp [TypedCfg.Terminator.returnDispatchTestCases, prefixCode,
      siteCode, tailCode, List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ siteCode ++ tailCode) := by
    simpa [hCodeEq] using hFits
  have hFitsAssoc :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ (siteCode ++ tailCode)) := by
    simpa [List.append_assoc] using hFitsAll
  have hPrefixFits :
      Assembly.Program.PCFitsFrom pre prefixCode :=
    Assembly.Program.PCFitsFrom.left hFitsAssoc
  have hAfterPrefixFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        (siteCode ++ tailCode) :=
    Assembly.Program.PCFitsFrom.right hFitsAssoc
  have hSiteFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode) siteCode :=
    Assembly.Program.PCFitsFrom.left hAfterPrefixFits
  rcases hResolved site (by simp) with ⟨caseDest, hCaseDest⟩
  have hPrefixResolved :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ prefixCode ++ (siteCode ++ tailCode ++ post)) before := by
    intro prior hMem
    rcases hResolved prior (by simp [hMem]) with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hPrefix :=
    returnDispatchTestCases_eventuallyWithOracle_of_all_ne
      (depth := depth) (sites := before)
      (front := front) (suffix := suffix) (token := token)
      (code := prefixCode) (pre := pre)
      (post := siteCode ++ tailCode ++ post) (state := state)
      (trace := trace)
      rfl hBound hFront hStack hBefore hPrefixFits hPc hPrefixResolved
  refine ⟨caseDest, hCaseDest, ?_⟩
  refine
    Assembly.Source.EventuallyWithOracle.bind_running
      (program :=
        pre ++
          TypedCfg.Terminator.returnDispatchTestCases depth
            (before ++ site :: after) ++ post)
      (middle := fun mid midTrace =>
        midTrace = trace ∧
          mid.stack = front ++ token :: suffix ∧
          Assembly.SameData mid state ∧
          mid.pc = (pre ++ prefixCode).pcAfter)
      ?_ ?_
  · exact Assembly.Source.EventuallyWithOracle.mono
      (by simpa [hCodeEq, List.append_assoc] using hPrefix)
      (by
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok pair =>
            rcases pair with ⟨result, midTrace⟩
            cases result with
            | halted halt => cases hOutcome
            | running mid => exact hOutcome)
  · intro mid midTrace hMid
    rcases hMid with ⟨hTrace, hStackMid, hDataMid, hPcMid⟩
    have hMidRecord :
        { mid with stack := front ++ token :: suffix } = mid := by
      rw [← hStackMid]
    have hCaseDest' :
        ((pre ++ prefixCode) ++ siteCode ++ (tailCode ++ post)).labelPc
            site.caseLabel =
          some caseDest := by
      simpa [hCodeEq, List.append_assoc] using hCaseDest
    have hSelected :=
      Assembly.StackShuffle.dispatchTest_source_exists_withOracle
        (state := mid) (front := front) (suffix := suffix)
        (token := token) (probe := site.token)
        (label := site.caseLabel) (dest := caseDest)
        (pre := pre ++ prefixCode) (post := tailCode ++ post)
        (trace := midTrace)
        (by
          simpa [siteCode, TypedCfg.Terminator.returnDispatchTest,
            hFront] using hSiteFits)
        (by simpa [hMidRecord] using hPcMid)
        (by omega)
        (by
          simpa [siteCode, TypedCfg.Terminator.returnDispatchTest,
            hFront, List.append_assoc] using hCaseDest')
    rw [hMidRecord] at hSelected
    exact Assembly.Source.EventuallyWithOracle.mono
      (by simpa [hCodeEq, siteCode,
        TypedCfg.Terminator.returnDispatchTest, hFront,
        List.append_assoc] using hSelected)
      (by
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok pair =>
            rcases pair with ⟨result, finalTrace⟩
            cases result with
            | halted halt => cases hOutcome
            | running final =>
                rcases hOutcome with
                  ⟨hFinalTrace, hStackFinal, hData, hPcFinal⟩
                exact
                  ⟨hFinalTrace.trans hTrace,
                    hStackFinal,
                    Assembly.SameData.trans
                      (by simpa [Assembly.SameData, hMidRecord] using hData)
                      hDataMid,
                    by simpa [hToken] using hPcFinal⟩)

theorem returnDispatchCase_eventuallyWithOracle
    {depth : Nat} {before after : List ReturnSite} {site : ReturnSite}
    {front suffix : List Word}
    {pre post : Assembly.Program} {state : EVMState} {trace : Trace}
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hStack : state.stack = front ++ site.token :: suffix)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after)))
    (hPc :
      state.pc =
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth before).pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedTargets
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        (.returnDispatch depth (before ++ site :: after))) :
    ∃ targetDest,
      (pre ++
        TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after) ++ post).labelPc site.target =
        some targetDest ∧
      Assembly.Source.EventuallyWithOracle
        (pre ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        state trace
        (Outcome.RunningAt targetDest
          { state with stack := front ++ suffix } trace) := by
  let prefixCode :=
    TypedCfg.Terminator.returnDispatchCases depth before
  let siteCode := TypedCfg.Terminator.returnDispatchCase depth site
  let tailCode :=
    TypedCfg.Terminator.returnDispatchCases depth after
  let cleanup := Assembly.StackShuffle.removeBuriedUnder depth
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCases depth
          (before ++ site :: after) =
        prefixCode ++ siteCode ++ tailCode := by
    simp [TypedCfg.Terminator.returnDispatchCases, prefixCode,
      siteCode, tailCode, List.append_assoc]
  have hSiteCodeEq :
      siteCode =
        [Assembly.Instr.label site.caseLabel] ++ cleanup ++
          [Assembly.Instr.jump site.target] := by
    simp [siteCode, cleanup, TypedCfg.Terminator.returnDispatchCase,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ (siteCode ++ tailCode)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hAfterPrefixFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        (siteCode ++ tailCode) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hSiteFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode) siteCode :=
    Assembly.Program.PCFitsFrom.left hAfterPrefixFits
  have hSiteFits' :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        ([Assembly.Instr.label site.caseLabel] ++ cleanup ++
          [Assembly.Instr.jump site.target]) := by
    simpa [hSiteCodeEq] using hSiteFits
  have hLabelFit : (pre ++ prefixCode).PCFits :=
    Assembly.Program.PCFitsFrom.start hSiteFits'
  have hAfterLabelFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        (cleanup ++ [Assembly.Instr.jump site.target]) := by
    simpa [List.append_assoc] using hSiteFits'.2
  have hCleanupFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        cleanup :=
    Assembly.Program.PCFitsFrom.left hAfterLabelFits
  have hJumpFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel] ++ cleanup)
        [Assembly.Instr.jump site.target] := by
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right hAfterLabelFits)
  rcases hResolved site.target
      (by
        simp [TypedCfg.Terminator.targets]) with
    ⟨targetDest, hTargetDest⟩
  have hTargetDest' :
      (pre ++ prefixCode ++ siteCode ++ tailCode ++ post).labelPc site.target =
        some targetDest := by
    simpa [hCodeEq, List.append_assoc] using hTargetDest
  let afterLabel : EVMState := state.incrPC
  have hAfterLabelPc :
      afterLabel.pc =
        (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel]).pcAfter := by
    calc
      afterLabel.pc = state.pc + EvmYul.UInt256.ofNat 1 := by
        simp [afterLabel, EvmYul.EVM.State.incrPC]
      _ = (pre ++ prefixCode).pcAfter + EvmYul.UInt256.ofNat 1 := by
        rw [hPc]
      _ =
          EvmYul.UInt256.ofNat ((pre ++ prefixCode).byteLength + 1) := by
        rw [Assembly.Program.pcAfter, Assembly.UInt256_ofNat_add]
      _ =
          (pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel]).pcAfter := by
        simp [Assembly.Program.pcAfter, Assembly.Program.byteLength_append,
          Assembly.Program.byteLength, Assembly.Instr.byteSize, Nat.add_assoc]
  have hLabelRun :
      Assembly.Source.runNResultWithOracle
          (pre ++ prefixCode ++ siteCode ++ tailCode ++ post)
          1 state trace =
        .ok (.running afterLabel, trace) := by
    rw [show
      pre ++ prefixCode ++ siteCode ++ tailCode ++ post =
        (pre ++ prefixCode) ++
          Assembly.Instr.label site.caseLabel ::
            (cleanup ++ Assembly.Instr.jump site.target :: tailCode ++ post) by
      simp [hSiteCodeEq, List.append_assoc]]
    rw [Assembly.Source.runNResultWithOracle_one_at_boundary hLabelFit hPc]
    rw [Assembly.Source.stepAtResultWithOracle_of_observer_none (by rfl)]
    simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
      Assembly.Instr.haltKind?, Assembly.Target.stepInstr, afterLabel]
    rfl
  have hAfterLabelStack :
      afterLabel.stack = front ++ site.token :: suffix := by
    simpa [afterLabel] using hStack
  refine ⟨targetDest, hTargetDest, ?_⟩
  refine
    Assembly.Source.EventuallyWithOracle.bind_running
      (program :=
        pre ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
      (middle := fun mid midTrace =>
        mid = afterLabel ∧ midTrace = trace)
      ?_ ?_
  · refine ⟨1, .ok (.running afterLabel, trace), ?_, rfl, rfl⟩
    simpa [hCodeEq, List.append_assoc] using hLabelRun
  · intro labelState labelTrace hLabelState
    rcases hLabelState with ⟨hLabelState, hLabelTrace⟩
    subst labelState
    rw [hLabelTrace]
    have hAfterLabelRecord :
        { afterLabel with stack := front ++ site.token :: suffix } =
          afterLabel := by
      rw [← hAfterLabelStack]
    have hCleanup :=
      Assembly.StackShuffle.removeBuriedUnder_source_exists_withOracle
        (state := afterLabel) (front := front) (suffix := suffix)
        (token := site.token)
        (pre :=
          pre ++ prefixCode ++ [Assembly.Instr.label site.caseLabel])
        (post := [Assembly.Instr.jump site.target] ++ tailCode ++ post)
        (trace := trace)
        (by simpa [hFront] using hCleanupFits)
        (by simpa [hAfterLabelRecord] using hAfterLabelPc)
        (by omega)
    rw [hAfterLabelRecord] at hCleanup
    refine
      Assembly.Source.EventuallyWithOracle.bind_running
        (program :=
          pre ++
            TypedCfg.Terminator.returnDispatchCases depth
              (before ++ site :: after) ++ post)
        (middle := fun cleaned cleanedTrace =>
          cleanedTrace = trace ∧
            cleaned.stack = front ++ suffix ∧
            Assembly.SameData cleaned
              { state with stack := front ++ suffix } ∧
            cleaned.pc =
              (pre ++ prefixCode ++
                [Assembly.Instr.label site.caseLabel] ++ cleanup).pcAfter)
        ?_ ?_
    · exact Assembly.Source.EventuallyWithOracle.mono
        (by
          simpa [hCodeEq, hSiteCodeEq, cleanup, hFront,
            List.append_assoc] using hCleanup)
        (by
          intro outcome hOutcome
          cases outcome with
          | error err => cases hOutcome
          | ok pair =>
              rcases pair with ⟨result, cleanedTrace⟩
              cases result with
              | halted halt => cases hOutcome
              | running cleaned =>
                  rcases hOutcome with
                    ⟨hTrace, hStackClean, hData, hPcClean⟩
                  refine ⟨hTrace, hStackClean, ?_, ?_⟩
                  · calc
                      Assembly.eraseControl cleaned =
                          Assembly.eraseControl
                            { afterLabel with stack := front ++ suffix } :=
                        hData
                      _ =
                          Assembly.eraseControl
                            { state with stack := front ++ suffix } := by
                        simp [afterLabel, Assembly.eraseControl,
                          Assembly.eraseGas, EvmYul.EVM.State.incrPC]
                  · simpa [cleanup, hFront, List.append_assoc] using hPcClean)
    · intro cleaned cleanedTrace hCleaned
      rcases hCleaned with
        ⟨hTraceClean, hStackClean, hDataClean, hPcClean⟩
      have hTargetDest'' :
          ((pre ++ prefixCode ++
              [Assembly.Instr.label site.caseLabel] ++ cleanup) ++
            [Assembly.Instr.jump site.target] ++ tailCode ++ post).labelPc
              site.target =
            some targetDest := by
        simpa [hSiteCodeEq, List.append_assoc] using hTargetDest'
      have hTargetDest''' :
          ((pre ++ prefixCode ++
              [Assembly.Instr.label site.caseLabel] ++ cleanup) ++
            Assembly.Instr.jump site.target :: tailCode ++ post).labelPc
              site.target =
            some targetDest := by
        simpa [List.append_assoc] using hTargetDest''
      refine
        ⟨1,
          .ok
            (.running (Assembly.Source.jumpPc targetDest cleaned),
              cleanedTrace),
          ?_, ?_⟩
      · let jumpPre :=
          pre ++ prefixCode ++
            [Assembly.Instr.label site.caseLabel] ++ cleanup
        have hTargetDestBase :
            (jumpPre ++
              Assembly.Instr.jump site.target :: (tailCode ++ post)).labelPc
                site.target =
              some targetDest := by
          simpa [jumpPre, List.append_assoc] using hTargetDest'''
        have hTargetDestActual :
            (pre ++
              (prefixCode ++
                Assembly.Instr.label site.caseLabel ::
                  (cleanup ++
                    Assembly.Instr.jump site.target ::
                      (tailCode ++ post)))).labelPc site.target =
              some targetDest := by
          simpa [jumpPre, List.append_assoc] using hTargetDestBase
        have hJumpRunBase :
            Assembly.Source.runNResultWithOracle
                (jumpPre ++
                  Assembly.Instr.jump site.target :: (tailCode ++ post))
                1 cleaned cleanedTrace =
              .ok
                (.running
                  (Assembly.Source.jumpPc targetDest cleaned),
                  cleanedTrace) := by
          rw [Assembly.Source.runNResultWithOracle_one_at_boundary
            (pre := jumpPre) (post := tailCode ++ post)
            (instr := Assembly.Instr.jump site.target)
            (by
              simpa [jumpPre, List.append_assoc] using
                Assembly.Program.PCFitsFrom.start hJumpFits)
            (by simpa [jumpPre, List.append_assoc] using hPcClean)]
          rw [Assembly.Source.stepAtResultWithOracle_of_observer_none (by rfl)]
          simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
            Assembly.Instr.haltKind?, hTargetDestActual,
            Assembly.Source.invalid, jumpPre, List.append_assoc]
          rfl
        simpa [jumpPre, hCodeEq, hSiteCodeEq, List.append_assoc] using
          hJumpRunBase
      · exact
          ⟨hTraceClean,
            rfl,
            Assembly.SameData.trans
              (Assembly.SameData.jumpPc targetDest cleaned)
              hDataClean⟩

theorem returnDispatch_selected_eventuallyWithOracle
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word} {target : Label}
    {code pre post : Assembly.Program} {state : EVMState} {trace : Trace}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = some token)
    (hFind : Block.ReturnSite.findTarget? token sites = some target)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolvedTargets :
      Preservation.Terminator.ResolvedTargets
        (pre ++ code ++ post)
        (.returnDispatch returnCount sites))
    (hResolvedCases :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ code ++ post) sites)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Assembly.Source.EventuallyWithOracle
      (pre ++ code ++ post) state trace
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape
          (.returnDispatch returnCount sites) state) trace) := by
  subst code
  subst returnCount
  rcases Preservation.List.getElem?_eq_some_split hGet with
    ⟨front, suffix, hStack, hFront⟩
  rcases Preservation.ReturnSite.findTarget?_eq_some_split hFind with
    ⟨before, site, after, hSites, hBefore, hToken, hTarget⟩
  subst sites
  let testCases :=
    TypedCfg.Terminator.returnDispatchTestCases depth
      (before ++ site :: after)
  let tests :=
    TypedCfg.Terminator.returnDispatchTests depth
      (before ++ site :: after)
  let cases :=
    TypedCfg.Terminator.returnDispatchCases depth
      (before ++ site :: after)
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCode depth
          (before ++ site :: after) =
        testCases ++ [Assembly.Instr.prim .invalid] ++ cases := by
    simp [TypedCfg.Terminator.returnDispatchCode,
      TypedCfg.Terminator.returnDispatchTests, testCases, tests, cases,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (testCases ++ ([Assembly.Instr.prim .invalid] ++ cases)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hTestCasesFits :
      Assembly.Program.PCFitsFrom pre testCases :=
    Assembly.Program.PCFitsFrom.left hFitsAll
  have hAfterTestCasesFits :
      Assembly.Program.PCFitsFrom (pre ++ testCases)
        ([Assembly.Instr.prim .invalid] ++ cases) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hCasesFits :
      Assembly.Program.PCFitsFrom
        (pre ++ testCases ++ [Assembly.Instr.prim .invalid]) cases := by
    simpa [List.append_assoc] using hAfterTestCasesFits.2
  have hResolvedCases' :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ testCases ++
          ([Assembly.Instr.prim .invalid] ++ cases ++ post))
        (before ++ site :: after) := by
    intro resolvedSite hMem
    rcases hResolvedCases resolvedSite hMem with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hSelected :=
    returnDispatchTestCases_eventuallyWithOracle_of_selected
      (depth := depth) (before := before) (after := after) (site := site)
      (front := front) (suffix := suffix) (token := token)
      (pre := pre)
      (post := [Assembly.Instr.prim .invalid] ++ cases ++ post)
      (state := state) (trace := trace)
      hBound hFront
      (by simpa [hStack, List.append_assoc])
      hBefore hToken
      (by simpa [testCases] using hTestCasesFits)
      hPc
      (by simpa [testCases, List.append_assoc] using hResolvedCases')
  rcases hSelected with ⟨caseDest, hCaseDest, hSelectedRun⟩
  let caseBase := pre ++ testCases ++ [Assembly.Instr.prim .invalid]
  let casePrefix :=
    TypedCfg.Terminator.returnDispatchCases depth before
  let caseTail :=
    Assembly.StackShuffle.removeBuriedUnder depth ++
      [Assembly.Instr.jump site.target] ++
      TypedCfg.Terminator.returnDispatchCases depth after ++ post
  have hProgramAtCase :
      pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post =
        (caseBase ++ casePrefix) ++
          Assembly.Instr.label site.caseLabel :: caseTail := by
    simp [hCodeEq, testCases, cases, caseBase, casePrefix, caseTail,
      TypedCfg.Terminator.returnDispatchCases,
      TypedCfg.Terminator.returnDispatchCase, List.append_assoc]
  have hInternalLabel :
      (pre ++
        TypedCfg.Terminator.returnDispatchCode depth
          (before ++ site :: after) ++ post).labelPc site.caseLabel =
        some (caseBase ++ casePrefix).byteLength := by
    rw [hProgramAtCase]
    exact
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        (caseBase ++ casePrefix) caseTail
        (by simpa [hProgramAtCase] using hLabels)
  have hCaseDestEq :
      caseDest = (caseBase ++ casePrefix).byteLength := by
    have hCaseDest' :
        (pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post).labelPc site.caseLabel =
          some caseDest := by
      simpa [hCodeEq, testCases, cases, List.append_assoc] using hCaseDest
    rw [hInternalLabel] at hCaseDest'
    exact (Option.some.inj hCaseDest').symm
  have hResolvedTargets' :
      Preservation.Terminator.ResolvedTargets
        (caseBase ++
          TypedCfg.Terminator.returnDispatchCases depth
            (before ++ site :: after) ++ post)
        (.returnDispatch depth (before ++ site :: after)) := by
    intro resolvedTarget hMem
    rcases hResolvedTargets resolvedTarget
        (by
          simpa [TypedCfg.Terminator.targets] using hMem) with
      ⟨dest, hDest⟩
    exact
      ⟨dest,
        by
          simpa [hCodeEq, testCases, cases, caseBase,
            List.append_assoc] using hDest⟩
  refine
    Assembly.Source.EventuallyWithOracle.bind_running
      (program :=
        pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post)
      (middle := fun selected selectedTrace =>
        selectedTrace = trace ∧
          selected.stack = front ++ token :: suffix ∧
          Assembly.SameData selected state ∧
          selected.pc = EvmYul.UInt256.ofNat caseDest)
      ?_ ?_
  · exact Assembly.Source.EventuallyWithOracle.mono
      (by
        simpa [hCodeEq, testCases, cases, List.append_assoc] using hSelectedRun)
      (by
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok pair =>
            rcases pair with ⟨result, selectedTrace⟩
            cases result with
            | halted halt => cases hOutcome
            | running selected => exact hOutcome)
  · intro selected selectedTrace hSelectedState
    rcases hSelectedState with
      ⟨hSelectedTrace, hSelectedStack, hSelectedData, hSelectedPc⟩
    have hCasePc :
        selected.pc = (caseBase ++ casePrefix).pcAfter := by
      rw [hSelectedPc, hCaseDestEq]
      rfl
    have hCaseRun :=
      returnDispatchCase_eventuallyWithOracle
        (depth := depth) (before := before) (after := after) (site := site)
        (front := front) (suffix := suffix)
        (pre := caseBase) (post := post) (state := selected)
        (trace := selectedTrace)
        hBound hFront
        (by simpa [hToken] using hSelectedStack)
        hCasesFits
        (by simpa [casePrefix] using hCasePc)
        hResolvedTargets'
    rcases hCaseRun with ⟨targetDest, hTargetDest, hRun⟩
    have hTargetDest' :
        (pre ++
          TypedCfg.Terminator.returnDispatchCode depth
            (before ++ site :: after) ++ post).labelPc target =
          some targetDest := by
      simpa [hTarget, hCodeEq, testCases, cases, caseBase,
        List.append_assoc] using hTargetDest
    exact Assembly.Source.EventuallyWithOracle.mono
      (by
        simpa [hCodeEq, testCases, cases, caseBase,
          List.append_assoc] using hRun)
      (by
        intro outcome hOutcome
        have hErase :
            state.stack.eraseIdx depth = front ++ suffix := by
          rw [hStack, ← hFront]
          exact Preservation.List.eraseIdx_append_at_length front suffix token
        simp [Block.runTerm, hDepth, hGet, hFind,
          Outcome.Simulates]
        have hTargetDestActual :
            (pre ++
              (TypedCfg.Terminator.returnDispatchCode depth
                (before ++ site :: after) ++ post)).labelPc target =
              some targetDest := by
          simpa [List.append_assoc] using hTargetDest'
        cases outcome with
        | error err => cases hOutcome
        | ok pair =>
            rcases pair with ⟨result, finalTrace⟩
            cases result with
            | halted halt => cases hOutcome
            | running final =>
                rcases hOutcome with
                  ⟨hFinalTrace, hPcFinal, hData⟩
                have hSelectedCleanData :
                    Assembly.SameData
                      { selected with stack := front ++ suffix }
                      { state with stack := front ++ suffix } :=
                  Assembly.eraseControl_with_stack_congr
                    hSelectedData
                exact
                  ⟨hFinalTrace.trans hSelectedTrace,
                    targetDest, hTargetDestActual, hPcFinal,
                    by
                      simpa [hErase] using
                        Assembly.SameData.trans hData hSelectedCleanData⟩)

theorem returnDispatch_unknown_token_eventuallyWithOracle
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite} {token : Word}
    {code pre post : Assembly.Program} {state : EVMState} {trace : Trace}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = some token)
    (hFind : Block.ReturnSite.findTarget? token sites = none)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolvedCases :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ code ++ post) sites) :
    Assembly.Source.EventuallyWithOracle
      (pre ++ code ++ post) state trace
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape
          (.returnDispatch returnCount sites) state) trace) := by
  subst code
  subst returnCount
  rcases Preservation.List.getElem?_eq_some_split hGet with
    ⟨front, suffix, hStack, hFront⟩
  let testCases :=
    TypedCfg.Terminator.returnDispatchTestCases depth sites
  let cases :=
    TypedCfg.Terminator.returnDispatchCases depth sites
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCode depth sites =
        testCases ++ [Assembly.Instr.prim .invalid] ++ cases := by
    simp [TypedCfg.Terminator.returnDispatchCode,
      TypedCfg.Terminator.returnDispatchTests, testCases, cases,
      List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (testCases ++ ([Assembly.Instr.prim .invalid] ++ cases)) := by
    simpa [hCodeEq, List.append_assoc] using hFits
  have hTestCasesFits :
      Assembly.Program.PCFitsFrom pre testCases :=
    Assembly.Program.PCFitsFrom.left hFitsAll
  have hAfterTestsFits :
      Assembly.Program.PCFitsFrom (pre ++ testCases)
        ([Assembly.Instr.prim .invalid] ++ cases) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hResolvedCases' :
      Preservation.Terminator.ResolvedCaseLabels
        (pre ++ testCases ++
          ([Assembly.Instr.prim .invalid] ++ cases ++ post)) sites := by
    intro site hMem
    rcases hResolvedCases site hMem with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hTests :=
    returnDispatchTestCases_eventuallyWithOracle_of_all_ne
      (depth := depth) (sites := sites)
      (front := front) (suffix := suffix) (token := token)
      (code := testCases) (pre := pre)
      (post := [Assembly.Instr.prim .invalid] ++ cases ++ post)
      (state := state) (trace := trace)
      rfl hBound hFront
      (by simpa [hStack, List.append_assoc])
      (Preservation.ReturnSite.findTarget?_eq_none_all_ne hFind)
      hTestCasesFits hPc hResolvedCases'
  refine
    Assembly.Source.EventuallyWithOracle.bind_running
      (program :=
        pre ++ TypedCfg.Terminator.returnDispatchCode depth sites ++ post)
      (middle := fun tested testedTrace =>
        testedTrace = trace ∧
          tested.stack = front ++ token :: suffix ∧
          Assembly.SameData tested state ∧
          tested.pc = (pre ++ testCases).pcAfter)
      ?_ ?_
  · exact Assembly.Source.EventuallyWithOracle.mono
      (by simpa [hCodeEq, List.append_assoc] using hTests)
      (by
        intro outcome hOutcome
        cases outcome with
        | error err => cases hOutcome
        | ok pair =>
            rcases pair with ⟨result, testedTrace⟩
            cases result with
            | halted halt => cases hOutcome
            | running tested => exact hOutcome)
  · intro tested testedTrace hTested
    rcases hTested with
      ⟨hTestedTrace, hTestedStack, hTestedData, hTestedPc⟩
    refine ⟨1, .error .InvalidInstruction, ?_, ?_⟩
    · have hInvalid :
          Assembly.Source.runNResultWithOracle
              ((pre ++ testCases) ++
                Assembly.Instr.prim .invalid :: (cases ++ post))
              1 tested testedTrace =
            .error .InvalidInstruction := by
        rw [Assembly.Source.runNResultWithOracle_one_at_boundary
          (Assembly.Program.PCFitsFrom.start hAfterTestsFits)
          hTestedPc]
        rw [Assembly.Source.stepAtResultWithOracle_of_observer_none (by rfl)]
        simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
          Assembly.Target.stepInstr, Assembly.PrimOp.step,
          Assembly.PrimOp.continuingStep?, Assembly.PrimStep.run]
        rfl
      simpa [hCodeEq, List.append_assoc] using hInvalid
    · simp [Block.runTerm, hDepth, hGet, hFind, Outcome.Simulates]
      exact ⟨.InvalidInstruction, rfl⟩

theorem returnDispatch_missing_token_eventuallyWithOracle
    {shape : Shape} {returnCount depth : Nat}
    {sites : List ReturnSite}
    {code pre post : Assembly.Program} {state : EVMState} {trace : Trace}
    (hDepth : shape.returnTokenDepth? = some depth)
    (hCount : depth = returnCount)
    (hSites : sites ≠ [])
    (hCode :
      code = TypedCfg.Terminator.returnDispatchCode depth sites)
    (hBound : depth < 16)
    (hGet : state.stack[depth]? = none)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.EventuallyWithOracle
      (pre ++ code ++ post) state trace
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape
          (.returnDispatch returnCount sites) state) trace) := by
  subst code
  subst returnCount
  cases sites with
  | nil =>
      exact (hSites rfl).elim
  | cons site rest =>
      have hLen : state.stack.length ≤ depth := by
        rw [List.getElem?_eq_none_iff] at hGet
        exact hGet
      have hDupError :
          Assembly.Target.stepInstr
              (Assembly.StackShuffle.targetInstr
                (Assembly.StackShuffle.dupInstr (depth + 1)))
              state =
            .error .StackUnderflow := by
        rw [Assembly.StackShuffle.dupInstr_step_eq_dup
          (by omega) (by omega)]
        simp [EvmYul.dup, show ¬depth + 1 ≤ state.stack.length by omega]
      have hCodeHead :
          TypedCfg.Terminator.returnDispatchCode depth (site :: rest) =
            Assembly.StackShuffle.dupInstr (depth + 1) ::
              ( [ Assembly.Instr.push site.token
                , Assembly.Instr.prim .eq
                , Assembly.Instr.jumpi site.caseLabel
                ] ++
                TypedCfg.Terminator.returnDispatchTestCases depth rest ++
                [Assembly.Instr.prim .invalid] ++
                TypedCfg.Terminator.returnDispatchCases depth (site :: rest)) := by
        simp [TypedCfg.Terminator.returnDispatchCode,
          TypedCfg.Terminator.returnDispatchTests,
          TypedCfg.Terminator.returnDispatchTestCases,
          TypedCfg.Terminator.returnDispatchTest,
          List.append_assoc]
      refine ⟨1, .error .StackUnderflow, ?_, ?_⟩
      · rw [show
          pre ++
              TypedCfg.Terminator.returnDispatchCode depth (site :: rest) ++
              post =
            pre ++
              Assembly.StackShuffle.dupInstr (depth + 1) ::
                ( [ Assembly.Instr.push site.token
                  , Assembly.Instr.prim .eq
                  , Assembly.Instr.jumpi site.caseLabel
                  ] ++
                  TypedCfg.Terminator.returnDispatchTestCases depth rest ++
                  [Assembly.Instr.prim .invalid] ++
                  TypedCfg.Terminator.returnDispatchCases depth
                    (site :: rest) ++ post) by
            rw [hCodeHead]
            simp [List.append_assoc]]
        rw [Assembly.Source.runNResultWithOracle_one_at_boundary hFits.1 hPc]
        rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
          (Assembly.StackShuffle.dupInstr_observer_none
            (n := depth + 1) (by omega) (by omega))]
        simp [Assembly.Source.stepAtResult,
          Assembly.StackShuffle.source_stepAt_eq_targetInstr
            (Assembly.StackShuffle.dupInstr_sourceLocal
              (n := depth + 1) (by omega) (by omega)),
          hDupError]
        rfl
      · simp [Block.runTerm, hDepth, hGet, Outcome.Simulates]
        exact ⟨.StackUnderflow, rfl⟩

theorem lowerAt?_eventuallyWithOracle_of_direct
    {shape : Shape} {term : TypedCfg.Terminator}
    {code pre post : Assembly.Program} {state : EVMState}
    {trace : Trace}
    (hDirect : Preservation.Terminator.Direct term)
    (hLower : term.lowerAt? shape = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedTargets
        (pre ++ code ++ post) term) :
    Assembly.Source.EventuallyWithOracle
      (pre ++ code ++ post) state trace
      (Outcome.Simulates (pre ++ code ++ post)
        (TypedCfg.Block.runTerm shape term state) trace) := by
  cases term with
  | fallthrough next =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved next (by simp [TypedCfg.Terminator.targets]) with
        ⟨dest, hDest⟩
      have hDest' :
          (pre ++ Assembly.Instr.jump next :: post).labelPc next =
            some dest := by
        simpa using hDest
      refine
        ⟨1,
          .ok (.running (Assembly.Source.jumpPc dest state), trace),
          ?_, ?_⟩
      · rw [show
          pre ++ [Assembly.Instr.jump next] ++ post =
            pre ++ Assembly.Instr.jump next :: post by simp]
        rw [Assembly.Source.runNResultWithOracle_one_at_boundary
          hFits.1 hPc]
        rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
          (by rfl)]
        simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
          Assembly.Instr.haltKind?, hDest', Assembly.Source.invalid,
          Except.map]
      · exact
          ⟨rfl, dest, hDest, rfl,
            Assembly.SameData.jumpPc dest state⟩
  | jump target =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved target (by simp [TypedCfg.Terminator.targets]) with
        ⟨dest, hDest⟩
      have hDest' :
          (pre ++ Assembly.Instr.jump target :: post).labelPc target =
            some dest := by
        simpa using hDest
      refine
        ⟨1,
          .ok (.running (Assembly.Source.jumpPc dest state), trace),
          ?_, ?_⟩
      · rw [show
          pre ++ [Assembly.Instr.jump target] ++ post =
            pre ++ Assembly.Instr.jump target :: post by simp]
        rw [Assembly.Source.runNResultWithOracle_one_at_boundary
          hFits.1 hPc]
        rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
          (by rfl)]
        simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
          Assembly.Instr.haltKind?, hDest', Assembly.Source.invalid,
          Except.map]
      · exact
          ⟨rfl, dest, hDest, rfl,
            Assembly.SameData.jumpPc dest state⟩
  | jumpi target next =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      rcases hResolved target (by simp [TypedCfg.Terminator.targets]) with
        ⟨targetDest, hTargetDest⟩
      rcases hResolved next (by simp [TypedCfg.Terminator.targets]) with
        ⟨nextDest, hNextDest⟩
      have hTargetDest' :
          (pre ++ Assembly.Instr.jumpi target ::
              Assembly.Instr.jump next :: post).labelPc target =
            some targetDest := by
        simpa using hTargetDest
      have hNextDest' :
          (pre ++ Assembly.Instr.jumpi target ::
              Assembly.Instr.jump next :: post).labelPc next =
            some nextDest := by
        simpa using hNextDest
      cases hPop : state.stack.pop with
      | none =>
          refine ⟨1, .error .StackUnderflow, ?_, ?_⟩
          · rw [show
              pre ++
                    [Assembly.Instr.jumpi target,
                      Assembly.Instr.jump next] ++ post =
                  pre ++ Assembly.Instr.jumpi target ::
                    Assembly.Instr.jump next :: post by simp]
            rw [Assembly.Source.runNResultWithOracle_one_at_boundary
              hFits.1 hPc]
            rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
              (by rfl)]
            simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
              Assembly.Instr.haltKind?, hTargetDest', hPop,
              Assembly.Source.invalid, Bind.bind, Except.bind, Except.map,
              Pure.pure, Except.pure]
          · simp [TypedCfg.Block.runTerm, hPop, Outcome.Simulates,
              Preservation.Outcome.Simulates]
      | some popResult =>
          rcases popResult with ⟨stack, cond⟩
          let popped : EVMState := { state with stack := stack }
          by_cases hZero : cond = EvmYul.UInt256.ofNat 0
          · subst cond
            let mid : EVMState :=
              { popped with
                pc := Assembly.Source.jumpiFallthroughPc state }
            have hMidPc :
                mid.pc =
                  (pre ++ [Assembly.Instr.jumpi target]).pcAfter := by
              calc
                mid.pc =
                    (state.pc +
                      EvmYul.UInt256.ofNat Assembly.Instr.push32Size) +
                        EvmYul.UInt256.ofNat 1 := rfl
                _ =
                    (pre.pcAfter +
                      EvmYul.UInt256.ofNat Assembly.Instr.push32Size) +
                        EvmYul.UInt256.ofNat 1 := by
                      rw [hPc]
                _ =
                    pre.pcAfter +
                      (EvmYul.UInt256.ofNat Assembly.Instr.push32Size +
                        EvmYul.UInt256.ofNat 1) := by
                      exact Preservation.uint256_add_assoc _ _ _
                _ =
                    pre.pcAfter +
                      EvmYul.UInt256.ofNat
                        (Assembly.Instr.push32Size + 1) := by
                      rw [Assembly.UInt256_ofNat_add]
                _ =
                    (pre ++ [Assembly.Instr.jumpi target]).pcAfter := by
                      simpa [Assembly.Instr.byteSize,
                        Assembly.Instr.jumpSize] using
                          (Assembly.Program.pcAfter_snoc pre
                            (Assembly.Instr.jumpi target)).symm
            have hFirst :
                Assembly.Source.runNResultWithOracle
                    (pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++ post)
                    1 state trace =
                  .ok (.running mid, trace) := by
              rw [show
                  pre ++
                        [Assembly.Instr.jumpi target,
                          Assembly.Instr.jump next] ++ post =
                      pre ++ Assembly.Instr.jumpi target ::
                        Assembly.Instr.jump next :: post by simp]
              rw [Assembly.Source.runNResultWithOracle_one_at_boundary
                hFits.1 hPc]
              rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
                (by rfl)]
              simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
                Assembly.Instr.haltKind?, hTargetDest', hPop,
                Assembly.Source.invalid, mid, popped,
                Preservation.uint256_bne_zero_self, Except.map]
            have hSecond :
                Assembly.Source.runNResultWithOracle
                    (pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++ post)
                    1 mid trace =
                  .ok
                    (.running
                      (Assembly.Source.jumpPc nextDest popped),
                      trace) := by
              rw [show
                  pre ++
                        [Assembly.Instr.jumpi target,
                          Assembly.Instr.jump next] ++ post =
                      (pre ++ [Assembly.Instr.jumpi target]) ++
                        Assembly.Instr.jump next :: post by simp]
              rw [Assembly.Source.runNResultWithOracle_one_at_boundary
                hFits.2.1 hMidPc]
              rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
                (by rfl)]
              simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
                Assembly.Instr.haltKind?, hNextDest',
                Assembly.Source.invalid, mid, popped,
                Assembly.Source.jumpPc, Except.map]
            refine
              ⟨2,
                .ok
                  (.running
                    (Assembly.Source.jumpPc nextDest popped),
                    trace),
                ?_, ?_⟩
            · exact
                Assembly.Source.runNResultWithOracle_running_bind
                  hFirst hSecond
            · simp [TypedCfg.Block.runTerm, hPop, popped,
                Outcome.Simulates, Preservation.Outcome.Simulates]
              exact
                ⟨nextDest, hNextDest', rfl,
                  Assembly.SameData.jumpPc nextDest popped⟩
          · have hBne :
                (cond != EvmYul.UInt256.ofNat 0) = true :=
              Preservation.uint256_bne_zero_of_ne cond hZero
            refine
              ⟨1,
                .ok
                  (.running
                    (Assembly.Source.jumpPc targetDest popped),
                    trace),
                ?_, ?_⟩
            · rw [show
                pre ++
                      [Assembly.Instr.jumpi target,
                        Assembly.Instr.jump next] ++ post =
                    pre ++ Assembly.Instr.jumpi target ::
                      Assembly.Instr.jump next :: post by simp]
              rw [Assembly.Source.runNResultWithOracle_one_at_boundary
                hFits.1 hPc]
              rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
                (by rfl)]
              simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
                Assembly.Instr.haltKind?, hTargetDest', hPop, hBne,
                Assembly.Source.invalid, popped,
                Assembly.Source.jumpPc, Except.map]
            · simp [TypedCfg.Block.runTerm, hPop, hZero, popped,
                Outcome.Simulates, Preservation.Outcome.Simulates]
              exact
                ⟨targetDest, hTargetDest', rfl,
                  Assembly.SameData.jumpPc targetDest popped⟩
  | returnDispatch _returnCount _sites =>
      simp [Preservation.Terminator.Direct] at hDirect
  | halt kind =>
      cases kind with
      | stop =>
          simp [TypedCfg.Terminator.lowerAt?] at hLower
          subst code
          refine
            ⟨1,
              (Assembly.Target.stepInstrResult (.prim .stop) state).map
                (fun result => (result, trace)),
              ?_, ?_⟩
          · rw [show
              pre ++ [Assembly.Instr.prim .stop] ++ post =
                pre ++ Assembly.Instr.prim .stop :: post by simp]
            rw [Assembly.Source.runNResultWithOracle_one_at_boundary
              hFits.1 hPc]
            rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
              (by rfl)]
            simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
              Assembly.Target.stepInstrResult,
              Assembly.Instr.haltKind?,
              Assembly.TargetInstr.haltKind?]
          · cases hStep :
                Assembly.Target.stepInstrResult (.prim .stop) state <;>
              simp [Outcome.Simulates,
                Preservation.Outcome.Simulates,
                TypedCfg.Block.runTerm, Assembly.HaltKind.toPrimOp,
                hStep, Except.map]
      | «return» =>
          simp [TypedCfg.Terminator.lowerAt?] at hLower
          subst code
          refine
            ⟨1,
              (Assembly.Target.stepInstrResult (.prim .return) state).map
                (fun result => (result, trace)),
              ?_, ?_⟩
          · rw [show
              pre ++ [Assembly.Instr.prim .return] ++ post =
                pre ++ Assembly.Instr.prim .return :: post by simp]
            rw [Assembly.Source.runNResultWithOracle_one_at_boundary
              hFits.1 hPc]
            rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
              (by rfl)]
            simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
              Assembly.Target.stepInstrResult,
              Assembly.Instr.haltKind?,
              Assembly.TargetInstr.haltKind?]
          · cases hStep :
                Assembly.Target.stepInstrResult (.prim .return) state <;>
              simp [Outcome.Simulates,
                Preservation.Outcome.Simulates,
                TypedCfg.Block.runTerm, Assembly.HaltKind.toPrimOp,
                hStep, Except.map]
      | revert =>
          simp [TypedCfg.Terminator.lowerAt?] at hLower
          subst code
          refine
            ⟨1,
              (Assembly.Target.stepInstrResult (.prim .revert) state).map
                (fun result => (result, trace)),
              ?_, ?_⟩
          · rw [show
              pre ++ [Assembly.Instr.prim .revert] ++ post =
                pre ++ Assembly.Instr.prim .revert :: post by simp]
            rw [Assembly.Source.runNResultWithOracle_one_at_boundary
              hFits.1 hPc]
            rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
              (by rfl)]
            simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
              Assembly.Target.stepInstrResult,
              Assembly.Instr.haltKind?,
              Assembly.TargetInstr.haltKind?]
          · cases hStep :
                Assembly.Target.stepInstrResult (.prim .revert) state <;>
              simp [Outcome.Simulates,
                Preservation.Outcome.Simulates,
                TypedCfg.Block.runTerm, Assembly.HaltKind.toPrimOp,
                hStep, Except.map]
      | selfdestruct =>
          simp [TypedCfg.Terminator.lowerAt?] at hLower
          subst code
          refine
            ⟨1,
              (Assembly.Target.stepInstrResult
                (.prim .selfdestruct) state).map
                  (fun result => (result, trace)),
              ?_, ?_⟩
          · rw [show
              pre ++ [Assembly.Instr.prim .selfdestruct] ++ post =
                pre ++ Assembly.Instr.prim .selfdestruct :: post by simp]
            rw [Assembly.Source.runNResultWithOracle_one_at_boundary
              hFits.1 hPc]
            rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
              (by rfl)]
            simp [Assembly.Source.stepAtResult, Assembly.Source.stepAt,
              Assembly.Target.stepInstrResult,
              Assembly.Instr.haltKind?,
              Assembly.TargetInstr.haltKind?]
          · cases hStep :
                Assembly.Target.stepInstrResult
                  (.prim .selfdestruct) state <;>
              simp [Outcome.Simulates,
                Preservation.Outcome.Simulates,
                TypedCfg.Block.runTerm, Assembly.HaltKind.toPrimOp,
                hStep, Except.map]
  | invalid =>
      simp [TypedCfg.Terminator.lowerAt?] at hLower
      subst code
      refine ⟨1, .error .InvalidInstruction, ?_, ?_⟩
      · rw [show
          pre ++ [Assembly.Instr.prim .invalid] ++ post =
            pre ++ Assembly.Instr.prim .invalid :: post by simp]
        rw [Assembly.Source.runNResultWithOracle_one_at_boundary
          hFits.1 hPc]
        rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
          (by rfl)]
        simp only [Assembly.Source.stepAtResult,
          Assembly.Source.stepAt, Assembly.Target.stepInstr]
        rw [Assembly.PrimOp.step_eq_continuingStep_run (by rfl)]
        rfl
      · exact ⟨.InvalidInstruction, rfl⟩

theorem lowerAt?_eventuallyWithOracle
    {shape : Shape} {term : TypedCfg.Terminator}
    {code pre post : Assembly.Program} {state : EVMState}
    {trace : Trace}
    (hLower : term.lowerAt? shape = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedControl
        (pre ++ code ++ post) term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Assembly.Source.EventuallyWithOracle
      (pre ++ code ++ post) state trace
      (Outcome.Simulates (pre ++ code ++ post)
        (Block.runTerm shape term state) trace) := by
  cases term with
  | fallthrough next =>
      exact lowerAt?_eventuallyWithOracle_of_direct
        (term := .fallthrough next)
        (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | jump target =>
      exact lowerAt?_eventuallyWithOracle_of_direct
        (term := .jump target)
        (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | jumpi target next =>
      exact lowerAt?_eventuallyWithOracle_of_direct
        (term := .jumpi target next)
        (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | halt kind =>
      exact lowerAt?_eventuallyWithOracle_of_direct
        (term := .halt kind)
        (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | invalid =>
      exact lowerAt?_eventuallyWithOracle_of_direct
        (term := .invalid)
        (by simp [Preservation.Terminator.Direct])
        hLower hFits hPc hResolved.1
  | returnDispatch returnCount sites =>
      cases hDepth : shape.returnTokenDepth? with
      | none =>
          simp [TypedCfg.Terminator.lowerAt?, hDepth] at hLower
      | some depth =>
          by_cases hBound : depth < 16
          · have hFacts :
                (sites ≠ [] ∧ depth = returnCount) ∧
                  TypedCfg.Terminator.returnDispatchCode depth sites = code := by
              simpa [TypedCfg.Terminator.lowerAt?, hDepth,
                TypedCfg.Terminator.returnDispatchCode?, hBound] using hLower
            have hGood : sites ≠ [] ∧ depth = returnCount := hFacts.1
            have hCodeEq :
                code =
                  TypedCfg.Terminator.returnDispatchCode depth sites :=
              hFacts.2.symm
            have hResolvedCases :
                Preservation.Terminator.ResolvedCaseLabels
                  (pre ++ code ++ post) sites := by
              intro site hMem
              exact hResolved.2 site.caseLabel
                (by
                  simp only [TypedCfg.Terminator.definedLabels]
                  exact List.mem_map.mpr ⟨site, hMem, rfl⟩)
            cases hGet : state.stack[depth]? with
            | none =>
                exact returnDispatch_missing_token_eventuallyWithOracle
                  hDepth hGood.2 hGood.1 hCodeEq hBound hGet
                  hFits hPc
            | some token =>
                cases hFind :
                    Block.ReturnSite.findTarget? token sites with
                | none =>
                    exact returnDispatch_unknown_token_eventuallyWithOracle
                      hDepth hGood.2 hCodeEq hBound hGet hFind
                      hFits hPc hResolvedCases
                | some target =>
                    exact returnDispatch_selected_eventuallyWithOracle
                      hDepth hGood.2 hCodeEq hBound hGet hFind
                      hFits hPc hResolved.1 hResolvedCases hLabels
          · simp [TypedCfg.Terminator.lowerAt?, hDepth,
              TypedCfg.Terminator.returnDispatchCode?, hBound] at hLower

end Terminator

namespace Block

def RunSimulates (program : Assembly.Program) :
    Except EVMException (TypedCfg.Outcome × Trace) →
      Assembly.Source.OracleExecutionOutcome → Prop
  | .error err, outcome => outcome = .error err
  | .ok (sourceOutcome, trace), outcome =>
      Outcome.Simulates program sourceOutcome trace outcome

theorem runBody_output_of_lowerBodyFrom?
    {body : List TypedCfg.Instr} {shape output runOutput : Shape}
    {code : Assembly.Program} {state final : EVMState}
    {trace trace' : Trace}
    (hLower :
      TypedCfg.Block.lowerBodyFrom? body shape = some (code, output))
    (hRun :
      ObserverSemantics.Block.runBody body shape state trace =
        .ok ((final, runOutput), trace')) :
    runOutput = output := by
  induction body generalizing
      shape output runOutput code state final trace trace' with
  | nil =>
      simp [TypedCfg.Block.lowerBodyFrom?,
        ObserverSemantics.Block.runBody_nil] at hLower hRun
      exact hRun.1.2.symm.trans hLower.2
  | cons instr rest ih =>
      unfold TypedCfg.Block.lowerBodyFrom? at hLower
      cases hHead : instr.lowerAt? shape with
      | none =>
          simp [hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, headOutput⟩
          cases hTail :
              TypedCfg.Block.lowerBodyFrom? rest headOutput with
          | none =>
              simp [hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailOutput⟩
              simp [hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hType :
                  instr.type? shape = some headOutput :=
                Preservation.Instr.type?_eq_some_of_lowerAt? hHead
              rw [ObserverSemantics.Block.runBody_cons] at hRun
              unfold ObserverSemantics.Instr.runAt at hRun
              rw [hType] at hRun
              cases hHeadRun :
                  ObserverSemantics.Instr.runState
                    instr shape state trace with
              | error err =>
                  simp [hHeadRun, Bind.bind, Except.bind] at hRun
              | ok pair =>
                  rcases pair with ⟨mid, traceMid⟩
                  simp [hHeadRun, Bind.bind, Except.bind] at hRun
                  exact ih hTail hRun

theorem runBody_pc_of_lowerBodyFrom?
    {body : List TypedCfg.Instr} {shape output : Shape}
    {code : Assembly.Program} {state final : EVMState}
    {trace trace' : Trace}
    (hLower :
      TypedCfg.Block.lowerBodyFrom? body shape = some (code, output))
    (hRun :
      ObserverSemantics.Block.runBody body shape state trace =
        .ok ((final, output), trace')) :
    final.pc =
      state.pc + EvmYul.UInt256.ofNat code.byteLength := by
  induction body generalizing
      shape code output state final trace trace' with
  | nil =>
      simp [TypedCfg.Block.lowerBodyFrom?,
        ObserverSemantics.Block.runBody_nil] at hLower hRun
      rcases hLower with ⟨rfl, rfl⟩
      obtain ⟨⟨hState, _hShape⟩, _hTrace⟩ := hRun
      subst final
      exact (Preservation.uint256_add_zero state.pc).symm
  | cons instr rest ih =>
      unfold TypedCfg.Block.lowerBodyFrom? at hLower
      cases hHead : instr.lowerAt? shape with
      | none =>
          simp [hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, headOutput⟩
          cases hTail :
              TypedCfg.Block.lowerBodyFrom? rest headOutput with
          | none =>
              simp [hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailOutput⟩
              simp [hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hType :
                  instr.type? shape = some headOutput :=
                Preservation.Instr.type?_eq_some_of_lowerAt? hHead
              rw [ObserverSemantics.Block.runBody_cons] at hRun
              unfold ObserverSemantics.Instr.runAt at hRun
              rw [hType] at hRun
              cases hHeadRun :
                  ObserverSemantics.Instr.runState
                    instr shape state trace with
              | error err =>
                  simp [hHeadRun, Bind.bind, Except.bind] at hRun
              | ok pair =>
                  rcases pair with ⟨mid, traceMid⟩
                  simp [hHeadRun, Bind.bind, Except.bind] at hRun
                  have hTailPc :=
                    ih (shape := headOutput) (code := tail)
                      (output := tailOutput) (state := mid)
                      (final := final) (trace := traceMid)
                      (trace' := trace') hTail hRun
                  calc
                    final.pc =
                        mid.pc +
                          EvmYul.UInt256.ofNat tail.byteLength :=
                      hTailPc
                    _ =
                        (state.pc +
                          EvmYul.UInt256.ofNat head.byteLength) +
                            EvmYul.UInt256.ofNat tail.byteLength := by
                      rw [ObserverSemantics.Instr.runState_pc_of_lowerAt
                        hHead hHeadRun]
                    _ =
                        state.pc +
                          (EvmYul.UInt256.ofNat head.byteLength +
                            EvmYul.UInt256.ofNat tail.byteLength) := by
                      exact Preservation.uint256_add_assoc _ _ _
                    _ =
                        state.pc +
                          EvmYul.UInt256.ofNat
                            (head.byteLength + tail.byteLength) := by
                      rw [Assembly.UInt256_ofNat_add]
                    _ =
                        state.pc +
                          EvmYul.UInt256.ofNat
                            (head ++ tail).byteLength := by
                      simp [Assembly.Program.byteLength_append]

theorem lowerBodyFrom?_source_runNResultWithOracle
    {body : List TypedCfg.Instr} {shape output : Shape}
    {code pre post : Assembly.Program} {state : EVMState}
    {trace : Trace}
    (hLower :
      TypedCfg.Block.lowerBodyFrom? body shape = some (code, output))
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.Source.runNResultWithOracle
        (pre ++ code ++ post) code.length state trace =
      (ObserverSemantics.Block.runBody body shape state trace).map
        (fun result =>
          (Assembly.StepResult.running result.1.1, result.2)) := by
  induction body generalizing shape code output pre state trace with
  | nil =>
      simp [TypedCfg.Block.lowerBodyFrom?] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      rfl
  | cons instr rest ih =>
      unfold TypedCfg.Block.lowerBodyFrom? at hLower
      cases hHead : instr.lowerAt? shape with
      | none =>
          simp [hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨head, headOutput⟩
          cases hTail :
              TypedCfg.Block.lowerBodyFrom? rest headOutput with
          | none =>
              simp [hHead, hTail] at hLower
          | some tailResult =>
              rcases tailResult with ⟨tail, tailOutput⟩
              simp [hHead, hTail] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              have hType :
                  instr.type? shape = some headOutput :=
                Preservation.Instr.type?_eq_some_of_lowerAt? hHead
              have hHeadFits :
                  Assembly.Program.PCFitsFrom pre head :=
                Assembly.Program.PCFitsFrom.left hFits
              have hTailFits :
                  Assembly.Program.PCFitsFrom (pre ++ head) tail :=
                Assembly.Program.PCFitsFrom.right hFits
              have hHeadRun :=
                Instr.lowerAt_source_runNResultWithOracle
                  (post := tail ++ post) (trace := trace)
                  hHead hHeadFits hPc
              rw [List.length_append,
                Assembly.Source.runNResultWithOracle_add]
              rw [show
                Assembly.Source.runNResultWithOracle
                    (pre ++ (head ++ tail) ++ post)
                    head.length state trace =
                  (ObserverSemantics.Instr.runAt
                    instr shape state trace).map
                      (fun result =>
                        (Assembly.StepResult.running result.1.1,
                          result.2)) by
                simpa [List.append_assoc] using hHeadRun]
              cases hRunState :
                  ObserverSemantics.Instr.runState
                    instr shape state trace with
              | error err =>
                  simp [ObserverSemantics.Instr.runAt,
                    ObserverSemantics.Block.runBody_cons, hType, hRunState,
                    Bind.bind, Except.bind, Except.map]
              | ok runPair =>
                  rcases runPair with ⟨mid, traceMid⟩
                  have hMidPc :
                      mid.pc = (pre ++ head).pcAfter := by
                    calc
                      mid.pc =
                          state.pc +
                            EvmYul.UInt256.ofNat head.byteLength :=
                        ObserverSemantics.Instr.runState_pc_of_lowerAt
                          hHead hRunState
                      _ =
                          pre.pcAfter +
                            EvmYul.UInt256.ofNat head.byteLength := by
                        rw [hPc]
                      _ = (pre ++ head).pcAfter := by
                        exact
                          (Assembly.Program.pcAfter_append
                            pre head).symm
                  have hTailRun :=
                    ih (shape := headOutput) (pre := pre ++ head)
                      (state := mid) (trace := traceMid)
                      hTail hTailFits hMidPc
                  simpa [List.append_assoc,
                    ObserverSemantics.Block.runBody_cons,
                    ObserverSemantics.Instr.runAt, hType, hRunState,
                    Bind.bind, Except.bind, Except.map] using hTailRun

theorem lower?_positiveEventuallyWithOracle
    {block : TypedCfg.Block} {code pre post : Assembly.Program}
    {state : EVMState} {trace : Trace}
    (hLower : block.lower? = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedControl
        (pre ++ code ++ post) block.term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    PositiveEventually
      (pre ++ code ++ post) state trace
      (RunSimulates (pre ++ code ++ post)
        (ObserverSemantics.Block.run block state.incrPC trace)) := by
  unfold TypedCfg.Block.lower? at hLower
  cases hBody :
      TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨body, output⟩
      by_cases hOutput : output = block.output
      · subst output
        cases hTerm : block.term.lowerAt? block.output with
        | none =>
            simp [hBody, hTerm] at hLower
        | some term =>
            simp [hBody, hTerm] at hLower
            subst code
            let program :=
              pre ++
                (Assembly.Instr.label block.label :: body ++ term) ++
                  post
            let entry := state.incrPC
            have hLabelRun :
                Assembly.Source.runNResultWithOracle
                    program 1 state trace =
                  .ok (.running entry, trace) := by
              have hRun :=
                Assembly.Source.runNResultWithOracle_one_at_boundary
                  (pre := pre)
                  (post := (body ++ term) ++ post)
                  (instr := Assembly.Instr.label block.label)
                  (trace := trace) hFits.1 hPc
              rw [Assembly.Source.stepAtResultWithOracle_of_observer_none
                (by rfl)] at hRun
              simpa [program, entry, List.append_assoc,
                Assembly.Source.stepAtResult, Assembly.Source.stepAt,
                Assembly.Target.stepInstr, Except.map] using hRun
            have hEntryPc :
                entry.pc =
                  (pre ++ [Assembly.Instr.label block.label]).pcAfter := by
              calc
                entry.pc =
                    state.pc + EvmYul.UInt256.ofNat 1 := rfl
                _ =
                    pre.pcAfter + EvmYul.UInt256.ofNat 1 := by
                  rw [hPc]
                _ =
                    (pre ++
                      [Assembly.Instr.label block.label]).pcAfter := by
                  simp [Assembly.Program.pcAfter,
                    Assembly.Program.byteLength_append,
                    Assembly.Program.byteLength,
                    Assembly.Instr.byteSize,
                    Assembly.UInt256_ofNat_add]
            have hBodyFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label]) body :=
              Assembly.Program.PCFitsFrom.left hFits.2
            have hTermFits :
                Assembly.Program.PCFitsFrom
                  (pre ++ [Assembly.Instr.label block.label] ++ body)
                  term := by
              simpa [List.append_assoc] using
                Assembly.Program.PCFitsFrom.right hFits.2
            have hBodyRun :=
              lowerBodyFrom?_source_runNResultWithOracle
                (pre := pre ++ [Assembly.Instr.label block.label])
                (post := term ++ post) (trace := trace)
                hBody hBodyFits hEntryPc
            have hBodyRun' :
                Assembly.Source.runNResultWithOracle
                    program body.length entry trace =
                  (ObserverSemantics.Block.runBody
                    block.body block.input entry trace).map
                      (fun result =>
                        (Assembly.StepResult.running result.1.1,
                          result.2)) := by
              simpa [program, List.append_assoc] using hBodyRun
            have hAfterLabel :
                Assembly.Source.EventuallyWithOracle program entry trace
                  (RunSimulates program
                    (ObserverSemantics.Block.run
                      block entry trace)) := by
              cases hRunBody :
                  ObserverSemantics.Block.runBody
                    block.body block.input entry trace with
              | error err =>
                  refine ⟨body.length, .error err, ?_, ?_⟩
                  · simpa [hRunBody, Except.map] using hBodyRun'
                  · simp [RunSimulates, ObserverSemantics.Block.run,
                      hRunBody, Bind.bind, Except.bind]
              | ok runPair =>
                  rcases runPair with ⟨stateShape, traceMid⟩
                  rcases stateShape with ⟨mid, bodyOutput⟩
                  have hBodyOutput : bodyOutput = block.output :=
                    runBody_output_of_lowerBodyFrom? hBody hRunBody
                  subst bodyOutput
                  have hBodyRunning :
                      Assembly.Source.runNResultWithOracle
                          program body.length entry trace =
                        .ok (.running mid, traceMid) := by
                    simpa [hRunBody] using hBodyRun'
                  have hMidPc :
                      mid.pc =
                        (pre ++ [Assembly.Instr.label block.label] ++
                          body).pcAfter := by
                    calc
                      mid.pc =
                          entry.pc +
                            EvmYul.UInt256.ofNat body.byteLength :=
                        runBody_pc_of_lowerBodyFrom? hBody hRunBody
                      _ =
                          (pre ++
                            [Assembly.Instr.label block.label]).pcAfter +
                              EvmYul.UInt256.ofNat body.byteLength := by
                        rw [hEntryPc]
                      _ =
                          (pre ++ [Assembly.Instr.label block.label] ++
                            body).pcAfter := by
                        exact
                          (Assembly.Program.pcAfter_append
                            (pre ++
                              [Assembly.Instr.label block.label])
                            body).symm
                  have hTermRun :
                      Assembly.Source.EventuallyWithOracle program
                        mid traceMid
                        (Outcome.Simulates program
                          (TypedCfg.Block.runTerm
                            block.output block.term mid) traceMid) := by
                    have hRun :=
                      Terminator.lowerAt?_eventuallyWithOracle
                        (pre :=
                          pre ++
                            [Assembly.Instr.label block.label] ++ body)
                        (post := post) (trace := traceMid)
                        hTerm hTermFits hMidPc
                        (by
                          simpa [program, List.append_assoc] using
                            hResolved)
                        (by
                          simpa [program, List.append_assoc] using
                            hLabels)
                    simpa [program, List.append_assoc] using hRun
                  have hBodyThenTerm :
                      Assembly.Source.EventuallyWithOracle program
                        entry trace
                        (Outcome.Simulates program
                          (TypedCfg.Block.runTerm
                            block.output block.term mid) traceMid) :=
                    Assembly.Source.EventuallyWithOracle.bind_running
                      (middle := fun current currentTrace =>
                        current = mid ∧ currentTrace = traceMid)
                      ⟨body.length, .ok (.running mid, traceMid),
                        hBodyRunning, rfl, rfl⟩
                      (by
                        intro current currentTrace hCurrent
                        rcases hCurrent with ⟨rfl, rfl⟩
                        exact hTermRun)
                  simpa [RunSimulates, ObserverSemantics.Block.run,
                    hRunBody, Bind.bind, Except.bind] using
                      hBodyThenTerm
            rcases hAfterLabel with
              ⟨tailFuel, outcome, hTailRun, hOutcome⟩
            refine
              ⟨1 + tailFuel, outcome, by omega, ?_, ?_⟩
            · rw [Assembly.Source.runNResultWithOracle_add]
              rw [show
                Assembly.Source.runNResultWithOracle
                    (pre ++
                      Assembly.Instr.label block.label ::
                        (body ++ term) ++ post)
                    1 state trace =
                  .ok (.running entry, trace) by
                    simpa [program, List.append_assoc] using hLabelRun]
              simpa [program, List.append_assoc] using hTailRun
            · simpa [program, entry] using hOutcome
      · simp [hBody, hOutput] at hLower

theorem lower?_eventuallyWithOracle
    {block : TypedCfg.Block} {code pre post : Assembly.Program}
    {state : EVMState} {trace : Trace}
    (hLower : block.lower? = some code)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter)
    (hResolved :
      Preservation.Terminator.ResolvedControl
        (pre ++ code ++ post) block.term)
    (hLabels : ((pre ++ code ++ post).labels).Nodup) :
    Assembly.Source.EventuallyWithOracle
      (pre ++ code ++ post) state trace
      (RunSimulates (pre ++ code ++ post)
        (ObserverSemantics.Block.run block state.incrPC trace)) :=
  PositiveEventually.eventually
    (lower?_positiveEventuallyWithOracle
      hLower hFits hPc hResolved hLabels)

end Block

namespace Program

def StepAccountsForHalt
    (target : Assembly.Program) (initial : EVMState) (initialTrace : Trace)
    (fullFuel : Nat) (halt : Assembly.Halt) (traceOut : Trace) :
    Except EVMException (TypedCfg.Outcome × Trace) → Prop
  | .error _ => False
  | .ok (sourceOutcome, sourceTrace) =>
      match sourceOutcome with
      | .fallthrough source =>
          ∃ prefixFuel targetState,
            0 < prefixFuel ∧
              prefixFuel < fullFuel ∧
              Assembly.Source.runNResultWithOracle
                  target prefixFuel initial initialTrace =
                .ok (.running targetState, sourceTrace) ∧
              Assembly.SameData targetState source
      | .jump next source =>
          ∃ prefixFuel targetState dest,
            0 < prefixFuel ∧
              prefixFuel < fullFuel ∧
              Assembly.Source.runNResultWithOracle
                  target prefixFuel initial initialTrace =
                .ok (.running targetState, sourceTrace) ∧
              target.labelPc next = some dest ∧
              targetState.pc = EvmYul.UInt256.ofNat dest ∧
              Assembly.SameData targetState source
      | .returnDispatch source =>
          ∃ prefixFuel targetState,
            0 < prefixFuel ∧
              prefixFuel < fullFuel ∧
              Assembly.Source.runNResultWithOracle
                  target prefixFuel initial initialTrace =
                .ok (.running targetState, sourceTrace) ∧
              Assembly.SameData targetState source
      | .halt kind source =>
          sourceTrace = traceOut ∧
            Assembly.Target.stepInstrResult
                (.prim kind.toPrimOp) source =
              .ok (.halted halt)
      | .invalid _ => False

theorem lower?_step_positiveEventuallyWithOracle
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : EVMState} {entryPc : Nat} {trace : Trace}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    PositiveEventually target state trace
      (Block.RunSimulates target
        (ObserverSemantics.Program.step
          program label state.incrPC trace)) := by
  rcases
      TypedCfg.Program.lower?_fragment_of_findBlock?
        hLower hFind with
    ⟨fragment⟩
  have hBlockLabel : block.label = label := by
    have hFound :
        (block.label == label) = true :=
      @List.find?_some TypedCfg.Block
        (fun candidate : TypedCfg.Block =>
          candidate.label == label)
        block program.blocks hFind
    exact beq_iff_eq.mp hFound
  subst label
  have hCodeFits :
      Assembly.Program.PCFitsFrom fragment.pre fragment.code := by
    apply Assembly.Program.PCFitsFrom.of_append
    rw [← fragment.target_eq]
    exact hFits
  have hResolved :
      Preservation.Terminator.ResolvedControl target block.term := by
    constructor
    · intro symbolic hSymbolic
      rcases
          TypedCfg.Block.target_instr_mem_of_lower?
            fragment.lower hSymbolic with
        ⟨instr, hInstr, hInstrTarget⟩
      have hInstrGlobal : instr ∈ target := by
        rw [fragment.target_eq]
        simp [hInstr]
      exact
        Assembly.Program.target_resolves_of_accepted
          hAccepted hInstrGlobal hInstrTarget
    · intro internal hInternal
      have hInstr :
          Assembly.Instr.label internal ∈ fragment.code :=
        TypedCfg.Block.definedLabel_instr_mem_of_lower?
          fragment.lower hInternal
      have hInstrGlobal :
          Assembly.Instr.label internal ∈ target := by
        rw [fragment.target_eq]
        simp [hInstr]
      exact
        Assembly.Program.labelPc_exists_of_mem_labels target
          (Assembly.Program.mem_labels_of_label_mem hInstrGlobal)
  rcases
      TypedCfg.Block.lower?_starts_with_label fragment.lower with
    ⟨tail, hCode⟩
  have hLabels : target.labels.Nodup :=
    Assembly.Program.labels_nodup_of_accepted hAccepted
  have hEntryLabel :
      target.labelPc block.label = some fragment.pre.byteLength := by
    have hNodup :
        (fragment.pre ++
          Assembly.Instr.label block.label ::
            (tail ++ fragment.post)).labels.Nodup := by
      simpa [fragment.target_eq, hCode, List.append_assoc] using hLabels
    have hAt :=
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        fragment.pre (tail ++ fragment.post) hNodup
    simpa [fragment.target_eq, hCode, List.append_assoc] using hAt
  have hEntryPcEq : entryPc = fragment.pre.byteLength := by
    rw [hEntryLabel] at hLabelPc
    exact (Option.some.inj hLabelPc).symm
  have hStatePc : state.pc = fragment.pre.pcAfter := by
    calc
      state.pc = EvmYul.UInt256.ofNat entryPc := hPc
      _ = EvmYul.UInt256.ofNat fragment.pre.byteLength := by
        rw [hEntryPcEq]
      _ = fragment.pre.pcAfter := rfl
  have hResolvedFragment :
      Preservation.Terminator.ResolvedControl
        (fragment.pre ++ fragment.code ++ fragment.post)
        block.term := by
    rw [← fragment.target_eq]
    exact hResolved
  have hRun :=
    Block.lower?_positiveEventuallyWithOracle
      (block := block) (code := fragment.code)
      (pre := fragment.pre) (post := fragment.post)
      (state := state) (trace := trace)
      fragment.lower hCodeFits hStatePc
      hResolvedFragment
      (by
        rw [← fragment.target_eq]
        exact hLabels)
  rw [fragment.target_eq]
  simpa [ObserverSemantics.Program.step, hFind] using hRun

theorem lower?_step_accountsForHalt
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : EVMState} {entryPc fullFuel : Nat}
    {trace traceOut : Trace} {halt : Assembly.Halt}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc)
    (hFull :
      Assembly.Source.runNResultWithOracle
          target fullFuel state trace =
        .ok (.halted halt, traceOut)) :
    StepAccountsForHalt target state trace fullFuel halt traceOut
      (ObserverSemantics.Program.step
        program label state.incrPC trace) := by
  have hPositive :=
    lower?_step_positiveEventuallyWithOracle
      (trace := trace)
      hLower hAccepted hFits hFind hLabelPc hPc
  rcases PositiveEventually.against_halted hPositive hFull with
    ⟨prefixFuel, prefixOutcome, hPrefixPositive, hPrefixRun,
      hSim, hCompare⟩
  unfold StepAccountsForHalt
  cases hSource :
      ObserverSemantics.Program.step
        program label state.incrPC trace with
  | error err =>
      rw [hSource] at hSim
      simp [Block.RunSimulates] at hSim
      rw [hSim] at hCompare
      exact hCompare
  | ok sourcePair =>
      rcases sourcePair with ⟨sourceOutcome, sourceTrace⟩
      rw [hSource] at hSim
      simp only [Block.RunSimulates] at hSim
      cases sourceOutcome with
      | fallthrough source =>
          cases prefixOutcome with
          | error err =>
              simp [Outcome.Simulates,
                Preservation.Outcome.Simulates,
                Preservation.Outcome.RunningData] at hSim
          | ok prefixPair =>
              rcases prefixPair with ⟨prefixResult, prefixTrace⟩
              cases prefixResult with
              | halted prefixHalt =>
                  simp [Outcome.Simulates,
                    Preservation.Outcome.Simulates,
                    Preservation.Outcome.RunningData] at hSim
              | running targetState =>
                  rcases hSim with ⟨hTrace, hData⟩
                  subst prefixTrace
                  exact
                    ⟨prefixFuel, targetState, hPrefixPositive,
                      hCompare, hPrefixRun, hData⟩
      | jump next source =>
          cases prefixOutcome with
          | error err =>
              simp [Outcome.Simulates,
                Preservation.Outcome.Simulates,
                Preservation.Outcome.RunningAt] at hSim
          | ok prefixPair =>
              rcases prefixPair with ⟨prefixResult, prefixTrace⟩
              cases prefixResult with
              | halted prefixHalt =>
                  simp [Outcome.Simulates,
                    Preservation.Outcome.Simulates,
                    Preservation.Outcome.RunningAt] at hSim
              | running targetState =>
                  rcases hSim with
                    ⟨hTrace, dest, hDest, hTargetPc, hData⟩
                  subst prefixTrace
                  exact
                    ⟨prefixFuel, targetState, dest,
                      hPrefixPositive, hCompare, hPrefixRun,
                      hDest, hTargetPc, hData⟩
      | returnDispatch source =>
          cases prefixOutcome with
          | error err =>
              simp [Outcome.Simulates,
                Preservation.Outcome.Simulates,
                Preservation.Outcome.RunningData] at hSim
          | ok prefixPair =>
              rcases prefixPair with ⟨prefixResult, prefixTrace⟩
              cases prefixResult with
              | halted prefixHalt =>
                  simp [Outcome.Simulates,
                    Preservation.Outcome.Simulates,
                    Preservation.Outcome.RunningData] at hSim
              | running targetState =>
                  rcases hSim with ⟨hTrace, hData⟩
                  subst prefixTrace
                  exact
                    ⟨prefixFuel, targetState, hPrefixPositive,
                      hCompare, hPrefixRun, hData⟩
      | halt kind source =>
          cases prefixOutcome with
          | error err =>
              exact hCompare.elim
          | ok prefixPair =>
              rcases prefixPair with ⟨prefixResult, prefixTrace⟩
              cases prefixResult with
              | running targetState =>
                  rcases hSim with ⟨_hTrace, hStep⟩
                  change
                    .ok (.running targetState) =
                      Assembly.Target.stepInstrResult
                        (.prim kind.toPrimOp) source at hStep
                  have hHaltKind :
                      (Assembly.TargetInstr.prim
                        kind.toPrimOp).haltKind? = some kind := by
                    cases kind <;> rfl
                  cases hExec :
                      Assembly.Target.stepInstr
                        (.prim kind.toPrimOp) source with
                  | error err =>
                      have hResult :
                          Assembly.Target.stepInstrResult
                              (.prim kind.toPrimOp) source =
                            .error err := by
                        simp [Assembly.Target.stepInstrResult, hExec,
                          Bind.bind, Except.bind]
                      rw [hResult] at hStep
                      cases hStep
                  | ok stepped =>
                      have hResult :
                          Assembly.Target.stepInstrResult
                              (.prim kind.toPrimOp) source =
                            .ok (.halted {
                              kind := kind
                              state := stepped
                              output := kind.output stepped }) := by
                        simp [Assembly.Target.stepInstrResult,
                          hExec, hHaltKind, Bind.bind, Except.bind]
                      rw [hResult] at hStep
                      cases hStep
              | halted prefixHalt =>
                  rcases hSim with ⟨hTrace, hStep⟩
                  rcases hCompare with ⟨hHalt, hTraceOut⟩
                  subst prefixHalt
                  exact
                    ⟨hTrace.symm.trans hTraceOut, hStep.symm⟩
      | invalid source =>
          cases prefixOutcome with
          | error err =>
              exact hCompare.elim
          | ok prefixPair =>
              rcases prefixPair with ⟨prefixResult, prefixTrace⟩
              cases prefixResult <;>
                simp [Outcome.Simulates,
                  Preservation.Outcome.Simulates] at hSim

theorem lower?_step_eventuallyWithOracle
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {state : EVMState} {entryPc : Nat} {trace : Trace}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc : state.pc = EvmYul.UInt256.ofNat entryPc) :
    Assembly.Source.EventuallyWithOracle target state trace
      (Block.RunSimulates target
        (ObserverSemantics.Program.step
          program label state.incrPC trace)) :=
  PositiveEventually.eventually
    (lower?_step_positiveEventuallyWithOracle
      hLower hAccepted hFits hFind hLabelPc hPc)

end Program

end ObserverPreservation
end TypedCfg
end EvmCompiler
