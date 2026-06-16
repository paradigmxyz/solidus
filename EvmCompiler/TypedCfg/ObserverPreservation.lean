import EvmCompiler.Assembly.Preservation
import EvmCompiler.Assembly.StackShuffleObserverPreservation
import EvmCompiler.TypedCfg.Certificate
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

namespace Instr

def eraseRunState
    (result : EVMState × Trace) : EVMState × Trace :=
  (Assembly.eraseRuntimeControl result.1, result.2)

/--
Observer-aware primitive execution is congruent modulo compiler-owned control
state for the effects admitted by the checked closed-program boundary.
-/
theorem prim_runState_map_eraseRuntimeControl
    {op : Assembly.PrimOp} {shape : Shape}
    {target source : EVMState} {trace : Trace}
    {arity : Nat × Nat}
    (hArity : op.stackArity? = some arity)
    (hNoPc : op ≠ .pc)
    (hNoCall : op.isExternalCallCreate = false)
    (hRel : Assembly.SameRuntimeData target source) :
    (ObserverSemantics.Instr.runState
        (.prim op) shape target trace).map eraseRunState =
      (ObserverSemantics.Instr.runState
        (.prim op) shape source trace).map eraseRunState := by
  unfold ObserverSemantics.Instr.runState
  simp only [TypedCfg.Instr.runState]
  have hStep :=
    Assembly.PrimOp.step_map_eraseRuntimeControl
      (op := op) ⟨arity, hArity⟩ hNoPc hNoCall hRel
  cases hTarget : op.step target with
  | error targetErr =>
      cases hSource : op.step source with
      | error sourceErr =>
          simp [hTarget, hSource, Except.map] at hStep ⊢
          subst sourceErr
          rfl
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hStep
  | ok targetFinal =>
      cases hSource : op.step source with
      | error sourceErr =>
          simp [hTarget, hSource, Except.map] at hStep
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hStep
          cases hObserver :
              Assembly.ResourceObserver.ofPrimOp? op with
          | none =>
              simpa [ObserverSemantics.Instr.handler, hObserver,
                Except.map, eraseRunState] using
                congrArg (fun state => (state, trace)) hStep
          | some kind =>
              simpa [ObserverSemantics.Instr.handler, hObserver,
                eraseRunState] using
                Assembly.ResourceObserver.applyOracleFromPostState_map_eraseRuntimeControl
                  (kind := kind) (trace := trace) hStep

theorem runPops_map_eraseRuntimeControl
    (count : Nat) {target source : EVMState}
    (hRel : Assembly.SameRuntimeData target source) :
    (TypedCfg.Instr.runPops count target).map
        Assembly.eraseRuntimeControl =
      (TypedCfg.Instr.runPops count source).map
        Assembly.eraseRuntimeControl := by
  induction count generalizing target source with
  | zero =>
      simpa [TypedCfg.Instr.runPops, Except.map] using hRel
  | succ count ih =>
      have hPop :=
        Assembly.PrimOp.step_map_eraseRuntimeControl
          (op := .pop) ⟨(1, 0), by rfl⟩ (by decide) (by rfl) hRel
      cases hTarget : Assembly.PrimOp.pop.step target with
      | error targetErr =>
          cases hSource : Assembly.PrimOp.pop.step source with
          | error sourceErr =>
              simp [TypedCfg.Instr.runPops, hTarget, hSource,
                Except.map] at hPop ⊢
              subst sourceErr
              rfl
          | ok sourceAfter =>
              simp [hTarget, hSource, Except.map] at hPop
      | ok targetAfter =>
          cases hSource : Assembly.PrimOp.pop.step source with
          | error sourceErr =>
              simp [hTarget, hSource, Except.map] at hPop
          | ok sourceAfter =>
              simp [hTarget, hSource, Except.map] at hPop
              simpa [TypedCfg.Instr.runPops, hTarget, hSource,
                Bind.bind, Except.bind] using
                  ih (target := targetAfter) (source := sourceAfter) hPop

theorem plain_runState_map_eraseRuntimeControl
    {instr : TypedCfg.Instr} {shape output : Shape}
    {target source : EVMState}
    (hType : instr.type? shape = some output)
    (hSafe : instr.ReplaySafe)
    (hRel : Assembly.SameRuntimeData target source) :
    (TypedCfg.Instr.runState instr shape target).map
        Assembly.eraseRuntimeControl =
      (TypedCfg.Instr.runState instr shape source).map
        Assembly.eraseRuntimeControl := by
  cases instr with
  | push value =>
      simpa [TypedCfg.Instr.runState, Except.map] using
        Assembly.SameRuntimeData.replaceStackAndIncrPC hRel
          (congrArg (fun stack => stack.push value)
            (Assembly.SameRuntimeData.stack_eq hRel))
  | returnToken value =>
      simpa [TypedCfg.Instr.runState, Except.map] using
        Assembly.SameRuntimeData.replaceStackAndIncrPC hRel
          (congrArg (fun stack => stack.push value)
            (Assembly.SameRuntimeData.stack_eq hRel))
  | prim op =>
      have hArity : ∃ arity, op.stackArity? = some arity := by
        unfold TypedCfg.Instr.type? at hType
        cases h : op.stackArity? with
        | none => simp [h] at hType
        | some arity => exact ⟨arity, rfl⟩
      have hNoPc : op ≠ .pc := by
        intro hEq
        subst op
        simp [TypedCfg.Instr.ReplaySafe, Effects.ReplaySafe,
          TypedCfg.Instr.effects, Effects.ofPrim] at hSafe
      have hNoCall : op.isExternalCallCreate = false := by
        simpa [TypedCfg.Instr.ReplaySafe, Effects.ReplaySafe,
          TypedCfg.Instr.effects, Effects.ofPrim] using hSafe.2
      exact
        Assembly.PrimOp.step_map_eraseRuntimeControl
          hArity hNoPc hNoCall hRel
  | pop =>
      simpa [TypedCfg.Instr.runState] using
        Assembly.PrimOp.step_map_eraseRuntimeControl
          (op := .pop) ⟨(1, 0), by rfl⟩ (by decide) (by rfl) hRel
  | dup depth =>
      have hDepth : depth < 16 := by
        by_contra hNot
        simp [TypedCfg.Instr.type?, hNot] at hType
      have hRun :=
        Assembly.PrimStep.run_map_eraseRuntimeControl
          (step := .dup (depth + 1)) hRel
      interval_cases depth <;>
        simp_all [TypedCfg.Instr.runState, Assembly.PrimOp.step,
          Assembly.PrimOp.continuingStep?]
  | swap depth =>
      have hDepth : depth < 16 := by
        by_contra hNot
        simp [TypedCfg.Instr.type?, hNot] at hType
      have hRun :=
        Assembly.PrimStep.run_map_eraseRuntimeControl
          (step := .swap (depth + 1)) hRel
      interval_cases depth <;>
        simp_all [TypedCfg.Instr.runState, Assembly.PrimOp.step,
          Assembly.PrimOp.continuingStep?]
  | bindLocals offset names =>
      simpa [TypedCfg.Instr.runState, Except.map] using hRel
  | bindScratch baseDepth name slot =>
      simpa [TypedCfg.Instr.runState, Except.map] using hRel
  | relabel targetShape =>
      simpa [TypedCfg.Instr.runState, Except.map] using hRel
  | unwind targetShape =>
      simpa [TypedCfg.Instr.runState] using
        runPops_map_eraseRuntimeControl
          (shape.length - targetShape.length) hRel

/--
One checked TypedCfg instruction has identical observer replay from
runtime-related states, modulo compiler-owned control counters.
-/
theorem runState_map_eraseRuntimeControl
    {instr : TypedCfg.Instr} {shape output : Shape}
    {target source : EVMState} {trace : Trace}
    (hType : instr.type? shape = some output)
    (hSafe : instr.ReplaySafe)
    (hRel : Assembly.SameRuntimeData target source) :
    (ObserverSemantics.Instr.runState instr shape target trace).map
        eraseRunState =
      (ObserverSemantics.Instr.runState instr shape source trace).map
        eraseRunState := by
  cases instr with
  | prim op =>
      have hArity : ∃ arity, op.stackArity? = some arity := by
        unfold TypedCfg.Instr.type? at hType
        cases h : op.stackArity? with
        | none => simp [h] at hType
        | some arity => exact ⟨arity, rfl⟩
      rcases hArity with ⟨arity, hArity⟩
      have hNoPc : op ≠ .pc := by
        intro hEq
        subst op
        simp [TypedCfg.Instr.ReplaySafe, Effects.ReplaySafe,
          TypedCfg.Instr.effects, Effects.ofPrim] at hSafe
      have hNoCall : op.isExternalCallCreate = false := by
        simpa [TypedCfg.Instr.ReplaySafe, Effects.ReplaySafe,
          TypedCfg.Instr.effects, Effects.ofPrim] using hSafe.2
      exact
        prim_runState_map_eraseRuntimeControl
          hArity hNoPc hNoCall hRel
  | push value | returnToken value | pop | dup value | swap value
  | bindLocals value names | bindScratch value name slot
  | relabel targetShape | unwind targetShape =>
      unfold ObserverSemantics.Instr.runState
      simp only [ObserverSemantics.Instr.handler]
      have hPlain :=
        plain_runState_map_eraseRuntimeControl hType hSafe hRel
      cases hTarget : TypedCfg.Instr.runState _ shape target with
      | error targetErr =>
          cases hSource : TypedCfg.Instr.runState _ shape source with
          | error sourceErr =>
              simp [hTarget, hSource, Except.map] at hPlain ⊢
              subst sourceErr
              rfl
          | ok sourceFinal =>
              simp [hTarget, hSource, Except.map] at hPlain
      | ok targetFinal =>
          cases hSource : TypedCfg.Instr.runState _ shape source with
          | error sourceErr =>
              simp [hTarget, hSource, Except.map] at hPlain
          | ok sourceFinal =>
              simp [hTarget, hSource, Except.map] at hPlain
              simpa [hTarget, hSource, Except.map, eraseRunState] using
                congrArg (fun state => (state, trace)) hPlain

def eraseRunAt
    (result : (EVMState × Shape) × Trace) :
    (EVMState × Shape) × Trace :=
  ((Assembly.eraseRuntimeControl result.1.1, result.1.2), result.2)

theorem runAt_output
    {instr : TypedCfg.Instr} {shape output actual : Shape}
    {state final : EVMState} {trace trace' : Trace}
    (hType : instr.type? shape = some output)
    (hRun :
      ObserverSemantics.Instr.runAt instr shape state trace =
        .ok ((final, actual), trace')) :
    actual = output := by
  unfold ObserverSemantics.Instr.runAt at hRun
  rw [hType] at hRun
  simp only [Option.elim_some, Bind.bind, Except.bind] at hRun
  cases hState :
      ObserverSemantics.Instr.runState instr shape state trace with
  | error err =>
      simp [hState] at hRun
  | ok result =>
      rcases result with ⟨state', trace''⟩
      simp [hState] at hRun
      exact hRun.1.2.symm

/--
Checked instruction replay is insensitive to compiler-owned control counters,
including the shape transition selected by the ordinary TypedCfg typechecker.
-/
theorem runAt_map_eraseRuntimeControl
    {instr : TypedCfg.Instr} {shape output : Shape}
    {target source : EVMState} {trace : Trace}
    (hType : instr.type? shape = some output)
    (hSafe : instr.ReplaySafe)
    (hRel : Assembly.SameRuntimeData target source) :
    (ObserverSemantics.Instr.runAt instr shape target trace).map
        eraseRunAt =
      (ObserverSemantics.Instr.runAt instr shape source trace).map
        eraseRunAt := by
  unfold ObserverSemantics.Instr.runAt
  rw [hType]
  simp only [Option.elim_some, Bind.bind, Except.bind]
  have hRun :=
    runState_map_eraseRuntimeControl
      (trace := trace) hType hSafe hRel
  cases hTarget :
      ObserverSemantics.Instr.runState instr shape target trace with
  | error targetErr =>
      cases hSource :
          ObserverSemantics.Instr.runState instr shape source trace with
      | error sourceErr =>
          simp [hTarget, hSource, Except.map] at hRun ⊢
          subst sourceErr
          rfl
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hRun
  | ok targetFinal =>
      cases hSource :
          ObserverSemantics.Instr.runState instr shape source trace with
      | error sourceErr =>
          simp [hTarget, hSource, Except.map] at hRun
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hRun
          simpa [hTarget, hSource, Except.map, eraseRunAt,
            eraseRunState] using
              congrArg
                (fun result =>
                  ((result.1, output), result.2))
                hRun

end Instr

namespace Outcome

def eraseRuntimeControl : TypedCfg.Outcome → TypedCfg.Outcome
  | .fallthrough state =>
      .fallthrough (Assembly.eraseRuntimeControl state)
  | .jump target state =>
      .jump target (Assembly.eraseRuntimeControl state)
  | .returnDispatch state =>
      .returnDispatch (Assembly.eraseRuntimeControl state)
  | .halt kind state =>
      .halt kind (Assembly.eraseRuntimeControl state)
  | .invalid state =>
      .invalid (Assembly.eraseRuntimeControl state)

def eraseWithTrace
    (result : TypedCfg.Outcome × Trace) :
    TypedCfg.Outcome × Trace :=
  (eraseRuntimeControl result.1, result.2)

/--
A target halt matches a TypedCfg halt state when the ordinary lowering theorem
can execute that halt from a runtime-related state.
-/
def HaltMatches (target : Assembly.Halt)
    (kind : Assembly.HaltKind) (source : EVMState) : Prop :=
  ∃ simulated,
    Assembly.SameRuntimeData simulated source ∧
      Assembly.Target.stepInstrResult
          (.prim kind.toPrimOp) simulated =
        .ok (.halted target)

theorem HaltMatches.elim
    {target : Assembly.Halt}
    {kind : Assembly.HaltKind} {source : EVMState}
    (hMatches : HaltMatches target kind source) :
    target.kind = kind ∧
      ∃ simulated,
        Assembly.SameRuntimeData simulated source ∧
          Assembly.Target.stepInstr (.prim kind.toPrimOp) simulated =
            .ok target.state ∧
          target.output =
            target.state.toMachineState.H_return := by
  rcases hMatches with ⟨simulated, hRel, hStep⟩
  have hOutput :=
    Assembly.Preservation.Target.stepInstrResult_terminal_output_eq_H_return
      hStep
  unfold Assembly.Target.stepInstrResult at hStep
  cases hRun :
      Assembly.Target.stepInstr (.prim kind.toPrimOp) simulated with
  | error err =>
      rw [hRun] at hStep
      cases hStep
  | ok final =>
      rw [hRun] at hStep
      have hKind :
          (Assembly.TargetInstr.prim kind.toPrimOp).haltKind? =
            some kind := by
        cases kind <;> rfl
      rw [hKind] at hStep
      cases hStep
      exact ⟨rfl, simulated, hRel, hRun, hOutput⟩

end Outcome

namespace Block

def eraseRunBody
    (result : (EVMState × Shape) × Trace) :
    (EVMState × Shape) × Trace :=
  ((Assembly.eraseRuntimeControl result.1.1, result.1.2), result.2)

/--
The shared effect interpreter replays a well-typed, checked instruction body
identically from states that differ only in compiler-owned control counters.
-/
theorem runBody_map_eraseRuntimeControl
    {body : List TypedCfg.Instr} {input output : Shape}
    {target source : EVMState} {trace : Trace}
    (hType : TypedCfg.Block.bodyType? body input = some output)
    (hSafe : body.Forall TypedCfg.Instr.ReplaySafe)
    (hRel : Assembly.SameRuntimeData target source) :
    (ObserverSemantics.Block.runBody body input target trace).map
        eraseRunBody =
      (ObserverSemantics.Block.runBody body input source trace).map
        eraseRunBody := by
  induction body generalizing input target source trace with
  | nil =>
      change
        Except.ok ((Assembly.eraseRuntimeControl target, input), trace) =
          Except.ok ((Assembly.eraseRuntimeControl source, input), trace)
      exact congrArg
        (fun state =>
          (Except.ok ((state, input), trace) :
            Except EVMException ((EVMState × Shape) × Trace))) hRel
  | cons instr rest ih =>
      rcases
          (List.forall_cons
            TypedCfg.Instr.ReplaySafe instr rest).mp hSafe with
        ⟨hHeadSafe, hRestSafe⟩
      cases hHeadType : instr.type? input with
      | none =>
          simp [TypedCfg.Block.bodyType?, hHeadType] at hType
      | some middle =>
          have hTailType :
              TypedCfg.Block.bodyType? rest middle = some output := by
            simpa [TypedCfg.Block.bodyType?, hHeadType] using hType
          have hHead :=
            Instr.runAt_map_eraseRuntimeControl
              (trace := trace) hHeadType hHeadSafe hRel
          cases hTarget :
              ObserverSemantics.Instr.runAt
                instr input target trace with
          | error targetErr =>
              cases hSource :
                  ObserverSemantics.Instr.runAt
                    instr input source trace with
              | error sourceErr =>
                  simp [hTarget, hSource, Except.map] at hHead ⊢
                  subst sourceErr
                  rfl
              | ok sourceFinal =>
                  simp [hTarget, hSource, Except.map] at hHead
          | ok targetFinal =>
              cases hSource :
                  ObserverSemantics.Instr.runAt
                    instr input source trace with
              | error sourceErr =>
                  simp [hTarget, hSource, Except.map] at hHead
              | ok sourceFinal =>
                  simp [hTarget, hSource, Except.map, Instr.eraseRunAt]
                    at hHead
                  rcases targetFinal with ⟨⟨targetAfter, targetShape⟩,
                    targetTrace⟩
                  rcases sourceFinal with ⟨⟨sourceAfter, sourceShape⟩,
                    sourceTrace⟩
                  rcases hHead with
                    ⟨⟨hAfter, hShape⟩, hTrace⟩
                  simp only [Prod.fst, Prod.snd] at hAfter hShape hTrace
                  have hTargetShape :
                      targetShape = middle :=
                    Instr.runAt_output hHeadType hTarget
                  subst targetShape
                  subst sourceShape
                  subst sourceTrace
                  have hTail :=
                    ih (trace := targetTrace)
                      hTailType hRestSafe hAfter
                  simpa only [ObserverSemantics.Block.runBody_cons,
                    hTarget, hSource, Bind.bind, Except.bind] using hTail

/--
TypedCfg terminators inspect only runtime data. Symbolic control outcomes are
therefore identical after erasing compiler-owned concrete control counters.
-/
theorem runTerm_map_eraseRuntimeControl
    {shape : Shape} {term : TypedCfg.Terminator}
    {target source : EVMState}
    (hRel : Assembly.SameRuntimeData target source) :
    Outcome.eraseRuntimeControl
        (TypedCfg.Block.runTerm shape term target) =
      Outcome.eraseRuntimeControl
        (TypedCfg.Block.runTerm shape term source) := by
  have hStack :
      target.stack = source.stack :=
    Assembly.SameRuntimeData.stack_eq hRel
  cases term with
  | fallthrough next =>
      simpa [TypedCfg.Block.runTerm, Outcome.eraseRuntimeControl] using
        congrArg (TypedCfg.Outcome.jump next) hRel
  | jump next =>
      simpa [TypedCfg.Block.runTerm, Outcome.eraseRuntimeControl] using
        congrArg (TypedCfg.Outcome.jump next) hRel
  | jumpi targetLabel fallthroughLabel =>
      simp only [TypedCfg.Block.runTerm]
      rw [hStack]
      cases hPop : source.stack.pop with
      | none =>
          simpa [TypedCfg.Block.runTerm, hPop,
            Outcome.eraseRuntimeControl] using
              congrArg TypedCfg.Outcome.invalid hRel
      | some pair =>
          rcases pair with ⟨stack, cond⟩
          have hReplace :
              Assembly.SameRuntimeData
                { target with stack := stack }
                { source with stack := stack } :=
            Assembly.SameRuntimeData.replaceStack hRel rfl
          by_cases hZero : cond = EvmYul.UInt256.ofNat 0
          · simpa [TypedCfg.Block.runTerm, hPop, hZero,
              Outcome.eraseRuntimeControl] using
                congrArg
                  (TypedCfg.Outcome.jump fallthroughLabel)
                  hReplace
          · simpa [TypedCfg.Block.runTerm, hPop, hZero,
              Outcome.eraseRuntimeControl] using
                congrArg
                  (TypedCfg.Outcome.jump targetLabel)
                  hReplace
  | returnDispatch returnCount sites =>
      simp only [TypedCfg.Block.runTerm]
      rw [hStack]
      cases hDepth : shape.returnTokenDepth? with
      | none =>
          simpa [TypedCfg.Block.runTerm, hDepth,
            Outcome.eraseRuntimeControl] using
              congrArg TypedCfg.Outcome.invalid hRel
      | some depth =>
          by_cases hCount : depth = returnCount
          · subst depth
            cases hToken : source.stack[returnCount]? with
            | none =>
                simpa [TypedCfg.Block.runTerm, hDepth, hToken,
                  Outcome.eraseRuntimeControl] using
                    congrArg TypedCfg.Outcome.invalid hRel
            | some token =>
                cases hFind :
                    TypedCfg.Block.ReturnSite.findTarget? token sites with
                | none =>
                    simpa [TypedCfg.Block.runTerm, hDepth,
                      hToken, hFind, Outcome.eraseRuntimeControl] using
                        congrArg TypedCfg.Outcome.invalid hRel
                | some next =>
                    have hReplace :
                        Assembly.SameRuntimeData
                          { target with
                            stack := source.stack.eraseIdx returnCount }
                          { source with
                            stack := source.stack.eraseIdx returnCount } :=
                      Assembly.SameRuntimeData.replaceStack hRel rfl
                    simpa [TypedCfg.Block.runTerm, hDepth,
                      hToken, hFind, Outcome.eraseRuntimeControl] using
                        congrArg
                          (TypedCfg.Outcome.jump next)
                          hReplace
          · simpa [TypedCfg.Block.runTerm, hDepth, hCount,
              Outcome.eraseRuntimeControl] using
                congrArg TypedCfg.Outcome.invalid hRel
  | halt kind =>
      simpa [TypedCfg.Block.runTerm, Outcome.eraseRuntimeControl] using
        congrArg (TypedCfg.Outcome.halt kind) hRel
  | invalid =>
      simpa [TypedCfg.Block.runTerm, Outcome.eraseRuntimeControl] using
        congrArg TypedCfg.Outcome.invalid hRel

/--
One ordinary well-typed block has the same observer outcome and transcript
from runtime-related states, modulo concrete compiler control counters.
-/
theorem run_map_eraseRuntimeControl
    {program : TypedCfg.Program} {block : TypedCfg.Block}
    {target source : EVMState} {trace : Trace}
    (hTyped : block.WellTyped program)
    (hSafe : block.ReplaySafe)
    (hRel : Assembly.SameRuntimeData target source) :
    (ObserverSemantics.Block.run block target trace).map
        Outcome.eraseWithTrace =
      (ObserverSemantics.Block.run block source trace).map
        Outcome.eraseWithTrace := by
  have hBody :=
    runBody_map_eraseRuntimeControl
      (trace := trace) hTyped.1 hSafe hRel
  cases hTarget :
      ObserverSemantics.Block.runBody
        block.body block.input target trace with
  | error targetErr =>
      cases hSource :
          ObserverSemantics.Block.runBody
            block.body block.input source trace with
      | error sourceErr =>
          simp [hTarget, hSource, Except.map] at hBody
          subst sourceErr
          simp [ObserverSemantics.Block.run, hTarget, hSource]
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map] at hBody
  | ok targetFinal =>
      cases hSource :
          ObserverSemantics.Block.runBody
            block.body block.input source trace with
      | error sourceErr =>
          simp [hTarget, hSource, Except.map] at hBody
      | ok sourceFinal =>
          simp [hTarget, hSource, Except.map, eraseRunBody] at hBody
          rcases targetFinal with
            ⟨⟨targetAfter, targetOutput⟩, targetTrace⟩
          rcases sourceFinal with
            ⟨⟨sourceAfter, sourceOutput⟩, sourceTrace⟩
          rcases hBody with
            ⟨⟨hAfter, hOutput⟩, hTrace⟩
          simp only [Prod.fst, Prod.snd] at hAfter hOutput hTrace
          subst sourceOutput
          subst sourceTrace
          have hTerm :=
            runTerm_map_eraseRuntimeControl
              (shape := targetOutput) (term := block.term) hAfter
          unfold ObserverSemantics.Block.run
          rw [hTarget, hSource]
          simp only [Bind.bind, Except.bind]
          by_cases hExpected : targetOutput = block.output
          · subst targetOutput
            simp [Except.map, Outcome.eraseWithTrace, hTerm]
          · simp [hExpected, Except.map]

end Block

namespace Program

/--
One shared-semantics CFG step is congruent modulo concrete control counters.
Both well-typedness and replay safety are ordinary checked program properties.
-/
theorem step_map_eraseRuntimeControl
    {program : TypedCfg.Program} {label : Label}
    {target source : EVMState} {trace : Trace}
    (hTyped : program.WellTyped)
    (hSafe : program.ReplaySafe)
    (hRel : Assembly.SameRuntimeData target source) :
    (ObserverSemantics.Program.step
        program label target trace).map Outcome.eraseWithTrace =
      (ObserverSemantics.Program.step
        program label source trace).map Outcome.eraseWithTrace := by
  cases hFind : program.findBlock? label with
  | none =>
      simpa [ObserverSemantics.Program.step, hFind, Except.map,
        Outcome.eraseWithTrace, Outcome.eraseRuntimeControl] using hRel
  | some block =>
      have hMem : block ∈ program.blocks := by
        unfold TypedCfg.Program.findBlock? at hFind
        exact List.mem_of_find?_eq_some hFind
      have hBlockTyped : block.WellTyped program :=
        (List.forall_iff_forall_mem.mp hTyped.2.1) block hMem
      have hBlockSafe : block.ReplaySafe :=
        (List.forall_iff_forall_mem.mp hSafe) block hMem
      have hBlock :=
        Block.run_map_eraseRuntimeControl
          (trace := trace) hBlockTyped hBlockSafe hRel
      simpa [ObserverSemantics.Program.step, hFind] using hBlock

/--
Fuel-indexed replay is a congruence under the pass-owned runtime-data relation.
This is the stable forward-preservation interface for TypedCfg execution.
-/
theorem runN_map_eraseRuntimeControl
    {program : TypedCfg.Program} {fuel : Nat} {label : Label}
    {target source : EVMState} {trace : Trace}
    (hTyped : program.WellTyped)
    (hSafe : program.ReplaySafe)
    (hRel : Assembly.SameRuntimeData target source) :
    (ObserverSemantics.Program.runN
        program fuel label target trace).map Outcome.eraseWithTrace =
      (ObserverSemantics.Program.runN
        program fuel label source trace).map Outcome.eraseWithTrace := by
  induction fuel generalizing label target source trace with
  | zero =>
      simpa [Except.map,
        Outcome.eraseWithTrace, Outcome.eraseRuntimeControl] using hRel
  | succ fuel ih =>
      have hStep :=
        step_map_eraseRuntimeControl
          (label := label) (trace := trace) hTyped hSafe hRel
      cases hTarget :
          ObserverSemantics.Program.step
            program label target trace with
      | error targetErr =>
          cases hSource :
              ObserverSemantics.Program.step
                program label source trace with
          | error sourceErr =>
              simp [hTarget, hSource, Except.map] at hStep
              subst sourceErr
              simp [ObserverSemantics.Program.runN_succ,
                hTarget, hSource]
          | ok sourceFinal =>
              simp [hTarget, hSource, Except.map] at hStep
      | ok targetFinal =>
          cases hSource :
              ObserverSemantics.Program.step
                program label source trace with
          | error sourceErr =>
              simp [hTarget, hSource, Except.map] at hStep
          | ok sourceFinal =>
              rcases targetFinal with ⟨targetOutcome, targetTrace⟩
              rcases sourceFinal with ⟨sourceOutcome, sourceTrace⟩
              cases targetOutcome <;> cases sourceOutcome <;>
                simp [hTarget, hSource, Except.map,
                  Outcome.eraseWithTrace,
                  Outcome.eraseRuntimeControl] at hStep
              case jump.jump targetLabel targetState sourceLabel sourceState =>
                rcases hStep with
                  ⟨⟨hLabel, hState⟩, hTrace⟩
                subst sourceLabel
                subst sourceTrace
                have hTail :=
                  ih (label := targetLabel)
                    (trace := targetTrace) hState
                simpa [ObserverSemantics.Program.runN_succ,
                  hTarget, hSource,
                  Bind.bind, Except.bind] using hTail
              all_goals
                simp [ObserverSemantics.Program.runN_succ,
                  hTarget, hSource,
                  Bind.bind, Except.bind, Except.map,
                  Outcome.eraseWithTrace,
                  Outcome.eraseRuntimeControl, hStep]

/--
A successful observer-aware CFG jump retains the ordinary typing guarantee
that its symbolic destination is a block in the same program.
-/
theorem findBlock?_exists_of_step_jump
    {program : TypedCfg.Program} {label next : Label}
    {state final : EVMState} {trace trace' : Trace}
    (hTyped : program.WellTyped)
    (hStep :
      ObserverSemantics.Program.step program label state trace =
        .ok (.jump next final, trace')) :
    ∃ block, program.findBlock? next = some block := by
  cases hFind : program.findBlock? label with
  | none =>
      simp [ObserverSemantics.Program.step, hFind] at hStep
  | some block =>
      have hMem : block ∈ program.blocks := by
        unfold TypedCfg.Program.findBlock? at hFind
        exact List.mem_of_find?_eq_some hFind
      have hBlockTyped : block.WellTyped program :=
        (List.forall_iff_forall_mem.mp hTyped.2.1) block hMem
      unfold ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      unfold ObserverSemantics.Block.run at hStep
      cases hBody :
          ObserverSemantics.Block.runBody
            block.body block.input state trace with
      | error err =>
          simp [hBody, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with
            ⟨⟨bodyState, bodyOutput⟩, bodyTrace⟩
          by_cases hOutput : bodyOutput = block.output
          · subst bodyOutput
            simp [hBody, Bind.bind, Except.bind] at hStep
            exact
              TypedCfg.Block.findBlock?_exists_of_type?_runTerm_jump
                hBlockTyped.2 hStep.1
          · simp [hBody, hOutput, Bind.bind, Except.bind] at hStep

theorem step_ne_fallthrough
    {program : TypedCfg.Program} {label : Label}
    {state final : EVMState} {trace trace' : Trace}
    (hStep :
      ObserverSemantics.Program.step program label state trace =
        .ok (.fallthrough final, trace')) :
    False := by
  cases hFind : program.findBlock? label with
  | none =>
      simp [ObserverSemantics.Program.step, hFind] at hStep
  | some block =>
      unfold ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      unfold ObserverSemantics.Block.run at hStep
      cases hBody :
          ObserverSemantics.Block.runBody
            block.body block.input state trace with
      | error err =>
          simp [hBody, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with
            ⟨⟨bodyState, bodyOutput⟩, bodyTrace⟩
          by_cases hOutput : bodyOutput = block.output
          · subst bodyOutput
            simp [hBody, Bind.bind, Except.bind] at hStep
            exact
              TypedCfg.Block.runTerm_ne_fallthrough
                block.output block.term bodyState final hStep.1
          · simp [hBody, hOutput, Bind.bind, Except.bind] at hStep

theorem step_ne_returnDispatch
    {program : TypedCfg.Program} {label : Label}
    {state final : EVMState} {trace trace' : Trace}
    (hStep :
      ObserverSemantics.Program.step program label state trace =
        .ok (.returnDispatch final, trace')) :
    False := by
  cases hFind : program.findBlock? label with
  | none =>
      simp [ObserverSemantics.Program.step, hFind] at hStep
  | some block =>
      unfold ObserverSemantics.Program.step at hStep
      rw [hFind] at hStep
      unfold ObserverSemantics.Block.run at hStep
      cases hBody :
          ObserverSemantics.Block.runBody
            block.body block.input state trace with
      | error err =>
          simp [hBody, Bind.bind, Except.bind] at hStep
      | ok bodyResult =>
          rcases bodyResult with
            ⟨⟨bodyState, bodyOutput⟩, bodyTrace⟩
          by_cases hOutput : bodyOutput = block.output
          · subst bodyOutput
            simp [hBody, Bind.bind, Except.bind] at hStep
            exact
              TypedCfg.Block.runTerm_ne_returnDispatch
                block.output block.term bodyState final hStep.1
          · simp [hBody, hOutput, Bind.bind, Except.bind] at hStep

end Program

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
              Assembly.SameRuntimeData final state ∧
              final.pc = (pre ++ code).pcAfter
        | _ => False) := by
  subst code
  induction sites generalizing pre state trace with
  | nil =>
      exact Assembly.Source.EventuallyWithOracle.pure
        (by
          simp [TypedCfg.Terminator.returnDispatchTestCases,
            Assembly.SameRuntimeData.refl, hStack, hPc])
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
              Assembly.SameRuntimeData mid state ∧
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
                    · simpa [Assembly.SameRuntimeData, hRecord] using hData
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
                        Assembly.SameRuntimeData.trans hData hDataMid,
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
                Assembly.SameRuntimeData final state ∧
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
          Assembly.SameRuntimeData mid state ∧
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
                    Assembly.SameRuntimeData.trans
                      (by
                        simpa [Assembly.SameRuntimeData, hMidRecord] using
                          hData)
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
            Assembly.SameRuntimeData cleaned
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
                      Assembly.eraseRuntimeControl cleaned =
                          Assembly.eraseRuntimeControl
                            { afterLabel with stack := front ++ suffix } :=
                        hData
                      _ =
                          Assembly.eraseRuntimeControl
                            { state with stack := front ++ suffix } := by
                        simp [afterLabel, Assembly.eraseRuntimeControl,
                          EvmYul.EVM.State.incrPC]
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
            Assembly.SameRuntimeData.trans
              (Assembly.SameRuntimeData.jumpPc targetDest cleaned)
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
          Assembly.SameRuntimeData selected state ∧
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
                    Assembly.SameRuntimeData
                      { selected with stack := front ++ suffix }
                      { state with stack := front ++ suffix } :=
                  Assembly.eraseRuntimeControl_with_stack_congr
                    hSelectedData
                exact
                  ⟨hFinalTrace.trans hSelectedTrace,
                    targetDest, hTargetDestActual, hPcFinal,
                    by
                      simpa [hErase] using
                        Assembly.SameRuntimeData.trans
                          hData hSelectedCleanData⟩)

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
          Assembly.SameRuntimeData tested state ∧
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
            Assembly.SameRuntimeData.jumpPc dest state⟩
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
            Assembly.SameRuntimeData.jumpPc dest state⟩
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
                  Assembly.SameRuntimeData.jumpPc nextDest popped⟩
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
                  Assembly.SameRuntimeData.jumpPc targetDest popped⟩
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
              Assembly.SameRuntimeData targetState source
      | .jump next source =>
          ∃ prefixFuel targetState dest,
            0 < prefixFuel ∧
              prefixFuel < fullFuel ∧
              Assembly.Source.runNResultWithOracle
                  target prefixFuel initial initialTrace =
                .ok (.running targetState, sourceTrace) ∧
              target.labelPc next = some dest ∧
              targetState.pc = EvmYul.UInt256.ofNat dest ∧
              Assembly.SameRuntimeData targetState source
      | .returnDispatch source =>
          ∃ prefixFuel targetState,
            0 < prefixFuel ∧
              prefixFuel < fullFuel ∧
              Assembly.Source.runNResultWithOracle
                  target prefixFuel initial initialTrace =
                .ok (.running targetState, sourceTrace) ∧
              Assembly.SameRuntimeData targetState source
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

/--
Backward adequacy for a complete terminal Assembly run of a replay-safe
TypedCfg program.

The theorem constructs the CFG fuel and halt outcome. Its public inputs are
ordinary source well-typedness/replay safety, the existing lowering, and a
concrete target run; no compiler-generated proof object is accepted.
-/
theorem lower?_terminal_backward
    {program : TypedCfg.Program} {target : Assembly.Program}
    {label : Label} {block : TypedCfg.Block}
    {targetInitial sourceInitial : EVMState} {entryPc fullFuel : Nat}
    {trace traceOut : Trace} {halt : Assembly.Halt}
    (hLower : program.lower? = some target)
    (hAccepted : target.accepted = true)
    (hFits : target.PCFits)
    (hTyped : program.WellTyped)
    (hSafe : program.ReplaySafe)
    (hFind : program.findBlock? label = some block)
    (hLabelPc : target.labelPc label = some entryPc)
    (hPc :
      targetInitial.pc = EvmYul.UInt256.ofNat entryPc)
    (hRel :
      Assembly.SameRuntimeData targetInitial sourceInitial)
    (hFull :
      Assembly.Source.runNResultWithOracle
          target fullFuel targetInitial trace =
        .ok (.halted halt, traceOut)) :
    ∃ cfgFuel kind sourceFinal,
      ObserverSemantics.Program.runN
          program cfgFuel label sourceInitial trace =
        .ok (.halt kind sourceFinal, traceOut) ∧
      Outcome.HaltMatches halt kind sourceFinal := by
  induction fullFuel using Nat.strong_induction_on generalizing
      label block targetInitial sourceInitial entryPc trace with
  | h fullFuel ih =>
      have hAccounts :=
        lower?_step_accountsForHalt
          hLower hAccepted hFits hFind hLabelPc hPc hFull
      have hCongruence :=
        ObserverPreservation.Program.step_map_eraseRuntimeControl
          (label := label) (trace := trace) hTyped hSafe
          (Assembly.SameRuntimeData.incrPC_left hRel)
      cases hTargetStep :
          ObserverSemantics.Program.step
            program label targetInitial.incrPC trace with
      | error targetErr =>
          unfold StepAccountsForHalt at hAccounts
          rw [hTargetStep] at hAccounts
          exact hAccounts.elim
      | ok targetPair =>
          rcases targetPair with ⟨targetOutcome, targetTrace⟩
          unfold StepAccountsForHalt at hAccounts
          rw [hTargetStep] at hAccounts
          cases targetOutcome with
          | fallthrough targetSource =>
              exact
                (ObserverPreservation.Program.step_ne_fallthrough
                  hTargetStep).elim
          | returnDispatch targetSource =>
              exact
                (ObserverPreservation.Program.step_ne_returnDispatch
                  hTargetStep).elim
          | invalid targetSource =>
              exact hAccounts.elim
          | halt kind simulated =>
              cases hSourceStep :
                  ObserverSemantics.Program.step
                    program label sourceInitial trace with
              | error sourceErr =>
                  simp [hTargetStep, hSourceStep, Except.map] at hCongruence
              | ok sourcePair =>
                  rcases sourcePair with ⟨sourceOutcome, sourceTrace⟩
                  cases sourceOutcome with
                  | fallthrough source =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                  | jump next source =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                  | returnDispatch source =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                  | invalid source =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                  | halt sourceKind sourceFinal =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                      rcases hCongruence with
                        ⟨⟨hKind, hState⟩, hTrace⟩
                      subst sourceKind
                      subst sourceTrace
                      refine
                        ⟨1, kind, sourceFinal, ?_,
                          ⟨simulated, hState, hAccounts.2⟩⟩
                      simpa [ObserverSemantics.Program.runN_succ,
                        hSourceStep, hAccounts.1]
          | jump next simulated =>
              rcases hAccounts with
                ⟨prefixFuel, targetNext, dest, hPrefixPositive,
                  hPrefixLt, hPrefixRun, hDest, hTargetPc,
                  hTargetRel⟩
              cases hSourceStep :
                  ObserverSemantics.Program.step
                    program label sourceInitial trace with
              | error sourceErr =>
                  simp [hTargetStep, hSourceStep, Except.map] at hCongruence
              | ok sourcePair =>
                  rcases sourcePair with ⟨sourceOutcome, sourceTrace⟩
                  cases sourceOutcome with
                  | fallthrough source =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                  | returnDispatch source =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                  | halt sourceKind source =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                  | invalid source =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                  | jump sourceNext sourceNextState =>
                      simp [hTargetStep, hSourceStep, Except.map,
                        Outcome.eraseWithTrace,
                        Outcome.eraseRuntimeControl] at hCongruence
                      rcases hCongruence with
                        ⟨⟨hNext, hSourceRel⟩, hTrace⟩
                      subst sourceNext
                      subst sourceTrace
                      rcases
                          findBlock?_exists_of_step_jump
                            hTyped hSourceStep with
                        ⟨nextBlock, hFindNext⟩
                      let restFuel := fullFuel - prefixFuel
                      have hFuelEq :
                          prefixFuel + restFuel = fullFuel :=
                        Nat.add_sub_of_le (Nat.le_of_lt hPrefixLt)
                      have hRestLt : restFuel < fullFuel := by
                        dsimp [restFuel]
                        omega
                      have hRestRun :
                          Assembly.Source.runNResultWithOracle
                              target restFuel targetNext targetTrace =
                            .ok (.halted halt, traceOut) := by
                        have hRewritten :
                            Assembly.Source.runNResultWithOracle
                                target (prefixFuel + restFuel)
                                  targetInitial trace =
                              .ok (.halted halt, traceOut) := by
                          simpa [hFuelEq] using hFull
                        rw [
                          Assembly.Source.runNResultWithOracle_add_of_running
                            hPrefixRun] at hRewritten
                        exact hRewritten
                      have hNextRel :
                          Assembly.SameRuntimeData
                            targetNext sourceNextState :=
                        Assembly.SameRuntimeData.trans
                          hTargetRel hSourceRel
                      rcases
                          ih restFuel hRestLt
                            hFindNext hDest hTargetPc hNextRel hRestRun with
                        ⟨tailFuel, finalKind, sourceFinal,
                          hTailRun, hHaltMatch⟩
                      refine
                        ⟨tailFuel + 1, finalKind, sourceFinal, ?_,
                          hHaltMatch⟩
                      simpa [ObserverSemantics.Program.runN_succ,
                        hSourceStep] using hTailRun

/--
Terminal target execution at the checked program entry. The generated entry
offset is hidden inside the semantic target-run relation.
-/
def EntryTerminalRun
    (program : TypedCfg.Program) (artifact : TypedCfg.Program.CertifiedArtifact)
    (fuel : Nat) (initial : EVMState) (trace traceOut : Trace)
    (halt : Assembly.Halt) : Prop :=
  ∃ entryPc,
    artifact.target.labelPc program.entry = some entryPc ∧
      Assembly.Source.runNResultWithOracle artifact.target fuel
          { initial with pc := EvmYul.UInt256.ofNat entryPc } trace =
        .ok (.halted halt, traceOut)

/--
Checked-artifact backward adequacy for the TypedCfg-to-Assembly boundary.

Block lookup, entry offset, acceptedness, PC fit, and the concrete lowering are
all recovered from the successful compiler. The only additional restriction
is the source-facing replay-safety property that upper passes must establish.
-/
theorem compileCertified?_entry_terminal_backward
    {program : TypedCfg.Program}
    {artifact : TypedCfg.Program.CertifiedArtifact}
    {fuel : Nat} {initial sourceInitial : EVMState}
    {trace traceOut : Trace} {halt : Assembly.Halt}
    (hCompile : program.compileCertified? = some artifact)
    (hSafe : program.ReplaySafe)
    (hRel : Assembly.SameRuntimeData initial sourceInitial)
    (hRun :
      EntryTerminalRun program artifact fuel initial trace traceOut halt) :
    ∃ cfgFuel kind sourceFinal,
      ObserverSemantics.Program.runN
          program cfgFuel program.entry sourceInitial trace =
        .ok (.halt kind sourceFinal, traceOut) ∧
      Outcome.HaltMatches halt kind sourceFinal := by
  have hTyped : program.WellTyped :=
    TypedCfg.Program.compileCertified?_wellTyped hCompile
  cases hFind : program.findBlock? program.entry with
  | none =>
      exact False.elim (hTyped.2.2.1 hFind)
  | some block =>
      rcases hRun with ⟨entryPc, hLabelPc, hTargetRun⟩
      exact
        lower?_terminal_backward
          (TypedCfg.Program.compileCertified?_target hCompile)
          (TypedCfg.Program.compileCertified?_targetAccepted hCompile)
          (TypedCfg.Program.compileCertified?_pcFits hCompile)
          hTyped hSafe hFind hLabelPc rfl
          (Assembly.SameRuntimeData.with_pc_left
            (EvmYul.UInt256.ofNat entryPc) hRel)
          hTargetRun

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
