import EvmCompiler.Assembly.InteractionPreservation
import EvmCompiler.TypedCfg.Certificate
import EvmCompiler.TypedCfg.InteractionSemantics
import Mathlib.Tactic.IntervalCases

namespace EvmCompiler
namespace TypedCfg
namespace InteractionCongruence

namespace Instr

abbrev RuntimeStateRel :=
  Assembly.InteractionPreservation.PrimOp.RuntimeStateRel

theorem runtimeStateRel_of_map_eraseRuntimeControl_eq
    {left right : Except EVMException EVMState}
    (hEq :
      left.map Assembly.eraseRuntimeControl =
        right.map Assembly.eraseRuntimeControl) :
    RuntimeStateRel left right := by
  cases left with
  | error leftError =>
      cases right with
      | error rightError =>
          simp [Except.map] at hEq
          exact
            Simulation.Interaction.ExceptRel.error hEq
      | ok rightState =>
          simp [Except.map] at hEq
  | ok leftState =>
      cases right with
      | error rightError =>
          simp [Except.map] at hEq
      | ok rightState =>
          simp [Except.map] at hEq
          exact
            Simulation.Interaction.ExceptRel.ok hEq

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
      | error targetError =>
          cases hSource : Assembly.PrimOp.pop.step source with
          | error sourceError =>
              simp [TypedCfg.Instr.runPops, hTarget, hSource,
                Except.map] at hPop ⊢
              subst sourceError
              rfl
          | ok sourceAfter =>
              simp [hTarget, hSource, Except.map] at hPop
      | ok targetAfter =>
          cases hSource : Assembly.PrimOp.pop.step source with
          | error sourceError =>
              simp [hTarget, hSource, Except.map] at hPop
          | ok sourceAfter =>
              simp [hTarget, hSource, Except.map] at hPop
              simpa [TypedCfg.Instr.runPops, hTarget, hSource,
                Bind.bind, Except.bind] using
                  ih (target := targetAfter) (source := sourceAfter) hPop

/--
TypedCfg instruction execution is insensitive to compiler-owned control
counters whenever the source instruction does not read `pc`. CALL/CREATE and
resource primitives use the shared open interaction protocol and remain fully
supported.
-/
theorem openRunState_runtimeRel
    {instr : TypedCfg.Instr} {shape output : Shape}
    {target source : EVMState}
    (hType : instr.type? shape = some output)
    (hIndependent : instr.ProgramCounterIndependent)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeStateRel
      (InteractionSemantics.Instr.openRunState instr shape target)
      (InteractionSemantics.Instr.openRunState instr shape source) := by
  cases instr with
  | prim op =>
      have hArity : ∃ arity, op.stackArity? = some arity := by
        unfold TypedCfg.Instr.type? at hType
        cases h : op.stackArity? with
        | none =>
            simp [h] at hType
        | some arity =>
            exact ⟨arity, rfl⟩
      have hNoPc : op ≠ .pc := by
        intro hEq
        subst op
        simp [TypedCfg.Instr.ProgramCounterIndependent,
          TypedCfg.Instr.effects, Effects.ofPrim] at hIndependent
      exact
        Assembly.InteractionPreservation.PrimOp.openStep_runtimeRel
          hArity hNoPc hRel
  | push value =>
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        Assembly.SameRuntimeData.replaceStackAndIncrPC hRel
          (congrArg (fun stack => stack.push value)
            (Assembly.SameRuntimeData.stack_eq hRel))
  | returnToken value =>
      apply Simulation.Interaction.Rel.done
      apply Simulation.Interaction.ExceptRel.ok
      exact
        Assembly.SameRuntimeData.replaceStackAndIncrPC hRel
          (congrArg (fun stack => stack.push value)
            (Assembly.SameRuntimeData.stack_eq hRel))
  | pop =>
      apply Simulation.Interaction.Rel.done
      apply runtimeStateRel_of_map_eraseRuntimeControl_eq
      exact
        Assembly.PrimOp.step_map_eraseRuntimeControl
          (op := .pop) ⟨(1, 0), by rfl⟩ (by decide) (by rfl) hRel
  | dup depth =>
      have hDepth : depth < 16 := by
        by_contra hNot
        simp [TypedCfg.Instr.type?, hNot] at hType
      have hRun :=
        Assembly.PrimStep.run_map_eraseRuntimeControl
          (step := .dup (depth + 1)) hRel
      apply Simulation.Interaction.Rel.done
      apply runtimeStateRel_of_map_eraseRuntimeControl_eq
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
      apply Simulation.Interaction.Rel.done
      apply runtimeStateRel_of_map_eraseRuntimeControl_eq
      interval_cases depth <;>
        simp_all [TypedCfg.Instr.runState, Assembly.PrimOp.step,
          Assembly.PrimOp.continuingStep?]
  | bindLocals offset names =>
      exact
        .done (Simulation.Interaction.ExceptRel.ok hRel)
  | bindScratch baseDepth name slot =>
      exact
        .done (Simulation.Interaction.ExceptRel.ok hRel)
  | relabel targetShape =>
      exact
        .done (Simulation.Interaction.ExceptRel.ok hRel)
  | unwind targetShape =>
      apply Simulation.Interaction.Rel.done
      apply runtimeStateRel_of_map_eraseRuntimeControl_eq
      exact
        runPops_map_eraseRuntimeControl
          (shape.length - targetShape.length) hRel

def StateShapeRel (output : Shape)
    (left right : EVMState × Shape) : Prop :=
  Assembly.SameRuntimeData left.1 right.1 ∧
    left.2 = output ∧ right.2 = output

abbrev RuntimeAtRel (output : Shape) :
    Except EVMException (EVMState × Shape) →
      Except EVMException (EVMState × Shape) → Prop :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    (StateShapeRel output)

theorem openRunAt_runtimeRel
    {instr : TypedCfg.Instr} {shape output : Shape}
    {target source : EVMState}
    (hType : instr.type? shape = some output)
    (hIndependent : instr.ProgramCounterIndependent)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel (RuntimeAtRel output)
      (InteractionSemantics.Instr.openRunAt instr shape target)
      (InteractionSemantics.Instr.openRunAt instr shape source) := by
  have hState :=
    openRunState_runtimeRel hType hIndependent hRel
  unfold InteractionSemantics.Instr.openRunAt
    Control.Instr.runAt
  rw [hType]
  simp only [Option.elim_some]
  apply Simulation.Interaction.Rel.bind hState
  intro targetAfter sourceAfter hAfter
  exact
    .done
      (.ok ⟨hAfter, rfl, rfl⟩)

end Instr

namespace Outcome

inductive RuntimeRel : TypedCfg.Outcome → TypedCfg.Outcome → Prop where
  | fallthrough {target source : EVMState} :
      Assembly.SameRuntimeData target source →
        RuntimeRel (.fallthrough target) (.fallthrough source)
  | jump (label : Label) {target source : EVMState} :
      Assembly.SameRuntimeData target source →
        RuntimeRel (.jump label target) (.jump label source)
  | returnDispatch {target source : EVMState} :
      Assembly.SameRuntimeData target source →
        RuntimeRel (.returnDispatch target) (.returnDispatch source)
  | halt (kind : Assembly.HaltKind) {target source : EVMState} :
      Assembly.SameRuntimeData target source →
        RuntimeRel (.halt kind target) (.halt kind source)
  | invalid {target source : EVMState} :
      Assembly.SameRuntimeData target source →
        RuntimeRel (.invalid target) (.invalid source)

namespace RuntimeRel

theorem refl (outcome : TypedCfg.Outcome) :
    RuntimeRel outcome outcome := by
  cases outcome with
  | fallthrough state =>
      exact .fallthrough (Assembly.SameRuntimeData.refl state)
  | jump label state =>
      exact .jump label (Assembly.SameRuntimeData.refl state)
  | returnDispatch state =>
      exact .returnDispatch (Assembly.SameRuntimeData.refl state)
  | halt kind state =>
      exact .halt kind (Assembly.SameRuntimeData.refl state)
  | invalid state =>
      exact .invalid (Assembly.SameRuntimeData.refl state)

theorem symm {left right : TypedCfg.Outcome}
    (hRel : RuntimeRel left right) :
    RuntimeRel right left := by
  cases hRel with
  | fallthrough hState =>
      exact .fallthrough hState.symm
  | jump label hState =>
      exact .jump label hState.symm
  | returnDispatch hState =>
      exact .returnDispatch hState.symm
  | halt kind hState =>
      exact .halt kind hState.symm
  | invalid hState =>
      exact .invalid hState.symm

theorem trans {first second third : TypedCfg.Outcome}
    (hFirst : RuntimeRel first second)
    (hSecond : RuntimeRel second third) :
    RuntimeRel first third := by
  cases hFirst <;> cases hSecond
  all_goals
    constructor
    exact Assembly.SameRuntimeData.trans ‹_› ‹_›

end RuntimeRel

def AdmissibleProgramStep :
    Except EVMException TypedCfg.Outcome → Prop
  | .ok (.fallthrough _) => False
  | .ok (.returnDispatch _) => False
  | _ => True

end Outcome

namespace Block

theorem openRunBody_runtimeRel
    {body : List TypedCfg.Instr} {input output : Shape}
    {target source : EVMState}
    (hType : TypedCfg.Block.bodyType? body input = some output)
    (hIndependent :
      body.Forall TypedCfg.Instr.ProgramCounterIndependent)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel (Instr.RuntimeAtRel output)
      (InteractionSemantics.Block.openRunBody body input target)
      (InteractionSemantics.Block.openRunBody body input source) := by
  induction body generalizing input target source with
  | nil =>
      simp [TypedCfg.Block.bodyType?] at hType
      subst output
      exact
        .done
          (.ok ⟨hRel, rfl, rfl⟩)
  | cons instr rest ih =>
      rcases
          (List.forall_cons
            TypedCfg.Instr.ProgramCounterIndependent instr rest).mp
            hIndependent with
        ⟨hHeadIndependent, hTailIndependent⟩
      cases hHeadType : instr.type? input with
      | none =>
          simp [TypedCfg.Block.bodyType?, hHeadType] at hType
      | some middle =>
          have hTailType :
              TypedCfg.Block.bodyType? rest middle = some output := by
            simpa [TypedCfg.Block.bodyType?, hHeadType] using hType
          have hHead :=
            Instr.openRunAt_runtimeRel
              hHeadType hHeadIndependent hRel
          unfold InteractionSemantics.Block.openRunBody
            Control.Block.runBody
          apply Simulation.Interaction.Rel.bind hHead
          intro targetPair sourcePair hPair
          rcases targetPair with ⟨targetAfter, targetShape⟩
          rcases sourcePair with ⟨sourceAfter, sourceShape⟩
          rcases hPair with
            ⟨hAfter, hTargetShape, hSourceShape⟩
          change
            Assembly.SameRuntimeData targetAfter sourceAfter at hAfter
          change targetShape = middle at hTargetShape
          change sourceShape = middle at hSourceShape
          subst targetShape
          subst sourceShape
          exact
            ih hTailType hTailIndependent hAfter

theorem runTerm_runtimeRel
    {shape : Shape} {term : TypedCfg.Terminator}
    {target source : EVMState}
    (hRel : Assembly.SameRuntimeData target source) :
    Outcome.RuntimeRel
      (TypedCfg.Block.runTerm shape term target)
      (TypedCfg.Block.runTerm shape term source) := by
  have hStack : target.stack = source.stack :=
    Assembly.SameRuntimeData.stack_eq hRel
  cases term with
  | fallthrough next =>
      exact .jump next hRel
  | jump next =>
      exact .jump next hRel
  | jumpi targetLabel fallthroughLabel =>
      simp only [TypedCfg.Block.runTerm]
      rw [hStack]
      cases hPop : source.stack.pop with
      | none =>
          exact .invalid hRel
      | some pair =>
          rcases pair with ⟨stack, cond⟩
          have hReplace :
              Assembly.SameRuntimeData
                { target with stack := stack }
                { source with stack := stack } :=
            Assembly.SameRuntimeData.replaceStack hRel rfl
          by_cases hZero : cond = EvmYul.UInt256.ofNat 0
          · simp [hZero]
            exact .jump fallthroughLabel hReplace
          · simp [hZero]
            exact .jump targetLabel hReplace
  | returnDispatch returnCount sites =>
      simp only [TypedCfg.Block.runTerm]
      rw [hStack]
      cases hDepth : shape.returnTokenDepth? with
      | none =>
          exact .invalid hRel
      | some depth =>
          by_cases hCount : depth = returnCount
          · subst depth
            cases hToken : source.stack[returnCount]? with
            | none =>
                simp [hToken]
                exact .invalid hRel
            | some token =>
                cases hFind :
                    TypedCfg.Block.ReturnSite.findTarget? token sites with
                | none =>
                    simp [hToken, hFind]
                    exact .invalid hRel
                | some next =>
                    have hReplace :
                        Assembly.SameRuntimeData
                          { target with
                            stack := source.stack.eraseIdx returnCount }
                          { source with
                            stack := source.stack.eraseIdx returnCount } :=
                      Assembly.SameRuntimeData.replaceStack hRel rfl
                    simp [hToken, hFind]
                    exact .jump next hReplace
          · simp [hCount]
            exact .invalid hRel
  | halt kind =>
      exact .halt kind hRel
  | invalid =>
      exact .invalid hRel

abbrev RuntimeOutcomeRel :
    Except EVMException TypedCfg.Outcome →
      Except EVMException TypedCfg.Outcome → Prop :=
  Simulation.Interaction.ExceptRel
    (fun left right : EVMException => left = right)
    Outcome.RuntimeRel

theorem openRun_runtimeRel
    {program : TypedCfg.Program} {block : TypedCfg.Block}
    {target source : EVMState}
    (hTyped : block.WellTyped program)
    (hIndependent : block.ProgramCounterIndependent)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel RuntimeOutcomeRel
      (InteractionSemantics.Block.openRun block target)
      (InteractionSemantics.Block.openRun block source) := by
  have hBody :=
    openRunBody_runtimeRel hTyped.1 hIndependent hRel
  unfold InteractionSemantics.Block.openRun
    Control.Block.run
  apply Simulation.Interaction.Rel.bind hBody
  intro targetPair sourcePair hPair
  rcases targetPair with ⟨targetAfter, targetOutput⟩
  rcases sourcePair with ⟨sourceAfter, sourceOutput⟩
  rcases hPair with
    ⟨hAfter, hTargetOutput, hSourceOutput⟩
  change Assembly.SameRuntimeData targetAfter sourceAfter at hAfter
  change targetOutput = block.output at hTargetOutput
  change sourceOutput = block.output at hSourceOutput
  subst targetOutput
  subst sourceOutput
  simp
  exact
    .done
      (.ok (runTerm_runtimeRel hAfter))

theorem openRun_admissibleProgramStep
    (block : TypedCfg.Block) (state : EVMState) :
    Simulation.Interaction.AllDone Outcome.AdmissibleProgramStep
      (InteractionSemantics.Block.openRun block state) := by
  unfold InteractionSemantics.Block.openRun
    Control.Block.run
  apply
    Simulation.Interaction.AllDone.bind
      (Simulation.Interaction.AllDone.trivial
        (InteractionSemantics.Block.openRunBody
          block.body block.input state))
  · intro error _
    trivial
  · intro result _
    rcases result with ⟨final, output⟩
    by_cases hOutput : output = block.output
    · subst output
      simp only
      apply Simulation.Interaction.AllDone.done
      have hNoFallthrough :=
        TypedCfg.Block.runTerm_ne_fallthrough
          block.output block.term final
      have hNoReturnDispatch :=
        TypedCfg.Block.runTerm_ne_returnDispatch
          block.output block.term final
      cases hRun :
          TypedCfg.Block.runTerm block.output block.term final with
      | fallthrough fallthroughState =>
          exact
            (hNoFallthrough fallthroughState hRun).elim
      | jump next jumpState =>
          trivial
      | returnDispatch dispatchState =>
          exact
            (hNoReturnDispatch dispatchState hRun).elim
      | halt kind haltState =>
          trivial
      | invalid invalidState =>
          trivial
    · exact
        (by
          simp only [hOutput, if_false]
          exact .done True.intro)

end Block

namespace Program

/--
One TypedCfg CFG step is a congruence under runtime-data related states. This
is the control interface needed to compose compiled blocks after symbolic
jumps; unlike the historical replay predicate, it permits all external effects.
-/
theorem openStep_runtimeRel
    {program : TypedCfg.Program} {label : Label}
    {target source : EVMState}
    (hTyped : program.WellTyped)
    (hIndependent : program.ProgramCounterIndependent)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel Block.RuntimeOutcomeRel
      (InteractionSemantics.Program.openStep program label target)
      (InteractionSemantics.Program.openStep program label source) := by
  cases hFind : program.findBlock? label with
  | none =>
      simpa [InteractionSemantics.Program.openStep,
        Control.Program.step, hFind] using
          (Simulation.Interaction.Rel.done
            (Simulation.Interaction.ExceptRel.ok
              (Outcome.RuntimeRel.invalid hRel)))
  | some block =>
      have hMem : block ∈ program.blocks := by
        unfold TypedCfg.Program.findBlock? at hFind
        exact List.mem_of_find?_eq_some hFind
      have hBlockTyped : block.WellTyped program :=
        (List.forall_iff_forall_mem.mp hTyped.2.1) block hMem
      have hBlockIndependent : block.ProgramCounterIndependent :=
        (List.forall_iff_forall_mem.mp hIndependent) block hMem
      simpa [InteractionSemantics.Program.openStep,
        Control.Program.step, hFind] using
          Block.openRun_runtimeRel
            hBlockTyped hBlockIndependent hRel

theorem openStep_admissibleProgramStep
    (program : TypedCfg.Program) (label : Label)
    (state : EVMState) :
    Simulation.Interaction.AllDone Outcome.AdmissibleProgramStep
      (InteractionSemantics.Program.openStep program label state) := by
  cases hFind : program.findBlock? label with
  | none =>
      simp only [InteractionSemantics.Program.openStep,
        Control.Program.step, hFind]
      exact .done True.intro
  | some block =>
      simpa [InteractionSemantics.Program.openStep,
        Control.Program.step, hFind] using
          Block.openRun_admissibleProgramStep block state

end Program

end InteractionCongruence
end TypedCfg
end EvmCompiler
