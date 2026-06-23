import EvmCompiler.Assembly.InteractionSemantics
import EvmCompiler.TypedCfg.Control
import EvmCompiler.TypedCfg.Lower

namespace EvmCompiler
namespace TypedCfg
namespace InteractionSemantics

abbrev OpenStep :=
  Simulation.Interaction EVMException EVMState

abbrev OpenOutcome :=
  Simulation.Interaction EVMException TypedCfg.Outcome

namespace Instr

/--
The TypedCfg instruction specialization of the shared open semantics.

Every primitive delegates to the Assembly-owned primitive semantics. All
TypedCfg-only bookkeeping instructions embed their ordinary authoritative
semantics.
-/
def openRunState (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) : OpenStep :=
  match instr with
  | .prim op =>
      Assembly.InteractionSemantics.PrimOp.openStep op state
  | _ =>
      .done (TypedCfg.Instr.runState instr shape state)

def openRunAt (instr : TypedCfg.Instr) (shape : Shape)
    (state : EVMState) :
    Simulation.Interaction EVMException (EVMState × Shape) :=
  Control.Instr.runAt openRunState instr shape state

/--
Non-primitive TypedCfg instructions embed their ordinary state transition
directly in the interaction carrier.
-/
theorem openRunState_eq_done_of_not_prim
    {instr : TypedCfg.Instr} {shape : Shape} {state : EVMState}
    (hNonPrim : ∀ op, instr ≠ .prim op) :
    openRunState instr shape state =
      .done (TypedCfg.Instr.runState instr shape state) := by
  cases instr with
  | prim op =>
      exact False.elim (hNonPrim op rfl)
  | push value
  | returnToken value
  | pop
  | dup depth
  | swap depth
  | bindLocals offset names
  | bindScratch baseDepth name slot
  | relabel targetShape
  | unwind targetShape =>
      rfl

/--
TypedCfg bookkeeping instructions embed the ordinary instruction semantics
without producing an interaction node.
-/
theorem openRunAt_eq_done_of_not_prim
    {instr : TypedCfg.Instr} {shape : Shape} {state : EVMState}
    (hNonPrim : ∀ op, instr ≠ .prim op) :
    openRunAt instr shape state =
      .done (TypedCfg.Instr.runAt instr shape state) := by
  unfold openRunAt Control.Instr.runAt TypedCfg.Instr.runAt
  cases hType : instr.type? shape with
  | none =>
      change
        Simulation.Interaction.bind
            (Simulation.Interaction.error .InvalidInstruction)
            (fun output =>
              Simulation.Interaction.bind
                (openRunState instr shape state)
                (fun state' =>
                  Simulation.Interaction.pure (state', output))) =
          .done (.error .InvalidInstruction)
      rfl
  | some output =>
      rw [openRunState_eq_done_of_not_prim hNonPrim]
      cases hRun : TypedCfg.Instr.runState instr shape state with
      | error err =>
          simp [
            hType, hRun, Simulation.Interaction.instMonad,
            Simulation.Interaction.bind, Simulation.Interaction.pure]
      | ok final =>
          simp [
            hType, hRun, Simulation.Interaction.instMonad,
            Simulation.Interaction.bind, Simulation.Interaction.pure]

@[simp] theorem openRunState_gas (shape : Shape) (state : EVMState) :
    openRunState (.prim .gas) shape state =
      Assembly.InteractionSemantics.PrimOp.resourceStep
        .gas state := rfl

@[simp] theorem openRunState_msize (shape : Shape) (state : EVMState) :
    openRunState (.prim .msize) shape state =
      Assembly.InteractionSemantics.PrimOp.resourceStep
        .msize state := rfl

@[simp] theorem openRunState_call (shape : Shape) (state : EVMState) :
    openRunState (.prim .call) shape state =
      Assembly.InteractionSemantics.PrimOp.callStep
        .call state := rfl

@[simp] theorem openRunState_callcode
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .callcode) shape state =
      Assembly.InteractionSemantics.PrimOp.callStep
        .callcode state := rfl

@[simp] theorem openRunState_delegatecall
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .delegatecall) shape state =
      Assembly.InteractionSemantics.PrimOp.callStep
        .delegatecall state := rfl

@[simp] theorem openRunState_staticcall
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .staticcall) shape state =
      Assembly.InteractionSemantics.PrimOp.callStep
        .staticcall state := rfl

@[simp] theorem openRunState_create
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .create) shape state =
      Assembly.InteractionSemantics.PrimOp.createStep
        .create state := rfl

@[simp] theorem openRunState_create2
    (shape : Shape) (state : EVMState) :
    openRunState (.prim .create2) shape state =
      Assembly.InteractionSemantics.PrimOp.createStep
        .create2 state := rfl

end Instr

namespace Block

def openRunBody (body : List TypedCfg.Instr) (shape : Shape)
    (state : EVMState) :
    Simulation.Interaction EVMException (EVMState × Shape) :=
  Control.Block.runBody Instr.openRunState body shape state

/--
A body containing only TypedCfg bookkeeping instructions is exactly the
ordinary body evaluator embedded as one completed interaction.
-/
theorem openRunBody_eq_done_of_forall_not_prim
    {body : List TypedCfg.Instr} {shape : Shape} {state : EVMState}
    (hNonPrim : ∀ instr ∈ body, ∀ op, instr ≠ .prim op) :
    openRunBody body shape state =
      .done (TypedCfg.Block.runBody body shape state) := by
  induction body generalizing shape state with
  | nil =>
      rfl
  | cons instr rest ih =>
      unfold openRunBody
      change
        Simulation.Interaction.bind
            (Instr.openRunAt instr shape state)
            (fun result =>
              openRunBody rest result.2 result.1) =
          .done (TypedCfg.Block.runBody (instr :: rest) shape state)
      rw [Instr.openRunAt_eq_done_of_not_prim
        (hNonPrim instr (by simp))]
      cases hRun : TypedCfg.Instr.runAt instr shape state with
      | error err =>
          simp [TypedCfg.Block.runBody, hRun]
      | ok result =>
          rcases result with ⟨nextState, nextShape⟩
          simp only [Simulation.Interaction.bind_done_ok]
          simp only [TypedCfg.Block.runBody, hRun]
          rw [ih (fun member hMember op =>
            hNonPrim member (by simp [hMember]) op)]
          rfl

def openRun (block : TypedCfg.Block) (state : EVMState) :
    OpenOutcome :=
  Control.Block.run Instr.openRunState block state

end Block

namespace Terminator

/--
Generated return-dispatch tests use conditional jumps to enter their selected
case. The final jump from a case is unconditional and remains source-visible.
-/
def returnDispatchFlowPolicy : Assembly.Instr → Bool
  | .jumpi _ => true
  | _ => false

def assemblyFlowPolicy : TypedCfg.Terminator → Assembly.Instr → Bool
  | .returnDispatch _ _ => returnDispatchFlowPolicy
  | _ => fun _ => false

@[simp] theorem returnDispatchFlowPolicy_jumpi (label : Label) :
    returnDispatchFlowPolicy (.jumpi label) = true := rfl

@[simp] theorem returnDispatchFlowPolicy_jump (label : Label) :
    returnDispatchFlowPolicy (.jump label) = false := rfl

end Terminator

namespace CompiledBlock

def fuelBudget (block : TypedCfg.Block) : Nat :=
  match TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none => 0
  | some (bodyCode, output) =>
      if output = block.output then
        match block.term.lowerAt? output with
        | none => 0
        | some termCode => 1 + bodyCode.length + termCode.length
      else
        0

/--
Execute one lowered TypedCfg block through the canonical Assembly runners.

The existing compiler selects the body and terminator fragments. This adapter
only sequences label execution, straight-line body execution, and the
terminator-owned transfer policy; it defines no primitive or external-effect
semantics of its own.
-/
def openRun (block : TypedCfg.Block)
    (program : Assembly.Program) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      .done (.error .InvalidInstruction)
  | some (bodyCode, output) =>
      if output = block.output then
        match block.term.lowerAt? output with
        | none =>
            .done (.error .InvalidInstruction)
        | some termCode => do
            let labelResult ←
              Assembly.InteractionSemantics.Source.openRunNResult
                program 1 state
            match labelResult with
            | .halted halt =>
                pure (.halted halt)
            | .running entry =>
                let bodyResult ←
                  Assembly.InteractionSemantics.Source.openRunNResult
                    program bodyCode.length entry
                match bodyResult with
                | .halted halt =>
                    pure (.halted halt)
                | .running mid =>
                    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                      (Terminator.assemblyFlowPolicy block.term)
                      program termCode.length mid
      else
        .done (.error .InvalidInstruction)

/-- One compiler-selected block execution is a bounded prefix of ordinary
Assembly source execution. -/
theorem openRun_executes_source_bounded
    {block : TypedCfg.Block} {program : Assembly.Program}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : Assembly.StepResult}
    (hExec : Simulation.Interaction.Executes
      (openRun block program state) transcript (.ok result)) :
    exists usedFuel,
      usedFuel <= fuelBudget block /\
        Simulation.Interaction.Executes
          (Assembly.InteractionSemantics.Source.openRunNResult
            program usedFuel state)
          transcript (.ok result) := by
  unfold openRun at hExec
  cases hBody : TypedCfg.Block.lowerBodyFrom?
      block.body block.input with
  | none =>
      simp only [hBody] at hExec
      cases hExec
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      simp only [hBody] at hExec
      by_cases hOutput : output = block.output
      · rw [if_pos hOutput] at hExec
        subst output
        cases hTerm : block.term.lowerAt? block.output with
        | none =>
            simp only [hTerm] at hExec
            cases hExec
        | some termCode =>
            simp only [hTerm] at hExec
            have hBudget : fuelBudget block =
                1 + bodyCode.length + termCode.length := by
              simp [fuelBudget, hBody, hTerm]
            rcases Simulation.Interaction.Executes.bind_cases hExec with
              hLabelError | hLabelOk
            · rcases hLabelError with
                ⟨error, hOutcome, _hLabel⟩
              cases hOutcome
            · rcases hLabelOk with
                ⟨labelResult, labelTranscript, restTranscript,
                  hTranscript, hLabel, hRest⟩
              subst transcript
              cases labelResult with
              | halted halt =>
                  cases hRest
                  refine ⟨1, by rw [hBudget]; omega, ?_⟩
                  simpa using hLabel
              | running entry =>
                  rcases Simulation.Interaction.Executes.bind_cases hRest with
                    hBodyError | hBodyOk
                  · rcases hBodyError with
                      ⟨error, hOutcome, _hBodyRun⟩
                    cases hOutcome
                  · rcases hBodyOk with
                      ⟨bodyResult, bodyTranscript, termTranscript,
                        hRestTranscript, hBodyRun, hTermRun⟩
                    subst restTranscript
                    cases bodyResult with
                    | halted halt =>
                        cases hTermRun
                        refine
                          ⟨1 + bodyCode.length,
                            by rw [hBudget]; omega, ?_⟩
                        rw [
                          Assembly.InteractionSemantics.Source.openRunNResult_add]
                        simpa [List.append_assoc] using
                          Simulation.Interaction.Executes.bind_ok
                            hLabel hBodyRun
                    | running mid =>
                        obtain ⟨termFuel, hTermFuel, hTermExec⟩ :=
                          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy_executes_openRunNResult_bounded
                            hTermRun
                        have hLabelBody : Simulation.Interaction.Executes
                            (Assembly.InteractionSemantics.Source.openRunNResult
                              program (1 + bodyCode.length) state)
                            (labelTranscript ++ bodyTranscript)
                            (.ok (.running mid)) := by
                          rw [
                            Assembly.InteractionSemantics.Source.openRunNResult_add]
                          exact Simulation.Interaction.Executes.bind_ok
                            hLabel hBodyRun
                        refine
                          ⟨1 + bodyCode.length + termFuel,
                            by rw [hBudget]; omega, ?_⟩
                        rw [
                          Assembly.InteractionSemantics.Source.openRunNResult_add]
                        simpa [List.append_assoc] using
                          Simulation.Interaction.Executes.bind_ok
                            hLabelBody hTermExec
      · rw [if_neg hOutput] at hExec
        cases hExec

/-- For a successfully lowered block, every compiler-selected error execution
is an exact bounded prefix of ordinary Assembly source execution. -/
theorem openRun_error_executes_source_bounded
    {block : TypedCfg.Block} {program code : Assembly.Program}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {sourceError : EVMException}
    (hLower : block.lower? = some code)
    (hExec : Simulation.Interaction.Executes
      (openRun block program state) transcript (.error sourceError)) :
    exists usedFuel,
      usedFuel <= fuelBudget block /\
        Simulation.Interaction.Executes
          (Assembly.InteractionSemantics.Source.openRunNResult
            program usedFuel state)
          transcript (.error sourceError) := by
  unfold TypedCfg.Block.lower? at hLower
  unfold openRun at hExec
  cases hBody : TypedCfg.Block.lowerBodyFrom?
      block.body block.input with
  | none => simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      simp only [hBody] at hExec hLower
      by_cases hOutput : output = block.output
      · rw [if_pos hOutput] at hExec
        subst output
        cases hTerm : block.term.lowerAt? block.output with
        | none => simp [hTerm] at hLower
        | some termCode =>
            simp only [hTerm] at hExec hLower
            have hBudget : fuelBudget block =
                1 + bodyCode.length + termCode.length := by
              simp [fuelBudget, hBody, hTerm]
            rcases Simulation.Interaction.Executes.bind_cases hExec with
              hLabelError | hLabelOk
            · rcases hLabelError with ⟨error, hOutcome, hLabel⟩
              cases hOutcome
              refine ⟨1, by rw [hBudget]; omega, ?_⟩
              simpa using hLabel
            · rcases hLabelOk with
                ⟨labelResult, labelTranscript, restTranscript,
                  hTranscript, hLabel, hRest⟩
              subst transcript
              cases labelResult with
              | halted halt => cases hRest
              | running entry =>
                  rcases Simulation.Interaction.Executes.bind_cases hRest with
                    hBodyError | hBodyOk
                  · rcases hBodyError with
                      ⟨error, hOutcome, hBodyRun⟩
                    cases hOutcome
                    refine
                      ⟨1 + bodyCode.length,
                        by rw [hBudget]; omega, ?_⟩
                    rw [
                      Assembly.InteractionSemantics.Source.openRunNResult_add]
                    exact Simulation.Interaction.Executes.bind_ok
                      hLabel hBodyRun
                  · rcases hBodyOk with
                      ⟨bodyResult, bodyTranscript, termTranscript,
                        hRestTranscript, hBodyRun, hTermRun⟩
                    subst restTranscript
                    cases bodyResult with
                    | halted halt => cases hTermRun
                    | running mid =>
                        obtain ⟨termFuel, hTermFuel, hTermExec⟩ :=
                          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy_error_executes_openRunNResult_bounded
                            hTermRun
                        have hLabelBody : Simulation.Interaction.Executes
                            (Assembly.InteractionSemantics.Source.openRunNResult
                              program (1 + bodyCode.length) state)
                            (labelTranscript ++ bodyTranscript)
                            (.ok (.running mid)) := by
                          rw [
                            Assembly.InteractionSemantics.Source.openRunNResult_add]
                          exact Simulation.Interaction.Executes.bind_ok
                            hLabel hBodyRun
                        refine
                          ⟨1 + bodyCode.length + termFuel,
                            by rw [hBudget]; omega, ?_⟩
                        rw [
                          Assembly.InteractionSemantics.Source.openRunNResult_add]
                        simpa [List.append_assoc] using
                          Simulation.Interaction.Executes.bind_ok
                            hLabelBody hTermExec
      · simp [hOutput] at hLower

end CompiledBlock

namespace CompiledProgram

def fuelBudget (source : TypedCfg.Program) : Nat :=
  (source.blocks.map CompiledBlock.fuelBudget).sum

theorem block_fuelBudget_le_of_findBlock?
    {source : TypedCfg.Program} {label : Label} {block : TypedCfg.Block}
    (hFind : source.findBlock? label = some block) :
    CompiledBlock.fuelBudget block <= fuelBudget source := by
  have hMem : block ∈ source.blocks := by
    exact List.mem_of_find?_eq_some hFind
  unfold fuelBudget
  have aux : forall blocks : List TypedCfg.Block,
      block ∈ blocks ->
        CompiledBlock.fuelBudget block <=
          (blocks.map CompiledBlock.fuelBudget).sum := by
    intro blocks hBlock
    induction blocks with
    | nil => simp at hBlock
    | cons head tail ih =>
        simp only [List.mem_cons] at hBlock
        simp only [List.map_cons, List.sum_cons]
        rcases hBlock with hHead | hTail
        · subst head
          omega
        · exact Nat.le_trans (ih hTail) (by omega)
  exact aux source.blocks hMem

/--
Execute one compiled TypedCfg block selected by the concrete Assembly program
counter. Only an Assembly label at the current PC may enter a source block.
The source program supplies immutable block syntax; control selection remains
entirely target-driven.
-/
def openStep (source : TypedCfg.Program)
    (target : Assembly.Program) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match target.instrAtPc state.pc.toNat with
  | some (_, .label label) =>
      match source.findBlock? label with
      | some block =>
          CompiledBlock.openRun block target state
      | none =>
          .done (.error .InvalidInstruction)
  | _ =>
      .done (.error .InvalidInstruction)

def openRunN (source : TypedCfg.Program)
    (target : Assembly.Program) (fuel : Nat) (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult :=
  Assembly.Control.runNResultWith
    (openStep source target) fuel state

@[simp] theorem openRunN_zero
    (source : TypedCfg.Program) (target : Assembly.Program)
    (state : EVMState) :
    openRunN source target 0 state =
      .done (.ok (.running state)) := rfl

theorem openRunN_succ
    (source : TypedCfg.Program) (target : Assembly.Program)
    (fuel : Nat) (state : EVMState) :
    openRunN source target (fuel + 1) state =
      (do
        let result ← openStep source target state
        match result with
        | .running state' =>
            openRunN source target fuel state'
        | .halted halt =>
            pure (.halted halt)) := rfl

theorem openStep_executes_source_bounded
    {source : TypedCfg.Program} {target : Assembly.Program}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : Assembly.StepResult}
    (hExec : Simulation.Interaction.Executes
      (openStep source target state) transcript (.ok result)) :
    exists usedFuel,
      usedFuel <= fuelBudget source /\
        Simulation.Interaction.Executes
          (Assembly.InteractionSemantics.Source.openRunNResult
            target usedFuel state)
          transcript (.ok result) := by
  unfold openStep at hExec
  cases hAt : target.instrAtPc state.pc.toNat with
  | none =>
      simp only [hAt] at hExec
      cases hExec
  | some located =>
      rcases located with ⟨pc, instr⟩
      simp only [hAt] at hExec
      cases instr with
      | label label =>
          cases hFind : source.findBlock? label with
          | none =>
              simp only [hFind] at hExec
              cases hExec
          | some block =>
              simp only [hFind] at hExec
              obtain ⟨usedFuel, hUsed, hSource⟩ :=
                CompiledBlock.openRun_executes_source_bounded hExec
              exact
                ⟨usedFuel,
                  Nat.le_trans hUsed
                    (block_fuelBudget_le_of_findBlock? hFind),
                  hSource⟩
      | prim op | push op | pushLabel op | jump op | jumpi op =>
          cases hExec
      | jumpDynamic =>
          cases hExec

theorem openRunN_executes_source_bounded
    {source : TypedCfg.Program} {target : Assembly.Program}
    {fuel : Nat} {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : Assembly.StepResult}
    (hExec : Simulation.Interaction.Executes
      (openRunN source target fuel state) transcript (.ok result)) :
    exists usedFuel,
      usedFuel <= fuel * fuelBudget source /\
        Simulation.Interaction.Executes
          (Assembly.InteractionSemantics.Source.openRunNResult
            target usedFuel state)
          transcript (.ok result) := by
  induction fuel generalizing state transcript result with
  | zero =>
      rw [openRunN_zero] at hExec
      cases hExec
      refine ⟨0, by simp, ?_⟩
      exact Simulation.Interaction.Executes.done
        (.ok (Assembly.StepResult.running state) :
          Except EVMException Assembly.StepResult)
  | succ fuel ih =>
      rw [openRunN_succ] at hExec
      rcases Simulation.Interaction.Executes.bind_cases hExec with
        hStepError | hStepOk
      · rcases hStepError with ⟨error, hOutcome, _hStep⟩
        cases hOutcome
      · rcases hStepOk with
          ⟨stepResult, headTranscript, restTranscript,
            hTranscript, hStep, hRest⟩
        subst transcript
        obtain ⟨headFuel, hHeadFuel, hHead⟩ :=
          openStep_executes_source_bounded hStep
        cases stepResult with
        | halted halt =>
            cases hRest
            refine ⟨headFuel, ?_, by simpa using hHead⟩
            rw [Nat.add_mul]
            omega
        | running mid =>
            obtain ⟨tailFuel, hTailFuel, hTail⟩ := ih hRest
            refine ⟨headFuel + tailFuel, ?_, ?_⟩
            · rw [Nat.add_mul]
              omega
            · rw [
                Assembly.InteractionSemantics.Source.openRunNResult_add]
              exact Simulation.Interaction.Executes.bind_ok hHead hTail

/-- Universally terminal compiler-selected block execution is structurally
related to one ordinary Assembly source run at a source-program-owned budget. -/
theorem openRunN_rel_source_terminal
    {source : TypedCfg.Program} {target : Assembly.Program}
    {fuel : Nat} {state : EVMState}
    (hTerminal : Simulation.Interaction.AllDone
      Assembly.InteractionSemantics.Terminal
      (openRunN source target fuel state)) :
    Simulation.Interaction.Rel Eq
      (openRunN source target fuel state)
      (Assembly.InteractionSemantics.Source.openRunNResult
        target (fuel * fuelBudget source) state) := by
  apply Simulation.Interaction.Rel.of_successful_executes
    (Assembly.InteractionSemantics.Terminal.successful hTerminal)
  intro transcript sourceResult hSourceExec
  have hSourceTerminal :=
    Simulation.Interaction.AllDone.property_of_executes
      hTerminal hSourceExec
  cases sourceResult with
  | running sourceFinal => cases hSourceTerminal
  | halted halt =>
      obtain ⟨usedFuel, hUsedFuel, hAssemblyExec⟩ :=
        openRunN_executes_source_bounded hSourceExec
      let extra := fuel * fuelBudget source - usedFuel
      have hFuel : usedFuel + extra = fuel * fuelBudget source :=
        Nat.add_sub_of_le hUsedFuel
      have hPadded :=
        Assembly.InteractionSemantics.Source.openRunNResult_halted_add_executes
          (extra := extra) hAssemblyExec
      rw [hFuel] at hPadded
      exact ⟨.ok (.halted halt), hPadded, rfl⟩

end CompiledProgram

namespace Program

def openStep (program : TypedCfg.Program) (label : Label)
    (state : EVMState) : OpenOutcome :=
  Control.Program.step Instr.openRunState program label state

def openRunNWithStop (stopJump : Label → EVMState → Bool)
    (program : TypedCfg.Program) (fuel : Nat)
    (label : Label) (state : EVMState) : OpenOutcome :=
  Control.Program.runNWithStop
    Instr.openRunState stopJump program fuel label state

abbrev OpenRunResult :=
  Simulation.Interaction EVMException Control.Program.RunResult

def openRunNResultWithStop (stopJump : Label → EVMState → Bool)
    (program : TypedCfg.Program) (fuel : Nat)
    (label : Label) (state : EVMState) : OpenRunResult :=
  Control.Program.runNResultWithStop
    Instr.openRunState stopJump program fuel label state

def afterOpenStepResultWithStop
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (fuel : Nat) : TypedCfg.Outcome → OpenRunResult
  | .jump next state =>
      if stopJump next state then
        pure (.stopped fuel (.jump next state))
      else
        openRunNResultWithStop stopJump program fuel next state
  | .fallthrough state =>
      pure (.stopped fuel (.fallthrough state))
  | .returnDispatch state =>
      pure (.stopped fuel (.returnDispatch state))
  | .halt kind state =>
      pure (.stopped fuel (.halt kind state))
  | .invalid state =>
      pure (.stopped fuel (.invalid state))

def openRunN (program : TypedCfg.Program) (fuel : Nat)
    (label : Label) (state : EVMState) : OpenOutcome :=
  openRunNWithStop (fun _ _ => false)
    program fuel label state

@[simp] theorem openRunNWithStop_zero
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (label : Label) (state : EVMState) :
    openRunNWithStop stopJump program 0 label state =
      .done (.ok (.jump label state)) := rfl

theorem openRunNWithStop_succ
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (fuel : Nat) (label : Label) (state : EVMState) :
    openRunNWithStop stopJump program (fuel + 1) label state =
      (do
        let outcome ← openStep program label state
        match outcome with
        | .jump next state' =>
            if stopJump next state' then
              pure (.jump next state')
            else
              openRunNWithStop stopJump
                program fuel next state'
        | .fallthrough state' => pure (.fallthrough state')
        | .returnDispatch state' => pure (.returnDispatch state')
        | .halt kind state' => pure (.halt kind state')
        | .invalid state' => pure (.invalid state')) := rfl

@[simp] theorem openRunNResultWithStop_zero
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (label : Label) (state : EVMState) :
    openRunNResultWithStop stopJump program 0 label state =
      .done (.ok (.exhausted label state)) := rfl

theorem openRunNResultWithStop_succ
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (fuel : Nat) (label : Label) (state : EVMState) :
    openRunNResultWithStop stopJump
        program (fuel + 1) label state =
      (do
        let outcome ← openStep program label state
        match outcome with
        | .jump next state' =>
            if stopJump next state' then
              pure (.stopped fuel (.jump next state'))
            else
              openRunNResultWithStop stopJump
                program fuel next state'
        | .fallthrough state' =>
            pure (.stopped fuel (.fallthrough state'))
        | .returnDispatch state' =>
            pure (.stopped fuel (.returnDispatch state'))
        | .halt kind state' =>
            pure (.stopped fuel (.halt kind state'))
        | .invalid state' =>
            pure (.stopped fuel (.invalid state'))) := rfl

theorem openRunNResultWithStop_succ_eq_bind
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (fuel : Nat) (label : Label) (state : EVMState) :
    openRunNResultWithStop stopJump
        program (fuel + 1) label state =
      Simulation.Interaction.bind
        (openStep program label state)
        (afterOpenStepResultWithStop
          stopJump program fuel) := rfl

@[simp] theorem openRunN_zero (program : TypedCfg.Program)
    (label : Label) (state : EVMState) :
    openRunN program 0 label state =
      .done (.ok (.jump label state)) := rfl

theorem openRunN_succ (program : TypedCfg.Program)
    (fuel : Nat) (label : Label) (state : EVMState) :
    openRunN program (fuel + 1) label state =
      (do
        let outcome ← openStep program label state
        match outcome with
        | .jump next state' =>
            openRunN program fuel next state'
        | .fallthrough state' => pure (.fallthrough state')
        | .returnDispatch state' => pure (.returnDispatch state')
        | .halt kind state' => pure (.halt kind state')
        | .invalid state' => pure (.invalid state')) := rfl

theorem openRunNWithStop_one
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (label : Label) (state : EVMState) :
    openRunNWithStop stopJump program 1 label state =
      openStep program label state := by
  rw [show 1 = 0 + 1 by rfl,
    openRunNWithStop_succ]
  have hContinuation :
      (fun outcome : TypedCfg.Outcome =>
        match outcome with
        | .jump next state' =>
            if stopJump next state' then
              pure (.jump next state')
            else
              openRunNWithStop stopJump
                program 0 next state'
        | .fallthrough state' => pure (.fallthrough state')
        | .returnDispatch state' => pure (.returnDispatch state')
        | .halt kind state' => pure (.halt kind state')
        | .invalid state' => pure (.invalid state')) =
        Simulation.Interaction.pure := by
    funext outcome
    cases outcome with
    | jump next state' =>
        change
          (if stopJump next state' = true then
            (Simulation.Interaction.pure
              (.jump next state') : OpenOutcome)
          else
            openRunNWithStop stopJump
              program 0 next state') =
            Simulation.Interaction.pure (.jump next state')
        by_cases hStop : stopJump next state' = true
        · simp [hStop]
        · simp [hStop]
          rfl
    | fallthrough state'
    | returnDispatch state'
    | halt kind state'
    | invalid state' =>
        rfl
  change
    Simulation.Interaction.bind
        (openStep program label state) _ =
      openStep program label state
  rw [hContinuation]
  exact Simulation.Interaction.bind_pure _

def continueOpenRunNResultWithStop
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (fuel : Nat) :
    Control.Program.RunResult → OpenRunResult
  | .exhausted label state =>
      openRunNResultWithStop stopJump program fuel label state
  | .stopped remaining outcome =>
      pure (.stopped (remaining + fuel) outcome)

/--
Tagged boundary execution composes exactly: exhausted fuel starts the next
segment, while an already reached semantic boundary remains stopped.
-/
theorem openRunNResultWithStop_add
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (firstFuel restFuel : Nat) (label : Label) (state : EVMState) :
    openRunNResultWithStop stopJump
        program (firstFuel + restFuel) label state =
      Simulation.Interaction.bind
        (openRunNResultWithStop stopJump
          program firstFuel label state)
        (continueOpenRunNResultWithStop
          stopJump program restFuel) := by
  induction firstFuel generalizing label state with
  | zero =>
      simp [continueOpenRunNResultWithStop]
  | succ firstFuel ih =>
      rw [show
        Nat.succ firstFuel + restFuel =
          (firstFuel + restFuel) + 1 by omega]
      rw [openRunNResultWithStop_succ,
        openRunNResultWithStop_succ]
      change
        Simulation.Interaction.bind
            (openStep program label state)
            (fun outcome =>
              match outcome with
              | .jump next state' =>
                  if stopJump next state' then
                    pure
                      (.stopped (firstFuel + restFuel)
                        (.jump next state'))
                  else
                    openRunNResultWithStop stopJump
                      program (firstFuel + restFuel) next state'
              | .fallthrough state' =>
                  pure
                    (.stopped (firstFuel + restFuel)
                      (.fallthrough state'))
              | .returnDispatch state' =>
                  pure
                    (.stopped (firstFuel + restFuel)
                      (.returnDispatch state'))
              | .halt kind state' =>
                  pure
                    (.stopped (firstFuel + restFuel)
                      (.halt kind state'))
              | .invalid state' =>
                  pure
                    (.stopped (firstFuel + restFuel)
                      (.invalid state'))) =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind
              (openStep program label state)
              (fun outcome =>
                match outcome with
                | .jump next state' =>
                    if stopJump next state' then
                      pure (.stopped firstFuel (.jump next state'))
                    else
                      openRunNResultWithStop stopJump
                        program firstFuel next state'
                | .fallthrough state' =>
                    pure (.stopped firstFuel (.fallthrough state'))
                | .returnDispatch state' =>
                    pure (.stopped firstFuel (.returnDispatch state'))
                | .halt kind state' =>
                    pure (.stopped firstFuel (.halt kind state'))
                | .invalid state' =>
                    pure (.stopped firstFuel (.invalid state'))))
            (continueOpenRunNResultWithStop
              stopJump program restFuel)
      rw [Simulation.Interaction.bind_assoc]
      apply congrArg (Simulation.Interaction.bind
        (openStep program label state))
      funext outcome
      cases outcome with
      | jump next state' =>
          by_cases hStop : stopJump next state' = true
          · simp [hStop, continueOpenRunNResultWithStop]
            rfl
          · simp [hStop, continueOpenRunNResultWithStop]
            exact ih next state'
      | fallthrough state'
      | returnDispatch state'
      | halt kind state'
      | invalid state' =>
          rfl

def continueOpenRunNResultWithRefinedStop
    (outerStop : Label → EVMState → Bool)
    (program : TypedCfg.Program) (extraFuel : Nat) :
    Control.Program.RunResult → OpenRunResult
  | .exhausted label state =>
      openRunNResultWithStop
        outerStop program extraFuel label state
  | .stopped remaining outcome =>
      afterOpenStepResultWithStop
        outerStop program (remaining + extraFuel) outcome

/--
An inner run may stop at every outer boundary plus additional internal
boundaries. Recording residual fuel makes the outer execution recoverable
exactly: outer boundaries remain stopped, while internal boundaries resume
with the unused inner budget plus the appended budget.
-/
theorem openRunNResultWithRefinedStop_add
    (outerStop innerStop : Label → EVMState → Bool)
    (program : TypedCfg.Program)
    (firstFuel extraFuel : Nat) (label : Label) (state : EVMState)
    (hRefines :
      ∀ next nextState,
        outerStop next nextState = true →
          innerStop next nextState = true) :
    openRunNResultWithStop outerStop
        program (firstFuel + extraFuel) label state =
      Simulation.Interaction.bind
        (openRunNResultWithStop innerStop
          program firstFuel label state)
        (continueOpenRunNResultWithRefinedStop
          outerStop program extraFuel) := by
  induction firstFuel generalizing label state with
  | zero =>
      simp [continueOpenRunNResultWithRefinedStop]
  | succ firstFuel ih =>
      rw [show
        Nat.succ firstFuel + extraFuel =
          (firstFuel + extraFuel) + 1 by omega]
      rw [openRunNResultWithStop_succ,
        openRunNResultWithStop_succ]
      change
        Simulation.Interaction.bind
            (openStep program label state)
            (fun outcome =>
              match outcome with
              | .jump next state' =>
                  if outerStop next state' then
                    pure
                      (.stopped (firstFuel + extraFuel)
                        (.jump next state'))
                  else
                    openRunNResultWithStop outerStop
                      program (firstFuel + extraFuel) next state'
              | .fallthrough state' =>
                  pure
                    (.stopped (firstFuel + extraFuel)
                      (.fallthrough state'))
              | .returnDispatch state' =>
                  pure
                    (.stopped (firstFuel + extraFuel)
                      (.returnDispatch state'))
              | .halt kind state' =>
                  pure
                    (.stopped (firstFuel + extraFuel)
                      (.halt kind state'))
              | .invalid state' =>
                  pure
                    (.stopped (firstFuel + extraFuel)
                      (.invalid state'))) =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind
              (openStep program label state)
              (fun outcome =>
                match outcome with
                | .jump next state' =>
                    if innerStop next state' then
                      pure (.stopped firstFuel (.jump next state'))
                    else
                      openRunNResultWithStop innerStop
                        program firstFuel next state'
                | .fallthrough state' =>
                    pure (.stopped firstFuel (.fallthrough state'))
                | .returnDispatch state' =>
                    pure (.stopped firstFuel (.returnDispatch state'))
                | .halt kind state' =>
                    pure (.stopped firstFuel (.halt kind state'))
                | .invalid state' =>
                    pure (.stopped firstFuel (.invalid state'))))
            (continueOpenRunNResultWithRefinedStop
              outerStop program extraFuel)
      rw [Simulation.Interaction.bind_assoc]
      apply congrArg (Simulation.Interaction.bind
        (openStep program label state))
      funext outcome
      cases outcome with
      | jump next state' =>
          by_cases hOuter : outerStop next state' = true
          · have hInner := hRefines next state' hOuter
            simp [
              hOuter, hInner,
              continueOpenRunNResultWithRefinedStop,
              afterOpenStepResultWithStop,
              Simulation.Interaction.instMonad,
              Simulation.Interaction.bind,
              Simulation.Interaction.pure]
          · by_cases hInner : innerStop next state' = true
            · simp [
                hOuter, hInner,
                continueOpenRunNResultWithRefinedStop,
                afterOpenStepResultWithStop,
                Simulation.Interaction.instMonad,
                Simulation.Interaction.bind,
                Simulation.Interaction.pure]
            · simp [
                hOuter, hInner,
                continueOpenRunNResultWithRefinedStop,
                Simulation.Interaction.instMonad,
                Simulation.Interaction.bind,
                Simulation.Interaction.pure]
              exact ih next state'
      | fallthrough state'
      | returnDispatch state'
      | halt kind state'
      | invalid state' =>
          simp [
            continueOpenRunNResultWithRefinedStop,
            afterOpenStepResultWithStop,
            Simulation.Interaction.instMonad,
            Simulation.Interaction.bind,
            Simulation.Interaction.pure]

def runResultOutcome : Control.Program.RunResult -> TypedCfg.Outcome
  | .exhausted label state => .jump label state
  | .stopped _ outcome => outcome

/-- Erasing residual fuel from the result runner recovers the outcome runner. -/
theorem map_openRunNResultWithStop_runResultOutcome
    (stopJump : Label -> EVMState -> Bool)
    (program : TypedCfg.Program) (fuel : Nat)
    (label : Label) (state : EVMState) :
    Simulation.Interaction.map runResultOutcome
        (openRunNResultWithStop stopJump program fuel label state) =
      openRunNWithStop stopJump program fuel label state := by
  induction fuel generalizing label state with
  | zero => rfl
  | succ fuel ih =>
      rw [openRunNResultWithStop_succ_eq_bind, openRunNWithStop_succ]
      unfold Simulation.Interaction.map
      rw [Simulation.Interaction.bind_assoc]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (openStep program label state))
      intro outcome _hDone
      cases outcome with
      | jump next nextState =>
          by_cases hStop : stopJump next nextState = true
          · simp [afterOpenStepResultWithStop, hStop,
              Simulation.Interaction.map, runResultOutcome,
              Simulation.Interaction.instMonad,
              Simulation.Interaction.bind,
              Simulation.Interaction.pure]
          · simp [afterOpenStepResultWithStop, hStop,
              Simulation.Interaction.map]
            exact ih next nextState
      | fallthrough final
      | returnDispatch final
      | halt kind final
      | invalid final =>
          rfl

/-- Successful stop-aware branches are terminal exactly when they halt. -/
def Halted : Except EVMException TypedCfg.Outcome -> Prop
  | .ok (.halt _ _) => True
  | _ => False

/-- Errors and EVM halts have both stopped execution; jumps and ordinary
control exits have not. -/
def Stopped : Except EVMException TypedCfg.Outcome -> Prop
  | .error _ => True
  | .ok (.halt _ _) => True
  | _ => False

/-- A TypedCfg halt whose corresponding Assembly terminal instruction is safe
to execute. -/
def AssemblySafeHalted : Except EVMException TypedCfg.Outcome -> Prop
  | .ok (.halt kind state) =>
      Assembly.InteractionSemantics.Terminal.SafeAt kind state
  | _ => False

/-- Runtime errors are already final; successful halts additionally require
the source-facing safety needed to execute their Assembly terminal primitive. -/
def AssemblySafeFinished : Except EVMException TypedCfg.Outcome -> Prop
  | .error _ => True
  | .ok (.halt kind state) =>
      Assembly.InteractionSemantics.Terminal.SafeAt kind state
  | _ => False

/-- A stop policy is inert when every branch already halts. -/
theorem openRunNWithStop_eq_openRunN_of_allDone_halted
    (stopJump : Label -> EVMState -> Bool)
    (program : TypedCfg.Program) (fuel : Nat)
    (label : Label) (state : EVMState)
    (hHalted : Simulation.Interaction.AllDone Halted
      (openRunNWithStop stopJump program fuel label state)) :
    openRunNWithStop stopJump program fuel label state =
      openRunN program fuel label state := by
  induction fuel generalizing label state with
  | zero =>
      cases hHalted with
      | done hDone => cases hDone
  | succ fuel ih =>
      rw [openRunNWithStop_succ, openRunN_succ]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.bind_inv hHalted)
      intro outcome hContinuation
      cases outcome with
      | jump next nextState =>
          change
            (if stopJump next nextState then
                pure (.jump next nextState)
              else
                openRunNWithStop stopJump program fuel next nextState) =
              openRunN program fuel next nextState
          change
            Simulation.Interaction.AllDone Halted
              (if stopJump next nextState then
                  pure (.jump next nextState)
                else
                  openRunNWithStop stopJump program fuel next nextState)
              at hContinuation
          by_cases hStop : stopJump next nextState = true
          · rw [hStop] at hContinuation
            cases hContinuation with
            | done hDone => cases hDone
          · rw [show stopJump next nextState = false by
                  exact Bool.eq_false_of_not_eq_true hStop]
              at hContinuation ⊢
            exact ih next nextState hContinuation
      | fallthrough final => rfl
      | returnDispatch final => rfl
      | halt kind final => rfl
      | invalid final => rfl

/-- A stop policy is inert when every branch has either errored or halted. -/
theorem openRunNWithStop_eq_openRunN_of_allDone_stopped
    (stopJump : Label -> EVMState -> Bool)
    (program : TypedCfg.Program) (fuel : Nat)
    (label : Label) (state : EVMState)
    (hStopped : Simulation.Interaction.AllDone Stopped
      (openRunNWithStop stopJump program fuel label state)) :
    openRunNWithStop stopJump program fuel label state =
      openRunN program fuel label state := by
  induction fuel generalizing label state with
  | zero => rfl
  | succ fuel ih =>
      rw [openRunNWithStop_succ, openRunN_succ]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.bind_inv hStopped)
      intro outcome hContinuation
      cases outcome with
      | jump next nextState =>
          change
            (if stopJump next nextState then
                pure (.jump next nextState)
              else
                openRunNWithStop stopJump program fuel next nextState) =
              openRunN program fuel next nextState
          change
            Simulation.Interaction.AllDone Stopped
              (if stopJump next nextState then
                  pure (.jump next nextState)
                else
                  openRunNWithStop stopJump program fuel next nextState)
              at hContinuation
          by_cases hStop : stopJump next nextState = true
          · rw [hStop] at hContinuation
            cases hContinuation with
            | done hDone => cases hDone
          · rw [show stopJump next nextState = false by
                  exact Bool.eq_false_of_not_eq_true hStop]
                at hContinuation ⊢
            exact ih next nextState hContinuation
      | fallthrough final => rfl
      | returnDispatch final => rfl
      | halt kind final => rfl
      | invalid final => rfl

def RunResultStopped :
    Except EVMException Control.Program.RunResult → Prop
  | .error _ => True
  | .ok (.exhausted _ _) => False
  | .ok (.stopped _ _) => True

def addFuelToRunResult (extra : Nat) :
    Control.Program.RunResult → Control.Program.RunResult
  | .exhausted label state => .exhausted label state
  | .stopped remaining outcome =>
      .stopped (remaining + extra) outcome

theorem continueOpenRunNResultWithStop_eq_pure_addFuel
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (fuel : Nat) (result : Control.Program.RunResult)
    (hStopped : RunResultStopped (.ok result)) :
    continueOpenRunNResultWithStop
        stopJump program fuel result =
      Simulation.Interaction.pure
        (addFuelToRunResult fuel result) := by
  cases result with
  | exhausted label state =>
      exact False.elim hStopped
  | stopped remaining outcome =>
      rfl

/--
Once every interaction branch has reached a tagged boundary, granting more
fuel changes only the recorded residual budget.
-/
theorem openRunNResultWithStop_add_eq_map_addFuel_of_allStopped
    (stopJump : Label → EVMState → Bool) (program : TypedCfg.Program)
    (fuel extra : Nat) (label : Label) (state : EVMState)
    (hStopped :
      Simulation.Interaction.AllDone RunResultStopped
        (openRunNResultWithStop stopJump
          program fuel label state)) :
    openRunNResultWithStop stopJump
        program (fuel + extra) label state =
      Simulation.Interaction.map
        (addFuelToRunResult extra)
        (openRunNResultWithStop stopJump
          program fuel label state) := by
  rw [openRunNResultWithStop_add]
  calc
    Simulation.Interaction.bind
        (openRunNResultWithStop stopJump
          program fuel label state)
        (continueOpenRunNResultWithStop
          stopJump program extra) =
      Simulation.Interaction.bind
        (openRunNResultWithStop stopJump
          program fuel label state)
        (fun result =>
          Simulation.Interaction.pure
            (addFuelToRunResult extra result)) := by
          apply Simulation.Interaction.AllDone.bind_congr hStopped
          intro result hResult
          exact
            continueOpenRunNResultWithStop_eq_pure_addFuel
              stopJump program extra result hResult
    _ =
      Simulation.Interaction.map
        (addFuelToRunResult extra)
        (openRunNResultWithStop stopJump
          program fuel label state) :=
      rfl

def continueOpenRunN (program : TypedCfg.Program) (fuel : Nat) :
    TypedCfg.Outcome → OpenOutcome
  | .jump next state =>
      openRunN program fuel next state
  | .fallthrough state =>
      pure (.fallthrough state)
  | .returnDispatch state =>
      pure (.returnDispatch state)
  | .halt kind state =>
      pure (.halt kind state)
  | .invalid state =>
      pure (.invalid state)

theorem openRunN_one (program : TypedCfg.Program)
    (label : Label) (state : EVMState) :
    openRunN program 1 label state =
      openStep program label state := by
  rw [show 1 = 0 + 1 by rfl, openRunN_succ]
  change
    Simulation.Interaction.bind
        (openStep program label state)
        (continueOpenRunN program 0) =
      openStep program label state
  have hContinuation :
      continueOpenRunN program 0 =
        Simulation.Interaction.pure := by
    funext outcome
    cases outcome <;> rfl
  rw [hContinuation]
  exact Simulation.Interaction.bind_pure _

/--
Fuel-bounded open execution composes at a residual jump. Non-jump outcomes
remain terminal for the TypedCfg control kernel.
-/
theorem openRunN_add (program : TypedCfg.Program)
    (firstFuel restFuel : Nat) (label : Label) (state : EVMState) :
    openRunN program (firstFuel + restFuel) label state =
      Simulation.Interaction.bind
        (openRunN program firstFuel label state)
        (continueOpenRunN program restFuel) := by
  induction firstFuel generalizing label state with
  | zero =>
      simp [continueOpenRunN]
  | succ firstFuel ih =>
      rw [show
        Nat.succ firstFuel + restFuel =
          (firstFuel + restFuel) + 1 by omega]
      rw [openRunN_succ, openRunN_succ]
      change
        Simulation.Interaction.bind
            (openStep program label state)
            (continueOpenRunN program (firstFuel + restFuel)) =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind
              (openStep program label state)
              (continueOpenRunN program firstFuel))
            (continueOpenRunN program restFuel)
      rw [Simulation.Interaction.bind_assoc]
      apply congrArg (Simulation.Interaction.bind
        (openStep program label state))
      funext outcome
      cases outcome with
      | jump next state' =>
          exact ih next state'
      | fallthrough state'
      | returnDispatch state'
      | halt kind state'
      | invalid state' =>
          rfl

end Program

end InteractionSemantics
end TypedCfg
end EvmCompiler
