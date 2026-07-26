import EvmCompiler.TypedCfg.ReturnAddressTerminal

namespace EvmCompiler
namespace TypedCfg
namespace ReturnAddressPreservation

namespace CompiledBlock

def fuelBudget (cfg : TypedCfg.Program) (block : TypedCfg.Block) : Nat :=
  match ReturnAddressLower.Block.lowerBodyFrom?
      cfg block.body block.input with
  | none => 0
  | some (bodyCode, output) =>
      if output = block.output then
        match ReturnAddressLower.Terminator.lowerAt? output block.term with
        | none => 0
        | some termCode => 1 + bodyCode.length + termCode.length
      else
        0

/-- One physical-return-lowered block execution is a bounded prefix of
ordinary Assembly source execution. -/
theorem openRun_executes_source_bounded
    {cfg : TypedCfg.Program} {block : TypedCfg.Block}
    {program : Assembly.Program} {state : Assembly.EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : Assembly.StepResult}
    (hExec : Simulation.Interaction.Executes
      (openRun cfg block program state) transcript (.ok result)) :
    ∃ usedFuel,
      usedFuel ≤ fuelBudget cfg block ∧
        Simulation.Interaction.Executes
          (Assembly.InteractionSemantics.Source.openRunNResult
            program usedFuel state)
          transcript (.ok result) := by
  unfold openRun at hExec
  cases hBody : ReturnAddressLower.Block.lowerBodyFrom?
      cfg block.body block.input with
  | none =>
      simp only [hBody] at hExec
      cases hExec
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      simp only [hBody] at hExec
      by_cases hOutput : output = block.output
      · rw [if_pos hOutput] at hExec
        subst output
        cases hTerm :
            ReturnAddressLower.Terminator.lowerAt?
              block.output block.term with
        | none =>
            simp only [hTerm] at hExec
            cases hExec
        | some termCode =>
            simp only [hTerm] at hExec
            have hBudget : fuelBudget cfg block =
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
                        have hLabelBody :
                            Simulation.Interaction.Executes
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

/-- For a successfully lowered physical-return block, every compiler-selected
error execution is an exact bounded prefix of ordinary Assembly execution. -/
theorem openRun_error_executes_source_bounded
    {cfg : TypedCfg.Program} {block : TypedCfg.Block}
    {program code : Assembly.Program} {state : Assembly.EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {sourceError : Assembly.EVMException}
    (hLower : ReturnAddressLower.Block.lower? cfg block = some code)
    (hExec : Simulation.Interaction.Executes
      (openRun cfg block program state) transcript (.error sourceError)) :
    ∃ usedFuel,
      usedFuel ≤ fuelBudget cfg block ∧
        Simulation.Interaction.Executes
          (Assembly.InteractionSemantics.Source.openRunNResult
            program usedFuel state)
          transcript (.error sourceError) := by
  unfold ReturnAddressLower.Block.lower? at hLower
  unfold openRun at hExec
  cases hBody : ReturnAddressLower.Block.lowerBodyFrom?
      cfg block.body block.input with
  | none => simp [hBody] at hLower
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      simp only [hBody] at hExec hLower
      by_cases hOutput : output = block.output
      · rw [if_pos hOutput] at hExec
        subst output
        cases hTerm :
            ReturnAddressLower.Terminator.lowerAt?
              block.output block.term with
        | none => simp [hTerm] at hLower
        | some termCode =>
            simp only [hTerm] at hExec hLower
            have hBudget : fuelBudget cfg block =
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
                        have hLabelBody :
                            Simulation.Interaction.Executes
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
  (source.blocks.map (CompiledBlock.fuelBudget source)).sum

theorem block_fuelBudget_le_of_findBlock?
    {source : TypedCfg.Program} {label : Assembly.Label}
    {block : TypedCfg.Block}
    (hFind : source.findBlock? label = some block) :
    CompiledBlock.fuelBudget source block ≤ fuelBudget source := by
  have hMem : block ∈ source.blocks :=
    List.mem_of_find?_eq_some hFind
  unfold fuelBudget
  have aux : ∀ blocks : List TypedCfg.Block,
      block ∈ blocks →
        CompiledBlock.fuelBudget source block ≤
          (blocks.map (CompiledBlock.fuelBudget source)).sum := by
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

theorem openStep_executes_source_bounded
    {source : TypedCfg.Program} {target : Assembly.Program}
    {state : Assembly.EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : Assembly.StepResult}
    (hExec : Simulation.Interaction.Executes
      (openStep source target state) transcript (.ok result)) :
    ∃ usedFuel,
      usedFuel ≤ fuelBudget source ∧
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
      | prim op | push op | pushLabel op | jump op | jumpi op
      | jumpDynamic =>
          cases hExec

theorem openStep_follows_source_bounded
    {source : TypedCfg.Program} {target : Assembly.Program}
    {state : Assembly.EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hLower : ReturnAddressLower.Program.lower? source = some target)
    (hExec : Simulation.Interaction.Executes
      (openStep source target state) transcript outcome) :
    ∃ usedFuel,
      usedFuel ≤ fuelBudget source ∧
        Simulation.Interaction.Follows
          (Assembly.InteractionSemantics.Source.openRunNResult
            target usedFuel state)
          transcript := by
  unfold openStep at hExec
  cases hAt : target.instrAtPc state.pc.toNat with
  | none =>
      simp only [hAt] at hExec
      cases hExec
      exact ⟨0, by simp, .nil _⟩
  | some located =>
      rcases located with ⟨pc, instr⟩
      simp only [hAt] at hExec
      cases instr with
      | label label =>
          cases hFind : source.findBlock? label with
          | none =>
              simp only [hFind] at hExec
              cases hExec
              exact ⟨0, by simp, .nil _⟩
          | some block =>
              simp only [hFind] at hExec
              cases outcome with
              | error error =>
                  rcases
                      ReturnAddressLower.Program.lower?_fragment_of_findBlock?
                        hLower hFind with
                    ⟨fragment⟩
                  obtain ⟨usedFuel, hUsed, hAssembly⟩ :=
                    CompiledBlock.openRun_error_executes_source_bounded
                      (sourceError := error) fragment.lower hExec
                  exact
                    ⟨usedFuel,
                      Nat.le_trans hUsed
                        (block_fuelBudget_le_of_findBlock? hFind),
                      hAssembly.follows⟩
              | ok result =>
                  obtain ⟨usedFuel, hUsed, hAssembly⟩ :=
                    CompiledBlock.openRun_executes_source_bounded hExec
                  exact
                    ⟨usedFuel,
                      Nat.le_trans hUsed
                        (block_fuelBudget_le_of_findBlock? hFind),
                      hAssembly.follows⟩
      | prim op | push op | pushLabel op | jump op | jumpi op
      | jumpDynamic =>
          cases hExec
          exact ⟨0, by simp, .nil _⟩

theorem openRunN_executes_source_bounded
    {source : TypedCfg.Program} {target : Assembly.Program}
    {fuel : Nat} {state : Assembly.EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {result : Assembly.StepResult}
    (hExec : Simulation.Interaction.Executes
      (openRunN source target fuel state) transcript (.ok result)) :
    ∃ usedFuel,
      usedFuel ≤ fuel * fuelBudget source ∧
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
          Except Assembly.EVMException Assembly.StepResult)
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

theorem openRunN_follows_source_bounded
    {source : TypedCfg.Program} {target : Assembly.Program}
    {fuel : Nat} {state : Assembly.EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hLower : ReturnAddressLower.Program.lower? source = some target)
    (hExec : Simulation.Interaction.Executes
      (openRunN source target fuel state) transcript outcome) :
    ∃ usedFuel,
      usedFuel ≤ fuel * fuelBudget source ∧
        Simulation.Interaction.Follows
          (Assembly.InteractionSemantics.Source.openRunNResult
            target usedFuel state)
          transcript := by
  induction fuel generalizing state transcript outcome with
  | zero =>
      rw [openRunN_zero] at hExec
      cases hExec
      exact ⟨0, by simp, .nil _⟩
  | succ fuel ih =>
      rw [openRunN_succ] at hExec
      rcases Simulation.Interaction.Executes.bind_cases hExec with
        hStepError | hStepOk
      · rcases hStepError with ⟨error, hOutcome, hStep⟩
        subst outcome
        obtain ⟨headFuel, hHeadFuel, hHead⟩ :=
          openStep_follows_source_bounded hLower hStep
        refine ⟨headFuel, ?_, hHead⟩
        rw [Nat.add_mul]
        omega
      · rcases hStepOk with
          ⟨stepResult, headTranscript, restTranscript,
            hTranscript, hStep, hRest⟩
        subst transcript
        obtain ⟨headFuel, hHeadFuel, hHead⟩ :=
          openStep_executes_source_bounded hStep
        cases stepResult with
        | halted halt =>
            cases hRest
            refine ⟨headFuel, ?_, by simpa using hHead.follows⟩
            rw [Nat.add_mul]
            omega
        | running mid =>
            obtain ⟨tailFuel, hTailFuel, hTail⟩ := ih hRest
            refine ⟨headFuel + tailFuel, ?_, ?_⟩
            · rw [Nat.add_mul]
              omega
            · rw [
                Assembly.InteractionSemantics.Source.openRunNResult_add]
              exact Simulation.Interaction.Follows.bind_ok hHead hTail

end CompiledProgram

/-- A source-side runtime error reached from a related physical-return entry
is reproduced by ordinary Assembly at a bounded prefix. The concrete target
error need not have the source error's internal constructor: the public
compiler relation observes only structural out-of-fuel direction. -/
theorem program_lower?_openRunN_error_executes_source_bounded
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {label : Assembly.Label} {block : TypedCfg.Block}
    {targetState sourceState : Assembly.EVMState}
    {entryPc fuel : Nat}
    {transcript : Simulation.Interaction.Transcript}
    {sourceError : Assembly.EVMException}
    (hLower : ReturnAddressLower.Program.lower? cfg = some assembly)
    (hAccepted : assembly.accepted = true)
    (hFits : assembly.PCFits)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hTerminalPlain :
      ReturnAddressLower.Program.TerminalArgsPlain cfg)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hFind : cfg.findBlock? label = some block)
    (hLabelPc : assembly.labelPc label = some entryPc)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRel :
      ReturnAddressRelation.RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        block.input targetState.incrPC sourceState)
    (hExec : Simulation.Interaction.Executes
      (TypedCfg.InteractionSemantics.Program.openRunN
        cfg fuel label sourceState)
      transcript (.error sourceError)) :
    ∃ usedFuel targetError,
      usedFuel ≤ fuel * CompiledProgram.fuelBudget cfg ∧
        Simulation.Interaction.Executes
          (Assembly.InteractionSemantics.Source.openRunNResult
            assembly usedFuel targetState)
          transcript (.error targetError) := by
  induction fuel generalizing
      label block targetState sourceState entryPc transcript with
  | zero =>
      rw [TypedCfg.InteractionSemantics.Program.openRunN_zero] at hExec
      cases hExec
  | succ fuel ih =>
      rw [TypedCfg.InteractionSemantics.Program.openRunN_succ] at hExec
      rcases Simulation.Interaction.Executes.bind_cases hExec with
        hStepError | hStepOk
      · rcases hStepError with
          ⟨error, hOutcome, hSourceStep⟩
        cases hOutcome
        have hStepRel :=
          program_lower?_step_openRun_runtimeRel
            hLower hAccepted hFits hTyped hEdgeSafe hTerminalPlain
            hTokensUnique hTargetsUnique
            hFind hLabelPc hPc hRel
        obtain ⟨targetDone, hTargetStep, hSim⟩ :=
          Simulation.Interaction.Rel.executes
            (Simulation.Interaction.Rel.symm hStepRel) hSourceStep
        cases targetDone with
        | error targetError =>
            have hTargetBlock := hTargetStep
            rw [
              compiled_openStep_eq_of_labelPc
                hFits hFind hLabelPc hPc] at hTargetBlock
            rcases
                ReturnAddressLower.Program.lower?_fragment_of_findBlock?
                  hLower hFind with
              ⟨fragment⟩
            obtain ⟨usedFuel, hUsedFuel, hAssemblyExec⟩ :=
              CompiledBlock.openRun_error_executes_source_bounded
                fragment.lower hTargetBlock
            refine ⟨usedFuel, targetError, ?_, hAssemblyExec⟩
            have hBlockFuel :=
              CompiledProgram.block_fuelBudget_le_of_findBlock? hFind
            rw [Nat.add_mul]
            omega
        | ok targetResult =>
            exact False.elim hSim
      · rcases hStepOk with
          ⟨sourceOutcome, headTranscript, restTranscript,
            hTranscript, hSourceStep, hSourceRest⟩
        subst transcript
        cases sourceOutcome with
        | fallthrough final => cases hSourceRest
        | returnDispatch final => cases hSourceRest
        | halt kind final => cases hSourceRest
        | invalid final => cases hSourceRest
        | jump next sourceAfter =>
            have hStepRel :=
              program_lower?_step_openRun_runtimeRel
                hLower hAccepted hFits hTyped hEdgeSafe hTerminalPlain
                hTokensUnique hTargetsUnique
                hFind hLabelPc hPc hRel
            obtain ⟨targetDone, hTargetStep, hSim⟩ :=
              Simulation.Interaction.Rel.executes
                (Simulation.Interaction.Rel.symm hStepRel) hSourceStep
            cases targetDone with
            | error targetError =>
                exact False.elim hSim
            | ok targetResult =>
                cases targetResult with
                | halted halt =>
                    exact False.elim hSim
                | running targetAfter =>
                    have hTargetBlock := hTargetStep
                    rw [
                      compiled_openStep_eq_of_labelPc
                        hFits hFind hLabelPc hPc] at hTargetBlock
                    rcases hSim with
                      ⟨nextBlock, dest, hNextFind, hDest,
                        hTargetPc, hNextRel⟩
                    obtain ⟨headFuel, hHeadFuel, hAssemblyHead⟩ :=
                      CompiledBlock.openRun_executes_source_bounded
                        hTargetBlock
                    obtain
                        ⟨tailFuel, targetError,
                          hTailFuel, hAssemblyTail⟩ :=
                      ih hNextFind hDest hTargetPc hNextRel hSourceRest
                    refine
                      ⟨headFuel + tailFuel, targetError, ?_, ?_⟩
                    · have hBlockFuel :=
                        CompiledProgram.block_fuelBudget_le_of_findBlock?
                          hFind
                      rw [Nat.add_mul]
                      omega
                    · rw [
                        Assembly.InteractionSemantics.Source.openRunNResult_add]
                      exact Simulation.Interaction.Executes.bind_ok
                        hAssemblyHead hAssemblyTail

/-- Every concrete physical-return CFG prefix is an Assembly prefix at the
physical lowering's fixed compiler budget. -/
theorem program_lower?_openRunNPrefix_assembly_follows_of_executes
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {label : Assembly.Label} {block : TypedCfg.Block}
    {targetState sourceState : Assembly.EVMState}
    {entryPc fuel : Nat}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Except Assembly.EVMException TypedCfg.Outcome}
    (hLower : ReturnAddressLower.Program.lower? cfg = some assembly)
    (hAccepted : assembly.accepted = true)
    (hFits : assembly.PCFits)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hTerminalPlain :
      ReturnAddressLower.Program.TerminalArgsPlain cfg)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hFind : cfg.findBlock? label = some block)
    (hLabelPc : assembly.labelPc label = some entryPc)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRel :
      ReturnAddressRelation.RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        block.input targetState.incrPC sourceState)
    (hSourceExec : Simulation.Interaction.Executes
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix
        cfg fuel label sourceState)
      transcript sourceDone) :
    Simulation.Interaction.Follows
      (Assembly.InteractionSemantics.Source.openRunNResult
        assembly
        (fuel * CompiledProgram.fuelBudget cfg)
        targetState)
      transcript := by
  have hBlocks :=
    program_lower?_openRunN_runtimeRel fuel
      hLower hAccepted hFits hTyped hEdgeSafe hTerminalPlain
      hTokensUnique hTargetsUnique hFind hLabelPc hPc hRel
  have hBlocksSource :=
    Simulation.Interaction.Rel.symm hBlocks
  unfold TypedCfg.InteractionSemantics.Program.openRunNPrefix
    at hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    hRunError | hRunOk
  · rcases hRunError with ⟨sourceError, hDone, hRun⟩
    subst sourceDone
    obtain ⟨targetDone, hTargetExec, _hResultRel⟩ :=
      Simulation.Interaction.Rel.executes hBlocksSource hRun
    obtain ⟨usedFuel, hUsedFuel, hAssemblyFollow⟩ :=
      CompiledProgram.openRunN_follows_source_bounded
        hLower hTargetExec
    exact
      Assembly.InteractionSemantics.Source.openRunNResult_follows_of_le_follows
        hUsedFuel hAssemblyFollow
  · rcases hRunOk with
      ⟨sourceOutcome, headTranscript, restTranscript,
        hTranscript, hRun, hFinish⟩
    subst transcript
    obtain ⟨targetDone, hTargetExec, _hResultRel⟩ :=
      Simulation.Interaction.Rel.executes hBlocksSource hRun
    obtain ⟨usedFuel, hUsedFuel, hAssemblyFollow⟩ :=
      CompiledProgram.openRunN_follows_source_bounded
        hLower hTargetExec
    cases sourceOutcome <;> cases hFinish <;>
      simpa using
        (Assembly.InteractionSemantics.Source.openRunNResult_follows_of_le_follows
          hUsedFuel hAssemblyFollow)

/-- Prefix-only lifting from a physical-return CFG to ordinary Assembly. -/
theorem program_lower?_openRunNPrefix_assembly_follows
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {label : Assembly.Label} {block : TypedCfg.Block}
    {targetState sourceState : Assembly.EVMState}
    {entryPc fuel : Nat}
    {transcript : Simulation.Interaction.Transcript}
    (hLower : ReturnAddressLower.Program.lower? cfg = some assembly)
    (hAccepted : assembly.accepted = true)
    (hFits : assembly.PCFits)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hTerminalPlain :
      ReturnAddressLower.Program.TerminalArgsPlain cfg)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hFind : cfg.findBlock? label = some block)
    (hLabelPc : assembly.labelPc label = some entryPc)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRel :
      ReturnAddressRelation.RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        block.input targetState.incrPC sourceState)
    (hFollow : Simulation.Interaction.Follows
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix
        cfg fuel label sourceState)
      transcript) :
    Simulation.Interaction.Follows
      (Assembly.InteractionSemantics.Source.openRunNResult
        assembly
        (fuel * CompiledProgram.fuelBudget cfg)
        targetState)
      transcript := by
  obtain ⟨suffix, sourceDone, hExec⟩ :=
    hFollow.exists_executes_extension
  have hAssembly :=
    program_lower?_openRunNPrefix_assembly_follows_of_executes
      hLower hAccepted hFits hTyped hEdgeSafe
      hTerminalPlain
      hTokensUnique hTargetsUnique hFind hLabelPc hPc hRel hExec
  exact Simulation.Interaction.Follows.prefix_of_append
    transcript suffix hAssembly

/-- Branch-local physical-return TypedCfg-to-Assembly prefix preservation.
Completed source errors and safe halts are padded to exact target outcomes;
residual control is the canonical `OutOfFuel` truncation arm. -/
theorem program_lower?_openRunNPrefix_assembly_branch
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {label : Assembly.Label} {block : TypedCfg.Block}
    {targetState sourceState : Assembly.EVMState}
    {entryPc fuel : Nat}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Except Assembly.EVMException TypedCfg.Outcome}
    (hLower : ReturnAddressLower.Program.lower? cfg = some assembly)
    (hAccepted : assembly.accepted = true)
    (hFits : assembly.PCFits)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hTerminalPlain :
      ReturnAddressLower.Program.TerminalArgsPlain cfg)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hFind : cfg.findBlock? label = some block)
    (hLabelPc : assembly.labelPc label = some entryPc)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRel :
      ReturnAddressRelation.RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        block.input targetState.incrPC sourceState)
    (hSourceExec : Simulation.Interaction.Executes
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix
        cfg fuel label sourceState)
      transcript sourceDone)
    (hSafeDone :
      TypedCfg.InteractionSemantics.Program.PrefixAssemblySafe sourceDone) :
    (∃ error,
        sourceDone = .error error ∧
          TypedCfg.InteractionSemantics.Program.PrefixTruncated error ∧
            Simulation.Interaction.Follows
              (Assembly.InteractionSemantics.Source.openRunNResult
                assembly
                (fuel * CompiledProgram.fuelBudget cfg)
                targetState)
              transcript) ∨
      ∃ targetDone,
        Simulation.Interaction.Executes
            (Assembly.InteractionSemantics.Source.openRunNResult
              assembly
              (fuel * CompiledProgram.fuelBudget cfg)
              targetState)
            transcript targetDone ∧
          ProgramRunResultRel cfg assembly assembly.labelPc
            (ReturnAddressLower.Program.returnSites cfg)
            targetDone sourceDone := by
  have hBlocks :=
    program_lower?_openRunN_runtimeRel fuel
      hLower hAccepted hFits hTyped hEdgeSafe hTerminalPlain
      hTokensUnique hTargetsUnique hFind hLabelPc hPc hRel
  have hBlocksSource :=
    Simulation.Interaction.Rel.symm hBlocks
  unfold TypedCfg.InteractionSemantics.Program.openRunNPrefix
    at hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    hRunError | hRunOk
  · rcases hRunError with ⟨sourceError, hDone, hRun⟩
    subst sourceDone
    obtain ⟨usedFuel, targetError, hUsedFuel, hAssemblyExec⟩ :=
      program_lower?_openRunN_error_executes_source_bounded
        hLower hAccepted hFits hTyped hEdgeSafe hTerminalPlain
        hTokensUnique hTargetsUnique hFind hLabelPc hPc hRel hRun
    let extra :=
      fuel * CompiledProgram.fuelBudget cfg - usedFuel
    have hFuel :
        usedFuel + extra =
          fuel * CompiledProgram.fuelBudget cfg :=
      Nat.add_sub_of_le hUsedFuel
    have hPadded :=
      Assembly.InteractionSemantics.Source.openRunNResult_error_add_executes
        (extra := extra) hAssemblyExec
    rw [hFuel] at hPadded
    exact .inr ⟨.error targetError, hPadded, by trivial⟩
  · rcases hRunOk with
      ⟨sourceOutcome, headTranscript, restTranscript,
        hTranscript, hRun, hFinish⟩
    subst transcript
    cases sourceOutcome with
    | halt kind sourceFinal =>
        cases hFinish
        obtain ⟨targetDone, hTargetExec, hResultRel⟩ :=
          Simulation.Interaction.Rel.executes hBlocksSource hRun
        have hResultRel' :
            ∃ output,
              kind.argCount ≤ output.length ∧
                ReturnAddressRelation.PlainSlots
                    (output.slots.take kind.argCount) ∧
                  LoweredBlockResultRel assembly assembly.labelPc
                    (ReturnAddressLower.Program.returnSites cfg)
                    output targetDone
                    (.ok (.halt kind sourceFinal)) := by
          cases targetDone with
          | error targetError =>
              exact hResultRel
          | ok targetResult =>
              cases targetResult with
              | running targetRunning =>
                  exact hResultRel
              | halted targetHalt =>
                  exact hResultRel
        rcases hResultRel' with
          ⟨output, hBound, hPlain, hBlockRel⟩
        obtain
            ⟨targetFinal, sourceAfter,
              hTargetDone, _hSourceStep, _hShared⟩ :=
          LoweredBlockResultRel.targetHalt_shared
            hBound hPlain hBlockRel hSafeDone
        subst targetDone
        obtain ⟨usedFuel, hUsedFuel, hAssemblyExec⟩ :=
          CompiledProgram.openRunN_executes_source_bounded
            hTargetExec
        let extra :=
          fuel * CompiledProgram.fuelBudget cfg - usedFuel
        have hFuel :
            usedFuel + extra =
              fuel * CompiledProgram.fuelBudget cfg :=
          Nat.add_sub_of_le hUsedFuel
        have hPadded :=
          Assembly.InteractionSemantics.Source.openRunNResult_halted_add_executes
            (extra := extra) hAssemblyExec
        rw [hFuel] at hPadded
        exact .inr
          ⟨.ok (.halted
            { kind := kind,
                state := targetFinal,
                output := kind.output targetFinal }),
            by simpa using hPadded,
            ⟨output, hBound, hPlain, hBlockRel⟩⟩
    | jump next sourceFinal
    | fallthrough sourceFinal
    | returnDispatch sourceFinal
    | invalid sourceFinal =>
        cases hFinish
        have hAssemblyFollow :=
          program_lower?_openRunNPrefix_assembly_follows_of_executes
            hLower hAccepted hFits hTyped hEdgeSafe hTerminalPlain
            hTokensUnique hTargetsUnique hFind hLabelPc hPc hRel
            (by
              unfold
                TypedCfg.InteractionSemantics.Program.openRunNPrefix
              exact
                Simulation.Interaction.Executes.bind_ok
                  hRun (Simulation.Interaction.Executes.done _))
        exact .inl
          ⟨.OutOfFuel, rfl, by trivial, hAssemblyFollow⟩

/-- Physical-return TypedCfg-to-Assembly preservation for every finite
interaction prefix. -/
theorem program_lower?_openRunNPrefix_assembly_forward
    {cfg : TypedCfg.Program} {assembly : Assembly.Program}
    {label : Assembly.Label} {block : TypedCfg.Block}
    {targetState sourceState : Assembly.EVMState}
    {entryPc : Nat} (fuel : Nat)
    (hLower : ReturnAddressLower.Program.lower? cfg = some assembly)
    (hAccepted : assembly.accepted = true)
    (hFits : assembly.PCFits)
    (hTyped : cfg.WellTyped)
    (hEdgeSafe : ReturnAddressLower.Program.EdgeClassSafe cfg)
    (hTerminalPlain :
      ReturnAddressLower.Program.TerminalArgsPlain cfg)
    (hTokensUnique :
      ReturnAddressLower.Program.tokensUnique? cfg = true)
    (hTargetsUnique :
      ReturnAddressLower.Program.targetsUnique? cfg = true)
    (hFind : cfg.findBlock? label = some block)
    (hLabelPc : assembly.labelPc label = some entryPc)
    (hPc : targetState.pc = EvmYul.UInt256.ofNat entryPc)
    (hRel :
      ReturnAddressRelation.RuntimeRel assembly.labelPc
        (ReturnAddressLower.Program.returnSites cfg)
        block.input targetState.incrPC sourceState)
    (hSafe : Simulation.Interaction.AllDone
      TypedCfg.InteractionSemantics.Program.PrefixAssemblySafe
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix
        cfg fuel label sourceState)) :
    Simulation.Interaction.ForwardRel
      TypedCfg.InteractionSemantics.Program.PrefixTruncated
      (fun sourceDone targetDone =>
        ProgramRunResultRel cfg assembly assembly.labelPc
          (ReturnAddressLower.Program.returnSites cfg)
          targetDone sourceDone)
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix
        cfg fuel label sourceState)
      (Assembly.InteractionSemantics.Source.openRunNResult
        assembly
        (fuel * CompiledProgram.fuelBudget cfg)
        targetState) := by
  apply Simulation.Interaction.ForwardRel.of_executes_or_follows
  intro transcript sourceDone hSourceExec
  exact
    program_lower?_openRunNPrefix_assembly_branch
      hLower hAccepted hFits hTyped hEdgeSafe hTerminalPlain
      hTokensUnique hTargetsUnique hFind hLabelPc hPc hRel
      hSourceExec
      (Simulation.Interaction.AllDone.property_of_executes
        hSafe hSourceExec)

end ReturnAddressPreservation
end TypedCfg
end EvmCompiler
