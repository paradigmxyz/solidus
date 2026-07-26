import EvmCompiler.TypedCfg.LateReturnPreservation

namespace EvmCompiler
namespace TypedCfg
namespace LateReturnCompactPreservation

open Assembly

namespace Compact

abbrev Artifact := ReturnAddressProbe.Compact.Artifact
abbrev SourceBlock := Assembly.Compact.SourceBlock

def resolvedStraightInstr?
    (pinnedPushPcs : List Nat) (branchWidth sourcePc : Nat)
    (labels : Assembly.Compact.LabelTable) :
    Assembly.Instr → Option Assembly.Compact.Instr
  | .label _ =>
      some .jumpdest
  | .prim op =>
      some (.prim op)
  | .push value => do
      let width ←
        Assembly.Compact.pushWidthAt?
          pinnedPushPcs sourcePc value
      some (Assembly.Compact.pushInstrOfWidth width value)
  | .pushLabel target => do
      let dest ← Assembly.Compact.lookupLabel? labels target
      if Assembly.Compact.fitsWidth? branchWidth dest then
        some
          (.push branchWidth (EvmYul.UInt256.ofNat dest))
      else
        none
  | .jump _ | .jumpi _ | .jumpDynamic =>
      none

def resolvedStraightFrom?
    (pinnedPushPcs : List Nat) (branchWidth : Nat)
    (labels : Assembly.Compact.LabelTable) :
    Assembly.Program → Nat → Option (List Assembly.Compact.Instr)
  | [], _sourcePc =>
      some []
  | instr :: rest, sourcePc => do
      let compactInstr ←
        resolvedStraightInstr?
          pinnedPushPcs branchWidth sourcePc labels instr
      let compactRest ←
        resolvedStraightFrom? pinnedPushPcs branchWidth labels
          rest (sourcePc + instr.byteSize)
      some (compactInstr :: compactRest)

def resolvedTargetInstr?
    (labels : Assembly.Compact.LabelTable) :
    Assembly.Instr → Option Assembly.TargetInstr
  | .label _ =>
      some .jumpdest
  | .prim op =>
      some (.prim op)
  | .push value =>
      some (.push32 value)
  | .pushLabel target => do
      let dest ← Assembly.Compact.lookupLabel? labels target
      some (.push32 (EvmYul.UInt256.ofNat dest))
  | .jump _ | .jumpi _ | .jumpDynamic =>
      none

def resolvedTargetFrom?
    (labels : Assembly.Compact.LabelTable) :
    Assembly.Program → Option (List Assembly.TargetInstr)
  | [] =>
      some []
  | instr :: rest => do
      let targetInstr ← resolvedTargetInstr? labels instr
      let targetRest ← resolvedTargetFrom? labels rest
      some (targetInstr :: targetRest)

theorem resolvedStraightInstr?_toLogical
    {pinnedPushPcs : List Nat} {branchWidth sourcePc : Nat}
    {labels : Assembly.Compact.LabelTable}
    {sourceInstr : Assembly.Instr}
    {compactInstr : Assembly.Compact.Instr}
    (hResolved :
      resolvedStraightInstr?
          pinnedPushPcs branchWidth sourcePc labels sourceInstr =
        some compactInstr) :
    resolvedTargetInstr? labels sourceInstr =
      some compactInstr.toLogical := by
  cases sourceInstr with
  | label name =>
      simp [resolvedStraightInstr?, resolvedTargetInstr?] at hResolved ⊢
      subst compactInstr
      rfl
  | prim op =>
      simp [resolvedStraightInstr?, resolvedTargetInstr?] at hResolved ⊢
      subst compactInstr
      rfl
  | push value =>
      cases hWidth :
          Assembly.Compact.pushWidthAt?
            pinnedPushPcs sourcePc value with
      | none =>
          simp [resolvedStraightInstr?, hWidth] at hResolved
      | some width =>
          simp [resolvedStraightInstr?, hWidth] at hResolved
          subst compactInstr
          unfold Assembly.Compact.pushInstrOfWidth
          by_cases hZero : width = 0
          · subst width
            have hValue :
                value = EvmYul.UInt256.ofNat 0 :=
              Assembly.Compact.pushWidthAt?_zero_value hWidth
            simp [resolvedTargetInstr?, hValue,
              Assembly.Compact.Instr.toLogical]
          · simp [hZero, resolvedTargetInstr?,
              Assembly.Compact.Instr.toLogical]
  | pushLabel target =>
      cases hDest :
          Assembly.Compact.lookupLabel? labels target with
      | none =>
          simp [resolvedStraightInstr?, hDest] at hResolved
      | some dest =>
          by_cases hFits :
              Assembly.Compact.fitsWidth? branchWidth dest = true
          · simp [resolvedStraightInstr?, hDest, hFits] at hResolved
            subst compactInstr
            simp [resolvedTargetInstr?, hDest,
              Assembly.Compact.Instr.toLogical]
          · have hFitsFalse :
                Assembly.Compact.fitsWidth? branchWidth dest =
                  false :=
              Bool.eq_false_of_not_eq_true hFits
            simp [resolvedStraightInstr?, hDest, hFitsFalse]
              at hResolved
  | jump target | jumpi target | jumpDynamic =>
      simp [resolvedStraightInstr?] at hResolved

theorem resolvedStraightFrom?_toLogical
    {pinnedPushPcs : List Nat} {branchWidth sourcePc : Nat}
    {labels : Assembly.Compact.LabelTable}
    {source : Assembly.Program}
    {compactCode : List Assembly.Compact.Instr}
    (hResolved :
      resolvedStraightFrom?
          pinnedPushPcs branchWidth labels source sourcePc =
        some compactCode) :
    resolvedTargetFrom? labels source =
      some (compactCode.map Assembly.Compact.Instr.toLogical) := by
  induction source generalizing sourcePc compactCode with
  | nil =>
      simp [resolvedStraightFrom?, resolvedTargetFrom?] at hResolved ⊢
      subst compactCode
      rfl
  | cons sourceInstr rest ih =>
      simp only [resolvedStraightFrom?] at hResolved
      cases hHead :
          resolvedStraightInstr?
            pinnedPushPcs branchWidth sourcePc labels sourceInstr with
      | none =>
          simp [hHead] at hResolved
      | some compactInstr =>
          simp [hHead] at hResolved
          cases hTail :
              resolvedStraightFrom?
                pinnedPushPcs branchWidth labels rest
                (sourcePc + sourceInstr.byteSize) with
          | none =>
              simp [hTail] at hResolved
          | some compactRest =>
              simp [hTail] at hResolved
              subst compactCode
              have hTargetHead :=
                resolvedStraightInstr?_toLogical hHead
              have hTargetTail :=
                ih hTail
              simp [resolvedTargetFrom?, hTargetHead, hTargetTail]

theorem resolvedStraightInstr?_sequential
    {pinnedPushPcs : List Nat} {branchWidth sourcePc : Nat}
    {labels : Assembly.Compact.LabelTable}
    {sourceInstr : Assembly.Instr}
    {compactInstr : Assembly.Compact.Instr}
    (hResolved :
      resolvedStraightInstr?
          pinnedPushPcs branchWidth sourcePc labels sourceInstr =
        some compactInstr) :
    compactInstr.Sequential := by
  cases sourceInstr with
  | label name | prim name =>
      simp [resolvedStraightInstr?] at hResolved
      subst compactInstr
      trivial
  | push value =>
      cases hWidth :
          Assembly.Compact.pushWidthAt?
            pinnedPushPcs sourcePc value with
      | none =>
          simp [resolvedStraightInstr?, hWidth] at hResolved
      | some width =>
          simp [resolvedStraightInstr?, hWidth] at hResolved
          subst compactInstr
          unfold Assembly.Compact.pushInstrOfWidth
          split <;> trivial
  | pushLabel target =>
      cases hDest :
          Assembly.Compact.lookupLabel? labels target with
      | none =>
          simp [resolvedStraightInstr?, hDest] at hResolved
      | some dest =>
          by_cases hFits :
              Assembly.Compact.fitsWidth? branchWidth dest = true
          · simp [resolvedStraightInstr?, hDest, hFits] at hResolved
            subst compactInstr
            trivial
          · have hFitsFalse :
                Assembly.Compact.fitsWidth? branchWidth dest = false :=
              Bool.eq_false_of_not_eq_true hFits
            simp [resolvedStraightInstr?, hDest, hFitsFalse]
              at hResolved
  | jump target | jumpi target | jumpDynamic =>
      simp [resolvedStraightInstr?] at hResolved

theorem resolvedStraightFrom?_sequential
    {pinnedPushPcs : List Nat} {branchWidth sourcePc : Nat}
    {labels : Assembly.Compact.LabelTable}
    {source : Assembly.Program}
    {compactCode : List Assembly.Compact.Instr}
    (hResolved :
      resolvedStraightFrom?
          pinnedPushPcs branchWidth labels source sourcePc =
        some compactCode) :
    ∀ instr ∈ compactCode, instr.Sequential := by
  induction source generalizing sourcePc compactCode with
  | nil =>
      simp [resolvedStraightFrom?] at hResolved
      subst compactCode
      simp
  | cons sourceInstr rest ih =>
      simp only [resolvedStraightFrom?] at hResolved
      cases hHead :
          resolvedStraightInstr?
            pinnedPushPcs branchWidth sourcePc labels sourceInstr with
      | none =>
          simp [hHead] at hResolved
      | some compactInstr =>
          simp [hHead] at hResolved
          cases hTail :
              resolvedStraightFrom?
                pinnedPushPcs branchWidth labels rest
                (sourcePc + sourceInstr.byteSize) with
          | none =>
              simp [hTail] at hResolved
          | some compactRest =>
              simp [hTail] at hResolved
              subst compactCode
              intro instr hMem
              simp at hMem
              cases hMem with
              | inl hEq =>
                  subst instr
                  exact resolvedStraightInstr?_sequential hHead
              | inr hRest =>
                  exact ih hTail instr hRest

theorem resolvedTargetFrom?_append
    (labels : Assembly.Compact.LabelTable)
    (left right : Assembly.Program) :
    resolvedTargetFrom? labels (left ++ right) =
      (do
        let targetLeft ← resolvedTargetFrom? labels left
        let targetRight ← resolvedTargetFrom? labels right
        some (targetLeft ++ targetRight)) := by
  induction left with
  | nil =>
      simp [resolvedTargetFrom?]
  | cons instr rest ih =>
      simp only [List.cons_append, resolvedTargetFrom?]
      rw [ih]
      cases resolvedTargetInstr? labels instr <;>
        cases resolvedTargetFrom? labels rest <;>
          cases resolvedTargetFrom? labels right <;> rfl

inductive StraightDecoding (bytes : ByteArray) :
    Nat → List Assembly.Compact.Instr → Prop
  | nil (pc : Nat) :
      StraightDecoding bytes pc []
  | cons (pc : Nat) (instr : Assembly.Compact.Instr)
      (rest : List Assembly.Compact.Instr)
      (hValid : instr.Valid)
      (hSequential : instr.Sequential)
      (hIndependent : instr.PCIndependent)
      (hDecode : Assembly.Compact.decodeAt bytes pc instr)
      (hRest :
        StraightDecoding bytes (pc + instr.byteSize) rest) :
      StraightDecoding bytes pc (instr :: rest)

def straightEndPc : Nat → List Assembly.Compact.Instr → Nat
  | pc, [] =>
      pc
  | pc, instr :: rest =>
      straightEndPc (pc + instr.byteSize) rest

theorem straight_openRunNResult_runningAt_end
    {bytes : ByteArray} {pc : Nat}
    {compactCode : List Assembly.Compact.Instr}
    {state : EVMState}
    (hDecoding : StraightDecoding bytes pc compactCode)
    (hPc : state.pc = EvmYul.UInt256.ofNat pc) :
    Simulation.Interaction.AllDone
      (Assembly.Compact.RunningAt
        (EvmYul.UInt256.ofNat
          (straightEndPc pc compactCode)))
      (Assembly.Compact.InteractionSemantics.openRunNResult
        bytes compactCode.length state) := by
  induction hDecoding generalizing state with
  | nil pc =>
      exact .done hPc
  | cons pc instr rest hValid hSequential hIndependent
      hDecode hRest ih =>
      rw [show (instr :: rest).length = 1 + rest.length by
            simp [Nat.add_comm],
        Assembly.Compact.InteractionSemantics.openRunNResult_add]
      apply Simulation.Interaction.AllDone.bind
        (Assembly.Compact.InteractionSemantics.openRunNResult_one_runningAt_next
          hValid hSequential hDecode hPc)
      · intro error hError
        trivial
      · intro result hAt
        cases result with
        | running mid =>
            exact ih hAt
        | halted halt =>
            exact .done trivial

theorem emitSourceBlock?_eq_singleton_of_resolvedStraightInstr?
    {pinnedPushPcs : List Nat} {branchWidth sourcePc compactPc : Nat}
    {labels : Assembly.Compact.LabelTable}
    {sourceInstr : Assembly.Instr}
    {compactInstr : Assembly.Compact.Instr}
    {code : List Assembly.Compact.Located}
    (hResolved :
      resolvedStraightInstr? pinnedPushPcs branchWidth sourcePc
          labels sourceInstr =
        some compactInstr)
    (hCode :
      ReturnAddressProbe.Compact.emitSourceBlock?
          pinnedPushPcs branchWidth sourcePc compactPc labels
          sourceInstr =
        some code) :
    code = [{ pc := compactPc, instr := compactInstr }] := by
  cases sourceInstr with
  | label name =>
      simp [resolvedStraightInstr?,
        ReturnAddressProbe.Compact.emitSourceBlock?,
        ReturnAddressProbe.Compact.emitInstrRev?] at hResolved hCode
      subst compactInstr
      simpa using hCode.symm
  | prim op =>
      simp [resolvedStraightInstr?,
        ReturnAddressProbe.Compact.emitSourceBlock?,
        ReturnAddressProbe.Compact.emitInstrRev?] at hResolved hCode
      subst compactInstr
      simpa using hCode.symm
  | push value =>
      cases hWidth :
          Assembly.Compact.pushWidthAt?
            pinnedPushPcs sourcePc value with
      | none =>
          simp [resolvedStraightInstr?, hWidth] at hResolved
      | some width =>
          simp [resolvedStraightInstr?, hWidth,
            ReturnAddressProbe.Compact.emitSourceBlock?,
            ReturnAddressProbe.Compact.emitInstrRev?]
              at hResolved hCode
          subst compactInstr
          simpa using hCode.symm
  | pushLabel target =>
      cases hDest :
          Assembly.Compact.lookupLabel? labels target with
      | none =>
          simp [resolvedStraightInstr?, hDest] at hResolved
      | some dest =>
          by_cases hFits :
              Assembly.Compact.fitsWidth? branchWidth dest = true
          · simp [resolvedStraightInstr?, hDest, hFits,
              ReturnAddressProbe.Compact.emitSourceBlock?,
              ReturnAddressProbe.Compact.emitInstrRev?]
                at hResolved hCode
            subst compactInstr
            simpa using hCode.symm
          · have hFitsFalse :
                Assembly.Compact.fitsWidth? branchWidth dest =
                  false :=
              Bool.eq_false_of_not_eq_true hFits
            simp [resolvedStraightInstr?, hDest, hFitsFalse]
              at hResolved
  | jump target | jumpi target | jumpDynamic =>
      simp [resolvedStraightInstr?] at hResolved

theorem ReturnAddressProbe.Compact.BlocksValidFrom.resolved_prefix_decoding
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {labels : Assembly.Compact.LabelTable}
    {sourcePc compactPc : Nat} {post : Assembly.Program}
    {blocks globalBlocks : List SourceBlock}
    {globalProgram : Assembly.Compact.Program}
    {bytes : ByteArray} {compactCode : List Assembly.Compact.Instr}
    (sourcePrefix : Assembly.Program)
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        pinnedPushPcs branchWidth labels
        (sourcePrefix ++ post) sourcePc compactPc blocks)
    (hResolved :
      resolvedStraightFrom? pinnedPushPcs branchWidth labels
          sourcePrefix sourcePc =
        some compactCode)
    (hSubset :
      ∀ block ∈ blocks, block ∈ globalBlocks)
    (hBlockCode :
      Assembly.Compact.blocksCode globalBlocks =
        globalProgram.code)
    (hProgramValid : globalProgram.Valid)
    (hProgramIndependent : globalProgram.PCIndependent)
    (hDecoding :
      Assembly.Compact.DecodingCorrect globalProgram bytes)
    (hSequential :
      ∀ instr ∈ compactCode, instr.Sequential) :
    StraightDecoding bytes compactPc compactCode := by
  induction sourcePrefix generalizing
      sourcePc compactPc blocks compactCode with
  | nil =>
      simp [resolvedStraightFrom?] at hResolved
      subst compactCode
      exact .nil compactPc
  | cons sourceInstr rest ih =>
      cases hValid with
      | @cons _ _ _ _ compactSize blockCode restBlocks
          hSize hCode hRest =>
          simp only [resolvedStraightFrom?] at hResolved
          cases hHead :
              resolvedStraightInstr? pinnedPushPcs branchWidth
                sourcePc labels sourceInstr with
          | none =>
              simp [hHead] at hResolved
          | some compactInstr =>
              simp [hHead] at hResolved
              cases hTail :
                  resolvedStraightFrom? pinnedPushPcs branchWidth labels
                    rest (sourcePc + sourceInstr.byteSize) with
              | none =>
                  simp [hTail] at hResolved
              | some compactRest =>
                  simp [hTail] at hResolved
                  subst compactCode
                  have hCodeEq :=
                    emitSourceBlock?_eq_singleton_of_resolvedStraightInstr?
                      hHead hCode
                  have hCodeLength :=
                    ReturnAddressProbe.Compact.emitSourceBlock?_codeByteLength
                      hSize hCode
                  rw [hCodeEq] at hCodeLength
                  have hSizeEq :
                      compactSize = compactInstr.byteSize := by
                    simpa [Assembly.Compact.Program.codeByteLength]
                      using hCodeLength.symm
                  let block : SourceBlock :=
                    { sourcePc := sourcePc
                      compactPc := compactPc
                      sourceInstr := sourceInstr
                      code := blockCode }
                  let located : Assembly.Compact.Located :=
                    { pc := compactPc, instr := compactInstr }
                  have hBlockMem : block ∈ globalBlocks :=
                    hSubset block (by simp [block])
                  have hLocatedInBlock :
                      located ∈ block.code := by
                    simp [block, located, hCodeEq]
                  have hLocatedMem :
                      located ∈ globalProgram.code := by
                    rw [← hBlockCode]
                    exact
                      List.mem_flatMap.mpr
                        ⟨block, hBlockMem, hLocatedInBlock⟩
                  have hRestSubset :
                      ∀ candidate ∈ restBlocks,
                        candidate ∈ globalBlocks := by
                    intro candidate hCandidate
                    exact
                      hSubset candidate
                        (by simp [hCandidate])
                  have hRestDecoding :=
                    ih hRest hTail hRestSubset
                      (by
                        intro instr hMem
                        exact
                          hSequential instr (by simp [hMem]))
                  rw [hSizeEq] at hRestDecoding
                  exact
                    .cons compactPc compactInstr compactRest
                      ((List.forall_iff_forall_mem.mp hProgramValid)
                        located hLocatedMem)
                      (hSequential compactInstr (by simp))
                      ((List.forall_iff_forall_mem.mp
                        hProgramIndependent) located hLocatedMem)
                      (hDecoding.decodes located hLocatedMem)
                      hRestDecoding

theorem ReturnAddressProbe.Compact.BlocksValidFrom.resolved_prefix_suffix
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {labels : Assembly.Compact.LabelTable}
    {sourcePc compactPc : Nat} {post : Assembly.Program}
    {blocks : List SourceBlock}
    {compactCode : List Assembly.Compact.Instr}
    (sourcePrefix : Assembly.Program)
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        pinnedPushPcs branchWidth labels
        (sourcePrefix ++ post) sourcePc compactPc blocks)
    (hResolved :
      resolvedStraightFrom? pinnedPushPcs branchWidth labels
          sourcePrefix sourcePc =
        some compactCode) :
    ∃ restBlocks,
      ReturnAddressProbe.Compact.BlocksValidFrom
          pinnedPushPcs branchWidth labels post
          (sourcePc + sourcePrefix.byteLength)
          (straightEndPc compactPc compactCode)
          restBlocks ∧
        ∀ block ∈ restBlocks, block ∈ blocks := by
  induction sourcePrefix generalizing
      sourcePc compactPc blocks compactCode with
  | nil =>
      simp [resolvedStraightFrom?] at hResolved
      subst compactCode
      exact ⟨blocks, by simpa [straightEndPc] using hValid,
        fun block hBlock => hBlock⟩
  | cons sourceInstr rest ih =>
      cases hValid with
      | @cons _ _ _ _ compactSize blockCode restBlocks
          hSize hCode hRest =>
          simp only [resolvedStraightFrom?] at hResolved
          cases hHead :
              resolvedStraightInstr? pinnedPushPcs branchWidth
                sourcePc labels sourceInstr with
          | none =>
              simp [hHead] at hResolved
          | some compactInstr =>
              simp [hHead] at hResolved
              cases hTail :
                  resolvedStraightFrom? pinnedPushPcs branchWidth labels
                    rest (sourcePc + sourceInstr.byteSize) with
              | none =>
                  simp [hTail] at hResolved
              | some compactRest =>
                  simp [hTail] at hResolved
                  subst compactCode
                  have hCodeEq :=
                    emitSourceBlock?_eq_singleton_of_resolvedStraightInstr?
                      hHead hCode
                  have hCodeLength :=
                    ReturnAddressProbe.Compact.emitSourceBlock?_codeByteLength
                      hSize hCode
                  rw [hCodeEq] at hCodeLength
                  have hSizeEq :
                      compactSize = compactInstr.byteSize := by
                    simpa [Assembly.Compact.Program.codeByteLength]
                      using hCodeLength.symm
                  obtain ⟨suffixBlocks, hSuffix, hSubset⟩ :=
                    ih hRest hTail
                  refine ⟨suffixBlocks, ?_, ?_⟩
                  · simpa [Assembly.Program.byteLength_cons,
                      straightEndPc, hSizeEq, Nat.add_assoc]
                      using hSuffix
                  · intro block hBlock
                    exact by simp [hSubset block hBlock]

theorem ReturnAddressProbe.Compact.BlocksValidFrom.drop_prefix
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {labels : Assembly.Compact.LabelTable}
    {sourcePc compactPc : Nat}
    {suffix : Assembly.Program}
    {blocks : List SourceBlock}
    (sourcePrefix : Assembly.Program)
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        pinnedPushPcs branchWidth labels
        (sourcePrefix ++ suffix) sourcePc compactPc blocks) :
    ∃ suffixCompactPc suffixBlocks,
      ReturnAddressProbe.Compact.BlocksValidFrom
          pinnedPushPcs branchWidth labels suffix
          (sourcePc + sourcePrefix.byteLength)
          suffixCompactPc suffixBlocks ∧
        ∀ block ∈ suffixBlocks, block ∈ blocks := by
  induction sourcePrefix generalizing
      sourcePc compactPc blocks with
  | nil =>
      exact
        ⟨compactPc, blocks, by simpa using hValid,
          fun block hBlock => hBlock⟩
  | cons instr rest ih =>
      cases hValid with
      | @cons _ _ _ _ compactSize blockCode restBlocks
          hSize hCode hRest =>
          obtain ⟨suffixCompactPc, suffixBlocks,
              hSuffix, hSubset⟩ :=
            ih hRest
          refine ⟨suffixCompactPc, suffixBlocks, ?_, ?_⟩
          · simpa [Assembly.Program.byteLength_cons,
              Nat.add_assoc] using hSuffix
          · intro block hBlock
            exact by simp [hSubset block hBlock]

theorem straight_openRunNResult_runtime_rel
    {bytes : ByteArray} {pc : Nat}
    {compactCode : List Assembly.Compact.Instr}
    {target source : EVMState}
    (hDecoding : StraightDecoding bytes pc compactCode)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat pc)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel
      Assembly.Compact.RuntimeOutcomeRel
      (Assembly.Compact.InteractionSemantics.openRunNResult
        bytes compactCode.length target)
      (Assembly.InteractionSemantics.Target.openRunListResult
        (compactCode.map Assembly.Compact.Instr.toLogical)
        source) := by
  induction hDecoding generalizing target source with
  | nil pc =>
      apply Simulation.Interaction.Rel.done
      exact Simulation.Interaction.ExceptRel.ok hRel
  | cons pc instr rest hValid hSequential hIndependent hDecode hRest ih =>
      have hStep :=
        Assembly.Compact.InteractionSemantics.openRunNResult_one_runtimeRel
          hValid
          hIndependent
          hDecode hTargetPc hRel
      have hTargetNext :=
        Assembly.Compact.InteractionSemantics.openRunNResult_one_runningAt_next
          hValid hSequential hDecode hTargetPc
      have hStepStrong :=
        Simulation.Interaction.Rel.strengthen_left
          hStep hTargetNext
      rw [show (instr :: rest).length = 1 + rest.length by
          simp [Nat.add_comm],
        Assembly.Compact.InteractionSemantics.openRunNResult_add]
      change
        Simulation.Interaction.Rel
          Assembly.Compact.RuntimeOutcomeRel
          (Simulation.Interaction.bind
            (Assembly.Compact.InteractionSemantics.openRunNResult
              bytes 1 target)
            (fun result =>
              match result with
              | .running mid =>
                  Assembly.Compact.InteractionSemantics.openRunNResult
                    bytes rest.length mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt)))
          (Simulation.Interaction.bind
            (Assembly.InteractionSemantics.Target.openStepInstrResult
              instr.toLogical source)
            (fun result =>
              match result with
              | .running mid =>
                  Assembly.InteractionSemantics.Target.openRunListResult
                    (rest.map Assembly.Compact.Instr.toLogical) mid
              | .halted halt =>
                  Simulation.Interaction.pure (.halted halt)))
      apply Simulation.Interaction.Rel.bind_custom hStepStrong
      intro targetDone sourceDone hDone
      rcases hDone with ⟨hRuntime, hTargetAt⟩
      cases hRuntime with
      | error hError =>
          exact .done (.error hError)
      | ok hResult =>
          rename_i targetResult sourceResult
          cases targetResult with
          | running targetMid =>
              cases sourceResult with
              | running sourceMid =>
                  exact ih hTargetAt hResult
              | halted sourceHalt =>
                  simp [Assembly.Compact.StepResultRuntimeRel]
                    at hResult
          | halted targetHalt =>
              cases sourceResult with
              | running sourceMid =>
                  simp [Assembly.Compact.StepResultRuntimeRel]
                    at hResult
              | halted sourceHalt =>
                  exact
                    .done
                      (.ok hResult)

theorem runtime_rel_right_running_inv
    {run : Assembly.InteractionSemantics.OpenStepResult}
    {source : EVMState}
    (hRel :
      Simulation.Interaction.Rel
        Assembly.Compact.RuntimeOutcomeRel
        run (.done (.ok (.running source)))) :
    ∃ target,
      run = .done (.ok (.running target)) ∧
        Assembly.SameRuntimeData target source := by
  have hSymm := Simulation.Interaction.Rel.symm hRel
  obtain ⟨targetDone, hRun, hDone⟩ :=
    Simulation.Interaction.Rel.done_left hSymm
  cases targetDone with
  | error targetError =>
      cases hDone
  | ok targetResult =>
      cases targetResult with
      | running target =>
          refine ⟨target, hRun, ?_⟩
          cases hDone with
          | ok hResult =>
              exact hResult
      | halted targetHalt =>
          cases hDone with
          | ok hResult =>
              exact False.elim hResult

def firstSelectionTarget
    (site : ReturnSite) (dest : Nat) :
    List Assembly.TargetInstr :=
  [ .prim .dup1
  , .push32 site.token
  , .prim .eq
  , .push32 (EvmYul.UInt256.ofNat dest)
  , .prim .mul
  ]

@[simp] theorem target_openRunListResult_nil
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openRunListResult [] state =
      .done (.ok (.running state)) := rfl

theorem target_openRunListResult_cons
    (instr : Assembly.TargetInstr)
    (rest : List Assembly.TargetInstr) (state : EVMState) :
    Assembly.InteractionSemantics.Target.openRunListResult
        (instr :: rest) state =
      (do
        let result ←
          Assembly.InteractionSemantics.Target.openStepInstrResult
            instr state
        match result with
        | .running state' =>
            Assembly.InteractionSemantics.Target.openRunListResult
              rest state'
        | .halted halt =>
            pure (.halted halt)) := rfl

theorem target_openRunListResult_cons_of_running
    {instr : Assembly.TargetInstr}
    {rest : List Assembly.TargetInstr}
    {state next : EVMState}
    (hStep :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          instr state =
        .done (.ok (.running next))) :
    Assembly.InteractionSemantics.Target.openRunListResult
        (instr :: rest) state =
      Assembly.InteractionSemantics.Target.openRunListResult
        rest next := by
  rw [target_openRunListResult_cons, hStep]
  rfl

theorem target_openRunListResult_append
    (left right : List Assembly.TargetInstr)
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openRunListResult
        (left ++ right) state =
      (do
        let result ←
          Assembly.InteractionSemantics.Target.openRunListResult
            left state
        match result with
        | .running mid =>
            Assembly.InteractionSemantics.Target.openRunListResult
              right mid
        | .halted halt =>
            pure (.halted halt)) := by
  induction left generalizing state with
  | nil =>
      rfl
  | cons instr rest ih =>
      rw [List.cons_append,
        target_openRunListResult_cons]
      calc
        (do
          let result ←
            Assembly.InteractionSemantics.Target.openStepInstrResult
              instr state
          match result with
          | .running state' =>
              Assembly.InteractionSemantics.Target.openRunListResult
                (rest ++ right) state'
          | .halted halt =>
              pure (.halted halt)) =
          (do
            let result ←
              Assembly.InteractionSemantics.Target.openStepInstrResult
                instr state
            match result with
            | .running state' =>
                (do
                  let tailResult ←
                    Assembly.InteractionSemantics.Target.openRunListResult
                      rest state'
                  match tailResult with
                  | .running mid =>
                      Assembly.InteractionSemantics.Target.openRunListResult
                        right mid
                  | .halted halt =>
                      pure (.halted halt))
            | .halted halt =>
                pure (.halted halt)) := by
                  apply congrArg
                    (Simulation.Interaction.bind
                      (Assembly.InteractionSemantics.Target.openStepInstrResult
                        instr state))
                  funext result
                  cases result with
                  | running state' =>
                      exact ih state'
                  | halted halt =>
                      rfl
        _ =
          (do
            let result ←
              Assembly.InteractionSemantics.Target.openRunListResult
                (instr :: rest) state
            match result with
            | .running mid =>
                Assembly.InteractionSemantics.Target.openRunListResult
                  right mid
            | .halted halt =>
                pure (.halted halt)) := by
                  rw [target_openRunListResult_cons]
                  change _ =
                    Simulation.Interaction.bind
                      (Simulation.Interaction.bind
                        (Assembly.InteractionSemantics.Target.openStepInstrResult
                          instr state)
                        (fun result =>
                          match result with
                          | .running state' =>
                              Assembly.InteractionSemantics.Target.openRunListResult
                                rest state'
                          | .halted halt =>
                              pure (.halted halt)))
                      (fun result =>
                        match result with
                        | .running mid =>
                            Assembly.InteractionSemantics.Target.openRunListResult
                              right mid
                        | .halted halt =>
                            pure (.halted halt))
                  rw [Simulation.Interaction.bind_assoc]
                  apply congrArg
                    (Simulation.Interaction.bind
                      (Assembly.InteractionSemantics.Target.openStepInstrResult
                        instr state))
                  funext result
                  cases result <;> rfl

theorem target_openRunListResult_append_of_running
    {left right : List Assembly.TargetInstr}
    {state final : EVMState}
    (hRun :
      Assembly.InteractionSemantics.Target.openRunListResult
          left state =
        .done (.ok (.running final))) :
    Assembly.InteractionSemantics.Target.openRunListResult
        (left ++ right) state =
      Assembly.InteractionSemantics.Target.openRunListResult
        right final := by
  rw [target_openRunListResult_append, hRun]
  rfl

theorem target_openStepInstrResult_prim_continuing
    {op : Assembly.PrimOp} {step : Assembly.PrimStep}
    (state : EVMState)
    (hStep : op.continuingStep? = some step)
    (hGas : op ≠ .gas) (hMsize : op ≠ .msize)
    (hHalt : op.haltKind? = none) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.prim op) state =
      .done
        (Except.map Assembly.StepResult.running
          (step.run state)) := by
  unfold
    Assembly.InteractionSemantics.Target.openStepInstrResult
    Assembly.Target.stepInstrResultWith
    Assembly.InteractionSemantics.Target.openStepInstr
    Assembly.Target.stepInstrWith
  change
    (do
      let state' ←
        Assembly.InteractionSemantics.PrimOp.openStep op state
      match op.haltKind? with
      | some kind =>
          pure
            (Assembly.StepResult.halted
              { kind := kind
                state := state'
                output := kind.output state' })
      | none =>
          pure (Assembly.StepResult.running state')) =
      .done
        (Except.map Assembly.StepResult.running
          (step.run state))
  rw [
    Assembly.InteractionSemantics.PrimOp.openStep_of_continuingStep
      hStep hGas hMsize]
  simp only [Assembly.TargetInstr.haltKind?, hHalt,
    Simulation.Interaction.bind]
  cases step.run state <;> rfl

@[simp] theorem target_openStepInstrResult_dup1
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.prim .dup1) state =
      .done
        (Except.map Assembly.StepResult.running
          ((Assembly.PrimStep.dup 1).run state)) :=
  target_openStepInstrResult_prim_continuing
    state rfl (by decide) (by decide) rfl

@[simp] theorem target_openStepInstrResult_dup2
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.prim .dup2) state =
      .done
        (Except.map Assembly.StepResult.running
          ((Assembly.PrimStep.dup 2).run state)) :=
  target_openStepInstrResult_prim_continuing
    state rfl (by decide) (by decide) rfl

@[simp] theorem target_openStepInstrResult_swap1
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.prim .swap1) state =
      .done
        (Except.map Assembly.StepResult.running
          ((Assembly.PrimStep.swap 1).run state)) :=
  target_openStepInstrResult_prim_continuing
    state rfl (by decide) (by decide) rfl

@[simp] theorem target_openStepInstrResult_pop
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.prim .pop) state =
      .done
        (Except.map Assembly.StepResult.running
          (Assembly.PrimStep.pop.run state)) :=
  target_openStepInstrResult_prim_continuing
    state rfl (by decide) (by decide) rfl

@[simp] theorem target_openStepInstrResult_eq
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.prim .eq) state =
      .done
        (Except.map Assembly.StepResult.running
          ((Assembly.PrimStep.bin EvmYul.UInt256.eq).run state)) :=
  target_openStepInstrResult_prim_continuing
    state rfl (by decide) (by decide) rfl

@[simp] theorem target_openStepInstrResult_mul
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.prim .mul) state =
      .done
        (Except.map Assembly.StepResult.running
          ((Assembly.PrimStep.bin EvmYul.UInt256.mul).run state)) :=
  target_openStepInstrResult_prim_continuing
    state rfl (by decide) (by decide) rfl

@[simp] theorem target_openStepInstrResult_add
    (state : EVMState) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.prim .add) state =
      .done
        (Except.map Assembly.StepResult.running
          ((Assembly.PrimStep.bin EvmYul.UInt256.add).run state)) :=
  target_openStepInstrResult_prim_continuing
    state rfl (by decide) (by decide) rfl

@[simp] theorem target_openStepInstrResult_push32
    (value : Word) (state : EVMState) :
    Assembly.InteractionSemantics.Target.openStepInstrResult
        (.push32 value) state =
      .done
        (.ok
          (.running
            (state.replaceStackAndIncrPC
              (EvmYul.Stack.push state.stack value)
              (pcΔ := Assembly.Instr.push32Size)))) := by
  rfl

theorem firstSelectionTarget_openRunListResult
    (site : ReturnSite) (dest : Nat)
    (state : EVMState) (token : Word) (suffix : List Word) :
    ∃ final,
      Assembly.InteractionSemantics.Target.openRunListResult
          (firstSelectionTarget site dest)
          { state with stack := token :: suffix } =
        .done (.ok (.running final)) ∧
      final.stack =
        EvmYul.UInt256.mul
            (EvmYul.UInt256.ofNat dest)
            (EvmYul.UInt256.eq site.token token) ::
          token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              EvmYul.UInt256.mul
                  (EvmYul.UInt256.ofNat dest)
                  (EvmYul.UInt256.eq site.token token) ::
                token :: suffix } := by
  let s0 : EVMState := { state with stack := token :: suffix }
  let s1 : EVMState :=
    s0.replaceStackAndIncrPC (token :: token :: suffix)
  let s2 : EVMState :=
    s1.replaceStackAndIncrPC
      (site.token :: token :: token :: suffix)
      (pcΔ := Assembly.Instr.push32Size)
  let s3 : EVMState :=
    s2.replaceStackAndIncrPC
      (EvmYul.UInt256.eq site.token token :: token :: suffix)
  let s4 : EVMState :=
    s3.replaceStackAndIncrPC
      (EvmYul.UInt256.ofNat dest ::
        EvmYul.UInt256.eq site.token token :: token :: suffix)
      (pcΔ := Assembly.Instr.push32Size)
  let s5 : EVMState :=
    s4.replaceStackAndIncrPC
      (EvmYul.UInt256.mul
          (EvmYul.UInt256.ofNat dest)
          (EvmYul.UInt256.eq site.token token) ::
        token :: suffix)
  have hDup :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.prim .dup1) s0 =
        .done (.ok (.running s1)) := by
    rw [target_openStepInstrResult_dup1]
    simp [s0, s1, Assembly.PrimStep.run, EvmYul.dup,
      Except.map, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hPushToken :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.push32 site.token) s1 =
        .done (.ok (.running s2)) := by
    rw [target_openStepInstrResult_push32]
    rfl
  have hEq :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.prim .eq) s2 =
        .done (.ok (.running s3)) := by
    rw [target_openStepInstrResult_eq]
    simp [s2, s3, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2,
      EvmYul.Stack.push,
      Except.map, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hPushDest :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.push32 (EvmYul.UInt256.ofNat dest)) s3 =
        .done (.ok (.running s4)) := by
    rw [target_openStepInstrResult_push32]
    rfl
  have hMul :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.prim .mul) s4 =
        .done (.ok (.running s5)) := by
    rw [target_openStepInstrResult_mul]
    simp [s4, s5, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2,
      EvmYul.Stack.push,
      Except.map, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  refine ⟨s5, ?_, ?_, ?_⟩
  · change
      Assembly.InteractionSemantics.Target.openRunListResult
          (firstSelectionTarget site dest) s0 =
        .done (.ok (.running s5))
    rw [firstSelectionTarget,
      target_openRunListResult_cons_of_running hDup,
      target_openRunListResult_cons_of_running hPushToken,
      target_openRunListResult_cons_of_running hEq,
      target_openRunListResult_cons_of_running hPushDest,
      target_openRunListResult_cons_of_running hMul,
      target_openRunListResult_nil]
  · simp [s5, s4, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · cases state
    rfl

def nextSelectionTarget
    (site : ReturnSite) (dest : Nat) :
    List Assembly.TargetInstr :=
  [ .prim .dup2
  , .push32 site.token
  , .prim .eq
  , .push32 (EvmYul.UInt256.ofNat dest)
  , .prim .mul
  , .prim .add
  ]

theorem nextSelectionTarget_openRunListResult
    (site : ReturnSite) (dest : Nat)
    (state : EVMState) (accumulator token : Word)
    (suffix : List Word) :
    ∃ final,
      Assembly.InteractionSemantics.Target.openRunListResult
          (nextSelectionTarget site dest)
          { state with stack := accumulator :: token :: suffix } =
        .done (.ok (.running final)) ∧
      final.stack =
        EvmYul.UInt256.add
            (EvmYul.UInt256.mul
              (EvmYul.UInt256.ofNat dest)
              (EvmYul.UInt256.eq site.token token))
            accumulator ::
          token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              EvmYul.UInt256.add
                  (EvmYul.UInt256.mul
                    (EvmYul.UInt256.ofNat dest)
                    (EvmYul.UInt256.eq site.token token))
                  accumulator ::
                token :: suffix } := by
  let s0 : EVMState :=
    { state with stack := accumulator :: token :: suffix }
  let s1 : EVMState :=
    s0.replaceStackAndIncrPC
      (token :: accumulator :: token :: suffix)
  let s2 : EVMState :=
    s1.replaceStackAndIncrPC
      (site.token :: token :: accumulator :: token :: suffix)
      (pcΔ := Assembly.Instr.push32Size)
  let condition := EvmYul.UInt256.eq site.token token
  let s3 : EVMState :=
    s2.replaceStackAndIncrPC
      (condition :: accumulator :: token :: suffix)
  let selected :=
    EvmYul.UInt256.mul
      (EvmYul.UInt256.ofNat dest) condition
  let s4 : EVMState :=
    s3.replaceStackAndIncrPC
      (EvmYul.UInt256.ofNat dest ::
        condition :: accumulator :: token :: suffix)
      (pcΔ := Assembly.Instr.push32Size)
  let s5 : EVMState :=
    s4.replaceStackAndIncrPC
      (selected :: accumulator :: token :: suffix)
  let s6 : EVMState :=
    s5.replaceStackAndIncrPC
      (EvmYul.UInt256.add selected accumulator ::
        token :: suffix)
  have hDup :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.prim .dup2) s0 =
        .done (.ok (.running s1)) := by
    rw [target_openStepInstrResult_dup2]
    simp [s0, s1, Assembly.PrimStep.run, EvmYul.dup,
      Except.map, EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  have hPushToken :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.push32 site.token) s1 =
        .done (.ok (.running s2)) := by
    rw [target_openStepInstrResult_push32]
    rfl
  have hEq :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.prim .eq) s2 =
        .done (.ok (.running s3)) := by
    rw [target_openStepInstrResult_eq]
    simp [s2, s3, condition, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2,
      EvmYul.Stack.push, Except.map,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hPushDest :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.push32 (EvmYul.UInt256.ofNat dest)) s3 =
        .done (.ok (.running s4)) := by
    rw [target_openStepInstrResult_push32]
    rfl
  have hMul :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.prim .mul) s4 =
        .done (.ok (.running s5)) := by
    rw [target_openStepInstrResult_mul]
    simp [s4, s5, selected, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2,
      EvmYul.Stack.push, Except.map,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  have hAdd :
      Assembly.InteractionSemantics.Target.openStepInstrResult
          (.prim .add) s5 =
        .done (.ok (.running s6)) := by
    rw [target_openStepInstrResult_add]
    simp [s5, s6, Assembly.PrimStep.run,
      EvmYul.EVM.execBinOp, EvmYul.Stack.pop2,
      EvmYul.Stack.push, Except.map,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC, Id.run]
  refine ⟨s6, ?_, ?_, ?_⟩
  · change
      Assembly.InteractionSemantics.Target.openRunListResult
          (nextSelectionTarget site dest) s0 =
        .done (.ok (.running s6))
    rw [nextSelectionTarget,
      target_openRunListResult_cons_of_running hDup,
      target_openRunListResult_cons_of_running hPushToken,
      target_openRunListResult_cons_of_running hEq,
      target_openRunListResult_cons_of_running hPushDest,
      target_openRunListResult_cons_of_running hMul,
      target_openRunListResult_cons_of_running hAdd,
      target_openRunListResult_nil]
  · simp [s6, s5, selected, condition,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC]
  · cases state
    rfl

def nextSelectionsTarget?
    (labels : Assembly.Compact.LabelTable) :
    List ReturnSite → Option (List Assembly.TargetInstr)
  | [] =>
      some []
  | site :: rest => do
      let dest ←
        Assembly.Compact.lookupLabel? labels site.target
      let tail ← nextSelectionsTarget? labels rest
      some (nextSelectionTarget site dest ++ tail)

theorem nextSelectionsTarget?_openRunListResult
    (labels : Assembly.Compact.LabelTable)
    (sites : List ReturnSite) (state : EVMState)
    (accumulator token : Word) (suffix : List Word)
    {code : List Assembly.TargetInstr}
    (hCode : nextSelectionsTarget? labels sites = some code) :
    ∃ final,
      Assembly.InteractionSemantics.Target.openRunListResult
          code
          { state with
            stack := accumulator :: token :: suffix } =
        .done (.ok (.running final)) ∧
      final.stack =
        sites.foldl
            (fun value site =>
              EvmYul.UInt256.add
                (LateReturnPreservation.selectedAddress
                  (Assembly.Compact.lookupLabel? labels)
                  token site)
                value)
            accumulator ::
          token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              sites.foldl
                  (fun value site =>
                    EvmYul.UInt256.add
                      (LateReturnPreservation.selectedAddress
                        (Assembly.Compact.lookupLabel? labels)
                        token site)
                      value)
                  accumulator ::
                token :: suffix } := by
  induction sites generalizing state accumulator code with
  | nil =>
      simp [nextSelectionsTarget?] at hCode
      subst code
      exact
        ⟨{ state with stack := accumulator :: token :: suffix },
          rfl, rfl, rfl⟩
  | cons site rest ih =>
      unfold nextSelectionsTarget? at hCode
      cases hDest :
          Assembly.Compact.lookupLabel? labels site.target with
      | none =>
          simp [hDest] at hCode
      | some dest =>
          simp [hDest] at hCode
          cases hTail : nextSelectionsTarget? labels rest with
          | none =>
              simp [hTail] at hCode
          | some tailCode =>
              simp [hTail] at hCode
              subst code
              obtain ⟨mid, hHeadRun, hHeadStack, hHeadRuntime⟩ :=
                nextSelectionTarget_openRunListResult
                  site dest state accumulator token suffix
              let selected :=
                LateReturnPreservation.selectedAddress
                  (Assembly.Compact.lookupLabel? labels)
                  token site
              let nextAccumulator :=
                EvmYul.UInt256.add selected accumulator
              have hSelected :
                  EvmYul.UInt256.mul
                      (EvmYul.UInt256.ofNat dest)
                      (EvmYul.UInt256.eq site.token token) =
                    selected := by
                exact
                  LateReturnPreservation.mul_eq_selectedAddress
                    (Assembly.Compact.lookupLabel? labels)
                    token site hDest
              have hMidStack :
                  mid.stack =
                    nextAccumulator :: token :: suffix := by
                simpa [nextAccumulator, selected, hSelected]
                  using hHeadStack
              have hMidRuntime :
                  Assembly.eraseRuntimeControl mid =
                    Assembly.eraseRuntimeControl
                      { state with
                        stack :=
                          nextAccumulator :: token :: suffix } := by
                simpa [nextAccumulator, selected, hSelected]
                  using hHeadRuntime
              obtain ⟨final, hTailRun, hFinalStack,
                  hFinalRuntime⟩ :=
                ih (state := mid)
                  (accumulator := nextAccumulator) hTail
              have hMidExact :
                  { mid with
                    stack := nextAccumulator :: token :: suffix } =
                    mid := by
                cases mid
                simp_all
              rw [hMidExact] at hTailRun
              refine ⟨final, ?_, ?_, ?_⟩
              · have hHeadRun' :
                    Assembly.InteractionSemantics.Target.openRunListResult
                        (nextSelectionTarget site dest)
                        { state with
                          stack := accumulator :: token :: suffix } =
                      .done (.ok (.running mid)) :=
                  hHeadRun
                rw [
                  target_openRunListResult_append_of_running
                    hHeadRun',
                  hTailRun]
              · simpa [nextAccumulator, selected]
                  using hFinalStack
              · let finalAccumulator :=
                  rest.foldl
                    (fun value candidate =>
                      EvmYul.UInt256.add
                        (LateReturnPreservation.selectedAddress
                          (Assembly.Compact.lookupLabel? labels)
                          token candidate)
                        value)
                    nextAccumulator
                have hFinalRuntime' :
                    Assembly.eraseRuntimeControl final =
                      Assembly.eraseRuntimeControl
                        { mid with
                          stack :=
                            finalAccumulator :: token :: suffix } := by
                  simpa [finalAccumulator] using hFinalRuntime
                calc
                  Assembly.eraseRuntimeControl final =
                      Assembly.eraseRuntimeControl
                        { mid with
                          stack :=
                            finalAccumulator :: token :: suffix } :=
                    hFinalRuntime'
                  _ =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack :=
                            finalAccumulator :: token :: suffix } := by
                    exact
                      Assembly.eraseRuntimeControl_with_stack_congr
                        (left := mid)
                        (right :=
                          { state with
                            stack :=
                              nextAccumulator :: token :: suffix })
                        (stack :=
                          finalAccumulator :: token :: suffix)
                        hMidRuntime
                  _ =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack :=
                            (site :: rest).foldl
                                (fun value candidate =>
                                  EvmYul.UInt256.add
                                    (LateReturnPreservation.selectedAddress
                                      (Assembly.Compact.lookupLabel? labels)
                                      token candidate)
                                    value)
                                accumulator ::
                              token :: suffix } := by
                    simp [finalAccumulator, nextAccumulator, selected]

def selectionTarget?
    (labels : Assembly.Compact.LabelTable) :
    List ReturnSite → Option (List Assembly.TargetInstr)
  | [] =>
      none
  | first :: rest => do
      let dest ←
        Assembly.Compact.lookupLabel? labels first.target
      let tail ← nextSelectionsTarget? labels rest
      some (firstSelectionTarget first dest ++ tail)

def selectionAndTestTarget?
    (labels : Assembly.Compact.LabelTable)
    (sites : List ReturnSite) :
    Option (List Assembly.TargetInstr) := do
  let selection ← selectionTarget? labels sites
  some
    (selection ++
      [ .prim .swap1
      , .prim .pop
      , .prim .dup1
      ])

theorem resolvedTargetFrom?_firstSelection
    (labels : Assembly.Compact.LabelTable)
    (site : ReturnSite) :
    resolvedTargetFrom? labels
        (LateReturnProbe.Terminator.firstSelection site) =
      (do
        let dest ←
          Assembly.Compact.lookupLabel? labels site.target
        some (firstSelectionTarget site dest)) := by
  cases hDest :
      Assembly.Compact.lookupLabel? labels site.target <;>
    simp [LateReturnProbe.Terminator.firstSelection,
      resolvedTargetFrom?, resolvedTargetInstr?,
      firstSelectionTarget, Assembly.StackShuffle.dupInstr,
      hDest]

theorem resolvedTargetFrom?_nextSelection
    (labels : Assembly.Compact.LabelTable)
    (site : ReturnSite) :
    resolvedTargetFrom? labels
        (LateReturnProbe.Terminator.nextSelection site) =
      (do
        let dest ←
          Assembly.Compact.lookupLabel? labels site.target
        some (nextSelectionTarget site dest)) := by
  cases hDest :
      Assembly.Compact.lookupLabel? labels site.target <;>
    simp [LateReturnProbe.Terminator.nextSelection,
      resolvedTargetFrom?, resolvedTargetInstr?,
      nextSelectionTarget, Assembly.StackShuffle.dupInstr,
      hDest]

theorem resolvedTargetFrom?_nextSelections
    (labels : Assembly.Compact.LabelTable)
    (sites : List ReturnSite) :
    resolvedTargetFrom? labels
        (sites.flatMap LateReturnProbe.Terminator.nextSelection) =
      nextSelectionsTarget? labels sites := by
  induction sites with
  | nil =>
      simp [resolvedTargetFrom?, nextSelectionsTarget?]
  | cons site rest ih =>
      rw [List.flatMap_cons, resolvedTargetFrom?_append,
        resolvedTargetFrom?_nextSelection, ih]
      cases hDest :
          Assembly.Compact.lookupLabel? labels site.target <;>
        cases hTail : nextSelectionsTarget? labels rest <;>
          simp [nextSelectionsTarget?, hDest, hTail]

theorem resolvedTargetFrom?_selectionCode_cons
    (labels : Assembly.Compact.LabelTable)
    (first : ReturnSite) (rest : List ReturnSite) :
    resolvedTargetFrom? labels
        (LateReturnProbe.Terminator.selectionCode (first :: rest)) =
      selectionTarget? labels (first :: rest) := by
  rw [show
    LateReturnProbe.Terminator.selectionCode (first :: rest) =
      LateReturnProbe.Terminator.firstSelection first ++
        rest.flatMap LateReturnProbe.Terminator.nextSelection by
      simp [LateReturnProbe.Terminator.selectionCode]]
  rw [resolvedTargetFrom?_append,
    resolvedTargetFrom?_firstSelection,
    resolvedTargetFrom?_nextSelections]
  cases hDest :
      Assembly.Compact.lookupLabel? labels first.target <;>
    cases hTail : nextSelectionsTarget? labels rest <;>
      simp [selectionTarget?, hDest, hTail]

theorem resolvedTargetFrom?_selectionAndTest_cons
    (labels : Assembly.Compact.LabelTable)
    (first : ReturnSite) (rest : List ReturnSite) :
    resolvedTargetFrom? labels
        (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
          Assembly.StackShuffle.removeBuriedUnder 1 ++
          [Assembly.StackShuffle.dupInstr 1]) =
      selectionAndTestTarget? labels (first :: rest) := by
  rw [resolvedTargetFrom?_append,
    resolvedTargetFrom?_append,
    resolvedTargetFrom?_selectionCode_cons]
  cases hSelection :
      selectionTarget? labels (first :: rest) <;>
    simp [selectionAndTestTarget?, resolvedTargetFrom?,
      resolvedTargetInstr?, Assembly.StackShuffle.removeBuriedUnder,
      Assembly.StackShuffle.liftBuriedToTop,
      Assembly.StackShuffle.swapInstr,
      Assembly.StackShuffle.dupInstr, hSelection,
      List.append_assoc]

theorem selectionTarget?_openRunListResult
    (labels : Assembly.Compact.LabelTable)
    (sites : List ReturnSite) (state : EVMState)
    (token : Word) (suffix : List Word)
    {code : List Assembly.TargetInstr}
    (hCode : selectionTarget? labels sites = some code) :
    ∃ final,
      Assembly.InteractionSemantics.Target.openRunListResult
          code
          { state with stack := token :: suffix } =
        .done (.ok (.running final)) ∧
      final.stack =
        LateReturnPreservation.selectedAddressSum
            (Assembly.Compact.lookupLabel? labels)
            token sites ::
          token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              LateReturnPreservation.selectedAddressSum
                  (Assembly.Compact.lookupLabel? labels)
                  token sites ::
                token :: suffix } := by
  cases sites with
  | nil =>
      simp [selectionTarget?] at hCode
  | cons first rest =>
      unfold selectionTarget? at hCode
      cases hDest :
          Assembly.Compact.lookupLabel? labels first.target with
      | none =>
          simp [hDest] at hCode
      | some dest =>
          simp [hDest] at hCode
          cases hTail : nextSelectionsTarget? labels rest with
          | none =>
              simp [hTail] at hCode
          | some tailCode =>
              simp [hTail] at hCode
              subst code
              obtain ⟨mid, hHeadRun, hHeadStack, hHeadRuntime⟩ :=
                firstSelectionTarget_openRunListResult
                  first dest state token suffix
              let firstValue :=
                LateReturnPreservation.selectedAddress
                  (Assembly.Compact.lookupLabel? labels)
                  token first
              have hFirstValue :
                  EvmYul.UInt256.mul
                      (EvmYul.UInt256.ofNat dest)
                      (EvmYul.UInt256.eq first.token token) =
                    firstValue := by
                exact
                  LateReturnPreservation.mul_eq_selectedAddress
                    (Assembly.Compact.lookupLabel? labels)
                    token first hDest
              have hMidStack :
                  mid.stack = firstValue :: token :: suffix := by
                simpa [firstValue, hFirstValue] using hHeadStack
              have hMidRuntime :
                  Assembly.eraseRuntimeControl mid =
                    Assembly.eraseRuntimeControl
                      { state with
                        stack := firstValue :: token :: suffix } := by
                simpa [firstValue, hFirstValue] using hHeadRuntime
              obtain ⟨final, hTailRun, hFinalStack,
                  hFinalRuntime⟩ :=
                nextSelectionsTarget?_openRunListResult
                  labels rest mid firstValue token suffix hTail
              have hMidExact :
                  { mid with stack := firstValue :: token :: suffix } =
                    mid := by
                cases mid
                simp_all
              rw [hMidExact] at hTailRun
              refine ⟨final, ?_, ?_, ?_⟩
              · rw [
                  target_openRunListResult_append_of_running
                    hHeadRun,
                  hTailRun]
              · simpa [LateReturnPreservation.selectedAddressSum,
                  firstValue] using hFinalStack
              · let finalValue :=
                  rest.foldl
                    (fun value site =>
                      EvmYul.UInt256.add
                        (LateReturnPreservation.selectedAddress
                          (Assembly.Compact.lookupLabel? labels)
                          token site)
                        value)
                    firstValue
                have hFinalRuntime' :
                    Assembly.eraseRuntimeControl final =
                      Assembly.eraseRuntimeControl
                        { mid with
                          stack := finalValue :: token :: suffix } := by
                  simpa [finalValue] using hFinalRuntime
                calc
                  Assembly.eraseRuntimeControl final =
                      Assembly.eraseRuntimeControl
                        { mid with
                          stack := finalValue :: token :: suffix } :=
                    hFinalRuntime'
                  _ =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack := finalValue :: token :: suffix } := by
                    exact
                      Assembly.eraseRuntimeControl_with_stack_congr
                        (left := mid)
                        (right :=
                          { state with
                            stack := firstValue :: token :: suffix })
                        (stack := finalValue :: token :: suffix)
                        hMidRuntime
                  _ =
                      Assembly.eraseRuntimeControl
                        { state with
                          stack :=
                            LateReturnPreservation.selectedAddressSum
                                (Assembly.Compact.lookupLabel? labels)
                                token (first :: rest) ::
                              token :: suffix } := by
                    simp [LateReturnPreservation.selectedAddressSum,
                      finalValue, firstValue]

theorem selectionAndTestTarget?_openRunListResult
    (labels : Assembly.Compact.LabelTable)
    (first : ReturnSite) (rest : List ReturnSite)
    (state : EVMState) (token : Word) (suffix : List Word)
    {code : List Assembly.TargetInstr}
    (hCode :
      selectionAndTestTarget? labels (first :: rest) =
        some code) :
    ∃ final,
      Assembly.InteractionSemantics.Target.openRunListResult
          code { state with stack := token :: suffix } =
        .done (.ok (.running final)) ∧
      final.stack =
        LateReturnPreservation.selectedAddressSum
              (Assembly.Compact.lookupLabel? labels)
              token (first :: rest) ::
          LateReturnPreservation.selectedAddressSum
              (Assembly.Compact.lookupLabel? labels)
              token (first :: rest) ::
            suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with
            stack :=
              LateReturnPreservation.selectedAddressSum
                    (Assembly.Compact.lookupLabel? labels)
                    token (first :: rest) ::
                LateReturnPreservation.selectedAddressSum
                    (Assembly.Compact.lookupLabel? labels)
                    token (first :: rest) ::
                  suffix } := by
  cases hSelection :
      selectionTarget? labels (first :: rest) with
  | none =>
      simp [selectionAndTestTarget?, hSelection] at hCode
  | some selectionCode =>
      simp [selectionAndTestTarget?, hSelection] at hCode
      subst code
      obtain ⟨selected, hSelectionRun, hSelectedStack,
          hSelectedRuntime⟩ :=
        selectionTarget?_openRunListResult
          labels (first :: rest) state token suffix hSelection
      let destination :=
        LateReturnPreservation.selectedAddressSum
          (Assembly.Compact.lookupLabel? labels)
          token (first :: rest)
      have hSelectedStack' :
          selected.stack = destination :: token :: suffix := by
        simpa [destination] using hSelectedStack
      let swapped : EVMState :=
        selected.replaceStackAndIncrPC
          (token :: destination :: suffix)
      let popped : EVMState :=
        swapped.replaceStackAndIncrPC
          (destination :: suffix)
      let duplicated : EVMState :=
        popped.replaceStackAndIncrPC
          (destination :: destination :: suffix)
      have hSwap :
          Assembly.InteractionSemantics.Target.openStepInstrResult
              (.prim .swap1) selected =
            .done (.ok (.running swapped)) := by
        rw [target_openStepInstrResult_swap1]
        simp [Assembly.PrimStep.run, EvmYul.swap,
          hSelectedStack', swapped,
          Except.map,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hPop :
          Assembly.InteractionSemantics.Target.openStepInstrResult
              (.prim .pop) swapped =
            .done (.ok (.running popped)) := by
        rw [target_openStepInstrResult_pop]
        simp [Assembly.PrimStep.run, EvmYul.Stack.pop,
          swapped, popped,
          Except.map,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      have hDup :
          Assembly.InteractionSemantics.Target.openStepInstrResult
              (.prim .dup1) popped =
            .done (.ok (.running duplicated)) := by
        rw [target_openStepInstrResult_dup1]
        simp [Assembly.PrimStep.run, EvmYul.dup,
          popped, duplicated,
          Except.map,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      refine ⟨duplicated, ?_, ?_, ?_⟩
      · rw [target_openRunListResult_append_of_running
              hSelectionRun,
            target_openRunListResult_cons_of_running hSwap,
            target_openRunListResult_cons_of_running hPop,
            target_openRunListResult_cons_of_running hDup,
            target_openRunListResult_nil]
      · simp [duplicated, popped, swapped, destination,
          EvmYul.EVM.State.replaceStackAndIncrPC,
          EvmYul.EVM.State.incrPC]
      · have hDuplicatedRuntime :
            Assembly.eraseRuntimeControl duplicated =
              Assembly.eraseRuntimeControl
                { selected with
                  stack :=
                    destination :: destination :: suffix } := by
          cases selected
          rfl
        calc
          Assembly.eraseRuntimeControl duplicated =
              Assembly.eraseRuntimeControl
                { selected with
                  stack :=
                    destination :: destination :: suffix } :=
            hDuplicatedRuntime
          _ =
              Assembly.eraseRuntimeControl
                { state with
                  stack :=
                    destination :: destination :: suffix } := by
            exact
              Assembly.eraseRuntimeControl_with_stack_congr
                (left := selected)
                (right :=
                  { state with
                    stack := destination :: token :: suffix })
                (stack :=
                  destination :: destination :: suffix)
                (by simpa [destination] using hSelectedRuntime)
          _ =
              Assembly.eraseRuntimeControl
                { state with
                  stack :=
                    LateReturnPreservation.selectedAddressSum
                          (Assembly.Compact.lookupLabel? labels)
                          token (first :: rest) ::
                      LateReturnPreservation.selectedAddressSum
                          (Assembly.Compact.lookupLabel? labels)
                          token (first :: rest) ::
                        suffix } := by
            rfl

theorem selectionCode_straight_openRunNResult_runtime_rel
    {pinnedPushPcs : List Nat} {branchWidth sourcePc pc : Nat}
    {labels : Assembly.Compact.LabelTable}
    {bytes : ByteArray}
    {first : ReturnSite} {rest : List ReturnSite}
    {compactCode : List Assembly.Compact.Instr}
    {target source : EVMState}
    (hResolved :
      resolvedStraightFrom? pinnedPushPcs branchWidth labels
          (LateReturnProbe.Terminator.selectionCode (first :: rest))
          sourcePc =
        some compactCode)
    (hDecoding : StraightDecoding bytes pc compactCode)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat pc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (token : Word) (suffix : List Word)
    (hSourceStack : source.stack = token :: suffix) :
    ∃ final,
      Simulation.Interaction.Rel
        Assembly.Compact.RuntimeOutcomeRel
        (Assembly.Compact.InteractionSemantics.openRunNResult
          bytes compactCode.length target)
        (.done (.ok (.running final))) ∧
      final.stack =
        LateReturnPreservation.selectedAddressSum
            (Assembly.Compact.lookupLabel? labels)
            token (first :: rest) ::
          token :: suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { source with
            stack :=
              LateReturnPreservation.selectedAddressSum
                  (Assembly.Compact.lookupLabel? labels)
                  token (first :: rest) ::
                token :: suffix } := by
  have hTargetCode :=
    resolvedStraightFrom?_toLogical hResolved
  rw [resolvedTargetFrom?_selectionCode_cons] at hTargetCode
  obtain ⟨final, hRun, hStack, hFinalRuntime⟩ :=
    selectionTarget?_openRunListResult
      labels (first :: rest) source token suffix hTargetCode
  have hSourceExact :
      { source with stack := token :: suffix } = source := by
    cases source
    simp_all
  rw [hSourceExact] at hRun
  have hRel :=
    straight_openRunNResult_runtime_rel
      hDecoding hTargetPc hRuntime
  rw [hRun] at hRel
  exact
    ⟨final, hRel, hStack, hFinalRuntime⟩

theorem selectionAndTest_straight_openRunNResult_runtime_rel
    {pinnedPushPcs : List Nat} {branchWidth sourcePc pc : Nat}
    {labels : Assembly.Compact.LabelTable}
    {bytes : ByteArray}
    {first : ReturnSite} {rest : List ReturnSite}
    {compactCode : List Assembly.Compact.Instr}
    {target source : EVMState}
    (hResolved :
      resolvedStraightFrom? pinnedPushPcs branchWidth labels
          (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
            Assembly.StackShuffle.removeBuriedUnder 1 ++
            [Assembly.StackShuffle.dupInstr 1])
          sourcePc =
        some compactCode)
    (hDecoding : StraightDecoding bytes pc compactCode)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat pc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (token : Word) (suffix : List Word)
    (hSourceStack : source.stack = token :: suffix) :
    ∃ final,
      Simulation.Interaction.Rel
        Assembly.Compact.RuntimeOutcomeRel
        (Assembly.Compact.InteractionSemantics.openRunNResult
          bytes compactCode.length target)
        (.done (.ok (.running final))) ∧
      final.stack =
        LateReturnPreservation.selectedAddressSum
              (Assembly.Compact.lookupLabel? labels)
              token (first :: rest) ::
          LateReturnPreservation.selectedAddressSum
              (Assembly.Compact.lookupLabel? labels)
              token (first :: rest) ::
            suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { source with
            stack :=
              LateReturnPreservation.selectedAddressSum
                    (Assembly.Compact.lookupLabel? labels)
                    token (first :: rest) ::
                LateReturnPreservation.selectedAddressSum
                    (Assembly.Compact.lookupLabel? labels)
                    token (first :: rest) ::
                  suffix } := by
  have hTargetCode :=
    resolvedStraightFrom?_toLogical hResolved
  rw [resolvedTargetFrom?_selectionAndTest_cons] at hTargetCode
  obtain ⟨final, hRun, hStack, hFinalRuntime⟩ :=
    selectionAndTestTarget?_openRunListResult
      labels first rest source token suffix hTargetCode
  have hSourceExact :
      { source with stack := token :: suffix } = source := by
    cases source
    simp_all
  rw [hSourceExact] at hRun
  have hRel :=
    straight_openRunNResult_runtime_rel
      hDecoding hTargetPc hRuntime
  rw [hRun] at hRel
  exact
    ⟨final, hRel, hStack, hFinalRuntime⟩

theorem selectionAndTest_straight_openRunNResult
    {pinnedPushPcs : List Nat} {branchWidth sourcePc pc : Nat}
    {labels : Assembly.Compact.LabelTable}
    {bytes : ByteArray}
    {first : ReturnSite} {rest : List ReturnSite}
    {compactCode : List Assembly.Compact.Instr}
    {target source : EVMState}
    (hResolved :
      resolvedStraightFrom? pinnedPushPcs branchWidth labels
          (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
            Assembly.StackShuffle.removeBuriedUnder 1 ++
            [Assembly.StackShuffle.dupInstr 1])
          sourcePc =
        some compactCode)
    (hDecoding : StraightDecoding bytes pc compactCode)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat pc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (token : Word) (suffix : List Word)
    (hSourceStack : source.stack = token :: suffix) :
    ∃ final,
      Assembly.Compact.InteractionSemantics.openRunNResult
          bytes compactCode.length target =
        .done (.ok (.running final)) ∧
      final.pc =
        EvmYul.UInt256.ofNat (straightEndPc pc compactCode) ∧
      final.stack =
        LateReturnPreservation.selectedAddressSum
              (Assembly.Compact.lookupLabel? labels)
              token (first :: rest) ::
          LateReturnPreservation.selectedAddressSum
              (Assembly.Compact.lookupLabel? labels)
              token (first :: rest) ::
            suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { source with
            stack :=
              LateReturnPreservation.selectedAddressSum
                    (Assembly.Compact.lookupLabel? labels)
                    token (first :: rest) ::
                LateReturnPreservation.selectedAddressSum
                    (Assembly.Compact.lookupLabel? labels)
                    token (first :: rest) ::
                  suffix } := by
  obtain ⟨sourceFinal, hRel, hSourceFinalStack,
      hSourceFinalRuntime⟩ :=
    selectionAndTest_straight_openRunNResult_runtime_rel
      hResolved hDecoding hTargetPc hRuntime
      token suffix hSourceStack
  obtain ⟨final, hRun, hFinalRel⟩ :=
    runtime_rel_right_running_inv hRel
  have hAt :=
    straight_openRunNResult_runningAt_end
      hDecoding hTargetPc
  rw [hRun] at hAt
  have hFinalPc :
      final.pc =
        EvmYul.UInt256.ofNat
          (straightEndPc pc compactCode) := by
    cases hAt with
    | done hDone =>
        exact hDone
  refine ⟨final, hRun, hFinalPc, ?_, ?_⟩
  · exact
      (Assembly.SameRuntimeData.stack_eq hFinalRel).trans
        hSourceFinalStack
  · exact hFinalRel.trans hSourceFinalRuntime

theorem compact_taken_return_tail
    {bytes : ByteArray}
    {branchPc branchWidth casePc : Nat}
    {destination : Word}
    {state : EVMState} {suffix : List Word}
    (hPushValid :
      (Assembly.Compact.Instr.push branchWidth
        (EvmYul.UInt256.ofNat casePc)).Valid)
    (hDecodePush :
      Assembly.Compact.decodeAt bytes branchPc
        (.push branchWidth (EvmYul.UInt256.ofNat casePc)))
    (hDecodeJumpi :
      Assembly.Compact.decodeAt bytes
        (branchPc + branchWidth + 1) .jumpi)
    (hDecodeCase :
      Assembly.Compact.decodeAt bytes casePc .jumpdest)
    (hDecodeJump :
      Assembly.Compact.decodeAt bytes (casePc + 1) .jump)
    (hPc : state.pc = EvmYul.UInt256.ofNat branchPc)
    (hStack :
      state.stack = destination :: destination :: suffix)
    (hNonzero : destination ≠ EvmYul.UInt256.ofNat 0) :
    ∃ final,
      Assembly.Compact.InteractionSemantics.openRunNResult
          bytes 4 state =
        .done (.ok (.running final)) ∧
      final.pc = destination ∧
      final.stack = suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { state with stack := suffix } := by
  let pushed : EVMState :=
    state.replaceStackAndIncrPC
      (EvmYul.UInt256.ofNat casePc ::
        destination :: destination :: suffix)
      (pcΔ := branchWidth + 1)
  let branched : EVMState :=
    { pushed with
      pc := EvmYul.UInt256.ofNat casePc
      stack := destination :: suffix }
  let entered : EVMState :=
    branched.incrPC
  let final : EVMState :=
    { entered with
      pc := destination
      stack := suffix }
  have hPushedPc :
      pushed.pc =
        EvmYul.UInt256.ofNat
          (branchPc + branchWidth + 1) := by
    simp [pushed, hPc,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC,
      Assembly.UInt256_ofNat_add,
      Nat.add_assoc]
  have hBranchedPc :
      branched.pc = EvmYul.UInt256.ofNat casePc := by
    rfl
  have hEnteredPc :
      entered.pc = EvmYul.UInt256.ofNat (casePc + 1) := by
    simp [entered, branched,
      EvmYul.EVM.State.incrPC,
      Assembly.UInt256_ofNat_add]
  have hPushOpen :
      (Assembly.Compact.Instr.push branchWidth
          (EvmYul.UInt256.ofNat casePc)).openStep state =
        .done (.ok pushed) := by
    simp [Assembly.Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepPush,
      Assembly.Target.stepPushWith,
      EvmYul.Stack.push, pushed, hStack]
  have hPushStep :
      Assembly.Compact.InteractionSemantics.openStepResult
          bytes state =
        .done (.ok (.running pushed)) := by
    rw [Assembly.Compact.openStepResultEqInstrOfDecodeAt
      hPushValid hDecodePush hPc]
    unfold Assembly.Compact.Instr.openStepResult
    rw [hPushOpen]
    rfl
  have hCondition :
      (destination != EvmYul.UInt256.ofNat 0) = true := by
    exact
      TypedCfg.Preservation.uint256_bne_zero_of_ne
        destination hNonzero
  have hJumpiOpen :
      Assembly.Compact.Instr.jumpi.openStep pushed =
        .done (.ok branched) := by
    simp [Assembly.Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith,
      EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC,
      pushed, branched, hCondition]
  have hJumpiStep :
      Assembly.Compact.InteractionSemantics.openStepResult
          bytes pushed =
        .done (.ok (.running branched)) := by
    rw [Assembly.Compact.openStepResultEqInstrOfDecodeAt
      (by trivial) hDecodeJumpi hPushedPc]
    unfold Assembly.Compact.Instr.openStepResult
    rw [hJumpiOpen]
    rfl
  have hCaseStep :
      Assembly.Compact.InteractionSemantics.openStepResult
          bytes branched =
        .done (.ok (.running entered)) := by
    rw [Assembly.Compact.openStepResultEqInstrOfDecodeAt
      (by trivial) hDecodeCase hBranchedPc]
    rfl
  have hJumpStep :
      Assembly.Compact.InteractionSemantics.openStepResult
          bytes entered =
        .done (.ok (.running final)) := by
    rw [Assembly.Compact.openStepResultEqInstrOfDecodeAt
      (by trivial) hDecodeJump hEnteredPc]
    rfl
  refine ⟨final, ?_, rfl, rfl, ?_⟩
  · rw [show 4 = 3 + 1 by omega,
      Assembly.Compact.InteractionSemantics.openRunNResult_succ,
      hPushStep]
    change
      Assembly.Compact.InteractionSemantics.openRunNResult
          bytes 3 pushed =
        .done (.ok (.running final))
    rw [show 3 = 2 + 1 by omega,
      Assembly.Compact.InteractionSemantics.openRunNResult_succ,
      hJumpiStep]
    change
      Assembly.Compact.InteractionSemantics.openRunNResult
          bytes 2 branched =
        .done (.ok (.running final))
    rw [show 2 = 1 + 1 by omega,
      Assembly.Compact.InteractionSemantics.openRunNResult_succ,
      hCaseStep]
    change
      Assembly.Compact.InteractionSemantics.openRunNResult
          bytes 1 entered =
        .done (.ok (.running final))
    rw [show 1 = 0 + 1 by omega,
      Assembly.Compact.InteractionSemantics.openRunNResult_succ,
      hJumpStep]
    rfl
  · cases state
    rfl

theorem compact_rejected_return_tail
    {bytes : ByteArray}
    {branchPc branchWidth casePc : Nat}
    {state : EVMState} {suffix : List Word}
    (hPushValid :
      (Assembly.Compact.Instr.push branchWidth
        (EvmYul.UInt256.ofNat casePc)).Valid)
    (hDecodePush :
      Assembly.Compact.decodeAt bytes branchPc
        (.push branchWidth (EvmYul.UInt256.ofNat casePc)))
    (hDecodeJumpi :
      Assembly.Compact.decodeAt bytes
        (branchPc + branchWidth + 1) .jumpi)
    (hDecodeInvalid :
      Assembly.Compact.decodeAt bytes
        (branchPc + branchWidth + 2) (.prim .invalid))
    (hPc : state.pc = EvmYul.UInt256.ofNat branchPc)
    (hStack :
      state.stack =
        EvmYul.UInt256.ofNat 0 :: EvmYul.UInt256.ofNat 0 :: suffix) :
    Assembly.Compact.InteractionSemantics.openRunNResult
        bytes 4 state =
      .done (.error .InvalidInstruction) := by
  let pushed : EVMState :=
    state.replaceStackAndIncrPC
      (EvmYul.UInt256.ofNat casePc ::
        EvmYul.UInt256.ofNat 0 ::
          EvmYul.UInt256.ofNat 0 :: suffix)
      (pcΔ := branchWidth + 1)
  let fallen : EVMState :=
    pushed.replaceStackAndIncrPC
      (EvmYul.UInt256.ofNat 0 :: suffix)
  have hPushedPc :
      pushed.pc =
        EvmYul.UInt256.ofNat
          (branchPc + branchWidth + 1) := by
    simp [pushed, hPc,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC,
      Assembly.UInt256_ofNat_add,
      Nat.add_assoc]
  have hFallenPc :
      fallen.pc =
        EvmYul.UInt256.ofNat
          (branchPc + branchWidth + 2) := by
    simp [fallen, pushed, hPc,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC,
      Assembly.UInt256_ofNat_add,
      Nat.add_assoc]
  have hPushOpen :
      (Assembly.Compact.Instr.push branchWidth
          (EvmYul.UInt256.ofNat casePc)).openStep state =
        .done (.ok pushed) := by
    simp [Assembly.Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepPush,
      Assembly.Target.stepPushWith,
      EvmYul.Stack.push, pushed, hStack]
  have hPushStep :
      Assembly.Compact.InteractionSemantics.openStepResult
          bytes state =
        .done (.ok (.running pushed)) := by
    rw [Assembly.Compact.openStepResultEqInstrOfDecodeAt
      hPushValid hDecodePush hPc]
    unfold Assembly.Compact.Instr.openStepResult
    rw [hPushOpen]
    rfl
  have hCondition :
      (EvmYul.UInt256.ofNat 0 !=
        EvmYul.UInt256.ofNat 0) = false :=
    TypedCfg.Preservation.uint256_bne_zero_self
  have hJumpiOpen :
      Assembly.Compact.Instr.jumpi.openStep pushed =
        .done (.ok fallen) := by
    simp [Assembly.Compact.Instr.openStep,
      Assembly.InteractionSemantics.Target.openStepInstr,
      Assembly.Target.stepInstrWith,
      EvmYul.Stack.pop2,
      EvmYul.EVM.State.replaceStackAndIncrPC,
      EvmYul.EVM.State.incrPC,
      pushed, fallen, hCondition]
  have hJumpiStep :
      Assembly.Compact.InteractionSemantics.openStepResult
          bytes pushed =
        .done (.ok (.running fallen)) := by
    rw [Assembly.Compact.openStepResultEqInstrOfDecodeAt
      (by trivial) hDecodeJumpi hPushedPc]
    unfold Assembly.Compact.Instr.openStepResult
    rw [hJumpiOpen]
    rfl
  have hInvalidStep :
      Assembly.Compact.InteractionSemantics.openStepResult
          bytes fallen =
        .done (.error .InvalidInstruction) := by
    rw [Assembly.Compact.openStepResultEqInstrOfDecodeAt
      (by trivial) hDecodeInvalid hFallenPc]
    rfl
  rw [show 4 = 3 + 1 by omega,
    Assembly.Compact.InteractionSemantics.openRunNResult_succ,
    hPushStep]
  change
    Assembly.Compact.InteractionSemantics.openRunNResult
        bytes 3 pushed =
      .done (.error .InvalidInstruction)
  rw [show 3 = 2 + 1 by omega,
    Assembly.Compact.InteractionSemantics.openRunNResult_succ,
    hJumpiStep]
  change
    Assembly.Compact.InteractionSemantics.openRunNResult
        bytes 2 fallen =
      .done (.error .InvalidInstruction)
  rw [show 2 = 1 + 1 by omega,
    Assembly.Compact.InteractionSemantics.openRunNResult_succ,
    hInvalidStep]
  rfl

structure ReturnTailDecoding
    (bytes : ByteArray) (branchPc branchWidth casePc : Nat) : Prop where
  pushValid :
    (Assembly.Compact.Instr.push branchWidth
      (EvmYul.UInt256.ofNat casePc)).Valid
  decodePush :
    Assembly.Compact.decodeAt bytes branchPc
      (.push branchWidth (EvmYul.UInt256.ofNat casePc))
  decodeJumpi :
    Assembly.Compact.decodeAt bytes
      (branchPc + branchWidth + 1) .jumpi
  decodeInvalid :
    Assembly.Compact.decodeAt bytes
      (branchPc + branchWidth + 2) (.prim .invalid)
  decodeCase :
    Assembly.Compact.decodeAt bytes casePc .jumpdest
  decodeJump :
    Assembly.Compact.decodeAt bytes (casePc + 1) .jump

theorem returnTail_decoding_of_blocks
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {caseLabel : Assembly.Label}
    {sourcePc branchPc : Nat}
    {post : Assembly.Program}
    {blocks : List SourceBlock}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        artifact.pinnedPushPcs artifact.branchWidth artifact.labels
        ([ .jumpi caseLabel
         , .prim .invalid
         , .label caseLabel
         , .jumpDynamic
         ] ++ post)
        sourcePc branchPc blocks)
    (hSubset :
      ∀ block ∈ blocks, block ∈ artifact.blocks) :
    ∃ casePc,
      Assembly.Compact.lookupLabel? artifact.labels caseLabel =
          some casePc ∧
        casePc = branchPc + artifact.branchWidth + 3 ∧
          ReturnTailDecoding
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            branchPc
            artifact.branchWidth casePc := by
  have hArtifact :=
    ReturnAddressProbe.Compact.compile?_valid hCompile
  have hDecoding :=
    ReturnAddressProbe.Compact.compile?_decodingCorrect_with_suffix
      hCompile byteSuffix
  cases hValid with
  | @cons _ _ _ _ jumpiSize jumpiCode afterJumpi
      hJumpiSize hJumpiCode hAfterJumpi =>
      cases hLookup :
          Assembly.Compact.lookupLabel?
            artifact.labels caseLabel with
      | none =>
          simp [ReturnAddressProbe.Compact.emitSourceBlock?,
            ReturnAddressProbe.Compact.emitInstrRev?, hLookup]
            at hJumpiCode
      | some casePc =>
          by_cases hFits :
              Assembly.Compact.fitsWidth?
                  artifact.branchWidth casePc =
                true
          · simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
              ReturnAddressProbe.Compact.emitSourceBlock?,
              ReturnAddressProbe.Compact.emitInstrRev?,
              hLookup, hFits] at hJumpiSize hJumpiCode
            subst jumpiSize
            subst jumpiCode
            cases hAfterJumpi with
            | @cons _ _ _ _ invalidSize invalidCode afterInvalid
                hInvalidSize hInvalidCode hAfterInvalid =>
                simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
                  ReturnAddressProbe.Compact.emitSourceBlock?,
                  ReturnAddressProbe.Compact.emitInstrRev?]
                    at hInvalidSize hInvalidCode
                subst invalidSize
                subst invalidCode
                cases hAfterInvalid with
                | @cons _ _ _ _ labelSize labelCode afterLabel
                    hLabelSize hLabelCode hAfterLabel =>
                    simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
                      ReturnAddressProbe.Compact.emitSourceBlock?,
                      ReturnAddressProbe.Compact.emitInstrRev?]
                        at hLabelSize hLabelCode
                    subst labelSize
                    subst labelCode
                    cases hAfterLabel with
                    | @cons _ _ _ _ jumpSize jumpCode afterJump
                        hJumpSize hJumpCode hAfterJump =>
                        simp [
                          ReturnAddressProbe.Compact.sourceInstrSizeAt?,
                          ReturnAddressProbe.Compact.emitSourceBlock?,
                          ReturnAddressProbe.Compact.emitInstrRev?]
                            at hJumpSize hJumpCode
                        subst jumpSize
                        subst jumpCode
                        let jumpiBlock : SourceBlock :=
                          { sourcePc := sourcePc
                            compactPc := branchPc
                            sourceInstr := .jumpi caseLabel
                            code :=
                              [ { pc := branchPc
                                  instr :=
                                    .push artifact.branchWidth
                                      (EvmYul.UInt256.ofNat casePc) }
                              , { pc :=
                                    branchPc +
                                      artifact.branchWidth + 1
                                  instr := .jumpi }
                              ] }
                        let invalidBlock : SourceBlock :=
                          { sourcePc :=
                              sourcePc +
                                (Assembly.Instr.jumpi caseLabel).byteSize
                            compactPc :=
                              branchPc + artifact.branchWidth + 2
                            sourceInstr := .prim .invalid
                            code :=
                              [ { pc :=
                                    branchPc +
                                      artifact.branchWidth + 2
                                  instr := .prim .invalid }
                              ] }
                        let labelBlock : SourceBlock :=
                          { sourcePc :=
                              sourcePc +
                                (Assembly.Instr.jumpi caseLabel).byteSize +
                                (Assembly.Instr.prim .invalid).byteSize
                            compactPc :=
                              branchPc +
                                (artifact.branchWidth + 2) + 1
                            sourceInstr := .label caseLabel
                            code :=
                              [ { pc :=
                                    branchPc +
                                      (artifact.branchWidth + 2) + 1
                                  instr := .jumpdest }
                              ] }
                        let dynamicBlock : SourceBlock :=
                          { sourcePc :=
                              sourcePc +
                                (Assembly.Instr.jumpi caseLabel).byteSize +
                                (Assembly.Instr.prim .invalid).byteSize +
                                (Assembly.Instr.label caseLabel).byteSize
                            compactPc :=
                              branchPc +
                                (artifact.branchWidth + 2) + 1 + 1
                            sourceInstr := .jumpDynamic
                            code :=
                              [ { pc :=
                                    branchPc +
                                      (artifact.branchWidth + 2) + 1 + 1
                                  instr := .jump }
                              ] }
                        have hJumpiBlock :
                            jumpiBlock ∈ artifact.blocks := by
                          apply hSubset jumpiBlock
                          simp [jumpiBlock]
                        have hInvalidBlock :
                            invalidBlock ∈ artifact.blocks := by
                          apply hSubset invalidBlock
                          simp [invalidBlock, Nat.add_assoc]
                        have hLabelBlock :
                            labelBlock ∈ artifact.blocks := by
                          apply hSubset labelBlock
                          simp [labelBlock]
                        have hDynamicBlock :
                            dynamicBlock ∈ artifact.blocks := by
                          apply hSubset dynamicBlock
                          simp [dynamicBlock]
                        have hCaseLookup :=
                          hArtifact.labelsConsistent labelBlock
                            hLabelBlock caseLabel (by rfl)
                        have hCasePc :
                            casePc =
                              branchPc +
                                artifact.branchWidth + 3 := by
                          rw [hLookup] at hCaseLookup
                          have hEq :=
                            Option.some.inj hCaseLookup
                          simpa [labelBlock, Nat.add_assoc] using hEq
                        let pushLocated : Assembly.Compact.Located :=
                          { pc := branchPc
                            instr :=
                              .push artifact.branchWidth
                                (EvmYul.UInt256.ofNat casePc) }
                        let jumpiLocated : Assembly.Compact.Located :=
                          { pc :=
                              branchPc + artifact.branchWidth + 1
                            instr := .jumpi }
                        let invalidLocated : Assembly.Compact.Located :=
                          { pc :=
                              branchPc + artifact.branchWidth + 2
                            instr := .prim .invalid }
                        let caseLocated : Assembly.Compact.Located :=
                          { pc := casePc
                            instr := .jumpdest }
                        let jumpLocated : Assembly.Compact.Located :=
                          { pc := casePc + 1
                            instr := .jump }
                        have hPushMem :
                            pushLocated ∈ artifact.program.code :=
                          hArtifact.mem_program_of_mem_block
                            hJumpiBlock
                            (by simp [jumpiBlock, pushLocated])
                        have hJumpiMem :
                            jumpiLocated ∈ artifact.program.code :=
                          hArtifact.mem_program_of_mem_block
                            hJumpiBlock
                            (by simp [jumpiBlock, jumpiLocated])
                        have hInvalidMem :
                            invalidLocated ∈ artifact.program.code :=
                          hArtifact.mem_program_of_mem_block
                            hInvalidBlock
                            (by simp [invalidBlock, invalidLocated])
                        have hCaseMem :
                            caseLocated ∈ artifact.program.code := by
                          apply
                            hArtifact.mem_program_of_mem_block
                              hLabelBlock
                          simp [labelBlock, caseLocated,
                            hCasePc, Nat.add_assoc]
                        have hJumpMem :
                            jumpLocated ∈ artifact.program.code := by
                          apply
                            hArtifact.mem_program_of_mem_block
                              hDynamicBlock
                          simp [dynamicBlock, jumpLocated,
                            hCasePc, Nat.add_assoc]
                        refine
                          ⟨casePc, by simpa [hLookup], hCasePc,
                            { pushValid :=
                                (List.forall_iff_forall_mem.mp
                                  hArtifact.wellFormed.1)
                                  pushLocated hPushMem
                              decodePush :=
                                hDecoding.decodes pushLocated hPushMem
                              decodeJumpi :=
                                hDecoding.decodes jumpiLocated hJumpiMem
                              decodeInvalid :=
                                hDecoding.decodes invalidLocated hInvalidMem
                              decodeCase :=
                                hDecoding.decodes caseLocated hCaseMem
                              decodeJump :=
                                hDecoding.decodes jumpLocated hJumpMem }⟩
          · have hFitsFalse :
                Assembly.Compact.fitsWidth?
                    artifact.branchWidth casePc =
                  false :=
              Bool.eq_false_of_not_eq_true hFits
            simp [ReturnAddressProbe.Compact.emitSourceBlock?,
              ReturnAddressProbe.Compact.emitInstrRev?,
              hLookup, hFitsFalse] at hJumpiCode

theorem lateReturnPhysicalSuffix_openRunNResult
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {first : ReturnSite} {rest : List ReturnSite}
    {sourcePc compactPc : Nat}
    {post : Assembly.Program}
    {blocks : List SourceBlock}
    {compactCode : List Assembly.Compact.Instr}
    {target source : EVMState}
    {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        artifact.pinnedPushPcs artifact.branchWidth artifact.labels
        ((LateReturnProbe.Terminator.selectionCode (first :: rest) ++
            Assembly.StackShuffle.removeBuriedUnder 1 ++
            [Assembly.StackShuffle.dupInstr 1]) ++
          ([ .jumpi first.caseLabel
           , .prim .invalid
           , .label first.caseLabel
           , .jumpDynamic
           ] ++ post))
        sourcePc compactPc blocks)
    (hSubset :
      ∀ block ∈ blocks, block ∈ artifact.blocks)
    (hResolved :
      resolvedStraightFrom?
          artifact.pinnedPushPcs artifact.branchWidth artifact.labels
          (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
            Assembly.StackShuffle.removeBuriedUnder 1 ++
            [Assembly.StackShuffle.dupInstr 1])
          sourcePc =
        some compactCode)
    (hTargetPc :
      target.pc = EvmYul.UInt256.ofNat compactPc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (hSourceStack : source.stack = token :: suffix)
    (hNonzero :
      LateReturnPreservation.selectedAddressSum
          (Assembly.Compact.lookupLabel? artifact.labels)
          token (first :: rest) ≠
        EvmYul.UInt256.ofNat 0) :
    ∃ final,
      Assembly.Compact.InteractionSemantics.openRunNResult
          (Assembly.Bytecode.ofList
            (artifact.bytes.toList ++ byteSuffix))
          (compactCode.length + 4) target =
        .done (.ok (.running final)) ∧
      final.pc =
        LateReturnPreservation.selectedAddressSum
          (Assembly.Compact.lookupLabel? artifact.labels)
          token (first :: rest) ∧
      final.stack = suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl
          { source with stack := suffix } := by
  have hArtifact :=
    ReturnAddressProbe.Compact.compile?_valid hCompile
  have hDecoding :=
    ReturnAddressProbe.Compact.compile?_decodingCorrect_with_suffix
      hCompile byteSuffix
  have hStraightDecoding :=
    ReturnAddressProbe.Compact.BlocksValidFrom.resolved_prefix_decoding
      (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
        Assembly.StackShuffle.removeBuriedUnder 1 ++
        [Assembly.StackShuffle.dupInstr 1])
      hValid hResolved hSubset hArtifact.blockCode
      hArtifact.wellFormed.1 hArtifact.wellFormed.2.2.2
      hDecoding
      (resolvedStraightFrom?_sequential hResolved)
  obtain ⟨selected, hSelectedRun, hSelectedPc,
      hSelectedStack, hSelectedRuntime⟩ :=
    selectionAndTest_straight_openRunNResult
      hResolved hStraightDecoding hTargetPc hRuntime
      token suffix hSourceStack
  obtain ⟨tailBlocks, hTailValid, hTailSubset⟩ :=
    ReturnAddressProbe.Compact.BlocksValidFrom.resolved_prefix_suffix
      (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
        Assembly.StackShuffle.removeBuriedUnder 1 ++
        [Assembly.StackShuffle.dupInstr 1])
      hValid hResolved
  have hTailGlobal :
      ∀ block ∈ tailBlocks, block ∈ artifact.blocks := by
    intro block hBlock
    exact hSubset block (hTailSubset block hBlock)
  obtain ⟨casePc, hCaseLookup, hCasePc, hTailDecoding⟩ :=
    returnTail_decoding_of_blocks
      hCompile byteSuffix hTailValid hTailGlobal
  let destination :=
    LateReturnPreservation.selectedAddressSum
      (Assembly.Compact.lookupLabel? artifact.labels)
      token (first :: rest)
  have hSelectedPc' :
      selected.pc =
        EvmYul.UInt256.ofNat
          (straightEndPc compactPc compactCode) :=
    hSelectedPc
  have hSelectedStack' :
      selected.stack = destination :: destination :: suffix := by
    simpa [destination] using hSelectedStack
  obtain ⟨final, hTailRun, hFinalPc, hFinalStack,
      hFinalRuntime⟩ :=
    compact_taken_return_tail
      hTailDecoding.pushValid
      hTailDecoding.decodePush
      hTailDecoding.decodeJumpi
      hTailDecoding.decodeCase
      hTailDecoding.decodeJump
      hSelectedPc' hSelectedStack'
      (by simpa [destination] using hNonzero)
  refine ⟨final, ?_, ?_, hFinalStack, ?_⟩
  · rw [
      Assembly.Compact.InteractionSemantics.openRunNResult_add,
      hSelectedRun]
    change
      Assembly.Compact.InteractionSemantics.openRunNResult
          (Assembly.Bytecode.ofList
            (artifact.bytes.toList ++ byteSuffix))
          4 selected =
        .done (.ok (.running final))
    exact hTailRun
  · simpa [destination] using hFinalPc
  · calc
      Assembly.eraseRuntimeControl final =
          Assembly.eraseRuntimeControl
            { selected with stack := suffix } :=
        hFinalRuntime
      _ =
          Assembly.eraseRuntimeControl
            { source with stack := suffix } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := selected)
            (right :=
              { source with
                stack :=
                  destination :: destination :: suffix })
            (stack := suffix)
            (by simpa [destination] using hSelectedRuntime)

theorem lateReturnPhysicalSuffix_rejected_openRunNResult
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {first : ReturnSite} {rest : List ReturnSite}
    {sourcePc compactPc : Nat}
    {post : Assembly.Program}
    {blocks : List SourceBlock}
    {compactCode : List Assembly.Compact.Instr}
    {target source : EVMState}
    {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        artifact.pinnedPushPcs artifact.branchWidth artifact.labels
        ((LateReturnProbe.Terminator.selectionCode (first :: rest) ++
            Assembly.StackShuffle.removeBuriedUnder 1 ++
            [Assembly.StackShuffle.dupInstr 1]) ++
          ([ .jumpi first.caseLabel
           , .prim .invalid
           , .label first.caseLabel
           , .jumpDynamic
           ] ++ post))
        sourcePc compactPc blocks)
    (hSubset :
      ∀ block ∈ blocks, block ∈ artifact.blocks)
    (hResolved :
      resolvedStraightFrom?
          artifact.pinnedPushPcs artifact.branchWidth artifact.labels
          (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
            Assembly.StackShuffle.removeBuriedUnder 1 ++
            [Assembly.StackShuffle.dupInstr 1])
          sourcePc =
        some compactCode)
    (hTargetPc :
      target.pc = EvmYul.UInt256.ofNat compactPc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (hSourceStack : source.stack = token :: suffix)
    (hZero :
      LateReturnPreservation.selectedAddressSum
          (Assembly.Compact.lookupLabel? artifact.labels)
          token (first :: rest) =
        EvmYul.UInt256.ofNat 0) :
    Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        (compactCode.length + 4) target =
      .done (.error .InvalidInstruction) := by
  have hArtifact :=
    ReturnAddressProbe.Compact.compile?_valid hCompile
  have hDecoding :=
    ReturnAddressProbe.Compact.compile?_decodingCorrect_with_suffix
      hCompile byteSuffix
  have hStraightDecoding :=
    ReturnAddressProbe.Compact.BlocksValidFrom.resolved_prefix_decoding
      (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
        Assembly.StackShuffle.removeBuriedUnder 1 ++
        [Assembly.StackShuffle.dupInstr 1])
      hValid hResolved hSubset hArtifact.blockCode
      hArtifact.wellFormed.1 hArtifact.wellFormed.2.2.2
      hDecoding
      (resolvedStraightFrom?_sequential hResolved)
  obtain ⟨selected, hSelectedRun, hSelectedPc,
      hSelectedStack, _hSelectedRuntime⟩ :=
    selectionAndTest_straight_openRunNResult
      hResolved hStraightDecoding hTargetPc hRuntime
      token suffix hSourceStack
  obtain ⟨tailBlocks, hTailValid, hTailSubset⟩ :=
    ReturnAddressProbe.Compact.BlocksValidFrom.resolved_prefix_suffix
      (LateReturnProbe.Terminator.selectionCode (first :: rest) ++
        Assembly.StackShuffle.removeBuriedUnder 1 ++
        [Assembly.StackShuffle.dupInstr 1])
      hValid hResolved
  have hTailGlobal :
      ∀ block ∈ tailBlocks, block ∈ artifact.blocks := by
    intro block hBlock
    exact hSubset block (hTailSubset block hBlock)
  obtain ⟨casePc, _hCaseLookup, _hCasePc, hTailDecoding⟩ :=
    returnTail_decoding_of_blocks
      hCompile byteSuffix hTailValid hTailGlobal
  have hSelectedStack' :
      selected.stack =
        EvmYul.UInt256.ofNat 0 ::
          EvmYul.UInt256.ofNat 0 :: suffix := by
    simpa [hZero] using hSelectedStack
  have hTailRun :=
    compact_rejected_return_tail
      hTailDecoding.pushValid
      hTailDecoding.decodePush
      hTailDecoding.decodeJumpi
      hTailDecoding.decodeInvalid
      hSelectedPc hSelectedStack'
  rw [
    Assembly.Compact.InteractionSemantics.openRunNResult_add,
    hSelectedRun]
  exact hTailRun

/--
Instructions whose compact execution preserves ordinary runtime data at the
next source boundary.  Late return materialisation deliberately handles
`pushLabel` and `jumpDynamic` only as one dispatcher macro.
-/
def Ordinary : Assembly.Instr → Prop
  | .pushLabel _ | .jumpDynamic => False
  | _ => True

def ordinaryFuel : Assembly.Instr → Nat
  | .label _ | .prim _ | .push _ => 1
  | .jump _ | .jumpi _ => 2
  | .pushLabel _ | .jumpDynamic => 0

def BoundaryStateRel (artifact : Artifact)
    (target source : EVMState) : Prop :=
  Assembly.Compact.BoundaryStateRel artifact.asCompact target source

abbrev BoundaryOutcomeRel (artifact : Artifact) :=
  Assembly.Compact.BoundaryOutcomeRel artifact.asCompact

/--
One ordinary source instruction is simulated by its checked custom compact
block.  The theorem is intentionally unavailable for symbolic address pushes
and dynamic jumps; those are sound only under the dispatcher invariant.
-/
theorem sourceBlock_open_rel
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : SourceBlock}
    {targetState sourceState : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (suffix : List UInt8 := [])
    (hBlock : block ∈ artifact.blocks)
    (hOrdinary : Ordinary block.sourceInstr)
    (hTargetPc :
      targetState.pc = EvmYul.UInt256.ofNat block.compactPc)
    (hSourcePc :
      sourceState.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : Assembly.SameRuntimeData targetState sourceState) :
    ∃ targetFuel,
      targetFuel ≤ 2 ∧
        targetFuel = ordinaryFuel block.sourceInstr ∧
        Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ suffix))
            targetFuel targetState)
          (Assembly.InteractionSemantics.Source.openStepAtResult
            artifact.physicalSource block.sourcePc
            block.sourceInstr sourceState) := by
  have hArtifact :=
    ReturnAddressProbe.Compact.compile?_valid hCompile
  have hBlocks :=
    ReturnAddressProbe.Compact.compile?_blocksValid hCompile
  have hDecoding :=
    ReturnAddressProbe.Compact.compile?_decodingCorrect_with_suffix
      hCompile suffix
  obtain ⟨compactSize, hSize, hCode⟩ :=
    hBlocks.block_emit_of_mem hBlock
  have hNextBoundary := hBlocks.next_boundary hBlock hSize
  rw [hArtifact.blockCode] at hNextBoundary
  rcases block with ⟨sourcePc, compactPc, sourceInstr, code⟩
  cases sourceInstr with
  | label name =>
      simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
        ReturnAddressProbe.Compact.emitSourceBlock?,
        ReturnAddressProbe.Compact.emitInstrRev?] at hSize hCode
      subst compactSize
      subst code
      let located : Assembly.Compact.Located :=
        { pc := compactPc, instr := .jumpdest }
      have hMem : located ∈ artifact.program.code :=
        hArtifact.mem_program_of_mem_block hBlock
          (by simp [located])
      exact
        ⟨1, by omega, by simp [ordinaryFuel],
          Assembly.Compact.InteractionSemantics.openRunNResult_one_source_boundary_rel
            (artifact := artifact.asCompact)
            (sourcePc := sourcePc) (compactPc := compactPc)
            (sourceInstr := .label name)
            (compactInstr := .jumpdest)
            (by simpa [ReturnAddressProbe.Compact.Artifact.asCompact]
              using hNextBoundary)
            (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.label
              name)
            trivial
            ((List.forall_iff_forall_mem.mp
              hArtifact.wellFormed.2.2.2) located hMem)
            (hDecoding.decodes located hMem)
            hTargetPc hSourcePc hRel⟩
  | prim op =>
      simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
        ReturnAddressProbe.Compact.emitSourceBlock?,
        ReturnAddressProbe.Compact.emitInstrRev?] at hSize hCode
      subst compactSize
      subst code
      let located : Assembly.Compact.Located :=
        { pc := compactPc, instr := .prim op }
      have hMem : located ∈ artifact.program.code :=
        hArtifact.mem_program_of_mem_block hBlock
          (by simp [located])
      exact
        ⟨1, by omega, by simp [ordinaryFuel],
          Assembly.Compact.InteractionSemantics.openRunNResult_one_source_boundary_rel
            (artifact := artifact.asCompact)
            (sourcePc := sourcePc) (compactPc := compactPc)
            (sourceInstr := .prim op)
            (compactInstr := .prim op)
            (by simpa [ReturnAddressProbe.Compact.Artifact.asCompact]
              using hNextBoundary)
            (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.prim
              op)
            trivial
            ((List.forall_iff_forall_mem.mp
              hArtifact.wellFormed.2.2.2) located hMem)
            (hDecoding.decodes located hMem)
            hTargetPc hSourcePc hRel⟩
  | push value =>
      cases hWidth :
          Assembly.Compact.pushWidthAt?
            artifact.pinnedPushPcs sourcePc value with
      | none =>
          simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
            hWidth] at hSize
      | some width =>
          simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
            hWidth, ReturnAddressProbe.Compact.emitSourceBlock?,
            ReturnAddressProbe.Compact.emitInstrRev?] at hSize hCode
          subst compactSize
          subst code
          let located : Assembly.Compact.Located :=
            { pc := compactPc
              instr :=
                Assembly.Compact.pushInstrOfWidth width value }
          have hMem : located ∈ artifact.program.code :=
            hArtifact.mem_program_of_mem_block hBlock
              (by simp [located])
          exact
            ⟨1, by omega, by simp [ordinaryFuel],
              Assembly.Compact.InteractionSemantics.openRunNResult_one_source_boundary_rel
                (artifact := artifact.asCompact)
                (sourcePc := sourcePc) (compactPc := compactPc)
                (sourceInstr := .push value)
                (compactInstr :=
                  Assembly.Compact.pushInstrOfWidth width value)
                (by
                  simpa [
                    ReturnAddressProbe.Compact.Artifact.asCompact,
                    Assembly.Compact.pushInstrOfWidth_byteSize]
                    using hNextBoundary)
                (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.pushInstrOfWidth
                  hWidth)
                ((List.forall_iff_forall_mem.mp
                  hArtifact.wellFormed.1) located hMem)
                ((List.forall_iff_forall_mem.mp
                  hArtifact.wellFormed.2.2.2) located hMem)
                (hDecoding.decodes located hMem)
                hTargetPc hSourcePc hRel⟩
  | pushLabel target =>
      exact False.elim hOrdinary
  | jump target =>
      cases hDest :
          Assembly.Compact.lookupLabel? artifact.labels target with
      | none =>
          simp [ReturnAddressProbe.Compact.emitSourceBlock?,
            ReturnAddressProbe.Compact.emitInstrRev?, hDest] at hCode
      | some compactDest =>
          by_cases hFitsBool :
              Assembly.Compact.fitsWidth?
                artifact.branchWidth compactDest = true
          · simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
              ReturnAddressProbe.Compact.emitSourceBlock?,
              ReturnAddressProbe.Compact.emitInstrRev?,
              hDest, hFitsBool] at hSize hCode
            subst compactSize
            subst code
            obtain ⟨sourceDest, hSourceDest⟩ :=
              ReturnAddressProbe.Compact.compile?_physical_labelPc_of_lookup
                hCompile
                hDest
            let pushLocated : Assembly.Compact.Located :=
              { pc := compactPc
                instr :=
                  .push artifact.branchWidth
                    (EvmYul.UInt256.ofNat compactDest) }
            let jumpLocated : Assembly.Compact.Located :=
              { pc := compactPc + artifact.branchWidth + 1
                instr := .jump }
            have hPushMem :
                pushLocated ∈ artifact.program.code :=
              hArtifact.mem_program_of_mem_block hBlock
                (by simp [pushLocated, jumpLocated])
            have hJumpMem :
                jumpLocated ∈ artifact.program.code :=
              hArtifact.mem_program_of_mem_block hBlock
                (by simp [pushLocated, jumpLocated])
            have hLabelBoundary :=
              ReturnAddressProbe.Compact.compile?_label_boundary
                hCompile hSourceDest hDest
            exact
              ⟨2, by omega, by simp [ordinaryFuel],
                Assembly.Compact.InteractionSemantics.openRunNResult_push_jump_source_boundary_rel
                  (artifact := artifact.asCompact)
                  (by
                    simpa [
                      ReturnAddressProbe.Compact.Artifact.asCompact]
                      using hLabelBoundary)
                  hSourceDest
                  ((List.forall_iff_forall_mem.mp
                    hArtifact.wellFormed.1)
                    pushLocated hPushMem)
                  (hDecoding.decodes pushLocated hPushMem)
                  (hDecoding.decodes jumpLocated hJumpMem)
                  hTargetPc hRel⟩
          · have hFitsFalse :
                Assembly.Compact.fitsWidth?
                    artifact.branchWidth compactDest =
                  false :=
              Bool.eq_false_of_not_eq_true hFitsBool
            simp [ReturnAddressProbe.Compact.emitSourceBlock?,
              ReturnAddressProbe.Compact.emitInstrRev?,
              hDest, hFitsFalse] at hCode
  | jumpi target =>
      cases hDest :
          Assembly.Compact.lookupLabel? artifact.labels target with
      | none =>
          simp [ReturnAddressProbe.Compact.emitSourceBlock?,
            ReturnAddressProbe.Compact.emitInstrRev?, hDest] at hCode
      | some compactDest =>
          by_cases hFitsBool :
              Assembly.Compact.fitsWidth?
                artifact.branchWidth compactDest = true
          · simp [ReturnAddressProbe.Compact.sourceInstrSizeAt?,
              ReturnAddressProbe.Compact.emitSourceBlock?,
              ReturnAddressProbe.Compact.emitInstrRev?,
              hDest, hFitsBool] at hSize hCode
            subst compactSize
            subst code
            obtain ⟨sourceDest, hSourceDest⟩ :=
              ReturnAddressProbe.Compact.compile?_physical_labelPc_of_lookup
                hCompile hDest
            let pushLocated : Assembly.Compact.Located :=
              { pc := compactPc
                instr :=
                  .push artifact.branchWidth
                    (EvmYul.UInt256.ofNat compactDest) }
            let jumpLocated : Assembly.Compact.Located :=
              { pc := compactPc + artifact.branchWidth + 1
                instr := .jumpi }
            have hPushMem :
                pushLocated ∈ artifact.program.code :=
              hArtifact.mem_program_of_mem_block hBlock
                (by simp [pushLocated, jumpLocated])
            have hJumpMem :
                jumpLocated ∈ artifact.program.code :=
              hArtifact.mem_program_of_mem_block hBlock
                (by simp [pushLocated, jumpLocated])
            have hTakenBoundary :=
              ReturnAddressProbe.Compact.compile?_label_boundary
                hCompile hSourceDest hDest
            exact
              ⟨2, by omega, by simp [ordinaryFuel],
                Assembly.Compact.InteractionSemantics.openRunNResult_push_jumpi_source_boundary_rel
                  (artifact := artifact.asCompact)
                  (by
                    simpa [
                      ReturnAddressProbe.Compact.Artifact.asCompact]
                      using hTakenBoundary)
                  (by
                    simpa [
                      ReturnAddressProbe.Compact.Artifact.asCompact,
                      Assembly.Instr.byteSize,
                      Assembly.Instr.jumpSize,
                      Nat.add_assoc]
                      using hNextBoundary)
                  hSourceDest
                  ((List.forall_iff_forall_mem.mp
                    hArtifact.wellFormed.1)
                    pushLocated hPushMem)
                  (hDecoding.decodes pushLocated hPushMem)
                  (hDecoding.decodes jumpLocated hJumpMem)
                  hTargetPc hSourcePc hRel⟩
          · have hFitsFalse :
                Assembly.Compact.fitsWidth?
                    artifact.branchWidth compactDest =
                  false :=
              Bool.eq_false_of_not_eq_true hFitsBool
            simp [ReturnAddressProbe.Compact.emitSourceBlock?,
              ReturnAddressProbe.Compact.emitInstrRev?,
              hDest, hFitsFalse] at hCode
  | jumpDynamic =>
      exact False.elim hOrdinary

namespace Preparation

def StateRel (sourceProgram : Assembly.Program) (artifact : Artifact)
    (target source : EVMState) : Prop :=
  Assembly.Compact.PreparationStateRel sourceProgram artifact.asCompact
    target source

abbrev OutcomeRel (sourceProgram : Assembly.Program) (artifact : Artifact) :=
  Assembly.Compact.PreparationOutcomeRel sourceProgram artifact.asCompact

theorem source_openStepResult_eq_block
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {state : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.sourcePc) :
    Assembly.InteractionSemantics.Source.openStepResult sourceProgram state =
      Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr state := by
  have hArtifact :=
    ReturnAddressProbe.Compact.compile?_valid hCompile
  have hPreparation :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  obtain ⟨pre, post, hSource, hBlockPc⟩ :=
    hPreparation.source_decompose_of_block_mem hBlock
  have hWholeFits := hArtifact.sourcePCFits
  rw [hSource] at hWholeFits ⊢
  have hPreFits :=
    (Assembly.Program.PCFitsFrom.of_append
      (pre := pre) (code := block.sourceInstr :: post) (post := [])
      (by simpa using hWholeFits)).start
  apply Assembly.InteractionPreservation.source_openStepResult_at_boundary
    hPreFits
  simpa [Assembly.Program.pcAfter, hBlockPc] using hPc

theorem target_openStepResult_eq_block
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {state : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep)
    (hPc : state.pc = EvmYul.UInt256.ofNat block.preparedPc) :
    Assembly.InteractionSemantics.Source.openStepResult
        artifact.physicalSource state =
      Assembly.InteractionSemantics.Source.openStepAtResult
        artifact.physicalSource block.preparedPc block.sourceInstr state := by
  have hArtifact :=
    ReturnAddressProbe.Compact.compile?_valid hCompile
  have hPreparation :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  obtain ⟨pre, post, hPrepared, hBlockPc⟩ :=
    hPreparation.prepared_decompose_of_keep hBlock hKeep
  have hWholeFits := hArtifact.physicalSourcePCFits
  rw [hPrepared] at hWholeFits ⊢
  have hPreFits :=
    (Assembly.Program.PCFitsFrom.of_append
      (pre := pre) (code := block.sourceInstr :: post) (post := [])
      (by simpa using hWholeFits)).start
  apply Assembly.InteractionPreservation.source_openStepResult_at_boundary
    hPreFits
  simpa [Assembly.Program.pcAfter, hBlockPc] using hPc

theorem simple_block_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep)
    (hSimple :
      Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
        block.sourceInstr)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (OutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hPreparation :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  have hNext := hPreparation.next_boundary hBlock
  have hTargetStep :=
    target_openStepResult_eq_block hCompile hBlock hKeep hTargetPc
  rw [Assembly.InteractionSemantics.Source.openRunNResult_one, hTargetStep]
  apply
    Assembly.Compact.runtimeRel_to_preparationRel
      (artifact := artifact.asCompact)
      (by
        simpa [ReturnAddressProbe.Compact.Artifact.asCompact] using hNext)
      (hSimple.openStepAtResult_runtimeRel
        artifact.physicalSource sourceProgram
        block.preparedPc block.sourcePc hRel)
  · simpa [Assembly.Compact.PreparationBlock.nextPreparedPc, hKeep,
      hTargetPc, Assembly.UInt256_ofNat_add] using
      hSimple.source_runningAt_next artifact.physicalSource
        block.preparedPc target
  · simpa [hSourcePc, Assembly.UInt256_ofNat_add] using
      hSimple.source_runningAt_next sourceProgram block.sourcePc source

theorem skip_label_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {name : Label} {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hInstr : block.sourceInstr = .label name)
    (hSkip : block.action = .skip)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (OutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 0 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hPreparation :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  have hNext := hPreparation.next_boundary hBlock
  rw [hInstr] at hNext ⊢
  rw [Assembly.InteractionSemantics.Source.openRunNResult_zero]
  apply
    Assembly.Compact.runtimeRel_to_preparationRel
      (artifact := artifact.asCompact)
      (by
        simpa [ReturnAddressProbe.Compact.Artifact.asCompact,
          Assembly.Compact.PreparationBlock.nextPreparedPc, hSkip]
          using hNext)
  · rw [
      (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.label name).openStepResult_eq
        sourceProgram block.sourcePc source]
    apply Simulation.Interaction.Rel.done
    apply Simulation.Interaction.ExceptRel.ok
    exact
      Assembly.SameRuntimeData.with_pc_right
        (source.pc + EvmYul.UInt256.ofNat 1) hRel
  · exact .done hTargetPc
  · simpa [hSourcePc, Assembly.UInt256_ofNat_add,
      Assembly.Instr.byteSize] using
      (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.label name).source_runningAt_next
        sourceProgram block.sourcePc source

theorem skip_jump_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {label : Label} {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hInstr : block.sourceInstr = .jump label)
    (hSkip : block.action = .skip)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (OutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 0 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hSafe :=
    ReturnAddressProbe.Compact.compile?_preparationSafe
      hCompile block hBlock
  unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
  rw [hSkip, hInstr] at hSafe
  change ∃ sourceDest,
    sourceProgram.labelPc label = some sourceDest ∧
      Assembly.Compact.preparationTargetPc? artifact.preparation
          sourceProgram.byteLength artifact.physicalSource.byteLength
          sourceDest =
        some block.preparedPc at hSafe
  obtain ⟨sourceDest, hSourceDest, hLookup⟩ := hSafe
  have hBoundary :=
    Assembly.Compact.preparationBoundaryPair_of_targetPc? hLookup
  rw [hInstr, Assembly.InteractionSemantics.Source.openRunNResult_zero]
  apply
    Assembly.Compact.runtimeRel_to_preparationRel
      (artifact := artifact.asCompact)
      (by
        simpa [ReturnAddressProbe.Compact.Artifact.asCompact]
          using hBoundary)
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt
      Assembly.Source.stepAt
    simp [hSourceDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done (.ok
      (Assembly.SameRuntimeData.with_pc_right
        (EvmYul.UInt256.ofNat sourceDest) hRel))
  · exact .done hTargetPc
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt
      Assembly.Source.stepAt
    simp [hSourceDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done rfl

theorem keep_jump_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {label : Label} {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hInstr : block.sourceInstr = .jump label)
    (hKeep : block.action = .keep)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (OutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hSafe :=
    ReturnAddressProbe.Compact.compile?_preparationSafe
      hCompile block hBlock
  unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
  rw [hKeep, hInstr] at hSafe
  change ∃ sourceDest preparedDest,
    sourceProgram.labelPc label = some sourceDest ∧
      artifact.physicalSource.labelPc label = some preparedDest ∧
        Assembly.Compact.preparationTargetPc? artifact.preparation
            sourceProgram.byteLength artifact.physicalSource.byteLength
            sourceDest =
          some preparedDest at hSafe
  obtain
      ⟨sourceDest, preparedDest, hSourceDest, hPreparedDest, hLookup⟩ :=
    hSafe
  have hBoundary :=
    Assembly.Compact.preparationBoundaryPair_of_targetPc? hLookup
  have hTargetStep :=
    target_openStepResult_eq_block hCompile hBlock hKeep hTargetPc
  rw [hInstr] at hTargetStep
  rw [hInstr, Assembly.InteractionSemantics.Source.openRunNResult_one,
    hTargetStep]
  apply
    Assembly.Compact.runtimeRel_to_preparationRel
      (artifact := artifact.asCompact)
      (by
        simpa [ReturnAddressProbe.Compact.Artifact.asCompact]
          using hBoundary)
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt
      Assembly.Source.stepAt
    simp [hSourceDest, hPreparedDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done (Simulation.Interaction.ExceptRel.ok
      (Assembly.SameRuntimeData.with_pc_right
        (EvmYul.UInt256.ofNat sourceDest)
        (Assembly.SameRuntimeData.with_pc_left
          (EvmYul.UInt256.ofNat preparedDest) hRel)))
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt
      Assembly.Source.stepAt
    simp [hPreparedDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done rfl
  · unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt
      Assembly.Source.stepAt
    simp [hSourceDest, Assembly.Source.jumpPc,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind]
    exact .done rfl

theorem keep_jumpi_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {label : Label} {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hInstr : block.sourceInstr = .jumpi label)
    (hKeep : block.action = .keep)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (OutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hSafe :=
    ReturnAddressProbe.Compact.compile?_preparationSafe
      hCompile block hBlock
  unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
  rw [hKeep, hInstr] at hSafe
  change ∃ sourceDest preparedDest,
    sourceProgram.labelPc label = some sourceDest ∧
      artifact.physicalSource.labelPc label = some preparedDest ∧
        Assembly.Compact.preparationTargetPc? artifact.preparation
            sourceProgram.byteLength artifact.physicalSource.byteLength
            sourceDest =
          some preparedDest at hSafe
  obtain
      ⟨sourceDest, preparedDest, hSourceDest, hPreparedDest, hLookup⟩ :=
    hSafe
  have hTakenBoundary :=
    Assembly.Compact.preparationBoundaryPair_of_targetPc? hLookup
  have hPreparation :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  have hNextBoundary := hPreparation.next_boundary hBlock
  have hTargetStep :=
    target_openStepResult_eq_block hCompile hBlock hKeep hTargetPc
  rw [hInstr] at hTargetStep hNextBoundary ⊢
  rw [Assembly.InteractionSemantics.Source.openRunNResult_one, hTargetStep]
  have hStack := Assembly.SameRuntimeData.stack_eq hRel
  have hRuntime :
      Simulation.Interaction.Rel Assembly.Compact.RuntimeOutcomeRel
        (Assembly.InteractionSemantics.Source.openStepAtResult
          artifact.physicalSource block.preparedPc (.jumpi label) target)
        (Assembly.InteractionSemantics.Source.openStepAtResult
          sourceProgram block.sourcePc (.jumpi label) source) := by
    unfold Assembly.InteractionSemantics.Source.openStepAtResult
      Assembly.InteractionSemantics.Source.openStepAt
      Assembly.Source.stepAt
    simp only [hSourceDest, hPreparedDest, Option.elim_some,
      Assembly.Instr.haltKind?, Simulation.Interaction.bind_done_ok]
    rw [hStack]
    cases hSourceStack : source.stack with
    | nil =>
        simp [hSourceStack, EvmYul.Stack.pop]
        exact .done (.error rfl)
    | cons cond stack =>
        simp [hSourceStack, EvmYul.Stack.pop]
        apply Simulation.Interaction.Rel.done
        apply Simulation.Interaction.ExceptRel.ok
        exact
          Assembly.SameRuntimeData.with_pc_right
            (if cond != EvmYul.UInt256.ofNat 0 then
              EvmYul.UInt256.ofNat sourceDest
            else Assembly.Source.jumpiFallthroughPc source)
            (Assembly.SameRuntimeData.with_pc_left
              (if cond != EvmYul.UInt256.ofNat 0 then
                EvmYul.UInt256.ofNat preparedDest
              else Assembly.Source.jumpiFallthroughPc target)
              (Assembly.SameRuntimeData.replaceStack
                (targetStack := stack) (sourceStack := stack) hRel rfl))
  cases hSourceStack : source.stack with
  | nil =>
      apply
        Assembly.Compact.runtimeRel_to_preparationRel
          (artifact := artifact.asCompact)
          (by
            simpa [ReturnAddressProbe.Compact.Artifact.asCompact,
              Assembly.Compact.PreparationBlock.nextPreparedPc, hKeep,
              hInstr] using hNextBoundary)
          hRuntime
      · unfold Assembly.InteractionSemantics.Source.openStepAtResult
          Assembly.InteractionSemantics.Source.openStepAt
          Assembly.Source.stepAt
        simp [hPreparedDest, hStack, hSourceStack,
          Assembly.Instr.haltKind?, EvmYul.Stack.pop]
        exact .done trivial
      · unfold Assembly.InteractionSemantics.Source.openStepAtResult
          Assembly.InteractionSemantics.Source.openStepAt
          Assembly.Source.stepAt
        simp [hSourceDest, hSourceStack,
          Assembly.Instr.haltKind?, EvmYul.Stack.pop]
        exact .done trivial
  | cons cond stack =>
      by_cases hCond : (cond != EvmYul.UInt256.ofNat 0) = true
      · apply
          Assembly.Compact.runtimeRel_to_preparationRel
            (artifact := artifact.asCompact)
            (by
              simpa [ReturnAddressProbe.Compact.Artifact.asCompact]
                using hTakenBoundary)
            hRuntime
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt
            Assembly.Source.stepAt
          simp [hPreparedDest, hStack, hSourceStack, hCond,
            Assembly.Instr.haltKind?, EvmYul.Stack.pop]
          exact .done (by simp [Assembly.Compact.RunningAt, hCond])
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt
            Assembly.Source.stepAt
          simp [hSourceDest, hSourceStack, hCond,
            Assembly.Instr.haltKind?, EvmYul.Stack.pop]
          exact .done (by simp [Assembly.Compact.RunningAt, hCond])
      · apply
          Assembly.Compact.runtimeRel_to_preparationRel
            (artifact := artifact.asCompact)
            (by
              simpa [ReturnAddressProbe.Compact.Artifact.asCompact,
                Assembly.Compact.PreparationBlock.nextPreparedPc, hKeep,
                hInstr] using hNextBoundary)
            hRuntime
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt
            Assembly.Source.stepAt
          simp [hPreparedDest, hStack, hSourceStack, hCond,
            Assembly.Source.jumpiFallthroughPc,
            Assembly.Instr.byteSize, Assembly.Instr.jumpSize,
            Assembly.Instr.push32Size, Assembly.Instr.haltKind?,
            EvmYul.Stack.pop, hTargetPc,
            Assembly.UInt256_ofNat_add,
            Assembly.UInt256_add_assoc, Nat.add_assoc]
          exact .done (by simp [Assembly.Compact.RunningAt, hCond])
        · unfold Assembly.InteractionSemantics.Source.openStepAtResult
            Assembly.InteractionSemantics.Source.openStepAt
            Assembly.Source.stepAt
          simp [hSourceDest, hSourceStack, hCond,
            Assembly.Source.jumpiFallthroughPc,
            Assembly.Instr.byteSize, Assembly.Instr.jumpSize,
            Assembly.Instr.push32Size, Assembly.Instr.haltKind?,
            EvmYul.Stack.pop, hSourcePc,
            Assembly.UInt256_ofNat_add,
            Assembly.UInt256_add_assoc, Nat.add_assoc]
          exact .done (by simp [Assembly.Compact.RunningAt, hCond])

theorem block_open_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hOrdinary : Ordinary block.sourceInstr)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : Assembly.SameRuntimeData target source) :
    ∃ targetFuel,
      targetFuel ≤ 1 ∧
        Simulation.Interaction.Rel
          (OutcomeRel sourceProgram artifact)
          (Assembly.InteractionSemantics.Source.openRunNResult
            artifact.physicalSource targetFuel target)
          (Assembly.InteractionSemantics.Source.openStepAtResult
            sourceProgram block.sourcePc block.sourceInstr source) := by
  cases hAction : block.action with
  | keep =>
      cases hInstr : block.sourceInstr with
      | label name =>
          have hSimple :
              Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
                block.sourceInstr :=
            hInstr.symm ▸
              Assembly.Compact.InteractionSemantics.PreparationSimpleInstr.label
                name
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (simple_block_rel hCompile hBlock hAction hSimple
              hTargetPc hSourcePc hRel)
      | prim op =>
          have hNoPc : op ≠ .pc := by
            intro hPc
            subst op
            have hSafe :=
              ReturnAddressProbe.Compact.compile?_preparationSafe
                hCompile block hBlock
            unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
            rw [hAction, hInstr] at hSafe
            exact hSafe
          have hSimple :
              Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
                block.sourceInstr :=
            hInstr.symm ▸
              Assembly.Compact.InteractionSemantics.PreparationSimpleInstr.prim
                op hNoPc
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (simple_block_rel hCompile hBlock hAction hSimple
              hTargetPc hSourcePc hRel)
      | push value =>
          have hSimple :
              Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
                block.sourceInstr :=
            hInstr.symm ▸
              Assembly.Compact.InteractionSemantics.PreparationSimpleInstr.push
                value
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (simple_block_rel hCompile hBlock hAction hSimple
              hTargetPc hSourcePc hRel)
      | pushLabel label =>
          have hImpossible : False := by
            simpa [Ordinary, hInstr] using hOrdinary
          exact False.elim hImpossible
      | jump label =>
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (keep_jump_rel hCompile hBlock hInstr hAction hTargetPc hRel)
      | jumpi label =>
          refine ⟨1, by omega, ?_⟩
          simpa [hInstr] using
            (keep_jumpi_rel hCompile hBlock hInstr hAction
              hTargetPc hSourcePc hRel)
      | jumpDynamic =>
          have hImpossible : False := by
            simpa [Ordinary, hInstr] using hOrdinary
          exact False.elim hImpossible
  | skip =>
      cases hInstr : block.sourceInstr with
      | label name =>
          refine ⟨0, by omega, ?_⟩
          simpa [hInstr] using
            (skip_label_rel hCompile hBlock hInstr hAction
              hTargetPc hSourcePc hRel)
      | jump label =>
          refine ⟨0, by omega, ?_⟩
          simpa [hInstr] using
            (skip_jump_rel hCompile hBlock hInstr hAction
              hTargetPc hRel)
      | prim op | push op | pushLabel op | jumpi op =>
          have hSafe :=
            ReturnAddressProbe.Compact.compile?_preparationSafe
              hCompile block hBlock
          unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
          rw [hAction, hInstr] at hSafe
          exact False.elim hSafe
      | jumpDynamic =>
          have hSafe :=
            ReturnAddressProbe.Compact.compile?_preparationSafe
              hCompile block hBlock
          unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
          rw [hAction, hInstr] at hSafe
          exact False.elim hSafe

theorem keep_block_open_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep)
    (hOrdinary : Ordinary block.sourceInstr)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (OutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 1 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  cases hInstr : block.sourceInstr with
  | label name =>
      have hSimple :
          Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
            block.sourceInstr :=
        hInstr.symm ▸
          Assembly.Compact.InteractionSemantics.PreparationSimpleInstr.label
            name
      simpa [hInstr] using
        (simple_block_rel hCompile hBlock hKeep hSimple
          hTargetPc hSourcePc hRel)
  | prim op =>
      have hNoPc : op ≠ .pc := by
        intro hPc
        subst op
        have hSafe :=
          ReturnAddressProbe.Compact.compile?_preparationSafe
            hCompile block hBlock
        unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
        rw [hKeep, hInstr] at hSafe
        exact hSafe
      have hSimple :
          Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
            block.sourceInstr :=
        hInstr.symm ▸
          Assembly.Compact.InteractionSemantics.PreparationSimpleInstr.prim
            op hNoPc
      simpa [hInstr] using
        (simple_block_rel hCompile hBlock hKeep hSimple
          hTargetPc hSourcePc hRel)
  | push value =>
      have hSimple :
          Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
            block.sourceInstr :=
        hInstr.symm ▸
          Assembly.Compact.InteractionSemantics.PreparationSimpleInstr.push
            value
      simpa [hInstr] using
        (simple_block_rel hCompile hBlock hKeep hSimple
          hTargetPc hSourcePc hRel)
  | pushLabel label =>
      have hImpossible : False := by
        simpa [Ordinary, hInstr] using hOrdinary
      exact False.elim hImpossible
  | jump label =>
      simpa [hInstr] using
        (keep_jump_rel hCompile hBlock hInstr hKeep hTargetPc hRel)
  | jumpi label =>
      simpa [hInstr] using
        (keep_jumpi_rel hCompile hBlock hInstr hKeep
          hTargetPc hSourcePc hRel)
  | jumpDynamic =>
      have hImpossible : False := by
        simpa [Ordinary, hInstr] using hOrdinary
      exact False.elim hImpossible

theorem skip_block_open_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hSkip : block.action = .skip)
    (hOrdinary : Ordinary block.sourceInstr)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hRel : Assembly.SameRuntimeData target source) :
    Simulation.Interaction.Rel
      (OutcomeRel sourceProgram artifact)
      (Assembly.InteractionSemantics.Source.openRunNResult
        artifact.physicalSource 0 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  cases hInstr : block.sourceInstr with
  | label name =>
      simpa [hInstr] using
        (skip_label_rel hCompile hBlock hInstr hSkip
          hTargetPc hSourcePc hRel)
  | jump label =>
      simpa [hInstr] using
        (skip_jump_rel hCompile hBlock hInstr hSkip hTargetPc hRel)
  | prim op | push op | pushLabel op | jumpi op =>
      have hSafe :=
        ReturnAddressProbe.Compact.compile?_preparationSafe
          hCompile block hBlock
      unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
      rw [hSkip, hInstr] at hSafe
      exact False.elim hSafe
  | jumpDynamic =>
      have hSafe :=
        ReturnAddressProbe.Compact.compile?_preparationSafe
          hCompile block hBlock
      unfold ReturnAddressProbe.Compact.PreparationBlockSafe at hSafe
      rw [hSkip, hInstr] at hSafe
      exact False.elim hSafe

theorem compact_block_of_keep
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep) :
    ∃ compactBlock,
      compactBlock ∈ artifact.blocks ∧
        compactBlock.sourcePc = block.preparedPc ∧
          compactBlock.sourceInstr = block.sourceInstr := by
  have hPreparation :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  obtain ⟨pre, post, hPrepared, hPreparedPc⟩ :=
    hPreparation.prepared_decompose_of_keep hBlock hKeep
  have hAt :
      artifact.physicalSource.instrAtPc block.preparedPc =
        some (block.preparedPc, block.sourceInstr) := by
    rw [hPrepared, hPreparedPc]
    unfold Assembly.Program.instrAtPc
    simpa using
      Assembly.Program.instrAtPcFrom_append_boundary_cons
        pre post block.sourceInstr 0
  exact
    ReturnAddressProbe.Compact.compile?_block_of_instrAtPc hCompile hAt

theorem ofNat_eq_of_lt
    {left right : Nat}
    (hLeft : left < EvmYul.UInt256.size)
    (hRight : right < EvmYul.UInt256.size)
    (hEq :
      EvmYul.UInt256.ofNat left = EvmYul.UInt256.ofNat right) :
    left = right := by
  have hToNat := congrArg EvmYul.UInt256.toNat hEq
  simpa [EvmYul.UInt256.toNat_ofNat_of_lt hLeft,
    EvmYul.UInt256.toNat_ofNat_of_lt hRight] using hToNat

theorem preparedPc_lt_size_of_keep
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep) :
    block.preparedPc < EvmYul.UInt256.size := by
  have hPreparation :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  obtain ⟨pre, post, hPrepared, hPreparedPc⟩ :=
    hPreparation.prepared_decompose_of_keep hBlock hKeep
  have hPreLt :
      pre.byteLength < artifact.physicalSource.byteLength := by
    rw [hPrepared]
    simp only [Assembly.Program.byteLength_append,
      Assembly.Program.byteLength_cons]
    have hInstrPos := Assembly.Instr.byteSize_pos block.sourceInstr
    omega
  have hWholeLt :=
    (ReturnAddressProbe.Compact.compile?_valid
      hCompile).physicalSourcePCFits.byteLength_lt
  rw [hPreparedPc]
  simpa using Nat.lt_trans hPreLt hWholeLt

theorem compactBoundarySourcePc_lt_size
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {sourcePc compactPc : Nat}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBoundary :
      Assembly.Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Assembly.Compact.Program.codeByteLength artifact.program.code)
        sourcePc compactPc) :
    sourcePc < EvmYul.UInt256.size := by
  have hWholeLt :=
    (ReturnAddressProbe.Compact.compile?_valid
      hCompile).physicalSourcePCFits.byteLength_lt
  rcases hBoundary with hBlock | hEnd
  · rcases hBlock with
      ⟨block, hMem, hSourcePc, _hCompactPc⟩
    have hBlocks :=
      ReturnAddressProbe.Compact.compile?_blocksValid hCompile
    obtain ⟨pre, post, hPhysical, hBlockPc⟩ :=
      hBlocks.decompose_of_block_mem hMem
    have hPreLt :
        pre.byteLength < artifact.physicalSource.byteLength := by
      rw [hPhysical]
      simp only [Assembly.Program.byteLength_append,
        Assembly.Program.byteLength_cons]
      have hInstrPos := Assembly.Instr.byteSize_pos block.sourceInstr
      omega
    rw [← hSourcePc, hBlockPc]
    simpa using Nat.lt_trans hPreLt hWholeLt
  · rw [hEnd.1]
    exact hWholeLt

theorem preparationBoundarySourcePc_lt_size
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {sourcePc preparedPc : Nat}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBoundary :
      Assembly.Compact.PreparationBoundaryPair artifact.preparation
        sourceProgram.byteLength artifact.physicalSource.byteLength
        sourcePc preparedPc) :
    sourcePc < EvmYul.UInt256.size := by
  have hWholeLt :=
    (ReturnAddressProbe.Compact.compile?_valid
      hCompile).sourcePCFits.byteLength_lt
  rcases hBoundary with hBlock | hEnd
  · rcases hBlock with
      ⟨block, hMem, hSourcePc, _hPreparedPc⟩
    have hPreparation :=
      ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
    obtain ⟨pre, post, hSource, hBlockPc⟩ :=
      hPreparation.source_decompose_of_block_mem hMem
    have hPreLt : pre.byteLength < sourceProgram.byteLength := by
      rw [hSource]
      simp only [Assembly.Program.byteLength_append,
        Assembly.Program.byteLength_cons]
      have hInstrPos := Assembly.Instr.byteSize_pos block.sourceInstr
      omega
    rw [← hSourcePc, hBlockPc]
    simpa using Nat.lt_trans hPreLt hWholeLt
  · rw [hEnd.1]
    exact hWholeLt

theorem preparedPc_eq_compactSourcePc_of_keep
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {compactSourcePc compactPc : Nat}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep)
    (hBoundary :
      Assembly.Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Assembly.Compact.Program.codeByteLength artifact.program.code)
        compactSourcePc compactPc)
    (hEq :
      EvmYul.UInt256.ofNat block.preparedPc =
        EvmYul.UInt256.ofNat compactSourcePc) :
    block.preparedPc = compactSourcePc :=
  ofNat_eq_of_lt
    (preparedPc_lt_size_of_keep hCompile hBlock hKeep)
    (compactBoundarySourcePc_lt_size hCompile hBoundary)
    hEq

theorem preparationBlock_preparedPc_unique
    {source prepared : Assembly.Program}
    {sourcePc preparedPc : Nat}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hValid :
      Assembly.Compact.PreparationBlocksValidFrom
        source prepared sourcePc preparedPc blocks)
    {left right : Assembly.Compact.PreparationBlock}
    (hLeft : left ∈ blocks)
    (hRight : right ∈ blocks)
    (hSource : left.sourcePc = right.sourcePc) :
    left.preparedPc = right.preparedPc := by
  induction hValid with
  | nil =>
      simp at hLeft
  | @keep instr sourceRest preparedRest sourcePc preparedPc blocks
      hRest ih =>
      simp only [List.mem_cons] at hLeft hRight
      cases hLeft with
      | inl hLeftHead =>
          subst left
          cases hRight with
          | inl hRightHead =>
              subst right
              rfl
          | inr hRightTail =>
              obtain ⟨pre, post, _hSourceRest, hRightPc⟩ :=
                hRest.source_decompose_of_block_mem hRightTail
              simp at hSource
              rw [hRightPc] at hSource
              have hInstrPos := Assembly.Instr.byteSize_pos instr
              omega
      | inr hLeftTail =>
          cases hRight with
          | inl hRightHead =>
              subst right
              obtain ⟨pre, post, _hSourceRest, hLeftPc⟩ :=
                hRest.source_decompose_of_block_mem hLeftTail
              simp at hSource
              rw [hLeftPc] at hSource
              have hInstrPos := Assembly.Instr.byteSize_pos instr
              omega
          | inr hRightTail =>
              exact ih hLeftTail hRightTail
  | @skip instr sourceRest prepared sourcePc preparedPc blocks hRest ih =>
      simp only [List.mem_cons] at hLeft hRight
      cases hLeft with
      | inl hLeftHead =>
          subst left
          cases hRight with
          | inl hRightHead =>
              subst right
              rfl
          | inr hRightTail =>
              obtain ⟨pre, post, _hSourceRest, hRightPc⟩ :=
                hRest.source_decompose_of_block_mem hRightTail
              simp at hSource
              rw [hRightPc] at hSource
              have hInstrPos := Assembly.Instr.byteSize_pos instr
              omega
      | inr hLeftTail =>
          cases hRight with
          | inl hRightHead =>
              subst right
              obtain ⟨pre, post, _hSourceRest, hLeftPc⟩ :=
                hRest.source_decompose_of_block_mem hLeftTail
              simp at hSource
              rw [hLeftPc] at hSource
              have hInstrPos := Assembly.Instr.byteSize_pos instr
              omega
          | inr hRightTail =>
              exact ih hLeftTail hRightTail

theorem sourceBlock_compactPc_unique
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {labels : Assembly.Compact.LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        pinnedPushPcs branchWidth labels source
        sourcePc compactPc blocks)
    {left right : SourceBlock}
    (hLeft : left ∈ blocks)
    (hRight : right ∈ blocks)
    (hSource : left.sourcePc = right.sourcePc) :
    left.compactPc = right.compactPc := by
  induction hValid with
  | nil =>
      simp at hLeft
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest ih =>
      simp only [List.mem_cons] at hLeft hRight
      cases hLeft with
      | inl hLeftHead =>
          subst left
          cases hRight with
          | inl hRightHead =>
              subst right
              rfl
          | inr hRightTail =>
              obtain ⟨pre, post, _hRest, hRightPc⟩ :=
                hRest.decompose_of_block_mem hRightTail
              simp at hSource
              rw [hRightPc] at hSource
              have hInstrPos := Assembly.Instr.byteSize_pos instr
              omega
      | inr hLeftTail =>
          cases hRight with
          | inl hRightHead =>
              subst right
              obtain ⟨pre, post, _hRest, hLeftPc⟩ :=
                hRest.decompose_of_block_mem hLeftTail
              simp at hSource
              rw [hLeftPc] at hSource
              have hInstrPos := Assembly.Instr.byteSize_pos instr
              omega
          | inr hRightTail =>
              exact ih hLeftTail hRightTail

theorem blocksValidFrom_initial_boundary
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {labels : Assembly.Compact.LabelTable}
    {source : Assembly.Program} {sourcePc compactPc : Nat}
    {blocks : List SourceBlock}
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        pinnedPushPcs branchWidth labels source
        sourcePc compactPc blocks) :
    Assembly.Compact.BoundaryPair blocks
      (sourcePc + source.byteLength)
      (compactPc +
        Assembly.Compact.Program.codeByteLength
          (Assembly.Compact.blocksCode blocks))
      sourcePc compactPc := by
  cases hValid with
  | nil sourcePc compactPc =>
      exact
        Or.inr
          ⟨by simp,
            by simp [Assembly.Compact.blocksCode,
              Assembly.Compact.Program.codeByteLength]⟩
  | @cons instr rest sourcePc compactPc compactSize code blocks
      hSize hCode hRest =>
      exact
        Or.inl
          ⟨{ sourcePc := sourcePc
             compactPc := compactPc
             sourceInstr := instr
             code := code },
            by simp⟩

theorem preparationBoundaryPair_preparedPc_unique
    {source prepared : Assembly.Program}
    {sourceStart preparedStart : Nat}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hValid :
      Assembly.Compact.PreparationBlocksValidFrom
        source prepared sourceStart preparedStart blocks)
    {query leftPrepared rightPrepared : Nat}
    (hLeft :
      Assembly.Compact.PreparationBoundaryPair blocks
        (sourceStart + source.byteLength)
        (preparedStart + prepared.byteLength)
        query leftPrepared)
    (hRight :
      Assembly.Compact.PreparationBoundaryPair blocks
        (sourceStart + source.byteLength)
        (preparedStart + prepared.byteLength)
        query rightPrepared) :
    leftPrepared = rightPrepared := by
  rcases hLeft with hLeftBlock | hLeftEnd
  · rcases hLeftBlock with
      ⟨left, hLeftMem, hLeftSource, hLeftPrepared⟩
    rcases hRight with hRightBlock | hRightEnd
    · rcases hRightBlock with
        ⟨right, hRightMem, hRightSource, hRightPrepared⟩
      have hPrepared :=
        preparationBlock_preparedPc_unique
          hValid hLeftMem hRightMem
          (hLeftSource.trans hRightSource.symm)
      rw [← hLeftPrepared, ← hRightPrepared]
      exact hPrepared
    · have hLeftDecompose :=
        hValid.source_decompose_of_block_mem hLeftMem
      obtain ⟨pre, post, _hSource, hLeftPc⟩ := hLeftDecompose
      have hPreLt : pre.byteLength < source.byteLength := by
        rw [_hSource]
        simp only [Assembly.Program.byteLength_append,
          Assembly.Program.byteLength_cons]
        have hInstrPos :=
          Assembly.Instr.byteSize_pos left.sourceInstr
        omega
      have hEq :
          sourceStart + pre.byteLength =
            sourceStart + source.byteLength :=
        hLeftPc.symm.trans (hLeftSource.trans hRightEnd.1)
      exact False.elim (by omega)
  · rcases hRight with hRightBlock | hRightEnd
    · rcases hRightBlock with
        ⟨right, hRightMem, hRightSource, hRightPrepared⟩
      obtain ⟨pre, post, hSource, hRightPc⟩ :=
        hValid.source_decompose_of_block_mem hRightMem
      have hPreLt : pre.byteLength < source.byteLength := by
        rw [hSource]
        simp only [Assembly.Program.byteLength_append,
          Assembly.Program.byteLength_cons]
        have hInstrPos :=
          Assembly.Instr.byteSize_pos right.sourceInstr
        omega
      have hEq :
          sourceStart + pre.byteLength =
            sourceStart + source.byteLength :=
        hRightPc.symm.trans (hRightSource.trans hLeftEnd.1)
      exact False.elim (by omega)
    · exact hLeftEnd.2.trans hRightEnd.2.symm

theorem boundaryPair_compactPc_unique
    {pinnedPushPcs : List Nat} {branchWidth : Nat}
    {labels : Assembly.Compact.LabelTable}
    {source : Assembly.Program} {sourceStart compactStart : Nat}
    {blocks : List SourceBlock} {compactEnd : Nat}
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        pinnedPushPcs branchWidth labels source
        sourceStart compactStart blocks)
    {query leftCompact rightCompact : Nat}
    (hLeft :
      Assembly.Compact.BoundaryPair blocks
        (sourceStart + source.byteLength) compactEnd
        query leftCompact)
    (hRight :
      Assembly.Compact.BoundaryPair blocks
        (sourceStart + source.byteLength) compactEnd
        query rightCompact) :
    leftCompact = rightCompact := by
  rcases hLeft with hLeftBlock | hLeftEnd
  · rcases hLeftBlock with
      ⟨left, hLeftMem, hLeftSource, hLeftCompact⟩
    rcases hRight with hRightBlock | hRightEnd
    · rcases hRightBlock with
        ⟨right, hRightMem, hRightSource, hRightCompact⟩
      have hCompact :=
        sourceBlock_compactPc_unique
          hValid hLeftMem hRightMem
          (hLeftSource.trans hRightSource.symm)
      rw [← hLeftCompact, ← hRightCompact]
      exact hCompact
    · obtain ⟨pre, post, hSource, hLeftPc⟩ :=
        hValid.decompose_of_block_mem hLeftMem
      have hPreLt : pre.byteLength < source.byteLength := by
        rw [hSource]
        simp only [Assembly.Program.byteLength_append,
          Assembly.Program.byteLength_cons]
        have hInstrPos :=
          Assembly.Instr.byteSize_pos left.sourceInstr
        omega
      have hEq :
          sourceStart + pre.byteLength =
            sourceStart + source.byteLength :=
        hLeftPc.symm.trans (hLeftSource.trans hRightEnd.1)
      exact False.elim (by omega)
  · rcases hRight with hRightBlock | hRightEnd
    · rcases hRightBlock with
        ⟨right, hRightMem, hRightSource, hRightCompact⟩
      obtain ⟨pre, post, hSource, hRightPc⟩ :=
        hValid.decompose_of_block_mem hRightMem
      have hPreLt : pre.byteLength < source.byteLength := by
        rw [hSource]
        simp only [Assembly.Program.byteLength_append,
          Assembly.Program.byteLength_cons]
        have hInstrPos :=
          Assembly.Instr.byteSize_pos right.sourceInstr
        omega
      have hEq :
          sourceStart + pre.byteLength =
            sourceStart + source.byteLength :=
        hRightPc.symm.trans (hRightSource.trans hLeftEnd.1)
      exact False.elim (by omega)
    · exact hLeftEnd.2.trans hRightEnd.2.symm

def CombinedOutcomeRel
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (targetDone sourceDone :
      Except Assembly.EVMException Assembly.StepResult) :
    Prop :=
  ∃ middleDone,
    BoundaryOutcomeRel artifact targetDone middleDone ∧
      OutcomeRel sourceProgram artifact middleDone sourceDone

def FullStateRel (sourceProgram : Assembly.Program) (artifact : Artifact)
    (target source : EVMState) : Prop :=
  ∃ sourcePc preparedPc compactSourcePc compactPc,
    Assembly.Compact.PreparationBoundaryPair artifact.preparation
        sourceProgram.byteLength artifact.physicalSource.byteLength
        sourcePc preparedPc ∧
      Assembly.Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Assembly.Compact.Program.codeByteLength artifact.program.code)
        compactSourcePc compactPc ∧
      EvmYul.UInt256.ofNat preparedPc =
        EvmYul.UInt256.ofNat compactSourcePc ∧
      source.pc = EvmYul.UInt256.ofNat sourcePc ∧
      target.pc = EvmYul.UInt256.ofNat compactPc ∧
      Assembly.SameRuntimeData target source

theorem FullStateRel.runtimeData
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {target source : EVMState}
    (hFull : FullStateRel sourceProgram artifact target source) :
    Assembly.SameRuntimeData target source := by
  rcases hFull with
    ⟨sourcePc, preparedPc, compactSourcePc, compactPc,
      hPreparationBoundary, hCompactBoundary, hPreparedWord,
      hSourcePc, hTargetPc, hRuntime⟩
  exact hRuntime

theorem FullStateRel.initial
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat 0)
    (hSourcePc : source.pc = EvmYul.UInt256.ofNat 0)
    (hRuntime : Assembly.SameRuntimeData target source) :
    FullStateRel sourceProgram artifact target source := by
  exact
    ⟨0, 0, 0, 0,
      by
        simpa using
          (ReturnAddressProbe.Compact.compile?_preparationBlocksValid
            hCompile).initial_boundary,
      ReturnAddressProbe.Compact.compile?_initial_boundary hCompile,
      rfl, hSourcePc, hTargetPc, hRuntime⟩

def FullStepResultRel
    (sourceProgram : Assembly.Program) (artifact : Artifact) :
    Assembly.StepResult → Assembly.StepResult → Prop
  | .running target, .running source =>
      FullStateRel sourceProgram artifact target source
  | .halted target, .halted source =>
      target.kind = source.kind ∧
        Assembly.SameRuntimeData target.state source.state ∧
          target.output = source.output
  | _, _ => False

abbrev FullOutcomeRel
    (sourceProgram : Assembly.Program) (artifact : Artifact) :
    Except Assembly.EVMException Assembly.StepResult →
      Except Assembly.EVMException Assembly.StepResult → Prop :=
  Simulation.Interaction.ExceptRel
    (fun targetError sourceError => targetError = sourceError)
    (FullStepResultRel sourceProgram artifact)

theorem combinedOutcomeRel_full
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {targetDone sourceDone :
      Except Assembly.EVMException Assembly.StepResult}
    (hRel :
      CombinedOutcomeRel sourceProgram artifact targetDone sourceDone) :
    FullOutcomeRel sourceProgram artifact targetDone sourceDone := by
  rcases hRel with ⟨middleDone, hTargetMiddle, hMiddleSource⟩
  cases hTargetMiddle with
  | error hTargetError =>
      cases hMiddleSource with
      | error hSourceError =>
          exact .error (hTargetError.trans hSourceError)
  | ok hTargetResult =>
      cases hMiddleSource with
      | ok hSourceResult =>
          rename_i targetResult middleResult sourceResult
          cases targetResult with
          | running target =>
              cases middleResult with
              | halted middle =>
                  simp [Assembly.Compact.BoundaryStepResultRel]
                    at hTargetResult
              | running middle =>
                  cases sourceResult with
                  | halted source =>
                      simp [Assembly.Compact.PreparationStepResultRel]
                        at hSourceResult
                  | running source =>
                      change BoundaryStateRel artifact target middle at hTargetResult
                      change StateRel sourceProgram artifact middle source at hSourceResult
                      rcases hTargetResult with
                        ⟨preparedPc, compactPc, hCompactBoundary,
                          hMiddlePc, hTargetPc, hTargetMiddleRuntime⟩
                      rcases hSourceResult with
                        ⟨sourcePc, preparedPc', hPreparationBoundary,
                          hSourcePc, hMiddlePc',
                          hMiddleSourceRuntime⟩
                      apply Simulation.Interaction.ExceptRel.ok
                      change FullStateRel sourceProgram artifact target source
                      exact
                        ⟨sourcePc, preparedPc', preparedPc, compactPc,
                          hPreparationBoundary, hCompactBoundary,
                          hMiddlePc'.symm.trans hMiddlePc,
                          hSourcePc, hTargetPc,
                          Assembly.SameRuntimeData.trans
                            hTargetMiddleRuntime
                            hMiddleSourceRuntime⟩
          | halted target =>
              cases middleResult with
              | running middle =>
                  simp [Assembly.Compact.BoundaryStepResultRel]
                    at hTargetResult
              | halted middle =>
                  cases sourceResult with
                  | running source =>
                      simp [Assembly.Compact.PreparationStepResultRel]
                        at hSourceResult
                  | halted source =>
                      apply Simulation.Interaction.ExceptRel.ok
                      change
                        target.kind = source.kind ∧
                          Assembly.SameRuntimeData target.state source.state ∧
                            target.output = source.output
                      rcases hTargetResult with
                        ⟨hTargetKind, hTargetRuntime, hTargetOutput⟩
                      rcases hSourceResult with
                        ⟨hSourceKind, hSourceRuntime, hSourceOutput⟩
                      exact
                        ⟨hTargetKind.trans hSourceKind,
                          Assembly.SameRuntimeData.trans
                            hTargetRuntime hSourceRuntime,
                          hTargetOutput.trans hSourceOutput⟩

theorem FullStateRel.active_of_terminal_succ
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {target source : EVMState} {fuel : Nat}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hFull : FullStateRel sourceProgram artifact target source)
    (hTerminal :
      Simulation.Interaction.AllDone
        Assembly.InteractionSemantics.Terminal
        (Assembly.InteractionSemantics.Source.openRunNResult
          sourceProgram (fuel + 1) source)) :
    ∃ block compactSourcePc compactPc,
      block ∈ artifact.preparation ∧
        source.pc = EvmYul.UInt256.ofNat block.sourcePc ∧
        EvmYul.UInt256.ofNat block.preparedPc =
          EvmYul.UInt256.ofNat compactSourcePc ∧
        Assembly.Compact.BoundaryPair artifact.blocks
          artifact.physicalSource.byteLength
          (Assembly.Compact.Program.codeByteLength artifact.program.code)
          compactSourcePc compactPc ∧
        target.pc = EvmYul.UInt256.ofNat compactPc ∧
        Assembly.SameRuntimeData target source := by
  rcases hFull with
    ⟨sourcePc, preparedPc, compactSourcePc, compactPc,
      hPreparationBoundary, hCompactBoundary, hPreparedEq,
      hSourcePc, hTargetPc, hRuntime⟩
  rcases hPreparationBoundary with hBlock | hEnd
  · rcases hBlock with
      ⟨block, hBlock, hBlockSource, hBlockPrepared⟩
    exact
      ⟨block, compactSourcePc, compactPc, hBlock,
        by simpa [hBlockSource] using hSourcePc,
        by simpa [hBlockPrepared] using hPreparedEq,
        hCompactBoundary, hTargetPc, hRuntime⟩
  · rcases hEnd with ⟨hSourceEnd, _hPreparedEnd⟩
    have hArtifact :=
      ReturnAddressProbe.Compact.compile?_valid hCompile
    have hToNat : source.pc.toNat = sourceProgram.byteLength := by
      rw [hSourcePc, hSourceEnd]
      exact hArtifact.sourcePCFits
    have hStep :
        Assembly.InteractionSemantics.Source.openStepResult
            sourceProgram source =
          .done (.error .InvalidInstruction) := by
      unfold Assembly.InteractionSemantics.Source.openStepResult
        Assembly.Source.stepResultWith
      rw [hToNat, Assembly.Compact.instrAtPc_end_eq_none]
      rfl
    rw [Assembly.InteractionSemantics.Source.openRunNResult_succ]
      at hTerminal
    have hPrefix := Simulation.Interaction.AllDone.bind_inv hTerminal
    rw [hStep] at hPrefix
    cases hPrefix with
    | done hDone => exact False.elim hDone

theorem FullStateRel.active_block
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {target source : EVMState}
    {block : Assembly.Compact.PreparationBlock}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hFull : FullStateRel sourceProgram artifact target source)
    (hBlock : block ∈ artifact.preparation)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat block.sourcePc) :
    ∃ compactSourcePc compactPc,
      EvmYul.UInt256.ofNat block.preparedPc =
          EvmYul.UInt256.ofNat compactSourcePc ∧
        Assembly.Compact.BoundaryPair artifact.blocks
          artifact.physicalSource.byteLength
          (Assembly.Compact.Program.codeByteLength artifact.program.code)
          compactSourcePc compactPc ∧
        target.pc = EvmYul.UInt256.ofNat compactPc ∧
        Assembly.SameRuntimeData target source := by
  rcases hFull with
    ⟨fullSourcePc, fullPreparedPc, compactSourcePc, compactPc,
      hPreparationBoundary, hCompactBoundary, hPreparedEq,
      hFullSourcePc, hTargetPc, hRuntime⟩
  have hFullSourceLt :=
    preparationBoundarySourcePc_lt_size
      hCompile hPreparationBoundary
  have hBlockBoundary :
      Assembly.Compact.PreparationBoundaryPair artifact.preparation
        sourceProgram.byteLength artifact.physicalSource.byteLength
        block.sourcePc block.preparedPc :=
    Or.inl ⟨block, hBlock, rfl, rfl⟩
  have hBlockSourceLt :=
    preparationBoundarySourcePc_lt_size hCompile hBlockBoundary
  have hSourceEq : fullSourcePc = block.sourcePc := by
    apply ofNat_eq_of_lt hFullSourceLt hBlockSourceLt
    exact hFullSourcePc.symm.trans hSourcePc
  subst fullSourcePc
  have hPreparationValid :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  have hPreparedPcEq : fullPreparedPc = block.preparedPc := by
    apply preparationBoundaryPair_preparedPc_unique hPreparationValid
    · simpa using hPreparationBoundary
    · simpa using hBlockBoundary
  subst fullPreparedPc
  exact
    ⟨compactSourcePc, compactPc, hPreparedEq,
      hCompactBoundary, hTargetPc, hRuntime⟩

def blockFuel (block : Assembly.Compact.PreparationBlock) : Nat :=
  match block.action with
  | .keep => ordinaryFuel block.sourceInstr
  | .skip => 0

theorem kept_ordinary_compact_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {target prepared source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hBlock : block ∈ artifact.preparation)
    (hKeep : block.action = .keep)
    (hOrdinary : Ordinary block.sourceInstr)
    (hTargetPc : ∃ compactBlock,
      compactBlock ∈ artifact.blocks ∧
        compactBlock.sourcePc = block.preparedPc ∧
          compactBlock.sourceInstr = block.sourceInstr ∧
            target.pc = EvmYul.UInt256.ofNat compactBlock.compactPc)
    (hPreparedPc :
      prepared.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hTargetPrepared : Assembly.SameRuntimeData target prepared)
    (hPreparedSource : Assembly.SameRuntimeData prepared source) :
    ∃ targetFuel,
      targetFuel ≤ 2 ∧
        targetFuel = ordinaryFuel block.sourceInstr ∧
        Simulation.Interaction.Rel
          (FullOutcomeRel sourceProgram artifact)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            targetFuel target)
          (Assembly.InteractionSemantics.Source.openStepAtResult
            sourceProgram block.sourcePc block.sourceInstr source) := by
  obtain
      ⟨compactBlock, hCompactBlock, hCompactSourcePc,
        hCompactInstr, hCompactPc⟩ :=
    hTargetPc
  have hCompactOrdinary : Ordinary compactBlock.sourceInstr := by
    simpa [hCompactInstr] using hOrdinary
  have hCompactSourceStatePc :
      prepared.pc =
        EvmYul.UInt256.ofNat compactBlock.sourcePc := by
    simpa [hCompactSourcePc] using hPreparedPc
  obtain ⟨targetFuel, hFuel, hFuelExact, hCompact⟩ :=
    sourceBlock_open_rel
      hCompile byteSuffix hCompactBlock hCompactOrdinary hCompactPc
      hCompactSourceStatePc hTargetPrepared
  have hPreparation :=
    keep_block_open_rel hCompile hBlock hKeep hOrdinary
      hPreparedPc hSourcePc hPreparedSource
  have hPreparedStep :=
    target_openStepResult_eq_block
      hCompile hBlock hKeep hPreparedPc
  rw [Assembly.InteractionSemantics.Source.openRunNResult_one,
    hPreparedStep] at hPreparation
  have hCompact' :
      Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
        (Assembly.Compact.InteractionSemantics.openRunNResult
          (Assembly.Bytecode.ofList
            (artifact.bytes.toList ++ byteSuffix))
          targetFuel target)
        (Assembly.InteractionSemantics.Source.openStepAtResult
          artifact.physicalSource block.preparedPc
          block.sourceInstr prepared) := by
    simpa [hCompactSourcePc, hCompactInstr] using hCompact
  refine
    ⟨targetFuel, hFuel,
      by simpa [hCompactInstr] using hFuelExact, ?_⟩
  apply Simulation.Interaction.Rel.mono
    (by
      simpa [CombinedOutcomeRel] using
        Simulation.Interaction.Rel.trans hCompact' hPreparation)
  intro targetDone sourceDone hDone
  exact combinedOutcomeRel_full hDone

theorem active_ordinary_compact_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {compactSourcePc compactPc : Nat}
    {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hBlock : block ∈ artifact.preparation)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hPreparedEq :
      EvmYul.UInt256.ofNat block.preparedPc =
        EvmYul.UInt256.ofNat compactSourcePc)
    (hCompactBoundary :
      Assembly.Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Assembly.Compact.Program.codeByteLength artifact.program.code)
        compactSourcePc compactPc)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat compactPc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (hOrdinary : Ordinary block.sourceInstr) :
    ∃ targetFuel,
      targetFuel ≤ 2 ∧
        targetFuel = blockFuel block ∧
        Simulation.Interaction.Rel
          (FullOutcomeRel sourceProgram artifact)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            targetFuel target)
          (Assembly.InteractionSemantics.Source.openStepAtResult
            sourceProgram block.sourcePc block.sourceInstr source) := by
  let prepared : EVMState :=
    { source with
      pc := EvmYul.UInt256.ofNat block.preparedPc }
  have hPreparedPc :
      prepared.pc = EvmYul.UInt256.ofNat block.preparedPc := rfl
  have hTargetPrepared :
      Assembly.SameRuntimeData target prepared := by
    exact Assembly.SameRuntimeData.with_pc_right
      (EvmYul.UInt256.ofNat block.preparedPc) hRuntime
  have hPreparedSource :
      Assembly.SameRuntimeData prepared source := by
    exact Assembly.SameRuntimeData.with_pc_left
      (EvmYul.UInt256.ofNat block.preparedPc)
      (Assembly.SameRuntimeData.refl source)
  cases hAction : block.action with
  | keep =>
      have hPreparedPcEq :
          block.preparedPc = compactSourcePc :=
        preparedPc_eq_compactSourcePc_of_keep
          hCompile hBlock hAction hCompactBoundary hPreparedEq
      rcases hCompactBoundary with hCompactBlock | hCompactEnd
      · rcases hCompactBlock with
          ⟨compactBlock, hCompactBlock, hCompactSourcePc,
            hCompactPc⟩
        have hCompactSourcePc' :
            compactBlock.sourcePc = block.preparedPc := by
          calc
            compactBlock.sourcePc = compactSourcePc := hCompactSourcePc
            _ = block.preparedPc := hPreparedPcEq.symm
        have hCompactInstr :
            compactBlock.sourceInstr = block.sourceInstr := by
          have hPhysicalAt :
              artifact.physicalSource.instrAtPc block.preparedPc =
                some (block.preparedPc, block.sourceInstr) := by
            have hPreparation :=
              ReturnAddressProbe.Compact.compile?_preparationBlocksValid
                hCompile
            obtain ⟨pre, post, hPrepared, hBlockPc⟩ :=
              hPreparation.prepared_decompose_of_keep
                hBlock hAction
            rw [hPrepared, hBlockPc]
            unfold Assembly.Program.instrAtPc
            simpa using
              Assembly.Program.instrAtPcFrom_append_boundary_cons
                pre post block.sourceInstr 0
          have hPhysicalAt' :
              artifact.physicalSource.instrAtPc compactBlock.sourcePc =
                some (compactBlock.sourcePc,
                  compactBlock.sourceInstr) := by
            have hBlocks :=
              ReturnAddressProbe.Compact.compile?_blocksValid hCompile
            obtain ⟨pre, post, hPhysical, hBlockPc⟩ :=
              hBlocks.decompose_of_block_mem hCompactBlock
            rw [hPhysical, hBlockPc]
            unfold Assembly.Program.instrAtPc
            simpa using
              Assembly.Program.instrAtPcFrom_append_boundary_cons
                pre post compactBlock.sourceInstr 0
          rw [hCompactSourcePc'] at hPhysicalAt'
          rw [hPhysicalAt] at hPhysicalAt'
          exact (congrArg Prod.snd (Option.some.inj hPhysicalAt')).symm
        obtain ⟨targetFuel, hFuel, hFuelExact, hRel⟩ :=
          kept_ordinary_compact_rel
            hCompile byteSuffix hBlock hAction hOrdinary
            ⟨compactBlock, hCompactBlock, hCompactSourcePc',
              hCompactInstr,
              by simpa [hCompactPc] using hTargetPc⟩
            hPreparedPc hSourcePc hTargetPrepared hPreparedSource
        exact
          ⟨targetFuel, hFuel,
            by simpa [blockFuel, hAction] using hFuelExact,
            hRel⟩
      · have hImpossible :
            compactSourcePc < artifact.physicalSource.byteLength := by
          rw [← hPreparedPcEq]
          have hPreparation :=
            ReturnAddressProbe.Compact.compile?_preparationBlocksValid
              hCompile
          obtain ⟨pre, post, hPrepared, hBlockPc⟩ :=
            hPreparation.prepared_decompose_of_keep hBlock hAction
          rw [hPrepared, hBlockPc]
          simp only [Assembly.Program.byteLength_append,
            Assembly.Program.byteLength_cons]
          have hInstrPos :=
            Assembly.Instr.byteSize_pos block.sourceInstr
          omega
        rw [hCompactEnd.1] at hImpossible
        omega
  | skip =>
      have hBoundaryState :
          BoundaryStateRel artifact target prepared :=
        ⟨compactSourcePc, compactPc, hCompactBoundary,
          by simpa [prepared] using hPreparedEq,
          hTargetPc, hTargetPrepared⟩
      refine ⟨0, by omega, by simp [blockFuel, hAction], ?_⟩
      have hPreparation :=
        skip_block_open_rel hCompile hBlock hAction hOrdinary
          hPreparedPc hSourcePc hPreparedSource
      have hCompact :
          Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
            (Assembly.Compact.InteractionSemantics.openRunNResult
              (Assembly.Bytecode.ofList
                (artifact.bytes.toList ++ byteSuffix)) 0 target)
            (Assembly.InteractionSemantics.Source.openRunNResult
              artifact.physicalSource 0 prepared) := by
        change
          Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
            (.done (.ok (.running target)))
            (.done (.ok (.running prepared)))
        exact .done (.ok hBoundaryState)
      apply Simulation.Interaction.Rel.mono
        (by
          simpa [CombinedOutcomeRel] using
            Simulation.Interaction.Rel.trans hCompact hPreparation)
      intro targetDone sourceDone hDone
      exact combinedOutcomeRel_full hDone

theorem FullStateRel.ordinary_open_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {target source : EVMState}
    {block : Assembly.Compact.PreparationBlock}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hFull : FullStateRel sourceProgram artifact target source)
    (hBlock : block ∈ artifact.preparation)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hOrdinary : Ordinary block.sourceInstr) :
    ∃ targetFuel,
      targetFuel ≤ 2 ∧
        targetFuel = blockFuel block ∧
        Simulation.Interaction.Rel
          (FullOutcomeRel sourceProgram artifact)
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            targetFuel target)
          (Assembly.InteractionSemantics.Source.openStepAtResult
            sourceProgram block.sourcePc block.sourceInstr source) := by
  obtain
      ⟨compactSourcePc, compactPc, hPreparedEq,
        hCompactBoundary, hTargetPc, hRuntime⟩ :=
    hFull.active_block hCompile hBlock hSourcePc
  exact
    active_ordinary_compact_rel
      hCompile byteSuffix hBlock hSourcePc hPreparedEq hCompactBoundary
      hTargetPc hRuntime hOrdinary

theorem skipped_ordinary_compact_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : Assembly.Compact.PreparationBlock}
    {target prepared source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (hBlock : block ∈ artifact.preparation)
    (hSkip : block.action = .skip)
    (hOrdinary : Ordinary block.sourceInstr)
    (hCompactBoundary : BoundaryStateRel artifact target prepared)
    (hPreparedPc :
      prepared.pc = EvmYul.UInt256.ofNat block.preparedPc)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat block.sourcePc)
    (hTargetPrepared : Assembly.SameRuntimeData target prepared)
    (hPreparedSource : Assembly.SameRuntimeData prepared source) :
    Simulation.Interaction.Rel
      (FullOutcomeRel sourceProgram artifact)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList artifact.bytes.toList) 0 target)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        sourceProgram block.sourcePc block.sourceInstr source) := by
  have hPreparation :=
    skip_block_open_rel hCompile hBlock hSkip hOrdinary
      hPreparedPc hSourcePc hPreparedSource
  have hCompact :
      Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
        (Assembly.Compact.InteractionSemantics.openRunNResult
          (Assembly.Bytecode.ofList artifact.bytes.toList) 0 target)
        (Assembly.InteractionSemantics.Source.openRunNResult
          artifact.physicalSource 0 prepared) := by
    change
      Simulation.Interaction.Rel (BoundaryOutcomeRel artifact)
        (.done (.ok (.running target)))
        (.done (.ok (.running prepared)))
    exact .done (.ok hCompactBoundary)
  apply Simulation.Interaction.Rel.mono
    (by
      simpa [CombinedOutcomeRel] using
        Simulation.Interaction.Rel.trans hCompact hPreparation)
  intro targetDone sourceDone hDone
  exact combinedOutcomeRel_full hDone

inductive SimpleTrace (artifact : Artifact) :
    Nat → List Assembly.Compact.PreparationBlock → Prop
  | nil (sourcePc : Nat) :
      SimpleTrace artifact sourcePc []
  | cons (sourcePc : Nat)
      (block : Assembly.Compact.PreparationBlock)
      (rest : List Assembly.Compact.PreparationBlock)
      (hBlock : block ∈ artifact.preparation)
      (hSourcePc : block.sourcePc = sourcePc)
      (hSimple :
        Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
          block.sourceInstr)
      (hRest :
        SimpleTrace artifact
          (sourcePc + block.sourceInstr.byteSize) rest) :
      SimpleTrace artifact sourcePc (block :: rest)

def SimpleTrace.targetFuel
    (blocks : List Assembly.Compact.PreparationBlock) : Nat :=
  (blocks.map blockFuel).sum

def SimpleTrace.sourceByteLength
    (blocks : List Assembly.Compact.PreparationBlock) : Nat :=
  (blocks.map fun block => block.sourceInstr.byteSize).sum

theorem ordinary_of_preparationSimple
    {instr : Assembly.Instr}
    (hSimple :
      Assembly.Compact.InteractionSemantics.PreparationSimpleInstr instr) :
    Ordinary instr := by
  cases hSimple <;> trivial

theorem SimpleTrace.openRunNResult_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : SimpleTrace artifact sourcePc blocks)
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    {target source : EVMState}
    (hFull : FullStateRel sourceProgram artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc) :
    Simulation.Interaction.Rel
      (FullOutcomeRel sourceProgram artifact)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        (SimpleTrace.targetFuel blocks) target)
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram blocks.length source) := by
  induction hTrace generalizing target source with
  | nil sourcePc =>
      change
        Simulation.Interaction.Rel
          (FullOutcomeRel sourceProgram artifact)
          (.done (.ok (.running target)))
          (.done (.ok (.running source)))
      exact .done (.ok hFull)
  | @cons sourcePc block rest hBlock hBlockSourcePc hSimple hRest ih =>
      have hSourcePc' :
          source.pc = EvmYul.UInt256.ofNat block.sourcePc := by
        simpa [hBlockSourcePc] using hSourcePc
      have hOrdinary : Ordinary block.sourceInstr :=
        ordinary_of_preparationSimple hSimple
      obtain ⟨stepFuel, _hStepFuel, hStepFuel, hStep⟩ :=
        hFull.ordinary_open_rel
          hCompile byteSuffix hBlock hSourcePc' hOrdinary
      have hSourceStep :=
        source_openStepResult_eq_block
          hCompile hBlock hSourcePc'
      have hNextAt :=
        hSimple.source_runningAt_next
          sourceProgram block.sourcePc source
      have hNextAt' :
          Simulation.Interaction.AllDone
            (Assembly.Compact.RunningAt
              (EvmYul.UInt256.ofNat
                (sourcePc + block.sourceInstr.byteSize)))
            (Assembly.InteractionSemantics.Source.openStepAtResult
              sourceProgram block.sourcePc block.sourceInstr source) := by
        apply Simulation.Interaction.AllDone.mono hNextAt
        intro outcome hAt
        cases outcome with
        | error error =>
            trivial
        | ok result =>
            cases result with
            | halted halt =>
                trivial
            | running next =>
                change
                  next.pc =
                    EvmYul.UInt256.ofNat
                      (sourcePc + block.sourceInstr.byteSize)
                change
                  next.pc =
                    source.pc +
                      EvmYul.UInt256.ofNat block.sourceInstr.byteSize
                  at hAt
                simpa [hSourcePc, Assembly.UInt256_ofNat_add] using hAt
      have hStepStrong :=
        Simulation.Interaction.Rel.strengthen_right hStep hNextAt'
      simp only [SimpleTrace.targetFuel, List.map_cons, List.sum_cons,
        List.length_cons]
      rw [
        ← hStepFuel,
        Assembly.Compact.InteractionSemantics.openRunNResult_add,
        Assembly.InteractionSemantics.Source.openRunNResult_succ,
        hSourceStep]
      apply Simulation.Interaction.Rel.bind_custom hStepStrong
      intro targetDone sourceDone hDone
      rcases hDone with ⟨hRelated, hNextSourcePc⟩
      cases hRelated with
      | error hError =>
          exact .done (.error hError)
      | ok hResult =>
          rename_i targetResult sourceResult
          cases targetResult with
          | running targetMid =>
              cases sourceResult with
              | running sourceMid =>
                  change
                    FullStateRel sourceProgram artifact
                      targetMid sourceMid at hResult
                  change
                    sourceMid.pc =
                      EvmYul.UInt256.ofNat
                        (sourcePc + block.sourceInstr.byteSize)
                    at hNextSourcePc
                  exact ih hResult hNextSourcePc
              | halted sourceHalt =>
                  simp [FullStepResultRel] at hResult
          | halted targetHalt =>
              cases sourceResult with
              | running sourceMid =>
                  simp [FullStepResultRel] at hResult
              | halted sourceHalt =>
                  exact .done (.ok hResult)

theorem SimpleTrace.source_runningAt_end
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : SimpleTrace artifact sourcePc blocks)
    (hCompile :
      ReturnAddressProbe.Compact.compile? sourceProgram pinnedPushPcs =
        some artifact)
    {source : EVMState}
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc) :
    Simulation.Interaction.AllDone
      (Assembly.Compact.RunningAt
        (EvmYul.UInt256.ofNat
          (sourcePc + SimpleTrace.sourceByteLength blocks)))
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram blocks.length source) := by
  induction hTrace generalizing source with
  | nil sourcePc =>
      change
        Simulation.Interaction.AllDone
          (Assembly.Compact.RunningAt
            (EvmYul.UInt256.ofNat sourcePc))
          (.done (.ok (.running source)))
      exact .done hSourcePc
  | @cons sourcePc block rest hBlock hBlockSourcePc hSimple hRest ih =>
      have hSourcePc' :
          source.pc = EvmYul.UInt256.ofNat block.sourcePc := by
        simpa [hBlockSourcePc] using hSourcePc
      have hSourceStep :=
        source_openStepResult_eq_block
          hCompile hBlock hSourcePc'
      have hNext :=
        hSimple.source_runningAt_next
          sourceProgram block.sourcePc source
      have hNext' :
          Simulation.Interaction.AllDone
            (Assembly.Compact.RunningAt
              (EvmYul.UInt256.ofNat
                (sourcePc + block.sourceInstr.byteSize)))
            (Assembly.InteractionSemantics.Source.openStepAtResult
              sourceProgram block.sourcePc block.sourceInstr source) := by
        apply Simulation.Interaction.AllDone.mono hNext
        intro outcome hAt
        cases outcome with
        | error error =>
            trivial
        | ok result =>
            cases result with
            | halted halt =>
                trivial
            | running next =>
                change
                  next.pc =
                    EvmYul.UInt256.ofNat
                      (sourcePc + block.sourceInstr.byteSize)
                change
                  next.pc =
                    source.pc +
                      EvmYul.UInt256.ofNat block.sourceInstr.byteSize
                  at hAt
                simpa [hSourcePc, Assembly.UInt256_ofNat_add] using hAt
      simp only [List.length_cons]
      rw [
        Assembly.InteractionSemantics.Source.openRunNResult_succ,
        hSourceStep]
      apply Simulation.Interaction.AllDone.bind hNext'
      · intro error hError
        trivial
      · intro result hResult
        cases result with
        | halted halt =>
            exact .done trivial
        | running next =>
            change
              next.pc =
                EvmYul.UInt256.ofNat
                  (sourcePc + block.sourceInstr.byteSize)
              at hResult
            have hTail := ih hResult
            simpa [SimpleTrace.sourceByteLength, Nat.add_assoc] using
              hTail

inductive OrdinaryTrace (artifact : Artifact) :
    Nat → List Assembly.Compact.PreparationBlock → Prop
  | nil (sourcePc : Nat) :
      OrdinaryTrace artifact sourcePc []
  | cons (sourcePc : Nat)
      (block : Assembly.Compact.PreparationBlock)
      (rest : List Assembly.Compact.PreparationBlock)
      (hBlock : block ∈ artifact.preparation)
      (hSourcePc : block.sourcePc = sourcePc)
      (hOrdinary : Ordinary block.sourceInstr)
      (hRest :
        OrdinaryTrace artifact
          (sourcePc + block.sourceInstr.byteSize) rest) :
      OrdinaryTrace artifact sourcePc (block :: rest)

def OrdinaryTrace.targetFuel
    (blocks : List Assembly.Compact.PreparationBlock) : Nat :=
  (blocks.map blockFuel).sum

def OrdinaryTrace.targetOpenUntil
    (continueTransfer : Assembly.Instr → Bool)
    (bytes : ByteArray) :
    List Assembly.Compact.PreparationBlock → EVMState →
      Assembly.InteractionSemantics.OpenStepResult
  | [], state =>
      pure (.running state)
  | block :: rest, state => do
      let result ←
        Assembly.Compact.InteractionSemantics.openRunNResult
          bytes (blockFuel block) state
      match
          block.sourceInstr.classifyFlowWith
            continueTransfer state result with
      | .next mid =>
          targetOpenUntil continueTransfer bytes rest mid
      | .exit result =>
          pure result

theorem ordinary_source_next_runningAt
    {program : Assembly.Program} {pc : Nat}
    {instr : Assembly.Instr} {state : EVMState}
    (hOrdinary : Ordinary instr) :
    Simulation.Interaction.AllDone
      (fun
        (outcome :
          Except Assembly.EVMException Assembly.StepResult) =>
        match outcome with
        | .ok result =>
            match instr.classifyFlow state result with
            | .next next =>
                next.pc =
                  state.pc +
                    EvmYul.UInt256.ofNat instr.byteSize
            | .exit _ => True
        | .error _ => True)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        program pc instr state) := by
  cases instr with
  | label name =>
      have hNext :=
        (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.label
          name).source_runningAt_next program pc state
      apply Simulation.Interaction.AllDone.mono hNext
      intro outcome hOutcome
      cases outcome with
      | error error =>
          trivial
      | ok result =>
          cases result with
          | running next =>
              exact hOutcome
          | halted halt =>
              trivial
  | prim op =>
      have hNext :=
        (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.prim
          op).source_runningAt_next program pc state
      apply Simulation.Interaction.AllDone.mono hNext
      intro outcome hOutcome
      cases outcome with
      | error error =>
          trivial
      | ok result =>
          cases result with
          | running next =>
              exact hOutcome
          | halted halt =>
              trivial
  | push value =>
      have hNext :=
        (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.push
          32 value).source_runningAt_next program pc state
      apply Simulation.Interaction.AllDone.mono hNext
      intro outcome hOutcome
      cases outcome with
      | error error =>
          trivial
      | ok result =>
          cases result with
          | running next =>
              exact hOutcome
          | halted halt =>
              trivial
  | pushLabel target =>
      exact False.elim hOrdinary
  | jump target =>
      apply Simulation.Interaction.AllDone.mono
        (Simulation.Interaction.AllDone.trivial
          (Assembly.InteractionSemantics.Source.openStepAtResult
            program pc (.jump target) state))
      intro outcome hOutcome
      cases outcome with
      | error error =>
          trivial
      | ok result =>
          cases result <;> trivial
  | jumpi target =>
      unfold Assembly.InteractionSemantics.Source.openStepAtResult
        Assembly.InteractionSemantics.Source.openStepAt
      simp only [Assembly.Instr.haltKind?,
        Simulation.Interaction.bind_done_ok]
      unfold Assembly.Source.stepAt
      cases hDest : program.labelPc target with
      | none =>
          simp only [hDest, Assembly.Source.invalid,
            Option.elim_none, pure_except]
          simp only [Bind.bind, Except.bind]
          rw [Simulation.Interaction.bind_done_error]
          exact .done trivial
      | some dest =>
          cases hPop : state.stack.pop with
          | none =>
              simp only [hDest, Option.elim_some,
                hPop, pure_except]
              simp only [Bind.bind, Except.bind]
              rw [Simulation.Interaction.bind_done_error]
              exact .done trivial
          | some popped =>
              rcases popped with ⟨stack, condition⟩
              by_cases hZero :
                  condition = EvmYul.UInt256.ofNat 0
              · simp only [hDest, Option.elim_some,
                  hPop, pure_except]
                simp only [Bind.bind, Except.bind]
                rw [Simulation.Interaction.bind_done_ok]
                apply Simulation.Interaction.AllDone.done
                simp [hPop, hZero,
                  Assembly.Instr.classifyFlow,
                  Assembly.Instr.classifyFlowWith,
                  Assembly.Source.jumpiFallthroughPc,
                  Assembly.Instr.byteSize,
                  Assembly.Instr.push32Size,
                  Assembly.Instr.jumpSize,
                  Assembly.UInt256_ofNat_add,
                  bne, EvmYul.instBEqUInt256,
                  EvmYul.instBEqUInt256.beq,
                  EvmYul.UInt256.ofNat, Id.run,
                  add_assoc]
                change
                  state.pc + EvmYul.UInt256.ofNat 33 +
                      EvmYul.UInt256.ofNat 1 =
                    state.pc + EvmYul.UInt256.ofNat 34
                rw [← Assembly.UInt256_ofNat_add 33 1]
                change
                  EvmYul.UInt256.add
                      (EvmYul.UInt256.add state.pc
                        (EvmYul.UInt256.ofNat 33))
                      (EvmYul.UInt256.ofNat 1) =
                    EvmYul.UInt256.add state.pc
                      (EvmYul.UInt256.add
                        (EvmYul.UInt256.ofNat 33)
                        (EvmYul.UInt256.ofNat 1))
                unfold EvmYul.UInt256.add
                congr 1
                exact add_assoc _ _ _
              · simp only [hDest, Option.elim_some,
                  hPop, pure_except]
                simp only [Bind.bind, Except.bind]
                rw [Simulation.Interaction.bind_done_ok]
                apply Simulation.Interaction.AllDone.done
                simp [hPop, hZero,
                  Assembly.Instr.classifyFlow,
                  Assembly.Instr.classifyFlowWith]
  | jumpDynamic =>
      exact False.elim hOrdinary

set_option maxHeartbeats 1000000 in
theorem OrdinaryTrace.targetOpenUntil_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {sourcePc : Nat}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : OrdinaryTrace artifact sourcePc blocks)
    (hCompile :
      ReturnAddressProbe.Compact.compile?
          sourceProgram pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    {target source : EVMState}
    (hFull : FullStateRel sourceProgram artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc) :
    Simulation.Interaction.Rel
      (FullOutcomeRel sourceProgram artifact)
      (OrdinaryTrace.targetOpenUntil
        (fun _ => false)
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        blocks target)
      (Assembly.InteractionSemantics.Source.openRunUntilTransfer
        sourceProgram blocks.length source) := by
  induction hTrace generalizing target source with
  | nil sourcePc =>
      change
        Simulation.Interaction.Rel
          (FullOutcomeRel sourceProgram artifact)
          (.done (.ok (.running target)))
          (.done (.ok (.running source)))
      exact .done (.ok hFull)
  | @cons sourcePc block rest hBlock hBlockSourcePc
      hOrdinary hRest ih =>
      have hSourceBlockPc :
          source.pc =
            EvmYul.UInt256.ofNat block.sourcePc := by
        simpa [hBlockSourcePc] using hSourcePc
      obtain ⟨stepFuel, hStepBound, hStepFuel, hStepRel⟩ :=
        hFull.ordinary_open_rel
          hCompile byteSuffix hBlock hSourceBlockPc hOrdinary
      have hNext :=
        ordinary_source_next_runningAt
          (program := sourceProgram)
          (pc := block.sourcePc)
          (state := source) hOrdinary
      have hStepStrong :=
        Simulation.Interaction.Rel.strengthen_right
          hStepRel hNext
      have hPreparation :=
        ReturnAddressProbe.Compact.compile?_preparationBlocksValid
          hCompile
      obtain ⟨pre, post, hProgram, hBlockPc⟩ :=
        hPreparation.source_decompose_of_block_mem hBlock
      have hWholeFits :=
        (ReturnAddressProbe.Compact.compile?_valid
          hCompile).sourcePCFits
      have hPreFits : pre.PCFits := by
        rw [hProgram] at hWholeFits
        exact
          (Assembly.Program.PCFitsFrom.of_append
            (pre := pre)
            (code := block.sourceInstr :: post)
            (post := [])
            (by simpa using hWholeFits)).start
      have hBoundaryPc : source.pc = pre.pcAfter := by
        simpa [Assembly.Program.pcAfter, hBlockPc] using
          hSourceBlockPc
      have hBeforeRuntime := hFull.runtimeData
      have hBeforeStack :
          target.stack = source.stack :=
        Assembly.SameRuntimeData.stack_eq hBeforeRuntime
      rw [hStepFuel] at hStepStrong
      simp only [OrdinaryTrace.targetOpenUntil]
      unfold
        Assembly.InteractionSemantics.Source.openRunUntilTransfer
      rw [show
        (block :: rest).length = rest.length + 1 by
          simp]
      have hSourceRunRaw :=
        Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_at_boundary
          (fun _ => false)
          (pre := pre)
          (post := post)
          (instr := block.sourceInstr)
          (state := source)
          rest.length hPreFits hBoundaryPc
      have hSourceRun :
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              (fun _ => false) sourceProgram (rest.length + 1) source =
            (do
              let result ←
                Assembly.InteractionSemantics.Source.openStepAtResult
                  sourceProgram block.sourcePc block.sourceInstr source
              match block.sourceInstr.classifyFlowWith
                  (fun _ => false) source result with
              | .next state' =>
                  Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                    (fun _ => false) sourceProgram rest.length state'
              | .exit result =>
                  pure result) := by
        simpa [hProgram, hBlockPc, List.append_assoc] using
          hSourceRunRaw
      rw [hSourceRun]
      apply Simulation.Interaction.Rel.bind_custom hStepStrong
      intro targetDone sourceDone hDone
      rcases hDone with ⟨hRelated, hNextFact⟩
      cases hRelated with
      | error hError =>
          exact .done (.error hError)
      | ok hResult =>
          rename_i targetResult sourceResult
          cases targetResult with
          | halted targetHalt =>
              cases sourceResult with
              | running sourceMid =>
                  simp [FullStepResultRel] at hResult
              | halted sourceHalt =>
                  exact .done (.ok hResult)
          | running targetMid =>
              cases sourceResult with
              | halted sourceHalt =>
                  simp [FullStepResultRel] at hResult
              | running sourceMid =>
                  change
                    FullStateRel sourceProgram artifact
                      targetMid sourceMid at hResult
                  cases hInstr : block.sourceInstr with
                  | label name =>
                      have hNextFact' :
                          sourceMid.pc =
                            source.pc +
                              EvmYul.UInt256.ofNat
                                block.sourceInstr.byteSize := by
                        simpa [hInstr,
                          Assembly.Instr.classifyFlow,
                          Assembly.Instr.classifyFlowWith] using
                          hNextFact
                      have hNextPc :
                          sourceMid.pc =
                            EvmYul.UInt256.ofNat
                              (sourcePc +
                                block.sourceInstr.byteSize) := by
                        simpa [hSourcePc,
                          Assembly.UInt256_ofNat_add] using hNextFact'
                      simpa [hInstr,
                        Assembly.Instr.classifyFlowWith] using
                        ih hResult hNextPc
                  | prim op =>
                      have hNextFact' :
                          sourceMid.pc =
                            source.pc +
                              EvmYul.UInt256.ofNat
                                block.sourceInstr.byteSize := by
                        simpa [hInstr,
                          Assembly.Instr.classifyFlow,
                          Assembly.Instr.classifyFlowWith] using
                          hNextFact
                      have hNextPc :
                          sourceMid.pc =
                            EvmYul.UInt256.ofNat
                              (sourcePc +
                                block.sourceInstr.byteSize) := by
                        simpa [hSourcePc,
                          Assembly.UInt256_ofNat_add] using hNextFact'
                      simpa [hInstr,
                        Assembly.Instr.classifyFlowWith] using
                        ih hResult hNextPc
                  | push value =>
                      have hNextFact' :
                          sourceMid.pc =
                            source.pc +
                              EvmYul.UInt256.ofNat
                                block.sourceInstr.byteSize := by
                        simpa [hInstr,
                          Assembly.Instr.classifyFlow,
                          Assembly.Instr.classifyFlowWith] using
                          hNextFact
                      have hNextPc :
                          sourceMid.pc =
                            EvmYul.UInt256.ofNat
                              (sourcePc +
                                block.sourceInstr.byteSize) := by
                        simpa [hSourcePc,
                          Assembly.UInt256_ofNat_add] using hNextFact'
                      simpa [hInstr,
                        Assembly.Instr.classifyFlowWith] using
                        ih hResult hNextPc
                  | pushLabel label =>
                      simp [Ordinary, hInstr] at hOrdinary
                  | jump label =>
                      simpa [hInstr,
                        Assembly.Instr.classifyFlowWith] using
                        (Simulation.Interaction.Rel.done (.ok hResult))
                  | jumpi label =>
                      cases hPop : source.stack.pop with
                      | none =>
                          simpa [hInstr,
                            Assembly.Instr.classifyFlowWith,
                            hBeforeStack, hPop] using
                            (Simulation.Interaction.Rel.done (.ok hResult))
                      | some popped =>
                          rcases popped with ⟨stack, condition⟩
                          by_cases hZero :
                              condition =
                                EvmYul.UInt256.ofNat 0
                          · have hNextFact' :
                                sourceMid.pc =
                                  source.pc +
                                    EvmYul.UInt256.ofNat
                                      block.sourceInstr.byteSize := by
                              simpa [hInstr,
                                Assembly.Instr.classifyFlow,
                                Assembly.Instr.classifyFlowWith,
                                hPop, hZero] using hNextFact
                            have hNextPc :
                                sourceMid.pc =
                                  EvmYul.UInt256.ofNat
                                    (sourcePc +
                                      block.sourceInstr.byteSize) := by
                              simpa [hSourcePc,
                                Assembly.UInt256_ofNat_add] using
                                  hNextFact'
                            simpa [hInstr,
                              Assembly.Instr.classifyFlowWith,
                              hBeforeStack, hPop, hZero] using
                              ih hResult hNextPc
                          · simpa [hInstr,
                              Assembly.Instr.classifyFlowWith,
                              hBeforeStack, hPop, hZero] using
                              (Simulation.Interaction.Rel.done (.ok hResult))
                  | jumpDynamic =>
                      simp [Ordinary, hInstr] at hOrdinary

def simpleInstr? : Assembly.Instr → Bool
  | .label _ | .push _ => true
  | .prim op =>
      decide (op ≠ .pc) && op.stackArity?.isSome
  | .pushLabel _ | .jump _ | .jumpi _ | .jumpDynamic => false

theorem simpleInstr?_sound
    {instr : Assembly.Instr}
    (hCheck : simpleInstr? instr = true) :
    Assembly.Compact.InteractionSemantics.PreparationSimpleInstr instr := by
  cases instr with
  | label name =>
      exact .label name
  | prim op =>
      have hParts := Bool.and_eq_true_iff.mp hCheck
      exact .prim op (by simpa using hParts.1)
  | push value =>
      exact .push value
  | pushLabel target | jump target | jumpi target | jumpDynamic =>
      simp [simpleInstr?] at hCheck

def ordinaryInstr? : Assembly.Instr → Bool
  | .pushLabel _ | .jumpDynamic => false
  | _ => true

theorem ordinaryInstr?_sound
    {instr : Assembly.Instr}
    (hCheck : ordinaryInstr? instr = true) :
    Ordinary instr := by
  cases instr <;> simp [ordinaryInstr?, Ordinary] at hCheck ⊢

theorem simpleInstr?_prim_arity
    {op : Assembly.PrimOp}
    (hCheck : simpleInstr? (.prim op) = true) :
    ∃ input output,
      op.stackArity? = some (input, output) := by
  have hParts := Bool.and_eq_true_iff.mp hCheck
  cases hArity : op.stackArity? with
  | none =>
      simp [hArity] at hParts
  | some arity =>
      rcases arity with ⟨input, output⟩
      exact ⟨input, output, by simpa using hArity⟩

def simpleHeightStep (instr : Assembly.Instr) (height : Nat) : Nat :=
  match instr with
  | .label _ => height
  | .push _ => height + 1
  | .prim op =>
      match op.stackArity? with
      | some (input, output) =>
          height - input + output
      | none => 0
  | .pushLabel _ | .jump _ | .jumpi _ | .jumpDynamic =>
      height

def simpleHeightRun : Assembly.Program → Nat → Nat
  | [], height => height
  | instr :: rest, height =>
      simpleHeightRun rest (simpleHeightStep instr height)

theorem simpleHeightRun_append
    (left right : Assembly.Program) (height : Nat) :
    simpleHeightRun (left ++ right) height =
      simpleHeightRun right (simpleHeightRun left height) := by
  induction left generalizing height with
  | nil =>
      rfl
  | cons instr rest ih =>
      simp [simpleHeightRun, ih]

theorem simpleHeightRun_guardedLiftBuriedToTop_pos
    (depth height : Nat) (hBound : depth < 16) :
    0 <
      simpleHeightRun
        (Assembly.StackShuffle.guardedLiftBuriedToTop depth)
        height := by
  interval_cases depth <;>
    simp [Assembly.StackShuffle.guardedLiftBuriedToTop,
      Assembly.StackShuffle.guardBuried,
      Assembly.StackShuffle.liftBuriedToTop,
      Assembly.StackShuffle.dupInstr,
      Assembly.StackShuffle.swapInstr,
      simpleHeightRun, simpleHeightStep,
      Assembly.PrimOp.stackArity?,
      Assembly.PrimOp.toEVM,
      EvmYul.EVM.δ, EvmYul.EVM.α] <;>
    omega

theorem simpleInstr?_source_step_height
    {program : Assembly.Program} {pc : Nat}
    {instr : Assembly.Instr} {state : EVMState}
    (hCheck : simpleInstr? instr = true) :
    Simulation.Interaction.AllDone
      (fun
        (outcome :
          Except Assembly.EVMException Assembly.StepResult) =>
        match outcome with
        | .ok (Assembly.StepResult.running final) =>
            final.stack.length =
              simpleHeightStep instr state.stack.length
        | _ => True)
      (Assembly.InteractionSemantics.Source.openStepAtResult
        program pc instr state) := by
  cases instr with
  | label name =>
      rw [
        (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.label
          name).openStepResult_eq program pc state]
      exact
        .done
          (by
            simp [simpleHeightStep,
              EvmYul.EVM.State.incrPC])
  | push value =>
      rw [
        (Assembly.Compact.InteractionSemantics.SimpleSourceInstrRel.push
          32 value).openStepResult_eq program pc state]
      exact
        .done
          (by
            simp [simpleHeightStep, EvmYul.Stack.push,
              EvmYul.EVM.State.replaceStackAndIncrPC,
              EvmYul.EVM.State.incrPC])
  | prim op =>
      obtain ⟨input, output, hArity⟩ :=
        simpleInstr?_prim_arity hCheck
      have hNoHalt :
          (Assembly.Instr.prim op).haltKind? = none := by
        cases op <;>
          simp [Assembly.Instr.haltKind?,
            Assembly.PrimOp.haltKind?,
            Assembly.PrimOp.stackArity?] at hArity ⊢
      have hRealizes :=
        Assembly.InteractionPreservation.PrimOp.openStep_realizesStackArity
          (state := state) hArity
      unfold Assembly.InteractionSemantics.Source.openStepAtResult
        Assembly.InteractionSemantics.Source.openStepAt
      rw [hNoHalt]
      apply Simulation.Interaction.AllDone.bind hRealizes
      · intro error hError
        trivial
      · intro final hFinal
        exact
          .done
            (by simpa [simpleHeightStep, hArity] using hFinal)
  | pushLabel target | jump target | jumpi target | jumpDynamic =>
      simp [simpleInstr?] at hCheck

def preparationBlockAt?
    (artifact : Artifact) (sourcePc : Nat) (instr : Assembly.Instr) :
    Option Assembly.Compact.PreparationBlock :=
  artifact.preparation.find? fun block =>
    decide (block.sourcePc = sourcePc ∧ block.sourceInstr = instr)

theorem preparationBlockAt?_sound
    {artifact : Artifact} {sourcePc : Nat} {instr : Assembly.Instr}
    {block : Assembly.Compact.PreparationBlock}
    (hFind :
      preparationBlockAt? artifact sourcePc instr = some block) :
    block ∈ artifact.preparation ∧
      block.sourcePc = sourcePc ∧ block.sourceInstr = instr := by
  unfold preparationBlockAt? at hFind
  have hMem := List.mem_of_find?_eq_some hFind
  have hCheck := List.find?_some hFind
  simpa using And.intro hMem (by simpa using hCheck)

def ordinaryTrace? (artifact : Artifact) :
    Nat → Assembly.Program →
      Option (List Assembly.Compact.PreparationBlock)
  | _sourcePc, [] =>
      some []
  | sourcePc, instr :: rest => do
      let _ ← if ordinaryInstr? instr then some () else none
      let block ← preparationBlockAt? artifact sourcePc instr
      let tail ←
        ordinaryTrace? artifact
          (sourcePc + instr.byteSize) rest
      some (block :: tail)

theorem ordinaryTrace?_sound
    {artifact : Artifact} {sourcePc : Nat}
    {code : Assembly.Program}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : ordinaryTrace? artifact sourcePc code = some blocks) :
    OrdinaryTrace artifact sourcePc blocks := by
  induction code generalizing sourcePc blocks with
  | nil =>
      simp [ordinaryTrace?] at hTrace
      subst blocks
      exact .nil sourcePc
  | cons instr rest ih =>
      unfold ordinaryTrace? at hTrace
      by_cases hOrdinary : ordinaryInstr? instr = true
      · simp [hOrdinary] at hTrace
        cases hBlock :
            preparationBlockAt? artifact sourcePc instr with
        | none =>
            simp [hBlock] at hTrace
        | some block =>
            simp [hBlock] at hTrace
            cases hTail :
                ordinaryTrace? artifact
                  (sourcePc + instr.byteSize) rest with
            | none =>
                simp [hTail] at hTrace
            | some tail =>
                simp [hTail] at hTrace
                subst blocks
                obtain ⟨hBlockMem, hBlockPc, hBlockInstr⟩ :=
                  preparationBlockAt?_sound hBlock
                exact
                  .cons sourcePc block tail
                    hBlockMem hBlockPc
                    (by
                      rw [hBlockInstr]
                      exact ordinaryInstr?_sound hOrdinary)
                    (by simpa [hBlockInstr] using ih hTail)
      · have hOrdinaryFalse :
            ordinaryInstr? instr = false :=
          Bool.eq_false_of_not_eq_true hOrdinary
        simp [hOrdinaryFalse] at hTrace

theorem ordinaryTrace?_length
    {artifact : Artifact} {sourcePc : Nat}
    {code : Assembly.Program}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : ordinaryTrace? artifact sourcePc code = some blocks) :
    blocks.length = code.length := by
  induction code generalizing sourcePc blocks with
  | nil =>
      simp [ordinaryTrace?] at hTrace
      subst blocks
      rfl
  | cons instr rest ih =>
      unfold ordinaryTrace? at hTrace
      by_cases hOrdinary : ordinaryInstr? instr = true
      · simp [hOrdinary] at hTrace
        cases hBlock :
            preparationBlockAt? artifact sourcePc instr with
        | none =>
            simp [hBlock] at hTrace
        | some block =>
            simp [hBlock] at hTrace
            cases hTail :
                ordinaryTrace? artifact
                  (sourcePc + instr.byteSize) rest with
            | none =>
                simp [hTail] at hTrace
            | some tail =>
                simp [hTail] at hTrace
                subst blocks
                simp [ih hTail]
      · have hOrdinaryFalse :
            ordinaryInstr? instr = false :=
          Bool.eq_false_of_not_eq_true hOrdinary
        simp [hOrdinaryFalse] at hTrace

def simpleTrace? (artifact : Artifact) :
    Nat → Assembly.Program →
      Option (List Assembly.Compact.PreparationBlock)
  | _sourcePc, [] =>
      some []
  | sourcePc, instr :: rest => do
      let _ ← if simpleInstr? instr then some () else none
      let block ← preparationBlockAt? artifact sourcePc instr
      let tail ←
        simpleTrace? artifact
          (sourcePc + instr.byteSize) rest
      some (block :: tail)

theorem simpleTrace?_sound
    {artifact : Artifact} {sourcePc : Nat}
    {code : Assembly.Program}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : simpleTrace? artifact sourcePc code = some blocks) :
    SimpleTrace artifact sourcePc blocks := by
  induction code generalizing sourcePc blocks with
  | nil =>
      simp [simpleTrace?] at hTrace
      subst blocks
      exact .nil sourcePc
  | cons instr rest ih =>
      unfold simpleTrace? at hTrace
      by_cases hSimple : simpleInstr? instr = true
      · simp [hSimple] at hTrace
        cases hBlock :
            preparationBlockAt? artifact sourcePc instr with
        | none =>
            simp [hBlock] at hTrace
        | some block =>
            simp [hBlock] at hTrace
            cases hTail :
                simpleTrace? artifact
                  (sourcePc + instr.byteSize) rest with
            | none =>
                simp [hTail] at hTrace
            | some tail =>
                simp [hTail] at hTrace
                subst blocks
                obtain ⟨hBlockMem, hBlockPc, hBlockInstr⟩ :=
                  preparationBlockAt?_sound hBlock
                have hBlockSimple :
                    Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
                      block.sourceInstr := by
                  rw [hBlockInstr]
                  exact simpleInstr?_sound hSimple
                exact
                  .cons sourcePc block tail
                    hBlockMem hBlockPc hBlockSimple
                      (by simpa [hBlockInstr] using ih hTail)
      · have hSimpleFalse :
            simpleInstr? instr = false :=
          Bool.eq_false_of_not_eq_true hSimple
        simp [hSimpleFalse] at hTrace

theorem simpleTrace?_all_simple
    {artifact : Artifact} {sourcePc : Nat}
    {code : Assembly.Program}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : simpleTrace? artifact sourcePc code = some blocks) :
    ∀ instr ∈ code,
      Assembly.Compact.InteractionSemantics.PreparationSimpleInstr instr := by
  induction code generalizing sourcePc blocks with
  | nil =>
      simp
  | cons instr rest ih =>
      unfold simpleTrace? at hTrace
      by_cases hSimple : simpleInstr? instr = true
      · simp [hSimple] at hTrace
        cases hBlock :
            preparationBlockAt? artifact sourcePc instr with
        | none =>
            simp [hBlock] at hTrace
        | some block =>
            simp [hBlock] at hTrace
            cases hTail :
                simpleTrace? artifact
                  (sourcePc + instr.byteSize) rest with
            | none =>
                simp [hTail] at hTrace
            | some tail =>
                simp [hTail] at hTrace
                subst blocks
                intro candidate hCandidate
                simp only [List.mem_cons] at hCandidate
                rcases hCandidate with hHead | hRest
                · subst candidate
                  exact simpleInstr?_sound hSimple
                · exact ih hTail candidate hRest
      · have hSimpleFalse :
            simpleInstr? instr = false :=
          Bool.eq_false_of_not_eq_true hSimple
        simp [hSimpleFalse] at hTrace

theorem simpleTrace?_source_height
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {sourcePc : Nat}
    {code : Assembly.Program}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : simpleTrace? artifact sourcePc code = some blocks)
    (hCompile :
      ReturnAddressProbe.Compact.compile?
          sourceProgram pinnedPushPcs =
        some artifact)
    {source : EVMState}
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc) :
    Simulation.Interaction.AllDone
      (fun
        (outcome :
          Except Assembly.EVMException Assembly.StepResult) =>
        match outcome with
        | .ok (Assembly.StepResult.running final) =>
            final.stack.length =
              simpleHeightRun code source.stack.length
        | _ => True)
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram blocks.length source) := by
  induction code generalizing sourcePc blocks source with
  | nil =>
      simp [simpleTrace?] at hTrace
      subst blocks
      change
        Simulation.Interaction.AllDone _
          (.done (.ok (Assembly.StepResult.running source)))
      exact .done (by simp [simpleHeightRun])
  | cons instr rest ih =>
      unfold simpleTrace? at hTrace
      by_cases hSimple : simpleInstr? instr = true
      · simp [hSimple] at hTrace
        cases hBlock :
            preparationBlockAt? artifact sourcePc instr with
        | none =>
            simp [hBlock] at hTrace
        | some block =>
            simp [hBlock] at hTrace
            cases hTail :
                simpleTrace? artifact
                  (sourcePc + instr.byteSize) rest with
            | none =>
                simp [hTail] at hTrace
            | some tail =>
                simp [hTail] at hTrace
                subst blocks
                obtain ⟨hBlockMem, hBlockPc, hBlockInstr⟩ :=
                  preparationBlockAt?_sound hBlock
                have hSourceBlockPc :
                    source.pc =
                      EvmYul.UInt256.ofNat block.sourcePc := by
                  simpa [hBlockPc] using hSourcePc
                have hSourceStep :=
                  source_openStepResult_eq_block
                    hCompile hBlockMem hSourceBlockPc
                rw [hBlockInstr] at hSourceStep
                have hHeight :=
                  simpleInstr?_source_step_height
                    (program := sourceProgram)
                    (pc := block.sourcePc)
                    (state := source) hSimple
                have hSimpleProof :=
                  simpleInstr?_sound hSimple
                have hNextRaw :=
                  hSimpleProof.source_runningAt_next
                    sourceProgram block.sourcePc source
                have hNext :
                    Simulation.Interaction.AllDone
                      (Assembly.Compact.RunningAt
                        (EvmYul.UInt256.ofNat
                          (sourcePc + instr.byteSize)))
                      (Assembly.InteractionSemantics.Source.openStepAtResult
                        sourceProgram block.sourcePc instr source) := by
                  apply Simulation.Interaction.AllDone.mono hNextRaw
                  intro outcome hAt
                  cases outcome with
                  | error error =>
                      trivial
                  | ok result =>
                      cases result with
                      | halted halt =>
                          trivial
                      | running next =>
                          change
                            next.pc =
                              EvmYul.UInt256.ofNat
                                (sourcePc + instr.byteSize)
                          change
                            next.pc =
                              source.pc +
                                EvmYul.UInt256.ofNat instr.byteSize
                            at hAt
                          simpa [hSourcePc,
                            Assembly.UInt256_ofNat_add] using hAt
                have hFacts :=
                  Simulation.Interaction.AllDone.inter
                    (by simpa [hBlockInstr] using hHeight)
                    hNext
                simp only [List.length_cons]
                rw [
                  Assembly.InteractionSemantics.Source.openRunNResult_succ,
                  hSourceStep]
                apply Simulation.Interaction.AllDone.bind hFacts
                · intro error hError
                  trivial
                · intro result hResult
                  rcases hResult with ⟨hHeightStep, hNextPc⟩
                  cases result with
                  | halted halt =>
                      exact .done trivial
                  | running next =>
                      have hTailHeight :=
                        ih hTail hNextPc
                      apply Simulation.Interaction.AllDone.mono hTailHeight
                      intro outcome hOutcome
                      cases outcome with
                      | error error =>
                          trivial
                      | ok finalResult =>
                          cases finalResult with
                          | halted halt =>
                              trivial
                          | running final =>
                              change
                                final.stack.length =
                                  simpleHeightRun rest next.stack.length
                                at hOutcome
                              change
                                final.stack.length =
                                  simpleHeightRun (instr :: rest)
                                    source.stack.length
                              simpa [simpleHeightRun, hHeightStep] using
                                hOutcome
      · have hSimpleFalse :
            simpleInstr? instr = false :=
          Bool.eq_false_of_not_eq_true hSimple
        simp [hSimpleFalse] at hTrace

theorem simpleTrace?_length
    {artifact : Artifact} {sourcePc : Nat}
    {code : Assembly.Program}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : simpleTrace? artifact sourcePc code = some blocks) :
    blocks.length = code.length := by
  induction code generalizing sourcePc blocks with
  | nil =>
      simp [simpleTrace?] at hTrace
      subst blocks
      rfl
  | cons instr rest ih =>
      unfold simpleTrace? at hTrace
      by_cases hSimple : simpleInstr? instr = true
      · simp [hSimple] at hTrace
        cases hBlock :
            preparationBlockAt? artifact sourcePc instr with
        | none =>
            simp [hBlock] at hTrace
        | some block =>
            simp [hBlock] at hTrace
            cases hTail :
                simpleTrace? artifact
                  (sourcePc + instr.byteSize) rest with
            | none =>
                simp [hTail] at hTrace
            | some tail =>
                simp [hTail] at hTrace
                subst blocks
                simp [ih hTail]
      · have hSimpleFalse :
            simpleInstr? instr = false :=
          Bool.eq_false_of_not_eq_true hSimple
        simp [hSimpleFalse] at hTrace

theorem simpleTrace?_sourceByteLength
    {artifact : Artifact} {sourcePc : Nat}
    {code : Assembly.Program}
    {blocks : List Assembly.Compact.PreparationBlock}
    (hTrace : simpleTrace? artifact sourcePc code = some blocks) :
    SimpleTrace.sourceByteLength blocks = code.byteLength := by
  induction code generalizing sourcePc blocks with
  | nil =>
      simp [simpleTrace?, SimpleTrace.sourceByteLength] at hTrace ⊢
      subst blocks
      rfl
  | cons instr rest ih =>
      unfold simpleTrace? at hTrace
      by_cases hSimple : simpleInstr? instr = true
      · simp [hSimple] at hTrace
        cases hBlock :
            preparationBlockAt? artifact sourcePc instr with
        | none =>
            simp [hBlock] at hTrace
        | some block =>
            simp [hBlock] at hTrace
            cases hTail :
                simpleTrace? artifact
                  (sourcePc + instr.byteSize) rest with
            | none =>
                simp [hTail] at hTrace
            | some tail =>
                simp [hTail] at hTrace
                subst blocks
                obtain ⟨_hBlockMem, _hBlockPc, hBlockInstr⟩ :=
                  preparationBlockAt?_sound hBlock
                calc
                  SimpleTrace.sourceByteLength (block :: tail) =
                      block.sourceInstr.byteSize +
                        SimpleTrace.sourceByteLength tail := by
                    rfl
                  _ =
                      instr.byteSize +
                        Assembly.Program.byteLength rest := by
                    rw [hBlockInstr, ih hTail]
                  _ =
                      Assembly.Program.byteLength (instr :: rest) := by
                    rw [Assembly.Program.byteLength_cons]
      · have hSimpleFalse :
            simpleInstr? instr = false :=
          Bool.eq_false_of_not_eq_true hSimple
        simp [hSimpleFalse] at hTrace

/--
A straight preparation prefix can be moved out of the transfer-aware runner
without changing any interaction branch.  This is the scheduling bridge
between `CompiledBlock.openRun`, which owns the complete terminator, and the
late-return certificate, which executes the guarded lift as part of its
ordinary compact prefix.
-/
theorem simpleCode_openRunUntilTransferWithPolicy
    (continueTransfer : Assembly.Instr → Bool)
    {code pre post : Assembly.Program} {state : EVMState}
    (fuel : Nat)
    (hSimple :
      ∀ instr ∈ code,
        Assembly.Compact.InteractionSemantics.PreparationSimpleInstr instr)
    (hFits : Assembly.Program.PCFitsFrom pre code)
    (hPc : state.pc = pre.pcAfter) :
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer (pre ++ code ++ post)
        (fuel + code.length) state =
      (do
        let prefixResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            (pre ++ code ++ post) code.length state
        match prefixResult with
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              continueTransfer (pre ++ code ++ post) fuel mid
        | .halted halt =>
            pure (.halted halt)) := by
  induction code generalizing pre state with
  | nil =>
      simp
  | cons instr rest ih =>
      have hHeadSimple :
          Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
            instr :=
        hSimple instr (by simp)
      have hRestSimple :
          ∀ candidate ∈ rest,
            Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
              candidate := by
        intro candidate hCandidate
        exact hSimple candidate (by simp [hCandidate])
      have hHeadFits : pre.PCFits := hFits.1
      have hRestFits :
          Assembly.Program.PCFitsFrom (pre ++ [instr]) rest := by
        simpa [List.append_assoc] using hFits.2
      let program := pre ++ instr :: rest ++ post
      have hNextRaw :=
        hHeadSimple.source_runningAt_next
          program pre.byteLength state
      have hNext :
          Simulation.Interaction.AllDone
            (Assembly.Compact.RunningAt
              ((pre ++ [instr]).pcAfter))
            (Assembly.InteractionSemantics.Source.openStepAtResult
              program pre.byteLength instr state) := by
        apply Simulation.Interaction.AllDone.mono hNextRaw
        intro outcome hOutcome
        cases outcome with
        | error error =>
            trivial
        | ok result =>
            cases result with
            | halted halt =>
                trivial
            | running next =>
                change
                  next.pc =
                    state.pc +
                      EvmYul.UInt256.ofNat instr.byteSize
                    at hOutcome
                change next.pc = (pre ++ [instr]).pcAfter
                calc
                  next.pc =
                      state.pc +
                        EvmYul.UInt256.ofNat instr.byteSize :=
                    hOutcome
                  _ =
                      pre.pcAfter +
                        EvmYul.UInt256.ofNat instr.byteSize := by
                    rw [hPc]
                  _ = (pre ++ [instr]).pcAfter := by
                    simpa using
                      (Assembly.Program.pcAfter_append
                        pre [instr]).symm
      have hProgram :
          pre ++ (instr :: rest) ++ post = program := by
        simp [program, List.append_assoc]
      rw [hProgram]
      dsimp [program]
      rw [show
        pre ++ instr :: rest ++ post =
            pre ++ instr :: (rest ++ post) by
          simp [List.append_assoc]]
      rw [show
        fuel + (rest.length + 1) =
            (fuel + rest.length) + 1 by
          omega]
      rw [
        Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_at_boundary
          continueTransfer (fuel + rest.length) hHeadFits hPc]
      rw [
        Assembly.InteractionSemantics.Source.openRunNResult_succ,
        Assembly.InteractionPreservation.source_openStepResult_at_boundary
          hHeadFits hPc]
      change
        Simulation.Interaction.bind _ _ =
          Simulation.Interaction.bind
            (Simulation.Interaction.bind _ _) _
      rw [Simulation.Interaction.bind_assoc]
      have hNext' :
          Simulation.Interaction.AllDone
            (Assembly.Compact.RunningAt
              ((pre ++ [instr]).pcAfter))
            (Assembly.InteractionSemantics.Source.openStepAtResult
              (pre ++ instr :: (rest ++ post))
              pre.byteLength instr state) := by
        simpa [program, List.append_assoc] using hNext
      apply Simulation.Interaction.AllDone.bind_congr hNext'
      intro result hResult
      cases result with
      | halted halt =>
          cases hHeadSimple <;> rfl
      | running next =>
          have hFlow :
              instr.classifyFlowWith
                  continueTransfer state (.running next) =
                .next next := by
            cases hHeadSimple <;> rfl
          rw [hFlow]
          have hTail :=
            ih (pre := pre ++ [instr]) (state := next)
              hRestSimple hRestFits hResult
          simpa [program, List.append_assoc] using hTail

end Preparation

def dispatcherStraightCode (sites : List ReturnSite) : Assembly.Program :=
  LateReturnProbe.Terminator.selectionCode sites ++
    Assembly.StackShuffle.removeBuriedUnder 1 ++
      [Assembly.StackShuffle.dupInstr 1]

def dispatcherTailCode (caseLabel : Label) : Assembly.Program :=
  [ .jumpi caseLabel
  , .prim .invalid
  , .label caseLabel
  , .jumpDynamic
  ]

def dispatcherCode (first : ReturnSite) (rest : List ReturnSite) :
    Assembly.Program :=
  dispatcherStraightCode (first :: rest) ++
    dispatcherTailCode first.caseLabel

def compactReturnTargetsNonzero?
    (labels : Assembly.Compact.LabelTable)
    (sites : List ReturnSite) : Bool :=
  sites.all fun site =>
    match Assembly.Compact.lookupLabel? labels site.target with
    | none => false
    | some compactPc =>
        decide
          (EvmYul.UInt256.ofNat compactPc ≠ EvmYul.UInt256.ofNat 0)

theorem compactReturnTargetsNonzero?_sound
    {labels : Assembly.Compact.LabelTable} {sites : List ReturnSite}
    (hCheck : compactReturnTargetsNonzero? labels sites = true) :
    ∀ site ∈ sites,
      ∃ compactPc,
        Assembly.Compact.lookupLabel? labels site.target =
            some compactPc ∧
          EvmYul.UInt256.ofNat compactPc ≠
            EvmYul.UInt256.ofNat 0 := by
  intro site hSite
  have hSiteCheck :=
    (List.all_eq_true.mp hCheck) site hSite
  cases hLookup :
      Assembly.Compact.lookupLabel? labels site.target with
  | none =>
      simp [compactReturnTargetsNonzero?, hLookup] at hSiteCheck
  | some compactPc =>
      refine ⟨compactPc, rfl, ?_⟩
      simpa [compactReturnTargetsNonzero?, hLookup] using hSiteCheck

def returnTargetsMappedNonzero?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (sites : List ReturnSite) : Bool :=
  sites.all fun site =>
    match sourceProgram.labelPc site.target,
        artifact.physicalSource.labelPc site.target,
        Assembly.Compact.lookupLabel? artifact.labels site.target with
    | some sourceDest, some preparedDest, some compactDest =>
        (Assembly.Compact.preparationTargetPc? artifact.preparation
            sourceProgram.byteLength artifact.physicalSource.byteLength
            sourceDest ==
          some preparedDest) &&
        decide
          (EvmYul.UInt256.ofNat compactDest ≠
            EvmYul.UInt256.ofNat 0)
    | _, _, _ => false

theorem returnTargetsMappedNonzero?_sound
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {sites : List ReturnSite}
    (hCheck :
      returnTargetsMappedNonzero? sourceProgram artifact sites = true) :
    ∀ site ∈ sites,
      ∃ sourceDest preparedDest compactDest,
        sourceProgram.labelPc site.target = some sourceDest ∧
        artifact.physicalSource.labelPc site.target =
          some preparedDest ∧
        Assembly.Compact.preparationTargetPc? artifact.preparation
            sourceProgram.byteLength artifact.physicalSource.byteLength
            sourceDest =
          some preparedDest ∧
        Assembly.Compact.lookupLabel? artifact.labels site.target =
          some compactDest ∧
        EvmYul.UInt256.ofNat compactDest ≠
          EvmYul.UInt256.ofNat 0 := by
  intro site hSite
  have hSiteCheck :=
    (List.all_eq_true.mp hCheck) site hSite
  cases hSource :
      sourceProgram.labelPc site.target with
  | none =>
      simp [returnTargetsMappedNonzero?, hSource] at hSiteCheck
  | some sourceDest =>
      cases hPrepared :
          artifact.physicalSource.labelPc site.target with
      | none =>
          simp [returnTargetsMappedNonzero?, hSource, hPrepared]
            at hSiteCheck
      | some preparedDest =>
          cases hCompact :
              Assembly.Compact.lookupLabel?
                artifact.labels site.target with
          | none =>
              simp [returnTargetsMappedNonzero?, hSource, hPrepared,
                hCompact] at hSiteCheck
          | some compactDest =>
              simp [returnTargetsMappedNonzero?, hSource, hPrepared,
                hCompact] at hSiteCheck
              exact
                ⟨sourceDest, preparedDest, compactDest,
                  rfl, rfl, hSiteCheck.1, rfl, hSiteCheck.2⟩

structure DispatcherLayout where
  preparedPc : Nat
  compactCode : List Assembly.Compact.Instr

def certifyDispatcher?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (sourcePc : Nat) (first : ReturnSite) (rest : List ReturnSite) :
    Option DispatcherLayout := do
  let preparedPc ←
    Assembly.Compact.preparationTargetPc? artifact.preparation
      sourceProgram.byteLength artifact.physicalSource.byteLength sourcePc
  let _ ←
    if ReturnAddressProbe.Compact.codeAtPc?
        sourceProgram sourcePc (dispatcherCode first rest) then
      some ()
    else
      none
  let _ ←
    if ReturnAddressProbe.Compact.codeAtPc?
        artifact.physicalSource preparedPc
        (dispatcherCode first rest) then
      some ()
    else
      none
  let compactCode ←
    resolvedStraightFrom?
      artifact.pinnedPushPcs artifact.branchWidth artifact.labels
      (dispatcherStraightCode (first :: rest)) preparedPc
  let _ ←
    if returnTargetsMappedNonzero?
        sourceProgram artifact (first :: rest) then
      some ()
    else
      none
  some { preparedPc, compactCode }

structure DispatcherLayout.ValidFor
    (layout : DispatcherLayout)
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (sourcePc : Nat) (first : ReturnSite) (rest : List ReturnSite) :
    Prop where
  preparation :
    Assembly.Compact.preparationTargetPc? artifact.preparation
        sourceProgram.byteLength artifact.physicalSource.byteLength
      sourcePc =
      some layout.preparedPc
  source :
    ∃ pre post,
      sourceProgram =
        pre ++ dispatcherCode first rest ++ post ∧
      sourcePc = pre.byteLength
  physical :
    ∃ pre post,
      artifact.physicalSource =
        pre ++ dispatcherCode first rest ++ post ∧
      layout.preparedPc = pre.byteLength
  resolved :
    resolvedStraightFrom?
        artifact.pinnedPushPcs artifact.branchWidth artifact.labels
        (dispatcherStraightCode (first :: rest)) layout.preparedPc =
      some layout.compactCode
  targets :
    ∀ site ∈ first :: rest,
      ∃ sourceDest preparedDest compactDest,
        sourceProgram.labelPc site.target = some sourceDest ∧
        artifact.physicalSource.labelPc site.target =
          some preparedDest ∧
        Assembly.Compact.preparationTargetPc? artifact.preparation
            sourceProgram.byteLength artifact.physicalSource.byteLength
            sourceDest =
          some preparedDest ∧
        Assembly.Compact.lookupLabel? artifact.labels site.target =
          some compactDest ∧
        EvmYul.UInt256.ofNat compactDest ≠
          EvmYul.UInt256.ofNat 0

theorem certifyDispatcher?_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {sourcePc : Nat} {first : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    (hCertify :
      certifyDispatcher? sourceProgram artifact sourcePc first rest =
        some layout) :
    layout.ValidFor sourceProgram artifact sourcePc first rest := by
  unfold certifyDispatcher? at hCertify
  cases hPrepared :
      Assembly.Compact.preparationTargetPc? artifact.preparation
        sourceProgram.byteLength artifact.physicalSource.byteLength
        sourcePc with
  | none =>
      simp [hPrepared] at hCertify
  | some preparedPc =>
      simp [hPrepared] at hCertify
      by_cases hSource :
          ReturnAddressProbe.Compact.codeAtPc?
              sourceProgram sourcePc
              (dispatcherCode first rest) =
            true
      · simp [hSource] at hCertify
        by_cases hPhysical :
            ReturnAddressProbe.Compact.codeAtPc?
                artifact.physicalSource preparedPc
                (dispatcherCode first rest) =
              true
        · simp [hPhysical] at hCertify
          cases hResolved :
              resolvedStraightFrom?
                artifact.pinnedPushPcs artifact.branchWidth artifact.labels
                (dispatcherStraightCode (first :: rest)) preparedPc with
          | none =>
              simp [hResolved] at hCertify
          | some compactCode =>
              simp [hResolved] at hCertify
              by_cases hNonzero :
                  returnTargetsMappedNonzero?
                      sourceProgram artifact (first :: rest) =
                    true
              · simp [hNonzero] at hCertify
                cases hCertify
                obtain
                    ⟨sourcePre, sourcePost, hSourceProgram, hSourcePc⟩ :=
                  ReturnAddressProbe.Compact.codeAtPc?_sound hSource
                obtain
                    ⟨physicalPre, physicalPost,
                      hPhysicalProgram, hPhysicalPc⟩ :=
                  ReturnAddressProbe.Compact.codeAtPc?_sound hPhysical
                exact
                  { preparation := hPrepared
                    source :=
                      ⟨sourcePre, sourcePost,
                        hSourceProgram, hSourcePc⟩
                    physical :=
                      ⟨physicalPre, physicalPost,
                        hPhysicalProgram, hPhysicalPc⟩
                    resolved := hResolved
                    targets :=
                      returnTargetsMappedNonzero?_sound hNonzero }
              · have hNonzeroFalse :
                    returnTargetsMappedNonzero?
                        sourceProgram artifact (first :: rest) =
                      false :=
                  Bool.eq_false_of_not_eq_true hNonzero
                simp [hNonzeroFalse] at hCertify
        · have hPhysicalFalse :
              ReturnAddressProbe.Compact.codeAtPc?
                  artifact.physicalSource preparedPc
                  (dispatcherCode first rest) =
                false :=
            Bool.eq_false_of_not_eq_true hPhysical
          simp [hPhysicalFalse] at hCertify
      · have hSourceFalse :
            ReturnAddressProbe.Compact.codeAtPc?
                sourceProgram sourcePc
                (dispatcherCode first rest) =
              false :=
          Bool.eq_false_of_not_eq_true hSource
        simp [hSourceFalse] at hCertify

theorem DispatcherLayout.preparedPc_lt_size
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat} {first : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout) :
    layout.preparedPc < EvmYul.UInt256.size := by
  have hLayout := certifyDispatcher?_valid hCertify
  obtain ⟨pre, post, hPhysical, hPreparedPc⟩ :=
    hLayout.physical
  have hTailPos :
      0 < (dispatcherTailCode first.caseLabel).byteLength := by
    exact
      Assembly.Program.byteLength_pos_of_cons
        (.jumpi first.caseLabel)
        [.prim .invalid, .label first.caseLabel, .jumpDynamic]
  have hCodePos :
      0 < (dispatcherCode first rest).byteLength := by
    rw [dispatcherCode, Assembly.Program.byteLength_append]
    omega
  have hPreLt :
      pre.byteLength < artifact.physicalSource.byteLength := by
    rw [hPhysical]
    simp only [Assembly.Program.byteLength_append]
    omega
  have hWholeLt :=
    (ReturnAddressProbe.Compact.compile?_valid
      hCompile).physicalSourcePCFits.byteLength_lt
  rw [hPreparedPc]
  exact Nat.lt_trans hPreLt hWholeLt

structure DispatcherSpec where
  blockLabel : Label
  sourcePc : Nat
  prefixTrace : List Assembly.Compact.PreparationBlock
  first : ReturnSite
  rest : List ReturnSite
  layout : DispatcherLayout

def dispatcherPrefixCode
    (block : TypedCfg.Block) (bodyCode : Assembly.Program)
    (depth : Nat) : Assembly.Program :=
  .label block.label ::
    bodyCode ++
      Assembly.StackShuffle.guardedLiftBuriedToTop depth

theorem dispatcherPrefixCode_height_pos
    (block : TypedCfg.Block) (bodyCode : Assembly.Program)
    (depth height : Nat) (hBound : depth < 16) :
    0 <
      Preparation.simpleHeightRun
        (dispatcherPrefixCode block bodyCode depth) height := by
  simp only [dispatcherPrefixCode, Preparation.simpleHeightRun,
    Preparation.simpleHeightStep]
  rw [Preparation.simpleHeightRun_append]
  exact
    Preparation.simpleHeightRun_guardedLiftBuriedToTop_pos
      depth (Preparation.simpleHeightRun bodyCode height) hBound

def certifyRawBlockDispatcher?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Option (Option DispatcherSpec) :=
  match block.term with
  | .returnDispatch returnCount sites => do
      let (bodyCode, output) ←
        TypedCfg.Block.lowerBodyFrom? block.body block.input
      let _ ← if output = block.output then some () else none
      let depth ← output.returnTokenDepth?
      let _ ←
        if depth = returnCount ∧ depth < 16 then some () else none
      let (first, rest) ←
        match sites with
        | [] => none
        | first :: rest => some (first, rest)
      let entryPc ← sourceProgram.labelPc block.label
      let sourcePc :=
        entryPc + (Assembly.Instr.label block.label).byteSize +
          bodyCode.byteLength +
            (Assembly.StackShuffle.guardedLiftBuriedToTop depth).byteLength
      let prefixTrace ←
        Preparation.simpleTrace? artifact entryPc
          (dispatcherPrefixCode block bodyCode depth)
      let layout ←
        certifyDispatcher? sourceProgram artifact sourcePc first rest
      some
        (some
          { blockLabel := block.label
            sourcePc
            prefixTrace
            first
            rest
            layout })
  | _ =>
      some none

def certifyBlockDispatcher?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Option (Option DispatcherSpec) :=
  match block.term with
  | .returnDispatch _ sites =>
      if sites.length ≤
          LateReturnProbe.Terminator.standardReturnSiteLimit then
        some none
      else
        certifyRawBlockDispatcher? sourceProgram artifact block
  | _ =>
      certifyRawBlockDispatcher? sourceProgram artifact block

def certifyProgramDispatchers?
    (sourceProgram : Assembly.Program) (artifact : Artifact) :
    List TypedCfg.Block → Option (List DispatcherSpec)
  | [] => some []
  | block :: blocks => do
      let current ←
        certifyBlockDispatcher? sourceProgram artifact block
      let rest ←
        certifyProgramDispatchers? sourceProgram artifact blocks
      match current with
      | none => some rest
      | some spec => some (spec :: rest)

def DispatcherSpec.ValidForBlock
    (spec : DispatcherSpec)
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Prop :=
  ∃ returnCount depth entryPc bodyCode output,
    block.term =
        .returnDispatch returnCount (spec.first :: spec.rest) ∧
    TypedCfg.Block.lowerBodyFrom? block.body block.input =
        some (bodyCode, output) ∧
    output = block.output ∧
    output.returnTokenDepth? = some depth ∧
    depth = returnCount ∧
    depth < 16 ∧
    sourceProgram.labelPc block.label = some entryPc ∧
    spec.blockLabel = block.label ∧
    spec.sourcePc =
      entryPc + (Assembly.Instr.label block.label).byteSize +
        bodyCode.byteLength +
          (Assembly.StackShuffle.guardedLiftBuriedToTop depth).byteLength ∧
    Preparation.simpleTrace? artifact entryPc
        (dispatcherPrefixCode block bodyCode depth) =
      some spec.prefixTrace ∧
    certifyDispatcher? sourceProgram artifact spec.sourcePc
        spec.first spec.rest =
      some spec.layout

theorem certifyRawBlockDispatcher?_some_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DispatcherSpec}
    (hCertify :
      certifyRawBlockDispatcher? sourceProgram artifact block =
        some (some spec)) :
    spec.ValidForBlock sourceProgram artifact block := by
  unfold certifyRawBlockDispatcher? at hCertify
  cases hTerm : block.term with
  | fallthrough next | jump next | jumpi next fallback
  | halt next | invalid =>
      simp [hTerm] at hCertify
  | returnDispatch returnCount sites =>
      simp [hTerm] at hCertify
      cases hBody :
          TypedCfg.Block.lowerBodyFrom? block.body block.input with
      | none =>
          simp [hBody] at hCertify
      | some bodyResult =>
          rcases bodyResult with ⟨bodyCode, output⟩
          simp [hBody] at hCertify
          by_cases hOutput : output = block.output
          · subst output
            simp at hCertify
            cases hDepth : block.output.returnTokenDepth? with
            | none =>
                simp [hDepth] at hCertify
            | some depth =>
                simp [hDepth] at hCertify
                by_cases hGate : depth = returnCount ∧ depth < 16
                · simp [hGate] at hCertify
                  cases sites with
                  | nil =>
                      simp at hCertify
                  | cons first rest =>
                      simp at hCertify
                      cases hEntry :
                          sourceProgram.labelPc block.label with
                      | none =>
                          simp [hEntry] at hCertify
                      | some entryPc =>
                          simp [hEntry] at hCertify
                          let sourcePc :=
                            entryPc +
                                (Assembly.Instr.label block.label).byteSize +
                              bodyCode.byteLength +
                                (Assembly.StackShuffle.guardedLiftBuriedToTop
                                  depth).byteLength
                          cases hPrefixTrace :
                              Preparation.simpleTrace? artifact entryPc
                                (dispatcherPrefixCode
                                  block bodyCode depth) with
                          | none =>
                              simp_all [sourcePc]
                          | some prefixTrace =>
                              cases hLayout :
                                  certifyDispatcher? sourceProgram artifact
                                    sourcePc first rest with
                              | none =>
                                  simp_all [sourcePc]
                              | some layout =>
                                  simp_all
                                    [sourcePc,
                                      DispatcherSpec.ValidForBlock]
                                  rcases hCertify with ⟨_, rfl⟩
                                  simp_all
                · have hGateFalse :
                      ¬ (depth = returnCount ∧ depth < 16) :=
                    hGate
                  simp [hGateFalse] at hCertify
          · simp [hOutput] at hCertify

theorem certifyRawBlockDispatcher?_return_ne_none
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {returnCount : Nat}
    {sites : List ReturnSite} {current : Option DispatcherSpec}
    (hTerm :
      block.term = .returnDispatch returnCount sites)
    (hCertify :
      certifyRawBlockDispatcher? sourceProgram artifact block =
        some current) :
    current ≠ none := by
  intro hNone
  subst current
  unfold certifyRawBlockDispatcher? at hCertify
  simp [hTerm] at hCertify
  cases hBody :
      TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hCertify
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      simp [hBody] at hCertify
      by_cases hOutput : output = block.output
      · subst output
        simp at hCertify
        cases hDepth : block.output.returnTokenDepth? with
        | none =>
            simp [hDepth] at hCertify
        | some depth =>
            simp [hDepth] at hCertify
            by_cases hGate : depth = returnCount ∧ depth < 16
            · simp [hGate] at hCertify
              cases sites with
              | nil =>
                  simp at hCertify
              | cons first rest =>
                  simp at hCertify
                  cases hEntry :
                      sourceProgram.labelPc block.label with
                  | none =>
                      simp [hEntry] at hCertify
                  | some entryPc =>
                      simp [hEntry] at hCertify
                      let sourcePc :=
                        entryPc +
                            (Assembly.Instr.label block.label).byteSize +
                          bodyCode.byteLength +
                            (Assembly.StackShuffle.guardedLiftBuriedToTop
                              depth).byteLength
                      cases hPrefixTrace :
                          Preparation.simpleTrace? artifact entryPc
                            (dispatcherPrefixCode
                              block bodyCode depth) with
                      | none =>
                          simp_all [sourcePc]
                      | some prefixTrace =>
                          cases hLayout :
                              certifyDispatcher? sourceProgram artifact
                                sourcePc first rest <;>
                            simp_all [sourcePc]
            · have hGateFalse :
                  ¬ (depth = returnCount ∧ depth < 16) :=
                hGate
              simp [hGateFalse] at hCertify
      · simp [hOutput] at hCertify

theorem certifyBlockDispatcher?_some_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DispatcherSpec}
    (hCertify :
      certifyBlockDispatcher? sourceProgram artifact block =
        some (some spec)) :
    spec.ValidForBlock sourceProgram artifact block := by
  cases hTerm : block.term with
  | returnDispatch returnCount sites =>
      by_cases hSmall :
          sites.length ≤
            LateReturnProbe.Terminator.standardReturnSiteLimit
      · simp [certifyBlockDispatcher?, hTerm, hSmall] at hCertify
      · apply certifyRawBlockDispatcher?_some_valid
        simpa [certifyBlockDispatcher?, hTerm, hSmall] using hCertify
  | fallthrough next | jump next | jumpi next fallback
  | halt kind | invalid =>
      apply certifyRawBlockDispatcher?_some_valid
      simpa [certifyBlockDispatcher?, hTerm] using hCertify

theorem certifyBlockDispatcher?_large_return_ne_none
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {returnCount : Nat}
    {sites : List ReturnSite} {current : Option DispatcherSpec}
    (hTerm :
      block.term = .returnDispatch returnCount sites)
    (hLarge :
      ¬ sites.length ≤
        LateReturnProbe.Terminator.standardReturnSiteLimit)
    (hCertify :
      certifyBlockDispatcher? sourceProgram artifact block =
        some current) :
    current ≠ none := by
  have hRaw :
      certifyRawBlockDispatcher? sourceProgram artifact block =
        some current := by
    simpa [certifyBlockDispatcher?, hTerm, hLarge] using hCertify
  exact
    certifyRawBlockDispatcher?_return_ne_none hTerm hRaw

theorem DispatcherSpec.prefixTrace_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DispatcherSpec}
    (hValid :
      spec.ValidForBlock sourceProgram artifact block) :
    ∃ entryPc,
      sourceProgram.labelPc block.label = some entryPc ∧
        Preparation.SimpleTrace artifact entryPc spec.prefixTrace := by
  unfold DispatcherSpec.ValidForBlock at hValid
  rcases hValid with
    ⟨returnCount, depth, entryPc, bodyCode, output,
      hTerm, hBody, hOutput, hDepth, hCount, hBound,
      hEntry, hBlockLabel, hSourcePc, hTrace, hLayout⟩
  exact
    ⟨entryPc, hEntry,
      Preparation.simpleTrace?_sound hTrace⟩

theorem DispatcherSpec.prefixTrace_length
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DispatcherSpec}
    (hValid :
      spec.ValidForBlock sourceProgram artifact block) :
    ∃ bodyCode depth,
      spec.prefixTrace.length =
        (dispatcherPrefixCode block bodyCode depth).length := by
  unfold DispatcherSpec.ValidForBlock at hValid
  rcases hValid with
    ⟨returnCount, depth, entryPc, bodyCode, output,
      hTerm, hBody, hOutput, hDepth, hCount, hBound,
      hEntry, hBlockLabel, hSourcePc, hTrace, hLayout⟩
  have hLength := Preparation.simpleTrace?_length hTrace
  exact ⟨bodyCode, depth, hLength⟩

theorem DispatcherSpec.sourcePc_lt_size
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : TypedCfg.Block}
    {spec : DispatcherSpec}
    (hCompile :
      ReturnAddressProbe.Compact.compile?
          sourceProgram pinnedPushPcs =
        some artifact)
    (hValid :
      spec.ValidForBlock sourceProgram artifact block) :
    spec.sourcePc < EvmYul.UInt256.size := by
  unfold DispatcherSpec.ValidForBlock at hValid
  rcases hValid with
    ⟨returnCount, depth, entryPc, bodyCode, output,
      hTerm, hBody, hOutput, hDepth, hCount, hBound,
      hEntry, hBlockLabel, hSpecSourcePc, hTrace, hCertify⟩
  have hLayout :=
    certifyDispatcher?_valid hCertify
  obtain ⟨pre, post, hSource, hSourcePc⟩ :=
    hLayout.source
  have hTailPos :
      0 < (dispatcherTailCode spec.first.caseLabel).byteLength := by
    exact
      Assembly.Program.byteLength_pos_of_cons
        (.jumpi spec.first.caseLabel)
        [.prim .invalid, .label spec.first.caseLabel, .jumpDynamic]
  have hCodePos :
      0 < (dispatcherCode spec.first spec.rest).byteLength := by
    rw [dispatcherCode, Assembly.Program.byteLength_append]
    omega
  have hPreLt :
      pre.byteLength < sourceProgram.byteLength := by
    rw [hSource]
    simp only [Assembly.Program.byteLength_append]
    omega
  have hWholeLt :=
    (ReturnAddressProbe.Compact.compile?_valid
      hCompile).sourcePCFits.byteLength_lt
  rw [hSourcePc]
  exact Nat.lt_trans hPreLt hWholeLt

theorem DispatcherSpec.prefix_ready
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact} {block : TypedCfg.Block}
    {spec : DispatcherSpec} {source : EVMState} {entryPc : Nat}
    (hCompile :
      ReturnAddressProbe.Compact.compile?
          sourceProgram pinnedPushPcs =
        some artifact)
    (hValid :
      spec.ValidForBlock sourceProgram artifact block)
    (hEntry :
      sourceProgram.labelPc block.label = some entryPc)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat entryPc) :
    Simulation.Interaction.AllDone
      (fun outcome =>
        match outcome with
        | .ok (Assembly.StepResult.running final) =>
            ∃ token suffix, final.stack = token :: suffix
        | _ => True)
      (Assembly.InteractionSemantics.Source.openRunNResult
        sourceProgram spec.prefixTrace.length source) := by
  unfold DispatcherSpec.ValidForBlock at hValid
  rcases hValid with
    ⟨returnCount, depth, validEntryPc, bodyCode, output,
      hTerm, hBody, hOutput, hDepth, hCount, hBound,
      hValidEntry, hBlockLabel, hSpecSourcePc,
      hTraceCheck, hDispatcherCheck⟩
  have hEntryPcEq : validEntryPc = entryPc := by
    rw [hEntry] at hValidEntry
    exact (Option.some.inj hValidEntry).symm
  subst validEntryPc
  have hHeight :=
    Preparation.simpleTrace?_source_height
      hTraceCheck hCompile hSourcePc
  apply Simulation.Interaction.AllDone.mono hHeight
  intro outcome hOutcome
  cases outcome with
  | error error =>
      trivial
  | ok result =>
      cases result with
      | halted halt =>
          trivial
      | running final =>
          have hPositive :
              0 <
                Preparation.simpleHeightRun
                  (dispatcherPrefixCode block bodyCode depth)
                  source.stack.length :=
            dispatcherPrefixCode_height_pos
              block bodyCode depth source.stack.length hBound
          rw [← hOutcome] at hPositive
          cases hStack : final.stack with
          | nil =>
              simp [hStack] at hPositive
          | cons token suffix =>
              exact ⟨token, suffix, hStack⟩

structure LateArtifactValidFor
    (artifact : LateReturnProbe.Artifact)
    (cfg : TypedCfg.Program) : Prop where
  optimized :
    ReturnAddressProbe.optimizedCfg? cfg = some artifact.cfg
  tokensUnique :
    ReturnAddressLower.Program.tokensUnique? artifact.cfg = true
  localReturnTokensUnique :
    LateReturnProbe.Program.localReturnTokensUnique? artifact.cfg = true
  lowered :
    LateReturnProbe.Program.lower? artifact.cfg =
      some artifact.assembly
  accepted :
    artifact.assembly.acceptedWithDynamic = true
  returnTargetsResolveNonzero :
    LateReturnProbe.Program.returnTargetsResolveNonzero?
        artifact.cfg artifact.assembly =
      true
  compactCompile :
    ReturnAddressProbe.Compact.compile? artifact.assembly =
      some artifact.compact

theorem lateCompileCfg?_valid
    {cfg : TypedCfg.Program} {artifact : LateReturnProbe.Artifact}
    (hCompile :
      LateReturnProbe.compileCfg? cfg = some artifact) :
    LateArtifactValidFor artifact cfg := by
  unfold LateReturnProbe.compileCfg? at hCompile
  obtain ⟨optimized, hOptimized, hAfterOptimized⟩ :=
    Option.bind_eq_some_iff.mp hCompile
  by_cases hUnique :
      (ReturnAddressLower.Program.tokensUnique? optimized &&
        LateReturnProbe.Program.localReturnTokensUnique? optimized) =
        true
  · rw [if_pos hUnique] at hAfterOptimized
    obtain ⟨assembly, hLower, hAfterLower⟩ :=
      Option.bind_eq_some_iff.mp hAfterOptimized
    by_cases hAccepted : assembly.acceptedWithDynamic = true
    · rw [if_pos hAccepted] at hAfterLower
      by_cases hNonzero :
          LateReturnProbe.Program.returnTargetsResolveNonzero?
              optimized assembly =
            true
      · rw [if_pos hNonzero] at hAfterLower
        obtain ⟨compact, hCompact, hFinal⟩ :=
          Option.bind_eq_some_iff.mp hAfterLower
        simp at hFinal
        subst artifact
        have hUniqueParts := Bool.and_eq_true_iff.mp hUnique
        exact
          { optimized := hOptimized
            tokensUnique := hUniqueParts.1
            localReturnTokensUnique := hUniqueParts.2
            lowered := hLower
            accepted := hAccepted
            returnTargetsResolveNonzero := hNonzero
            compactCompile := hCompact }
      · rw [if_neg hNonzero] at hAfterLower
        cases hAfterLower
    · rw [if_neg hAccepted] at hAfterLower
      cases hAfterLower
  · rw [if_neg hUnique] at hAfterOptimized
    cases hAfterOptimized

def DispatcherCoverage
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (blocks : List TypedCfg.Block)
    (specs : List DispatcherSpec) : Prop :=
  ∀ block ∈ blocks, ∀ returnCount sites,
    block.term = .returnDispatch returnCount sites →
      ¬ sites.length ≤
        LateReturnProbe.Terminator.standardReturnSiteLimit →
      ∃ spec, spec ∈ specs ∧
        spec.ValidForBlock sourceProgram artifact block

theorem certifyProgramDispatchers?_coverage
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {blocks : List TypedCfg.Block} {specs : List DispatcherSpec}
    (hCertify :
      certifyProgramDispatchers? sourceProgram artifact blocks =
        some specs) :
    DispatcherCoverage sourceProgram artifact blocks specs := by
  induction blocks generalizing specs with
  | nil =>
      simp [DispatcherCoverage]
  | cons head tail ih =>
      cases hCurrent :
          certifyBlockDispatcher? sourceProgram artifact head with
      | none =>
          simp [certifyProgramDispatchers?, hCurrent] at hCertify
      | some current =>
          cases hRest :
              certifyProgramDispatchers? sourceProgram artifact tail with
          | none =>
              simp [certifyProgramDispatchers?, hCurrent, hRest]
                at hCertify
          | some rest =>
              cases current with
              | none =>
                  simp [certifyProgramDispatchers?, hCurrent, hRest]
                    at hCertify
                  subst specs
                  unfold DispatcherCoverage
                  intro block hMem returnCount sites hTerm hLarge
                  simp only [List.mem_cons] at hMem
                  rcases hMem with hHead | hTail
                  · subst block
                    exact
                      False.elim
                        ((certifyBlockDispatcher?_large_return_ne_none
                            hTerm hLarge hCurrent) rfl)
                  · exact
                      ih hRest block hTail returnCount sites hTerm
                        hLarge
              | some spec =>
                  simp [certifyProgramDispatchers?, hCurrent, hRest]
                    at hCertify
                  subst specs
                  unfold DispatcherCoverage
                  intro block hMem returnCount sites hTerm hLarge
                  simp only [List.mem_cons] at hMem
                  rcases hMem with hHead | hTail
                  · subst block
                    exact
                      ⟨spec, by simp,
                        certifyBlockDispatcher?_some_valid hCurrent⟩
                  · obtain ⟨tailSpec, hTailMem, hTailValid⟩ :=
                      ih hRest block hTail returnCount sites hTerm
                        hLarge
                    exact
                      ⟨tailSpec, by simp [hTailMem], hTailValid⟩

namespace Verified

structure Artifact where
  base : LateReturnProbe.Artifact
  dispatchers : List DispatcherSpec

structure Artifact.ValidFor (artifact : Artifact)
    (cfg : TypedCfg.Program) : Prop where
  baseCompile :
    LateReturnProbe.compileCfg? cfg = some artifact.base
  dispatcherCoverage :
    DispatcherCoverage artifact.base.assembly artifact.base.compact
      artifact.base.cfg.blocks artifact.dispatchers

theorem Artifact.ValidFor.baseValid
    {artifact : Artifact} {cfg : TypedCfg.Program}
    (hValid : artifact.ValidFor cfg) :
    LateArtifactValidFor artifact.base cfg :=
  lateCompileCfg?_valid hValid.baseCompile

def compileCfg? (cfg : TypedCfg.Program) : Option Artifact := do
  let base ← LateReturnProbe.compileCfg? cfg
  let dispatchers ←
    certifyProgramDispatchers?
      base.assembly base.compact base.cfg.blocks
  some { base, dispatchers }

theorem compileCfg?_valid
    {cfg : TypedCfg.Program} {artifact : Artifact}
    (hCompile : compileCfg? cfg = some artifact) :
    artifact.ValidFor cfg := by
  unfold compileCfg? at hCompile
  obtain ⟨base, hBase, hAfterBase⟩ :=
    Option.bind_eq_some_iff.mp hCompile
  obtain ⟨dispatchers, hDispatchers, hFinal⟩ :=
    Option.bind_eq_some_iff.mp hAfterBase
  simp at hFinal
  subst artifact
  exact
    { baseCompile := hBase
      dispatcherCoverage :=
        certifyProgramDispatchers?_coverage hDispatchers }

def compileFunctions? (source : Functions.Program) : Option Artifact := do
  let stack ← Compiler.StackArtifact.compile? source
  compileCfg? stack.cfg

end Verified

/--
Expose the checked compact blocks for a physically contiguous late-return
dispatcher.  This is the structural bridge needed by the whole-block proof:
all byte decoding and execution remains owned by
`lateReturnPhysicalSuffix_openRunNResult`.
-/
theorem dispatcherBlocks_of_physical_decompose
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {first : ReturnSite} {rest : List ReturnSite}
    {pre post : Assembly.Program}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (hPhysical :
      artifact.physicalSource =
        pre ++
          ((LateReturnProbe.Terminator.selectionCode (first :: rest) ++
              Assembly.StackShuffle.removeBuriedUnder 1 ++
              [Assembly.StackShuffle.dupInstr 1]) ++
            ([ .jumpi first.caseLabel
             , .prim .invalid
             , .label first.caseLabel
             , .jumpDynamic
             ] ++ post))) :
    ∃ compactPc blocks,
      ReturnAddressProbe.Compact.BlocksValidFrom
          artifact.pinnedPushPcs artifact.branchWidth artifact.labels
          ((LateReturnProbe.Terminator.selectionCode (first :: rest) ++
              Assembly.StackShuffle.removeBuriedUnder 1 ++
              [Assembly.StackShuffle.dupInstr 1]) ++
            ([ .jumpi first.caseLabel
             , .prim .invalid
             , .label first.caseLabel
             , .jumpDynamic
             ] ++ post))
          pre.byteLength compactPc blocks ∧
        (∀ block ∈ blocks, block ∈ artifact.blocks) := by
  have hGlobal :=
    ReturnAddressProbe.Compact.compile?_blocksValid hCompile
  rw [hPhysical] at hGlobal
  obtain ⟨compactPc, blocks, hSuffix, hSubset⟩ :=
    ReturnAddressProbe.Compact.BlocksValidFrom.drop_prefix pre hGlobal
  exact
    ⟨compactPc, blocks,
      by simpa [List.append_assoc] using hSuffix,
      hSubset⟩

theorem certifiedDispatcher_blocks
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat} {first : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout) :
    ∃ compactPc blocks post,
      ReturnAddressProbe.Compact.BlocksValidFrom
          artifact.pinnedPushPcs artifact.branchWidth artifact.labels
          (dispatcherCode first rest ++ post)
          layout.preparedPc compactPc blocks ∧
        (∀ block ∈ blocks, block ∈ artifact.blocks) := by
  have hLayout := certifyDispatcher?_valid hCertify
  obtain ⟨pre, post, hPhysical, hPreparedPc⟩ :=
    hLayout.physical
  obtain ⟨compactPc, blocks, hBlocks, hSubset⟩ :=
    dispatcherBlocks_of_physical_decompose
      hCompile
      (by
        simpa [dispatcherCode, dispatcherStraightCode,
          dispatcherTailCode, List.append_assoc] using hPhysical)
  exact
    ⟨compactPc, blocks, post,
      by
        simpa [dispatcherCode, dispatcherStraightCode,
          dispatcherTailCode, hPreparedPc, List.append_assoc]
          using hBlocks,
      hSubset⟩

theorem certifiedDispatcher_start_of_full
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat} {first : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout)
    (hFull : Preparation.FullStateRel input artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc)
    (hSourcePcLt : sourcePc < EvmYul.UInt256.size) :
    ∃ compactPc blocks post,
      ReturnAddressProbe.Compact.BlocksValidFrom
          artifact.pinnedPushPcs artifact.branchWidth artifact.labels
          (dispatcherCode first rest ++ post)
          layout.preparedPc compactPc blocks ∧
        (∀ block ∈ blocks, block ∈ artifact.blocks) ∧
        target.pc = EvmYul.UInt256.ofNat compactPc ∧
        Assembly.SameRuntimeData target source := by
  rcases hFull with
    ⟨fullSourcePc, fullPreparedPc, fullCompactSourcePc, fullCompactPc,
      hPreparationBoundary, hCompactBoundary, hPreparedWord,
      hFullSourcePc, hTargetPc, hRuntime⟩
  have hFullSourcePcLt :=
    Preparation.preparationBoundarySourcePc_lt_size
      hCompile hPreparationBoundary
  have hSourceWord :
      EvmYul.UInt256.ofNat fullSourcePc =
        EvmYul.UInt256.ofNat sourcePc :=
    hFullSourcePc.symm.trans hSourcePc
  have hSourceEq : fullSourcePc = sourcePc :=
    Preparation.ofNat_eq_of_lt
      hFullSourcePcLt hSourcePcLt hSourceWord
  subst fullSourcePc
  have hLayout := certifyDispatcher?_valid hCertify
  have hCertifiedPreparation :=
    Assembly.Compact.preparationBoundaryPair_of_targetPc?
      hLayout.preparation
  have hPreparationValid :=
    ReturnAddressProbe.Compact.compile?_preparationBlocksValid hCompile
  have hPreparedEq : fullPreparedPc = layout.preparedPc := by
    apply Preparation.preparationBoundaryPair_preparedPc_unique
      hPreparationValid
    · simpa using hPreparationBoundary
    · simpa using hCertifiedPreparation
  have hLayoutPreparedLt :=
    DispatcherLayout.preparedPc_lt_size hCompile hCertify
  have hFullCompactSourceLt :=
    Preparation.compactBoundarySourcePc_lt_size
      hCompile hCompactBoundary
  have hPreparedCompactEq :
      layout.preparedPc = fullCompactSourcePc := by
    apply Preparation.ofNat_eq_of_lt
      hLayoutPreparedLt hFullCompactSourceLt
    simpa [hPreparedEq] using hPreparedWord
  obtain ⟨compactPc, blocks, post, hBlocks, hSubset⟩ :=
    certifiedDispatcher_blocks hCompile hCertify
  have hCertifiedCompactBoundary :
      Assembly.Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Assembly.Compact.Program.codeByteLength artifact.program.code)
        layout.preparedPc compactPc := by
    have hInitial :=
      Preparation.blocksValidFrom_initial_boundary hBlocks
    rcases hInitial with hBlock | hEnd
    · rcases hBlock with
        ⟨block, hBlock, hBlockSource, hBlockCompact⟩
      exact
        Or.inl
          ⟨block, hSubset block hBlock,
            hBlockSource, hBlockCompact⟩
    · have hTailPos :
          0 < (dispatcherTailCode first.caseLabel).byteLength := by
        exact
          Assembly.Program.byteLength_pos_of_cons
            (.jumpi first.caseLabel)
            [.prim .invalid, .label first.caseLabel, .jumpDynamic]
      have hCodePos :
          0 < (dispatcherCode first rest ++ post).byteLength := by
        rw [Assembly.Program.byteLength_append,
          dispatcherCode, Assembly.Program.byteLength_append]
        omega
      exact False.elim (by omega)
  have hFullCompactBoundary :
      Assembly.Compact.BoundaryPair artifact.blocks
        artifact.physicalSource.byteLength
        (Assembly.Compact.Program.codeByteLength artifact.program.code)
        layout.preparedPc fullCompactPc := by
    simpa [hPreparedCompactEq] using hCompactBoundary
  have hGlobalBlocks :=
    ReturnAddressProbe.Compact.compile?_blocksValid hCompile
  have hCompactEq : fullCompactPc = compactPc := by
    apply Preparation.boundaryPair_compactPc_unique hGlobalBlocks
    · simpa using hFullCompactBoundary
    · simpa using hCertifiedCompactBoundary
  exact
    ⟨compactPc, blocks, post, hBlocks, hSubset,
      by simpa [hCompactEq] using hTargetPc,
      hRuntime⟩

set_option maxHeartbeats 1000000 in
theorem certifiedSourceDispatcher_openRunUntilTransfer
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat} {first : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    {source : EVMState} {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout)
    (hLabels : input.labels.Nodup)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc)
    (hSourceStack : source.stack = token :: suffix) :
    let destination :=
      LateReturnPreservation.selectedAddressSum
        input.labelPc token (first :: rest)
    ∃ final,
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input (dispatcherCode first rest).length source =
        if destination = EvmYul.UInt256.ofNat 0 then
          .done (.error .InvalidInstruction)
        else
          .done (.ok (.running final))) ∧
      final.pc = destination ∧
      final.stack = suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl { source with stack := suffix } := by
  have hLayout := certifyDispatcher?_valid hCertify
  obtain ⟨pre, post, hInput, hPrePc⟩ := hLayout.source
  let selection :=
    LateReturnProbe.Terminator.selectionCode (first :: rest)
  let remove := Assembly.StackShuffle.removeBuriedUnder 1
  let tail : Assembly.Program :=
    [ Assembly.StackShuffle.dupInstr 1
    , .jumpi first.caseLabel
    , .prim .invalid
    , .label first.caseLabel
    , .jumpDynamic
    ]
  let code := dispatcherCode first rest
  let destination :=
    LateReturnPreservation.selectedAddressSum
      input.labelPc token (first :: rest)
  have hCodeEq :
      code = selection ++ remove ++ tail := by
    simp [code, selection, remove, tail, dispatcherCode,
      dispatcherStraightCode, dispatcherTailCode,
      List.append_assoc]
  have hFits :
      Assembly.Program.PCFitsFrom pre code := by
    have hWholeFits :=
      (ReturnAddressProbe.Compact.compile?_valid hCompile).sourcePCFits
    rw [hInput] at hWholeFits
    exact
      Assembly.Program.PCFitsFrom.of_append
        (pre := pre) (code := code) (post := post)
        (by simpa using hWholeFits)
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (selection ++ remove ++ tail) := by
    simpa [hCodeEq] using hFits
  have hSelectionFits :
      Assembly.Program.PCFitsFrom pre selection := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [List.append_assoc] using hFitsAll
  have hAfterSelectionFits :
      Assembly.Program.PCFitsFrom
        (pre ++ selection) (remove ++ tail) := by
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right
        (by simpa [List.append_assoc] using hFitsAll))
  have hRemoveFits :
      Assembly.Program.PCFitsFrom
        (pre ++ selection) remove :=
    Assembly.Program.PCFitsFrom.left hAfterSelectionFits
  have hTailFits :
      Assembly.Program.PCFitsFrom
        (pre ++ selection ++ remove) tail := by
    simpa [List.append_assoc] using
      (Assembly.Program.PCFitsFrom.right hAfterSelectionFits)
  have hSourceRecord :
      { source with stack := token :: suffix } = source := by
    cases source
    simpa using hSourceStack.symm
  have hStartPc :
      ({ source with stack := token :: suffix }).pc =
        pre.pcAfter := by
    rw [hSourceRecord, hSourcePc, hPrePc]
    rfl
  have hResolved :
      ∀ site ∈ first :: rest,
        ∃ dest,
          (pre ++ selection ++
              (remove ++ tail ++ post)).labelPc site.target =
            some dest := by
    intro site hSite
    obtain
        ⟨sourceDest, _preparedDest, _compactDest,
          hSourceDest, _hPreparedDest, _hPreparationDest,
          _hCompactDest, _hNonzero⟩ :=
      hLayout.targets site hSite
    exact
      ⟨sourceDest,
        by
          simpa [hInput, code, hCodeEq, List.append_assoc]
            using hSourceDest⟩
  obtain
      ⟨selected, hSelectionRun, hSelectedStack,
        hSelectedRuntime, hSelectedPc⟩ :=
    LateReturnPreservation.selectionCode_source_run
      (state := source) (token := token) (suffix := suffix)
      (first := first) (rest := rest)
      (pre := pre) (post := remove ++ tail ++ post)
      (by simpa [selection] using hSelectionFits)
      hStartPc
      (by
        intro site hSite
        simpa [selection, List.append_assoc] using
          hResolved site hSite)
  have hSelectionRun' :
      Assembly.Source.runNResult
          (pre ++ selection ++ (remove ++ tail ++ post))
          selection.length source =
        .ok (.running selected) := by
    rw [← hSourceRecord]
    simpa [selection, List.append_assoc] using hSelectionRun
  have hSelectionOpenRaw :=
    ReturnAddressPreservation.returnGuardCode_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (code := selection) (pre := pre)
      (post := remove ++ tail ++ post)
      (state := source) (final := selected)
      (5 + remove.length)
      (by
        intro instr hInstr
        exact
          LateReturnPreservation.selectionCode_returnGuard
            (first :: rest) instr
            (by simpa [selection] using hInstr))
      hSelectionFits
      (by simpa [hPrePc] using hSourcePc)
      hSelectionRun'
  have hSelectionOpen :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input ((5 + remove.length) + selection.length) source =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input (5 + remove.length) selected := by
    simpa [hInput, code, hCodeEq, List.append_assoc] using
      hSelectionOpenRaw
  have hSelectedStack' :
      selected.stack = destination :: token :: suffix := by
    simpa [destination, hInput, code, hCodeEq, selection,
      List.append_assoc] using hSelectedStack
  have hSelectedPc' :
      selected.pc = (pre ++ selection).pcAfter := by
    simpa [selection] using hSelectedPc
  have hSelectedRecord :
      { selected with stack := destination :: token :: suffix } =
        selected := by
    cases selected
    simpa using hSelectedStack'.symm
  let tested : EVMState :=
    { selected with
      stack := destination :: suffix
      pc := (pre ++ selection ++ remove).pcAfter }
  let final : EVMState :=
    { tested with stack := suffix, pc := destination }
  have hRemoveRaw :=
    Assembly.StackShuffle.InteractionPreservation.removeBuriedUnder_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (front := [destination]) (suffix := suffix)
      (token := token)
      (pre := pre ++ selection) (post := tail ++ post)
      (state := selected) (fuel := 5)
      (by simpa [remove] using hRemoveFits)
      (by simpa [hSelectedRecord] using hSelectedPc')
      (by simp)
  have hRemoveOpen :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input (5 + remove.length) selected =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input 5 tested := by
    have hRemove := hRemoveRaw
    simp only [List.length_singleton, List.singleton_append] at hRemove
    rw [hSelectedRecord] at hRemove
    simpa [hInput, code, hCodeEq, remove, tested,
      List.append_assoc] using hRemove
  have hTailRaw :=
    LateReturnPreservation.lateReturnTail_openRunUntilTransferWithPolicy
      (caseLabel := first.caseLabel)
      (destination := destination) (suffix := suffix)
      (pre := pre ++ selection ++ remove) (post := post)
      (state := tested)
      (by simpa [tail] using hTailFits)
      (by simp [tested])
      (by
        simpa [hInput, code, hCodeEq, tail,
          List.append_assoc] using hLabels)
  have hTail :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input 5 tested =
        if destination = EvmYul.UInt256.ofNat 0 then
          .done (.error .InvalidInstruction)
        else
          .done (.ok (.running final)) := by
    have hTail' :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            input 5
            { tested with stack := destination :: suffix } =
          if destination = EvmYul.UInt256.ofNat 0 then
            .done (.error .InvalidInstruction)
          else
            .done
              (.ok
                (.running
                  { tested with
                    stack := suffix
                    pc := destination })) := by
      simpa [hInput, code, hCodeEq, tail,
        List.append_assoc] using hTailRaw
    have hTestedRecord :
        { tested with stack := destination :: suffix } = tested := by
      rfl
    rw [hTestedRecord] at hTail'
    simpa [final] using hTail'
  have hFinalRuntime :
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl { source with stack := suffix } := by
    have hSelectedRuntime' :
        Assembly.eraseRuntimeControl selected =
          Assembly.eraseRuntimeControl
            { source with
              stack := destination :: token :: suffix } := by
      simpa [destination, hInput, code, hCodeEq, selection,
        List.append_assoc] using hSelectedRuntime
    calc
      Assembly.eraseRuntimeControl final =
          Assembly.eraseRuntimeControl
            { selected with stack := suffix } := by
        simp [final, tested, Assembly.eraseRuntimeControl]
      _ =
          Assembly.eraseRuntimeControl
            { source with stack := suffix } := by
        exact
          Assembly.eraseRuntimeControl_with_stack_congr
            (left := selected)
            (right :=
              { source with
                stack := destination :: token :: suffix })
            (stack := suffix)
            hSelectedRuntime'
  have hLength :
      code.length = (5 + remove.length) + selection.length := by
    rw [hCodeEq]
    simp [tail]
    omega
  refine
    ⟨final, ?_,
      by simp [final, destination],
      by simp [final],
      hFinalRuntime⟩
  rw [show dispatcherCode first rest = code by rfl, hLength]
  exact hSelectionOpen.trans (hRemoveOpen.trans hTail)

theorem certifiedDispatcher_openRunNResult
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc compactPc : Nat}
    {first selected : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    {post : Assembly.Program} {blocks : List SourceBlock}
    {target source : EVMState} {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout)
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        artifact.pinnedPushPcs artifact.branchWidth artifact.labels
        (dispatcherCode first rest ++ post)
        layout.preparedPc compactPc blocks)
    (hSubset : ∀ block ∈ blocks, block ∈ artifact.blocks)
    (hUnique :
      ReturnAddressRelation.TokensUnique (first :: rest))
    (hSelected : selected ∈ first :: rest)
    (hToken : selected.token = token)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat compactPc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (hSourceStack : source.stack = token :: suffix) :
    ∃ destination final,
      Assembly.Compact.lookupLabel? artifact.labels selected.target =
          some destination ∧
      Assembly.Compact.InteractionSemantics.openRunNResult
          (Assembly.Bytecode.ofList
            (artifact.bytes.toList ++ byteSuffix))
          (layout.compactCode.length + 4) target =
        .done (.ok (.running final)) ∧
      final.pc = EvmYul.UInt256.ofNat destination ∧
      final.stack = suffix ∧
      Assembly.eraseRuntimeControl final =
        Assembly.eraseRuntimeControl { source with stack := suffix } := by
  have hLayout := certifyDispatcher?_valid hCertify
  obtain
      ⟨_sourceDest, _preparedDest, destination,
        _hSourceDestination, _hPreparedDestination,
        _hPreparationDestination, hDestination,
        hDestinationNonzero⟩ :=
    hLayout.targets selected hSelected
  have hSelectedSum :
      LateReturnPreservation.selectedAddressSum
          (Assembly.Compact.lookupLabel? artifact.labels)
          token (first :: rest) =
        EvmYul.UInt256.ofNat destination := by
    exact
      LateReturnPreservation.selectedAddressSum_eq_of_unique
        hUnique hSelected hToken hDestination
  have hNonzero :
      LateReturnPreservation.selectedAddressSum
          (Assembly.Compact.lookupLabel? artifact.labels)
          token (first :: rest) ≠
        EvmYul.UInt256.ofNat 0 := by
    rw [hSelectedSum]
    exact hDestinationNonzero
  obtain ⟨final, hRun, hFinalPc, hFinalStack, hFinalRuntime⟩ :=
    lateReturnPhysicalSuffix_openRunNResult
      hCompile byteSuffix
      (by
        simpa [dispatcherCode, dispatcherStraightCode,
          dispatcherTailCode, List.append_assoc] using hValid)
      hSubset
      (by
        simpa [dispatcherStraightCode] using hLayout.resolved)
      hTargetPc hRuntime hSourceStack hNonzero
  exact
    ⟨destination, final, hDestination, hRun,
      by simpa [hSelectedSum] using hFinalPc,
      hFinalStack, hFinalRuntime⟩

theorem certifiedDispatcher_rejected_openRunNResult
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc compactPc : Nat}
    {first : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    {post : Assembly.Program} {blocks : List SourceBlock}
    {target source : EVMState} {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout)
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        artifact.pinnedPushPcs artifact.branchWidth artifact.labels
        (dispatcherCode first rest ++ post)
        layout.preparedPc compactPc blocks)
    (hSubset : ∀ block ∈ blocks, block ∈ artifact.blocks)
    (hAllNe :
      ∀ site ∈ first :: rest, site.token ≠ token)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat compactPc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (hSourceStack : source.stack = token :: suffix) :
    Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        (layout.compactCode.length + 4) target =
      .done (.error .InvalidInstruction) := by
  have hLayout := certifyDispatcher?_valid hCertify
  have hZero :
      LateReturnPreservation.selectedAddressSum
          (Assembly.Compact.lookupLabel? artifact.labels)
          token (first :: rest) =
        EvmYul.UInt256.ofNat 0 :=
    LateReturnPreservation.selectedAddressSum_eq_zero_of_all_ne
      (Assembly.Compact.lookupLabel? artifact.labels)
      token (first :: rest) hAllNe
  exact
    lateReturnPhysicalSuffix_rejected_openRunNResult
      hCompile byteSuffix
      (by
        simpa [dispatcherCode, dispatcherStraightCode,
          dispatcherTailCode, List.append_assoc] using hValid)
      hSubset
      (by
        simpa [dispatcherStraightCode] using hLayout.resolved)
      hTargetPc hRuntime hSourceStack hZero

theorem certifiedDispatcher_openRunNResult_full
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc compactPc : Nat}
    {first selected : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    {post : Assembly.Program} {blocks : List SourceBlock}
    {target source : EVMState} {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout)
    (hValid :
      ReturnAddressProbe.Compact.BlocksValidFrom
        artifact.pinnedPushPcs artifact.branchWidth artifact.labels
        (dispatcherCode first rest ++ post)
        layout.preparedPc compactPc blocks)
    (hSubset : ∀ block ∈ blocks, block ∈ artifact.blocks)
    (hUnique :
      ReturnAddressRelation.TokensUnique (first :: rest))
    (hSelected : selected ∈ first :: rest)
    (hToken : selected.token = token)
    (hTargetPc : target.pc = EvmYul.UInt256.ofNat compactPc)
    (hRuntime : Assembly.SameRuntimeData target source)
    (hSourceStack : source.stack = token :: suffix) :
    ∃ sourceDest preparedDest compactDest final,
      input.labelPc selected.target = some sourceDest ∧
      artifact.physicalSource.labelPc selected.target =
        some preparedDest ∧
      Assembly.Compact.lookupLabel? artifact.labels selected.target =
        some compactDest ∧
      Assembly.Compact.InteractionSemantics.openRunNResult
          (Assembly.Bytecode.ofList
            (artifact.bytes.toList ++ byteSuffix))
          (layout.compactCode.length + 4) target =
        .done (.ok (.running final)) ∧
      Preparation.FullStateRel input artifact final
        { source with
          stack := suffix
          pc := EvmYul.UInt256.ofNat sourceDest } := by
  have hLayout := certifyDispatcher?_valid hCertify
  obtain
      ⟨sourceDest, preparedDest, compactDest,
        hSourceDestination, hPreparedDestination,
        hPreparationDestination, hCompactDestination,
        _hCompactNonzero⟩ :=
    hLayout.targets selected hSelected
  obtain
      ⟨destination, final, hDestination, hRun,
        hFinalPc, hFinalStack, hFinalRuntime⟩ :=
    certifiedDispatcher_openRunNResult
      hCompile byteSuffix hCertify hValid hSubset hUnique hSelected hToken
      hTargetPc hRuntime hSourceStack
  have hDestinationEq : destination = compactDest := by
    rw [hCompactDestination] at hDestination
    exact (Option.some.inj hDestination).symm
  subst destination
  have hPreparationBoundary :=
    Assembly.Compact.preparationBoundaryPair_of_targetPc?
      hPreparationDestination
  have hCompactBoundary :=
    ReturnAddressProbe.Compact.compile?_label_boundary
      hCompile hPreparedDestination hCompactDestination
  have hFinalRuntime' :
      Assembly.SameRuntimeData final
        { source with
          stack := suffix
          pc := EvmYul.UInt256.ofNat sourceDest } := by
    simpa [Assembly.SameRuntimeData,
      Assembly.eraseRuntimeControl] using hFinalRuntime
  exact
    ⟨sourceDest, preparedDest, compactDest, final,
      hSourceDestination, hPreparedDestination,
      hCompactDestination, hRun,
      ⟨sourceDest, preparedDest, preparedDest, compactDest,
        hPreparationBoundary, hCompactBoundary, rfl, rfl,
        hFinalPc, hFinalRuntime'⟩⟩

theorem certifiedDispatcher_from_full
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat}
    {first selected : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    {target source : EVMState} {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout)
    (hFull : Preparation.FullStateRel input artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc)
    (hSourcePcLt : sourcePc < EvmYul.UInt256.size)
    (hUnique :
      ReturnAddressRelation.TokensUnique (first :: rest))
    (hSelected : selected ∈ first :: rest)
    (hToken : selected.token = token)
    (hSourceStack : source.stack = token :: suffix) :
    ∃ sourceDest preparedDest compactDest final,
      input.labelPc selected.target = some sourceDest ∧
      artifact.physicalSource.labelPc selected.target =
        some preparedDest ∧
      Assembly.Compact.lookupLabel? artifact.labels selected.target =
        some compactDest ∧
      Assembly.Compact.InteractionSemantics.openRunNResult
          (Assembly.Bytecode.ofList
            (artifact.bytes.toList ++ byteSuffix))
          (layout.compactCode.length + 4) target =
        .done (.ok (.running final)) ∧
      Preparation.FullStateRel input artifact final
        { source with
          stack := suffix
          pc := EvmYul.UInt256.ofNat sourceDest } := by
  obtain
      ⟨compactPc, blocks, post, hBlocks, hSubset,
        hTargetPc, hRuntime⟩ :=
    certifiedDispatcher_start_of_full
      hCompile hCertify hFull hSourcePc hSourcePcLt
  exact
    certifiedDispatcher_openRunNResult_full
      hCompile byteSuffix hCertify hBlocks hSubset hUnique hSelected hToken
      hTargetPc hRuntime hSourceStack

theorem certifiedDispatcher_rejected_from_full
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat}
    {first : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    {target source : EVMState} {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout)
    (hFull : Preparation.FullStateRel input artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc)
    (hSourcePcLt : sourcePc < EvmYul.UInt256.size)
    (hAllNe :
      ∀ site ∈ first :: rest, site.token ≠ token)
    (hSourceStack : source.stack = token :: suffix) :
    Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        (layout.compactCode.length + 4) target =
      .done (.error .InvalidInstruction) := by
  obtain
      ⟨compactPc, blocks, post, hBlocks, hSubset,
        hTargetPc, hRuntime⟩ :=
    certifiedDispatcher_start_of_full
      hCompile hCertify hFull hSourcePc hSourcePcLt
  exact
    certifiedDispatcher_rejected_openRunNResult
      hCompile byteSuffix hCertify hBlocks hSubset hAllNe
      hTargetPc hRuntime hSourceStack

set_option maxHeartbeats 1000000 in
theorem certifiedDispatcher_openRunUntilTransfer_rel
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {sourcePc : Nat}
    {first : ReturnSite} {rest : List ReturnSite}
    {layout : DispatcherLayout}
    {target source : EVMState} {token : Word} {suffix : List Word}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hCertify :
      certifyDispatcher? input artifact sourcePc first rest =
        some layout)
    (hFull : Preparation.FullStateRel input artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat sourcePc)
    (hSourcePcLt : sourcePc < EvmYul.UInt256.size)
    (hUnique :
      ReturnAddressRelation.TokensUnique (first :: rest))
    (hLabels : input.labels.Nodup)
    (hSourceTargetsNonzero :
      ∀ site ∈ first :: rest,
        ∃ dest,
          input.labelPc site.target = some dest ∧
            EvmYul.UInt256.ofNat dest ≠
              EvmYul.UInt256.ofNat 0)
    (hSourceStack : source.stack = token :: suffix) :
    Simulation.Interaction.Rel
      (Preparation.FullOutcomeRel input artifact)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        (layout.compactCode.length + 4) target)
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        input (dispatcherCode first rest).length source) := by
  obtain
      ⟨sourceFinal, hSourceRun, hSourceFinalPc,
        hSourceFinalStack, hSourceFinalRuntime⟩ :=
    certifiedSourceDispatcher_openRunUntilTransfer
      hCompile hCertify hLabels hSourcePc hSourceStack
  cases hFind :
      TypedCfg.Block.ReturnSite.findTarget?
        token (first :: rest) with
  | none =>
      have hAllNe :
          ∀ site ∈ first :: rest, site.token ≠ token :=
        TypedCfg.Preservation.ReturnSite.findTarget?_eq_none_all_ne
          hFind
      have hZero :
          LateReturnPreservation.selectedAddressSum
              input.labelPc token (first :: rest) =
            EvmYul.UInt256.ofNat 0 :=
        LateReturnPreservation.selectedAddressSum_eq_zero_of_all_ne
          input.labelPc token (first :: rest) hAllNe
      have hTargetRun :=
        certifiedDispatcher_rejected_from_full
          hCompile byteSuffix hCertify hFull hSourcePc hSourcePcLt
          hAllNe hSourceStack
      rw [hTargetRun, hSourceRun, hZero]
      exact .done (.error rfl)
  | some targetLabel =>
      obtain
          ⟨selected, hSelectedMem,
            hSelectedToken, hSelectedTarget⟩ :=
        TypedCfg.Block.ReturnSite.mem_token_of_findTarget?_eq_some
          hFind
      obtain
          ⟨sourceDest, hSourceDest, hSourceDestNonzero⟩ :=
        hSourceTargetsNonzero selected hSelectedMem
      have hDestination :
          LateReturnPreservation.selectedAddressSum
              input.labelPc token (first :: rest) =
            EvmYul.UInt256.ofNat sourceDest := by
        exact
          LateReturnPreservation.selectedAddressSum_eq_of_unique
            hUnique hSelectedMem hSelectedToken hSourceDest
      obtain
          ⟨certifiedSourceDest, preparedDest, compactDest,
            targetFinal, hCertifiedSourceDest, hPreparedDest,
            hCompactDest, hTargetRun, hTargetFull⟩ :=
        certifiedDispatcher_from_full
          hCompile byteSuffix hCertify hFull hSourcePc hSourcePcLt
          hUnique hSelectedMem hSelectedToken hSourceStack
      have hSourceDestEq :
          certifiedSourceDest = sourceDest := by
        rw [hSourceDest] at hCertifiedSourceDest
        exact (Option.some.inj hCertifiedSourceDest).symm
      subst certifiedSourceDest
      have hLogicalSource :
          Assembly.SameRuntimeData
            { source with
              stack := suffix
              pc := EvmYul.UInt256.ofNat sourceDest }
            sourceFinal := by
        unfold Assembly.SameRuntimeData
        calc
          Assembly.eraseRuntimeControl
              { source with
                stack := suffix
                pc := EvmYul.UInt256.ofNat sourceDest } =
              Assembly.eraseRuntimeControl
                { source with stack := suffix } := by
            rfl
          _ = Assembly.eraseRuntimeControl sourceFinal :=
            hSourceFinalRuntime.symm
      rcases hTargetFull with
        ⟨fullSourcePc, fullPreparedPc,
          fullCompactSourcePc, fullCompactPc,
          hPreparationBoundary, hCompactBoundary,
          hPreparedWord, hLogicalPc, hTargetPc,
          hTargetRuntime⟩
      have hSourceFinalPc' :
          sourceFinal.pc =
            EvmYul.UInt256.ofNat fullSourcePc := by
        calc
          sourceFinal.pc =
              LateReturnPreservation.selectedAddressSum
                input.labelPc token (first :: rest) :=
            hSourceFinalPc
          _ = EvmYul.UInt256.ofNat sourceDest := hDestination
          _ =
              ({ source with
                stack := suffix
                pc := EvmYul.UInt256.ofNat sourceDest } : EVMState).pc := by
            rfl
          _ = EvmYul.UInt256.ofNat fullSourcePc := hLogicalPc
      have hFinalFull :
          Preparation.FullStateRel input artifact
            targetFinal sourceFinal :=
        ⟨fullSourcePc, fullPreparedPc,
          fullCompactSourcePc, fullCompactPc,
          hPreparationBoundary, hCompactBoundary,
          hPreparedWord, hSourceFinalPc', hTargetPc,
          Assembly.SameRuntimeData.trans
            hTargetRuntime hLogicalSource⟩
      rw [hTargetRun, hSourceRun, hDestination,
        if_neg hSourceDestNonzero]
      exact .done (.ok hFinalFull)

set_option maxHeartbeats 1000000 in
theorem certifiedReturnBlock_openRun_rel
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DispatcherSpec}
    {target source : EVMState} {entryPc : Nat}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hValid :
      spec.ValidForBlock input artifact block)
    (hFull : Preparation.FullStateRel input artifact target source)
    (hEntry :
      input.labelPc block.label = some entryPc)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat entryPc)
    (hUnique :
      ReturnAddressRelation.TokensUnique
        (spec.first :: spec.rest))
    (hLabels : input.labels.Nodup)
    (hSourceTargetsNonzero :
      ∀ site ∈ spec.first :: spec.rest,
        ∃ dest,
          input.labelPc site.target = some dest ∧
            EvmYul.UInt256.ofNat dest ≠
              EvmYul.UInt256.ofNat 0) :
    Simulation.Interaction.Rel
      (Preparation.FullOutcomeRel input artifact)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        (Preparation.SimpleTrace.targetFuel spec.prefixTrace +
          (spec.layout.compactCode.length + 4))
        target)
      (do
        let prefixResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            input spec.prefixTrace.length source
        match prefixResult with
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              input (dispatcherCode spec.first spec.rest).length mid
        | .halted halt =>
            pure (.halted halt)) := by
  have hSourcePcLt :=
    spec.sourcePc_lt_size hCompile hValid
  have hReady :=
    spec.prefix_ready hCompile hValid hEntry hSourcePc
  unfold DispatcherSpec.ValidForBlock at hValid
  rcases hValid with
    ⟨returnCount, depth, validEntryPc, bodyCode, output,
      hTerm, hBody, hOutput, hDepth, hCount, hBound,
      hValidEntry, hBlockLabel, hSpecSourcePc,
      hTraceCheck, hDispatcherCheck⟩
  have hEntryPcEq : validEntryPc = entryPc := by
    rw [hEntry] at hValidEntry
    exact (Option.some.inj hValidEntry).symm
  subst validEntryPc
  have hTrace :=
    Preparation.simpleTrace?_sound hTraceCheck
  have hTraceBytes :=
    Preparation.simpleTrace?_sourceByteLength hTraceCheck
  have hPrefixRel :=
    hTrace.openRunNResult_rel
      hCompile byteSuffix hFull hSourcePc
  have hPrefixEndRaw :=
    hTrace.source_runningAt_end hCompile hSourcePc
  have hPrefixEnd :
      Simulation.Interaction.AllDone
        (Assembly.Compact.RunningAt
          (EvmYul.UInt256.ofNat spec.sourcePc))
        (Assembly.InteractionSemantics.Source.openRunNResult
          input spec.prefixTrace.length source) := by
    have hPrefixBytes :
        entryPc +
            Preparation.SimpleTrace.sourceByteLength spec.prefixTrace =
          spec.sourcePc := by
      rw [hTraceBytes, hSpecSourcePc]
      simp [dispatcherPrefixCode,
        Assembly.Program.byteLength_cons,
        Assembly.Program.byteLength_append]
      omega
    simpa [hPrefixBytes] using hPrefixEndRaw
  have hPrefixFacts :=
    Simulation.Interaction.AllDone.inter hPrefixEnd hReady
  have hPrefixStrong :=
    Simulation.Interaction.Rel.strengthen_right
      hPrefixRel hPrefixFacts
  rw [
    Assembly.Compact.InteractionSemantics.openRunNResult_add]
  apply Simulation.Interaction.Rel.bind_custom hPrefixStrong
  intro targetDone sourceDone hDone
  rcases hDone with ⟨hRelated, hEnd, hReadyDone⟩
  cases hRelated with
  | error hError =>
      exact .done (.error hError)
  | ok hResult =>
      rename_i targetResult sourceResult
      cases targetResult with
      | halted targetHalt =>
          cases sourceResult with
          | running sourceMid =>
              simp [Preparation.FullStepResultRel] at hResult
          | halted sourceHalt =>
              exact .done (.ok hResult)
      | running targetMid =>
          cases sourceResult with
          | halted sourceHalt =>
              simp [Preparation.FullStepResultRel] at hResult
          | running sourceMid =>
              change
                Preparation.FullStateRel input artifact
                  targetMid sourceMid at hResult
              change
                sourceMid.pc =
                  EvmYul.UInt256.ofNat spec.sourcePc at hEnd
              rcases hReadyDone with
                ⟨token, suffix, hSourceStack⟩
              have hDispatcher :=
                certifiedDispatcher_openRunUntilTransfer_rel
                  hCompile byteSuffix hDispatcherCheck hResult hEnd
                  hSourcePcLt
                  hUnique hLabels hSourceTargetsNonzero hSourceStack
              simpa [Assembly.Bytecode.ofList] using hDispatcher

set_option maxHeartbeats 1000000 in
theorem certifiedReturnBlock_sourceRun_eq_compiled
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DispatcherSpec}
    {code pre post : Assembly.Program} {source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (hValid :
      spec.ValidForBlock input artifact block)
    (hLower :
      LateReturnProbe.Block.lower? block = some code)
    (hInput : input = pre ++ code ++ post)
    (hStart : source.pc = pre.pcAfter)
    (hLarge :
      ¬ (spec.first :: spec.rest).length ≤
        LateReturnProbe.Terminator.standardReturnSiteLimit) :
    (do
      let prefixResult ←
        Assembly.InteractionSemantics.Source.openRunNResult
          input spec.prefixTrace.length source
      match prefixResult with
      | .running mid =>
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            input (dispatcherCode spec.first spec.rest).length mid
      | .halted halt =>
          pure (.halted halt)) =
      LateReturnProbe.CompiledBlock.openRun
        block input source := by
  unfold DispatcherSpec.ValidForBlock at hValid
  rcases hValid with
    ⟨returnCount, depth, entryPc, bodyCode, output,
      hTerm, hBody, hOutput, hDepth, hCount, hBound,
      hEntry, hBlockLabel, hSpecSourcePc,
      hTraceCheck, hDispatcherCheck⟩
  subst returnCount
  let before : Assembly.Program :=
    .label block.label :: bodyCode
  let guard : Assembly.Program :=
    Assembly.StackShuffle.guardedLiftBuriedToTop depth
  let dispatcher : Assembly.Program :=
    dispatcherCode spec.first spec.rest
  let prefixCode : Assembly.Program :=
    dispatcherPrefixCode block bodyCode depth
  have hPrefixEq : prefixCode = before ++ guard := by
    simp [prefixCode, before, guard, dispatcherPrefixCode,
      List.append_assoc]
  have hDynamicEq :
      LateReturnProbe.Terminator.dynamicReturnCode
          depth (spec.first :: spec.rest) =
        guard ++ dispatcher := by
    simp [guard, dispatcher,
      LateReturnProbe.Terminator.dynamicReturnCode,
      dispatcherCode, dispatcherStraightCode,
      dispatcherTailCode, List.append_assoc]
  have hLarge' :
      ¬ spec.rest.length + 1 ≤
        LateReturnProbe.Terminator.standardReturnSiteLimit := by
    simpa using hLarge
  have hTermLower :
      LateReturnProbe.Terminator.lowerAt? output block.term =
        some (guard ++ dispatcher) := by
    rw [hTerm]
    simp [LateReturnProbe.Terminator.lowerAt?,
      hLarge',
      hDepth, hBound, hDynamicEq]
  have hTermLowerBlock :
      LateReturnProbe.Terminator.lowerAt? block.output block.term =
        some (guard ++ dispatcher) := by
    simpa [hOutput] using hTermLower
  have hCodeEq :
      code = prefixCode ++ dispatcher := by
    unfold LateReturnProbe.Block.lower? at hLower
    rw [hBody] at hLower
    simp [hOutput, hTermLowerBlock] at hLower
    calc
      code =
          .label block.label ::
            (bodyCode ++ (guard ++ dispatcher)) :=
        hLower.symm
      _ = prefixCode ++ dispatcher := by
        simp [prefixCode, before, guard, dispatcherPrefixCode,
          List.append_assoc]
  have hWholeFits :=
    (ReturnAddressProbe.Compact.compile?_valid hCompile).sourcePCFits
  have hCodeFits :
      Assembly.Program.PCFitsFrom pre code := by
    apply Assembly.Program.PCFitsFrom.of_append
    rw [← hInput]
    exact hWholeFits
  have hPrefixDispatcherFits :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ dispatcher) := by
    simpa [hCodeEq] using hCodeFits
  have hPrefixFits :
      Assembly.Program.PCFitsFrom pre prefixCode :=
    Assembly.Program.PCFitsFrom.left hPrefixDispatcherFits
  have hAfterPrefixFits :
      Assembly.Program.PCFitsFrom
        (pre ++ prefixCode) dispatcher := by
    simpa [List.append_assoc] using
      Assembly.Program.PCFitsFrom.right hPrefixDispatcherFits
  have hBeforeGuardFits :
      Assembly.Program.PCFitsFrom pre
        (before ++ guard) := by
    simpa [hPrefixEq] using hPrefixFits
  have hBeforeFits :
      Assembly.Program.PCFitsFrom pre before :=
    Assembly.Program.PCFitsFrom.left hBeforeGuardFits
  have hPrefixSimple :
      ∀ instr ∈ prefixCode,
        Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
          instr := by
    exact Preparation.simpleTrace?_all_simple hTraceCheck
  have hBeforeSimple :
      ∀ instr ∈ before,
        Assembly.Compact.InteractionSemantics.PreparationSimpleInstr
          instr := by
    intro instr hInstr
    apply hPrefixSimple instr
    rw [hPrefixEq]
    exact List.mem_append_left guard hInstr
  have hPrefixLength :
      spec.prefixTrace.length = prefixCode.length :=
    Preparation.simpleTrace?_length hTraceCheck
  have hProgram :
      input = pre ++ prefixCode ++ dispatcher ++ post := by
    simpa [hCodeEq, List.append_assoc] using hInput
  have hWholeBridgeRaw :=
    Preparation.simpleCode_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (code := prefixCode) (pre := pre)
      (post := dispatcher ++ post) (state := source)
      dispatcher.length hPrefixSimple hPrefixFits hStart
  have hWholeBridge :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input (dispatcher.length + prefixCode.length) source =
        (do
          let prefixResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              input prefixCode.length source
          match prefixResult with
          | .running mid =>
              Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
                input dispatcher.length mid
          | .halted halt =>
              pure (.halted halt)) := by
    simpa [hProgram, List.append_assoc, Nat.add_comm] using
      hWholeBridgeRaw
  have hBeforeBridgeRaw :=
    Preparation.simpleCode_openRunUntilTransferWithPolicy
      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
      (code := before) (pre := pre)
      (post := guard ++ dispatcher ++ post) (state := source)
      (guard.length + dispatcher.length)
      hBeforeSimple hBeforeFits hStart
  have hBeforeBridge :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input
          ((guard.length + dispatcher.length) + before.length)
          source =
        (do
          let beforeResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              input before.length source
          match beforeResult with
          | .running mid =>
              Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
                input (guard.length + dispatcher.length) mid
          | .halted halt =>
              pure (.halted halt)) := by
    simpa [hProgram, hPrefixEq, List.append_assoc] using
      hBeforeBridgeRaw
  have hTotals :
      dispatcher.length + prefixCode.length =
        (guard.length + dispatcher.length) + before.length := by
    rw [hPrefixEq, List.length_append]
    omega
  have hCombinedBefore :
      Assembly.InteractionSemantics.Source.openRunNResult
          input before.length source =
        (do
          let labelResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              input 1 source
          match labelResult with
          | .running entry =>
              Assembly.InteractionSemantics.Source.openRunNResult
                input bodyCode.length entry
          | .halted halt =>
              pure (.halted halt)) := by
    simpa [before, Nat.add_comm] using
      (Assembly.InteractionSemantics.Source.openRunNResult_add
        input 1 bodyCode.length source)
  have hCompiled :
      LateReturnProbe.CompiledBlock.openRun block input source =
        (do
          let beforeResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              input before.length source
          match beforeResult with
          | .running mid =>
              Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
                input (guard.length + dispatcher.length) mid
          | .halted halt =>
              pure (.halted halt)) := by
    unfold LateReturnProbe.CompiledBlock.openRun
    rw [hBody]
    simp [hOutput, hTermLowerBlock]
    simp [hTerm, List.length_append,
      TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy]
    rw [hCombinedBefore]
    let bodyNext :
        Assembly.StepResult →
          Assembly.InteractionSemantics.OpenStepResult
      | .running entry =>
          Assembly.InteractionSemantics.Source.openRunNResult
            input bodyCode.length entry
      | .halted halt =>
          pure (.halted halt)
    let finish :
        Assembly.StepResult →
          Assembly.InteractionSemantics.OpenStepResult
      | .running mid =>
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            input (guard.length + dispatcher.length) mid
      | .halted halt =>
          pure (.halted halt)
    have hAssoc :=
      Simulation.Interaction.bind_assoc
        (Assembly.InteractionSemantics.Source.openRunNResult
          input 1 source)
        bodyNext finish
    have hNormalize :
        (do
          let labelResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              input 1 source
          match labelResult with
          | .running entry =>
              do
                let bodyResult ←
                  Assembly.InteractionSemantics.Source.openRunNResult
                    input bodyCode.length entry
                finish bodyResult
          | .halted halt =>
              pure (.halted halt)) =
          Simulation.Interaction.bind
            (Assembly.InteractionSemantics.Source.openRunNResult
              input 1 source)
            (fun labelResult =>
              Simulation.Interaction.bind
                (bodyNext labelResult) finish) := by
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Assembly.InteractionSemantics.Source.openRunNResult
            input 1 source))
      intro labelResult hDone
      cases labelResult with
      | running entry =>
          rfl
      | halted halt =>
          rw [show bodyNext (.halted halt) =
              .done (.ok (.halted halt)) by
            rfl]
          rw [Simulation.Interaction.bind_done_ok]
    have hOrder :
        (do
          let labelResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              input 1 source
          match labelResult with
          | .halted halt =>
              pure (.halted halt)
          | .running entry =>
              do
                let bodyResult ←
                  Assembly.InteractionSemantics.Source.openRunNResult
                    input bodyCode.length entry
                match bodyResult with
                | .halted halt =>
                    pure (.halted halt)
                | .running mid =>
                    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                      TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
                      input (guard.length + dispatcher.length) mid) =
          (do
            let labelResult ←
              Assembly.InteractionSemantics.Source.openRunNResult
                input 1 source
            match labelResult with
            | .running entry =>
                do
                  let bodyResult ←
                    Assembly.InteractionSemantics.Source.openRunNResult
                      input bodyCode.length entry
                  finish bodyResult
            | .halted halt =>
                pure (.halted halt)) := by
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Assembly.InteractionSemantics.Source.openRunNResult
            input 1 source))
      intro labelResult hDone
      cases labelResult with
      | halted halt =>
          rfl
      | running entry =>
          apply Simulation.Interaction.AllDone.bind_congr
            (Simulation.Interaction.AllDone.trivial
              (Assembly.InteractionSemantics.Source.openRunNResult
                input bodyCode.length entry))
          intro bodyResult hBodyDone
          cases bodyResult <;> rfl
    simpa [bodyNext, finish] using
      hOrder.trans (hNormalize.trans hAssoc.symm)
  calc
    (do
        let prefixResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            input spec.prefixTrace.length source
        match prefixResult with
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              input (dispatcherCode spec.first spec.rest).length mid
        | .halted halt =>
            pure (.halted halt)) =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input (dispatcher.length + prefixCode.length) source := by
      simpa [dispatcher, hPrefixLength] using hWholeBridge.symm
    _ =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          input
            ((guard.length + dispatcher.length) + before.length)
            source := by
      rw [hTotals]
    _ =
        (do
          let beforeResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              input before.length source
          match beforeResult with
          | .running mid =>
              Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
                input (guard.length + dispatcher.length) mid
          | .halted halt =>
              pure (.halted halt)) :=
      hBeforeBridge
    _ =
        LateReturnProbe.CompiledBlock.openRun block input source :=
      hCompiled.symm

set_option maxHeartbeats 1000000 in
theorem certifiedReturnBlock_compiled_openRun_rel
    {input : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DispatcherSpec}
    {code pre post : Assembly.Program}
    {target source : EVMState} {entryPc : Nat}
    (hCompile :
      ReturnAddressProbe.Compact.compile? input pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hValid :
      spec.ValidForBlock input artifact block)
    (hLower :
      LateReturnProbe.Block.lower? block = some code)
    (hInput : input = pre ++ code ++ post)
    (hFull : Preparation.FullStateRel input artifact target source)
    (hEntry :
      input.labelPc block.label = some entryPc)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat entryPc)
    (hStart : source.pc = pre.pcAfter)
    (hLarge :
      ¬ (spec.first :: spec.rest).length ≤
        LateReturnProbe.Terminator.standardReturnSiteLimit)
    (hUnique :
      ReturnAddressRelation.TokensUnique
        (spec.first :: spec.rest))
    (hLabels : input.labels.Nodup)
    (hSourceTargetsNonzero :
      ∀ site ∈ spec.first :: spec.rest,
        ∃ dest,
          input.labelPc site.target = some dest ∧
            EvmYul.UInt256.ofNat dest ≠
              EvmYul.UInt256.ofNat 0) :
    Simulation.Interaction.Rel
      (Preparation.FullOutcomeRel input artifact)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        (Preparation.SimpleTrace.targetFuel spec.prefixTrace +
          (spec.layout.compactCode.length + 4))
        target)
      (LateReturnProbe.CompiledBlock.openRun
        block input source) := by
  have hSplit :=
    certifiedReturnBlock_openRun_rel
      hCompile byteSuffix hValid hFull hEntry hSourcePc
      hUnique hLabels hSourceTargetsNonzero
  have hSourceEq :=
    certifiedReturnBlock_sourceRun_eq_compiled
      hCompile hValid hLower hInput hStart hLarge
  rw [hSourceEq] at hSplit
  exact hSplit

/-!
The return dispatcher is only one of the two block shapes in a late-return
program.  Direct blocks still use the ordinary lowering, but must be
re-certified against the custom compact artifact: the label/body prefix is a
straight preparation trace and the terminator is an ordinary transfer trace.
Keeping both traces in the executable certificate lets the whole-program
runner use the exact `CompiledBlock.openRun` scheduling rather than assuming
that a transfer-free prefix and a terminator are interchangeable.
-/

namespace StandardReturn

def usesSharedLayout (depth : Nat) (sites : List ReturnSite) : Bool :=
  decide (2 < depth * (sites.length - 1))

def guardCode (depth : Nat) (sites : List ReturnSite) :
    Assembly.Program :=
  if usesSharedLayout depth sites then
    Assembly.StackShuffle.guardedLiftBuriedToTop depth
  else
    []

def caseDepth (depth : Nat) (sites : List ReturnSite) : Nat :=
  if usesSharedLayout depth sites then 0 else depth

theorem loweredCode_eq
    (depth : Nat) (sites : List ReturnSite) :
    TypedCfg.Terminator.returnDispatchLoweredCode depth sites =
      guardCode depth sites ++
        TypedCfg.Terminator.returnDispatchCode
          (caseDepth depth sites) sites := by
  by_cases hShared : 2 < depth * (sites.length - 1)
  · simp [TypedCfg.Terminator.returnDispatchLoweredCode,
      TypedCfg.Terminator.returnDispatchSharedCode,
      guardCode, caseDepth, usesSharedLayout, hShared]
  · simp [TypedCfg.Terminator.returnDispatchLoweredCode,
      guardCode, caseDepth, usesSharedLayout, hShared]

def selectedTestCode
    (depth : Nat) (sites before : List ReturnSite)
    (site : ReturnSite) : Assembly.Program :=
  guardCode depth sites ++
    TypedCfg.Terminator.returnDispatchTestCases
      (caseDepth depth sites) (before ++ [site])

def rejectCode
    (depth : Nat) (sites : List ReturnSite) : Assembly.Program :=
  guardCode depth sites ++
    TypedCfg.Terminator.returnDispatchTests
      (caseDepth depth sites) sites

structure CaseSpec where
  site : ReturnSite
  before : List ReturnSite
  after : List ReturnSite
  casePc : Nat
  testTrace : List Assembly.Compact.PreparationBlock
  caseTrace : List Assembly.Compact.PreparationBlock

structure Spec where
  blockLabel : Label
  entryPc : Nat
  termPc : Nat
  depth : Nat
  sites : List ReturnSite
  prefixTrace : List Assembly.Compact.PreparationBlock
  cases : List CaseSpec
  rejectTrace : List Assembly.Compact.PreparationBlock

def CaseSpec.Valid
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (termPc depth : Nat) (sites : List ReturnSite)
    (spec : CaseSpec) : Prop :=
  sites = spec.before ++ spec.site :: spec.after ∧
    Preparation.ordinaryTrace? artifact termPc
        (selectedTestCode depth sites spec.before spec.site) =
      some spec.testTrace ∧
    sourceProgram.labelPc spec.site.caseLabel = some spec.casePc ∧
    Preparation.ordinaryTrace? artifact spec.casePc
        (TypedCfg.Terminator.returnDispatchCase
          (caseDepth depth sites) spec.site) =
      some spec.caseTrace

def Spec.ValidForBlock
    (spec : Spec)
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Prop :=
  ∃ bodyCode output termCode,
    block.term = .returnDispatch spec.depth spec.sites ∧
    spec.sites.length ≤
      LateReturnProbe.Terminator.standardReturnSiteLimit ∧
    spec.depth < 16 ∧
    TypedCfg.Block.lowerBodyFrom? block.body block.input =
      some (bodyCode, output) ∧
    output = block.output ∧
    output.returnTokenDepth? = some spec.depth ∧
    LateReturnProbe.Terminator.lowerAt? output block.term =
      some termCode ∧
    termCode =
      TypedCfg.Terminator.returnDispatchLoweredCode
        spec.depth spec.sites ∧
    sourceProgram.labelPc block.label = some spec.entryPc ∧
    spec.blockLabel = block.label ∧
    spec.termPc =
      spec.entryPc +
        Assembly.Program.byteLength
          (Assembly.Instr.label block.label :: bodyCode) ∧
    Preparation.simpleTrace? artifact spec.entryPc
        (Assembly.Instr.label block.label :: bodyCode) =
      some spec.prefixTrace ∧
    spec.cases.map CaseSpec.site = spec.sites ∧
    (∀ caseSpec ∈ spec.cases,
      caseSpec.Valid sourceProgram artifact
        spec.termPc spec.depth spec.sites) ∧
    Preparation.ordinaryTrace? artifact spec.termPc
        (rejectCode spec.depth spec.sites) =
      some spec.rejectTrace

def certifyCases?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (termPc depth : Nat) (sites : List ReturnSite) :
    List ReturnSite → List ReturnSite → Option (List CaseSpec)
  | _before, [] =>
      some []
  | before, site :: after => do
      let testTrace ←
        Preparation.ordinaryTrace? artifact termPc
          (selectedTestCode depth sites before site)
      let casePc ← sourceProgram.labelPc site.caseLabel
      let caseTrace ←
        Preparation.ordinaryTrace? artifact casePc
          (TypedCfg.Terminator.returnDispatchCase
            (caseDepth depth sites) site)
      let rest ←
        certifyCases? sourceProgram artifact termPc depth sites
          (before ++ [site]) after
      some
        ({ site
           before
           after
           casePc
           testTrace
           caseTrace } :: rest)

theorem certifyCases?_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {termPc depth : Nat} {sites : List ReturnSite}
    {before remaining : List ReturnSite}
    {specs : List CaseSpec}
    (hSplit : sites = before ++ remaining)
    (hCertify :
      certifyCases? sourceProgram artifact termPc depth sites
          before remaining =
        some specs) :
    specs.map CaseSpec.site = remaining ∧
      ∀ spec ∈ specs,
        spec.Valid sourceProgram artifact termPc depth sites := by
  induction remaining generalizing before specs with
  | nil =>
      simp [certifyCases?] at hCertify
      subst specs
      simp
  | cons site after ih =>
      cases hTest :
          Preparation.ordinaryTrace? artifact termPc
            (selectedTestCode depth sites before site) with
      | none =>
          simp [certifyCases?, hTest] at hCertify
      | some testTrace =>
          cases hCasePc :
              sourceProgram.labelPc site.caseLabel with
          | none =>
              simp [certifyCases?, hTest, hCasePc] at hCertify
          | some casePc =>
              cases hCase :
                  Preparation.ordinaryTrace? artifact casePc
                    (TypedCfg.Terminator.returnDispatchCase
                      (caseDepth depth sites) site) with
              | none =>
                  simp [certifyCases?, hTest, hCasePc, hCase]
                    at hCertify
              | some caseTrace =>
                  cases hRest :
                      certifyCases? sourceProgram artifact termPc depth
                        sites (before ++ [site]) after with
                  | none =>
                      simp [certifyCases?, hTest, hCasePc, hCase, hRest]
                        at hCertify
                  | some rest =>
                      simp [certifyCases?, hTest, hCasePc, hCase, hRest]
                        at hCertify
                      subst specs
                      have hTailSplit :
                          sites = (before ++ [site]) ++ after := by
                        simpa [List.append_assoc] using hSplit
                      obtain ⟨hRestSites, hRestValid⟩ :=
                        ih hTailSplit hRest
                      constructor
                      · simp [hRestSites]
                      · intro spec hMem
                        simp only [List.mem_cons] at hMem
                        rcases hMem with hHead | hTail
                        · subst spec
                          exact
                            ⟨hSplit, hTest, hCasePc, hCase⟩
                        · exact hRestValid spec hTail

def certifySpec?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Option Spec :=
  match block.term with
  | .returnDispatch returnCount sites => do
      let _ ←
        if sites.length ≤
            LateReturnProbe.Terminator.standardReturnSiteLimit then
          some ()
        else
          none
      let (bodyCode, output) ←
        TypedCfg.Block.lowerBodyFrom? block.body block.input
      let _ ← if output = block.output then some () else none
      let depth ← output.returnTokenDepth?
      let _ ←
        if depth = returnCount ∧ depth < 16 then some () else none
      let termCode ←
        LateReturnProbe.Terminator.lowerAt? output block.term
      let _ ←
        if termCode =
            TypedCfg.Terminator.returnDispatchLoweredCode
              depth sites then
          some ()
        else
          none
      let entryPc ← sourceProgram.labelPc block.label
      let prefixCode : Assembly.Program :=
        .label block.label :: bodyCode
      let prefixTrace ←
        Preparation.simpleTrace? artifact entryPc prefixCode
      let termPc := entryPc + prefixCode.byteLength
      let cases ←
        certifyCases? sourceProgram artifact termPc depth sites
          [] sites
      let rejectTrace ←
        Preparation.ordinaryTrace? artifact termPc
          (rejectCode depth sites)
      some
        { blockLabel := block.label
          entryPc
          termPc
          depth
          sites
          prefixTrace
          cases
          rejectTrace }
  | _ =>
      none

theorem certifySpec?_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : Spec}
    (hCertify :
      certifySpec? sourceProgram artifact block = some spec) :
    spec.ValidForBlock sourceProgram artifact block := by
  cases hTerm : block.term with
  | fallthrough next | jump next | jumpi next fallback
  | halt kind | invalid =>
      simp [certifySpec?, hTerm] at hCertify
  | returnDispatch returnCount sites =>
      simp only [certifySpec?, hTerm] at hCertify
      by_cases hSmall :
          sites.length ≤
            LateReturnProbe.Terminator.standardReturnSiteLimit
      · simp [hSmall] at hCertify
        cases hBody :
            TypedCfg.Block.lowerBodyFrom? block.body block.input with
        | none =>
            simp [hBody] at hCertify
        | some bodyResult =>
            rcases bodyResult with ⟨bodyCode, output⟩
            simp [hBody] at hCertify
            by_cases hOutput : output = block.output
            · subst output
              simp at hCertify
              cases hDepth : block.output.returnTokenDepth? with
              | none =>
                  simp [hDepth] at hCertify
              | some depth =>
                  simp [hDepth] at hCertify
                  by_cases hGate :
                      depth = returnCount ∧ depth < 16
                  · simp [hGate] at hCertify
                    have hDepthCount := hGate.1
                    subst returnCount
                    have hCertify := hCertify.2
                    cases hTermCode :
                        LateReturnProbe.Terminator.lowerAt?
                          block.output
                            (.returnDispatch depth sites) with
                    | none =>
                        simp [hTermCode] at hCertify
                    | some termCode =>
                        simp [hTermCode] at hCertify
                        by_cases hCode :
                            termCode =
                              TypedCfg.Terminator.returnDispatchLoweredCode
                                depth sites
                        · simp [hCode] at hCertify
                          cases hEntry :
                              sourceProgram.labelPc block.label with
                          | none =>
                              simp [hEntry] at hCertify
                          | some entryPc =>
                              simp [hEntry] at hCertify
                              let prefixCode : Assembly.Program :=
                                .label block.label :: bodyCode
                              cases hPrefix :
                                  Preparation.simpleTrace?
                                    artifact entryPc prefixCode with
                              | none =>
                                  simp [prefixCode, hPrefix] at hCertify
                              | some prefixTrace =>
                                  simp [prefixCode, hPrefix] at hCertify
                                  let termPc :=
                                    entryPc +
                                      ((Assembly.Instr.label block.label).byteSize +
                                        bodyCode.byteLength)
                                  cases hCases :
                                      certifyCases? sourceProgram artifact
                                        termPc depth sites [] sites with
                                  | none =>
                                      simp [termPc, hCases] at hCertify
                                  | some cases =>
                                      simp [termPc, hCases] at hCertify
                                      cases hReject :
                                          Preparation.ordinaryTrace?
                                            artifact termPc
                                            (rejectCode depth sites) with
                                      | none =>
                                          simp [termPc, hReject] at hCertify
                                      | some rejectTrace =>
                                          simp [termPc, hReject] at hCertify
                                          subst spec
                                          obtain
                                              ⟨hCaseSites, hCaseValid⟩ :=
                                            certifyCases?_valid
                                              (sites := sites)
                                              (before := [])
                                              (remaining := sites)
                                              (by simp)
                                              hCases
                                          exact
                                            ⟨bodyCode, block.output, termCode,
                                              hTerm, hSmall, hGate.2,
                                              hBody, rfl, hDepth,
                                              (by simpa [hTerm] using
                                                hTermCode),
                                              hCode, hEntry,
                                              rfl, by simp [termPc,
                                                prefixCode],
                                              by simpa [prefixCode] using
                                                hPrefix,
                                              hCaseSites, hCaseValid,
                                              hReject⟩
                        · simp [hCode] at hCertify
                  · simp [hGate] at hCertify
            · simp [hOutput] at hCertify
      · simp [hSmall] at hCertify

def certifyBlock?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Option (Option Spec) :=
  match block.term with
  | .returnDispatch _ sites =>
      if sites.length ≤
          LateReturnProbe.Terminator.standardReturnSiteLimit then
        (certifySpec? sourceProgram artifact block).map some
      else
        some none
  | _ =>
      some none

theorem certifyBlock?_some_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : Spec}
    (hCertify :
      certifyBlock? sourceProgram artifact block =
        some (some spec)) :
    spec.ValidForBlock sourceProgram artifact block := by
  cases hTerm : block.term with
  | fallthrough next | jump next | jumpi next fallback
  | halt kind | invalid =>
      simp [certifyBlock?, hTerm] at hCertify
  | returnDispatch returnCount sites =>
      by_cases hSmall :
          sites.length ≤
            LateReturnProbe.Terminator.standardReturnSiteLimit
      · simp [certifyBlock?, hTerm, hSmall] at hCertify
        exact certifySpec?_valid hCertify
      · simp [certifyBlock?, hTerm, hSmall] at hCertify

theorem certifyBlock?_small_return_ne_none
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {returnCount : Nat}
    {sites : List ReturnSite} {current : Option Spec}
    (hTerm :
      block.term = .returnDispatch returnCount sites)
    (hSmall :
      sites.length ≤
        LateReturnProbe.Terminator.standardReturnSiteLimit)
    (hCertify :
      certifyBlock? sourceProgram artifact block =
        some current) :
    current ≠ none := by
  simp [certifyBlock?, hTerm, hSmall] at hCertify
  rcases hCertify with ⟨spec, hSpec, rfl⟩
  simp

def certifyProgram?
    (sourceProgram : Assembly.Program) (artifact : Artifact) :
    List TypedCfg.Block → Option (List Spec)
  | [] =>
      some []
  | block :: blocks => do
      let current ← certifyBlock? sourceProgram artifact block
      let rest ← certifyProgram? sourceProgram artifact blocks
      match current with
      | none => some rest
      | some spec => some (spec :: rest)

def Coverage
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (blocks : List TypedCfg.Block)
    (specs : List Spec) : Prop :=
  ∀ block ∈ blocks, ∀ returnCount sites,
    block.term = .returnDispatch returnCount sites →
      sites.length ≤
        LateReturnProbe.Terminator.standardReturnSiteLimit →
      ∃ spec, spec ∈ specs ∧
        spec.ValidForBlock sourceProgram artifact block

theorem certifyProgram?_coverage
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {blocks : List TypedCfg.Block} {specs : List Spec}
    (hCertify :
      certifyProgram? sourceProgram artifact blocks =
        some specs) :
    Coverage sourceProgram artifact blocks specs := by
  induction blocks generalizing specs with
  | nil =>
      simp [Coverage]
  | cons head tail ih =>
      cases hCurrent :
          certifyBlock? sourceProgram artifact head with
      | none =>
          simp [certifyProgram?, hCurrent] at hCertify
      | some current =>
          cases hRest :
              certifyProgram? sourceProgram artifact tail with
          | none =>
              simp [certifyProgram?, hCurrent, hRest] at hCertify
          | some rest =>
              cases current with
              | none =>
                  simp [certifyProgram?, hCurrent, hRest] at hCertify
                  subst specs
                  unfold Coverage
                  intro block hMem returnCount sites hTerm hSmall
                  simp only [List.mem_cons] at hMem
                  rcases hMem with hHead | hTail
                  · subst block
                    exact
                      False.elim
                        ((certifyBlock?_small_return_ne_none
                            hTerm hSmall hCurrent) rfl)
                  · exact
                      ih hRest block hTail returnCount sites
                        hTerm hSmall
              | some spec =>
                  simp [certifyProgram?, hCurrent, hRest] at hCertify
                  subst specs
                  unfold Coverage
                  intro block hMem returnCount sites hTerm hSmall
                  simp only [List.mem_cons] at hMem
                  rcases hMem with hHead | hTail
                  · subst block
                    exact
                      ⟨spec, by simp,
                        certifyBlock?_some_valid hCurrent⟩
                  · obtain ⟨tailSpec, hTailMem, hTailValid⟩ :=
                      ih hRest block hTail returnCount sites
                        hTerm hSmall
                    exact
                      ⟨tailSpec, by simp [hTailMem], hTailValid⟩

def Spec.findCase? (spec : Spec) (token : Word) :
    Option CaseSpec :=
  spec.cases.find? fun caseSpec =>
    decide (caseSpec.site.token = token)

theorem Spec.findCase?_some_mem
    {spec : Spec} {token : Word} {caseSpec : CaseSpec}
    (hFind : spec.findCase? token = some caseSpec) :
    caseSpec ∈ spec.cases :=
  List.mem_of_find?_eq_some hFind

theorem Spec.findCase?_some_token
    {spec : Spec} {token : Word} {caseSpec : CaseSpec}
    (hFind : spec.findCase? token = some caseSpec) :
    caseSpec.site.token = token := by
  have hCheck := List.find?_some hFind
  simpa [Spec.findCase?] using hCheck

theorem Spec.findCase?_none_all_ne
    {spec : Spec} {token : Word}
    (hSites : spec.cases.map CaseSpec.site = spec.sites)
    (hFind : spec.findCase? token = none) :
    ∀ site ∈ spec.sites, site.token ≠ token := by
  intro site hSite
  rw [← hSites] at hSite
  simp only [List.mem_map] at hSite
  rcases hSite with ⟨caseSpec, hCaseMem, hSiteEq⟩
  subst site
  have hNone :=
    (List.find?_eq_none.mp hFind) caseSpec hCaseMem
  simpa [Spec.findCase?] using hNone

theorem Spec.resolvedCaseLabels
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : Spec}
    (hValid :
      spec.ValidForBlock sourceProgram artifact block) :
    TypedCfg.Preservation.Terminator.ResolvedCaseLabels
      sourceProgram spec.sites := by
  rcases hValid with
    ⟨bodyCode, output, termCode, hTerm, hSmall, hBound,
      hBody, hOutput, hDepth, hTermLower, hTermCode,
      hEntry, hBlockLabel, hTermPc, hPrefix,
      hCases, hCaseValid, hReject⟩
  intro site hSite
  rw [← hCases] at hSite
  simp only [List.mem_map] at hSite
  rcases hSite with ⟨caseSpec, hCaseMem, hSiteEq⟩
  subst site
  exact
    ⟨caseSpec.casePc,
      (hCaseValid caseSpec hCaseMem).2.2.1⟩

theorem tokensUnique_before_ne
    {before after : List ReturnSite} {site : ReturnSite}
    (hUnique :
      ReturnAddressRelation.TokensUnique
        (before ++ site :: after)) :
    ∀ prior ∈ before, prior.token ≠ site.token := by
  induction before with
  | nil =>
      simp
  | cons head rest ih =>
      simp only [List.cons_append,
        ReturnAddressRelation.TokensUnique] at hUnique
      rcases hUnique with ⟨hFresh, hRestUnique⟩
      intro prior hPrior
      simp only [List.mem_cons] at hPrior
      rcases hPrior with rfl | hPrior
      · exact hFresh site (by simp)
      · exact ih hRestUnique prior hPrior

theorem findTarget?_eq_some_of_split
    {before after : List ReturnSite} {site : ReturnSite}
    {token : Word}
    (hBefore :
      ∀ prior ∈ before, prior.token ≠ token)
    (hToken : site.token = token) :
    TypedCfg.Block.ReturnSite.findTarget? token
        (before ++ site :: after) =
      some site.target := by
  induction before with
  | nil =>
      simp [TypedCfg.Block.ReturnSite.findTarget?, hToken]
  | cons head rest ih =>
      have hHead : head.token ≠ token :=
        hBefore head (by simp)
      have hRest :
          ∀ prior ∈ rest, prior.token ≠ token := by
        intro prior hPrior
        exact hBefore prior (by simp [hPrior])
      simp [TypedCfg.Block.ReturnSite.findTarget?,
        hHead, ih hRest]

theorem resolvedTargets_of_sites
    {sourceProgram : Assembly.Program}
    {depth : Nat} {sites : List ReturnSite}
    (hTargets :
      ∀ site ∈ sites,
        ∃ dest,
          sourceProgram.labelPc site.target = some dest) :
    TypedCfg.Preservation.Terminator.ResolvedTargets
      sourceProgram (.returnDispatch depth sites) := by
  intro target hTarget
  simp only [TypedCfg.Terminator.targets, List.mem_map] at hTarget
  rcases hTarget with ⟨site, hSite, hTargetEq⟩
  subst target
  exact hTargets site hSite

theorem sameRuntimeData_of_shared_stack
    {left right : EVMState}
    (hShared : left.toSharedState = right.toSharedState)
    (hStack : left.stack = right.stack) :
    Assembly.SameRuntimeData left right := by
  cases left
  cases right
  simp_all [Assembly.SameRuntimeData,
    Assembly.eraseRuntimeControl]

theorem fullOutcomeRel_replace_source_jump
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {label : Label} {logical : EVMState}
    {targetDone pathDone fullDone :
      Except Assembly.EVMException Assembly.StepResult}
    (hTargetPath :
      Preparation.FullOutcomeRel sourceProgram artifact
        targetDone pathDone)
    (hPath :
      TypedCfg.Preservation.Outcome.Simulates
        sourceProgram (.jump label logical) pathDone)
    (hFull :
      TypedCfg.Preservation.Outcome.Simulates
        sourceProgram (.jump label logical) fullDone) :
    Preparation.FullOutcomeRel sourceProgram artifact
      targetDone fullDone := by
  unfold TypedCfg.Preservation.Outcome.Simulates at hPath hFull
  rcases hPath with
    ⟨pathDest, hPathLabel, hPathAt⟩
  rcases hFull with
    ⟨fullDest, hFullLabel, hFullAt⟩
  have hDest : pathDest = fullDest := by
    rw [hPathLabel] at hFullLabel
    exact Option.some.inj hFullLabel
  subst fullDest
  cases pathDone with
  | error pathError =>
      simp [TypedCfg.Preservation.Outcome.RunningAt] at hPathAt
  | ok pathResult =>
      cases pathResult with
      | halted pathHalt =>
          simp [TypedCfg.Preservation.Outcome.RunningAt] at hPathAt
      | running pathState =>
          rcases hPathAt with
            ⟨hPathPc, hPathRuntime⟩
          cases fullDone with
          | error fullError =>
              simp [TypedCfg.Preservation.Outcome.RunningAt] at hFullAt
          | ok fullResult =>
              cases fullResult with
              | halted fullHalt =>
                  simp [TypedCfg.Preservation.Outcome.RunningAt] at hFullAt
              | running fullState =>
                  rcases hFullAt with
                    ⟨hFullPc, hFullRuntime⟩
                  cases hTargetPath with
                  | ok hStep =>
                      rename_i targetResult
                      cases targetResult with
                      | halted targetHalt =>
                          simp [Preparation.FullStepResultRel] at hStep
                      | running targetState =>
                          change
                            Preparation.FullStateRel sourceProgram artifact
                              targetState pathState at hStep
                          rcases hStep with
                            ⟨sourcePc, preparedPc,
                              compactSourcePc, compactPc,
                              hPreparationBoundary, hCompactBoundary,
                              hPreparedWord, hSourcePc, hTargetPc,
                              hTargetRuntime⟩
                          apply Simulation.Interaction.ExceptRel.ok
                          exact
                            ⟨sourcePc, preparedPc,
                              compactSourcePc, compactPc,
                              hPreparationBoundary, hCompactBoundary,
                              hPreparedWord,
                              hFullPc.trans
                                (hPathPc.symm.trans hSourcePc),
                              hTargetPc,
                              Assembly.SameRuntimeData.trans
                                hTargetRuntime
                                (Assembly.SameRuntimeData.trans
                                  hPathRuntime
                                  hFullRuntime.symm)⟩

theorem selectedTestPrefix_openRun
    {depth : Nat} {before after : List ReturnSite}
    {site : ReturnSite}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {state : EVMState}
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hBefore :
      ∀ prior, prior ∈ before → prior.token ≠ token)
    (hToken : site.token = token)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchCode
          depth (before ++ site :: after)))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      TypedCfg.Preservation.Terminator.ResolvedCaseLabels
        (pre ++
          TypedCfg.Terminator.returnDispatchCode
            depth (before ++ site :: after) ++ post)
        (before ++ site :: after)) :
    ∃ caseDest,
      (pre ++
        TypedCfg.Terminator.returnDispatchCode
          depth (before ++ site :: after) ++ post).labelPc
          site.caseLabel =
        some caseDest ∧
      Assembly.InteractionSemantics.Source.openRunUntilTransfer
          (pre ++
            TypedCfg.Terminator.returnDispatchCode
              depth (before ++ site :: after) ++ post)
          (TypedCfg.Terminator.returnDispatchTestCases
            depth (before ++ [site])).length
          { state with stack := front ++ token :: suffix } =
        .done
          (.ok
            (.running
              { state with
                stack := front ++ token :: suffix
                pc := EvmYul.UInt256.ofNat caseDest })) := by
  let selectedTests :=
    TypedCfg.Terminator.returnDispatchTestCases
      depth (before ++ [site])
  let tailTests :=
    TypedCfg.Terminator.returnDispatchTestCases depth after
  let cases :=
    TypedCfg.Terminator.returnDispatchCases
      depth (before ++ site :: after)
  have hTestsEq :
      TypedCfg.Terminator.returnDispatchTestCases
          depth (before ++ site :: after) =
        selectedTests ++ tailTests := by
    simp [selectedTests, tailTests,
      TypedCfg.Terminator.returnDispatchTestCases,
      List.append_assoc]
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchCode
          depth (before ++ site :: after) =
        selectedTests ++
          (tailTests ++ [Assembly.Instr.prim .invalid] ++ cases) := by
    simp [TypedCfg.Terminator.returnDispatchCode,
      TypedCfg.Terminator.returnDispatchTests,
      hTestsEq, cases, List.append_assoc]
  have hSelectedFits :
      Assembly.Program.PCFitsFrom pre selectedTests := by
    apply Assembly.Program.PCFitsFrom.left
    simpa [hCodeEq, List.append_assoc] using hFits
  have hResolvedSelected :
      TypedCfg.Preservation.Terminator.ResolvedCaseLabels
        (pre ++ selectedTests ++
          (tailTests ++ [Assembly.Instr.prim .invalid] ++
            cases ++ post))
        (before ++ [site]) := by
    intro selected hSelected
    have hSelectedFull :
        selected ∈ before ++ site :: after := by
      simp only [List.mem_append, List.mem_singleton] at hSelected
      simp only [List.mem_append, List.mem_cons]
      rcases hSelected with hBeforeMem | hSiteEq
      · exact Or.inl hBeforeMem
      · exact Or.inr (Or.inl hSiteEq)
    rcases hResolved selected hSelectedFull with
      ⟨dest, hDest⟩
    exact
      ⟨dest,
        by
          simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hSelected :=
    TypedCfg.InteractionPreservation.Terminator.returnDispatchTestCases_openRunUntilTransfer_of_selected
      (fun _ => false)
      (depth := depth) (before := before) (after := [])
      (site := site) (front := front) (suffix := suffix)
      (token := token) (pre := pre)
      (post :=
        tailTests ++ [Assembly.Instr.prim .invalid] ++ cases ++ post)
      (state := state) (fuel := 0)
      (Or.inr (by rfl))
      hBound hFront hBefore hToken
      (by simpa [selectedTests] using hSelectedFits)
      hPc
      (by
        simpa [selectedTests, List.append_assoc] using
          hResolvedSelected)
  rcases hSelected with
    ⟨caseDest, hCaseDest, hRun⟩
  refine ⟨caseDest, ?_, ?_⟩
  · simpa [hCodeEq, List.append_assoc] using hCaseDest
  · have hZero :
        Assembly.InteractionSemantics.Source.openRunUntilTransfer
            (pre ++
              TypedCfg.Terminator.returnDispatchCode
                depth (before ++ site :: after) ++ post)
            0
            { state with
              stack := front ++ token :: suffix
              pc := EvmYul.UInt256.ofNat caseDest } =
          .done
            (.ok
              (.running
                { state with
                  stack := front ++ token :: suffix
                  pc := EvmYul.UInt256.ofNat caseDest })) := by
        rfl
    simpa [Assembly.InteractionSemantics.Source.openRunUntilTransfer,
      selectedTests, hCodeEq, List.append_assoc, hZero] using hRun

theorem returnDispatchTests_unknown_openRun
    (continueTransfer : Assembly.Instr → Bool)
    {depth : Nat} {sites : List ReturnSite}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {state : EVMState}
    (fuel : Nat)
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hNe : ∀ site, site ∈ sites → site.token ≠ token)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchTests depth sites))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      TypedCfg.Preservation.Terminator.ResolvedCaseLabels
        (pre ++
          TypedCfg.Terminator.returnDispatchTests depth sites ++ post)
        sites) :
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++
          TypedCfg.Terminator.returnDispatchTests depth sites ++ post)
        (fuel +
          (TypedCfg.Terminator.returnDispatchTests depth sites).length)
        { state with stack := front ++ token :: suffix } =
      .done (.error .InvalidInstruction) := by
  let testCases :=
    TypedCfg.Terminator.returnDispatchTestCases depth sites
  have hCodeEq :
      TypedCfg.Terminator.returnDispatchTests depth sites =
        testCases ++ [Assembly.Instr.prim .invalid] := by
    simp [testCases, TypedCfg.Terminator.returnDispatchTests]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (testCases ++ [Assembly.Instr.prim .invalid]) := by
    simpa [hCodeEq] using hFits
  have hTestFits :
      Assembly.Program.PCFitsFrom pre testCases :=
    Assembly.Program.PCFitsFrom.left hFitsAll
  have hAfterTestsFits :
      Assembly.Program.PCFitsFrom (pre ++ testCases)
        [Assembly.Instr.prim .invalid] :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hResolvedTests :
      TypedCfg.Preservation.Terminator.ResolvedCaseLabels
        (pre ++ testCases ++
          (Assembly.Instr.prim .invalid :: post))
        sites := by
    intro site hSite
    rcases hResolved site hSite with ⟨dest, hDest⟩
    exact
      ⟨dest,
        by simpa [hCodeEq, List.append_assoc] using hDest⟩
  have hTests :=
    TypedCfg.InteractionPreservation.Terminator.returnDispatchTestCases_openRunUntilTransfer_of_all_ne
      continueTransfer
      (depth := depth) (sites := sites)
      (front := front) (suffix := suffix) (token := token)
      (pre := pre) (post := Assembly.Instr.prim .invalid :: post)
      (state := state) (fuel + 1)
      hBound hFront hNe hTestFits hPc hResolvedTests
  let tested : EVMState :=
    { state with
      stack := front ++ token :: suffix
      pc := (pre ++ testCases).pcAfter }
  have hTestsRun :
      Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          continueTransfer
          (pre ++
            TypedCfg.Terminator.returnDispatchTests depth sites ++ post)
          ((fuel + 1) + testCases.length)
          { state with stack := front ++ token :: suffix } =
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          continueTransfer
          (pre ++
            TypedCfg.Terminator.returnDispatchTests depth sites ++ post)
          (fuel + 1) tested := by
    simpa [hCodeEq, testCases, tested, List.append_assoc] using hTests
  have hInvalidOpen :
      Assembly.InteractionSemantics.Source.openStepAtResult
          ((pre ++ testCases) ++
            Assembly.Instr.prim .invalid :: post)
          (pre ++ testCases).byteLength
          (.prim .invalid) tested =
        .done (.error .InvalidInstruction) := by
    rw [Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
      (Assembly.InteractionPreservation.source_openStepAt_prim_closed
        (by rfl) (by decide) (by decide))]
    rfl
  have hInvalidRun :=
    Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_error
      continueTransfer
      (pre := pre ++ testCases) (post := post)
      (instr := Assembly.Instr.prim .invalid)
      (state := tested) (err := .InvalidInstruction)
      fuel
      (Assembly.Program.PCFitsFrom.start hAfterTestsFits)
      (by simp [tested])
      hInvalidOpen
  rw [show
    fuel +
        (TypedCfg.Terminator.returnDispatchTests depth sites).length =
      (fuel + 1) + testCases.length by
    rw [hCodeEq]
    simp
    omega]
  rw [hTestsRun]
  simpa [hCodeEq, testCases, tested, List.append_assoc] using hInvalidRun

theorem rejectCode_unknown_openRun
    (continueTransfer : Assembly.Instr → Bool)
    {depth : Nat} {sites : List ReturnSite}
    {front suffix : List Word} {token : Word}
    {pre post : Assembly.Program} {state : EVMState}
    (fuel : Nat)
    (hBound : depth < 16)
    (hFront : front.length = depth)
    (hNe : ∀ site, site ∈ sites → site.token ≠ token)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchLoweredCode depth sites))
    (hPc :
      ({ state with stack := front ++ token :: suffix }).pc =
        pre.pcAfter)
    (hResolved :
      TypedCfg.Preservation.Terminator.ResolvedCaseLabels
        (pre ++
          TypedCfg.Terminator.returnDispatchLoweredCode depth sites ++
            post)
        sites) :
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++
          TypedCfg.Terminator.returnDispatchLoweredCode depth sites ++
            post)
        (fuel + (rejectCode depth sites).length)
        { state with stack := front ++ token :: suffix } =
      .done (.error .InvalidInstruction) := by
  by_cases hShared :
      2 < depth * (sites.length - 1)
  · let guard :=
      Assembly.StackShuffle.guardedLiftBuriedToTop depth
    let tests :=
      TypedCfg.Terminator.returnDispatchTests 0 sites
    let cases :=
      TypedCfg.Terminator.returnDispatchCases 0 sites
    have hLowered :
        TypedCfg.Terminator.returnDispatchLoweredCode depth sites =
          guard ++ (tests ++ cases) := by
      unfold TypedCfg.Terminator.returnDispatchLoweredCode
      rw [if_pos hShared]
      simp [guard, tests, cases,
        TypedCfg.Terminator.returnDispatchSharedCode,
        TypedCfg.Terminator.returnDispatchCode,
        List.append_assoc]
    have hReject :
        rejectCode depth sites = guard ++ tests := by
      simp [rejectCode, guardCode, caseDepth, usesSharedLayout,
        guard, tests, hShared]
    have hFitsAll :
        Assembly.Program.PCFitsFrom pre
          (guard ++ (tests ++ cases)) := by
      simpa [hLowered] using hFits
    have hGuardFits :
        Assembly.Program.PCFitsFrom pre guard :=
      Assembly.Program.PCFitsFrom.left hFitsAll
    have hAfterGuardFits :
        Assembly.Program.PCFitsFrom (pre ++ guard)
          (tests ++ cases) :=
      Assembly.Program.PCFitsFrom.right hFitsAll
    have hTestsFits :
        Assembly.Program.PCFitsFrom (pre ++ guard) tests :=
      Assembly.Program.PCFitsFrom.left hAfterGuardFits
    let prepared : EVMState :=
      { state with
        stack := token :: front ++ suffix
        pc := (pre ++ guard).pcAfter }
    have hGuardRun :=
      Assembly.StackShuffle.InteractionPreservation.guardedLiftBuriedToTop_openRunUntilTransferWithPolicy
        continueTransfer
        (front := front) (suffix := suffix) (token := token)
        (pre := pre) (post := tests ++ cases ++ post)
        (state := state) (fuel := fuel + tests.length)
        (by simpa [guard, hFront] using hGuardFits)
        hPc
        (by simpa [hFront] using hBound)
    have hGuardRun' :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            continueTransfer
            (pre ++ guard ++ (tests ++ cases ++ post))
            ((fuel + tests.length) + guard.length)
            { state with stack := front ++ token :: suffix } =
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            continueTransfer
            (pre ++ guard ++ (tests ++ cases ++ post))
            (fuel + tests.length) prepared := by
      simpa [guard, prepared, hFront, List.append_assoc] using hGuardRun
    have hResolvedTests :
        TypedCfg.Preservation.Terminator.ResolvedCaseLabels
          ((pre ++ guard) ++ tests ++ (cases ++ post)) sites := by
      simpa [hLowered, List.append_assoc] using hResolved
    have hTestsRun :=
      returnDispatchTests_unknown_openRun
        continueTransfer
        (depth := 0) (sites := sites)
        (front := []) (suffix := front ++ suffix)
        (token := token) (pre := pre ++ guard)
        (post := cases ++ post) (state := prepared)
        fuel (by omega) (by simp) hNe
        (by simpa [tests] using hTestsFits)
        (by simp [prepared])
        (by simpa [tests, List.append_assoc] using hResolvedTests)
    have hTestsRun' :
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            continueTransfer
            (pre ++ guard ++ (tests ++ cases ++ post))
            (fuel + tests.length) prepared =
          .done (.error .InvalidInstruction) := by
      simpa [prepared, tests, List.append_assoc] using hTestsRun
    rw [hReject, List.length_append]
    rw [show
      fuel + (guard.length + tests.length) =
        (fuel + tests.length) + guard.length by omega]
    rw [show
      pre ++
          TypedCfg.Terminator.returnDispatchLoweredCode depth sites ++
            post =
        pre ++ guard ++ (tests ++ cases ++ post) by
      simp [hLowered, List.append_assoc]]
    rw [hGuardRun', hTestsRun']
  · have hLowered :
        TypedCfg.Terminator.returnDispatchLoweredCode depth sites =
          TypedCfg.Terminator.returnDispatchCode depth sites := by
      unfold TypedCfg.Terminator.returnDispatchLoweredCode
      rw [if_neg hShared]
    have hReject :
        rejectCode depth sites =
          TypedCfg.Terminator.returnDispatchTests depth sites := by
      simp [rejectCode, guardCode, caseDepth,
        usesSharedLayout, hShared]
    have hTestsFits :
        Assembly.Program.PCFitsFrom pre
          (TypedCfg.Terminator.returnDispatchTests depth sites) := by
      rw [hLowered] at hFits
      exact
        Assembly.Program.PCFitsFrom.left
          (by
            simpa [TypedCfg.Terminator.returnDispatchCode,
              List.append_assoc] using hFits)
    have hResolvedTests :
        TypedCfg.Preservation.Terminator.ResolvedCaseLabels
          (pre ++
            TypedCfg.Terminator.returnDispatchTests depth sites ++
              (TypedCfg.Terminator.returnDispatchCases depth sites ++
                post))
          sites := by
      simpa [hLowered, TypedCfg.Terminator.returnDispatchCode,
        List.append_assoc] using hResolved
    have hRun :=
      returnDispatchTests_unknown_openRun
        continueTransfer
        (depth := depth) (sites := sites)
        (front := front) (suffix := suffix) (token := token)
        (pre := pre)
        (post :=
          TypedCfg.Terminator.returnDispatchCases depth sites ++ post)
        (state := state) fuel hBound hFront hNe
        hTestsFits hPc hResolvedTests
    simpa [hReject, hLowered,
      TypedCfg.Terminator.returnDispatchCode,
      List.append_assoc] using hRun

theorem dup_missing_openRun
    (continueTransfer : Assembly.Instr → Bool)
    {depth fuel : Nat} {restCode : Assembly.Program}
    {pre post : Assembly.Program} {state : EVMState}
    (hFuel : 1 ≤ fuel)
    (hBound : depth < 16)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (Assembly.StackShuffle.dupInstr (depth + 1) :: restCode))
    (hPc : state.pc = pre.pcAfter)
    (hGet : state.stack[depth]? = none) :
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++
          Assembly.StackShuffle.dupInstr (depth + 1) ::
            (restCode ++ post))
        fuel state =
      .done (.error .StackUnderflow) := by
  let duplicate :=
    Assembly.StackShuffle.dupInstr (depth + 1)
  have hLen : state.stack.length ≤ depth := by
    rw [List.getElem?_eq_none_iff] at hGet
    exact hGet
  have hDupError :
      Assembly.Target.stepInstr
          (Assembly.StackShuffle.targetInstr duplicate)
          state =
        .error .StackUnderflow := by
    rw [show
      duplicate =
        Assembly.StackShuffle.dupInstr (depth + 1) from rfl]
    rw [Assembly.StackShuffle.dupInstr_step_eq_dup
      (by omega) (by omega)]
    simp [EvmYul.dup,
      show ¬depth + 1 ≤ state.stack.length by omega]
  have hDupOpen :
      Assembly.InteractionSemantics.Source.openStepAtResult
          (pre ++ duplicate :: (restCode ++ post))
          pre.byteLength duplicate state =
        .done (.error .StackUnderflow) := by
    rw [Assembly.InteractionPreservation.source_openStepAtResult_eq_done_of_stepAt
      (Assembly.StackShuffle.InteractionPreservation.openStepAt_dupInstr_eq_done
        (n := depth + 1) (by omega) (by omega))]
    simp [Assembly.Source.stepAtResult,
      Assembly.StackShuffle.source_stepAt_eq_targetInstr
        (Assembly.StackShuffle.dupInstr_sourceLocal
          (n := depth + 1) (by omega) (by omega)),
      duplicate, hDupError]
  have hRun :=
    Assembly.InteractionPreservation.source_openRunUntilTransferWithPolicy_succ_of_step_error
      continueTransfer
      (pre := pre) (post := restCode ++ post)
      (instr := duplicate) (state := state)
      (err := .StackUnderflow)
      (fuel - 1) hFits.1 hPc hDupOpen
  have hFuelEq : fuel - 1 + 1 = fuel :=
    Nat.sub_add_cancel hFuel
  simpa [duplicate, hFuelEq] using hRun

theorem returnDispatchLowered_missing_openRun
    (continueTransfer : Assembly.Instr → Bool)
    {depth fuel : Nat} {sites : List ReturnSite}
    {pre post : Assembly.Program} {state : EVMState}
    (hFuel : 1 ≤ fuel)
    (hBound : depth < 16)
    (hSites : sites ≠ [])
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchLoweredCode depth sites))
    (hPc : state.pc = pre.pcAfter)
    (hGet : state.stack[depth]? = none) :
    Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        continueTransfer
        (pre ++
          TypedCfg.Terminator.returnDispatchLoweredCode depth sites ++
            post)
        fuel state =
      .done (.error .StackUnderflow) := by
  cases sites with
  | nil =>
      exact (hSites rfl).elim
  | cons site rest =>
      by_cases hShared :
          2 < depth * ((site :: rest).length - 1)
      · let duplicate :=
          Assembly.StackShuffle.dupInstr (depth + 1)
        let restCode : Assembly.Program :=
          Assembly.Instr.prim .pop ::
            (Assembly.StackShuffle.liftBuriedToTop depth ++
              TypedCfg.Terminator.returnDispatchCode
                0 (site :: rest))
        have hCodeHead :
            TypedCfg.Terminator.returnDispatchLoweredCode
                depth (site :: rest) =
              duplicate :: restCode := by
          unfold TypedCfg.Terminator.returnDispatchLoweredCode
          rw [if_pos hShared]
          simp [TypedCfg.Terminator.returnDispatchSharedCode,
            Assembly.StackShuffle.guardedLiftBuriedToTop,
            Assembly.StackShuffle.guardBuried,
            duplicate, restCode, List.append_assoc]
        have hFitsHead :
            Assembly.Program.PCFitsFrom pre
              (duplicate :: restCode) := by
          simpa [hCodeHead] using hFits
        have hRun :=
          dup_missing_openRun
            continueTransfer
            (depth := depth) (fuel := fuel)
            (restCode := restCode) (pre := pre) (post := post)
            (state := state) hFuel hBound
            (by simpa [duplicate] using hFitsHead)
            hPc hGet
        simpa [hCodeHead, duplicate, List.append_assoc] using hRun
      · let duplicate :=
          Assembly.StackShuffle.dupInstr (depth + 1)
        let restCode : Assembly.Program :=
          [ Assembly.Instr.push site.token
          , Assembly.Instr.prim .eq
          , Assembly.Instr.jumpi site.caseLabel
          ] ++
            TypedCfg.Terminator.returnDispatchTestCases depth rest ++
            [Assembly.Instr.prim .invalid] ++
            TypedCfg.Terminator.returnDispatchCases
              depth (site :: rest)
        have hCodeHead :
            TypedCfg.Terminator.returnDispatchLoweredCode
                depth (site :: rest) =
              duplicate :: restCode := by
          unfold TypedCfg.Terminator.returnDispatchLoweredCode
          rw [if_neg hShared]
          simp [TypedCfg.Terminator.returnDispatchCode,
            TypedCfg.Terminator.returnDispatchTests,
            TypedCfg.Terminator.returnDispatchTestCases,
            TypedCfg.Terminator.returnDispatchTest,
            duplicate, restCode, List.append_assoc]
        have hFitsHead :
            Assembly.Program.PCFitsFrom pre
              (duplicate :: restCode) := by
          simpa [hCodeHead] using hFits
        have hRun :=
          dup_missing_openRun
            continueTransfer
            (depth := depth) (fuel := fuel)
            (restCode := restCode) (pre := pre) (post := post)
            (state := state) hFuel hBound
            (by simpa [duplicate] using hFitsHead)
            hPc hGet
        simpa [hCodeHead, duplicate, List.append_assoc] using hRun

theorem CaseSpec.source_test_eq_runningAt_case
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {termPc depth : Nat} {sites : List ReturnSite}
    {spec : CaseSpec}
    {pre post : Assembly.Program}
    {source : EVMState} {front suffix : List Word}
    {token : Word}
    (hValid :
      spec.Valid sourceProgram artifact termPc depth sites)
    (hUnique :
      ReturnAddressRelation.TokensUnique sites)
    (hProgram :
      sourceProgram =
        pre ++
          TypedCfg.Terminator.returnDispatchLoweredCode
            depth sites ++ post)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchLoweredCode
          depth sites))
    (hSourcePc :
      source.pc = pre.pcAfter)
    (hStack :
      source.stack = front ++ token :: suffix)
    (hFront : front.length = depth)
    (hToken : spec.site.token = token)
    (hBound : depth < 16)
    (hResolved :
      TypedCfg.Preservation.Terminator.ResolvedCaseLabels
        sourceProgram sites) :
    ∃ selected,
      Assembly.InteractionSemantics.Source.openRunUntilTransfer
          sourceProgram spec.testTrace.length source =
        .done (.ok (.running selected)) ∧
      selected.pc = EvmYul.UInt256.ofNat spec.casePc ∧
        selected.stack =
          (if usesSharedLayout depth sites then
              token :: front ++ suffix
            else
              front ++ token :: suffix) ∧
        Assembly.SameRuntimeData selected
          { source with
            stack :=
              if usesSharedLayout depth sites then
                token :: front ++ suffix
              else
                front ++ token :: suffix } := by
  rcases hValid with
    ⟨hSplit, hTestTrace, hCasePc, hCaseTrace⟩
  have hBefore :
      ∀ prior, prior ∈ spec.before →
        prior.token ≠ token := by
    have hBeforeSite :=
      tokensUnique_before_ne
        (hUnique := by simpa [hSplit] using hUnique)
    intro prior hPrior hPriorToken
    exact
      (hBeforeSite prior hPrior)
        (hPriorToken.trans hToken.symm)
  have hTraceLength :=
    Preparation.ordinaryTrace?_length hTestTrace
  by_cases hShared :
      2 < depth * (sites.length - 1)
  · let guard :=
      Assembly.StackShuffle.guardedLiftBuriedToTop depth
    let selectedTests :=
      TypedCfg.Terminator.returnDispatchTestCases
        0 (spec.before ++ [spec.site])
    let dispatch :=
      TypedCfg.Terminator.returnDispatchCode
        0 (spec.before ++ spec.site :: spec.after)
    have hLowered :
        TypedCfg.Terminator.returnDispatchLoweredCode depth sites =
          guard ++ dispatch := by
      unfold TypedCfg.Terminator.returnDispatchLoweredCode
      rw [if_pos hShared]
      simp [guard, dispatch,
        TypedCfg.Terminator.returnDispatchSharedCode, hSplit]
    have hTestCode :
        selectedTestCode depth sites spec.before spec.site =
          guard ++ selectedTests := by
      simp [selectedTestCode, guard, selectedTests,
        guardCode, caseDepth, usesSharedLayout, hShared]
    have hProgram' := hProgram
    have hFits' := hFits
    rw [hLowered] at hProgram' hFits'
    have hResolved' := hResolved
    rw [hSplit] at hResolved'
    have hFitsBoth :
        Assembly.Program.PCFitsFrom pre (guard ++ dispatch) := by
      exact hFits'
    have hGuardFits :
        Assembly.Program.PCFitsFrom pre guard :=
      Assembly.Program.PCFitsFrom.left hFitsBoth
    have hDispatchFits :
        Assembly.Program.PCFitsFrom (pre ++ guard) dispatch :=
      Assembly.Program.PCFitsFrom.right hFitsBoth
    let prepared : EVMState :=
      { source with
        stack := token :: front ++ suffix
        pc := (pre ++ guard).pcAfter }
    have hGuardRunRaw :=
      Assembly.StackShuffle.InteractionPreservation.guardedLiftBuriedToTop_openRunUntilTransferWithPolicy
        (fun _ => false)
        (front := front) (suffix := suffix) (token := token)
        (pre := pre) (post := dispatch ++ post)
        (state := source) (fuel := selectedTests.length)
        (by simpa [guard, hFront] using hGuardFits)
        (by simpa [hStack] using hSourcePc)
        (by simpa [hFront] using hBound)
    have hStartEq :
        { source with stack := front ++ token :: suffix } =
          source := by
      rw [← hStack]
    have hGuardRun :
        Assembly.InteractionSemantics.Source.openRunUntilTransfer
            sourceProgram (selectedTests.length + guard.length) source =
          Assembly.InteractionSemantics.Source.openRunUntilTransfer
            sourceProgram selectedTests.length prepared := by
      simpa [Assembly.InteractionSemantics.Source.openRunUntilTransfer,
        hProgram', guard, dispatch, prepared,
        hFront, hStartEq, List.append_assoc] using hGuardRunRaw
    have hResolvedDispatch :
        TypedCfg.Preservation.Terminator.ResolvedCaseLabels
          ((pre ++ guard) ++ dispatch ++ post)
          (spec.before ++ spec.site :: spec.after) := by
      rw [hProgram'] at hResolved'
      simpa [List.append_assoc] using hResolved'
    have hSelectedRaw :=
      selectedTestPrefix_openRun
        (depth := 0) (before := spec.before)
        (after := spec.after) (site := spec.site)
        (front := []) (suffix := front ++ suffix)
        (token := token) (pre := pre ++ guard) (post := post)
        (state := prepared)
        (by omega) (by simp) hBefore hToken
        (by exact hDispatchFits)
        (by simp [prepared])
        hResolvedDispatch
    rcases hSelectedRaw with
      ⟨caseDest, hCaseDest, hSelectedRun⟩
    have hCasePc' := hCasePc
    rw [hProgram'] at hCasePc'
    have hCaseDestEq : caseDest = spec.casePc := by
      have hBoth :
          some caseDest = some spec.casePc := by
        calc
          some caseDest =
              ((pre ++ guard) ++ dispatch ++ post).labelPc
                spec.site.caseLabel := hCaseDest.symm
          _ = some spec.casePc := by
            simpa [List.append_assoc] using hCasePc'
      exact Option.some.inj hBoth
    subst caseDest
    rw [hTraceLength, hTestCode]
    simp only [List.length_append]
    rw [Nat.add_comm, hGuardRun]
    have hPreparedStart :
        { prepared with
          stack := [] ++ token :: (front ++ suffix) } =
          prepared := by
      simp [prepared]
    rw [show
      Assembly.InteractionSemantics.Source.openRunUntilTransfer
          sourceProgram selectedTests.length prepared =
        .done
          (.ok
            (.running
              { prepared with
                stack := [] ++ token :: (front ++ suffix)
                pc := EvmYul.UInt256.ofNat spec.casePc })) by
      simpa [selectedTests, hProgram', guard, hPreparedStart,
        dispatch, List.append_assoc] using hSelectedRun]
    exact
      ⟨_,
        rfl, rfl,
        by simp [usesSharedLayout, hShared, prepared],
        by
          simp [usesSharedLayout, hShared, prepared,
            Assembly.SameRuntimeData,
            Assembly.eraseRuntimeControl]⟩
  · have hLowered :
        TypedCfg.Terminator.returnDispatchLoweredCode depth sites =
          TypedCfg.Terminator.returnDispatchCode depth sites := by
      unfold TypedCfg.Terminator.returnDispatchLoweredCode
      rw [if_neg hShared]
    have hTestCode :
        selectedTestCode depth sites spec.before spec.site =
          TypedCfg.Terminator.returnDispatchTestCases
            depth (spec.before ++ [spec.site]) := by
      simp [selectedTestCode, guardCode, caseDepth,
        usesSharedLayout, hShared]
    have hProgram' := hProgram
    have hFits' := hFits
    rw [hLowered] at hProgram' hFits'
    have hResolved' := hResolved
    rw [hSplit] at hResolved'
    have hSelectedRaw :=
      selectedTestPrefix_openRun
        (depth := depth) (before := spec.before)
        (after := spec.after) (site := spec.site)
        (front := front) (suffix := suffix) (token := token)
        (pre := pre) (post := post) (state := source)
        hBound hFront hBefore hToken
        (by simpa [hSplit] using hFits')
        (by simpa [hStack] using hSourcePc)
        (by
          simpa [hProgram', hSplit] using hResolved')
    rcases hSelectedRaw with
      ⟨caseDest, hCaseDest, hSelectedRun⟩
    have hCasePc' := hCasePc
    rw [hProgram'] at hCasePc'
    have hCaseDestEq : caseDest = spec.casePc := by
      have hBoth :
          some caseDest = some spec.casePc := by
        calc
          some caseDest =
              (pre ++
                TypedCfg.Terminator.returnDispatchCode
                  depth (spec.before ++ spec.site :: spec.after) ++
                post).labelPc spec.site.caseLabel :=
            hCaseDest.symm
          _ = some spec.casePc := by
            simpa [hSplit] using hCasePc'
      exact Option.some.inj hBoth
    subst caseDest
    have hSourceStart :
        { source with stack := front ++ token :: suffix } =
          source := by
      rw [← hStack]
    rw [hTraceLength, hTestCode]
    rw [show
      Assembly.InteractionSemantics.Source.openRunUntilTransfer
          sourceProgram
          (TypedCfg.Terminator.returnDispatchTestCases
            depth (spec.before ++ [spec.site])).length
          source =
        .done
          (.ok
            (.running
              { source with
                stack := front ++ token :: suffix
                pc := EvmYul.UInt256.ofNat spec.casePc })) by
      simpa [hSourceStart, hProgram', hSplit] using hSelectedRun]
    exact
      ⟨_,
        rfl, rfl,
        by simp [usesSharedLayout, hShared],
        by
          simp [usesSharedLayout, hShared,
            Assembly.SameRuntimeData,
            Assembly.eraseRuntimeControl]⟩

theorem CaseSpec.source_test_runningAt_case
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {termPc depth : Nat} {sites : List ReturnSite}
    {spec : CaseSpec}
    {pre post : Assembly.Program}
    {source : EVMState} {front suffix : List Word}
    {token : Word}
    (hValid :
      spec.Valid sourceProgram artifact termPc depth sites)
    (hUnique :
      ReturnAddressRelation.TokensUnique sites)
    (hProgram :
      sourceProgram =
        pre ++
          TypedCfg.Terminator.returnDispatchLoweredCode
            depth sites ++ post)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchLoweredCode
          depth sites))
    (hSourcePc :
      source.pc = pre.pcAfter)
    (hStack :
      source.stack = front ++ token :: suffix)
    (hFront : front.length = depth)
    (hToken : spec.site.token = token)
    (hBound : depth < 16)
    (hResolved :
      TypedCfg.Preservation.Terminator.ResolvedCaseLabels
        sourceProgram sites) :
    Simulation.Interaction.AllDone
      (fun
        (outcome :
          Except Assembly.EVMException Assembly.StepResult) =>
        ∃ selected,
          outcome = .ok (.running selected) ∧
            selected.pc = EvmYul.UInt256.ofNat spec.casePc ∧
              selected.stack =
                (if usesSharedLayout depth sites then
                    token :: front ++ suffix
                  else
                    front ++ token :: suffix) ∧
              Assembly.SameRuntimeData selected
                { source with
                  stack :=
                    if usesSharedLayout depth sites then
                      token :: front ++ suffix
                    else
                      front ++ token :: suffix })
      (Assembly.InteractionSemantics.Source.openRunUntilTransfer
        sourceProgram spec.testTrace.length source) := by
  obtain
      ⟨selected, hRun, hPc, hStack', hRuntime⟩ :=
    source_test_eq_runningAt_case
      (spec := spec) (pre := pre) (post := post)
      hValid hUnique hProgram hFits hSourcePc hStack hFront
      hToken hBound hResolved
  rw [hRun]
  exact
    Simulation.Interaction.AllDone.done
      ⟨selected, rfl, hPc, hStack', hRuntime⟩

def CaseSpec.targetOpenRun
    (artifact : Artifact) (spec : CaseSpec)
    (state : EVMState) (byteSuffix : List UInt8 := []) :
    Assembly.InteractionSemantics.OpenStepResult := do
  let testResult ←
    Preparation.OrdinaryTrace.targetOpenUntil
      (fun _ => false)
      (Assembly.Bytecode.ofList
        (artifact.bytes.toList ++ byteSuffix))
      spec.testTrace state
  match testResult with
  | .halted halt =>
      pure (.halted halt)
  | .running selected =>
      Preparation.OrdinaryTrace.targetOpenUntil
        (fun _ => false)
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        spec.caseTrace selected

def CaseSpec.sourceOpenRun
    (sourceProgram : Assembly.Program) (spec : CaseSpec)
    (state : EVMState) :
    Assembly.InteractionSemantics.OpenStepResult := do
  let testResult ←
    Assembly.InteractionSemantics.Source.openRunUntilTransfer
      sourceProgram spec.testTrace.length state
  match testResult with
  | .halted halt =>
      pure (.halted halt)
  | .running selected =>
      Assembly.InteractionSemantics.Source.openRunUntilTransfer
        sourceProgram spec.caseTrace.length selected

set_option maxHeartbeats 1000000 in
theorem CaseSpec.sourceOpenRun_simulates
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {termPc depth : Nat} {sites : List ReturnSite}
    {spec : CaseSpec}
    {pre post : Assembly.Program}
    {source : EVMState} {front suffix : List Word}
    {token : Word}
    (hValid :
      spec.Valid sourceProgram artifact termPc depth sites)
    (hUnique :
      ReturnAddressRelation.TokensUnique sites)
    (hProgram :
      sourceProgram =
        pre ++
          TypedCfg.Terminator.returnDispatchLoweredCode
            depth sites ++ post)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchLoweredCode
          depth sites))
    (hSourcePc :
      source.pc = pre.pcAfter)
    (hStack :
      source.stack = front ++ token :: suffix)
    (hFront : front.length = depth)
    (hToken : spec.site.token = token)
    (hBound : depth < 16)
    (hResolvedCases :
      TypedCfg.Preservation.Terminator.ResolvedCaseLabels
        sourceProgram sites)
    (hTargets :
      ∀ site ∈ sites,
        ∃ dest,
          sourceProgram.labelPc site.target = some dest)
    (hLabels : sourceProgram.labels.Nodup) :
    ∃ outcome,
      spec.sourceOpenRun sourceProgram source = .done outcome ∧
        TypedCfg.Preservation.Outcome.Simulates sourceProgram
          (.jump spec.site.target
            { source with stack := front ++ suffix })
          outcome := by
  have hValidCopy := hValid
  rcases hValid with
    ⟨hSplit, hTestTrace, hCasePc, hCaseTrace⟩
  obtain
      ⟨selected, hTestRun, hSelectedPc,
        hSelectedStack, hSelectedRuntime⟩ :=
    source_test_eq_runningAt_case
      (spec := spec) (pre := pre) (post := post)
      hValidCopy hUnique hProgram hFits hSourcePc hStack hFront
      hToken hBound hResolvedCases
  let guard := guardCode depth sites
  let dispatchDepth := caseDepth depth sites
  let tests :=
    TypedCfg.Terminator.returnDispatchTests dispatchDepth sites
  let cases :=
    TypedCfg.Terminator.returnDispatchCases dispatchDepth sites
  have hProgramCases :
      sourceProgram =
        pre ++ guard ++ tests ++ cases ++ post := by
    calc
      sourceProgram =
          pre ++
            TypedCfg.Terminator.returnDispatchLoweredCode
              depth sites ++ post :=
        hProgram
      _ =
          pre ++
              (guard ++
                TypedCfg.Terminator.returnDispatchCode
                  dispatchDepth sites) ++
            post := by
        rw [loweredCode_eq]
      _ = pre ++ guard ++ tests ++ cases ++ post := by
        simp [guard, dispatchDepth, tests, cases,
          TypedCfg.Terminator.returnDispatchCode,
          List.append_assoc]
  have hFitsAll :
      Assembly.Program.PCFitsFrom pre
        (guard ++ (tests ++ cases)) := by
    rw [loweredCode_eq] at hFits
    simpa [guard, dispatchDepth, tests, cases,
      TypedCfg.Terminator.returnDispatchCode,
      List.append_assoc] using hFits
  have hAfterGuardFits :
      Assembly.Program.PCFitsFrom (pre ++ guard)
        (tests ++ cases) :=
    Assembly.Program.PCFitsFrom.right hFitsAll
  have hCasesFits :
      Assembly.Program.PCFitsFrom
        (pre ++ guard ++ tests) cases := by
    simpa [List.append_assoc] using
      Assembly.Program.PCFitsFrom.right hAfterGuardFits
  have hResolvedTargets :=
    resolvedTargets_of_sites
      (depth := dispatchDepth) hTargets
  rw [hProgramCases] at hResolvedTargets
  let casePrefix :=
    TypedCfg.Terminator.returnDispatchCases
      dispatchDepth spec.before
  let caseTail :=
    TypedCfg.Terminator.returnDispatchCases
      dispatchDepth spec.after
  let cleanup :=
    Assembly.StackShuffle.removeBuriedUnder dispatchDepth
  have hProgramAtCase :
      sourceProgram =
        (pre ++ guard ++ tests ++ casePrefix) ++
          Assembly.Instr.label spec.site.caseLabel ::
        (cleanup ++
              Assembly.Instr.jump spec.site.target ::
                caseTail ++ post) := by
    rw [hProgramCases]
    simp [cases, casePrefix, caseTail, cleanup, hSplit,
      TypedCfg.Terminator.returnDispatchCases,
      TypedCfg.Terminator.returnDispatchCase,
      List.append_assoc]
  have hInternalCase :
      sourceProgram.labelPc spec.site.caseLabel =
        some (pre ++ guard ++ tests ++ casePrefix).byteLength := by
    rw [hProgramAtCase]
    exact
      Assembly.Program.labelPc_append_label_eq_of_labels_nodup
        (pre ++ guard ++ tests ++ casePrefix)
        (cleanup ++
          Assembly.Instr.jump spec.site.target ::
            caseTail ++ post)
        (by simpa [hProgramAtCase] using hLabels)
  have hCasePcEq :
      spec.casePc =
        (pre ++ guard ++ tests ++ casePrefix).byteLength := by
    rw [hInternalCase] at hCasePc
    exact (Option.some.inj hCasePc).symm
  have hCaseTraceLength :=
    Preparation.ordinaryTrace?_length hCaseTrace
  unfold CaseSpec.sourceOpenRun
  rw [hTestRun]
  change
    ∃ outcome,
      Assembly.InteractionSemantics.Source.openRunUntilTransfer
          sourceProgram spec.caseTrace.length selected =
        .done outcome ∧
      TypedCfg.Preservation.Outcome.Simulates sourceProgram
        (.jump spec.site.target
          { source with stack := front ++ suffix })
        outcome
  by_cases hShared :
      2 < depth * (sites.length - 1)
  · exact by
      have hGuard :
          guard =
            Assembly.StackShuffle.guardedLiftBuriedToTop depth := by
        simp [guard, guardCode, usesSharedLayout, hShared]
      have hDispatchDepth :
          dispatchDepth = 0 := by
        simp [dispatchDepth, caseDepth, usesSharedLayout, hShared]
      have hCaseDepth :
          caseDepth depth sites = 0 := by
        simp [caseDepth, usesSharedLayout, hShared]
      have hCaseDepthSplit :
          caseDepth depth
              (spec.before ++ spec.site :: spec.after) =
            0 := by
        rw [← hSplit]
        exact hCaseDepth
      have hSelectedStack' :
          selected.stack = token :: front ++ suffix := by
        simpa [usesSharedLayout, hShared] using hSelectedStack
      have hSelectedStart :
          { selected with stack := [] ++ token :: (front ++ suffix) } =
            selected := by
        rw [show
          [] ++ token :: (front ++ suffix) = selected.stack by
            simpa using hSelectedStack'.symm]
      have hSelectedStart' :
          { selected with stack := token :: (front ++ suffix) } =
            selected := by
        simpa using hSelectedStart
      have hCaseRun :=
        TypedCfg.InteractionPreservation.Terminator.returnDispatchCase_openRunUntilTransfer
          (fun _ => false)
          (depth := 0) (before := spec.before)
          (after := spec.after) (site := spec.site)
          (front := []) (suffix := front ++ suffix)
          (pre := pre ++ guard ++ tests) (post := post)
          (state := selected) (fuel := 0)
          (by omega) (by simp)
          (by
            simpa [cases, hDispatchDepth, hSplit] using hCasesFits)
          (by
            simpa [hSelectedStart, Assembly.Program.pcAfter,
              casePrefix, hDispatchDepth, hCasePcEq] using
              hSelectedPc)
          (by
            simpa [cases, hDispatchDepth, hSplit,
              List.append_assoc] using hResolvedTargets)
          rfl
      rcases hCaseRun with
        ⟨targetDest, hTargetDest, hCaseRun⟩
      simp only [Nat.zero_add, List.nil_append] at hCaseRun
      rw [hToken, hSelectedStart'] at hCaseRun
      rw [hCaseTraceLength]
      rw [show
        Assembly.InteractionSemantics.Source.openRunUntilTransfer
            sourceProgram
            (TypedCfg.Terminator.returnDispatchCase
              (caseDepth depth sites) spec.site).length selected =
          .done
            (.ok
              (.running
                (Assembly.Source.jumpPc targetDest
                  { selected with stack := front ++ suffix }))) by
        simpa [Assembly.InteractionSemantics.Source.openRunUntilTransfer,
          hProgramCases, cases, hDispatchDepth, hCaseDepth,
          hCaseDepthSplit, hSplit, List.append_assoc] using hCaseRun]
      refine ⟨_, rfl, targetDest, ?_, ?_, ?_⟩
      · simpa [hProgramCases, cases, hDispatchDepth, hSplit,
          List.append_assoc] using hTargetDest
      · rfl
      · apply sameRuntimeData_of_shared_stack
        · simpa [Assembly.Source.jumpPc] using
            Assembly.SameRuntimeData.shared_eq hSelectedRuntime
        · rfl
  · exact by
      have hGuard :
          guard = [] := by
        simp [guard, guardCode, usesSharedLayout, hShared]
      have hDispatchDepth :
          dispatchDepth = depth := by
        simp [dispatchDepth, caseDepth, usesSharedLayout, hShared]
      have hCaseDepth :
          caseDepth depth sites = depth := by
        simp [caseDepth, usesSharedLayout, hShared]
      have hCaseDepthSplit :
          caseDepth depth
              (spec.before ++ spec.site :: spec.after) =
            depth := by
        rw [← hSplit]
        exact hCaseDepth
      have hSelectedStack' :
          selected.stack = front ++ token :: suffix := by
        simpa [usesSharedLayout, hShared] using hSelectedStack
      have hSelectedStart :
          { selected with stack := front ++ token :: suffix } =
            selected := by
        rw [← hSelectedStack']
      have hCaseRun :=
        TypedCfg.InteractionPreservation.Terminator.returnDispatchCase_openRunUntilTransfer
          (fun _ => false)
          (depth := depth) (before := spec.before)
          (after := spec.after) (site := spec.site)
          (front := front) (suffix := suffix)
          (pre := pre ++ guard ++ tests) (post := post)
          (state := selected) (fuel := 0)
          hBound hFront
          (by
            simpa [cases, hDispatchDepth, hSplit] using hCasesFits)
          (by
            simpa [hSelectedStart, Assembly.Program.pcAfter,
              casePrefix, hDispatchDepth, hCasePcEq] using
              hSelectedPc)
          (by
            simpa [cases, hDispatchDepth, hSplit,
              List.append_assoc] using hResolvedTargets)
          rfl
      rcases hCaseRun with
        ⟨targetDest, hTargetDest, hCaseRun⟩
      simp only [Nat.zero_add] at hCaseRun
      rw [hToken, hSelectedStart] at hCaseRun
      rw [hCaseTraceLength]
      rw [show
        Assembly.InteractionSemantics.Source.openRunUntilTransfer
            sourceProgram
            (TypedCfg.Terminator.returnDispatchCase
              (caseDepth depth sites) spec.site).length selected =
          .done
            (.ok
              (.running
                (Assembly.Source.jumpPc targetDest
                  { selected with stack := front ++ suffix }))) by
        simpa [Assembly.InteractionSemantics.Source.openRunUntilTransfer,
          hProgramCases, cases, hDispatchDepth, hCaseDepth,
          hCaseDepthSplit, hSplit, List.append_assoc] using hCaseRun]
      refine ⟨_, rfl, targetDest, ?_, ?_, ?_⟩
      · simpa [hProgramCases, cases, hDispatchDepth, hSplit,
          List.append_assoc] using hTargetDest
      · rfl
      · apply sameRuntimeData_of_shared_stack
        · simpa [Assembly.Source.jumpPc] using
            Assembly.SameRuntimeData.shared_eq hSelectedRuntime
        · rfl

set_option maxHeartbeats 1000000 in
theorem CaseSpec.targetOpenRun_rel
    {sourceProgram : Assembly.Program}
    {pinnedPushPcs : List Nat} {artifact : Artifact}
    {termPc depth : Nat} {sites : List ReturnSite}
    {spec : CaseSpec} {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile?
          sourceProgram pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hValid :
      spec.Valid sourceProgram artifact termPc depth sites)
    (hFull :
      Preparation.FullStateRel sourceProgram artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat termPc)
    (hTestEnd :
      Simulation.Interaction.AllDone
        (fun
          (outcome :
            Except Assembly.EVMException Assembly.StepResult) =>
          match outcome with
          | .ok (.running selected) =>
              selected.pc = EvmYul.UInt256.ofNat spec.casePc
          | _ => True)
        (Assembly.InteractionSemantics.Source.openRunUntilTransfer
          sourceProgram spec.testTrace.length source)) :
    Simulation.Interaction.Rel
      (Preparation.FullOutcomeRel sourceProgram artifact)
      (spec.targetOpenRun artifact target byteSuffix)
      (spec.sourceOpenRun sourceProgram source) := by
  rcases hValid with
    ⟨hSplit, hTestTrace, hCasePc, hCaseTrace⟩
  have hTestRel :=
    Preparation.OrdinaryTrace.targetOpenUntil_rel
      (Preparation.ordinaryTrace?_sound hTestTrace)
      hCompile byteSuffix hFull hSourcePc
  have hTestStrong :=
    Simulation.Interaction.Rel.strengthen_right
      hTestRel hTestEnd
  unfold CaseSpec.targetOpenRun CaseSpec.sourceOpenRun
  apply Simulation.Interaction.Rel.bind_custom hTestStrong
  intro targetDone sourceDone hDone
  rcases hDone with ⟨hRelated, hEnd⟩
  cases hRelated with
  | error hError =>
      exact .done (.error hError)
  | ok hResult =>
      rename_i targetResult sourceResult
      cases targetResult with
      | halted targetHalt =>
          cases sourceResult with
          | running sourceMid =>
              simp [Preparation.FullStepResultRel] at hResult
          | halted sourceHalt =>
              exact .done (.ok hResult)
      | running targetMid =>
          cases sourceResult with
          | halted sourceHalt =>
              simp [Preparation.FullStepResultRel] at hResult
          | running sourceMid =>
              change
                Preparation.FullStateRel sourceProgram artifact
                  targetMid sourceMid at hResult
              have hCaseRel :=
                Preparation.OrdinaryTrace.targetOpenUntil_rel
                  (Preparation.ordinaryTrace?_sound hCaseTrace)
                  hCompile byteSuffix hResult hEnd
              simpa using hCaseRel

def Spec.targetTermOpenRun
    (artifact : Artifact) (spec : Spec)
    (state : EVMState) (byteSuffix : List UInt8 := []) :
    Assembly.InteractionSemantics.OpenStepResult :=
  match state.stack[spec.depth]? with
  | none =>
      Preparation.OrdinaryTrace.targetOpenUntil
        (fun _ => false)
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        spec.rejectTrace state
  | some token =>
      match spec.findCase? token with
      | none =>
          Preparation.OrdinaryTrace.targetOpenUntil
            (fun _ => false)
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            spec.rejectTrace state
      | some caseSpec =>
          caseSpec.targetOpenRun artifact state byteSuffix

set_option maxHeartbeats 2000000 in
theorem Spec.targetTermOpenRun_rel
    {sourceProgram : Assembly.Program}
    {pinnedPushPcs : List Nat} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : Spec}
    {pre post : Assembly.Program}
    {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile?
          sourceProgram pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hValid :
      spec.ValidForBlock sourceProgram artifact block)
    (hProgram :
      sourceProgram =
        pre ++
          TypedCfg.Terminator.returnDispatchLoweredCode
            spec.depth spec.sites ++ post)
    (hFits :
      Assembly.Program.PCFitsFrom pre
        (TypedCfg.Terminator.returnDispatchLoweredCode
          spec.depth spec.sites))
    (hFull :
      Preparation.FullStateRel sourceProgram artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat spec.termPc)
    (hStart :
      source.pc = pre.pcAfter)
    (hUnique :
      ReturnAddressRelation.TokensUnique spec.sites)
    (hTargets :
      ∀ site ∈ spec.sites,
        ∃ dest,
          sourceProgram.labelPc site.target = some dest)
    (hLabels : sourceProgram.labels.Nodup) :
    Simulation.Interaction.Rel
      (Preparation.FullOutcomeRel sourceProgram artifact)
      (spec.targetTermOpenRun artifact target byteSuffix)
      (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
        sourceProgram
        (TypedCfg.Terminator.returnDispatchLoweredCode
          spec.depth spec.sites).length
        source) := by
  have hValidCopy := hValid
  rcases hValid with
    ⟨bodyCode, output, termCode, hTerm, hSmall, hBound,
      hBody, hOutput, hDepth, hTermLower, hTermCode,
      hEntry, hBlockLabel, hTermPc, hPrefix,
      hCases, hCaseValid, hReject⟩
  rw [hTerm] at hTermLower
  rw [hTermCode] at hTermLower
  have hStandardLower :
      TypedCfg.Terminator.lowerAt? output
          (.returnDispatch spec.depth spec.sites) =
        some
          (TypedCfg.Terminator.returnDispatchLoweredCode
            spec.depth spec.sites) := by
    simpa [LateReturnProbe.Terminator.lowerAt?, hSmall] using
      hTermLower
  have hSites : spec.sites ≠ [] := by
    intro hNil
    rw [hNil] at hStandardLower
    simp [TypedCfg.Terminator.lowerAt?, hDepth] at hStandardLower
  have hResolvedCases :=
    Spec.resolvedCaseLabels hValidCopy
  have hResolvedTargets :=
    resolvedTargets_of_sites
      (depth := spec.depth) hTargets
  have hResolvedControl :
      TypedCfg.Preservation.Terminator.ResolvedControl
        sourceProgram
        (.returnDispatch spec.depth spec.sites) := by
    refine ⟨hResolvedTargets, ?_⟩
    intro label hLabel
    simp only [TypedCfg.Terminator.definedLabels,
      List.mem_map] at hLabel
    rcases hLabel with ⟨site, hSite, rfl⟩
    exact hResolvedCases site hSite
  have hStandardRel :
      Simulation.Interaction.Rel
        (TypedCfg.Preservation.Block.RunSimulates sourceProgram)
        (.done
          (TypedCfg.Block.runTermChecked output
            (.returnDispatch spec.depth spec.sites) source))
        (Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          sourceProgram
          (TypedCfg.Terminator.returnDispatchLoweredCode
            spec.depth spec.sites).length
          source) := by
    have hRel :=
      TypedCfg.InteractionPreservation.Terminator.lowerAt?_openRunUntilTransfer_rel
        (pre := pre) (post := post)
        hStandardLower hFits hStart
        (by simpa [hProgram] using hResolvedControl)
        (by simpa [hProgram] using hLabels)
    simpa [hProgram,
      TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy]
      using hRel
  have hRejectLength :=
    Preparation.ordinaryTrace?_length hReject
  have hRejectPositive :
      1 ≤ spec.rejectTrace.length := by
    rw [hRejectLength]
    simp [rejectCode,
      TypedCfg.Terminator.returnDispatchTests]
    omega
  have hCodePositive :
      1 ≤
        (TypedCfg.Terminator.returnDispatchLoweredCode
          spec.depth spec.sites).length := by
    rw [loweredCode_eq]
    simp [TypedCfg.Terminator.returnDispatchCode,
      TypedCfg.Terminator.returnDispatchTests]
    omega
  have hTargetStack :
      target.stack = source.stack :=
    Assembly.SameRuntimeData.stack_eq
      (Preparation.FullStateRel.runtimeData hFull)
  cases hGet : source.stack[spec.depth]? with
  | none =>
      have hTargetGet :
          target.stack[spec.depth]? = none := by
        rw [hTargetStack, hGet]
      have hRejectRel :=
        Preparation.OrdinaryTrace.targetOpenUntil_rel
          (Preparation.ordinaryTrace?_sound hReject)
          hCompile byteSuffix hFull hSourcePc
      have hPathError :
          Assembly.InteractionSemantics.Source.openRunUntilTransfer
              sourceProgram spec.rejectTrace.length source =
            .done (.error .StackUnderflow) := by
        have hRun :=
          returnDispatchLowered_missing_openRun
            (fun _ => false)
            (depth := spec.depth)
            (fuel := spec.rejectTrace.length)
            (sites := spec.sites)
            (pre := pre) (post := post) (state := source)
            hRejectPositive hBound hSites hFits hStart hGet
        simpa [Assembly.InteractionSemantics.Source.openRunUntilTransfer,
          hProgram] using hRun
      have hFullError :
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              sourceProgram
              (TypedCfg.Terminator.returnDispatchLoweredCode
                spec.depth spec.sites).length
              source =
            .done (.error .StackUnderflow) := by
        have hRun :=
          returnDispatchLowered_missing_openRun
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            (depth := spec.depth)
            (fuel :=
              (TypedCfg.Terminator.returnDispatchLoweredCode
                spec.depth spec.sites).length)
            (sites := spec.sites)
            (pre := pre) (post := post) (state := source)
            hCodePositive hBound hSites hFits hStart hGet
        simpa [hProgram] using hRun
      rw [hPathError] at hRejectRel
      rw [hFullError]
      simpa [Spec.targetTermOpenRun, hTargetGet] using hRejectRel
  | some token =>
      have hTargetGet :
          target.stack[spec.depth]? = some token := by
        rw [hTargetStack, hGet]
      cases hFind : spec.findCase? token with
      | none =>
          obtain ⟨front, suffix, hStack, hFront⟩ :=
            TypedCfg.Preservation.List.getElem?_eq_some_split hGet
          have hSourceStack :
              { source with stack := front ++ token :: suffix } =
                source := by
            rw [← hStack]
          have hNe :=
            Spec.findCase?_none_all_ne hCases hFind
          have hResolvedCases' :
              TypedCfg.Preservation.Terminator.ResolvedCaseLabels
                (pre ++
                  TypedCfg.Terminator.returnDispatchLoweredCode
                    spec.depth spec.sites ++ post)
                spec.sites := by
            simpa [hProgram] using hResolvedCases
          have hRejectRel :=
            Preparation.OrdinaryTrace.targetOpenUntil_rel
              (Preparation.ordinaryTrace?_sound hReject)
              hCompile byteSuffix hFull hSourcePc
          have hPathError :
              Assembly.InteractionSemantics.Source.openRunUntilTransfer
                  sourceProgram spec.rejectTrace.length source =
                .done (.error .InvalidInstruction) := by
            have hRun :=
              rejectCode_unknown_openRun
                (fun _ => false)
                (depth := spec.depth) (sites := spec.sites)
                (front := front) (suffix := suffix) (token := token)
                (pre := pre) (post := post) (state := source)
                0 hBound hFront hNe hFits
                (by simpa [hSourceStack] using hStart)
                hResolvedCases'
            simpa [Assembly.InteractionSemantics.Source.openRunUntilTransfer,
              hRejectLength, hProgram, hSourceStack] using hRun
          let caseCode :=
            TypedCfg.Terminator.returnDispatchCases
              (caseDepth spec.depth spec.sites) spec.sites
          have hFullLength :
              caseCode.length +
                  (rejectCode spec.depth spec.sites).length =
                (TypedCfg.Terminator.returnDispatchLoweredCode
                  spec.depth spec.sites).length := by
            rw [loweredCode_eq]
            simp [caseCode, rejectCode,
              TypedCfg.Terminator.returnDispatchCode]
            omega
          have hFullError :
              Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                  TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
                  sourceProgram
                  (TypedCfg.Terminator.returnDispatchLoweredCode
                    spec.depth spec.sites).length
                  source =
                .done (.error .InvalidInstruction) := by
            have hRun :=
              rejectCode_unknown_openRun
                TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
                (depth := spec.depth) (sites := spec.sites)
                (front := front) (suffix := suffix) (token := token)
                (pre := pre) (post := post) (state := source)
                caseCode.length hBound hFront hNe hFits
                (by simpa [hSourceStack] using hStart)
                hResolvedCases'
            simpa [hProgram, hSourceStack, hFullLength] using hRun
          rw [hPathError] at hRejectRel
          rw [hFullError]
          simpa [Spec.targetTermOpenRun, hTargetGet, hFind] using
            hRejectRel
      | some caseSpec =>
          have hCaseMem :=
            Spec.findCase?_some_mem hFind
          have hCaseValid :=
            hCaseValid caseSpec hCaseMem
          have hToken :=
            Spec.findCase?_some_token hFind
          obtain ⟨front, suffix, hStack, hFront⟩ :=
            TypedCfg.Preservation.List.getElem?_eq_some_split hGet
          have hTestFacts :=
            CaseSpec.source_test_runningAt_case
              (spec := caseSpec)
              (pre := pre) (post := post)
              hCaseValid hUnique hProgram hFits hStart
              hStack hFront hToken hBound hResolvedCases
          have hTestEnd :
              Simulation.Interaction.AllDone
                (fun
                  (outcome :
                    Except Assembly.EVMException Assembly.StepResult) =>
                  match outcome with
                  | .ok (.running selected) =>
                      selected.pc =
                        EvmYul.UInt256.ofNat caseSpec.casePc
                  | _ => True)
                (Assembly.InteractionSemantics.Source.openRunUntilTransfer
                  sourceProgram caseSpec.testTrace.length source) := by
            apply Simulation.Interaction.AllDone.mono hTestFacts
            intro outcome hOutcome
            rcases hOutcome with
              ⟨selected, rfl, hSelectedPc,
                hSelectedStack, hSelectedRuntime⟩
            exact hSelectedPc
          have hTargetPath :=
            CaseSpec.targetOpenRun_rel
              hCompile byteSuffix hCaseValid hFull hSourcePc hTestEnd
          obtain ⟨pathDone, hPathRun, hPathDone⟩ :=
            CaseSpec.sourceOpenRun_simulates
              (spec := caseSpec)
              (pre := pre) (post := post)
              hCaseValid hUnique hProgram hFits hStart
              hStack hFront hToken hBound hResolvedCases
              hTargets hLabels
          rw [hPathRun] at hTargetPath
          have hBefore :
              ∀ prior ∈ caseSpec.before,
                prior.token ≠ token := by
            have hBeforeRaw :=
              tokensUnique_before_ne
                (hUnique := by
                  simpa [hCaseValid.1] using hUnique)
            intro prior hPrior hPriorToken
            exact
              (hBeforeRaw prior hPrior)
                (hPriorToken.trans hToken.symm)
          have hFindTarget :
              TypedCfg.Block.ReturnSite.findTarget? token spec.sites =
                some caseSpec.site.target := by
            rw [hCaseValid.1]
            exact
              findTarget?_eq_some_of_split hBefore hToken
          have hErase :
              source.stack.eraseIdx spec.depth =
                front ++ suffix := by
            calc
              source.stack.eraseIdx spec.depth =
                  (front ++ token :: suffix).eraseIdx front.length := by
                    rw [hStack, hFront]
              _ = front ++ suffix :=
                TypedCfg.Preservation.List.eraseIdx_append_at_length
                  front suffix token
          obtain
              ⟨standardDone, hStandardRun, hStandardDone⟩ :=
            Simulation.Interaction.Rel.done_left hStandardRel
          rw [hStandardRun]
          have hFullDone :
              TypedCfg.Preservation.Outcome.Simulates
                sourceProgram
                (.jump caseSpec.site.target
                  { source with stack := front ++ suffix })
                standardDone := by
            rw [
              TypedCfg.Preservation.Block.runTermChecked_simulates_iff]
              at hStandardDone
            simpa [TypedCfg.Block.runTerm, hDepth, hGet,
              hFindTarget, hErase] using hStandardDone
          have hSelectedRel :
              Simulation.Interaction.Rel
                (Preparation.FullOutcomeRel sourceProgram artifact)
                (caseSpec.targetOpenRun artifact target byteSuffix)
                (.done standardDone) := by
            obtain
                ⟨targetDone, hTargetRun, hTargetDone⟩ :=
              Simulation.Interaction.Rel.done_left
                (Simulation.Interaction.Rel.symm hTargetPath)
            rw [hTargetRun]
            exact
              Simulation.Interaction.Rel.done
                (fullOutcomeRel_replace_source_jump
                  hTargetDone hPathDone hFullDone)
          simpa [Spec.targetTermOpenRun, hTargetGet, hFind]
            using hSelectedRel

def Spec.targetOpenRun
    (artifact : Artifact) (spec : Spec)
    (state : EVMState) (byteSuffix : List UInt8 := []) :
    Assembly.InteractionSemantics.OpenStepResult := do
  let prefixResult ←
    Assembly.Compact.InteractionSemantics.openRunNResult
      (Assembly.Bytecode.ofList
        (artifact.bytes.toList ++ byteSuffix))
      (Preparation.SimpleTrace.targetFuel spec.prefixTrace)
      state
  match prefixResult with
  | .halted halt =>
      pure (.halted halt)
  | .running mid =>
      spec.targetTermOpenRun artifact mid byteSuffix

def CaseSpec.fuelBudget (spec : CaseSpec) : Nat :=
  Preparation.OrdinaryTrace.targetFuel spec.testTrace +
    Preparation.OrdinaryTrace.targetFuel spec.caseTrace

def Spec.termFuelBudget (spec : Spec) : Nat :=
  Preparation.OrdinaryTrace.targetFuel spec.rejectTrace +
    (spec.cases.map CaseSpec.fuelBudget).sum

def Spec.fuelBudget (spec : Spec) : Nat :=
  Preparation.SimpleTrace.targetFuel spec.prefixTrace +
    spec.termFuelBudget

theorem Spec.sourceRun_eq_compiled
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : Spec}
    {source : EVMState}
    (hValid :
      spec.ValidForBlock sourceProgram artifact block) :
    (do
      let prefixResult ←
        Assembly.InteractionSemantics.Source.openRunNResult
          sourceProgram spec.prefixTrace.length source
      match prefixResult with
      | .running mid =>
          Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
            TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
            sourceProgram
            (TypedCfg.Terminator.returnDispatchLoweredCode
              spec.depth spec.sites).length
            mid
      | .halted halt =>
          pure (.halted halt)) =
      LateReturnProbe.CompiledBlock.openRun
        block sourceProgram source := by
  unfold Spec.ValidForBlock at hValid
  rcases hValid with
    ⟨bodyCode, output, termCode,
      hTerm, hSmall, hBound, hBody, hOutput, hDepth,
      hTermLower, hTermCode, hEntry, hBlockLabel, hTermPc,
      hPrefix, hCases, hCaseValid, hReject⟩
  have hPrefixLength :
      spec.prefixTrace.length =
        (Assembly.Instr.label block.label :: bodyCode).length :=
    Preparation.simpleTrace?_length hPrefix
  have hPolicy :
      TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
          block.term =
        TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy := by
    simp [hTerm,
      TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy]
  have hPrefixRun :
      Assembly.InteractionSemantics.Source.openRunNResult
          sourceProgram
          (Assembly.Instr.label block.label :: bodyCode).length
          source =
        (do
          let labelResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              sourceProgram 1 source
          match labelResult with
          | .running entry =>
              Assembly.InteractionSemantics.Source.openRunNResult
                sourceProgram bodyCode.length entry
          | .halted halt =>
              pure (.halted halt)) := by
    simpa [Nat.add_comm] using
      (Assembly.InteractionSemantics.Source.openRunNResult_add
        sourceProgram 1 bodyCode.length source)
  rw [hPrefixLength, hPrefixRun]
  unfold LateReturnProbe.CompiledBlock.openRun
  rw [hBody]
  simp only [if_pos hOutput]
  rw [hTermLower, hTermCode, hPolicy]
  simp
  let labelRun :=
    Assembly.InteractionSemantics.Source.openRunNResult
      sourceProgram 1 source
  let bodyNext :
      Assembly.StepResult →
        Assembly.InteractionSemantics.OpenStepResult
    | .running entry =>
        Assembly.InteractionSemantics.Source.openRunNResult
          sourceProgram bodyCode.length entry
    | .halted halt =>
        pure (.halted halt)
  let finish :
      Assembly.StepResult →
        Assembly.InteractionSemantics.OpenStepResult
    | .running mid =>
        Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
          TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
          sourceProgram
          (TypedCfg.Terminator.returnDispatchLoweredCode
            spec.depth spec.sites).length
          mid
    | .halted halt =>
        pure (.halted halt)
  let compiledNext :
      Assembly.StepResult →
        Assembly.InteractionSemantics.OpenStepResult
    | .halted halt =>
        pure (.halted halt)
    | .running entry => do
        let bodyResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            sourceProgram bodyCode.length entry
        match bodyResult with
        | .halted halt =>
            pure (.halted halt)
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
              TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
              sourceProgram
              (TypedCfg.Terminator.returnDispatchLoweredCode
                spec.depth spec.sites).length
              mid
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind labelRun bodyNext)
        finish =
      Simulation.Interaction.bind labelRun compiledNext
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial labelRun)
  intro labelResult hLabelDone
  cases labelResult with
  | running entry =>
      dsimp [bodyNext, compiledNext]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Assembly.InteractionSemantics.Source.openRunNResult
            sourceProgram bodyCode.length entry))
      intro bodyResult hBodyDone
      cases bodyResult <;> rfl
  | halted halt =>
      dsimp [bodyNext, finish, compiledNext]
      change
        Simulation.Interaction.bind
            (.done (.ok (Assembly.StepResult.halted halt)))
            (fun (result : Assembly.StepResult) =>
              match result with
              | Assembly.StepResult.running mid =>
                  Assembly.InteractionSemantics.Source.openRunUntilTransferWithPolicy
                    TypedCfg.InteractionSemantics.Terminator.returnDispatchFlowPolicy
                    sourceProgram
                    (TypedCfg.Terminator.returnDispatchLoweredCode
                      spec.depth spec.sites).length
                    mid
              | Assembly.StepResult.halted halt =>
                  pure (Assembly.StepResult.halted halt)) =
          .done (.ok (Assembly.StepResult.halted halt))
      rw [Simulation.Interaction.bind_done_ok]
      rfl

set_option maxHeartbeats 2000000 in
theorem certifiedStandardReturnBlock_compiled_openRun_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : TypedCfg.Block} {spec : Spec}
    {code pre post : Assembly.Program}
    {target source : EVMState} {entryPc : Nat}
    (hCompile :
      ReturnAddressProbe.Compact.compile?
          sourceProgram pinnedPushPcs =
        some artifact)
    (byteSuffix : List UInt8 := [])
    (hValid :
      spec.ValidForBlock sourceProgram artifact block)
    (hLower :
      LateReturnProbe.Block.lower? block = some code)
    (hProgram :
      sourceProgram = pre ++ code ++ post)
    (hFull :
      Preparation.FullStateRel sourceProgram artifact target source)
    (hEntry :
      sourceProgram.labelPc block.label = some entryPc)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat entryPc)
    (hStart : source.pc = pre.pcAfter)
    (hUnique :
      ReturnAddressRelation.TokensUnique spec.sites)
    (hLabels : sourceProgram.labels.Nodup)
    (hTargets :
      ∀ site ∈ spec.sites,
        ∃ dest,
          sourceProgram.labelPc site.target = some dest) :
    Simulation.Interaction.Rel
      (Preparation.FullOutcomeRel sourceProgram artifact)
      (spec.targetOpenRun artifact target byteSuffix)
      (LateReturnProbe.CompiledBlock.openRun
        block sourceProgram source) := by
  have hValidCopy := hValid
  rcases hValid with
    ⟨bodyCode, output, termCode,
      hTerm, hSmall, hBound, hBody, hOutput, hDepth,
      hTermLower, hTermCode, hSpecEntry, hBlockLabel,
      hTermPc, hPrefix, hCases, hCaseValid, hReject⟩
  have hEntryEq : spec.entryPc = entryPc := by
    rw [hEntry] at hSpecEntry
    exact (Option.some.inj hSpecEntry).symm
  have hSourceSpecPc :
      source.pc = EvmYul.UInt256.ofNat spec.entryPc := by
    simpa [hEntryEq] using hSourcePc
  let prefixCode : Assembly.Program :=
    Assembly.Instr.label block.label :: bodyCode
  have hTermLowerBlock :
      LateReturnProbe.Terminator.lowerAt? block.output block.term =
        some termCode := by
    simpa [hOutput] using hTermLower
  have hCodeEq :
      code = prefixCode ++ termCode := by
    unfold LateReturnProbe.Block.lower? at hLower
    rw [hBody] at hLower
    simp [hOutput, hTermLowerBlock] at hLower
    calc
      code =
          Assembly.Instr.label block.label ::
            (bodyCode ++ termCode) :=
        hLower.symm
      _ = prefixCode ++ termCode := by
        simp [prefixCode, List.append_assoc]
  have hWholeFits :=
    (ReturnAddressProbe.Compact.compile?_valid hCompile).sourcePCFits
  have hCodeFits :
      Assembly.Program.PCFitsFrom pre code := by
    apply Assembly.Program.PCFitsFrom.of_append
    rw [← hProgram]
    exact hWholeFits
  have hPrefixTermFits :
      Assembly.Program.PCFitsFrom pre
        (prefixCode ++ termCode) := by
    simpa [hCodeEq] using hCodeFits
  have hTermFits :
      Assembly.Program.PCFitsFrom (pre ++ prefixCode)
        (TypedCfg.Terminator.returnDispatchLoweredCode
          spec.depth spec.sites) := by
    rw [← hTermCode]
    exact
      Assembly.Program.PCFitsFrom.right hPrefixTermFits
  have hProgramTerm :
      sourceProgram =
        (pre ++ prefixCode) ++
          TypedCfg.Terminator.returnDispatchLoweredCode
            spec.depth spec.sites ++ post := by
    rw [hProgram, hCodeEq, hTermCode]
    simp [List.append_assoc]
  have hPrefixValid :=
    Preparation.simpleTrace?_sound hPrefix
  have hPrefixRel :=
    Preparation.SimpleTrace.openRunNResult_rel
      hPrefixValid hCompile byteSuffix hFull hSourceSpecPc
  have hPrefixEnd :=
    Preparation.SimpleTrace.source_runningAt_end
      hPrefixValid hCompile hSourceSpecPc
  have hPrefixStrong :=
    Simulation.Interaction.Rel.strengthen_right
      hPrefixRel hPrefixEnd
  have hSourceEq :=
    Spec.sourceRun_eq_compiled
      (source := source) hValidCopy
  rw [← hSourceEq]
  unfold Spec.targetOpenRun
  apply Simulation.Interaction.Rel.bind_custom hPrefixStrong
  intro targetDone sourceDone hDone
  rcases hDone with ⟨hRelated, hEnd⟩
  cases hRelated with
  | error hError =>
      exact .done (.error hError)
  | ok hResult =>
      rename_i targetResult sourceResult
      cases targetResult with
      | halted targetHalt =>
          cases sourceResult with
          | running sourceMid =>
              simp [Preparation.FullStepResultRel] at hResult
          | halted sourceHalt =>
              exact .done (.ok hResult)
      | running targetMid =>
          cases sourceResult with
          | halted sourceHalt =>
              simp [Preparation.FullStepResultRel] at hResult
          | running sourceMid =>
              change
                Preparation.FullStateRel sourceProgram artifact
                  targetMid sourceMid at hResult
              have hPrefixBytes :=
                Preparation.simpleTrace?_sourceByteLength hPrefix
              have hMidTermPc :
                  sourceMid.pc =
                    EvmYul.UInt256.ofNat spec.termPc := by
                change
                  sourceMid.pc =
                    EvmYul.UInt256.ofNat
                      (spec.entryPc +
                        Preparation.SimpleTrace.sourceByteLength
                          spec.prefixTrace) at hEnd
                simpa [hTermPc, prefixCode, hPrefixBytes] using hEnd
              have hMidStart :
                  sourceMid.pc = (pre ++ prefixCode).pcAfter := by
                calc
                  sourceMid.pc =
                      EvmYul.UInt256.ofNat spec.termPc :=
                    hMidTermPc
                  _ =
                      EvmYul.UInt256.ofNat
                        (spec.entryPc + prefixCode.byteLength) := by
                    rw [hTermPc]
                  _ =
                      EvmYul.UInt256.ofNat spec.entryPc +
                        EvmYul.UInt256.ofNat prefixCode.byteLength := by
                    exact
                      (Assembly.UInt256_ofNat_add
                        spec.entryPc prefixCode.byteLength).symm
                  _ =
                      source.pc +
                        EvmYul.UInt256.ofNat prefixCode.byteLength := by
                    rw [hSourceSpecPc]
                  _ =
                      pre.pcAfter +
                        EvmYul.UInt256.ofNat prefixCode.byteLength := by
                    rw [hStart]
                  _ = (pre ++ prefixCode).pcAfter :=
                    (Assembly.Program.pcAfter_append
                      pre prefixCode).symm
              have hTermRel :=
                Spec.targetTermOpenRun_rel
                  hCompile byteSuffix hValidCopy hProgramTerm
                  hTermFits hResult hMidTermPc hMidStart
                  hUnique hTargets hLabels
              simpa using hTermRel

end StandardReturn

structure DirectSpec where
  blockLabel : Label
  entryPc : Nat
  prefixTrace : List Assembly.Compact.PreparationBlock
  termTrace : List Assembly.Compact.PreparationBlock

def DirectSpec.ValidForBlock
    (spec : DirectSpec)
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Prop :=
  ∃ bodyCode output termCode,
    TypedCfg.Preservation.Terminator.Direct block.term ∧
    TypedCfg.Block.lowerBodyFrom? block.body block.input =
      some (bodyCode, output) ∧
    output = block.output ∧
    LateReturnProbe.Terminator.lowerAt? output block.term =
      some termCode ∧
    sourceProgram.labelPc block.label = some spec.entryPc ∧
    spec.blockLabel = block.label ∧
    Preparation.simpleTrace? artifact spec.entryPc
        (Assembly.Instr.label block.label :: bodyCode) =
      some spec.prefixTrace ∧
    Preparation.ordinaryTrace? artifact
        (spec.entryPc +
          Assembly.Program.byteLength
            (Assembly.Instr.label block.label :: bodyCode))
        termCode =
      some spec.termTrace

def certifyDirectSpec?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Option DirectSpec := do
  let (bodyCode, output) ←
    TypedCfg.Block.lowerBodyFrom? block.body block.input
  let _ ← if output = block.output then some () else none
  let termCode ←
    LateReturnProbe.Terminator.lowerAt? output block.term
  let entryPc ← sourceProgram.labelPc block.label
  let prefixCode : Assembly.Program :=
    .label block.label :: bodyCode
  let prefixTrace ←
    Preparation.simpleTrace? artifact entryPc prefixCode
  let termTrace ←
    Preparation.ordinaryTrace? artifact
      (entryPc + prefixCode.byteLength) termCode
  some
    { blockLabel := block.label
      entryPc
      prefixTrace
      termTrace }

theorem certifyDirectSpec?_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DirectSpec}
    (hDirect :
      TypedCfg.Preservation.Terminator.Direct block.term)
    (hCertify :
      certifyDirectSpec? sourceProgram artifact block = some spec) :
    spec.ValidForBlock sourceProgram artifact block := by
  unfold certifyDirectSpec? at hCertify
  cases hBody :
      TypedCfg.Block.lowerBodyFrom? block.body block.input with
  | none =>
      simp [hBody] at hCertify
  | some bodyResult =>
      rcases bodyResult with ⟨bodyCode, output⟩
      simp [hBody] at hCertify
      by_cases hOutput : output = block.output
      · subst output
        simp at hCertify
        cases hTermCode :
            LateReturnProbe.Terminator.lowerAt?
              block.output block.term with
        | none =>
            rw [hTermCode] at hCertify
            cases hCertify
        | some termCode =>
            rw [hTermCode] at hCertify
            cases hEntry :
                sourceProgram.labelPc block.label with
            | none =>
                rw [hEntry] at hCertify
                cases hCertify
            | some entryPc =>
                rw [hEntry] at hCertify
                simp only [Option.bind_some] at hCertify
                let prefixCode : Assembly.Program :=
                  .label block.label :: bodyCode
                cases hPrefix :
                    Preparation.simpleTrace?
                      artifact entryPc prefixCode with
                | none =>
                    rw [hPrefix] at hCertify
                    cases hCertify
                | some prefixTrace =>
                    rw [hPrefix] at hCertify
                    cases hTermTrace :
                        Preparation.ordinaryTrace? artifact
                          (entryPc +
                            ((Assembly.Instr.label block.label).byteSize +
                              bodyCode.byteLength))
                          termCode with
                    | none =>
                        rw [hTermTrace] at hCertify
                        cases hCertify
                    | some termTrace =>
                        rw [hTermTrace] at hCertify
                        simp only [Option.bind_some,
                          Option.some.injEq] at hCertify
                        subst spec
                        exact
                          ⟨bodyCode, block.output, termCode,
                            hDirect, hBody, rfl, hTermCode,
                            hEntry, rfl,
                            by simpa [prefixCode] using hPrefix,
                            by simpa [prefixCode] using hTermTrace⟩
      · simp [hOutput] at hCertify

def certifyBlockDirect?
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (block : TypedCfg.Block) : Option (Option DirectSpec) :=
  match block.term with
  | .returnDispatch _ _ =>
      some none
  | _ =>
      (certifyDirectSpec? sourceProgram artifact block).map some

theorem certifyBlockDirect?_some_valid
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DirectSpec}
    (hCertify :
      certifyBlockDirect? sourceProgram artifact block =
        some (some spec)) :
    spec.ValidForBlock sourceProgram artifact block := by
  cases hTerm : block.term with
  | returnDispatch returnCount sites =>
      simp [certifyBlockDirect?, hTerm] at hCertify
  | fallthrough next | jump next | jumpi next fallback
  | halt kind | invalid =>
      have hSpec :
          certifyDirectSpec? sourceProgram artifact block =
            some spec := by
        simpa [certifyBlockDirect?, hTerm] using hCertify
      exact
        certifyDirectSpec?_valid
          (by
            simp [TypedCfg.Preservation.Terminator.Direct, hTerm])
          hSpec

def DirectSpec.targetOpenRun
    (artifact : Artifact) (spec : DirectSpec)
    (state : EVMState) (byteSuffix : List UInt8 := []) :
    Assembly.InteractionSemantics.OpenStepResult := do
  let prefixResult ←
    Assembly.Compact.InteractionSemantics.openRunNResult
      (Assembly.Bytecode.ofList
        (artifact.bytes.toList ++ byteSuffix))
      (Preparation.SimpleTrace.targetFuel spec.prefixTrace)
      state
  match prefixResult with
  | .running mid =>
      Preparation.OrdinaryTrace.targetOpenUntil
        (fun _ => false)
        (Assembly.Bytecode.ofList
          (artifact.bytes.toList ++ byteSuffix))
        spec.termTrace mid
  | .halted halt =>
      pure (.halted halt)

theorem DirectSpec.sourceRun_eq_compiled
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DirectSpec}
    {source : EVMState}
    (hValid :
      spec.ValidForBlock sourceProgram artifact block) :
    (do
      let prefixResult ←
        Assembly.InteractionSemantics.Source.openRunNResult
          sourceProgram spec.prefixTrace.length source
      match prefixResult with
      | .running mid =>
          Assembly.InteractionSemantics.Source.openRunUntilTransfer
            sourceProgram spec.termTrace.length mid
      | .halted halt =>
          pure (.halted halt)) =
      LateReturnProbe.CompiledBlock.openRun
        block sourceProgram source := by
  unfold DirectSpec.ValidForBlock at hValid
  rcases hValid with
    ⟨bodyCode, output, termCode,
      hDirect, hBody, hOutput, hTerm,
      hEntry, hBlockLabel, hPrefix, hTermTrace⟩
  subst output
  have hPrefixLength :
      spec.prefixTrace.length =
        (Assembly.Instr.label block.label :: bodyCode).length :=
    Preparation.simpleTrace?_length hPrefix
  have hTermLength :
      spec.termTrace.length = termCode.length :=
    Preparation.ordinaryTrace?_length hTermTrace
  have hPolicy :
      TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy
          block.term =
        (fun _ => false) := by
    cases hBlockTerm : block.term <;>
      simp [TypedCfg.Preservation.Terminator.Direct,
        hBlockTerm,
        TypedCfg.InteractionSemantics.Terminator.assemblyFlowPolicy]
        at hDirect ⊢
  have hPrefixRun :
      Assembly.InteractionSemantics.Source.openRunNResult
          sourceProgram
          (Assembly.Instr.label block.label :: bodyCode).length
          source =
        (do
          let labelResult ←
            Assembly.InteractionSemantics.Source.openRunNResult
              sourceProgram 1 source
          match labelResult with
          | .running entry =>
              Assembly.InteractionSemantics.Source.openRunNResult
                sourceProgram bodyCode.length entry
          | .halted halt =>
              pure (.halted halt)) := by
    simpa [Nat.add_comm] using
      (Assembly.InteractionSemantics.Source.openRunNResult_add
        sourceProgram 1 bodyCode.length source)
  rw [hPrefixLength, hTermLength, hPrefixRun]
  unfold LateReturnProbe.CompiledBlock.openRun
  rw [hBody]
  simp only [if_pos rfl]
  rw [hTerm]
  rw [hPolicy]
  simp
  let labelRun :=
    Assembly.InteractionSemantics.Source.openRunNResult
      sourceProgram 1 source
  let bodyNext :
      Assembly.StepResult →
        Assembly.InteractionSemantics.OpenStepResult
    | .running entry =>
        Assembly.InteractionSemantics.Source.openRunNResult
          sourceProgram bodyCode.length entry
    | .halted halt =>
        pure (.halted halt)
  let finish :
      Assembly.StepResult →
        Assembly.InteractionSemantics.OpenStepResult
    | .running mid =>
        Assembly.InteractionSemantics.Source.openRunUntilTransfer
          sourceProgram termCode.length mid
    | .halted halt =>
        pure (.halted halt)
  let compiledNext :
      Assembly.StepResult →
        Assembly.InteractionSemantics.OpenStepResult
    | .halted halt =>
        pure (.halted halt)
    | .running entry => do
        let bodyResult ←
          Assembly.InteractionSemantics.Source.openRunNResult
            sourceProgram bodyCode.length entry
        match bodyResult with
        | .halted halt =>
            pure (.halted halt)
        | .running mid =>
            Assembly.InteractionSemantics.Source.openRunUntilTransfer
              sourceProgram termCode.length mid
  change
    Simulation.Interaction.bind
        (Simulation.Interaction.bind labelRun bodyNext)
        finish =
      Simulation.Interaction.bind labelRun compiledNext
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial labelRun)
  intro labelResult hLabelDone
  cases labelResult with
  | running entry =>
      dsimp [bodyNext, compiledNext]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial
          (Assembly.InteractionSemantics.Source.openRunNResult
            sourceProgram bodyCode.length entry))
      intro bodyResult hBodyDone
      cases bodyResult <;> rfl
  | halted halt =>
      dsimp [bodyNext, finish, compiledNext]
      change
        Simulation.Interaction.bind
            (.done (.ok (Assembly.StepResult.halted halt)))
            (fun (result : Assembly.StepResult) =>
              match result with
              | Assembly.StepResult.running mid =>
                  Assembly.InteractionSemantics.Source.openRunUntilTransfer
                    sourceProgram termCode.length mid
              | Assembly.StepResult.halted halt =>
                  pure (Assembly.StepResult.halted halt)) =
          .done (.ok (Assembly.StepResult.halted halt))
      rw [Simulation.Interaction.bind_done_ok]
      rfl

set_option maxHeartbeats 1000000 in
theorem certifiedDirectBlock_compiled_openRun_rel
    {sourceProgram : Assembly.Program} {pinnedPushPcs : List Nat}
    {artifact : Artifact}
    {block : TypedCfg.Block} {spec : DirectSpec}
    {target source : EVMState}
    (hCompile :
      ReturnAddressProbe.Compact.compile?
          sourceProgram pinnedPushPcs =
        some artifact)
    (hValid :
      spec.ValidForBlock sourceProgram artifact block)
    (hFull :
      Preparation.FullStateRel sourceProgram artifact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat spec.entryPc)
    (byteSuffix : List UInt8 := []) :
    Simulation.Interaction.Rel
      (Preparation.FullOutcomeRel sourceProgram artifact)
      (spec.targetOpenRun artifact target byteSuffix)
      (LateReturnProbe.CompiledBlock.openRun
        block sourceProgram source) := by
  unfold DirectSpec.ValidForBlock at hValid
  rcases hValid with
    ⟨bodyCode, output, termCode,
      hDirect, hBody, hOutput, hTerm,
      hEntry, hBlockLabel, hPrefix, hTermTrace⟩
  have hValid :
      spec.ValidForBlock sourceProgram artifact block :=
    ⟨bodyCode, output, termCode,
      hDirect, hBody, hOutput, hTerm,
      hEntry, hBlockLabel, hPrefix, hTermTrace⟩
  have hPrefixValid :=
    Preparation.simpleTrace?_sound hPrefix
  have hPrefixRel :=
    Preparation.SimpleTrace.openRunNResult_rel
      hPrefixValid hCompile byteSuffix hFull hSourcePc
  have hPrefixEnd :=
    Preparation.SimpleTrace.source_runningAt_end
      hPrefixValid hCompile hSourcePc
  have hPrefixStrong :=
    Simulation.Interaction.Rel.strengthen_right
      hPrefixRel hPrefixEnd
  have hSourceEq :=
    DirectSpec.sourceRun_eq_compiled
      (source := source) hValid
  rw [← hSourceEq]
  unfold DirectSpec.targetOpenRun
  apply Simulation.Interaction.Rel.bind_custom hPrefixStrong
  intro targetDone sourceDone hDone
  rcases hDone with ⟨hRelated, hEnd⟩
  cases hRelated with
  | error hError =>
      exact .done (.error hError)
  | ok hResult =>
      rename_i targetResult sourceResult
      cases targetResult with
      | halted targetHalt =>
          cases sourceResult with
          | running sourceMid =>
              simp [Preparation.FullStepResultRel] at hResult
          | halted sourceHalt =>
              exact .done (.ok hResult)
      | running targetMid =>
          cases sourceResult with
          | halted sourceHalt =>
              simp [Preparation.FullStepResultRel] at hResult
          | running sourceMid =>
              change
                Preparation.FullStateRel sourceProgram artifact
                  targetMid sourceMid at hResult
              have hPrefixBytes :=
                Preparation.simpleTrace?_sourceByteLength hPrefix
              have hTermPc :
                  sourceMid.pc =
                    EvmYul.UInt256.ofNat
                      (spec.entryPc +
                        Assembly.Program.byteLength
                          (Assembly.Instr.label block.label ::
                            bodyCode)) := by
                change
                  sourceMid.pc =
                    EvmYul.UInt256.ofNat
                      (spec.entryPc +
                        Preparation.SimpleTrace.sourceByteLength
                          spec.prefixTrace) at hEnd
                simpa [hPrefixBytes] using hEnd
              have hTermRel :=
                Preparation.OrdinaryTrace.targetOpenUntil_rel
                  (Preparation.ordinaryTrace?_sound hTermTrace)
                  hCompile byteSuffix hResult hTermPc
              simpa [Preparation.ordinaryTrace?_length hTermTrace]
                using hTermRel

theorem Preparation.OrdinaryTrace.targetOpenUntil_executes_bounded
    {continueTransfer : Assembly.Instr → Bool}
    {bytes : ByteArray}
    {blocks : List Assembly.Compact.PreparationBlock}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hExec :
      Simulation.Interaction.Executes
        (targetOpenUntil continueTransfer bytes blocks state)
        transcript outcome) :
    ∃ usedFuel,
      usedFuel ≤ targetFuel blocks ∧
        Simulation.Interaction.Executes
          (Assembly.Compact.InteractionSemantics.openRunNResult
            bytes usedFuel state)
          transcript outcome := by
  induction blocks generalizing state transcript outcome with
  | nil =>
      cases hExec
      refine ⟨0, by simp [targetFuel], ?_⟩
      change
        Simulation.Interaction.Executes
          (.done
            (.ok (Assembly.StepResult.running state)))
          []
          (.ok (Assembly.StepResult.running state))
      exact
        Simulation.Interaction.Executes.done
          (.ok (Assembly.StepResult.running state))
  | cons block rest ih =>
      change
        Simulation.Interaction.Executes
          (do
            let result ←
              Assembly.Compact.InteractionSemantics.openRunNResult
                bytes (Preparation.blockFuel block) state
            match
                block.sourceInstr.classifyFlowWith
                  continueTransfer state result with
            | .next mid =>
                targetOpenUntil continueTransfer bytes rest mid
            | .exit result =>
                pure result)
          transcript outcome at hExec
      rcases Simulation.Interaction.Executes.bind_cases hExec with
        hHeadError | hHeadOk
      · rcases hHeadError with
          ⟨error, hOutcome, hHead⟩
        subst outcome
        refine
          ⟨Preparation.blockFuel block, ?_, hHead⟩
        simp [targetFuel]
      · rcases hHeadOk with
          ⟨result, headTranscript, restTranscript,
            hTranscript, hHead, hRest⟩
        subst transcript
        cases hFlow :
            block.sourceInstr.classifyFlowWith
              continueTransfer state result with
        | exit final =>
            have hFinal :
                final = result := by
              have hResult :=
                Assembly.InteractionSemantics.Instr.classifyFlowWith_result
                  continueTransfer block.sourceInstr state result
              rw [hFlow] at hResult
              exact hResult
            subst final
            rw [hFlow] at hRest
            cases hRest
            refine
              ⟨Preparation.blockFuel block, ?_, ?_⟩
            · simp [targetFuel]
            · simpa using hHead
        | next mid =>
            have hResult :
                Assembly.StepResult.running mid = result := by
              have hResult :=
                Assembly.InteractionSemantics.Instr.classifyFlowWith_result
                  continueTransfer block.sourceInstr state result
              rw [hFlow] at hResult
              exact hResult
            rw [← hResult] at hHead
            rw [hFlow] at hRest
            obtain ⟨tailFuel, hTailBound, hTail⟩ :=
              ih hRest
            refine
              ⟨Preparation.blockFuel block + tailFuel,
                ?_, ?_⟩
            · simp only [targetFuel, List.map_cons,
                List.sum_cons]
              exact Nat.add_le_add_left hTailBound _
            · rw [
                Assembly.Compact.InteractionSemantics.openRunNResult_add]
              exact
                Simulation.Interaction.Executes.bind_ok
                  hHead hTail

namespace StandardReturn

theorem CaseSpec.fuelBudget_le_sum_of_mem
    {caseSpec : CaseSpec} {cases : List CaseSpec}
    (hMem : caseSpec ∈ cases) :
    caseSpec.fuelBudget ≤
      (cases.map CaseSpec.fuelBudget).sum := by
  induction cases with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      simp only [List.mem_cons] at hMem
      simp only [List.map_cons, List.sum_cons]
      rcases hMem with rfl | hTail
      · omega
      · exact Nat.le_trans (ih hTail) (by omega)

theorem CaseSpec.targetOpenRun_executes_bounded
    {artifact : Artifact} {spec : CaseSpec}
    {byteSuffix : List UInt8}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hExec :
      Simulation.Interaction.Executes
        (spec.targetOpenRun artifact state byteSuffix)
        transcript outcome) :
    ∃ usedFuel,
      usedFuel ≤ spec.fuelBudget ∧
        Simulation.Interaction.Executes
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            usedFuel state)
          transcript outcome := by
  unfold CaseSpec.targetOpenRun at hExec
  rcases Simulation.Interaction.Executes.bind_cases hExec with
    hTestError | hTestOk
  · rcases hTestError with
      ⟨error, hOutcome, hTest⟩
    subst outcome
    obtain ⟨testFuel, hTestBound, hTestRaw⟩ :=
      Preparation.OrdinaryTrace.targetOpenUntil_executes_bounded
        hTest
    exact
      ⟨testFuel,
        by
          unfold CaseSpec.fuelBudget
          omega,
        hTestRaw⟩
  · rcases hTestOk with
      ⟨testResult, testTranscript, restTranscript,
        hTranscript, hTest, hRest⟩
    subst transcript
    cases testResult with
    | halted halt =>
        cases hRest
        obtain ⟨testFuel, hTestBound, hTestRaw⟩ :=
          Preparation.OrdinaryTrace.targetOpenUntil_executes_bounded
            hTest
        exact
          ⟨testFuel,
            by
              unfold CaseSpec.fuelBudget
              omega,
            by simpa using hTestRaw⟩
    | running mid =>
        obtain ⟨testFuel, hTestBound, hTestRaw⟩ :=
          Preparation.OrdinaryTrace.targetOpenUntil_executes_bounded
            hTest
        obtain ⟨caseFuel, hCaseBound, hCaseRaw⟩ :=
          Preparation.OrdinaryTrace.targetOpenUntil_executes_bounded
            hRest
        refine
          ⟨testFuel + caseFuel, ?_, ?_⟩
        · unfold CaseSpec.fuelBudget
          omega
        · rw [
            Assembly.Compact.InteractionSemantics.openRunNResult_add]
          exact
            Simulation.Interaction.Executes.bind_ok
              hTestRaw hCaseRaw

theorem Spec.targetTermOpenRun_executes_bounded
    {artifact : Artifact} {spec : Spec}
    {byteSuffix : List UInt8}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hExec :
      Simulation.Interaction.Executes
        (spec.targetTermOpenRun artifact state byteSuffix)
        transcript outcome) :
    ∃ usedFuel,
      usedFuel ≤ spec.termFuelBudget ∧
        Simulation.Interaction.Executes
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            usedFuel state)
          transcript outcome := by
  unfold Spec.targetTermOpenRun at hExec
  cases hGet : state.stack[spec.depth]? with
  | none =>
      simp only [hGet] at hExec
      obtain ⟨usedFuel, hBound, hRaw⟩ :=
        Preparation.OrdinaryTrace.targetOpenUntil_executes_bounded
          hExec
      exact
        ⟨usedFuel,
          by
            unfold Spec.termFuelBudget
            omega,
          hRaw⟩
  | some token =>
      simp only [hGet] at hExec
      cases hFind : spec.findCase? token with
      | none =>
          simp only [hFind] at hExec
          obtain ⟨usedFuel, hBound, hRaw⟩ :=
            Preparation.OrdinaryTrace.targetOpenUntil_executes_bounded
              hExec
          exact
            ⟨usedFuel,
              by
                unfold Spec.termFuelBudget
                omega,
              hRaw⟩
      | some caseSpec =>
          simp only [hFind] at hExec
          obtain ⟨usedFuel, hBound, hRaw⟩ :=
            CaseSpec.targetOpenRun_executes_bounded hExec
          have hCaseBound :
              caseSpec.fuelBudget ≤
                (spec.cases.map CaseSpec.fuelBudget).sum :=
            CaseSpec.fuelBudget_le_sum_of_mem
              (Spec.findCase?_some_mem hFind)
          exact
            ⟨usedFuel,
              by
                unfold Spec.termFuelBudget
                omega,
              hRaw⟩

theorem Spec.targetOpenRun_executes_bounded
    {artifact : Artifact} {spec : Spec}
    {byteSuffix : List UInt8}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hExec :
      Simulation.Interaction.Executes
        (spec.targetOpenRun artifact state byteSuffix)
        transcript outcome) :
    ∃ usedFuel,
      usedFuel ≤ spec.fuelBudget ∧
        Simulation.Interaction.Executes
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            usedFuel state)
          transcript outcome := by
  unfold Spec.targetOpenRun at hExec
  rcases Simulation.Interaction.Executes.bind_cases hExec with
    hPrefixError | hPrefixOk
  · rcases hPrefixError with
      ⟨error, hOutcome, hPrefix⟩
    subst outcome
    exact
      ⟨Preparation.SimpleTrace.targetFuel spec.prefixTrace,
        by simp [Spec.fuelBudget],
        hPrefix⟩
  · rcases hPrefixOk with
      ⟨prefixResult, prefixTranscript, restTranscript,
        hTranscript, hPrefix, hRest⟩
    subst transcript
    cases prefixResult with
    | halted halt =>
        cases hRest
        exact
          ⟨Preparation.SimpleTrace.targetFuel spec.prefixTrace,
            by simp [Spec.fuelBudget],
            by simpa using hPrefix⟩
    | running mid =>
        obtain ⟨termFuel, hTermBound, hTerm⟩ :=
          Spec.targetTermOpenRun_executes_bounded hRest
        refine
          ⟨Preparation.SimpleTrace.targetFuel spec.prefixTrace +
              termFuel,
            ?_, ?_⟩
        · unfold Spec.fuelBudget
          omega
        · rw [
            Assembly.Compact.InteractionSemantics.openRunNResult_add]
          exact
            Simulation.Interaction.Executes.bind_ok
              hPrefix hTerm

end StandardReturn

def DirectSpec.fuelBudget (spec : DirectSpec) : Nat :=
  Preparation.SimpleTrace.targetFuel spec.prefixTrace +
    Preparation.OrdinaryTrace.targetFuel spec.termTrace

theorem DirectSpec.targetOpenRun_executes_bounded
    {artifact : Artifact} {spec : DirectSpec}
    {byteSuffix : List UInt8}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hExec :
      Simulation.Interaction.Executes
        (spec.targetOpenRun artifact state byteSuffix)
        transcript outcome) :
    ∃ usedFuel,
      usedFuel ≤ spec.fuelBudget ∧
        Simulation.Interaction.Executes
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.bytes.toList ++ byteSuffix))
            usedFuel state)
          transcript outcome := by
  unfold DirectSpec.targetOpenRun at hExec
  rcases Simulation.Interaction.Executes.bind_cases hExec with
    hPrefixError | hPrefixOk
  · rcases hPrefixError with
      ⟨error, hOutcome, hPrefix⟩
    subst outcome
    exact
      ⟨Preparation.SimpleTrace.targetFuel spec.prefixTrace,
        by simp [DirectSpec.fuelBudget],
        hPrefix⟩
  · rcases hPrefixOk with
      ⟨prefixResult, prefixTranscript, restTranscript,
        hTranscript, hPrefix, hRest⟩
    subst transcript
    cases prefixResult with
    | halted halt =>
        cases hRest
        exact
          ⟨Preparation.SimpleTrace.targetFuel spec.prefixTrace,
            by simp [DirectSpec.fuelBudget],
            by simpa using hPrefix⟩
    | running mid =>
        obtain ⟨termFuel, hTermBound, hTerm⟩ :=
          Preparation.OrdinaryTrace.targetOpenUntil_executes_bounded
            hRest
        refine
          ⟨Preparation.SimpleTrace.targetFuel spec.prefixTrace +
              termFuel,
            ?_, ?_⟩
        · unfold DirectSpec.fuelBudget
          omega
        · rw [
            Assembly.Compact.InteractionSemantics.openRunNResult_add]
          exact
            Simulation.Interaction.Executes.bind_ok
              hPrefix hTerm

def certifyProgramDirects?
    (sourceProgram : Assembly.Program) (artifact : Artifact) :
    List TypedCfg.Block → Option (List DirectSpec)
  | [] =>
      some []
  | block :: blocks => do
      let current ← certifyBlockDirect? sourceProgram artifact block
      let rest ← certifyProgramDirects? sourceProgram artifact blocks
      match current with
      | none => some rest
      | some spec => some (spec :: rest)

def DirectCoverage
    (sourceProgram : Assembly.Program) (artifact : Artifact)
    (blocks : List TypedCfg.Block)
    (specs : List DirectSpec) : Prop :=
  ∀ block ∈ blocks,
    TypedCfg.Preservation.Terminator.Direct block.term →
      ∃ spec, spec ∈ specs ∧
        spec.ValidForBlock sourceProgram artifact block

theorem certifyBlockDirect?_direct_ne_none
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {block : TypedCfg.Block} {current : Option DirectSpec}
    (hDirect :
      TypedCfg.Preservation.Terminator.Direct block.term)
    (hCertify :
      certifyBlockDirect? sourceProgram artifact block =
        some current) :
    current ≠ none := by
  cases hTerm : block.term with
  | returnDispatch returnCount sites =>
      simp [TypedCfg.Preservation.Terminator.Direct, hTerm]
        at hDirect
  | fallthrough next | jump next | jumpi next fallback
  | halt kind | invalid =>
      simp [certifyBlockDirect?, hTerm] at hCertify
      rcases hCertify with ⟨spec, hSpec, rfl⟩
      simp

theorem certifyProgramDirects?_coverage
    {sourceProgram : Assembly.Program} {artifact : Artifact}
    {blocks : List TypedCfg.Block} {specs : List DirectSpec}
    (hCertify :
      certifyProgramDirects? sourceProgram artifact blocks =
        some specs) :
    DirectCoverage sourceProgram artifact blocks specs := by
  induction blocks generalizing specs with
  | nil =>
      simp [DirectCoverage]
  | cons head tail ih =>
      cases hCurrent :
          certifyBlockDirect? sourceProgram artifact head with
      | none =>
          simp [certifyProgramDirects?, hCurrent] at hCertify
      | some current =>
          cases hRest :
              certifyProgramDirects? sourceProgram artifact tail with
          | none =>
              simp [certifyProgramDirects?, hCurrent, hRest]
                at hCertify
          | some rest =>
              cases current with
              | none =>
                  simp [certifyProgramDirects?, hCurrent, hRest]
                    at hCertify
                  subst specs
                  unfold DirectCoverage
                  intro block hMem hDirect
                  simp only [List.mem_cons] at hMem
                  rcases hMem with hHead | hTail
                  · subst block
                    exact
                      False.elim
                        ((certifyBlockDirect?_direct_ne_none
                            hDirect hCurrent) rfl)
                  · exact ih hRest block hTail hDirect
              | some spec =>
                  simp [certifyProgramDirects?, hCurrent, hRest]
                    at hCertify
                  subst specs
                  unfold DirectCoverage
                  intro block hMem hDirect
                  simp only [List.mem_cons] at hMem
                  rcases hMem with hHead | hTail
                  · subst block
                    exact
                      ⟨spec, by simp,
                        certifyBlockDirect?_some_valid hCurrent⟩
                  · obtain ⟨tailSpec, hTailMem, hTailValid⟩ :=
                      ih hRest block hTail hDirect
                    exact
                      ⟨tailSpec, by simp [hTailMem], hTailValid⟩

namespace WholeVerified

structure Artifact where
  base : Verified.Artifact
  standards : List StandardReturn.Spec
  directs : List DirectSpec

structure Artifact.ValidFor (artifact : Artifact)
    (cfg : TypedCfg.Program) : Prop where
  baseValid : artifact.base.ValidFor cfg
  standardCoverage :
    StandardReturn.Coverage artifact.base.base.assembly
      artifact.base.base.compact
      artifact.base.base.cfg.blocks artifact.standards
  directCoverage :
    DirectCoverage artifact.base.base.assembly
      artifact.base.base.compact
      artifact.base.base.cfg.blocks artifact.directs

def compileCfg? (cfg : TypedCfg.Program) : Option Artifact := do
  let base ← Verified.compileCfg? cfg
  let standards ←
    StandardReturn.certifyProgram?
      base.base.assembly base.base.compact base.base.cfg.blocks
  let directs ←
    certifyProgramDirects?
      base.base.assembly base.base.compact base.base.cfg.blocks
  some { base, standards, directs }

theorem compileCfg?_valid
    {cfg : TypedCfg.Program} {artifact : Artifact}
    (hCompile : compileCfg? cfg = some artifact) :
    artifact.ValidFor cfg := by
  unfold compileCfg? at hCompile
  obtain ⟨base, hBase, hAfterBase⟩ :=
    Option.bind_eq_some_iff.mp hCompile
  obtain ⟨standards, hStandards, hAfterStandards⟩ :=
    Option.bind_eq_some_iff.mp hAfterBase
  obtain ⟨directs, hDirects, hFinal⟩ :=
    Option.bind_eq_some_iff.mp hAfterStandards
  simp at hFinal
  subst artifact
  exact
    { baseValid := Verified.compileCfg?_valid hBase
      standardCoverage :=
        StandardReturn.certifyProgram?_coverage hStandards
      directCoverage :=
        certifyProgramDirects?_coverage hDirects }

def compileFunctions? (source : Functions.Program) : Option Artifact := do
  let stack ← Compiler.StackArtifact.compile? source
  compileCfg? stack.cfg

def dispatcherFuelBudget (spec : DispatcherSpec) : Nat :=
  Preparation.SimpleTrace.targetFuel spec.prefixTrace +
    (spec.layout.compactCode.length + 4)

def Artifact.fuelBudget (artifact : Artifact) : Nat :=
  (artifact.base.dispatchers.map dispatcherFuelBudget).sum +
    (artifact.standards.map StandardReturn.Spec.fuelBudget).sum +
    (artifact.directs.map DirectSpec.fuelBudget).sum

private theorem map_sum_ge_of_mem
    {α : Type} (cost : α → Nat) {item : α} :
    ∀ {items : List α}, item ∈ items →
      cost item ≤ (items.map cost).sum
  | [], hMem => by simp at hMem
  | head :: tail, hMem => by
      simp only [List.mem_cons] at hMem
      simp only [List.map_cons, List.sum_cons]
      rcases hMem with rfl | hTail
      · omega
      · exact Nat.le_trans (map_sum_ge_of_mem cost hTail) (by omega)

theorem Artifact.dispatcherFuel_le
    {artifact : Artifact} {spec : DispatcherSpec}
    (hMem : spec ∈ artifact.base.dispatchers) :
    dispatcherFuelBudget spec ≤ artifact.fuelBudget := by
  unfold Artifact.fuelBudget
  have hLeft :=
    map_sum_ge_of_mem dispatcherFuelBudget hMem
  omega

theorem Artifact.directFuel_le
    {artifact : Artifact} {spec : DirectSpec}
    (hMem : spec ∈ artifact.directs) :
    spec.fuelBudget ≤ artifact.fuelBudget := by
  unfold Artifact.fuelBudget
  have hRight :=
    map_sum_ge_of_mem DirectSpec.fuelBudget hMem
  omega

theorem Artifact.standardFuel_le
    {artifact : Artifact} {spec : StandardReturn.Spec}
    (hMem : spec ∈ artifact.standards) :
    spec.fuelBudget ≤ artifact.fuelBudget := by
  unfold Artifact.fuelBudget
  have hMiddle :=
    map_sum_ge_of_mem StandardReturn.Spec.fuelBudget hMem
  omega

/-!
One certified late-return block exposes an exact bounded prefix of the raw
compact byte stream.  The result relation remembers the late Assembly
boundary, which is the induction invariant used by the whole-program bridge.
-/
set_option maxHeartbeats 1000000 in
theorem Artifact.compiledBlock_executes_compact_bounded
    {artifact : Artifact} {cfg : TypedCfg.Program}
    {block : TypedCfg.Block} {entryPc : Nat}
    {target source : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Except Assembly.EVMException Assembly.StepResult}
    (hValid : artifact.ValidFor cfg)
    (byteSuffix : List UInt8 := [])
    (hFind :
      artifact.base.base.cfg.findBlock? block.label = some block)
    (hEntry :
      artifact.base.base.assembly.labelPc block.label =
        some entryPc)
    (hTargetSource :
      Preparation.FullStateRel artifact.base.base.assembly
        artifact.base.base.compact target source)
    (hSourcePc :
      source.pc = EvmYul.UInt256.ofNat entryPc)
    (hExec :
      Simulation.Interaction.Executes
        (LateReturnProbe.CompiledBlock.openRun
          block artifact.base.base.assembly source)
        transcript sourceDone) :
    ∃ usedFuel targetDone,
      usedFuel ≤ artifact.fuelBudget ∧
        Simulation.Interaction.Executes
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.base.base.compact.bytes.toList ++ byteSuffix))
            usedFuel target)
          transcript targetDone ∧
        Preparation.FullOutcomeRel artifact.base.base.assembly
          artifact.base.base.compact targetDone sourceDone := by
  have hLate :
      LateArtifactValidFor artifact.base.base cfg :=
    hValid.baseValid.baseValid
  have hBlock :
      block ∈ artifact.base.base.cfg.blocks :=
    List.mem_of_find?_eq_some hFind
  have hLabels :
      artifact.base.base.assembly.labels.Nodup :=
    Assembly.Program.labels_nodup_of_acceptedWithDynamic hLate.accepted
  cases hTerm : block.term with
  | returnDispatch returnCount sites =>
      obtain ⟨fragment⟩ :=
        LateReturnProbe.Program.lower?_fragment_of_findBlock?
          hLate.lowered hFind
      rcases
          LateReturnProbe.Block.lower?_starts_with_label
            fragment.lower with
        ⟨tail, hCode⟩
      have hEntryAt :
          artifact.base.base.assembly.labelPc block.label =
            some fragment.pre.byteLength := by
        have hNodup :
            (fragment.pre ++
              Assembly.Instr.label block.label ::
                (tail ++ fragment.post)).labels.Nodup := by
          simpa [fragment.target_eq, hCode, List.append_assoc] using
            hLabels
        have hAt :=
          Assembly.Program.labelPc_append_label_eq_of_labels_nodup
            fragment.pre (tail ++ fragment.post) hNodup
        simpa [fragment.target_eq, hCode, List.append_assoc] using hAt
      have hStart :
          source.pc = fragment.pre.pcAfter := by
        have hPcEq : entryPc = fragment.pre.byteLength := by
          rw [hEntryAt] at hEntry
          exact (Option.some.inj hEntry).symm
        calc
          source.pc = EvmYul.UInt256.ofNat entryPc := hSourcePc
          _ = EvmYul.UInt256.ofNat fragment.pre.byteLength := by
            rw [hPcEq]
          _ = fragment.pre.pcAfter := rfl
      by_cases hSmall :
          sites.length ≤
            LateReturnProbe.Terminator.standardReturnSiteLimit
      · obtain ⟨spec, hSpecMem, hSpecValid⟩ :=
          hValid.standardCoverage
            block hBlock returnCount sites hTerm hSmall
        have hSpecValidCopy := hSpecValid
        rcases hSpecValidCopy with
          ⟨bodyCode, output, termCode, hSpecTerm, hSpecSmall,
            hBound, hBody, hOutput, hDepth, hTermLower,
            hTermCode, hSpecEntry, hSpecLabel, hSpecTermPc,
            hPrefix, hCases, hCaseValid, hReject⟩
        have hUnique :
            ReturnAddressRelation.TokensUnique spec.sites := by
          have hLocal :=
            LateReturnPreservation.Program.returnTokensUnique_of_check
              hLate.localReturnTokensUnique hBlock
          rw [hSpecTerm] at hLocal
          exact hLocal
        have hTargets :
            ∀ site ∈ spec.sites,
              ∃ dest,
                artifact.base.base.assembly.labelPc site.target =
                  some dest := by
          intro site hSite
          obtain ⟨dest, hDest, hNonzero⟩ :=
            LateReturnPreservation.Program.returnTargetsResolveNonzero_of_check
              hLate.returnTargetsResolveNonzero site
              (by
                apply ReturnAddressLower.term_site_mem_returnSites hBlock
                simpa [ReturnAddressLower.Terminator.sites,
                  hSpecTerm] using hSite)
          exact ⟨dest, hDest⟩
        have hRel :=
          StandardReturn.certifiedStandardReturnBlock_compiled_openRun_rel
            hLate.compactCompile byteSuffix hSpecValid fragment.lower
            fragment.target_eq hTargetSource hEntry hSourcePc hStart
            hUnique hLabels hTargets
        obtain ⟨targetDone, hTargetExec, hDone⟩ :=
          Simulation.Interaction.Rel.executes
            (Simulation.Interaction.Rel.symm hRel) hExec
        obtain ⟨usedFuel, hUsed, hRawExec⟩ :=
          StandardReturn.Spec.targetOpenRun_executes_bounded
            hTargetExec
        exact
          ⟨usedFuel, targetDone,
            Nat.le_trans hUsed
              (artifact.standardFuel_le hSpecMem),
            hRawExec, hDone⟩
      · obtain ⟨spec, hSpecMem, hSpecValid⟩ :=
          hValid.baseValid.dispatcherCoverage
            block hBlock returnCount sites hTerm hSmall
        have hSpecValidCopy := hSpecValid
        rcases hSpecValidCopy with
          ⟨specReturnCount, depth, specEntryPc, bodyCode, output,
            hSpecTerm, hBody, hOutput, hDepth, hCount, hBound,
            hSpecEntry, hSpecLabel, hSpecSourcePc,
            hPrefix, hDispatcher⟩
        have hEntryEq : specEntryPc = entryPc := by
          rw [hEntry] at hSpecEntry
          exact (Option.some.inj hSpecEntry).symm
        subst specEntryPc
        have hTermEq :
            TypedCfg.Terminator.returnDispatch returnCount sites =
              TypedCfg.Terminator.returnDispatch specReturnCount
                (spec.first :: spec.rest) :=
          hTerm.symm.trans hSpecTerm
        have hSitesEq :
            sites = spec.first :: spec.rest := by
          injection hTermEq
        have hLargeSpec :
            ¬ (spec.first :: spec.rest).length ≤
              LateReturnProbe.Terminator.standardReturnSiteLimit := by
          simpa [hSitesEq] using hSmall
        have hUnique :
            ReturnAddressRelation.TokensUnique
              (spec.first :: spec.rest) := by
          have hLocal :=
            LateReturnPreservation.Program.returnTokensUnique_of_check
              hLate.localReturnTokensUnique hBlock
          rw [hSpecTerm] at hLocal
          exact hLocal
        have hTargets :
            ∀ site ∈ spec.first :: spec.rest,
              ∃ dest,
                artifact.base.base.assembly.labelPc site.target =
                    some dest ∧
                  EvmYul.UInt256.ofNat dest ≠
                    EvmYul.UInt256.ofNat 0 := by
          intro site hSite
          apply
            LateReturnPreservation.Program.returnTargetsResolveNonzero_of_check
              hLate.returnTargetsResolveNonzero site
          apply ReturnAddressLower.term_site_mem_returnSites hBlock
          simpa [ReturnAddressLower.Terminator.sites, hSpecTerm] using
            hSite
        have hRel :=
          certifiedReturnBlock_compiled_openRun_rel
            hLate.compactCompile byteSuffix hSpecValid fragment.lower
            fragment.target_eq hTargetSource hEntry hSourcePc hStart
            hLargeSpec hUnique hLabels hTargets
        obtain ⟨targetDone, hTargetExec, hDone⟩ :=
          Simulation.Interaction.Rel.executes
            (Simulation.Interaction.Rel.symm hRel) hExec
        refine
          ⟨dispatcherFuelBudget spec, targetDone,
            artifact.dispatcherFuel_le hSpecMem, ?_, hDone⟩
        simpa [dispatcherFuelBudget] using hTargetExec
  | fallthrough next
  | jump next
  | jumpi next fallback
  | halt kind
  | invalid =>
      have hDirect :
          TypedCfg.Preservation.Terminator.Direct block.term := by
        simp [TypedCfg.Preservation.Terminator.Direct, hTerm]
      obtain ⟨spec, hSpecMem, hSpecValid⟩ :=
        hValid.directCoverage block hBlock hDirect
      have hSpecValidCopy := hSpecValid
      rcases hSpecValidCopy with
        ⟨bodyCode, output, termCode, _hDirect, hBody,
          hOutput, hTermCode, hSpecEntry, hSpecLabel,
          hPrefix, hTermTrace⟩
      have hSpecPc : spec.entryPc = entryPc := by
        rw [hEntry] at hSpecEntry
        exact (Option.some.inj hSpecEntry).symm
      have hSourceSpecPc :
          source.pc = EvmYul.UInt256.ofNat spec.entryPc := by
        simpa [hSpecPc] using hSourcePc
      have hRel :=
        certifiedDirectBlock_compiled_openRun_rel
          hLate.compactCompile hSpecValid hTargetSource hSourceSpecPc
          byteSuffix
      obtain ⟨targetDone, hTargetExec, hDone⟩ :=
        Simulation.Interaction.Rel.executes
          (Simulation.Interaction.Rel.symm hRel) hExec
      obtain ⟨usedFuel, hUsed, hRawExec⟩ :=
        DirectSpec.targetOpenRun_executes_bounded hTargetExec
      exact
        ⟨usedFuel, targetDone,
          Nat.le_trans hUsed (artifact.directFuel_le hSpecMem),
          hRawExec, hDone⟩

private theorem findBlock?_exists_of_wellTyped_target
    {program : TypedCfg.Program} {block : TypedCfg.Block}
    {next : Label}
    (hTyped : block.WellTyped program)
    (hTarget : next ∈ block.term.targets) :
    ∃ nextBlock, program.findBlock? next = some nextBlock := by
  have hTermTyped := hTyped.2
  cases hTerm : block.term with
  | fallthrough target =>
      have hNext : next = target := by
        simpa [TypedCfg.Terminator.targets, hTerm] using hTarget
      subst next
      cases hFind : program.findBlock? target with
      | none =>
          simp [TypedCfg.Terminator.type?,
            TypedCfg.Program.labelShape?, hFind, hTerm] at hTermTyped
      | some targetBlock =>
          exact ⟨targetBlock, rfl⟩
  | jump target =>
      have hNext : next = target := by
        simpa [TypedCfg.Terminator.targets, hTerm] using hTarget
      subst next
      cases hFind : program.findBlock? target with
      | none =>
          simp [TypedCfg.Terminator.type?,
            TypedCfg.Program.labelShape?, hFind, hTerm] at hTermTyped
      | some targetBlock =>
          exact ⟨targetBlock, rfl⟩
  | jumpi target fallback =>
      have hNext : next = target ∨ next = fallback := by
        simpa [TypedCfg.Terminator.targets, hTerm] using hTarget
      cases hTargetFind : program.findBlock? target with
      | none =>
          simp [TypedCfg.Terminator.type?,
            TypedCfg.Program.labelShape?, hTargetFind, hTerm] at hTermTyped
      | some targetBlock =>
          cases hFallbackFind : program.findBlock? fallback with
          | none =>
              simp [TypedCfg.Terminator.type?,
                TypedCfg.Program.labelShape?, hTargetFind,
                hFallbackFind, hTerm] at hTermTyped
          | some fallbackBlock =>
              rcases hNext with hNext | hNext
              · exact ⟨targetBlock, by simpa [hNext] using hTargetFind⟩
              · exact
                  ⟨fallbackBlock, by
                    simpa [hNext] using hFallbackFind⟩
  | returnDispatch returnCount sites =>
      have hTargetSites :
          next ∈ sites.map ReturnSite.target := by
        simpa [TypedCfg.Terminator.targets, hTerm] using hTarget
      rcases List.mem_map.mp hTargetSites with
        ⟨site, hSiteMem, hSiteTarget⟩
      subst next
      cases hDepth : block.output.returnTokenDepth? with
      | none =>
          simp [TypedCfg.Terminator.type?, hDepth, hTerm] at hTermTyped
      | some depth =>
          by_cases hCount : depth = returnCount
          · subst depth
            have hShapes :
                TypedCfg.Terminator.targetsHaveShape?
                    program (block.output.erase returnCount) sites =
                  true := by
              have hChecked :
                  sites ≠ [] ∧
                    TypedCfg.Terminator.targetsHaveShape?
                        program (block.output.erase returnCount) sites =
                      true := by
                simpa [TypedCfg.Terminator.type?, hDepth, hTerm] using
                  hTermTyped
              exact hChecked.2
            exact
              TypedCfg.Block.findBlock?_exists_of_targetsHaveShape?_eq_true
                hShapes hSiteMem
          · simp [TypedCfg.Terminator.type?,
              hDepth, hCount, hTerm] at hTermTyped
  | halt kind =>
      simp [TypedCfg.Terminator.targets, hTerm] at hTarget
  | invalid =>
      simp [TypedCfg.Terminator.targets, hTerm] at hTarget

/-!
The public source-side relation for the whole-program bridge factors through
the late Assembly outcome.  Keeping that witness explicit makes the two proof
obligations independent: the TypedCfg lowering establishes `RunSimulates`,
while the executable compact certificate establishes `FullOutcomeRel`.
-/
def CompactRunSimulates
    (artifact : Artifact)
    (sourceDone : Except Assembly.EVMException TypedCfg.Outcome)
    (targetDone : Except Assembly.EVMException Assembly.StepResult) : Prop :=
  ∃ lateDone,
    TypedCfg.InteractionPreservation.OpenBlock.RunSimulates
        artifact.base.base.assembly sourceDone lateDone ∧
      Preparation.FullOutcomeRel artifact.base.base.assembly
        artifact.base.base.compact targetDone lateDone

private theorem CompactRunSimulates.jump
    {artifact : Artifact} {next : Label} {source : EVMState}
    {targetDone : Except Assembly.EVMException Assembly.StepResult}
    (hRel :
      CompactRunSimulates artifact
        (.ok (.jump next source)) targetDone) :
    ∃ target late dest,
      targetDone = .ok (.running target) ∧
        artifact.base.base.assembly.labelPc next = some dest ∧
        late.pc = EvmYul.UInt256.ofNat dest ∧
        Assembly.SameRuntimeData late source ∧
        Preparation.FullStateRel artifact.base.base.assembly
          artifact.base.base.compact target late := by
  rcases hRel with ⟨lateDone, hSourceLate, hTargetLate⟩
  unfold
    TypedCfg.InteractionPreservation.OpenBlock.RunSimulates
    TypedCfg.InteractionPreservation.OpenOutcome.Simulates
    TypedCfg.Preservation.Outcome.Simulates
    TypedCfg.Preservation.Outcome.RunningAt at hSourceLate
  rcases hSourceLate with ⟨dest, hDest, hRunning⟩
  cases lateDone with
  | error lateError =>
      exact hRunning.elim
  | ok lateResult =>
      cases lateResult with
      | halted lateHalt =>
          exact hRunning.elim
      | running late =>
          rcases hRunning with ⟨hLatePc, hRuntime⟩
          cases targetDone with
          | error targetError =>
              cases hTargetLate
          | ok targetResult =>
              cases targetResult with
              | halted targetHalt =>
                  cases hTargetLate with
                  | ok hStep =>
                      exact hStep.elim
              | running target =>
                  cases hTargetLate with
                  | ok hFull =>
                      exact
                        ⟨target, late, dest, rfl, hDest,
                          hLatePc, hRuntime, hFull⟩

/-!
One well-typed TypedCfg step is reproduced by an exact bounded execution of
the compact bytecode.  This is the induction step used below: its hypotheses
are precisely the label, runtime-data, and compact-boundary invariants exposed
by the two adjacent preservation theorems.
-/
set_option maxHeartbeats 1000000 in
theorem Artifact.openStep_executes_compact_bounded
    {artifact : Artifact} {cfg : TypedCfg.Program}
    {label : Label} {block : TypedCfg.Block} {entryPc : Nat}
    {target late source : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Except Assembly.EVMException TypedCfg.Outcome}
    (hValid : artifact.ValidFor cfg)
    (byteSuffix : List UInt8 := [])
    (hTyped : artifact.base.base.cfg.WellTyped)
    (hIndependent :
      artifact.base.base.cfg.ProgramCounterIndependent)
    (hFind :
      artifact.base.base.cfg.findBlock? label = some block)
    (hEntry :
      artifact.base.base.assembly.labelPc label = some entryPc)
    (hLatePc :
      late.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData source late.incrPC)
    (hTargetLate :
      Preparation.FullStateRel artifact.base.base.assembly
        artifact.base.base.compact target late)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openStep
          artifact.base.base.cfg label source)
        transcript sourceDone) :
    ∃ usedFuel targetDone,
      usedFuel ≤ artifact.fuelBudget ∧
        Simulation.Interaction.Executes
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.base.base.compact.bytes.toList ++ byteSuffix))
            usedFuel target)
          transcript targetDone ∧
        CompactRunSimulates artifact sourceDone targetDone := by
  have hLate :
      LateArtifactValidFor artifact.base.base cfg :=
    hValid.baseValid.baseValid
  have hFits : artifact.base.base.assembly.PCFits :=
    (ReturnAddressProbe.Compact.compile?_valid
      hLate.compactCompile).sourcePCFits
  have hStepRel :=
    LateReturnPreservation.Program.lower?_step_openRunSimulates_rel_of_related
      hLate.lowered hLate.accepted hFits hTyped hIndependent
      hLate.localReturnTokensUnique hLate.returnTargetsResolveNonzero
      hFind hEntry hLatePc hRuntime
  obtain ⟨lateDone, hLateExec, hSourceLate⟩ :=
    Simulation.Interaction.Rel.executes hStepRel hExec
  have hBlockLabel : block.label = label := by
    have hFound :
        (block.label == label) = true :=
      @List.find?_some TypedCfg.Block
        (fun candidate : TypedCfg.Block =>
          candidate.label == label)
        block artifact.base.base.cfg.blocks hFind
    exact beq_iff_eq.mp hFound
  subst label
  obtain ⟨usedFuel, targetDone, hUsed, hTargetExec, hTargetLateDone⟩ :=
    artifact.compiledBlock_executes_compact_bounded
      hValid byteSuffix hFind hEntry hTargetLate hLatePc hLateExec
  exact
    ⟨usedFuel, targetDone, hUsed, hTargetExec,
      ⟨lateDone, hSourceLate, hTargetLateDone⟩⟩

/-!
Fuel-indexed whole-program execution of the optimized TypedCfg is reproduced
by a bounded prefix of the certified compact bytecode.  The target budget is
path-independent: every source block consumes at most `artifact.fuelBudget`,
so a source run of `fuel` blocks consumes at most their product.
-/
set_option maxHeartbeats 2000000 in
theorem Artifact.openRunN_executes_compact_bounded
    {artifact : Artifact} {cfg : TypedCfg.Program}
    (hValid : artifact.ValidFor cfg)
    (byteSuffix : List UInt8 := [])
    (hTyped : artifact.base.base.cfg.WellTyped)
    (hIndependent :
      artifact.base.base.cfg.ProgramCounterIndependent)
    (fuel : Nat)
    {label : Label} {block : TypedCfg.Block} {entryPc : Nat}
    {target late source : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {sourceDone : Except Assembly.EVMException TypedCfg.Outcome}
    (hFind :
      artifact.base.base.cfg.findBlock? label = some block)
    (hEntry :
      artifact.base.base.assembly.labelPc label = some entryPc)
    (hLatePc :
      late.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData source late.incrPC)
    (hTargetLate :
      Preparation.FullStateRel artifact.base.base.assembly
        artifact.base.base.compact target late)
    (hExec :
      Simulation.Interaction.Executes
        (TypedCfg.InteractionSemantics.Program.openRunN
          artifact.base.base.cfg fuel label source)
        transcript sourceDone) :
    ∃ usedFuel targetDone,
      usedFuel ≤ fuel * artifact.fuelBudget ∧
        Simulation.Interaction.Executes
          (Assembly.Compact.InteractionSemantics.openRunNResult
            (Assembly.Bytecode.ofList
              (artifact.base.base.compact.bytes.toList ++ byteSuffix))
            usedFuel target)
          transcript targetDone ∧
        CompactRunSimulates artifact sourceDone targetDone := by
  induction fuel generalizing
      label block entryPc target late source transcript sourceDone with
  | zero =>
      rw [TypedCfg.InteractionSemantics.Program.openRunN_zero] at hExec
      cases hExec
      have hLateSource :
          Assembly.SameRuntimeData late source :=
        Assembly.SameRuntimeData.trans
          (Assembly.SameRuntimeData.incrPC_right
            (Assembly.SameRuntimeData.refl late))
          hRuntime.symm
      refine
        ⟨0, .ok (Assembly.StepResult.running target), by simp,
          ?_, ?_⟩
      · simpa using
          (Simulation.Interaction.Executes.done
            (.ok (Assembly.StepResult.running target) :
              Except Assembly.EVMException Assembly.StepResult))
      exact
        ⟨.ok (Assembly.StepResult.running late),
          ⟨entryPc, hEntry, hLatePc, hLateSource⟩,
          .ok hTargetLate⟩
  | succ fuel ih =>
      rw [TypedCfg.InteractionSemantics.Program.openRunN_succ] at hExec
      rcases Simulation.Interaction.Executes.bind_cases hExec with
        hStepError | hStepOk
      · rcases hStepError with
          ⟨error, hOutcome, hSourceStep⟩
        subst sourceDone
        obtain
            ⟨headFuel, targetDone, hHeadFuel,
              hTargetHead, hHeadRel⟩ :=
          artifact.openStep_executes_compact_bounded
            hValid byteSuffix hTyped hIndependent hFind hEntry hLatePc
            hRuntime hTargetLate hSourceStep
        refine
          ⟨headFuel, targetDone, ?_, hTargetHead, hHeadRel⟩
        rw [Nat.add_mul]
        omega
      · rcases hStepOk with
          ⟨sourceOutcome, headTranscript, restTranscript,
            hTranscript, hSourceStep, hSourceRest⟩
        subst transcript
        obtain
            ⟨headFuel, targetDone, hHeadFuel,
              hTargetHead, hHeadRel⟩ :=
          artifact.openStep_executes_compact_bounded
            hValid byteSuffix hTyped hIndependent hFind hEntry hLatePc
            hRuntime hTargetLate hSourceStep
        cases sourceOutcome with
        | fallthrough sourceFinal
        | returnDispatch sourceFinal
        | halt kind sourceFinal
        | invalid sourceFinal =>
            cases hSourceRest
            refine
              ⟨headFuel, targetDone, ?_, ?_, hHeadRel⟩
            · rw [Nat.add_mul]
              omega
            · simpa using hTargetHead
        | jump next sourceAfter =>
            obtain
                ⟨targetAfter, lateAfter, nextPc,
                  hTargetDone, hNextEntry, hLateAfterPc,
                  hLateRuntime, hTargetLateAfter⟩ :=
              CompactRunSimulates.jump hHeadRel
            subst targetDone
            have hBlockExec :
                Simulation.Interaction.Executes
                  (TypedCfg.InteractionSemantics.Block.openRun
                    block source)
                  headTranscript
                  (.ok (.jump next sourceAfter)) := by
              simpa [
                TypedCfg.InteractionSemantics.Program.openStep,
                TypedCfg.Control.Program.step, hFind] using
                  hSourceStep
            have hJumpTarget :
                next ∈ block.term.targets :=
              Simulation.Interaction.AllDone.property_of_executes
                (ReturnAddressPreservation.block_openRun_jumpTarget
                  block source)
                hBlockExec
            have hBlockMem :
                block ∈ artifact.base.base.cfg.blocks :=
              List.mem_of_find?_eq_some hFind
            have hBlockTyped : block.WellTyped artifact.base.base.cfg :=
              (List.forall_iff_forall_mem.mp hTyped.2.1)
                block hBlockMem
            obtain ⟨nextBlock, hNextFind⟩ :=
              findBlock?_exists_of_wellTyped_target
                hBlockTyped hJumpTarget
            have hNextRuntime :
                Assembly.SameRuntimeData
                  sourceAfter lateAfter.incrPC :=
              Assembly.SameRuntimeData.incrPC_right hLateRuntime.symm
            obtain
                ⟨tailFuel, finalTarget, hTailFuel,
                  hTargetTail, hTailRel⟩ :=
              ih
                (label := next) (block := nextBlock)
                (entryPc := nextPc)
                (target := targetAfter) (late := lateAfter)
                (source := sourceAfter)
                hNextFind hNextEntry hLateAfterPc
                hNextRuntime hTargetLateAfter hSourceRest
            refine
              ⟨headFuel + tailFuel, finalTarget, ?_, ?_, hTailRel⟩
            · rw [Nat.add_mul]
              omega
            · rw [
                Assembly.Compact.InteractionSemantics.openRunNResult_add]
              exact
                Simulation.Interaction.Executes.bind_ok
                  hTargetHead hTargetTail

private theorem CompactRunSimulates.targetFinished
    {artifact : Artifact}
    {sourceDone : Except Assembly.EVMException TypedCfg.Outcome}
    {targetDone : Except Assembly.EVMException Assembly.StepResult}
    (hStopped :
      TypedCfg.InteractionSemantics.Program.Stopped sourceDone)
    (hRel : CompactRunSimulates artifact sourceDone targetDone) :
    Assembly.InteractionSemantics.Finished targetDone := by
  rcases hRel with ⟨lateDone, hSourceLate, hTargetLate⟩
  have hLateFinished :
      Assembly.InteractionSemantics.Finished lateDone := by
    cases sourceDone with
    | error sourceError =>
        unfold
          TypedCfg.InteractionPreservation.OpenBlock.RunSimulates
            at hSourceLate
        subst lateDone
        trivial
    | ok sourceOutcome =>
        cases sourceOutcome with
        | fallthrough source
        | jump next source
        | returnDispatch source
        | invalid source =>
            exact hStopped.elim
        | halt kind source =>
            unfold
              TypedCfg.InteractionPreservation.OpenBlock.RunSimulates
              TypedCfg.InteractionPreservation.OpenOutcome.Simulates
                at hSourceLate
            rcases hSourceLate with
              ⟨simulated, _hRuntime, hTarget⟩
            unfold Assembly.Target.stepInstrResult at hTarget
            cases hRun :
                Assembly.Target.stepInstr
                  (.prim kind.toPrimOp) simulated with
            | error error =>
                rw [hRun] at hTarget
                subst lateDone
                trivial
            | ok final =>
                rw [hRun] at hTarget
                have hKind :
                    (Assembly.TargetInstr.prim
                      kind.toPrimOp).haltKind? = some kind := by
                  cases kind <;> rfl
                rw [hKind] at hTarget
                subst lateDone
                trivial
  cases lateDone with
  | error lateError =>
      cases targetDone with
      | error targetError =>
          trivial
      | ok targetResult =>
          cases hTargetLate
  | ok lateResult =>
      cases lateResult with
      | running late =>
          exact hLateFinished.elim
      | halted lateHalt =>
          cases targetDone with
          | error targetError =>
              cases hTargetLate
          | ok targetResult =>
              cases targetResult with
              | running target =>
                  cases hTargetLate with
                  | ok hStep =>
                      exact hStep.elim
              | halted targetHalt =>
                  trivial

private theorem compact_openRunNResult_follows_of_le_executes
    {bytes : ByteArray} {usedFuel totalFuel : Nat}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hFuel : usedFuel ≤ totalFuel)
    (hExec :
      Simulation.Interaction.Executes
        (Assembly.Compact.InteractionSemantics.openRunNResult
          bytes usedFuel state)
        transcript outcome) :
    Simulation.Interaction.Follows
      (Assembly.Compact.InteractionSemantics.openRunNResult
        bytes totalFuel state)
      transcript := by
  have hEq :
      usedFuel + (totalFuel - usedFuel) = totalFuel :=
    Nat.add_sub_of_le hFuel
  rw [← hEq]
  rw [Assembly.Compact.InteractionSemantics.openRunNResult_add]
  exact Simulation.Interaction.Follows.bind hExec.follows

private theorem compact_openRunNResult_finished_pad
    {bytes : ByteArray} {usedFuel totalFuel : Nat}
    {state : EVMState}
    {transcript : Simulation.Interaction.Transcript}
    {outcome : Except Assembly.EVMException Assembly.StepResult}
    (hFuel : usedFuel ≤ totalFuel)
    (hExec :
      Simulation.Interaction.Executes
        (Assembly.Compact.InteractionSemantics.openRunNResult
          bytes usedFuel state)
        transcript outcome)
    (hFinished : Assembly.InteractionSemantics.Finished outcome) :
    Simulation.Interaction.Executes
      (Assembly.Compact.InteractionSemantics.openRunNResult
        bytes totalFuel state)
      transcript outcome := by
  have hEq :
      usedFuel + (totalFuel - usedFuel) = totalFuel :=
    Nat.add_sub_of_le hFuel
  rw [← hEq]
  cases outcome with
  | error error =>
      exact
        Assembly.Compact.InteractionSemantics.openRunNResult_error_add_executes
          hExec
  | ok result =>
      cases result with
      | running final =>
          exact hFinished.elim
      | halted halt =>
          exact
            Assembly.Compact.InteractionSemantics.openRunNResult_halted_add_executes
              hExec

/-!
Canonical finite-prefix preservation for the optimized late-return CFG.
Residual CFG control is exactly the source truncation arm; completed errors and
halts are padded to the fixed path-independent compact budget.
-/
set_option maxHeartbeats 2000000 in
theorem Artifact.openRunNPrefix_compact_forward
    {artifact : Artifact} {cfg : TypedCfg.Program}
    (hValid : artifact.ValidFor cfg)
    (byteSuffix : List UInt8 := [])
    (hTyped : artifact.base.base.cfg.WellTyped)
    (hIndependent :
      artifact.base.base.cfg.ProgramCounterIndependent)
    (fuel : Nat)
    {label : Label} {block : TypedCfg.Block} {entryPc : Nat}
    {target late source : EVMState}
    (hFind :
      artifact.base.base.cfg.findBlock? label = some block)
    (hEntry :
      artifact.base.base.assembly.labelPc label = some entryPc)
    (hLatePc :
      late.pc = EvmYul.UInt256.ofNat entryPc)
    (hRuntime :
      Assembly.SameRuntimeData source late.incrPC)
    (hTargetLate :
      Preparation.FullStateRel artifact.base.base.assembly
        artifact.base.base.compact target late) :
    Simulation.Interaction.ForwardRel
      TypedCfg.InteractionSemantics.Program.PrefixTruncated
      (CompactRunSimulates artifact)
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix
        artifact.base.base.cfg fuel label source)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.base.base.compact.bytes.toList ++ byteSuffix))
        (fuel * artifact.fuelBudget) target) := by
  apply Simulation.Interaction.ForwardRel.of_executes_or_follows
  intro transcript sourceDone hSourceExec
  unfold TypedCfg.InteractionSemantics.Program.openRunNPrefix at hSourceExec
  rcases Simulation.Interaction.Executes.bind_cases hSourceExec with
    hRunError | hRunOk
  · rcases hRunError with ⟨error, hOutcome, hRunExec⟩
    subst sourceDone
    obtain
        ⟨usedFuel, targetDone, hUsed, hTargetExec, hRelated⟩ :=
      artifact.openRunN_executes_compact_bounded
        hValid byteSuffix hTyped hIndependent fuel hFind hEntry hLatePc
        hRuntime hTargetLate hRunExec
    have hFinished :
        Assembly.InteractionSemantics.Finished targetDone :=
      CompactRunSimulates.targetFinished (by trivial) hRelated
    have hTargetPadded :=
      compact_openRunNResult_finished_pad hUsed hTargetExec hFinished
    exact .inr ⟨targetDone, hTargetPadded, hRelated⟩
  · rcases hRunOk with
      ⟨sourceOutcome, headTranscript, restTranscript,
        hTranscript, hRunExec, hFinishExec⟩
    subst transcript
    obtain
        ⟨usedFuel, targetDone, hUsed, hTargetExec, hRelated⟩ :=
      artifact.openRunN_executes_compact_bounded
        hValid byteSuffix hTyped hIndependent fuel hFind hEntry hLatePc
        hRuntime hTargetLate hRunExec
    cases sourceOutcome with
    | halt kind final =>
        cases hFinishExec
        have hFinished :
            Assembly.InteractionSemantics.Finished targetDone :=
          CompactRunSimulates.targetFinished (by trivial) hRelated
        have hTargetPadded :=
          compact_openRunNResult_finished_pad hUsed hTargetExec hFinished
        exact
          .inr
            ⟨targetDone, by simpa using hTargetPadded, hRelated⟩
    | fallthrough final
    | jump next final
    | returnDispatch final
    | invalid final =>
        cases hFinishExec
        have hFollow :=
          compact_openRunNResult_follows_of_le_executes
            hUsed hTargetExec
        exact
          .inl
            ⟨.OutOfFuel, rfl, by trivial, by simpa using hFollow⟩

/-!
Entry-point specialization used by the frontend splice.  The TypedCfg state
may carry any irrelevant program counter; the late Assembly and raw states
start at physical pc zero with identical runtime data.
-/
theorem Artifact.entry_openRunNPrefix_compact_forward
    {artifact : Artifact} {cfg : TypedCfg.Program}
    (hValid : artifact.ValidFor cfg)
    (hIndependent : cfg.ProgramCounterIndependent)
    (fuel : Nat) (source : EVMState)
    (byteSuffix : List UInt8 := []) :
    Simulation.Interaction.ForwardRel
      TypedCfg.InteractionSemantics.Program.PrefixTruncated
      (CompactRunSimulates artifact)
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix
        artifact.base.base.cfg fuel artifact.base.base.cfg.entry source)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.base.base.compact.bytes.toList ++ byteSuffix))
        (fuel * artifact.fuelBudget)
        { source with pc := EvmYul.UInt256.ofNat 0 }) := by
  have hLate :
      LateArtifactValidFor artifact.base.base cfg :=
    hValid.baseValid.baseValid
  have hTyped : artifact.base.base.cfg.WellTyped :=
    ReturnAddressProbe.optimizedCfg?_wellTyped hLate.optimized
  have hOptimizedIndependent :
      artifact.base.base.cfg.ProgramCounterIndependent :=
    ReturnAddressProbe.optimizedCfg?_programCounterIndependent
      hIndependent hLate.optimized
  cases hFind :
      artifact.base.base.cfg.findBlock?
        artifact.base.base.cfg.entry with
  | none =>
      exact False.elim (hTyped.2.2.1 hFind)
  | some block =>
      have hEntry :
          artifact.base.base.assembly.labelPc
              artifact.base.base.cfg.entry =
            some 0 :=
        LateReturnProbe.Program.lower?_entry_labelPc_zero hLate.lowered
      let initial : EVMState :=
        { source with pc := EvmYul.UInt256.ofNat 0 }
      have hInitialPc :
          initial.pc = EvmYul.UInt256.ofNat 0 := rfl
      have hRuntime :
          Assembly.SameRuntimeData source initial.incrPC := by
        apply Assembly.SameRuntimeData.incrPC_right
        apply Assembly.SameRuntimeData.with_pc_right
        exact Assembly.SameRuntimeData.refl source
      have hFull :
          Preparation.FullStateRel artifact.base.base.assembly
            artifact.base.base.compact initial initial :=
        Preparation.FullStateRel.initial
          hLate.compactCompile hInitialPc hInitialPc
          (Assembly.SameRuntimeData.refl initial)
      simpa [initial] using
        artifact.openRunNPrefix_compact_forward
          hValid byteSuffix hTyped hOptimizedIndependent fuel
          (label := artifact.base.base.cfg.entry)
          (block := block) (entryPc := 0)
          (target := initial) (late := initial) (source := source)
          hFind hEntry hInitialPc hRuntime hFull

def GeneratedCompactRunSimulates
    (artifact : Artifact)
    (sourceDone : Except Assembly.EVMException TypedCfg.Outcome)
    (targetDone : Except Assembly.EVMException Assembly.StepResult) : Prop :=
  ∃ optimizedDone,
    InteractionCongruence.Block.RuntimeOutcomeRel
        sourceDone optimizedDone ∧
      CompactRunSimulates artifact optimizedDone targetDone

/-!
Compose the generated-CFG optimizer congruence with the certified late-return
raw execution.  The only truncation reflection obligation is equality of CFG
errors across `RuntimeOutcomeRel`.
-/
theorem Artifact.generated_entry_openRunNPrefix_compact_forward
    {artifact : Artifact}
    {sourceProgram : Structured.Program}
    {entryShapes : Structured.TypedCfgCompiler.ProcEntryShapes}
    {cfg : TypedCfg.Program}
    (context :
      Structured.TypedCfgPreservation.Program.GeneratedContext
        sourceProgram entryShapes cfg)
    (hSourceWF : sourceProgram.WF)
    (hTyped : cfg.WellTyped)
    (hIndependent : cfg.ProgramCounterIndependent)
    {sourceState : Structured.RunState} {cfgState : EVMState}
    (hStateRel :
      Structured.TypedCfgPreservation.StateRel sourceState [] cfgState)
    (hValid : artifact.ValidFor cfg)
    (fuel : Nat) (byteSuffix : List UInt8 := []) :
    Simulation.Interaction.ForwardRel
      TypedCfg.InteractionSemantics.Program.PrefixTruncated
      (GeneratedCompactRunSimulates artifact)
      (TypedCfg.InteractionSemantics.Program.openRunNPrefix
        cfg fuel cfg.entry cfgState)
      (Assembly.Compact.InteractionSemantics.openRunNResult
        (Assembly.Bytecode.ofList
          (artifact.base.base.compact.bytes.toList ++ byteSuffix))
        (fuel * artifact.fuelBudget)
        { cfgState with pc := EvmYul.UInt256.ofNat 0 }) := by
  have hLate :
      LateArtifactValidFor artifact.base.base cfg :=
    hValid.baseValid.baseValid
  have hOptimized :=
    ReturnAddressProbe.optimizedCfg?_entry_openRunNPrefix_rel_of_generated
      context hSourceWF hTyped hIndependent hStateRel
      hLate.optimized fuel
  have hRaw :=
    artifact.entry_openRunNPrefix_compact_forward
      hValid hIndependent fuel cfgState byteSuffix
  have hComposed :=
    Simulation.Interaction.ForwardRel.trans
      (Simulation.Interaction.ForwardRel.ofRel hOptimized)
      hRaw
      (fun sourceDone optimizedError hDone hTruncated => by
        have hSourceDone :
            sourceDone = .error optimizedError :=
          TypedCfg.Peephole.runtimeOutcomeRel_eq_error_right hDone
        subst sourceDone
        exact ⟨optimizedError, rfl, hTruncated⟩)
  simpa [GeneratedCompactRunSimulates] using hComposed

end WholeVerified

end Compact

end LateReturnCompactPreservation
end TypedCfg
end EvmCompiler
