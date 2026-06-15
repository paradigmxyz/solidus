import EvmCompiler.Yul.FunctionsObserverCompiler
import EvmCompiler.Yul.FunctionsObserverExpression

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverCall

/-!
Function-call preservation owned by the adjacent Yul-to-Functions pass.

This module composes the ordinary selected `FunDef`, canonical call-frame
semantics, and the recursive body theorem. It does not define a call
interpreter, compiler, replay certificate, or callee oracle.
-/

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

structure ReturnedBody
    (contract : MemoryContract.Contract)
    (transcript : Trace)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (fn : Functions.FunDef)
    (args : List Word)
    (bodyFuel : Nat)
    (sourceAfterBody : ObserverSemantics.SourceReplay.State transcript)
    (targetCaller : Functions.ObserverSemantics.State transcript) where
  paramStore : Locals.Source.Store
  bodyOutcome :
    Functions.Source.Effectful.Outcome
      (Functions.ObserverSemantics.State transcript)
  finalCtx : Functions.Source.Ctx
  params :
    Functions.Source.Store.insertMany fn.params args
        Locals.Source.Store.empty =
      some paramStore
  run :
    Functions.Source.Effectful.Block.runOpen
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program (Functions.Source.Effectful.FunDef.bodyCtx fn)
        bodyFuel fn.body
        (targetCaller.withSource
          { shared := targetCaller.source.shared,
            vars :=
              Functions.Source.Store.initReturns fn.returns paramStore }) =
      .ok
        (bodyOutcome, finalCtx)
  mode :
    bodyOutcome.mode = .regular ∨ bodyOutcome.mode = .leave
  relation :
    StateRelation.Replay.ScopedExactRel codeRel
      (fn.returns ++ fn.params)
      (sourceAfterBody.withSource sourceAfterBody.source.reviveJump)
      bodyOutcome.state

namespace ReturnedBody

theorem compose
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {fn : Functions.FunDef}
    {args : List Word}
    {bodyFuel : Nat}
    {sourceCaller sourceAfterBody :
      ObserverSemantics.SourceReplay.State transcript}
    {targetCaller : Functions.ObserverSemantics.State transcript}
    (body :
      ReturnedBody contract transcript codeRel program fn args bodyFuel
        sourceAfterBody targetCaller)
    (hCaller :
      StateRelation.Replay.Rel codeRel sourceCaller targetCaller) :
    ∃ returnValues,
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn args (bodyFuel + 1) targetCaller =
        .ok
          (Functions.Source.Effectful.CallResult.returned
            body.bodyOutcome.state returnValues) ∧
      returnValues =
        List.map sourceAfterBody.source.lookup! fn.returns ∧
      StateRelation.Replay.Rel codeRel
        (sourceAfterBody.withSource
          ((sourceAfterBody.source.reviveJump.overwrite?
            sourceCaller.source).setStore sourceCaller.source))
        (body.bodyOutcome.state.withSource
          { shared := body.bodyOutcome.state.source.shared,
            vars := targetCaller.source.vars }) := by
  have hReturns :
      Functions.Source.Store.lookupMany fn.returns
          body.bodyOutcome.state.source.vars =
        some (List.map sourceAfterBody.source.lookup! fn.returns) :=
    StateRelation.Replay.lookupMany_of_scopedExact body.relation
      (by
        intro name hMem
        exact List.mem_append_left fn.params hMem)
  have hRunBody :
      Functions.Source.Effectful.FunDef.runBody
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program fn args (bodyFuel + 1) targetCaller =
        .ok
          (Functions.Source.Effectful.CallResult.returned
            body.bodyOutcome.state
            (List.map sourceAfterBody.source.lookup! fn.returns)) :=
    Functions.Source.Effectful.FunDef.runBody_returned_of_parts
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program body.params body.run body.mode hReturns rfl
  exact
    ⟨List.map sourceAfterBody.source.lookup! fn.returns,
      hRunBody, rfl,
      StateRelation.Replay.restore_call hCaller body.relation⟩

end ReturnedBody

end FunctionsObserverCall
end Yul
end EvmCompiler
