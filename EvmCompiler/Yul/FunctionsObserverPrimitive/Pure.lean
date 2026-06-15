import EvmCompiler.Yul.FunctionsObserverPrimitive.Core

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

inductive PureBinary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      EvmYul.Primop.Binary → Prop where
  | add : PureBinary (.StopArith .ADD) .add EvmYul.UInt256.add
  | mul : PureBinary (.StopArith .MUL) .mul EvmYul.UInt256.mul
  | sub : PureBinary (.StopArith .SUB) .sub EvmYul.UInt256.sub
  | div : PureBinary (.StopArith .DIV) .div EvmYul.UInt256.div
  | sdiv : PureBinary (.StopArith .SDIV) .sdiv EvmYul.UInt256.sdiv
  | mod : PureBinary (.StopArith .MOD) .mod EvmYul.UInt256.mod
  | smod : PureBinary (.StopArith .SMOD) .smod EvmYul.UInt256.smod
  | exp : PureBinary (.StopArith .EXP) .exp EvmYul.UInt256.exp
  | signextend :
      PureBinary (.StopArith .SIGNEXTEND) .signextend
        EvmYul.UInt256.signextend
  | lt : PureBinary (.CompBit .LT) .lt EvmYul.UInt256.lt
  | gt : PureBinary (.CompBit .GT) .gt EvmYul.UInt256.gt
  | slt : PureBinary (.CompBit .SLT) .slt EvmYul.UInt256.slt
  | sgt : PureBinary (.CompBit .SGT) .sgt EvmYul.UInt256.sgt
  | eq : PureBinary (.CompBit .EQ) .eq EvmYul.UInt256.eq
  | and : PureBinary (.CompBit .AND) .and EvmYul.UInt256.land
  | or : PureBinary (.CompBit .OR) .or EvmYul.UInt256.lor
  | xor : PureBinary (.CompBit .XOR) .xor EvmYul.UInt256.xor
  | byte : PureBinary (.CompBit .BYTE) .byte EvmYul.UInt256.byteAt
  | shl :
      PureBinary (.CompBit .SHL) .shl
        (flip EvmYul.UInt256.shiftLeft)
  | shr :
      PureBinary (.CompBit .SHR) .shr
        (flip EvmYul.UInt256.shiftRight)
  | sar : PureBinary (.CompBit .SAR) .sar EvmYul.UInt256.sar

def YulPureBinaryOneAt (fuel : Nat)
    (prim : EvmYul.Operation .Yul) (f : EvmYul.Primop.Binary) : Prop :=
  ∀ {sourceShared : EvmYul.SharedState .Yul}
    {sourceVars : EvmYul.Yul.VarStore}
    {sourceValues : List Word}
    {sourceAfter : EvmYul.Yul.State} {outputs : List Word},
    EvmYul.Yul.primCall fuel (.Ok sourceShared sourceVars)
        prim sourceValues =
      .ok (sourceAfter, outputs) →
    ∃ left right : Word,
      sourceValues = [left, right] ∧
        sourceAfter = .Ok sourceShared sourceVars ∧
        outputs = [f left right]

def FunctionsPureBinaryOne
    (op : Structured.BasicOp) (f : EvmYul.Primop.Binary) : Prop :=
  ∀ (shared : EvmYul.SharedState .EVM) (left right : Word),
    Locals.Source.PrimitiveSemantics.structured.eval
        op shared [right, left] =
      .ok (shared, [f left right])

theorem yul_primCall_succ_eq_of_pureBinary
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.execBinOp f source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem PureBinary.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_pureBinary hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.execBinOp] at hRun
          subst exception
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons left rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.execBinOp] at hRun
              subst exception
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable
          | cons right extra =>
              cases extra with
              | nil =>
                  simp [EvmYul.Yul.execBinOp] at hRun
              | cons head tail =>
                  simp [EvmYul.Yul.execBinOp] at hRun
                  subst exception
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem yulPureBinaryOneAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    YulPureBinaryOneAt fuel prim f := by
  intro sourceShared sourceVars sourceValues sourceAfter outputs hCall
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      rw [yul_primCall_succ_eq_of_pureBinary hFamily] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.execBinOp] at hCall
      | cons left rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.execBinOp] at hCall
          | cons right extra =>
              cases extra with
              | nil =>
                  simp [EvmYul.Yul.execBinOp] at hCall
                  rcases hCall with ⟨rfl, rfl⟩
                  exact ⟨left, right, rfl, rfl, rfl⟩
              | cons head tail =>
                  simp [EvmYul.Yul.execBinOp] at hCall

theorem PureBinary.inputs
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    Expressions.Structured.BasicOp.inputs op = 2 := by
  cases hFamily <;> rfl

theorem PureBinary.sourceContinuingStep
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
      some (.bin f) := by
  cases hFamily <;> rfl

theorem PureBinary.yulObserver
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    ObserverSemantics.yulPrimObserver? prim = none := by
  cases hFamily <;> rfl

theorem PureBinary.functionsObserver
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    Functions.ObserverSemantics.basicOpObserver? op = none := by
  cases hFamily <;> rfl

theorem PureBinary.nonterminal
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    Prim.terminal? prim = none := by
  cases hFamily <;> rfl

theorem PureBinary.compilerOp
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> rfl

theorem functionsPureBinaryOne
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    FunctionsPureBinaryOne op f := by
  intro shared left right
  have hInputs := hFamily.inputs
  have hStep := hFamily.sourceContinuingStep
  simp [Locals.Source.PrimitiveSemantics.structured,
    hInputs, hStep, Assembly.PrimStep.run, EvmYul.EVM.execBinOp,
    EvmYul.EVM.State.replaceStackAndIncrPC,
    EvmYul.EVM.State.incrPC, EvmYul.Stack.pop2,
    EvmYul.Stack.push]
  rfl

theorem forwardAt_of_pureBinary
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    (hFamily : PureBinary prim op f) :
    ForwardAt codeRel fuel prim op := by
  intro source source' target sourceValues outputs hRel hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  obtain
      ⟨left, right, hValues, hSourceAfter, hOutputs⟩ :=
    yulPureBinaryOneAt hFamily hCall
  subst sourceValues
  subst source'
  subst outputs
  refine ⟨target.shared, ?_, ?_, by rfl⟩
  · simpa using functionsPureBinaryOne hFamily target.shared left right
  · simpa [Locals.Source.State.withShared] using
      (show
        StateRelation.Regular.Rel codeRel
          (.Ok sourceShared sourceVars) target from
        ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem safePureBinary
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Binary}
    {sourceValues outputs : List Word}
    (hFamily : PureBinary prim op f)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store :=
  safeBasicOp hFamily.yulObserver hFamily.functionsObserver
    hFamily.nonterminal hFamily.compilerOp
    (forwardAt_of_pureBinary hFamily) hRel hRun

inductive PureUnary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      EvmYul.Primop.Unary → Prop where
  | iszero : PureUnary (.CompBit .ISZERO) .iszero EvmYul.UInt256.isZero
  | not : PureUnary (.CompBit .NOT) .not EvmYul.UInt256.lnot

inductive PureTernary :
    EvmYul.Operation .Yul → Structured.BasicOp →
      EvmYul.Primop.Ternary → Prop where
  | addmod :
      PureTernary (.StopArith .ADDMOD) .addmod EvmYul.UInt256.addMod
  | mulmod :
      PureTernary (.StopArith .MULMOD) .mulmod EvmYul.UInt256.mulMod

theorem yul_primCall_succ_eq_of_pureUnary
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Unary}
    (hFamily : PureUnary prim op f)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.execUnOp f source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem yul_primCall_succ_eq_of_pureTernary
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Ternary}
    (hFamily : PureTernary prim op f)
    (fuel : Nat) (source : EvmYul.Yul.State)
    (args : List Word) :
    EvmYul.Yul.primCall fuel.succ source prim args =
      (match EvmYul.Yul.execTriOp f source args with
      | .ok (state, value?) => .ok (state, value?.toList)
      | .error err => .error err) := by
  cases hFamily <;>
    simp [EvmYul.Yul.primCall] <;>
    unfold EvmYul.step <;>
    rfl

theorem PureUnary.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {f : EvmYul.Primop.Unary}
    (hFamily : PureUnary prim op f) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_pureUnary hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.execUnOp] at hRun
          subst exception
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons value extra =>
          cases extra with
          | nil =>
              simp [EvmYul.Yul.execUnOp] at hRun
          | cons head tail =>
              simp [EvmYul.Yul.execUnOp] at hRun
              subst exception
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem PureTernary.rawNoObservableFailureAt
    {fuel : Nat} {prim : EvmYul.Operation .Yul}
    {op : Structured.BasicOp} {f : EvmYul.Primop.Ternary}
    (hFamily : PureTernary prim op f) :
    RawNoObservableFailureAt fuel prim := by
  intro source values exception hRun hObservable
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hRun
      subst exception
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  | succ previous =>
      rw [yul_primCall_succ_eq_of_pureTernary hFamily] at hRun
      cases values with
      | nil =>
          simp [EvmYul.Yul.execTriOp] at hRun
          subst exception
          simp [Yul.Source.Effectful.Exception.Observable] at hObservable
      | cons first rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.execTriOp] at hRun
              subst exception
              simp [Yul.Source.Effectful.Exception.Observable] at hObservable
          | cons second rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.execTriOp] at hRun
                  subst exception
                  simp [Yul.Source.Effectful.Exception.Observable] at hObservable
              | cons third extra =>
                  cases extra with
                  | nil =>
                      simp [EvmYul.Yul.execTriOp] at hRun
                  | cons head tail =>
                      simp [EvmYul.Yul.execTriOp] at hRun
                      subst exception
                      simp [Yul.Source.Effectful.Exception.Observable] at hObservable

theorem PureUnary.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Unary}
    (hFamily : PureUnary prim op f) :
    Expressions.Structured.BasicOp.inputs op = 1 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.un f) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PureTernary.metadata
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Ternary}
    (hFamily : PureTernary prim op f) :
    Expressions.Structured.BasicOp.inputs op = 3 ∧
      Locals.Source.PrimitiveSemantics.sourceContinuingStep? op =
        some (.tri f) ∧
      ObserverSemantics.yulPrimObserver? prim = none ∧
      Functions.ObserverSemantics.basicOpObserver? op = none ∧
      Prim.terminal? prim = none ∧
      Prim.toUncheckedBasicOp? prim = some op := by
  cases hFamily <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem forwardAt_of_pureUnary
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Unary}
    (hFamily : PureUnary prim op f) :
    ForwardAt codeRel fuel prim op := by
  intro source source' target sourceValues outputs hRel hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      rw [yul_primCall_succ_eq_of_pureUnary hFamily] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.execUnOp] at hCall
      | cons value rest =>
          cases rest with
          | cons head tail =>
              simp [EvmYul.Yul.execUnOp] at hCall
          | nil =>
              simp [EvmYul.Yul.execUnOp] at hCall
              rcases hCall with ⟨rfl, rfl⟩
              refine ⟨target.shared, ?_, ?_, by rfl⟩
              · obtain ⟨hInputs, hStep, _⟩ := hFamily.metadata
                simp [Locals.Source.PrimitiveSemantics.structured,
                  hInputs, hStep, Assembly.PrimStep.run,
                  EvmYul.EVM.execUnOp, EvmYul.Stack.pop,
                  EvmYul.EVM.State.replaceStackAndIncrPC,
                  EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
                rfl
              · simpa [Locals.Source.State.withShared] using
                  (show
                    StateRelation.Regular.Rel codeRel
                      (.Ok sourceShared sourceVars) target from
                    ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem forwardAt_of_pureTernary
    {codeRel : StateRelation.CodeRel} {fuel : Nat}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Ternary}
    (hFamily : PureTernary prim op f) :
    ForwardAt codeRel fuel prim op := by
  intro source source' target sourceValues outputs hRel hCall
  rcases hRel with
    ⟨sourceShared, sourceVars, hSource, hShared, hVars⟩
  subst source
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hCall
  | succ fuel =>
      rw [yul_primCall_succ_eq_of_pureTernary hFamily] at hCall
      cases sourceValues with
      | nil =>
          simp [EvmYul.Yul.execTriOp] at hCall
      | cons left rest =>
          cases rest with
          | nil =>
              simp [EvmYul.Yul.execTriOp] at hCall
          | cons middle rest =>
              cases rest with
              | nil =>
                  simp [EvmYul.Yul.execTriOp] at hCall
              | cons right extra =>
                  cases extra with
                  | cons head tail =>
                      simp [EvmYul.Yul.execTriOp] at hCall
                  | nil =>
                      simp [EvmYul.Yul.execTriOp] at hCall
                      rcases hCall with ⟨rfl, rfl⟩
                      refine ⟨target.shared, ?_, ?_, by rfl⟩
                      · obtain ⟨hInputs, hStep, _⟩ := hFamily.metadata
                        simp [Locals.Source.PrimitiveSemantics.structured,
                          hInputs, hStep, Assembly.PrimStep.run,
                          EvmYul.EVM.execTriOp, EvmYul.Stack.pop3,
                          EvmYul.EVM.State.replaceStackAndIncrPC,
                          EvmYul.EVM.State.incrPC, EvmYul.Stack.push]
                        rfl
                      · simpa [Locals.Source.State.withShared] using
                          (show
                            StateRelation.Regular.Rel codeRel
                              (.Ok sourceShared sourceVars) target from
                            ⟨sourceShared, sourceVars, rfl, hShared, hVars⟩)

theorem safePureUnary
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Unary}
    {sourceValues outputs : List Word}
    (hFamily : PureUnary prim op f)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOp hYulObserver hFunctionsObserver hTerminal hOp
      (forwardAt_of_pureUnary hFamily) hRel hRun

theorem safePureTernary
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {f : EvmYul.Primop.Ternary}
    {sourceValues outputs : List Word}
    (hFamily : PureTernary prim op f)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store := by
  obtain ⟨_hInputs, _hStep, hYulObserver, hFunctionsObserver,
      hTerminal, hOp⟩ := hFamily.metadata
  exact
    safeBasicOp hYulObserver hFunctionsObserver hTerminal hOp
      (forwardAt_of_pureTernary hFamily) hRel hRun

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
