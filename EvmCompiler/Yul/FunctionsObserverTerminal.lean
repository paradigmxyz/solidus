import EvmCompiler.Yul.FunctionsObserverExpression
import EvmCompiler.Yul.FunctionsObserverOutcome
import EvmCompiler.Yul.CompilerStatementDecomposition

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverTerminal

abbrev Trace := Assembly.ResourceTrace
abbrev Word := Assembly.Word

private theorem stop
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source failureState :
      ObserverSemantics.SourceReplay.State transcript}
    {sourceFinal : EvmYul.Yul.State}
    {value : Word}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval
          fuel source (.StopArith .STOP) [] =
        .error
          { exception := .YulHalt sourceFinal value
            state := failureState }) :
    ∃ targetFinal,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).terminal .stop target [] =
        .ok targetFinal ∧
      FunctionsObserverOutcome.TerminalFailureRel codeRel
        { exception := .YulHalt sourceFinal value
          state := failureState }
        (Functions.Source.Effectful.Outcome.halt .stop targetFinal) := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, hShared,
      _hVars, _hDomain⟩
  obtain ⟨_hSafe, hPrimCall⟩ :=
    ObserverSafety.SafeSemantics.eval_yulHalt_parts hEval
  cases fuel with
  | zero =>
      simp [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.fail] at hPrimCall
  | succ first =>
      cases first with
      | zero =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ previous =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            EvmYul.Yul.primCall, hSource,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.setMachineState,
            ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall
          rcases hPrimCall with ⟨rfl, rfl, rfl⟩
          let targetFinal :=
            target.withSource
              (target.source.withShared
                { target.source.shared with
                  returnData := ByteArray.empty
                  H_return := ByteArray.empty })
          have hTargetObserver :
              (Functions.ObserverSemantics.primitiveSemantics
                  transcript).terminal .stop target [] =
                .ok targetFinal := by
            rfl
          have hTarget :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).terminal .stop target [] =
                .ok targetFinal :=
            Functions.ObserverSafety.SafeSemantics.terminal_of_safe
              ⟨Functions.ObserverSafety.terminalMemorySafe_stop contract,
                by simp [Functions.ObserverSafety.TerminalPermitted]⟩
              hTargetObserver
          refine ⟨targetFinal, hTarget, .stop ?_⟩
          refine
            ⟨?_,
              { sourceShared with H_return := ByteArray.empty },
              sourceVars, ?_, ?_⟩
          · simpa [targetFinal] using hRel.1
          · simp [EvmYul.Yul.State.setMachineState,
              EvmYul.Yul.State.toMachineState,
              EvmYul.MachineState.setHReturn,
              ObserverSemantics.SourceReplay.State.afterException]
          · simpa [targetFinal, Locals.Source.State.withShared] using
              StateRelation.TerminalShared.stop hShared

private theorem return_
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source failureState :
      ObserverSemantics.SourceReplay.State transcript}
    {sourceFinal : EvmYul.Yul.State}
    {value address size : Word}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval
          fuel source (.System .RETURN) [address, size] =
        .error
          { exception := .YulHalt sourceFinal value
            state := failureState }) :
    ∃ targetFinal,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).terminal .return target [size, address] =
        .ok targetFinal ∧
      FunctionsObserverOutcome.TerminalFailureRel codeRel
        { exception := .YulHalt sourceFinal value
          state := failureState }
        (Functions.Source.Effectful.Outcome.halt .return targetFinal) := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, hShared,
      _hVars, _hDomain⟩
  obtain ⟨hSafe, hPrimCall⟩ :=
    ObserverSafety.SafeSemantics.eval_yulHalt_parts hEval
  have hMemorySafe :
      Functions.ObserverSafety.TerminalMemorySafe
        contract .return [size, address] := by
    exact
      (ObserverSafety.primitiveSafe_terminal
        (contract := contract)
        (machine := source.source.sharedState.toMachineState)
        (values := [address, size]) (kind := .return)
        (prim := (.System .RETURN : EvmYul.Operation .Yul))
        rfl).mp hSafe
  cases fuel with
  | zero =>
      simp [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.fail] at hPrimCall
  | succ first =>
      cases first with
      | zero =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ previous =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, hSource,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.setMachineState,
            ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall
          rcases hPrimCall with ⟨rfl, rfl, rfl⟩
          let targetFinal :=
            target.withSource
              (target.source.withShared
                { target.source.shared with
                  toMachineState :=
                    target.source.shared.toMachineState.evmReturn
                      address size })
          have hTargetObserver :
              (Functions.ObserverSemantics.primitiveSemantics
                  transcript).terminal .return target [size, address] =
                .ok targetFinal := by
            rfl
          have hTarget :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).terminal
                  .return target [size, address] =
                .ok targetFinal :=
            Functions.ObserverSafety.SafeSemantics.terminal_of_safe
              ⟨hMemorySafe,
                by simp [Functions.ObserverSafety.TerminalPermitted]⟩
              hTargetObserver
          refine ⟨targetFinal, hTarget, .return ?_⟩
          refine
            ⟨?_,
              { sourceShared with
                  toMachineState :=
                    sourceShared.toMachineState.evmReturn address size },
              sourceVars, ?_, ?_⟩
          · simpa [targetFinal] using hRel.1
          · simp [EvmYul.Yul.State.setMachineState,
              EvmYul.Yul.State.toMachineState,
              ObserverSemantics.SourceReplay.State.afterException]
          · simpa [targetFinal, Locals.Source.State.withShared] using
              StateRelation.TerminalShared.evmReturn
                hShared address size

private theorem revert
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source failureState :
      ObserverSemantics.SourceReplay.State transcript}
    {sourceFinal : EvmYul.Yul.State}
    {address size : Word}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval
          fuel source (.System .REVERT) [address, size] =
        .error
          { exception := .Revert sourceFinal
            state := failureState }) :
    ∃ targetFinal,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).terminal .revert target [size, address] =
        .ok targetFinal ∧
      FunctionsObserverOutcome.TerminalFailureRel codeRel
        { exception := .Revert sourceFinal
          state := failureState }
        (Functions.Source.Effectful.Outcome.halt .revert targetFinal) := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, hShared,
      _hVars, _hDomain⟩
  obtain ⟨hSafe, hPrimCall⟩ :=
    ObserverSafety.SafeSemantics.eval_revert_parts hEval
  have hMemorySafe :
      Functions.ObserverSafety.TerminalMemorySafe
        contract .revert [size, address] := by
    exact
      (ObserverSafety.primitiveSafe_terminal
        (contract := contract)
        (machine := source.source.sharedState.toMachineState)
        (values := [address, size]) (kind := .revert)
        (prim := (.System .REVERT : EvmYul.Operation .Yul))
        rfl).mp hSafe
  cases fuel with
  | zero =>
      simp [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.fail] at hPrimCall
  | succ first =>
      cases first with
      | zero =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ previous =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, hSource,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.setMachineState,
            ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall
          rcases hPrimCall with ⟨rfl, rfl⟩
          let targetFinal :=
            target.withSource
              (target.source.withShared
                { target.source.shared with
                  toMachineState :=
                    target.source.shared.toMachineState.evmRevert
                      address size })
          have hTargetObserver :
              (Functions.ObserverSemantics.primitiveSemantics
                  transcript).terminal .revert target [size, address] =
                .ok targetFinal := by
            rfl
          have hTarget :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).terminal
                  .revert target [size, address] =
                .ok targetFinal :=
            Functions.ObserverSafety.SafeSemantics.terminal_of_safe
              ⟨hMemorySafe,
                by simp [Functions.ObserverSafety.TerminalPermitted]⟩
              hTargetObserver
          refine ⟨targetFinal, hTarget, .revert ?_⟩
          refine
            ⟨?_,
              { sourceShared with
                  toMachineState :=
                    sourceShared.toMachineState.evmRevert address size },
              sourceVars, ?_, ?_⟩
          · simpa [targetFinal] using hRel.1
          · simp [EvmYul.Yul.State.setMachineState,
              EvmYul.Yul.State.toMachineState,
              ObserverSemantics.SourceReplay.State.afterException]
          · simpa [targetFinal, Locals.Source.State.withShared] using
              StateRelation.TerminalShared.evmRevert
                hShared address size

private theorem selfdestruct
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source failureState :
      ObserverSemantics.SourceReplay.State transcript}
    {sourceFinal : EvmYul.Yul.State}
    {value recipient : Word}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval
          fuel source (.System .SELFDESTRUCT) [recipient] =
        .error
          { exception := .YulHalt sourceFinal value
            state := failureState }) :
    ∃ targetFinal,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).terminal
          .selfdestruct target [recipient] =
        .ok targetFinal ∧
      FunctionsObserverOutcome.TerminalFailureRel codeRel
        { exception := .YulHalt sourceFinal value
          state := failureState }
        (Functions.Source.Effectful.Outcome.halt
          .selfdestruct targetFinal) := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, hShared,
      _hVars, _hDomain⟩
  obtain ⟨hSafe, hPrimCall⟩ :=
    ObserverSafety.SafeSemantics.eval_yulHalt_parts hEval
  have hMemorySafe :
      Functions.ObserverSafety.TerminalMemorySafe
        contract .selfdestruct [recipient] := by
    exact
      (ObserverSafety.primitiveSafe_terminal
        (contract := contract)
        (machine := source.source.sharedState.toMachineState)
        (values := [recipient]) (kind := .selfdestruct)
        (prim := (.System .SELFDESTRUCT : EvmYul.Operation .Yul))
        rfl).mp hSafe
  cases fuel with
  | zero =>
      simp [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.fail] at hPrimCall
  | succ first =>
      cases first with
      | zero =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ previous =>
          have hPermSource :
              sourceShared.executionEnv.perm = true := by
            by_cases hPerm :
                sourceShared.executionEnv.perm = false
            · have hStatic :
                  EvmYul.Yul.primCall previous.succ
                      (.Ok sourceShared sourceVars)
                      (.System .SELFDESTRUCT) [recipient] =
                    .error .StaticModeViolation := by
                simp [EvmYul.Yul.primCall,
                  EvmYul.Yul.State.executionEnv, hPerm,
                  MonadExcept.throw, MonadExceptOf.throw,
                  instMonadExceptOfExcept, Except.bind]
                change
                  (Except.error .StaticModeViolation :
                    Except EvmYul.Yul.Exception
                      (EvmYul.Yul.State × List Word)) =
                    .error .StaticModeViolation
                rfl
              simp only [ObserverSemantics.SourceReplay.primCall,
                ObserverSemantics.yulPrimObserver?,
                Prim.toUncheckedBasicOp?, Prim.toBasicOp?, hSource]
                at hPrimCall
              rw [hStatic] at hPrimCall
              simp [ObserverSemantics.SourceReplay.State.afterException,
                Yul.Source.Effectful.fail] at hPrimCall
            · cases hValue : sourceShared.executionEnv.perm with
              | false => exact (hPerm hValue).elim
              | true => rfl
          have hPermTarget :
              target.source.shared.executionEnv.perm = true := by
            rw [← hShared.world.executionEnv.permission]
            exact hPermSource
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, hSource,
            EvmYul.Yul.State.executionEnv, hPermSource,
            EvmYul.Yul.State.setState,
            EvmYul.Yul.State.setMachineState,
            ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall
          rcases hPrimCall with ⟨rfl, rfl, rfl⟩
          let targetFinal :=
            target.withSource
              (target.source.withShared
                ((EvmYul.EVM.selfdestructState
                  { toSharedState := target.source.shared
                    pc := EvmYul.UInt256.ofNat 0
                    stack := [recipient]
                    execLength := 0 }
                  recipient []).toSharedState))
          have hTargetObserver :
              (Functions.ObserverSemantics.primitiveSemantics
                  transcript).terminal
                  .selfdestruct target [recipient] =
                .ok targetFinal := by
            rfl
          have hTarget :
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                  contract transcript).terminal
                  .selfdestruct target [recipient] =
                .ok targetFinal :=
            Functions.ObserverSafety.SafeSemantics.terminal_of_safe
              ⟨hMemorySafe,
                by
                  intro _hKind
                  exact hPermTarget⟩
              hTargetObserver
          refine ⟨targetFinal, hTarget, .selfdestruct ?_⟩
          refine
            ⟨?_,
              (EvmYul.Yul.selfdestructState
                (.Ok sourceShared sourceVars) recipient).sharedState,
              sourceVars, ?_, ?_⟩
          · simpa [targetFinal] using hRel.1
          · simp [ObserverSemantics.SourceReplay.State.afterException,
              EvmYul.Yul.selfdestructState,
              EvmYul.Yul.State.setState,
              EvmYul.Yul.State.setMachineState,
              EvmYul.Yul.State.sharedState,
              EvmYul.Yul.State.toState,
              EvmYul.Yul.State.executionEnv,
              EvmYul.Yul.State.toMachineState,
              EvmYul.MachineState.setHReturn]
          · simpa [targetFinal, Locals.Source.State.withShared] using
              StateRelation.TerminalShared.selfdestruct
                hShared sourceVars recipient

private inductive Invocation
    (contract : MemoryContract.Contract)
    (machine : EvmYul.MachineState) :
    EvmYul.Operation .Yul → Assembly.HaltKind → List Word → Prop where
  | stop :
      Invocation contract machine (.StopArith .STOP) .stop []
  | return (address size : Word)
      (safe :
        Simulation.MemorySafety.TerminalMemorySafe
          contract .return [size, address]) :
      Invocation contract machine
        (.System .RETURN) .return [address, size]
  | revert (address size : Word)
      (safe :
        Simulation.MemorySafety.TerminalMemorySafe
          contract .revert [size, address]) :
      Invocation contract machine
        (.System .REVERT) .revert [address, size]
  | selfdestruct (recipient : Word) :
      Invocation contract machine
        (.System .SELFDESTRUCT) .selfdestruct [recipient]

private theorem Invocation.of_safe
    {contract : MemoryContract.Contract}
    {machine : EvmYul.MachineState}
    {prim : EvmYul.Operation .Yul}
    {kind : Assembly.HaltKind}
    {values : List Word}
    (hTerminal : Prim.terminal? prim = some kind)
    (hSafe : ObserverSafety.PrimitiveSafe contract prim machine values) :
    Invocation contract machine prim kind values := by
  have hTerminalSafe :
      Simulation.MemorySafety.TerminalMemorySafe
        contract kind values.reverse :=
    (ObserverSafety.primitiveSafe_terminal hTerminal).mp hSafe
  cases prim with
  | StopArith primitive =>
      cases primitive <;> simp [Prim.terminal?] at hTerminal
      case STOP =>
        subst kind
        cases values with
        | nil => exact .stop
        | cons head tail =>
            simp [Simulation.MemorySafety.TerminalMemorySafe]
              at hTerminalSafe
  | CompBit primitive =>
      cases primitive <;> simp [Prim.terminal?] at hTerminal
  | Keccak primitive =>
      cases primitive <;> simp [Prim.terminal?] at hTerminal
  | Env primitive =>
      cases primitive <;> simp [Prim.terminal?] at hTerminal
  | Block primitive =>
      cases primitive <;> simp [Prim.terminal?] at hTerminal
  | StackMemFlow primitive =>
      cases primitive <;> simp [Prim.terminal?] at hTerminal
  | Log primitive =>
      cases primitive <;> simp [Prim.terminal?] at hTerminal
  | System primitive =>
      cases primitive <;> simp [Prim.terminal?] at hTerminal
      case RETURN =>
        subst kind
        cases values with
        | nil =>
            simp [Simulation.MemorySafety.TerminalMemorySafe]
              at hTerminalSafe
        | cons address rest =>
          cases rest with
          | nil =>
              simp [Simulation.MemorySafety.TerminalMemorySafe]
                at hTerminalSafe
          | cons size tail =>
            cases tail with
            | nil =>
                exact .return address size hTerminalSafe
            | cons third tail =>
                simp [Simulation.MemorySafety.TerminalMemorySafe]
                  at hTerminalSafe
      case REVERT =>
        subst kind
        cases values with
        | nil =>
            simp [Simulation.MemorySafety.TerminalMemorySafe]
              at hTerminalSafe
        | cons address rest =>
          cases rest with
          | nil =>
              simp [Simulation.MemorySafety.TerminalMemorySafe]
                at hTerminalSafe
          | cons size tail =>
            cases tail with
            | nil =>
                exact .revert address size hTerminalSafe
            | cons third tail =>
                simp [Simulation.MemorySafety.TerminalMemorySafe]
                  at hTerminalSafe
      case SELFDESTRUCT =>
        subst kind
        cases values with
        | nil =>
            simp [Simulation.MemorySafety.TerminalMemorySafe]
              at hTerminalSafe
        | cons recipient tail =>
          cases tail with
          | nil => exact .selfdestruct recipient
          | cons next tail =>
              simp [Simulation.MemorySafety.TerminalMemorySafe]
                at hTerminalSafe

private theorem stop_not_revert
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source failureState :
      ObserverSemantics.SourceReplay.State transcript}
    {sourceFinal : EvmYul.Yul.State}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval
          fuel source (.StopArith .STOP) [] =
        .error
          { exception := .Revert sourceFinal
            state := failureState }) :
    False := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, _hShared,
      _hVars, _hDomain⟩
  obtain ⟨_hSafe, hPrimCall⟩ :=
    ObserverSafety.SafeSemantics.eval_revert_parts hEval
  cases fuel with
  | zero =>
      simp [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.fail] at hPrimCall
  | succ first =>
      cases first with
      | zero =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ previous =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, hSource,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.setMachineState,
            ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall
          obtain ⟨halted, value, hStep⟩ :
              ∃ halted value,
                EvmYul.step
                    (.StopArith .STOP : EvmYul.Operation .Yul)
                    (arg := none) (.Ok sourceShared sourceVars) [] =
                  .error (.YulHalt halted value) := by
            exact ⟨_, _, rfl⟩
          rw [hStep] at hPrimCall
          simp [
            ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall

private theorem return_not_revert
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source failureState :
      ObserverSemantics.SourceReplay.State transcript}
    {sourceFinal : EvmYul.Yul.State}
    {address size : Word}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval
          fuel source (.System .RETURN) [address, size] =
        .error
          { exception := .Revert sourceFinal
            state := failureState }) :
    False := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, _hShared,
      _hVars, _hDomain⟩
  obtain ⟨_hSafe, hPrimCall⟩ :=
    ObserverSafety.SafeSemantics.eval_revert_parts hEval
  cases fuel with
  | zero =>
      simp [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.fail] at hPrimCall
  | succ first =>
      cases first with
      | zero =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ previous =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, hSource,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.setMachineState,
            ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall
          obtain ⟨halted, value, hStep⟩ :
              ∃ halted value,
                EvmYul.step
                    (.System .RETURN : EvmYul.Operation .Yul)
                    (arg := none) (.Ok sourceShared sourceVars)
                    [address, size] =
                  .error (.YulHalt halted value) := by
            exact ⟨_, _, rfl⟩
          rw [hStep] at hPrimCall
          simp [ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall

private theorem revert_not_yulHalt
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source failureState :
      ObserverSemantics.SourceReplay.State transcript}
    {sourceFinal : EvmYul.Yul.State}
    {value address size : Word}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval
          fuel source (.System .REVERT) [address, size] =
        .error
          { exception := .YulHalt sourceFinal value
            state := failureState }) :
    False := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, _hShared,
      _hVars, _hDomain⟩
  obtain ⟨_hSafe, hPrimCall⟩ :=
    ObserverSafety.SafeSemantics.eval_yulHalt_parts hEval
  cases fuel with
  | zero =>
      simp [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.fail] at hPrimCall
  | succ first =>
      cases first with
      | zero =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ previous =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, hSource,
            EvmYul.Yul.State.executionEnv,
            EvmYul.Yul.State.setMachineState,
            ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall
          obtain ⟨reverted, hStep⟩ :
              ∃ reverted,
                EvmYul.step
                    (.System .REVERT : EvmYul.Operation .Yul)
                    (arg := none) (.Ok sourceShared sourceVars)
                    [address, size] =
                  .error (.Revert reverted) := by
            exact ⟨_, rfl⟩
          rw [hStep] at hPrimCall
          simp [ObserverSemantics.SourceReplay.State.afterException,
            Yul.Source.Effectful.fail] at hPrimCall

private theorem selfdestruct_not_revert
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source failureState :
      ObserverSemantics.SourceReplay.State transcript}
    {sourceFinal : EvmYul.Yul.State}
    {recipient : Word}
    {target : Functions.ObserverSemantics.State transcript}
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval
          fuel source (.System .SELFDESTRUCT) [recipient] =
        .error
          { exception := .Revert sourceFinal
            state := failureState }) :
    False := by
  rcases hRel.2 with
    ⟨sourceShared, sourceVars, hSource, _hShared,
      _hVars, _hDomain⟩
  obtain ⟨_hSafe, hPrimCall⟩ :=
    ObserverSafety.SafeSemantics.eval_revert_parts hEval
  cases fuel with
  | zero =>
      simp [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.fail] at hPrimCall
  | succ first =>
      cases first with
      | zero =>
          simp [ObserverSemantics.SourceReplay.primCall,
            ObserverSemantics.yulPrimObserver?,
            Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
            EvmYul.Yul.primCall, Yul.Source.Effectful.fail] at hPrimCall
      | succ previous =>
          by_cases hPerm :
              sourceShared.executionEnv.perm = false
          · have hStatic :
                EvmYul.Yul.primCall previous.succ
                    (.Ok sourceShared sourceVars)
                    (.System .SELFDESTRUCT) [recipient] =
                  .error .StaticModeViolation := by
              simp [EvmYul.Yul.primCall,
                EvmYul.Yul.State.executionEnv, hPerm,
                MonadExcept.throw, MonadExceptOf.throw,
                instMonadExceptOfExcept, Except.bind]
              change
                (Except.error .StaticModeViolation :
                  Except EvmYul.Yul.Exception
                    (EvmYul.Yul.State × List Word)) =
                  .error .StaticModeViolation
              rfl
            simp only [ObserverSemantics.SourceReplay.primCall,
              ObserverSemantics.yulPrimObserver?,
              Prim.toUncheckedBasicOp?, Prim.toBasicOp?, hSource]
              at hPrimCall
            rw [hStatic] at hPrimCall
            simp [ObserverSemantics.SourceReplay.State.afterException,
              Yul.Source.Effectful.fail] at hPrimCall
          · cases hValue : sourceShared.executionEnv.perm with
            | false => exact (hPerm hValue).elim
            | true =>
                simp [ObserverSemantics.SourceReplay.primCall,
                  ObserverSemantics.yulPrimObserver?,
                  Prim.toUncheckedBasicOp?, Prim.toBasicOp?,
                  EvmYul.Yul.primCall, hSource,
                  EvmYul.Yul.State.executionEnv, hValue,
                  EvmYul.Yul.State.setState,
                  EvmYul.Yul.State.setMachineState,
                  ObserverSemantics.SourceReplay.State.afterException,
                  Yul.Source.Effectful.fail] at hPrimCall
                obtain ⟨halted, value, hStep⟩ :
                    ∃ halted value,
                      EvmYul.step
                          (.System .SELFDESTRUCT :
                            EvmYul.Operation .Yul)
                          (arg := none) (.Ok sourceShared sourceVars)
                          [recipient] =
                        .error (.YulHalt halted value) := by
                  exact ⟨_, _, rfl⟩
                rw [hStep] at hPrimCall
                simp [
                  ObserverSemantics.SourceReplay.State.afterException,
                  Yul.Source.Effectful.fail] at hPrimCall

/--
Every observable guarded execution of a primitive selected as terminal by the
ordinary Yul-to-Functions compiler is implemented by the canonical Functions
terminal handler. Arity, halt mode, and source exception shape are all derived
from the actual source execution.
-/
theorem primitiveForward
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {layout : List Name}
    {fuel : Nat}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul}
    {kind : Assembly.HaltKind}
    {values : List Word}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    (hTerminal : Prim.terminal? prim = some kind)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception)
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hEval :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel source prim values =
        .error failure) :
    ∃ targetFinal,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).terminal
          kind target values.reverse =
        .ok targetFinal ∧
      FunctionsObserverOutcome.TerminalFailureRel codeRel failure
        (Functions.Source.Effectful.Outcome.halt kind targetFinal) := by
  rcases failure with ⟨exception, failureState⟩
  cases exception with
  | YulHalt sourceFinal value =>
      have hSafe :=
        (ObserverSafety.SafeSemantics.eval_yulHalt_parts hEval).1
      cases Invocation.of_safe hTerminal hSafe with
      | stop =>
          exact stop hRel hEval
      | «return» address size safe =>
          exact return_ hRel hEval
      | revert address size safe =>
          exact (revert_not_yulHalt hRel hEval).elim
      | selfdestruct recipient =>
          exact selfdestruct hRel hEval
  | Revert sourceFinal =>
      have hSafe :=
        (ObserverSafety.SafeSemantics.eval_revert_parts hEval).1
      cases Invocation.of_safe hTerminal hSafe with
      | stop =>
          exact (stop_not_revert hRel hEval).elim
      | «return» address size safe =>
          exact (return_not_revert hRel hEval).elim
      | revert address size safe =>
          exact revert hRel hEval
      | selfdestruct recipient =>
          exact (selfdestruct_not_revert hRel hEval).elim
  | _ =>
      simp [Yul.Source.Effectful.Exception.Observable] at hObservable

structure StatementResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (lower : List Functions.Stmt)
    (failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript))
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx) where
  kind : Assembly.HaltKind
  finalTarget : Functions.ObserverSemantics.State transcript
  finalCtx : Functions.Source.Ctx
  run :
    ∃ fuel,
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx fuel { stmts := lower } target =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind finalTarget,
            finalCtx)
  relation :
    FunctionsObserverOutcome.TerminalFailureRel codeRel failure
      (Functions.Source.Effectful.Outcome.halt kind finalTarget)

structure ForLoopResult
    {transcript : Trace}
    (contract : MemoryContract.Contract)
    (codeRel : StateRelation.CodeRel)
    (program : Functions.Program)
    (post body : Functions.Block)
    (failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript))
    (target : Functions.ObserverSemantics.State transcript)
    (ctx : Functions.Source.Ctx) where
  kind : Assembly.HaltKind
  finalTarget : Functions.ObserverSemantics.State transcript
  run :
    ∃ fuel,
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx.withoutLoopControl
          (.lit (EvmYul.UInt256.ofNat 1))
          ctx.withoutLoopControl post
          (ctx.withLoopControl ctx.scope ctx.scope)
          body fuel target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            kind finalTarget)
  relation :
    FunctionsObserverOutcome.TerminalFailureRel codeRel failure
      (Functions.Source.Effectful.Outcome.halt kind finalTarget)

namespace ForLoopResult

def ofBody
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {post body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (bodyResult :
      StatementResult contract codeRel program body.stmts failure target
        (ctx.withLoopControl ctx.scope ctx.scope)) :
    Nonempty
      (ForLoopResult contract codeRel program post body
        failure target ctx) := by
  rcases body with ⟨bodyStmts⟩
  obtain ⟨bodyFuel, hBodyOpen⟩ := bodyResult.run
  have hBodyScoped :
      Functions.Source.Effectful.Block.runScoped
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program (ctx.withLoopControl ctx.scope ctx.scope)
          { stmts := bodyStmts } bodyFuel target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            bodyResult.kind bodyResult.finalTarget) :=
    by
      simpa using
        Functions.Source.Effectful.Block.runScoped_nonregular_of_runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program hBodyOpen (by simp)
  have hOuterCond :
      Functions.Source.Effectful.Expr.evalCondition
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          (.lit (EvmYul.UInt256.ofNat 1)) target =
        .ok (target, true) :=
    Functions.ObserverSafety.SafeSemantics.evalCondition_one target
  exact
    ⟨
      { kind := bodyResult.kind
        finalTarget := bodyResult.finalTarget
        run :=
          ⟨bodyFuel + 1,
            Functions.Source.Effectful.Stmt.runForLoop_body_halt_of_runs
              (Functions.ObserverSemantics.stateModel transcript)
              (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              program hOuterCond hBodyScoped⟩
        relation := bodyResult.relation }⟩

end ForLoopResult

namespace StatementResult

def prependRegularRun
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {leftLower rightLower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target middleTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx middleCtx : Functions.Source.Ctx}
    (left :
      ∃ fuel,
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx fuel { stmts := leftLower } target =
          .ok
            (Functions.Source.Effectful.Outcome.regular middleTarget,
              middleCtx))
    (right :
      StatementResult contract codeRel program rightLower failure
        middleTarget middleCtx) :
    StatementResult contract codeRel program
      (leftLower ++ rightLower) failure target ctx := by
  exact
    { kind := right.kind
      finalTarget := right.finalTarget
      finalCtx := right.finalCtx
      run :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program leftLower rightLower ctx middleCtx target middleTarget
          (Functions.Source.Effectful.Outcome.halt
            right.kind right.finalTarget)
          right.finalCtx left right.run
      relation := right.relation }

def prependPrepared
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {leftLower rightLower : List Functions.Stmt}
    {middleFresh : Fresh.State}
    {sourceMiddle :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      FunctionsObserverExpression.Prepared
        contract transcript codeRel program leftLower middleFresh
        sourceMiddle target ctx)
    (right :
      StatementResult contract codeRel program rightLower failure
        left.finalTarget left.finalCtx) :
    StatementResult contract codeRel program
      (leftLower ++ rightLower) failure target ctx := by
  exact
    { kind := right.kind
      finalTarget := right.finalTarget
      finalCtx := right.finalCtx
      run :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program leftLower rightLower ctx left.finalCtx target
          left.finalTarget
          (Functions.Source.Effectful.Outcome.halt
            right.kind right.finalTarget)
          right.finalCtx left.run right.run
      relation := right.relation }

def prependRegular
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {sourceControl : FunctionsObserverOutcome.SourceControlScopes}
    {leftLower rightLower : List Functions.Stmt}
    {initial middle : Fresh.State}
    {entryLayout : List Name}
    {sourceMiddle :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      FunctionsObserverOutcome.ScopedOpenResult
        contract codeRel program leftLower initial middle
        entryLayout sourceMiddle target ctx
        (sourceControl := sourceControl))
    (hRegular : left.outcome.mode = .regular)
    (right :
      StatementResult contract codeRel program rightLower failure
        left.outcome.state left.finalCtx) :
    StatementResult contract codeRel program
      (leftLower ++ rightLower) failure target ctx := by
  have hLeftOutcome :
      left.outcome =
        Functions.Source.Effectful.Outcome.regular
          left.outcome.state :=
    Functions.Source.Effectful.Outcome.eq_regular_of_mode hRegular
  have hLeftRun :
      ∃ fuel,
        Functions.Source.Effectful.Block.runOpen
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx fuel { stmts := leftLower } target =
          .ok
            (Functions.Source.Effectful.Outcome.regular
              left.outcome.state,
              left.finalCtx) := by
    rcases left.run with ⟨fuel, hRun⟩
    rw [hLeftOutcome] at hRun
    exact ⟨fuel, hRun⟩
  exact
    { kind := right.kind
      finalTarget := right.finalTarget
      finalCtx := right.finalCtx
      run :=
        Functions.Source.Effectful.Block.runOpen_append_regular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program leftLower rightLower ctx left.finalCtx target
          left.outcome.state
          (Functions.Source.Effectful.Outcome.halt
            right.kind right.finalTarget)
          right.finalCtx hLeftRun right.run
      relation := right.relation }

def appendUnreachable
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {leftLower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (left :
      StatementResult contract codeRel program leftLower
        failure target ctx)
    (rightLower : List Functions.Stmt) :
    StatementResult contract codeRel program
      (leftLower ++ rightLower) failure target ctx := by
  exact
    { kind := left.kind
      finalTarget := left.finalTarget
      finalCtx := left.finalCtx
      run :=
        Functions.Source.Effectful.Block.runOpen_append_nonregular_exists
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program leftLower rightLower ctx target
          (Functions.Source.Effectful.Outcome.halt
            left.kind left.finalTarget)
          left.finalCtx left.run (by simp)
      relation := left.relation }

def block
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {lower : List Functions.Stmt}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    (body :
      StatementResult contract codeRel program lower
        failure target ctx) :
    StatementResult contract codeRel program
      [.block { stmts := lower }] failure target ctx := by
  exact
    { kind := body.kind
      finalTarget := body.finalTarget
      finalCtx := ctx
      run :=
        Functions.Source.Effectful.Block.runOpen_singleton_block_of_runOpen_nonregular
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program body.run (by simp)
      relation := body.relation }

def ofForLoop
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {post body : Functions.Block}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target finalTarget :
      Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {kind : Assembly.HaltKind}
    (hLoop :
      ∃ fuel,
        Functions.Source.Effectful.Stmt.runForLoop
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program ctx.withoutLoopControl
            (.lit (EvmYul.UInt256.ofNat 1))
            ctx.withoutLoopControl post
            (ctx.withLoopControl ctx.scope ctx.scope)
            body fuel target =
          .ok
            (Functions.Source.Effectful.Outcome.halt
              kind finalTarget))
    (hRelation :
      FunctionsObserverOutcome.TerminalFailureRel codeRel failure
        (Functions.Source.Effectful.Outcome.halt kind finalTarget)) :
    Nonempty
      (StatementResult contract codeRel program
        [.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
          post body]
        failure target ctx) := by
  obtain ⟨loopFuel, hLoopRun⟩ := hLoop
  let commonFuel := max 1 loopFuel
  have hInit :
      Functions.Source.Effectful.Block.runOpen
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx.withoutLoopControl commonFuel
          { stmts := [] } target =
        .ok
          (Functions.Source.Effectful.Outcome.regular target,
            ctx.withoutLoopControl) :=
    Functions.Source.Effectful.Block.runOpen_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (by simp [commonFuel])
      (Functions.Source.Effectful.Block.runOpen_nil
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program ctx.withoutLoopControl 0 target)
  have hLoopRun' :
      Functions.Source.Effectful.Stmt.runForLoop
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx.withoutLoopControl
          (.lit (EvmYul.UInt256.ofNat 1))
          ctx.withoutLoopControl post
          (ctx.withLoopControl ctx.scope ctx.scope)
          body commonFuel target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            kind finalTarget) :=
    Functions.Source.Effectful.Stmt.runForLoop_mono
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program (by simp [commonFuel]) hLoopRun
  have hStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program ctx (commonFuel + 1)
          (.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
            post body)
          target =
        .ok
          (Functions.Source.Effectful.Outcome.halt
            kind finalTarget,
            ctx) := by
    simpa [Functions.Source.Ctx.withoutLoopControl,
      Functions.Source.Ctx.withLoopControl] using
      Functions.Source.Effectful.Stmt.run_for_halt_of_runs
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hInit hLoopRun'
  exact
    ⟨
      { kind := kind
        finalTarget := finalTarget
        finalCtx := ctx
        run :=
          Functions.Source.Effectful.Block.runOpen_singleton_of_run
            (Functions.ObserverSemantics.stateModel transcript)
            (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
              contract transcript)
            program hStmt
        relation := hRelation }⟩

end StatementResult

/--
Terminal statement preservation once all source arguments have evaluated
regularly. The compiler-owned argument preamble and stack sequence are executed
through the generic expression theorem; only the final terminal action uses
`primitiveForward`.
-/
theorem statementAfterArgs
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {argsFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {preArgs : List Functions.Stmt}
    {lowerArgs : List (Locals.Expr 1)}
    {seq : Locals.ExprSeq kind.argCount}
    {source sourceAfterArgs :
      ObserverSemantics.SourceReplay.State transcript}
    {reversedValues : List Word}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {Eligible : AstExpr → Prop}
    (hTerminal : Prim.terminal? prim = some kind)
    (hLowerArgs :
      Expr.List.lowerBound1Unchecked? before args =
        some (preArgs, lowerArgs, after))
    (hSeq :
      Expr.List.toStackSeq? lowerArgs kind.argCount = some seq)
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < argsFuel →
          Eligible expr →
          Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin
              exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            (FunctionsObserverExpression.ScopedPreparedValue
              contract transcript codeRel program exprPre exprLower
              exprAfter layout exprSource' exprTarget exprCtx value))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hArgsRun :
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          argsFuel args.reverse codeOverride source =
        .ok (sourceAfterArgs, reversedValues))
    (hPrimRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval argsFuel sourceAfterArgs prim
          reversedValues.reverse =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    Nonempty
      (StatementResult contract codeRel program
        (preArgs ++ [Functions.Stmt.terminalArgs kind seq])
        failure target ctx) := by
  obtain ⟨argsPrepared⟩ :=
    FunctionsObserverExpression.ScopedPreparedArgs.ofUncheckedLowering
      (Expr.List.uncheckedBoundLowering_of_lowerBound1Unchecked?
        hLowerArgs)
      hEligible
      (fun hArgFuel hArgOk hArgLower hArgRel
          hArgDomain hArgScope hArgRun =>
        hExpr hArgFuel hArgOk hArgLower hArgRel
          hArgDomain hArgScope hArgRun)
      hRel hDomain hScope hArgsRun
  let targetAfterArgs :=
    argsPrepared.prepared.prepared.finalTarget
  have hStackArgs :=
    argsPrepared.prepared.stackStable targetAfterArgs
      (StateRelation.Vars.TargetExtends.refl _)
  have hTargetArgList :
      Functions.Source.Effectful.ArgList.eval
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          lowerArgs.reverse targetAfterArgs =
        .ok (targetAfterArgs, reversedValues) := by
    simpa [targetAfterArgs] using hStackArgs
  obtain ⟨targetFinal, hTargetTerminal, hTerminalRel⟩ :=
    primitiveForward hTerminal hObservable
      argsPrepared.relation hPrimRun
  have hTargetTerminal' :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).terminal kind targetAfterArgs
          reversedValues =
        .ok targetFinal := by
    simpa [targetAfterArgs] using hTargetTerminal
  have hTerminalStmt :
      Functions.Source.Effectful.Stmt.run
          (Functions.ObserverSemantics.stateModel transcript)
          (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          program
          argsPrepared.prepared.prepared.finalCtx 0
          (.terminalArgs kind seq) targetAfterArgs =
        .ok
          (Functions.Source.Effectful.Outcome.halt kind targetFinal,
            argsPrepared.prepared.prepared.finalCtx) := by
    exact
      FunctionsObserverExpression.terminalArgs_run_of_argList
        (Functions.ObserverSemantics.stateModel transcript)
        (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        program hSeq hTargetArgList hTargetTerminal'
  have hTerminalBlock :=
    Functions.Source.Effectful.Block.runOpen_singleton_of_run
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program hTerminalStmt
  have hFullRun :=
    Functions.Source.Effectful.Block.runOpen_append_regular_exists
      (Functions.ObserverSemantics.stateModel transcript)
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
        contract transcript)
      program preArgs
      [Functions.Stmt.terminalArgs kind seq]
      ctx argsPrepared.prepared.prepared.finalCtx
      target targetAfterArgs
      (Functions.Source.Effectful.Outcome.halt kind targetFinal)
      argsPrepared.prepared.prepared.finalCtx
      argsPrepared.prepared.prepared.run hTerminalBlock
  exact
    ⟨kind, targetFinal, argsPrepared.prepared.prepared.finalCtx,
      hFullRun, hTerminalRel⟩

/--
Compiler-driven classification for an observable terminal expression
statement. A source failure either comes from a recursively evaluated argument,
or the real emitted argument preamble and `terminalArgs` statement reach the
checked terminal primitive theorem.
-/
theorem statementClassify
    {contract : MemoryContract.Contract}
    {transcript : Trace}
    {codeRel : StateRelation.CodeRel}
    {program : Functions.Program}
    {codeOverride : Option EvmYul.Yul.Ast.YulContract}
    {sourceFuel compilerFuel : Nat}
    {before after : Fresh.State}
    {layout : List Name}
    {prim : EvmYul.Operation .Yul}
    {args : List AstExpr}
    {kind : Assembly.HaltKind}
    {lower : List Functions.Stmt}
    {source :
      ObserverSemantics.SourceReplay.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {target : Functions.ObserverSemantics.State transcript}
    {ctx : Functions.Source.Ctx}
    {Eligible : AstExpr → Prop}
    (hTerminal : Prim.terminal? prim = some kind)
    (hLower :
      Stmt.toFunctionsListUncheckedFuel? compilerFuel before
          (.ExprStmtCall (.Call (.inl prim) args)) =
        some (lower, after))
    (hEligible : ∀ expr, expr ∈ args → Eligible expr)
    (hExpr :
      ∀ {exprFuel : Nat} {exprBefore exprAfter : Fresh.State}
        {expr : AstExpr} {exprPre : List Functions.Stmt}
        {exprLower : Locals.Expr 1}
        {exprSource exprSource' :
          ObserverSemantics.SourceReplay.State transcript}
        {exprTarget : Functions.ObserverSemantics.State transcript}
        {exprCtx : Functions.Source.Ctx} {value : Word},
        exprFuel < sourceFuel →
          Eligible expr →
          Expr.lower1Unchecked? exprBefore expr =
            some (exprPre, exprLower, exprAfter) →
          StateRelation.Replay.ScopedExactRel codeRel layout
            exprSource exprTarget →
          StateRelation.Vars.TargetDomainWithin
              exprBefore.used exprTarget.source.vars →
          StateRelation.Vars.NamesWithin
              exprBefore.used exprCtx.scope →
          Yul.Source.Effectful.eval
              (ObserverSemantics.SourceReplay.stateModel transcript)
              (ObserverSafety.SafeSemantics.primitiveSemantics
                contract transcript)
              exprFuel expr codeOverride exprSource =
            .ok (exprSource', value) →
          Nonempty
            (FunctionsObserverExpression.ScopedPreparedValue
              contract transcript codeRel program exprPre exprLower
              exprAfter layout exprSource' exprTarget exprCtx value))
    (hRel :
      StateRelation.Replay.ScopedExactRel codeRel layout source target)
    (hDomain :
      StateRelation.Vars.TargetDomainWithin
        before.used target.source.vars)
    (hScope :
      StateRelation.Vars.NamesWithin before.used ctx.scope)
    (hRun :
      Yul.Source.Effectful.exec
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          sourceFuel
          (.ExprStmtCall (.Call (.inl prim) args))
          codeOverride source =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    (∃ argsFuel,
      sourceFuel = argsFuel + 1 ∧
      Yul.Source.Effectful.evalArgs
          (ObserverSemantics.SourceReplay.stateModel transcript)
          (ObserverSafety.SafeSemantics.primitiveSemantics
            contract transcript)
          argsFuel args.reverse codeOverride source =
        .error failure) ∨
    Nonempty
      (StatementResult contract codeRel program lower failure target ctx) := by
  obtain ⟨preArgs, lowerArgs, seq,
      hLowerArgs, hSeq, hLowerStmts⟩ :=
    Stmt.toFunctionsListUncheckedFuel?_expr_terminal_parts
      hTerminal hLower
  subst lower
  rcases
      Yul.Source.Effectful.exec_expr_primitive_error_parts
        (ObserverSemantics.SourceReplay.stateModel transcript)
        (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript)
        hRun with hOuter | hPrevious
  · rcases hOuter with ⟨rfl, hFailure⟩
    rw [← hFailure] at hObservable
    simp [Yul.Source.Effectful.Exception.Observable] at hObservable
  · rcases hPrevious with
      ⟨argsFuel, hSourceFuel, hArgsFailure | hPrimitive⟩
    · exact Or.inl ⟨argsFuel, hSourceFuel, hArgsFailure⟩
    · rcases hPrimitive with
        ⟨sourceAfterArgs, reversedValues, hArgsRun, hPrimRun⟩
      refine Or.inr ?_
      apply
        statementAfterArgs hTerminal hLowerArgs hSeq hEligible
          (fun hArgFuel hArgOk hArgLower hArgRel
              hArgDomain hArgScope hArgRun =>
            hExpr (by omega) hArgOk hArgLower hArgRel
              hArgDomain hArgScope hArgRun)
          hRel hDomain hScope hArgsRun hPrimRun hObservable

end FunctionsObserverTerminal
end Yul
end EvmCompiler
