import EvmCompiler.Yul.FunctionsObserverPrimitive.Copy
import EvmCompiler.Yul.FunctionsObserverPrimitive.Environment
import EvmCompiler.Yul.FunctionsObserverPrimitive.Invalid
import EvmCompiler.Yul.FunctionsObserverPrimitive.Log
import EvmCompiler.Yul.FunctionsObserverPrimitive.Machine
import EvmCompiler.Yul.FunctionsObserverPrimitive.Observer
import EvmCompiler.Yul.FunctionsObserverPrimitive.Pure
import EvmCompiler.Yul.FunctionsObserverPrimitive.World

namespace EvmCompiler
namespace Yul
namespace FunctionsObserverPrimitive

/--
Adjacent preservation for every nonterminal primitive selected by the ordinary
Yul-to-Functions compiler.

External call/create operations have no successful guarded source run under the
closed memory contract, so those cases are discharged internally.
-/
theorem safeCompilerSelected
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source source' : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues outputs : List Word}
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hArity :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel.succ source prim sourceValues =
        .ok (source', outputs)) :
    ∃ target' : Functions.ObserverSemantics.State transcript,
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs) ∧
      StateRelation.Replay.Rel codeRel source' target' := by
  cases prim with
  | StopArith primitive =>
      cases primitive with
      | STOP => simp [Prim.terminal?] at hTerminal
      | ADD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .add hRel hRun
      | MUL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .mul hRel hRun
      | SUB =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .sub hRel hRun
      | DIV =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .div hRel hRun
      | SDIV =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .sdiv hRel hRun
      | MOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .mod hRel hRun
      | SMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .smod hRel hRun
      | ADDMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureTernary .addmod hRel hRun
      | MULMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureTernary .mulmod hRel hRun
      | EXP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .exp hRel hRun
      | SIGNEXTEND =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .signextend hRel hRun
  | CompBit primitive =>
      cases primitive with
      | LT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .lt hRel hRun
      | GT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .gt hRel hRun
      | SLT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .slt hRel hRun
      | SGT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .sgt hRel hRun
      | EQ =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .eq hRel hRun
      | ISZERO =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureUnary .iszero hRel hRun
      | AND =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .and hRel hRun
      | OR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .or hRel hRun
      | XOR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .xor hRel hRun
      | NOT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureUnary .not hRel hRun
      | BYTE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .byte hRel hRun
      | SHL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .shl hRel hRun
      | SHR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .shr hRel hRun
      | SAR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinary .sar hRel hRun
  | Keccak primitive =>
      cases primitive with
      | KECCAK256 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeKeccak256 hRel hRun
  | Env primitive =>
      cases primitive with
      | ADDRESS =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .address (by simpa using hArity) hRel hRun
      | BALANCE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccess .balance hRel hRun
      | ORIGIN =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .origin (by simpa using hArity) hRel hRun
      | CALLER =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .caller (by simpa using hArity) hRel hRun
      | CALLVALUE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .callvalue (by simpa using hArity) hRel hRun
      | CALLDATALOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryRead .calldataload hRel hRun
      | CALLDATASIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .calldatasize (by simpa using hArity) hRel hRun
      | CALLDATACOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeSharedTernaryCopy .calldatacopy hRel hRun
      | GASPRICE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .gasprice (by simpa using hArity) hRel hRun
      | CODESIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .codesize (by simpa using hArity) hRel hRun
      | CODECOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeSharedTernaryCopy .codecopy hRel hRun
      | EXTCODESIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccess .extcodesize hRel hRun
      | EXTCODECOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeExtcodecopy hRel hRun
      | RETURNDATASIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeReturndatasize (by simpa using hArity) hRel hRun
      | RETURNDATACOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeReturndatacopy hRel hRun
      | EXTCODEHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccess .extcodehash hRel hRun
  | Block primitive =>
      cases primitive with
      | BLOCKHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryRead .blockhash hRel hRun
      | COINBASE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullary .coinbase (by simpa using hArity) hRel hRun
      | TIMESTAMP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullary .timestamp (by simpa using hArity) hRel hRun
      | NUMBER =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullary .number (by simpa using hArity) hRel hRun
      | PREVRANDAO =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .prevrandao (by simpa using hArity) hRel hRun
      | GASLIMIT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullary .gaslimit (by simpa using hArity) hRel hRun
      | CHAINID =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullary .chainid (by simpa using hArity) hRel hRun
      | SELFBALANCE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullary .selfbalance (by simpa using hArity) hRel hRun
      | BASEFEE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .basefee (by simpa using hArity) hRel hRun
      | BLOBHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentUnary .blobhash hRel hRun
      | BLOBBASEFEE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullary .blobbasefee (by simpa using hArity) hRel hRun
  | StackMemFlow primitive =>
      cases primitive with
      | POP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePop (by simpa using hArity) hRel hRun
      | MLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeMload hRel hRun
      | MSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeMachineBinaryZero .mstore hRel hRun
      | SLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccess .sload hRel hRun
      | SSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldBinaryWrite .sstore hRel hRun
      | MSTORE8 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeMachineBinaryZero .mstore8 hRel hRun
      | MSIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          have hValues : sourceValues = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa [Expressions.Structured.BasicOp.inputs] using hArity
          subst sourceValues
          exact msizeSafe hRel hRun
      | GAS =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          have hValues : sourceValues = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa [Expressions.Structured.BasicOp.inputs] using hArity
          subst sourceValues
          exact gasSafe hRel hRun
      | TLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccess .tload hRel hRun
      | TSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldBinaryWrite .tstore hRel hRun
      | MCOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeMcopy hRel hRun
  | Log primitive =>
      cases primitive with
      | LOG0 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLog .log0 (by simpa using hArity) hRel hRun
      | LOG1 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLog .log1 (by simpa using hArity) hRel hRun
      | LOG2 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLog .log2 (by simpa using hArity) hRel hRun
      | LOG3 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLog .log3 (by simpa using hArity) hRel hRun
      | LOG4 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLog .log4 (by simpa using hArity) hRel hRun
  | System primitive =>
      cases primitive with
      | CREATE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _⟩ :=
            ObserverSafety.SafeSemantics.eval_ok_parts hRun
          have hImpossible :=
            (ObserverSafety.primitiveSafe_basicOp
                (op := Structured.BasicOp.create) (by rfl) (by rfl)).mp hSafe
          have : False := by
            simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using hImpossible
          exact this.elim
      | CALL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _⟩ :=
            ObserverSafety.SafeSemantics.eval_ok_parts hRun
          have hImpossible :=
            (ObserverSafety.primitiveSafe_basicOp
                (op := Structured.BasicOp.call) (by rfl) (by rfl)).mp hSafe
          have : False := by
            simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using hImpossible
          exact this.elim
      | CALLCODE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _⟩ :=
            ObserverSafety.SafeSemantics.eval_ok_parts hRun
          have hImpossible :=
            (ObserverSafety.primitiveSafe_basicOp
                (op := Structured.BasicOp.callcode) (by rfl) (by rfl)).mp hSafe
          have : False := by
            simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using hImpossible
          exact this.elim
      | RETURN => simp [Prim.terminal?] at hTerminal
      | DELEGATECALL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _⟩ :=
            ObserverSafety.SafeSemantics.eval_ok_parts hRun
          have hImpossible :=
            (ObserverSafety.primitiveSafe_basicOp
                (op := Structured.BasicOp.delegatecall) (by rfl) (by rfl)).mp hSafe
          have : False := by
            simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using hImpossible
          exact this.elim
      | CREATE2 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _⟩ :=
            ObserverSafety.SafeSemantics.eval_ok_parts hRun
          have hImpossible :=
            (ObserverSafety.primitiveSafe_basicOp
                (op := Structured.BasicOp.create2) (by rfl) (by rfl)).mp hSafe
          have : False := by
            simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using hImpossible
          exact this.elim
      | STATICCALL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _⟩ :=
            ObserverSafety.SafeSemantics.eval_ok_parts hRun
          have hImpossible :=
            (ObserverSafety.primitiveSafe_basicOp
                (op := Structured.BasicOp.staticcall) (by rfl) (by rfl)).mp hSafe
          have : False := by
            simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using hImpossible
          exact this.elim
      | REVERT => simp [Prim.terminal?] at hTerminal
      | INVALID =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeInvalid hRel hRun
      | SELFDESTRUCT => simp [Prim.terminal?] at hTerminal

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
