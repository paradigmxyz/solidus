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
      StateRelation.Replay.Rel codeRel source' target' ∧
      source'.source.store = source.source.store := by
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

theorem safeCompilerSelectedBackwardAt
    (fuel : Nat)
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues outputs : List Word}
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval (fuel + 2) source prim sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store := by
  cases prim with
  | StopArith primitive =>
      cases primitive with
      | STOP => simp [Prim.terminal?] at hTerminal
      | ADD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .add hRel hRun
      | MUL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .mul hRel hRun
      | SUB =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .sub hRel hRun
      | DIV =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .div hRel hRun
      | SDIV =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .sdiv hRel hRun
      | MOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .mod hRel hRun
      | SMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .smod hRel hRun
      | ADDMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureTernaryBackward .addmod hRel hRun
      | MULMOD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureTernaryBackward .mulmod hRel hRun
      | EXP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .exp hRel hRun
      | SIGNEXTEND =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .signextend hRel hRun
  | CompBit primitive =>
      cases primitive with
      | LT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .lt hRel hRun
      | GT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .gt hRel hRun
      | SLT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .slt hRel hRun
      | SGT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .sgt hRel hRun
      | EQ =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .eq hRel hRun
      | ISZERO =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureUnaryBackward .iszero hRel hRun
      | AND =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .and hRel hRun
      | OR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .or hRel hRun
      | XOR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .xor hRel hRun
      | NOT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureUnaryBackward .not hRel hRun
      | BYTE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .byte hRel hRun
      | SHL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .shl hRel hRun
      | SHR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .shr hRel hRun
      | SAR =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePureBinaryBackward .sar hRel hRun
  | Keccak primitive =>
      cases primitive with
      | KECCAK256 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeKeccak256Backward hRel hRun
  | Env primitive =>
      cases primitive with
      | ADDRESS =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .address hRel hRun
      | BALANCE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccessBackward .balance hRel hRun
      | ORIGIN =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .origin hRel hRun
      | CALLER =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .caller hRel hRun
      | CALLVALUE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .callvalue hRel hRun
      | CALLDATALOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryReadBackward .calldataload hRel hRun
      | CALLDATASIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .calldatasize hRel hRun
      | CALLDATACOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeSharedTernaryCopyBackward .calldatacopy hRel hRun
      | GASPRICE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .gasprice hRel hRun
      | CODESIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .codesize hRel hRun
      | CODECOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeSharedTernaryCopyBackward .codecopy hRel hRun
      | EXTCODESIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccessBackward .extcodesize hRel hRun
      | EXTCODECOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeExtcodecopyBackward hRel hRun
      | RETURNDATASIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeReturndatasizeBackward hRel hRun
      | RETURNDATACOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeReturndatacopyBackward hRel hRun
      | EXTCODEHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccessBackward .extcodehash hRel hRun
  | Block primitive =>
      cases primitive with
      | BLOCKHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryReadBackward .blockhash hRel hRun
      | COINBASE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullaryBackward .coinbase hRel hRun
      | TIMESTAMP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullaryBackward .timestamp hRel hRun
      | NUMBER =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullaryBackward .number hRel hRun
      | PREVRANDAO =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .prevrandao hRel hRun
      | GASLIMIT =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullaryBackward .gaslimit hRel hRun
      | CHAINID =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullaryBackward .chainid hRel hRun
      | SELFBALANCE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldNullaryBackward .selfbalance hRel hRun
      | BASEFEE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .basefee hRel hRun
      | BLOBHASH =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentUnaryBackward .blobhash hRel hRun
      | BLOBBASEFEE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeEnvironmentNullaryBackward .blobbasefee hRel hRun
  | StackMemFlow primitive =>
      cases primitive with
      | POP =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safePopBackward hRel hRun
      | MLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeMloadBackward hRel hRun
      | MSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeMachineBinaryZeroBackward .mstore hRel hRun
      | SLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccessBackward .sload hRel hRun
      | SSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldBinaryWriteBackward .sstore hRel hRun
      | MSTORE8 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeMachineBinaryZeroBackward .mstore8 hRel hRun
      | MSIZE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          have hReverse :
              sourceValues.reverse = [] :=
            Functions.ObserverSafety.SafeSemantics.eval_observer_values_eq_nil
              (by rfl) hRun
          have hValues : sourceValues = [] := by
            simpa using congrArg List.reverse hReverse
          subst sourceValues
          simpa using msizeSafeBackward (fuel := fuel + 1) hRel hRun
      | GAS =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          have hReverse :
              sourceValues.reverse = [] :=
            Functions.ObserverSafety.SafeSemantics.eval_observer_values_eq_nil
              (by rfl) hRun
          have hValues : sourceValues = [] := by
            simpa using congrArg List.reverse hReverse
          subst sourceValues
          simpa using gasSafeBackward (fuel := fuel + 1) hRel hRun
      | TLOAD =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldUnaryAccessBackward .tload hRel hRun
      | TSTORE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeWorldBinaryWriteBackward .tstore hRel hRun
      | MCOPY =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeMcopyBackward hRel hRun
  | Log primitive =>
      cases primitive with
      | LOG0 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLogBackward .log0 hRel hRun
      | LOG1 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLogBackward .log1 hRel hRun
      | LOG2 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLogBackward .log2 hRel hRun
      | LOG3 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLogBackward .log3 hRel hRun
      | LOG4 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeLogBackward .log4 hRel hRun
  | System primitive =>
      cases primitive with
      | CREATE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _hPermitted, _hTargetRun⟩ :=
            Functions.ObserverSafety.SafeSemantics.eval_parts hRun
          have : False := by
            simpa only [
              Functions.ObserverSafety.PrimitiveMemorySafe,
              Simulation.MemorySafety.PrimitiveMemorySafe] using hSafe
          exact this.elim
      | CALL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _hPermitted, _hTargetRun⟩ :=
            Functions.ObserverSafety.SafeSemantics.eval_parts hRun
          have : False := by
            simpa only [
              Functions.ObserverSafety.PrimitiveMemorySafe,
              Simulation.MemorySafety.PrimitiveMemorySafe] using hSafe
          exact this.elim
      | CALLCODE =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _hPermitted, _hTargetRun⟩ :=
            Functions.ObserverSafety.SafeSemantics.eval_parts hRun
          have : False := by
            simpa only [
              Functions.ObserverSafety.PrimitiveMemorySafe,
              Simulation.MemorySafety.PrimitiveMemorySafe] using hSafe
          exact this.elim
      | RETURN => simp [Prim.terminal?] at hTerminal
      | DELEGATECALL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _hPermitted, _hTargetRun⟩ :=
            Functions.ObserverSafety.SafeSemantics.eval_parts hRun
          have : False := by
            simpa only [
              Functions.ObserverSafety.PrimitiveMemorySafe,
              Simulation.MemorySafety.PrimitiveMemorySafe] using hSafe
          exact this.elim
      | CREATE2 =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _hPermitted, _hTargetRun⟩ :=
            Functions.ObserverSafety.SafeSemantics.eval_parts hRun
          have : False := by
            simpa only [
              Functions.ObserverSafety.PrimitiveMemorySafe,
              Simulation.MemorySafety.PrimitiveMemorySafe] using hSafe
          exact this.elim
      | STATICCALL =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          obtain ⟨hSafe, _hPermitted, _hTargetRun⟩ :=
            Functions.ObserverSafety.SafeSemantics.eval_parts hRun
          have : False := by
            simpa only [
              Functions.ObserverSafety.PrimitiveMemorySafe,
              Simulation.MemorySafety.PrimitiveMemorySafe] using hSafe
          exact this.elim
      | REVERT => simp [Prim.terminal?] at hTerminal
      | INVALID =>
          simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
          subst op
          exact safeInvalidBackward hRel hRun
      | SELFDESTRUCT => simp [Prim.terminal?] at hTerminal

/--
The canonical minimum-fuel specialization used by leaf expression proofs.
-/
theorem safeCompilerSelectedBackward
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target target' : Functions.ObserverSemantics.State transcript}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues outputs : List Word}
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (Functions.ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval op target sourceValues.reverse =
        .ok (target', outputs)) :
    ∃ source' : ObserverSemantics.SourceReplay.State transcript,
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval 2 source prim sourceValues =
          .ok (source', outputs) ∧
        StateRelation.Replay.Rel codeRel source' target' ∧
        source'.source.store = source.source.store := by
  simpa using
    safeCompilerSelectedBackwardAt 0 hTerminal hOp hRel hRun

/--
A guarded, compiler-selected nonterminal primitive cannot produce a public
terminal Yul exception. Malformed arguments, static-mode rejection, depleted
observer replay, and other interpreter failures remain non-observable.
-/
theorem safeCompilerSelected_noObservableFailure
    {contract : MemoryContract.Contract}
    {transcript : Assembly.ResourceTrace}
    {codeRel : StateRelation.CodeRel}
    {fuel : Nat}
    {source : ObserverSemantics.SourceReplay.State transcript}
    {target : Functions.ObserverSemantics.State transcript}
    {failure :
      Yul.Source.Effectful.Failure
        (ObserverSemantics.SourceReplay.State transcript)}
    {prim : EvmYul.Operation .Yul} {op : Structured.BasicOp}
    {sourceValues : List Word}
    (hTerminal : Prim.terminal? prim = none)
    (hOp : Prim.toUncheckedBasicOp? prim = some op)
    (hArity :
      sourceValues.length = Expressions.Structured.BasicOp.inputs op)
    (hRel : StateRelation.Replay.Rel codeRel source target)
    (hRun :
      (ObserverSafety.SafeSemantics.primitiveSemantics
          contract transcript).eval fuel source prim sourceValues =
        .error failure)
    (hObservable :
      Yul.Source.Effectful.Exception.Observable failure.exception) :
    False := by
  obtain ⟨hSourceSafe, hSourceRun⟩ :=
    ObserverSafety.SafeSemantics.eval_observable_error_parts
      hRun hObservable
  cases fuel with
  | zero =>
      have hResultObservable :
          Yul.Source.Effectful.Result.Observable
            (ObserverSemantics.SourceReplay.primCall
              0 source prim sourceValues) := by
        rw [hSourceRun]
        exact hObservable
      simpa [ObserverSemantics.SourceReplay.primCall,
        Yul.Source.Effectful.Result.Observable,
        Yul.Source.Effectful.fail] using hResultObservable
  | succ previous =>
      have hRawLift
          (hObserver :
            ObserverSemantics.yulPrimObserver? prim = none)
          (hRaw :
            ∀ {rawException : EvmYul.Yul.Exception},
              EvmYul.Yul.primCall previous source.source
                  prim sourceValues =
                .error rawException →
              ¬Yul.Source.Effectful.Exception.Observable
                rawException) :
          False :=
        guardedNoObservableFailure_of_raw
          hObserver hRaw hRun hObservable
      rcases hRel.2 with
        ⟨sourceShared, sourceVars, hSource, _hShared, _hVars⟩
      cases prim with
      | StopArith primitive =>
          cases primitive with
          | STOP => simp [Prim.terminal?] at hTerminal
          | ADD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .add)
          | MUL =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .mul)
          | SUB =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .sub)
          | DIV =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .div)
          | SDIV =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .sdiv)
          | MOD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .mod)
          | SMOD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .smod)
          | ADDMOD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureTernary.rawNoObservableFailureAt .addmod)
          | MULMOD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureTernary.rawNoObservableFailureAt .mulmod)
          | EXP =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .exp)
          | SIGNEXTEND =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .signextend)
      | CompBit primitive =>
          cases primitive with
          | LT =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .lt)
          | GT =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .gt)
          | SLT =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .slt)
          | SGT =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .sgt)
          | EQ =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .eq)
          | ISZERO =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureUnary.rawNoObservableFailureAt .iszero)
          | AND =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .and)
          | OR =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .or)
          | XOR =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .xor)
          | NOT =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureUnary.rawNoObservableFailureAt .not)
          | BYTE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .byte)
          | SHL =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .shl)
          | SHR =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .shr)
          | SAR =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (PureBinary.rawNoObservableFailureAt .sar)
      | Keccak primitive =>
          cases primitive with
          | KECCAK256 =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (rawNoObservableFailureAt_keccak256 previous)
      | Env primitive =>
          cases primitive with
          | ADDRESS =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .address)
          | BALANCE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldUnaryAccess.rawNoObservableFailureAt .balance)
          | ORIGIN =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .origin)
          | CALLER =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .caller)
          | CALLVALUE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .callvalue)
          | CALLDATALOAD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldUnaryRead.rawNoObservableFailureAt .calldataload)
          | CALLDATASIZE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .calldatasize)
          | CALLDATACOPY =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (SharedTernaryCopy.rawNoObservableFailureAt .calldatacopy)
          | GASPRICE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .gasprice)
          | CODESIZE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .codesize)
          | CODECOPY =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (SharedTernaryCopy.rawNoObservableFailureAt .codecopy)
          | EXTCODESIZE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldUnaryAccess.rawNoObservableFailureAt .extcodesize)
          | EXTCODECOPY =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              obtain ⟨account, destination, readStart, size, hValues⟩ :=
                list_eq_four_of_length_eq (by simpa using hArity)
              subst sourceValues
              apply hRawLift (by rfl)
              intro rawException hRaw
              rw [hSource] at hRaw
              exact rawNoObservableFailure_extcodecopy hRaw
          | RETURNDATASIZE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hValues : sourceValues = [] := by
                apply List.eq_nil_of_length_eq_zero
                simpa [Expressions.Structured.BasicOp.inputs] using hArity
              subst sourceValues
              apply hRawLift (by rfl)
              intro rawException hRaw
              exact rawNoObservableFailure_returndatasize hRaw
          | RETURNDATACOPY =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              obtain ⟨destination, readStart, size, hValues⟩ :=
                List.length_eq_three.mp (by simpa using hArity)
              subst sourceValues
              apply hRawLift (by rfl)
              intro rawException hRaw
              rw [hSource] at hRaw
              exact rawNoObservableFailure_returndatacopy hRaw
          | EXTCODEHASH =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldUnaryAccess.rawNoObservableFailureAt .extcodehash)
      | Block primitive =>
          cases primitive with
          | BLOCKHASH =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldUnaryRead.rawNoObservableFailureAt .blockhash)
          | COINBASE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldNullary.rawNoObservableFailureAt .coinbase)
          | TIMESTAMP =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldNullary.rawNoObservableFailureAt .timestamp)
          | NUMBER =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldNullary.rawNoObservableFailureAt .number)
          | PREVRANDAO =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .prevrandao)
          | GASLIMIT =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldNullary.rawNoObservableFailureAt .gaslimit)
          | CHAINID =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldNullary.rawNoObservableFailureAt .chainid)
          | SELFBALANCE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldNullary.rawNoObservableFailureAt .selfbalance)
          | BASEFEE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .basefee)
          | BLOBHASH =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentUnary.rawNoObservableFailureAt .blobhash)
          | BLOBBASEFEE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (EnvironmentNullary.rawNoObservableFailureAt .blobbasefee)
      | StackMemFlow primitive =>
          cases primitive with
          | POP =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              obtain ⟨value, hValues⟩ :=
                List.length_eq_one_iff.mp (by simpa using hArity)
              subst sourceValues
              apply hRawLift (by rfl)
              intro rawException hRaw
              exact rawNoObservableFailure_pop hRaw
          | MLOAD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (rawNoObservableFailureAt_mload previous)
          | MSTORE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (MachineBinaryZero.rawNoObservableFailureAt .mstore)
          | SLOAD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldUnaryAccess.rawNoObservableFailureAt .sload)
          | SSTORE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldBinaryWrite.rawNoObservableFailureAt .sstore)
          | MSTORE8 =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (MachineBinaryZero.rawNoObservableFailureAt .mstore8)
          | MSIZE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hValues : sourceValues = [] := by
                apply List.eq_nil_of_length_eq_zero
                simpa [Expressions.Structured.BasicOp.inputs] using hArity
              subst sourceValues
              exact safeObserverNoObservableFailure
                ObserverSemantics.yulPrimObserver?_msize
                hRun hObservable
          | GAS =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hValues : sourceValues = [] := by
                apply List.eq_nil_of_length_eq_zero
                simpa [Expressions.Structured.BasicOp.inputs] using hArity
              subst sourceValues
              exact safeObserverNoObservableFailure
                ObserverSemantics.yulPrimObserver?_gas
                hRun hObservable
          | TLOAD =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldUnaryAccess.rawNoObservableFailureAt .tload)
          | TSTORE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (WorldBinaryWrite.rawNoObservableFailureAt .tstore)
          | MCOPY =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              exact hRawLift (by rfl)
                (rawNoObservableFailureAt_mcopy previous)
      | Log primitive =>
          cases primitive with
          | LOG0 =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              apply hRawLift (by rfl)
              intro rawException hRaw
              rw [hSource] at hRaw
              exact LogFamily.rawNoObservableFailure .log0
                (by simpa using hArity) hRaw
          | LOG1 =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              apply hRawLift (by rfl)
              intro rawException hRaw
              rw [hSource] at hRaw
              exact LogFamily.rawNoObservableFailure .log1
                (by simpa using hArity) hRaw
          | LOG2 =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              apply hRawLift (by rfl)
              intro rawException hRaw
              rw [hSource] at hRaw
              exact LogFamily.rawNoObservableFailure .log2
                (by simpa using hArity) hRaw
          | LOG3 =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              apply hRawLift (by rfl)
              intro rawException hRaw
              rw [hSource] at hRaw
              exact LogFamily.rawNoObservableFailure .log3
                (by simpa using hArity) hRaw
          | LOG4 =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              apply hRawLift (by rfl)
              intro rawException hRaw
              rw [hSource] at hRaw
              exact LogFamily.rawNoObservableFailure .log4
                (by simpa using hArity) hRaw
      | System primitive =>
          cases primitive with
          | CREATE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hImpossible :=
                (ObserverSafety.primitiveSafe_basicOp
                  (op := Structured.BasicOp.create)
                  (by rfl) (by rfl)).mp hSourceSafe
              simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using
                hImpossible
          | CALL =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hImpossible :=
                (ObserverSafety.primitiveSafe_basicOp
                  (op := Structured.BasicOp.call)
                  (by rfl) (by rfl)).mp hSourceSafe
              simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using
                hImpossible
          | CALLCODE =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hImpossible :=
                (ObserverSafety.primitiveSafe_basicOp
                  (op := Structured.BasicOp.callcode)
                  (by rfl) (by rfl)).mp hSourceSafe
              simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using
                hImpossible
          | RETURN => simp [Prim.terminal?] at hTerminal
          | DELEGATECALL =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hImpossible :=
                (ObserverSafety.primitiveSafe_basicOp
                  (op := Structured.BasicOp.delegatecall)
                  (by rfl) (by rfl)).mp hSourceSafe
              simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using
                hImpossible
          | CREATE2 =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hImpossible :=
                (ObserverSafety.primitiveSafe_basicOp
                  (op := Structured.BasicOp.create2)
                  (by rfl) (by rfl)).mp hSourceSafe
              simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using
                hImpossible
          | STATICCALL =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              have hImpossible :=
                (ObserverSafety.primitiveSafe_basicOp
                  (op := Structured.BasicOp.staticcall)
                  (by rfl) (by rfl)).mp hSourceSafe
              simpa only [Simulation.MemorySafety.PrimitiveMemorySafe] using
                hImpossible
          | REVERT => simp [Prim.terminal?] at hTerminal
          | INVALID =>
              simp [Prim.toUncheckedBasicOp?, Prim.toBasicOp?] at hOp
              subst op
              apply hRawLift (by rfl)
              intro rawException hRaw
              rw [hSource] at hRaw
              exact rawNoObservableFailure_invalid hRaw
          | SELFDESTRUCT => simp [Prim.terminal?] at hTerminal

end FunctionsObserverPrimitive
end Yul
end EvmCompiler
