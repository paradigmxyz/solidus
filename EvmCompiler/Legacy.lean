import EvmCompiler
import EvmCompiler.Assembly.Preservation
import EvmCompiler.Assembly.GasAware
import EvmCompiler.Assembly.Observer
import EvmCompiler.Structured.Preservation
import EvmCompiler.Structured.StackResource
import EvmCompiler.Expressions.Preservation
import EvmCompiler.Locals.StackLowering
import EvmCompiler.Locals.SourceLowering
import EvmCompiler.Locals.Preservation
import EvmCompiler.Functions.LiveLayout
import EvmCompiler.Functions.SourceLowering
import EvmCompiler.Functions.SourceDirect
import EvmCompiler.Functions.LiveLayoutBridge
import EvmCompiler.Functions.Preservation
import EvmCompiler.Functions.LiveLayoutPreservation
import EvmCompiler.Functions.CallAwareSpill
import EvmCompiler.Functions.ScratchFrameMemory
import EvmCompiler.Functions.ScratchFrameSpill
import EvmCompiler.Functions.CallDepth
import EvmCompiler.Functions.CallDepthRanked
import EvmCompiler.Objects.Preservation
import EvmCompiler.Yul.ArgSlots
import EvmCompiler.Yul.PrimSemantics
import EvmCompiler.Yul.Preservation
import EvmCompiler.Yul.ObjectModel
import EvmCompiler.Yul.ObjectSemantics
import EvmCompiler.Yul.ObjectPreservation
import EvmCompiler.Yul.RecursiveBridgeSupport
import EvmCompiler.Yul.ObjectRuntime
import EvmCompiler.Yul.OpenExternal
import EvmCompiler.Yul.OpenAssembly
import EvmCompiler.Yul.OpenLowering
import EvmCompiler.Yul.ObserverOracle
import EvmCompiler.Yul.NoCallCreate
import EvmCompiler.Yul.NoCallRuntime
import EvmCompiler.Solidity.BridgeJson
import EvmCompiler.LayerAudit

/-!
Compatibility import for the pre-migration public theorem surface.

New compiler clients should import `EvmCompiler` or `EvmCompiler.Public`.
Proof artifacts that intentionally audit historical runtime corridors may
import this module or their specific legacy modules directly.
-/
