import EvmCompiler.Assembly.InteractionSemantics

namespace EvmCompiler
namespace Simulation
namespace InteractionRegression

theorem classifies_all_external_kinds :
    ExternalKind.ofEVMOperation? EvmYul.Operation.CALL =
        some (.call .call) /\
      ExternalKind.ofEVMOperation? EvmYul.Operation.CALLCODE =
        some (.call .callcode) /\
      ExternalKind.ofEVMOperation? EvmYul.Operation.DELEGATECALL =
        some (.call .delegatecall) /\
      ExternalKind.ofEVMOperation? EvmYul.Operation.STATICCALL =
        some (.call .staticcall) /\
      ExternalKind.ofEVMOperation? EvmYul.Operation.CREATE =
        some (.create .create) /\
      ExternalKind.ofEVMOperation? EvmYul.Operation.CREATE2 =
        some (.create .create2) := by
  repeat' apply And.intro rfl
  rfl

/-- A representative mixed resource/external trace. The interaction carrier
fixes this order before quantifying over every answer. -/
def mixedTrace (world : OpenWorld) (call : CallRequest)
    (create : CreateRequest) : Interaction Unit Unit :=
  .request (.resource .gas) fun _gas =>
    .request (.external world (.call call)) fun _callResponse =>
      .request (.resource .msize) fun _msize =>
        .request (.external world (.create create)) fun _createResponse =>
          .done (.ok ())

theorem mixedTrace_rel (world : OpenWorld) (call : CallRequest)
    (create : CreateRequest) :
    Interaction.Rel Eq (mixedTrace world call create)
      (mixedTrace world call create) := by
  exact Interaction.Rel.refl (fun result => rfl) _

theorem mixedTrace_first_query
    {world : OpenWorld} {call : CallRequest} {create : CreateRequest}
    {exchange : Interaction.Exchange} {transcript : Interaction.Transcript}
    {outcome : Except Unit Unit}
    (hExec : Interaction.Executes (mixedTrace world call create)
      (exchange :: transcript) outcome) :
    exchange.query = .resource .gas := by
  obtain ⟨answer, hHead, _hTail⟩ :=
    Interaction.Executes.request_inv hExec
  cases hHead
  rfl

/-- External responses may install any code-erased post-world. This is the
reentrancy/open-world regression: caller storage, logs/substate, balances, and
accounts may all differ after a call. -/
theorem finishCall_installs_arbitrary_postWorld
    (state : Assembly.EVMState) (rest : EvmYul.Stack InteractionWord)
    (callLocal : CallLocal) (response : CallResponse) :
    OpenWorld.ofEVMShared
        (Assembly.InteractionSemantics.EVMState.finishCall
          state rest callLocal response).toSharedState =
      response.postWorld := by
  simp [Assembly.InteractionSemantics.EVMState.finishCall,
    Assembly.InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC]
  change OpenWorld.ofEVMState
      (OpenWorld.installEVM state.toSharedState.toState response.postWorld) =
    response.postWorld
  exact OpenWorld.ofEVMState_installEVM _ _

theorem finishCreate_installs_arbitrary_postWorld
    (state : Assembly.EVMState) (rest : EvmYul.Stack InteractionWord)
    (createLocal : CreateLocal) (response : CreateResponse) :
    OpenWorld.ofEVMShared
        (Assembly.InteractionSemantics.EVMState.finishCreate
          state rest createLocal response).toSharedState =
      response.postWorld := by
  simp [Assembly.InteractionSemantics.EVMState.finishCreate,
    Assembly.InteractionSemantics.EVMState.installWorld,
    EvmYul.EVM.State.incrPC]
  change OpenWorld.ofEVMState
      (OpenWorld.installEVM state.toSharedState.toState response.postWorld) =
    response.postWorld
  exact OpenWorld.ofEVMState_installEVM _ _

theorem callStep_rejects_static_violation
    {kind : CallKind} {state : Assembly.EVMState}
    {rest : EvmYul.Stack InteractionWord} {operands : CallOperands}
    (hOperands : kind.evmOperands? state.stack = some (rest, operands))
    (hAllowed : kind.allowedIn
      (ExternalFrame.ofShared state.toSharedState) operands = false) :
    Assembly.InteractionSemantics.PrimOp.callStep kind state =
      .done (.error .StaticModeViolation) := by
  simp [Assembly.InteractionSemantics.PrimOp.callStep,
    hOperands, hAllowed]

theorem createStep_rejects_static_mode
    {kind : CreateKind} {state : Assembly.EVMState}
    {rest : EvmYul.Stack InteractionWord} {operands : CreateOperands}
    (hOperands : kind.evmOperands? state.stack = some (rest, operands))
    (hStatic :
      (ExternalFrame.ofShared state.toSharedState).permission = false) :
    Assembly.InteractionSemantics.PrimOp.createStep kind state =
      .done (.error .StaticModeViolation) := by
  simp [Assembly.InteractionSemantics.PrimOp.createStep,
    hOperands, hStatic]

theorem calldata_zero_window
    (frame : ExternalFrame) (offset outputOffset outputSize : InteractionWord) :
    frame.calldata
        { inputOffset := offset
          inputSize := EvmYul.UInt256.ofNat 0
          outputOffset := outputOffset
          outputSize := outputSize } =
      ByteArray.empty := by
  have hZero : (EvmYul.UInt256.ofNat 0).toNat = 0 :=
    EvmYul.UInt256.toNat_ofNat_of_lt (by
      simp [EvmYul.UInt256.size])
  unfold ExternalFrame.calldata
  rw [hZero]
  simp [ByteArray.readWithPadding, ffi.ByteArray.zeroes,
    ByteArray.readWithoutPadding]
  rfl

theorem initCode_zero_window
    (frame : ExternalFrame) (offset : InteractionWord) :
    frame.initCode
        { initOffset := offset
          initSize := EvmYul.UInt256.ofNat 0 } =
      ByteArray.empty := by
  have hZero : (EvmYul.UInt256.ofNat 0).toNat = 0 :=
    EvmYul.UInt256.toNat_ofNat_of_lt (by
      simp [EvmYul.UInt256.size])
  unfold ExternalFrame.initCode
  rw [hZero]
  simp [ByteArray.readWithPadding, ffi.ByteArray.zeroes,
    ByteArray.readWithoutPadding]
  rfl

end InteractionRegression
end Simulation
end EvmCompiler
