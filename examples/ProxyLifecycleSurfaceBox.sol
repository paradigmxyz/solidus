// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract ProxyLifecycleLogicV1 {
    error DeliberateFailure(uint256 attempted);

    event ValueChanged(uint256 indexed beforeValue, uint256 indexed afterValue);
    event Reentered(uint256 indexed requested, uint256 returnedValue);

    uint256 public value;

    function set(uint256 next) external virtual returns (uint256) {
        uint256 beforeValue = value;
        value = next;
        emit ValueChanged(beforeValue, next);
        return value;
    }

    function reenter(uint256 next) external returns (uint256 result) {
        (bool ok, bytes memory output) = address(this).call(
            abi.encodeCall(this.set, (next))
        );
        if (!ok) {
            assembly ("memory-safe") {
                revert(add(output, 0x20), mload(output))
            }
        }
        result = abi.decode(output, (uint256));
        emit Reentered(next, result);
    }

    function failAfterStore(uint256 attempted) external {
        uint256 beforeValue = value;
        value = attempted;
        emit ValueChanged(beforeValue, attempted);
        revert DeliberateFailure(attempted);
    }

    function version() external pure virtual returns (uint256) {
        return 1;
    }
}

contract ProxyLifecycleLogicV2 is ProxyLifecycleLogicV1 {
    function set(uint256 next) external override returns (uint256) {
        uint256 adjusted = next + 1;
        uint256 beforeValue = value;
        value = adjusted;
        emit ValueChanged(beforeValue, adjusted);
        return value;
    }

    function version() external pure override returns (uint256) {
        return 2;
    }
}

/// @notice Executes proxy dispatch, delegated state, reentrancy, rollback,
/// child creation, and upgrade behavior through one persistent call sequence.
contract ProxyLifecycleSurfaceBox {
    event Upgraded(address indexed implementation);

    bytes32 private constant IMPLEMENTATION_SLOT =
        bytes32(uint256(keccak256("eip1967.proxy.implementation")) - 1);

    constructor() {
        _setImplementation(address(new ProxyLifecycleLogicV1()));
    }

    function implementation() external view returns (address result) {
        bytes32 slot = IMPLEMENTATION_SLOT;
        assembly ("memory-safe") {
            result := sload(slot)
        }
    }

    function upgradeToV2() external returns (address result) {
        result = address(new ProxyLifecycleLogicV2());
        _setImplementation(result);
        emit Upgraded(result);
    }

    function _setImplementation(address implementation_) private {
        bytes32 slot = IMPLEMENTATION_SLOT;
        assembly ("memory-safe") {
            sstore(slot, implementation_)
        }
    }

    fallback() external payable {
        bytes32 slot = IMPLEMENTATION_SLOT;
        assembly ("memory-safe") {
            let target := sload(slot)
            calldatacopy(0, 0, calldatasize())
            let ok := delegatecall(gas(), target, 0, calldatasize(), 0, 0)
            returndatacopy(0, 0, returndatasize())
            switch ok
            case 0 { revert(0, returndatasize()) }
            default { return(0, returndatasize()) }
        }
    }
}
