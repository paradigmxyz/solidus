// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice Keeps observable effects interleaved in optimized Yul so the
/// frontend and checked backend cannot validate each family only in isolation.
contract EffectOrderingSurfaceBox {
    function interleave(
        address target,
        bytes calldata payload,
        bytes memory initCode,
        bytes32 salt
    ) external payable returns (address child, bool callSucceeded) {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, caller())
            log1(ptr, 0x20, 0x11)

            callSucceeded := call(
                gas(), target, callvalue(), payload.offset, payload.length, ptr, 0x20
            )
            log2(ptr, 0x20, 0x22, callSucceeded)

            child := create2(0, add(initCode, 0x20), mload(initCode), salt)
            log3(ptr, 0x20, 0x33, child, returndatasize())
        }
    }

    function proxy(address target, bytes calldata payload) external payable {
        assembly {
            let succeeded := delegatecall(
                gas(), target, payload.offset, payload.length, 0, 0
            )
            let size := returndatasize()
            returndatacopy(0, 0, size)
            switch succeeded
            case 0 { revert(0, size) }
            default { return(0, size) }
        }
    }
}
