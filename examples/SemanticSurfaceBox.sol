// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice Adversarial coverage for low-level operations that ordinary ABI
/// examples rarely retain in optimized Yul.
contract SemanticSurfaceBox {
    function transientAndBlob(bytes32 key, uint256 value, uint256 blobIndex)
        external
        returns (uint256 loaded, bytes32 versionedHash, uint256 blobFee)
    {
        assembly {
            tstore(key, value)
            loaded := tload(key)
            versionedHash := blobhash(blobIndex)
            blobFee := blobbasefee()
        }
    }

    function memoryAndCode(address account, uint256 value)
        external
        view
        returns (
            uint256 copied,
            uint256 localSize,
            uint256 externalSize,
            bytes32 externalHash,
            bytes32 localCodeHash,
            bytes32 externalCodeHash
        )
    {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, value)
            mcopy(add(ptr, 0x20), ptr, 0x20)
            copied := mload(add(ptr, 0x20))

            localSize := codesize()
            codecopy(add(ptr, 0x40), 0, localSize)
            localCodeHash := keccak256(add(ptr, 0x40), localSize)

            externalSize := extcodesize(account)
            extcodecopy(account, add(ptr, 0x40), 0, externalSize)
            externalCodeHash := keccak256(add(ptr, 0x40), externalSize)
            externalHash := extcodehash(account)
        }
    }

    function calls(address target, bytes calldata payload)
        external
        payable
        returns (
            bool callOk,
            bool callcodeOk,
            bool delegateOk,
            bool staticOk,
            bytes32 returnHash
        )
    {
        assembly {
            let ptr := mload(0x40)
            callOk := call(
                gas(), target, callvalue(), payload.offset, payload.length, ptr, 0x20
            )
            callcodeOk := callcode(
                gas(), target, 0, payload.offset, payload.length, ptr, 0x20
            )
            delegateOk := delegatecall(
                gas(), target, payload.offset, payload.length, ptr, 0x20
            )
            staticOk := staticcall(
                gas(), target, payload.offset, payload.length, ptr, 0x20
            )
            let size := returndatasize()
            returndatacopy(ptr, 0, size)
            returnHash := keccak256(ptr, size)
        }
    }

    function creates(bytes memory initCode, bytes32 salt)
        external
        payable
        returns (address first, address second)
    {
        assembly {
            let start := add(initCode, 0x20)
            let size := mload(initCode)
            first := create(callvalue(), start, size)
            second := create2(0, start, size, salt)
        }
    }

    function logs(bytes32 topic1, bytes32 topic2, bytes32 topic3, bytes32 topic4)
        external
    {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, caller())
            log0(ptr, 0x20)
            log1(ptr, 0x20, topic1)
            log2(ptr, 0x20, topic1, topic2)
            log3(ptr, 0x20, topic1, topic2, topic3)
            log4(ptr, 0x20, topic1, topic2, topic3, topic4)
        }
    }

    function terminate(uint256 mode, address payable beneficiary) external {
        assembly {
            switch mode
            case 0 { stop() }
            case 1 { selfdestruct(beneficiary) }
            default { invalid() }
        }
    }
}
