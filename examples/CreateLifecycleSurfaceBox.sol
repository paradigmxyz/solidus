// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

contract CreateLifecycleChild {
    error BirthFailed(uint256 seed);

    event Born(uint256 indexed seed, uint256 value);

    uint256 public stored;

    constructor(uint256 seed, bool fail) payable {
        stored = seed;
        emit Born(seed, msg.value);
        if (fail) revert BirthFailed(seed);
    }
}

/// @notice Exercises recursive creation objects, constructor rollback, creation
/// revert data, value transfer, and CREATE2 collision behavior.
contract CreateLifecycleSurfaceBox {
    event Attempt(
        uint256 indexed seed,
        uint8 indexed kind,
        bool succeeded,
        bytes32 detail
    );

    function createSuccess(uint256 seed)
        external
        payable
        returns (
            bool childPresent,
            uint256 storedValue,
            uint256 childBalance,
            bytes32 readHash
        )
    {
        CreateLifecycleChild child =
            new CreateLifecycleChild{value: msg.value}(seed, false);
        (bool ok, bytes memory data) =
            address(child).staticcall(abi.encodeCall(child.stored, ()));
        require(ok);

        childPresent = address(child).code.length != 0;
        storedValue = abi.decode(data, (uint256));
        childBalance = address(child).balance;
        readHash = keccak256(data);
    }

    function createFailure(uint256 seed)
        external
        payable
        returns (
            bool failed,
            uint256 revertSize,
            bytes32 revertHash,
            uint256 retainedBalance
        )
    {
        bytes memory initCode = bytes.concat(
            type(CreateLifecycleChild).creationCode,
            abi.encode(seed, true)
        );
        assembly {
            let child := create(callvalue(), add(initCode, 0x20), mload(initCode))
            failed := iszero(child)
            revertSize := returndatasize()
            let ptr := mload(0x40)
            returndatacopy(ptr, 0, revertSize)
            revertHash := keccak256(ptr, revertSize)
        }
        retainedBalance = address(this).balance;
        emit Attempt(seed, 1, !failed, revertHash);
    }

    function create2Collision(uint256 seed, bytes32 salt)
        external
        returns (
            bool firstPresent,
            bool secondFailed,
            uint256 storedValue,
            bytes32 readHash
        )
    {
        CreateLifecycleChild first =
            new CreateLifecycleChild{salt: salt}(seed, false);
        bytes memory initCode = bytes.concat(
            type(CreateLifecycleChild).creationCode,
            abi.encode(seed, false)
        );
        address second;
        assembly {
            second := create2(0, add(initCode, 0x20), mload(initCode), salt)
        }

        (bool ok, bytes memory data) =
            address(first).staticcall(abi.encodeCall(first.stored, ()));
        require(ok);
        firstPresent = address(first).code.length != 0;
        secondFailed = second == address(0);
        storedValue = abi.decode(data, (uint256));
        readHash = keccak256(data);
        emit Attempt(seed, 2, !secondFailed, readHash);
    }

    function parentBalance() external view returns (uint256) {
        return address(this).balance;
    }
}
