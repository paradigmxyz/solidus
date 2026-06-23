// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

/// @notice Exercises high-level Solidity shapes that lower to nontrivial
/// optimized Yul control, object, and ABI machinery.
contract AbiControlSurfaceBox {
    struct Item {
        uint128 unsignedValue;
        int128 signedValue;
        bytes payload;
    }

    error LimitExceeded(uint256 value, uint256 limit);

    event Folded(address indexed caller, uint256 count, uint256 result);

    uint256 public immutable deploymentChain;

    constructor() {
        deploymentChain = block.chainid;
    }

    modifier below(uint256 value, uint256 limit) {
        if (value > limit) revert LimitExceeded(value, limit);
        _;
    }

    function recursive(uint256 value) public pure returns (uint256) {
        if (value == 0) return 1;
        return value * recursive(value - 1);
    }

    function control(uint256[] calldata values)
        external
        below(values.length, 64)
        returns (uint256 result)
    {
        for (uint256 i; i < values.length; ++i) {
            uint256 value = values[i];
            if (value == 0) continue;
            if (value == type(uint256).max) break;
            result ^= value * (i + 1);
        }
        emit Folded(msg.sender, values.length, result);
    }

    function nested(Item[] calldata items, bytes[] calldata blobs)
        external
        view
        returns (bytes32)
    {
        return keccak256(abi.encode(deploymentChain, msg.sender, items, blobs));
    }

    function indirect(uint256 value) external pure returns (uint256) {
        function(uint256) pure returns (uint256) operation = square;
        return operation(value);
    }

    function square(uint256 value) internal pure returns (uint256) {
        return value * value;
    }
}
