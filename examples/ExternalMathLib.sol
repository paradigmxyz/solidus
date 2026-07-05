// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

library ExternalMathLib {
    function scaled(uint256 value) external pure returns (uint256) {
        return value * 3 + 1;
    }

    function mixed(uint256 a, uint256 b) public pure returns (uint256) {
        return a * b + (a ^ b);
    }
}

contract ExternalMathBox {
    function score(uint256 value) public pure returns (uint256) {
        return ExternalMathLib.scaled(value) + 7;
    }

    function blend(uint256 a, uint256 b) public pure returns (uint256) {
        return ExternalMathLib.mixed(a, b) + ExternalMathLib.scaled(a);
    }
}
