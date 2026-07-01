// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract PostCancunPrecompileBoundary {
    function callPrecompile(uint256 target, bytes memory input, uint256 outputSize)
        public
        view
        returns (bool ok, bytes memory output)
    {
        output = new bytes(outputSize);
        assembly ("memory-safe") {
            ok := staticcall(
                gas(),
                target,
                add(input, 0x20),
                mload(input),
                add(output, 0x20),
                outputSize
            )
        }
    }

    function blsG1Add(bytes memory input) public view returns (bool, bytes memory) {
        return callPrecompile(0x0b, input, 128);
    }

    function blsG1Msm(bytes memory input) public view returns (bool, bytes memory) {
        return callPrecompile(0x0c, input, 128);
    }

    function blsG2Add(bytes memory input) public view returns (bool, bytes memory) {
        return callPrecompile(0x0d, input, 256);
    }

    function blsG2Msm(bytes memory input) public view returns (bool, bytes memory) {
        return callPrecompile(0x0e, input, 256);
    }

    function blsPairing(bytes memory input) public view returns (bool, bytes memory) {
        return callPrecompile(0x0f, input, 32);
    }

    function blsMapFpToG1(bytes memory input) public view returns (bool, bytes memory) {
        return callPrecompile(0x10, input, 128);
    }

    function blsMapFp2ToG2(bytes memory input) public view returns (bool, bytes memory) {
        return callPrecompile(0x11, input, 256);
    }

    function p256Verify(bytes memory input) public view returns (bool, bytes memory) {
        return callPrecompile(0x100, input, 32);
    }
}
