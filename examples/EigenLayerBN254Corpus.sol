// SPDX-License-Identifier: MIT
pragma solidity ^0.8.27;

import {BN254} from "eigen/libraries/BN254.sol";

/// @notice Executes the real EigenLayer BN254 library through its precompiles.
contract EigenLayerBN254Corpus {
    using BN254 for BN254.G1Point;

    function generators()
        external
        pure
        returns (BN254.G1Point memory g1, BN254.G2Point memory g2)
    {
        return (BN254.generatorG1(), BN254.generatorG2());
    }

    function addGenerator()
        external
        view
        returns (BN254.G1Point memory)
    {
        BN254.G1Point memory generator = BN254.generatorG1();
        return generator.plus(generator);
    }

    function multiplyGenerator(uint256 scalar)
        external
        view
        returns (BN254.G1Point memory)
    {
        return BN254.generatorG1().scalar_mul(scalar);
    }

    function tinyMultiply(uint16 scalar)
        external
        view
        returns (BN254.G1Point memory)
    {
        return BN254.scalar_mul_tiny(BN254.generatorG1(), scalar);
    }

    function pairingIdentity() external view returns (bool) {
        BN254.G1Point memory generator = BN254.generatorG1();
        return BN254.pairing(
            generator,
            BN254.generatorG2(),
            generator.negate(),
            BN254.generatorG2()
        );
    }

    function safePairingIdentity(uint256 pairingGas)
        external
        view
        returns (bool precompileSucceeded, bool identityHolds)
    {
        BN254.G1Point memory generator = BN254.generatorG1();
        return BN254.safePairing(
            generator,
            BN254.generatorG2(),
            generator.negate(),
            BN254.generatorG2(),
            pairingGas
        );
    }

    function hashToPoint(bytes32 input)
        external
        view
        returns (BN254.G1Point memory)
    {
        return BN254.hashToG1(input);
    }

    function pointHashes()
        external
        pure
        returns (bytes32 g1Hash, bytes32 g2Hash)
    {
        return (
            BN254.hashG1Point(BN254.generatorG1()),
            BN254.hashG2Point(BN254.generatorG2())
        );
    }
}
