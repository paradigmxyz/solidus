// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

type Price is uint128;

library PriceMath {
    function saturatingAdd(Price left, Price right)
        internal
        pure
        returns (Price)
    {
        uint256 sum = uint256(Price.unwrap(left)) + Price.unwrap(right);
        if (sum > type(uint128).max) return Price.wrap(type(uint128).max);
        return Price.wrap(uint128(sum));
    }
}

interface IAdvancedTypeTarget {
    function consume(bytes32 key, uint256 value) external returns (bytes32);
}

abstract contract AccumulatorBase {
    function adjust(uint256 value) public pure virtual returns (uint256) {
        return value + 1;
    }
}

/// @notice Exercises optimized-Yul patterns produced by advanced Solidity
/// types, nested storage, calldata slices, ABI codecs, and precompile calls.
contract AdvancedTypeSurfaceBox is AccumulatorBase {
    using PriceMath for Price;

    enum Mode {
        Add,
        Multiply,
        Hash
    }

    struct Record {
        Price price;
        uint64 nonce;
        bytes32 digest;
    }

    mapping(address owner => mapping(bytes32 key => Record)) public records;

    event Recorded(
        address indexed owner,
        bytes32 indexed key,
        uint128 price,
        uint64 nonce
    );

    function adjust(uint256 value)
        public
        pure
        override
        returns (uint256)
    {
        return super.adjust(value) * 3;
    }

    function saturating(uint128 left, uint128 right)
        external
        pure
        returns (uint128)
    {
        return Price.unwrap(Price.wrap(left).saturatingAdd(Price.wrap(right)));
    }

    function modular(uint256 x, uint256 y, uint256 modulus)
        external
        pure
        returns (uint256 sum, uint256 product)
    {
        sum = addmod(x, y, modulus);
        product = mulmod(x, y, modulus);
    }

    function sliceHash(bytes calldata payload, uint256 start, uint256 end)
        external
        pure
        returns (bytes32)
    {
        return keccak256(payload[start:end]);
    }

    function codec(Record calldata input)
        external
        pure
        returns (uint128 price, uint64 nonce, bytes32 digest)
    {
        Record memory decoded = abi.decode(abi.encode(input), (Record));
        return (Price.unwrap(decoded.price), decoded.nonce, decoded.digest);
    }

    function hashPrecompiles(bytes calldata payload)
        external
        pure
        returns (bytes32 sha, bytes20 ripe)
    {
        sha = sha256(payload);
        ripe = ripemd160(payload);
    }

    function encodeTargetCall(bytes32 key, uint256 value)
        external
        pure
        returns (bytes memory)
    {
        return abi.encodeCall(IAdvancedTypeTarget.consume, (key, value));
    }

    function select(Mode mode, uint256 left, uint256 right)
        external
        pure
        returns (uint256)
    {
        if (mode == Mode.Add) return left + right;
        if (mode == Mode.Multiply) return left * right;
        return uint256(keccak256(abi.encodePacked(left, right)));
    }

    function writeRecord(bytes32 key, uint128 price, bytes32 digest)
        external
        returns (uint64 nonce)
    {
        Record storage record = records[msg.sender][key];
        nonce = record.nonce + 1;
        record.price = Price.wrap(price);
        record.nonce = nonce;
        record.digest = digest;
        emit Recorded(msg.sender, key, price, nonce);
    }

    function clearRecord(bytes32 key) external {
        delete records[msg.sender][key];
    }
}
