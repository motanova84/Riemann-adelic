// SPDX-License-Identifier: CC-BY-NC-SA-4.0
pragma solidity ^0.8.20;

/**
 * @title AIKBeaconsProofOfMath
 * @author José Manuel Mota Burruezo Ψ ✧ ∞³
 * @notice Smart contract for AIK Beacons - Proof of Mathematical Truth NFTs
 * @dev Deployed on Base Mainnet for immutable mathematical proof certification
 * 
 * This contract enables:
 * - Minting NFTs only when a mathematical proof is valid
 * - On-chain verification of beacon hashes and IPFS CIDs
 * - Offline verification capability via beacon hash lookup
 * 
 * Integration with QCAL Framework:
 * - Base frequency: f0 = 141.7001 Hz
 * - Coherence constant: C = 244.36
 * - DOI: 10.5281/zenodo.17379721
 */

import "@openzeppelin/contracts/token/ERC721/ERC721.sol";
import "@openzeppelin/contracts/token/ERC721/extensions/ERC721URIStorage.sol";
import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/cryptography/ECDSA.sol";
import "@openzeppelin/contracts/utils/cryptography/MessageHashUtils.sol";

contract AIKBeaconsProofOfMath is ERC721, ERC721URIStorage, Ownable {
    using ECDSA for bytes32;
    using MessageHashUtils for bytes32;

    /// @notice Contract name constant
    string public constant NAME = "AIK Beacons - Proof of Mathematical Truth";
    
    /// @notice Contract symbol constant
    string public constant SYMBOL = unicode"AIK∞³";

    /// @notice QCAL base frequency in millihertz (141.7001 Hz = 141700100 mHz)
    uint256 public constant F0_MILLIHERTZ = 141700100;

    /// @notice Mapping from token ID to beacon SHA3-256 hash
    mapping(uint256 => bytes32) public beaconHash;
    
    /// @notice Mapping from token ID to IPFS CID
    mapping(uint256 => string) public beaconCID;
    
    /// @notice Mapping from token ID to proof validity status
    mapping(uint256 => bool) public isValidProof;
    
    /// @notice Mapping from token ID to theorem statement
    mapping(uint256 => string) public theoremStatement;
    
    /// @notice Mapping from beacon hash to token ID for reverse lookup
    mapping(bytes32 => uint256) public hashToTokenId;
    
    /// @notice Mapping to track if a beacon hash has been minted
    mapping(bytes32 => bool) public isMinted;

    /// @notice Current total supply of tokens
    uint256 public totalSupply;
    
    /// @notice Authorized signer address for proof verification
    address public authorizedSigner;

    /// @notice Event emitted when a new beacon NFT is minted
    /// @param tokenId The ID of the newly minted token
    /// @param beaconHash The SHA3-256 hash of the beacon
    /// @param theorem The theorem statement
    /// @param ipfsCid The IPFS CID of the beacon JSON
    event BeaconMinted(
        uint256 indexed tokenId,
        bytes32 beaconHash,
        string theorem,
        string ipfsCid
    );

    /// @notice Event emitted when the authorized signer is updated
    /// @param oldSigner The previous authorized signer
    /// @param newSigner The new authorized signer
    event SignerUpdated(address indexed oldSigner, address indexed newSigner);

    /// @notice Error for invalid IPFS CID
    error InvalidCID();
    
    /// @notice Error for invalid signature
    error InvalidSignature();
    
    /// @notice Error for hash mismatch
    error HashMismatch();
    
    /// @notice Error for already minted beacon
    error AlreadyMinted();
    
    /// @notice Error for empty theorem
    error EmptyTheorem();

    /**
     * @notice Constructor initializes the contract with owner and signer
     * @param initialOwner The initial owner of the contract
     * @param initialSigner The initial authorized signer for proof verification
     */
    constructor(
        address initialOwner,
        address initialSigner
    ) ERC721("AIK Beacons - Proof of Mathematical Truth", unicode"AIK∞³") Ownable(initialOwner) {
        authorizedSigner = initialSigner;
    }

    /**
     * @notice Mint a new beacon NFT if the proof is valid
     * @param theorem The theorem statement being certified
     * @param proofFileCID The IPFS CID of the formal proof file
     * @param ipfsCid The IPFS CID of the beacon JSON
     * @param expectedBeaconHash The expected SHA3-256 hash of the beacon
     * @param signature ECDSA signature from the authorized signer
     * @return tokenId The ID of the newly minted token
     */
    function mintIfValidProof(
        string memory theorem,
        string memory proofFileCID,
        string memory ipfsCid,
        bytes32 expectedBeaconHash,
        bytes calldata signature
    ) external returns (uint256 tokenId) {
        // 1. Validate inputs
        if (bytes(ipfsCid).length == 0) revert InvalidCID();
        if (bytes(theorem).length == 0) revert EmptyTheorem();
        if (isMinted[expectedBeaconHash]) revert AlreadyMinted();

        // 2. Verify the ECDSA signature from the authorized signer
        bytes32 messageHash = keccak256(
            abi.encodePacked(theorem, proofFileCID, ipfsCid, expectedBeaconHash)
        );
        bytes32 ethSignedHash = messageHash.toEthSignedMessageHash();
        address signer = ethSignedHash.recover(signature);
        if (signer != authorizedSigner) revert InvalidSignature();

        // 3. Mint the token
        tokenId = totalSupply;
        totalSupply++;

        beaconHash[tokenId] = expectedBeaconHash;
        beaconCID[tokenId] = ipfsCid;
        theoremStatement[tokenId] = theorem;
        isValidProof[tokenId] = true;
        hashToTokenId[expectedBeaconHash] = tokenId;
        isMinted[expectedBeaconHash] = true;

        _safeMint(msg.sender, tokenId);
        _setTokenURI(tokenId, string(abi.encodePacked("ipfs://", ipfsCid)));

        emit BeaconMinted(tokenId, expectedBeaconHash, theorem, ipfsCid);

        return tokenId;
    }

    /**
     * @notice Verify if a token ID represents a valid proof (offline verification)
     * @param tokenId The token ID to verify
     * @return isValid True if the token represents a valid proof
     */
    function verifyOffline(uint256 tokenId) public view returns (bool isValid) {
        return isValidProof[tokenId];
    }

    /**
     * @notice Verify a proof by its beacon hash
     * @param hash The beacon hash to verify
     * @return isValid True if a valid proof exists with this hash
     * @return tokenId The token ID if found (0 if not found)
     */
    function verifyByHash(bytes32 hash) public view returns (bool isValid, uint256 tokenId) {
        if (!isMinted[hash]) {
            return (false, 0);
        }
        tokenId = hashToTokenId[hash];
        isValid = isValidProof[tokenId];
        return (isValid, tokenId);
    }

    /**
     * @notice Get complete beacon information for a token
     * @param tokenId The token ID to query
     * @return hash The beacon hash
     * @return cid The IPFS CID
     * @return theorem The theorem statement
     * @return valid Whether the proof is valid
     */
    function getBeaconInfo(uint256 tokenId) public view returns (
        bytes32 hash,
        string memory cid,
        string memory theorem,
        bool valid
    ) {
        require(tokenId < totalSupply, "Token does not exist");
        return (
            beaconHash[tokenId],
            beaconCID[tokenId],
            theoremStatement[tokenId],
            isValidProof[tokenId]
        );
    }

    /**
     * @notice Update the authorized signer address (only owner)
     * @param newSigner The new authorized signer address
     */
    function setAuthorizedSigner(address newSigner) external onlyOwner {
        require(newSigner != address(0), "Invalid signer address");
        address oldSigner = authorizedSigner;
        authorizedSigner = newSigner;
        emit SignerUpdated(oldSigner, newSigner);
    }

    /**
     * @notice Get the QCAL base frequency
     * @return frequency The base frequency in millihertz
     */
    function getQCALFrequency() external pure returns (uint256 frequency) {
        return F0_MILLIHERTZ;
    }

    // Required overrides for ERC721URIStorage

    function tokenURI(uint256 tokenId)
        public
        view
        override(ERC721, ERC721URIStorage)
        returns (string memory)
    {
        return super.tokenURI(tokenId);
    }

    function supportsInterface(bytes4 interfaceId)
        public
        view
        override(ERC721, ERC721URIStorage)
        returns (bool)
    {
        return super.supportsInterface(interfaceId);
    }
}
