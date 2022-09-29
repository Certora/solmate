methods {
    name() returns string envfree;
    symbol() returns string envfree;
    ownerOf(uint256) returns address envfree;
    balanceOf(address) returns uint256 envfree;
    getApproved(uint256) returns address;
    isApprovedForAll(address,address) returns bool;
    approve(address,uint256);
    setApprovalForAll(address,bool);
    transferFrom(address,address,uint256);
    safeTransferFrom(address,address,uint256);
    safeTransferFrom(address,address,uint256,bytes);
    supportsInterface(bytes4) returns bool;
    mint(address,uint256);
    burn(uint256);
    safeMint(address,uint256);
    safeMint(address,uint256,bytes);
    tokenURI(uint256) returns string;
}

//// # Unit Test Rules /////////////////////////////////////////////////////////

rule balanceOfRevertsForZeroAddress {
    address zeroAddress;
    require zeroAddress == 0;
    balanceOf@withrevert(zeroAddress);

    assert lastReverted,
        "calls to balanceOf must revert if passed address zero";
}

/// @dev this rule is definitely not working yet
rule ownerOfRevertsForZeroOwnedToken {
    uint256 tokenId; 
    // require ownerOf(tokenId) == 0; // rewrite require as `=>` ?
    address owner = ownerOf(tokenId);
    // require owner == 0;
    // ownerOf@withrevert(tokenId);
    // assert owner == 0 => lastReverted,
    assert owner != 0,
        "calls to ownerOf must revert if passed address zero";
}

/// @notice Transfers the ownership of an NFT from one address to another address

/// @param _from The current owner of the NFT
/// @param _to The new owner
/// @param _tokenId The NFT to transfer
/// @param data Additional data with no specified format, sent in call to `_to`

rule safeTransferFromReverts {
/// @dev Throws unless `msg.sender` is the current owner, an authorized
///  operator, or the approved address for this NFT. 
// X if msg.sender != owner && 
// msg.sender is not authorized && 
// msg.sender is not approved address for NFT
//         => revert
// X if it didn't revert, one of the 3 good things happened
// X if none of good things happened => reverts
//        if !(msg.sender == owner || msg.sender is authorized || msg.sender is approved)
//                 => reverts
///  Throws if `_from` is not the current owner. 
// from != owner => revert
///  Throws if `_to` is the zero address. 
// to == 0 => revert
///  Throws if `_tokenId` is not a valid NFT. 
///  When transfer is complete, this function
///  checks if `_to` is a smart contract (code size > 0). 
///  If so, it calls `onERC721Received` on `_to` and throws if the return value is not
///  `bytes4(keccak256("onERC721Received(address,address,uint256,bytes)"))`.   
// 3 cases for above:
// code = 0 (not a smart contract) [experiment with how tool deals with code size for arbitrary address]
// code > 0 and does the right thing 
// code > 0 and does not do the right thing
// [two above need a contract that does right thing and contract that does not do right thing]
// [or one contract with toggle to do / not do right]
// [first check if calls `onERC721Received` on `_to`]
// [next check if return is correct]
/// write this rule for safeTransferFrom with data, then prove the 2 safeTransferFroms are equivalent
}

rule safeTransferFromReverts2{
    env e; uint256 tokenId;
    address owner; require ownerOf(tokenId) == owner;
    address authorized; require getApproved(tokenId) == 
    address nftAddress;
    address from; address to; 

    safeTransferFrom@withrevert(e, from, to, tokenId);

    assert (e.msg.sender != owner && from != owner) => lastReverted,
        "calls to safeTransferFrom must revert for an inappropriate caller";
}



//// # Utility Rules ///////////////////////////////////////////////////////////

/// This rule should always fail.
rule sanity {
    method f; env e; calldataarg args;

    f(e, args);

    assert false, 
        "this rule should always fail";
}