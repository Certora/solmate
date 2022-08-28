// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

import {ERC721} from "../../../src/tokens/ERC721.sol";

/// A dummy implementation for the ERC721 standard
/// This contract provides external mint and burn for everyone
contract DummyERC721 is ERC721 {
    constructor() ERC721("Dummy ERC721", "DERC721") {}

    function mint(address to, uint tokenId) external {
        _mint(to, tokenId);
    }

    function safeMint(address to, uint tokenId) external {
        _safeMint(to, tokenId);
    }
    function safeMint(address from, uint tokenId, bytes memory data) external {
        _safeMint(from, tokenId, data);
    }

    function burn(uint tokenId) external {
        _burn(tokenId);
    }

    function tokenURI(uint256) public view override returns (string memory) {
        return "";
    }
}
