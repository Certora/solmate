// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

import {ERC20} from "../../../src/tokens/ERC20.sol";

/// A dummy implementation for the ERC20 standard
/// This contract provides external mint and burn for everyone
contract DummyERC20 is ERC20 {
    constructor() ERC20("Dummy ERC20", "DERC20", 18) {}

    function mint(address to, uint amount) external {
        _mint(to, amount);
    }

    function burn(address from, uint amount) external {
        _burn(from, amount);
    }
}
