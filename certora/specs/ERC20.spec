methods {
    // ERC20 Logic
    approve(address, uint256) returns bool
    transfer(address, uint256) returns bool
    transferFrom(address, address, uint256) returns bool
    // EIP-2612 Logic
    permit(address, address, uint256, uint256, uint8, bytes32, bytes32)
    DOMAIN_SEPARATOR() returns bytes32
    computeDomainSeparator() returns bytes32
    // Harness Methods
    mint(address, uint) 
    burn(address, uint)
}

/// transfer must revert if the caller has an insufficient balance
rule transferRevertsOnInsufficientBalance() {
    env e;
    uint256 callerBalance = balanceOf(e, e.msg.sender);
    
    uint256 amount;
    transfer@withrevert(e, _, amount);

    assert callerBalance < amount => lastReverted, 
        "tranfer must revert if the caller's balance is less than the amount";
}

/// This rule should always fail.
rule sanity {
    method f; env e; calldataarg args;

    f(e, args);

    assert false, 
        "This rule should always fail";
}