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
    // ERC20 Storage
    balanceOf(address) returns uint256 envfree
    allowance(address, address) returns uint256 envfree
    totalSupply() returns uint256 envfree
}

/// transfer must revert if the caller has an insufficient balance
rule transferRevertsOnInsufficientBalance() {
    env e;
    uint256 callerBalance = balanceOf(e.msg.sender);
    
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

/// @dev transferFrom "Cannot overflow because the sum of all user balances can't exceed the max uint256 value."
rule noFeeOnTransferFrom(address alice, address bob, uint256 amount) {
    env e;
    calldataarg args;
    require alice != bob;
    require allowance(alice, e.msg.sender) >= amount;
    uint256 balanceBefore = balanceOf(bob);

    transferFrom(e, alice, bob, amount);

    uint256 balanceAfter = balanceOf(bob);
    assert balanceAfter == balanceBefore + amount,
        "calls to transferFrom must not collect a fee";
}

/// @dev transfer "Cannot overflow because the sum of all user balances can't exceed the max uint256 value."
rule noFeeOnTransfer(address bob, uint256 amount) {
    env e;
    calldataarg args;
    require bob != e.msg.sender;
    uint256 balanceSenderBefore = balanceOf(e.msg.sender);
    uint256 balanceBefore = balanceOf(bob);

    transfer(e, bob, amount);

    uint256 balanceAfter = balanceOf(bob);
    uint256 balanceSenderAfter = balanceOf(e.msg.sender);
    assert balanceAfter == balanceBefore + amount,
        "calls to transfer must not collect a fee";
}

rule transferCorrect(address to, uint256 amount) {
    env e;
    require e.msg.value == 0 && e.msg.sender != 0 && e.msg.sender != currentContract;
    uint256 fromBalanceBefore = balanceOf(e.msg.sender);
    uint256 toBalanceBefore = balanceOf(to);
    require fromBalanceBefore + toBalanceBefore <= max_uint256;

    transfer@withrevert(e, to, amount);
    bool reverted = lastReverted;
    if (!reverted) {
        if (e.msg.sender == to) {
            assert balanceOf(e.msg.sender) == fromBalanceBefore,
                "the balance of the recipient must not change if they are the message sender";
        } else {
            assert balanceOf(e.msg.sender) == fromBalanceBefore - amount,
                "the balance of the message sender must decrease by the amount if they are not the recipient";
            assert balanceOf(to) == toBalanceBefore + amount,
                "the balance of the recipient must increase by the amount if they are not the message sender";
        }
    } else {
        assert amount > fromBalanceBefore || to == 0,
            "transfer must only revert if the recipient is address 0 or the amount exceeds the sender's prior balance";
    }
}

rule transferFromCorrect(address from, address to, uint256 amount) {
    env e;
    require e.msg.value == 0;
    uint256 fromBalanceBefore = balanceOf(from);
    uint256 toBalanceBefore = balanceOf(to);
    uint256 allowanceBefore = allowance(from, e.msg.sender);
    require fromBalanceBefore + toBalanceBefore <= max_uint256;

    transferFrom(e, from, to, amount);

    assert from != to =>
        balanceOf(from) == fromBalanceBefore - amount &&
        balanceOf(to) == toBalanceBefore + amount &&
        allowance(from, e.msg.sender) == allowanceBefore - amount,
            "if the source and recipient are different, the associated balances and allowance must change correctly";
}

rule transferFromReverts(address from, address to, uint256 amount) {
    env e;
    uint256 allowanceBefore = allowance(from, e.msg.sender);
    uint256 fromBalanceBefore = balanceOf(from);
    require from != 0 && e.msg.sender != 0;
    require e.msg.value == 0;
    require fromBalanceBefore + balanceOf(to) <= max_uint256;

    transferFrom@withrevert(e, from, to, amount);

    assert lastReverted <=> (allowanceBefore < amount || amount > fromBalanceBefore || to == 0),
        "transferFrom must revert iff the recipient is address 0 or the amount exceeds the needed balance or allowance";
}

/// The zero address must always have a balance of 0
invariant ZeroAddressNoBalance()
    balanceOf(0) == 0

rule NoChangeTotalSupply(method f) {
    // require f.selector != burn(uint256).selector && f.selector != mint(address, uint256).selector;
    uint256 totalSupplyBefore = totalSupply();
    env e;
    calldataarg args;
    f(e, args);
    assert totalSupply() == totalSupplyBefore,
        "method calls must not alter the total supply";
}

rule noBurningTokens(method f) {
    uint256 totalSupplyBefore = totalSupply();
    env e;
    calldataarg args;
    f(e, args);
    assert totalSupply() >= totalSupplyBefore,
        "method calls must not decrease the total supply";
}

rule noMintingTokens(method f) {
    uint256 totalSupplyBefore = totalSupply();
    env e;
    calldataarg args;
    f(e, args);
    assert totalSupply() <= totalSupplyBefore,
        "method calls must not increase the total supply";
}

rule ChangingAllowance(method f, address from, address spender) {
    uint256 allowanceBefore = allowance(from, spender);
    env e;
    if (f.selector == approve(address, uint256).selector) {
        address spender_;
        uint256 amount;
        approve(e, spender_, amount);
        if (from == e.msg.sender && spender == spender_) {
            assert allowance(from, spender) == amount,
                "a proper call to approve must update a spender's allowance";
        } else {
            assert allowance(from, spender) == allowanceBefore,
                "an improper call to approve must leave a spender's allowance unchanged";
        }
    } else if (f.selector == transferFrom(address,address,uint256).selector) {
        address from_;
        address to;
        address amount;
        transferFrom(e, from_, to, amount);
        uint256 allowanceAfter = allowance(from, spender);
        if (from == from_ && spender == e.msg.sender) {
            assert from == to || allowanceBefore == max_uint256 || allowanceAfter == allowanceBefore - amount,
                "given a spender's allowance for an account, if that spender calls transferFrom drawing from that account, \
                either the allowance must drop by the amount, the source and recipient must be the same, or the prior \
                allowance must be the largest possible value"; // this feels like an awkwardly constructed rule
        } else {
            assert allowance(from, spender) == allowanceBefore,
                "a transferFrom call must not change a spender's allowance for an account if either the account isn't the \
                source or the spender isn't the caller";
        }
    } else
    {
        calldataarg args;
        f(e, args);
        assert allowance(from, spender) == allowanceBefore,
            "method calls other than approve or transferFrom must not change a spender's allowance for an account";
    }
}

rule TransferSumOfFromAndToBalancesStaySame(address to, uint256 amount) {
    env e;
    mathint sum = balanceOf(e.msg.sender) + balanceOf(to);
    require sum < max_uint256;
    transfer(e, to, amount); 
    assert balanceOf(e.msg.sender) + balanceOf(to) == sum,
        "a call to transfer must not change the sum of the source and recipient balances";
}

rule TransferFromSumOfFromAndToBalancesStaySame(address from, address to, uint256 amount) {
    env e;
    mathint sum = balanceOf(from) + balanceOf(to);
    require sum < max_uint256;
    transferFrom(e, from, to, amount); 
    assert balanceOf(from) + balanceOf(to) == sum,
        "a call to transferFrom must not change the sum of the source and recipient balances";
}

rule TransferDoesntChangeOtherBalance(address to, uint256 amount, address other) {
    env e;
    require other != e.msg.sender;
    require other != to && other != currentContract;
    uint256 balanceBefore = balanceOf(other);
    transfer(e, to, amount); 
    assert balanceBefore == balanceOf(other),
        "a call to transfer must not change the balance of an address not involved in the transaction";
}

rule TransferFromDoesntChangeOtherBalance(address from, address to, uint256 amount, address other) {
    env e;
    require other != from;
    require other != to;
    uint256 balanceBefore = balanceOf(other);
    transferFrom(e, from, to, amount); 
    assert balanceBefore == balanceOf(other),
        "a call to transferFrom must not change the balance of an address not involved in the transaction";
}

rule OtherBalanceOnlyGoesUp(address other, method f) {
    env e;
    require other != currentContract;
    uint256 balanceBefore = balanceOf(other);

    if (f.selector == transferFrom(address, address, uint256).selector) {
        address from;
        address to;
        uint256 amount;
        require(other != from);
        require balanceOf(from) + balanceBefore < max_uint256;
        transferFrom(e, from, to, amount);
    } else if (f.selector == transfer(address, uint256).selector) {
        require other != e.msg.sender;
        require balanceOf(e.msg.sender) + balanceBefore < max_uint256;
        calldataarg args;
        f(e, args);
    } else {
        require other != e.msg.sender;
        calldataarg args;
        f(e, args);
    }

    assert balanceOf(other) >= balanceBefore,
        "the balance of an address must not decrease if the address is neither the source for a transferFrom call nor the caller of any other method";
}

rule isMintPrivileged(address privileged, address recipient, uint256 amount) {
    env e1;
	require e1.msg.sender == privileged;

	storage initialStorage = lastStorage;
    uint256 totalSupplyBefore = totalSupply();
	mint(e1, recipient, amount); // no revert
	uint256 totalSupplyAfter1 = totalSupply();
    require(totalSupplyAfter1 > totalSupplyBefore);

	env e2;
	require e2.msg.sender != privileged;
	mint@withrevert(e2, recipient, amount) at initialStorage;
	bool secondSucceeded = !lastReverted;
    uint256 totalSupplyAfter2 = totalSupply();

    // either non privileged mint reverted or it didn't influence total supply
	assert  !secondSucceeded || (totalSupplyBefore == totalSupplyAfter2),
        "only a single address may mint tokens to increase supply";
}
