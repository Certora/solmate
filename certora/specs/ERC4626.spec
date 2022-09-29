// import "../helpers/erc20.spec"



methods {
    name() returns string envfree;
    symbol() returns string envfree;
    decimals() returns uint8 envfree;
    asset() returns address envfree;

    totalSupply() returns uint256 envfree;
    balanceOf(address) returns uint256 envfree => DISPATCHER(true);
    nonces(address) returns uint256 envfree;

    approve(address,uint256) returns bool;
    transfer(address,uint256) returns bool => DISPATCHER(true);
    transferFrom(address,address,uint256) returns bool => DISPATCHER(true);
    deposit(uint256,address);
    mint(uint256,address);
    withdraw(uint256,address,address);
    redeem(uint256,address,address);

    totalAssets() returns uint256 envfree;
    userAssets(address) returns uint256 envfree;
    convertToShares(uint256) returns uint256 envfree;
    convertToAssets(uint256) returns uint256 envfree;
    previewDeposit(uint256) returns uint256 envfree;
    previewMint(uint256) returns uint256 envfree;
    previewWithdraw(uint256) returns uint256 envfree;
    previewRedeem(uint256) returns uint256 envfree;

    maxDeposit(address) returns uint256 envfree;
    maxMint(address) returns uint256 envfree;
    maxWithdraw(address) returns uint256 envfree;
    maxRedeem(address) returns uint256 envfree;

    permit(address,address,uint256,uint256,uint8,bytes32,bytes32);
    DOMAIN_SEPARATOR() returns bytes32;
}

//// # Stakeholder Logic ///////////////////////////////////////////////////////

// ********************* Permissions ************************************************************************************

// Only I/approved should be able to remove any of the assets/shares I have in the vault

// No one should be able to take out more than they have in the vault

// ********************* Risks to user ************************************************************************************

// No one should contribute assets to the vault without receiving shares

// bank can't rob you of shares

// rule userAssetsSharesInverseInputOutput(method f) 
// filtered {
//     f -> f.selector == deposit(uint256,address).selector
//       || f.selector == mint(uint256,address).selector
//       || f.selector == withdraw(uint256,address,address).selector
//       || f.selector == redeem(uint256,address,address).selector
// }
// {
//     address user; env e;
//     require user != currentContract; require user == e.msg.sender;
//     uint256 userAssetsBefore = userAssets(user); uint256 userSharesBefore = balanceOf(user);

//     calldataarg args;
//     f(e, args);

//     uint256 userAssetsAfter = userAssets(user); uint256 userSharesAfter = balanceOf(user);

//     assert userAssetsBefore > userAssetsAfter <=> userSharesBefore < userSharesAfter,
//         "a user's underlying asset balance must decrease on vault IO if and only if their vault token balance increases";
//     assert userAssetsBefore < userAssetsAfter <=> userSharesBefore > userSharesAfter,
//         "a user's underlying asset balance must increase on vault IO if and only if their vault token balance decreases";
// }

/*

// rule depositingProducesShares() {
rule mintingProducesShares() {
    env e; uint256 assets; uint256 shares;
    address contributor; require contributor == e.msg.sender;
    address receiver;
    require currentContract != contributor
         && currentContract != receiver
         && currentContract != asset();

    requireInvariant sumOfBalancePairsBounded(contributor, receiver);
    requireInvariant vaultSolvency();
    require previewDeposit(assets) + balanceOf(receiver) <= max_uint256; // safe assumption because call to _mint will revert if totalSupply += amount overflows
    require shares + balanceOf(receiver) <= max_uint256; // same as above

    uint256 contributorAssetsBefore = userAssets(contributor);
    uint256 receiverSharesBefore = balanceOf(receiver);

    // deposit(e, assets, receiver); // working with deposit? yes
    mint(e, shares, receiver); // working with mint? yes

    uint256 contributorAssetsAfter = userAssets(contributor);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert contributorAssetsBefore > contributorAssetsAfter <=> receiverSharesBefore < receiverSharesAfter,
        "a contributor's assets must decrease if and only if the receiver's shares increase";
} // generalize as contributingProducesShares w function contribute

*/

rule contributingProducesShares(method f)
filtered {
    f -> f.selector == deposit(uint256,address).selector
      || f.selector == mint(uint256,address).selector
}
{
    env e; uint256 assets; uint256 shares;
    address contributor; require contributor == e.msg.sender;
    address receiver;
    require currentContract != contributor
         && currentContract != receiver
         && currentContract != asset();

    requireInvariant sumOfBalancePairsBounded(contributor, receiver);
    requireInvariant vaultSolvency();
    require previewDeposit(assets) + balanceOf(receiver) <= max_uint256; // safe assumption because call to _mint will revert if totalSupply += amount overflows
    require shares + balanceOf(receiver) <= max_uint256; // same as above

    uint256 contributorAssetsBefore = userAssets(contributor);
    uint256 receiverSharesBefore = balanceOf(receiver);

    callContributionMethods(e, f, assets, shares, receiver);

    uint256 contributorAssetsAfter = userAssets(contributor);
    uint256 receiverSharesAfter = balanceOf(receiver);

    assert contributorAssetsBefore > contributorAssetsAfter <=> receiverSharesBefore < receiverSharesAfter,
        "a contributor's assets must decrease if and only if the receiver's shares increase";
}


function callContributionMethods(env e, method f, uint256 assets, uint256 shares, address receiver) {
    if (f.selector == deposit(uint256,address).selector) {

        deposit(e, assets, receiver);
        // return;
    }
    if (f.selector == mint(uint256,address).selector) {

        mint(e, shares, receiver);
        // return;
    }
} // file bug report on weird java error when returns are present, works when returns commented out


invariant vaultSolvency()
    totalAssets() >= convertToAssets(totalSupply()) && 
    convertToShares(totalAssets()) >= totalSupply()

invariant vaultSolvencyAssets()
    totalAssets() >= convertToAssets(totalSupply())
    {
        preserved {
            requireInvariant vaultSolvencyShares();
        }
    }

invariant vaultSolvencyShares()
    convertToShares(totalAssets()) >= totalSupply()
    {
        preserved {
            requireInvariant vaultSolvencyAssets();
        }
    }

ghost uint256 sumOfBalances {
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalances = sumOfBalances + newValue - oldValue;
}

invariant totalSupplyIsSumOfBalances()
    totalSupply() == sumOfBalances


invariant sumOfBalancePairsBounded(address addy1, address addy2)
    addy1 != addy2 => balanceOf(addy1) + balanceOf(addy2) <= totalSupply()
    // balanceOf(addy1) + balanceOf(addy2) <= totalSupply()
    {
        preserved {
            // because totalSupplyIsSumOfBalances is proven, the sum of any distinct two must be less than totalSupply
            require false; // this feels more honest than pretending
        }
    }

/*
invariant convertToAssetsAdditivity(uint256 sharesA, uint256 sharesB)
    convertToAssets(sharesA) + convertToAssets(sharesB) == convertToAssets(sharesA + sharesB)
    {
        preserved {
            require to_mathint(sharesA) + to_mathint(sharesB) < max_uint128
                 && to_mathint(convertToAssets(sharesA)) + to_mathint(convertToAssets(sharesB)) < max_uint256
                 && to_mathint(convertToAssets(sharesA + sharesB)) < max_uint256;
        }
    }
*/

// invariant totalAssetsIsSumOfAssets()
//     totalAssets() == convertToAssets(sumOfBalances) // Nick says changing == to >= will make this my solvency invariant

/*
invariant convertToSharesAdditivity(mathint assetsA, mathint assetsB)
    convertToShares(to_uint256(assetsA)) + convertToShares(to_uint256(assetsB)) == convertToShares(to_uint256(assetsA + assetsB))
*/

// preserved transferFrom(address x, address y, uint256 amount) with (env e) {
//     require e.msg.sender != currentContract;
//     requireInvariant totalSupplyIsSumOfBalances();
//     requireInvariant sumOfBalancePairsBounded(x, y);
// }

//// # State Change Logic //////////////////////////////////////////////////////

// rounding direction in transactions should always favor vault

// No one should trade in shares without receiving assets in return

// ********************* Risks to vault ************************************************************************************

// Bank No one should receive shares without contributing assets to the vault (account for staking etc.)
// assert total supply increase <=> total assets increase

// Bank (!!!) No one should be able to remove assets from the vault without trading in shares
/*
rule assetsSupplyChangeTogether {
    assert false,
    // assert (totalSupplyBefore < totalSupplyAfter <=> totalAssetsBefore < totalAssetsAfter)
    //     && (totalSupplyBefore > totalSupplyAfter <=> totalAssetsBefore > totalAssetsAfter),
        "increases and decreases in totalSupply must occur with corresponding increases and decreases in totalAssets";
}

// Bank Assets (totalAssets or balanceOf(contract address)) must equal or exceed liabilities (totalSupply)
*/

/// This rule should always fail.
rule sanity {
    method f; env e; calldataarg args;

    f(e, args);

    assert false, 
        "This rule should always fail";
}


// (1) start with solvency
// also prevents getting out assets without redeeming shares

// (2) if you redeem shares you get back assets

// (3) if you deposit assets, you should get shares

// (4) independence only I / authorized can change my balances

// (5) list of state change rules

// no assets iff no supply

/*
//// # invariants //////////////////////////////////////////////////////////////

/// totalSupply and sumOfBalances

//// # method equivalence //////////////////////////////////////////////////////

/// A contribution with a given value must yield the same result whether done via deposit or mint.
rule depositWithdrawEquivalence {
    assert false,
        "TODO";
} // add inequality consideration

/// A removal with a given value must yield the same result whether done via withdraw or redeem.
rule withdrawRedeemEquivalence {
    assert false,
        "TODO";
} // add inequality consideration

//// # conversion integrity ////////////////////////////////////////////////////

/// An assets to shares to assets calculation must return the largest possible assets <= original assets.
rule assetsSharesAssetsConversionIntegrity {
    assert false,
        "TODO";
} // check direction

/// A shares to assets to shares calculation must return the largest possible shares <= original shares but not too <.
rule sharesAssetsSharesConversionIntegrity {
    assert false,
        "TODO";
} // check direction

//// # convertTo_____ previewFunction //////////////////////////////////////////

/// relationship between convertToShares and previewDeposit

/// relationship between convertToAssets and previewMint

/// relationship between convertToShares and previewWithdraw

/// relationship between convertToAssets and previewRedeem



//// # function previewFunction ////////////////////////////////////////////////

/// relationship between deposit and previewDeposit
/// A call to deposit must return the smallest value >= previewDeposit's return when called in the same transaction.
rule depositPreviewDepositRelationship {
    assert false,
        "TODO";    
}

/// relationship between mint and previewMint
/// A call to mint must return the largest value <= previewMint's return when called in the same transaction.
rule mintPreviewMintRelationship {
    assert false,
        "TODO";    
}

/// relationship between withdraw and previewWithdraw
/// A call to withdraw must return the largest value <= previewWithdraw's return when called in the same transaction.
rule withdrawPreviewWithdrawRelationship {
    assert false,
        "TODO";    
}

/// relationship between redeem and previewRedeem
/// A call to redeem must return the smallest value >= previewRedeem's return when called in the same transaction.
rule redeemPreviewRedeemRelationship {
    assert false,
        "TODO";    
}

//// # function maxFunction ////////////////////////////////////////////////////

/// relationship between deposit and maxDeposit
/// A maxDeposit calculation must return the largest value <= the largest deposit that would not revert
rule depositMaxDepositRelationship {
    assert false,
        "TODO";    
}

/// relationship between mint and maxMint
/// A maxMint calculation must return the largest value <= the largest mint that would not revert
rule mintMaxMintRelationship {
    assert false,
        "TODO";    
}

/// relationship between withdraw and maxWithdraw
/// A maxWithdraw calculation must return the largest value <= the largest withdraw that would not revert
rule withdrawMaxWithdrawRelationship {
    assert false,
        "TODO";    
}

/// relationship between redeem and maxRedeem
/// A maxRedeem calculation must return the largest value <= the largest redeem that would not revert
rule redeemMaxRedeemRelationship {
    assert false,
        "TODO";    
}
*/