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



////////////////////////////////////////////////////////////////////////////////
//// # mathematical properties /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// weak monotonicity
// weak additivity
// epsilon error delta
// convertToAssets(a) + convertToAssets(b) is within epsilon of convertToAssets(a + b)
// current assets of system
// invariants when, how

//// # strong and weak monotonicity ////////////////////////////////////////////

rule depositStrongWeakMonotonicity() { // before simplifying to exclude token ratios, consider whether the improper behavior is a bug.
    env e; storage before = lastStorage;

    address receiver; uint256 receiverPriorBalance = balanceOf(receiver);
    uint256 smallerAssets; uint256 largerAssets;
    
    require currentContract != e.msg.sender
         && currentContract != receiver
         && currentContract != asset();

    requireInvariant sumOfBalancePairsBounded(e.msg.sender, receiver);
    requireInvariant vaultSolvency();

    deposit(e, smallerAssets, receiver) at before;
    uint256 smallerShares = balanceOf(receiver) - receiverPriorBalance;

    deposit(e, largerAssets, receiver) at before;
    uint256 largerShares = balanceOf(receiver) - receiverPriorBalance;

    if (totalSupply() > totalAssets()) {
        // weakly monotonic behavior when supply tokens outnumber asset tokens
        assert smallerAssets < largerAssets => smallerShares <= largerShares,
            "when supply tokens outnumber asset tokens, a larger deposit of assets will produce an equal or greater number of shares";
    } else {
        // strongly monotonic behavior when supply tokens do not outnumber asset tokens
        assert smallerAssets < largerAssets => smallerShares < largerShares, // passes when smallerShares <= largerShares, could simplify to exclude token ratios
            "when supply tokens do not outnumber asset tokens, a larger deposit of assets will produce a greater number of shares";
    }
}



rule totalsWeakMonotonicity() {
    method f; env e; calldataarg args;
    storage before = lastStorage;
    uint256 totalSupplyBefore = totalSupply();
    uint256 totalAssetsBefore = totalAssets();

    f(e, args) at before; // check to see if signs can be opposite --> using !(a xor b), but how to account for oldLevel == newLevel

    uint256 totalSupplyChangeA = updateChangeMarker(e, totalSupplyBefore, totalSupply());
    uint256 totalAssetsChangeA = updateChangeMarker(e, totalAssetsBefore, totalAssets());

    f(e, args) at before;

    uint256 totalSupplyChangeB = updateChangeMarker(e, totalSupplyBefore, totalSupply());
    uint256 totalAssetsChangeB = updateChangeMarker(e, totalAssetsBefore, totalAssets());

    assert totalSupplyChangeA < totalSupplyChangeB => totalAssetsChangeA <= totalAssetsChangeB;
    assert totalSupplyChangeA == totalSupplyChangeB => totalAssetsChangeA == totalAssetsChangeB;
    // assert totalSupplyChangeA > totalSupplyChangeB => totalAssetsChangeA >= totalAssetsChangeB; // not necessary because of A-B equivalence
}

function updateChangeMarker(env e, uint256 oldLevel, uint256 newLevel) returns uint256 {
    if (oldLevel <= newLevel) {
        return to_uint256(newLevel - oldLevel);
    } else {
        return to_uint256(oldLevel - newLevel);
    }
}

/*
rule generalWeakMonotonicity() {
    method f; env e; calldataarg args;
    storage before = lastStorage;
    uint256 totalSupplyBefore = totalSupply();
    uint256 totalAssetsBefore = totalAssets();
    uint256 totalSupplyChangeA; uint256 totalSupplyChangeB;
    uint256 totalAssetsChangeA; uint256 totalAssetsChangeB;
    f(e, args) at before; // check to see if signs can be opposite
    if (totalSupplyBefore <= totalSupply()) {
        totalSupplyChangeA = totalSupply() - totalSupplyBefore;
    } else {
        totalSupplyChangeA = totalSupplyBefore - totalSupply();
    }
    if (totalAssetsBefore <= totalAssets()) {
        totalAssetsChangeA = totalAssets() - totalAssetsBefore;
    } else {
        totalAssetsChangeA = totalAssetsBefore - totalAssets();
    }
    f(e, args) at before;
        if (totalSupplyBefore <= totalSupply()) {
        totalSupplyChangeB = totalSupply() - totalSupplyBefore;
    } else {
        totalSupplyChangeB = totalSupplyBefore - totalSupply();
    }
    if (totalAssetsBefore <= totalAssets()) {
        totalAssetsChangeB = totalAssets() - totalAssetsBefore;
    } else {
        totalAssetsChangeB = totalAssetsBefore - totalAssets();
    }

    assert totalSupplyChangeA < totalSupplyChangeB => totalAssetsChangeA <= totalAssetsChangeB;
    assert totalSupplyChangeA == totalSupplyChangeB => totalAssetsChangeA == totalAssetsChangeB;
    // assert totalSupplyChangeA > totalSupplyChangeB => totalAssetsChangeA >= totalAssetsChangeB; // not necessary because of A-B equivalence
}
*/

//// # strong and weak additivity //////////////////////////////////////////////

invariant convertToAssetsWeakAdditivity(uint256 sharesA, uint256 sharesB) // this isn't true w ==
    sharesA + sharesB < max_uint128 &&
    convertToAssets(sharesA) + convertToAssets(sharesB) < max_uint256 &&
    convertToAssets(sharesA + sharesB) < max_uint256 =>
    convertToAssets(sharesA) + convertToAssets(sharesB) <= convertToAssets(sharesA + sharesB) // == --> <= bc convertToAssets always rounds down

invariant convertToSharesWeakAdditivity(uint256 assetsA, uint256 assetsB) // true?
    assetsA + assetsB < max_uint128 &&
    convertToShares(assetsA) + convertToShares(assetsB) < max_uint256 &&
    convertToShares(assetsA + assetsB) < max_uint256 =>
    convertToShares(assetsA) + convertToShares(assetsB) <= convertToShares(assetsA + assetsB) // == --> <= bc convertToShares always rounds down

invariant conversionWeakIntegrity(uint256 sharesOrAssets)
    convertToShares(convertToAssets(sharesOrAssets)) <= sharesOrAssets &&
    convertToAssets(convertToShares(sharesOrAssets)) <= sharesOrAssets

//// # zero ////////////////////////////////////////////////////////////////////

invariant noSupplyIffNoAssets() // broken
    totalSupply() == 0 <=> userAssets(currentContract) == 0

//// # function epsilon ////////////////////////////////////////////////////////

rule contributionMethodWeakEquivalence() {
    env e; storage before = lastStorage;
    address contractAddress = currentContract; address assetAddress = asset();
    address receiver; uint256 receiverPriorBalance = balanceOf(receiver);
    uint256 senderPriorAssets = userAssets(e.msg.sender);
    require contractAddress != e.msg.sender
         && contractAddress != receiver
         && contractAddress != assetAddress;

    requireInvariant sumOfBalancePairsBounded(e.msg.sender, receiver);
    requireInvariant vaultSolvency();

    uint256 assets; uint256 shares;

    deposit(e, assets, receiver) at before; // 1 asset in, 102 shares out from previewDeposit [ (1 * 102) / 1 ] -> [ (assets * totalSupply) / totalAssets ]
    uint256 depositAssetsIn = senderPriorAssets - userAssets(e.msg.sender);
    uint256 depositSharesOut = balanceOf(receiver) - receiverPriorBalance;
    
    mint(e, shares, receiver) at before; // 1 asset in, 1 share out from previewMint [ (((1 * 1) - 1) / 102) + 1 ] -> [ (((shares * totalAssets) - 1) / totalSupply) + 1 ]
    uint256 mintAssetsIn = senderPriorAssets - userAssets(e.msg.sender);
    uint256 mintSharesOut = balanceOf(receiver) - receiverPriorBalance;

    assert depositAssetsIn == mintAssetsIn => depositSharesOut <= mintSharesOut,
        "if deposit and mint contribute equal assets, then deposit must produce shares less than or equal to mint";
    assert depositSharesOut == mintSharesOut => depositAssetsIn <= mintAssetsIn,
        "if deposit and mint produce equal shares, then deposit must contribute assets less than or equal to mint";
    
}

rule reclaimingMethodWeakEquivalence() {
    env e; storage before = lastStorage;
    address contractAddress = currentContract; address assetAddress = asset();
    address receiver; uint256 receiverPriorAssets = userAssets(receiver);
    address owner; uint256 ownerPriorBalance = balanceOf(owner);
    require contractAddress != receiver
         && contractAddress != owner
         && contractAddress != assetAddress;

    requireInvariant sumOfBalancePairsBounded(owner, receiver);
    requireInvariant vaultSolvency();

    uint256 assets; uint256 shares;

    withdraw(e, assets, receiver, owner) at before;
    uint256 withdrawSharesIn = ownerPriorBalance - balanceOf(owner);
    uint256 withdrawAssetsOut = userAssets(receiver) - receiverPriorAssets;
    
    redeem(e, shares, receiver, owner) at before; 
    uint256 redeemSharesIn = ownerPriorBalance - balanceOf(owner);
    uint256 redeemAssetsOut = userAssets(receiver) - receiverPriorAssets;

    assert withdrawSharesIn == redeemSharesIn => withdrawAssetsOut >= redeemAssetsOut,
        "if withdraw and redeem trade in equal shares, then withdraw must produce assets greater than or equal to redeem";
    assert withdrawAssetsOut == redeemAssetsOut => withdrawSharesIn >= redeemSharesIn,
        "if withdraw and redeem produce equal assets, then withdraw must contribute shares greater than or equal to redeem";    
}

////////////////////////////////////////////////////////////////////////////////
//// # stakeholder properties //////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

//// # vault cannot rob you ////////////////////////////////////////////////////

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

rule onlyContributionMethodsReduceAssets(method f) {
    address user; require user != currentContract;
    require asset() != currentContract;
    uint256 userAssetsBefore = userAssets(user);

    env e; calldataarg args;
    f(e, args);

    uint256 userAssetsAfter = userAssets(user);

    assert userAssetsBefore > userAssetsAfter =>
        (f.selector == deposit(uint256,address).selector ||
         f.selector == mint(uint256,address).selector),
        "a user's assets must not go down except on calls to contribution methods";
}

rule reclaimingProducesAssets(method f)
filtered {
    f -> f.selector == withdraw(uint256,address,address).selector
      || f.selector == redeem(uint256,address,address).selector
}
{
    env e; uint256 assets; uint256 shares;
    address caller; require caller == e.msg.sender;
    address receiver; address owner;
    require currentContract != caller
         && currentContract != receiver
         && currentContract != owner
         && currentContract != asset();

    requireInvariant sumOfBalancePairsBounded(owner, receiver); // check if needed
    requireInvariant vaultSolvency(); // not needed for withdrawing, check for redeeming

    uint256 ownerSharesBefore = balanceOf(owner);
    uint256 receiverAssetsBefore = userAssets(receiver);

    callReclaimingMethods(e, f, assets, shares, receiver, owner);

    uint256 ownerSharesAfter = balanceOf(owner);
    uint256 receiverAssetsAfter = userAssets(receiver);

    assert ownerSharesBefore > ownerSharesAfter <=> receiverAssetsBefore < receiverAssetsAfter,
        "an owner's shares must decrease if and only if the receiver's assets increase";
}

function callReclaimingMethods(env e, method f, uint256 assets, uint256 shares, address receiver, address owner) {
    if (f.selector == withdraw(uint256,address,address).selector) {
        withdraw(e, assets, receiver, owner);
    }
    if (f.selector == redeem(uint256,address,address).selector) {
        redeem(e, shares, receiver, owner);
    }
}

rule vaultMustAllowReclaiming() {
    assert false,
        "TODO calls to withdraw and redeem must not revert improperly";
}

invariant totalAssetsLeqVaultAssetBalance()
    totalAssets() <= userAssets(currentContract)

invariant totalAssetsAsSharesLeqVaultAssetBalanceAsShares() // rewrite as rule, as x <= y => f(x) <= f(y)
    convertToShares(totalAssets()) <= convertToShares(userAssets(currentContract))

invariant vaultSolvency()
    totalAssets() >= convertToAssets(totalSupply()) && 
    convertToShares(totalAssets()) >= totalSupply()

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
    {
        preserved {
            // because totalSupplyIsSumOfBalances is proven, the sum of any distinct two must be less than totalSupply
            require false; // this feels more honest than pretending
            // state assumption and say why safe assumption
            // write and function (safe assumptions function) with requireInvariants
        }
    }

invariant singleBalanceBounded(address addy)
    balanceOf(addy) <= totalSupply()
    {
        preserved {
            // because totalSupplyIsSumOfBalances is proven, any single balance must be less than totalSupply
            require false; // this feels more honest than pretending
        }
    }

rule totalSupplyReflectsMintingBurningShares {

    assert false,
        "TODO totalSupply must reflect minting and burning of shares";
}

rule totalAssetsReflectsContributionReclaimingAssets {
    assert false,
        "TODO totalAssets must reflect contribution and reclaiming of assets";
}

//// # you cannot rob vault ////////////////////////////////////////////////////



//// # you cannot rob another user /////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
//// # variable change properties //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

rule assetsSupplyChangeTogether {
    assert false,
    // assert (totalSupplyBefore < totalSupplyAfter <=> totalAssetsBefore < totalAssetsAfter)
    //     && (totalSupplyBefore > totalSupplyAfter <=> totalAssetsBefore > totalAssetsAfter),
        "increases and decreases in totalSupply must occur with corresponding increases and decreases in totalAssets";
}// math rule


////////////////////////////////////////////////////////////////////////////////
//// # variable relationship properties ////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

invariant assetIsNotVaultToken() // violated init state
    asset() != currentContract // Armen interesting idea. Bug? Def weird



////////////////////////////////////////////////////////////////////////////////
//// # state change properties /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// invariant noSupplyIffNoAssets() // broken
//     totalSupply() == 0 <=> userAssets(currentContract) == 0


// rule asset doesn't change after method

rule contractCannotCallIoMethods {
    assert false,
        "the vault must not be able to call its own contribution and reclaiming functions";
}

////////////////////////////////////////////////////////////////////////////////
//// # unit test properties //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

























//// # State Change Logic //////////////////////////////////////////////////////

// rounding direction in transactions should always favor vault

// No one should trade in shares without receiving assets in return

// ********************* Risks to vault ************************************************************************************

// Bank No one should receive shares without contributing assets to the vault (account for staking etc.)
// assert total supply increase <=> total assets increase



// Bank Assets (totalAssets or balanceOf(contract address)) must equal or exceed liabilities (totalSupply)


// ********************* Permissions ************************************************************************************

// Only I/approved should be able to remove any of the assets/shares I have in the vault

// No one should be able to take out more than they have in the vault




/// This rule should always fail.
rule sanity {
    method f; env e; calldataarg args;

    f(e, args);

    assert false, 
        "This rule should always fail";
}



/*



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






// rule userAssetsSharesInverseInputOutput(method f) // filtered and incorrect version
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

// rule depositingProducesShares() { // single method of contribution
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

rule withdrawingProducesAssets() { // single method of reclaiming
// rule redeemingProducesAssets() {
    env e; uint256 assets; uint256 shares;
    address caller; require caller == e.msg.sender;
    address receiver; address owner;
    require currentContract != caller
         && currentContract != receiver
         && currentContract != owner
         && currentContract != asset();

    requireInvariant sumOfBalancePairsBounded(owner, receiver); // check if needed
    requireInvariant vaultSolvency(); // not needed for withdrawing, check for redeeming

    uint256 ownerSharesBefore = balanceOf(owner);
    uint256 receiverAssetsBefore = userAssets(receiver);

    withdraw(e, assets, receiver, owner); // working with withdraw? yes, but verify
    // redeem(e, shares, receiver, owner); // working with redeem? no

    uint256 ownerSharesAfter = balanceOf(owner);
    uint256 receiverAssetsAfter = userAssets(receiver);

    assert ownerSharesBefore > ownerSharesAfter <=> receiverAssetsBefore < receiverAssetsAfter,
        "an owner's shares must decrease if and only if the receiver's assets increase";
} // generalize as reclaimingProducesAssets w function reclaim // exchange better?

*/

// preserved transferFrom(address x, address y, uint256 amount) with (env e) { // example for reference
//     require e.msg.sender != currentContract;
//     requireInvariant totalSupplyIsSumOfBalances();
//     requireInvariant sumOfBalancePairsBounded(x, y);
// }

/*
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
*/

// invariant totalAssetsIsSumOfAssets() // not useful?
//     totalAssets() == convertToAssets(sumOfBalances)




/*
                [down]
deposit A   ->  S(A)
mint  A(S)  ->    S
      [up]

IF  A == A(S) => S(A) <= S
IF S(A) == S => A <= A(S)

*/