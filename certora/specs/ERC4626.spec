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
//// # solvency properties /////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

invariant totalAssetsVsVaultAssetBalance()
    false // TODO 

invariant vaultSolvency()
    false // TODO

ghost uint256 sumOfBalances { // DONE
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE { // DONE
    sumOfBalances = sumOfBalances + newValue - oldValue;
}

invariant totalSupplyIsSumOfBalances() // DONE
    totalSupply() == sumOfBalances

invariant sumOfBalancePairsBounded(address addy1, address addy2) // TODO rework preserved block for better justification
    addy1 != addy2 => balanceOf(addy1) + balanceOf(addy2) <= totalSupply()
    {
        preserved {
            // totalSupplyIsSumOfBalances implies that the sum of any two distinct balances must be less than totalSupply
            // require false; // this feels more honest than pretending
            requireInvariant totalSupplyIsSumOfBalances(); // Does this convey the idea better?
        }
    }

invariant singleBalanceBounded(address addy) // TODO 
    balanceOf(addy) <= totalSupply()
    {
        preserved {
            // totalSupplyIsSumOfBalances implies that the sum of any single balance must be less than totalSupply
            // require false; // this feels more honest than pretending
            requireInvariant totalSupplyIsSumOfBalances(); // Does this convey the idea better?
        }
    }

rule vaultCoversReclaiming() { // TODO incomplete rule
    address owner;
    uint256 shares; require shares == balanceOf(owner);
    requireInvariant totalSupplyIsSumOfBalances(); // TODO safeAssumptions refactor
    requireInvariant singleBalanceBounded(owner);
    env e;
    redeem(e, shares, _, owner);
    uint256 ownerBalanceAfter = balanceOf(owner);
    assert ownerBalanceAfter == 0;
}

rule totalSupplyReflectsMintingBurningShares { // TODO solvency

    assert false,
        "TODO totalSupply must reflect minting and burning of shares";
}

rule totalAssetsReflectsContributionReclaimingAssets { // TODO solvency
    assert false,
        "TODO totalAssets must reflect contribution and reclaiming of assets";
}

rule assetsSupplyChangeTogether { // TODO
    assert false,
    // assert (totalSupplyBefore < totalSupplyAfter <=> totalAssetsBefore < totalAssetsAfter)
    //     && (totalSupplyBefore > totalSupplyAfter <=> totalAssetsBefore > totalAssetsAfter),
        "increases and decreases in totalSupply must occur with corresponding increases and decreases in totalAssets";
}// math rule

////////////////////////////////////////////////////////////////////////////////
//// # mathematical properties /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

invariant noSupplyIffNoAssets() // DONE(?) but FAILING
    totalSupply() == 0 <=> userAssets(currentContract) == 0
    {
        preserved with (env e) {
            address receiver1;
            safeAssumptions(e, receiver1, e.msg.sender);
        }
        preserved transfer(address receiver, uint256 shares) with (env e2) {
            safeAssumptions(e2, receiver, e2.msg.sender);
        }
        preserved transferFrom(address owner, address receiver, uint256 shares) with (env e3) {
            safeAssumptions(e3, receiver, owner);
        }
        preserved withdraw(uint256 assets, address receiver, address owner) with (env e4) { // FAILING withdraw leaves assets in the pool while zeroing out totalSupply due to rounding
            safeAssumptions(e4, receiver, owner);
        }
        preserved redeem(uint256 shares, address receiver, address owner) with (env e5) { // FAILING redeem leaves assets in the pool while zeroing out totalSupply by transferring
            safeAssumptions(e5, receiver, owner);
        }
    }

// TODO x3 this rule is a specific rule dealing with only deposit
// option 1 (repetitious, simple): write 4 rules
// option 2 (less repetitious, less simple): write 2 rules, 1 for share-unit methods, 1 for asset-unit methods
// option 3 (succinct, more complex): write 1 rule handling all 4 methods
rule depositStrongWeakMonotonicity() { // TODO before simplifying to exclude token ratios, consider whether the improper behavior is a bug.
    env e; storage before = lastStorage;

    address receiver; uint256 receiverPriorBalance = balanceOf(receiver);
    uint256 smallerAssets; uint256 largerAssets;
    
    require currentContract != e.msg.sender
         && currentContract != receiver
         && currentContract != asset();

    requireInvariant sumOfBalancePairsBounded(e.msg.sender, receiver); // TODO needs safeAssumptions refactor
    requireInvariant vaultSolvency();

    deposit(e, smallerAssets, receiver) at before;
    uint256 smallerShares = balanceOf(receiver) - receiverPriorBalance;

    deposit(e, largerAssets, receiver) at before;
    uint256 largerShares = balanceOf(receiver) - receiverPriorBalance;

    if (totalSupply() > totalAssets()) {
        // weakly monotonic behavior when supply tokens outnumber asset tokens
        assert smallerAssets < largerAssets => smallerShares <= largerShares,
            "when supply tokens outnumber asset tokens, a larger deposit of assets must produce an equal or greater number of shares";
    } else {
        // strongly monotonic behavior when supply tokens do not outnumber asset tokens
        assert smallerAssets < largerAssets => smallerShares < largerShares, // TODO FAILING passes when smallerShares <= largerShares, could simplify to exclude token ratios
            "when supply tokens do not outnumber asset tokens, a larger deposit of assets must produce a greater number of shares";
    }
}

rule totalsWeakMonotonicity() {
    method f; env e; calldataarg args;
    storage before = lastStorage;
    uint256 totalSupplyBefore = totalSupply();
    uint256 totalAssetsBefore = totalAssets();

    f(e, args) at before; // TODO with below check to see if signs can be opposite --> likely !(a xor b) but should account for oldLevel == newLevel

    uint256 totalSupplyChangeA = updateChangeMarker(e, totalSupplyBefore, totalSupply());
    uint256 totalAssetsChangeA = updateChangeMarker(e, totalAssetsBefore, totalAssets());

    f(e, args) at before;

    uint256 totalSupplyChangeB = updateChangeMarker(e, totalSupplyBefore, totalSupply());
    uint256 totalAssetsChangeB = updateChangeMarker(e, totalAssetsBefore, totalAssets());

    // possibly assert totalSupply and totalAssets must not change in opposite directions
    assert totalSupplyChangeA < totalSupplyChangeB => totalAssetsChangeA <= totalAssetsChangeB,
        "if totalSupply changes by a larger amount, the corresponding change in totalAssets must remain the same or grow";
    assert totalSupplyChangeA == totalSupplyChangeB => totalAssetsChangeA == totalAssetsChangeB,
        "equal size changes to totalSupply must yield equal size changes to totalAssets";
}

rule conversionOfZero { //  DONE
    uint256 convertZeroShares = convertToAssets(0);
    uint256 convertZeroAssets = convertToShares(0);

    assert convertZeroShares == 0,
        "converting zero shares must return zero assets";
    assert convertZeroAssets == 0,
        "converting zero assets must return zero shares";
}

// TODO was passing, now timing out, likely refactor as rule
// TODO refactor for better handling of overflow/safeAssumptions
invariant convertToAssetsWeakAdditivity(uint256 sharesA, uint256 sharesB) // TODO update to account for 'floor' of possible values
    sharesA + sharesB < max_uint128 &&
    convertToAssets(sharesA) + convertToAssets(sharesB) < max_uint256 &&
    convertToAssets(sharesA + sharesB) < max_uint256 =>
    convertToAssets(sharesA) + convertToAssets(sharesB) <= convertToAssets(sharesA + sharesB)

// TODO was passing, now timing out, likely refactor as rule
// TODO refactor for better handling of overflow/safeAssumptions
invariant convertToSharesWeakAdditivity(uint256 assetsA, uint256 assetsB) // TODO update to account for 'floor' of possible values
    assetsA + assetsB < max_uint128 &&
    convertToShares(assetsA) + convertToShares(assetsB) < max_uint256 &&
    convertToShares(assetsA + assetsB) < max_uint256 =>
    convertToShares(assetsA) + convertToShares(assetsB) <= convertToShares(assetsA + assetsB)

rule conversionWeakMonotonicity { // TODO refactor to account for floor of possible values
    uint256 smallerShares; uint256 largerShares;
    uint256 smallerAssets; uint256 largerAssets;

    assert smallerShares < largerShares => convertToAssets(smallerShares) <= convertToAssets(largerShares),
        "converting more shares must yield equal or greater assets";
    assert smallerAssets < largerAssets => convertToShares(smallerAssets) <= convertToShares(largerAssets),
        "converting more assets must yield equal or greater shares";
}

// TODO likely refactor as rule
// TODO consider refactor to form of inverse_amount and inverse_shares from math properties
invariant conversionWeakIntegrity(uint256 sharesOrAssets) // TODO update to include floor for returned value for rounding
    convertToShares(convertToAssets(sharesOrAssets)) <= sharesOrAssets &&
    convertToAssets(convertToShares(sharesOrAssets)) <= sharesOrAssets


////////////////////////////////////////////////////////////////////////////////
//// # stakeholder properties //////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

rule contributingProducesShares(method f) // PASSING
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

    requireInvariant sumOfBalancePairsBounded(contributor, receiver); // TODO safeAssumptions refactor
    requireInvariant vaultSolvency(); // TODO replace
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

rule onlyContributionMethodsReduceAssets(method f) { // PASSING
    address user; require user != currentContract; // TODO needs safeAssumptions refactor
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

rule reclaimingProducesAssets(method f) // PASSING
filtered {
    f -> f.selector == withdraw(uint256,address,address).selector
      || f.selector == redeem(uint256,address,address).selector
}
{
    env e; uint256 assets; uint256 shares;
    address caller; require caller == e.msg.sender;
    address receiver; address owner;
    require currentContract != caller // TODO needs safeAssumptions refactor
         && currentContract != receiver
         && currentContract != owner
         && currentContract != asset();

    requireInvariant sumOfBalancePairsBounded(owner, receiver); // check if needed
    requireInvariant vaultSolvency(); // not needed for withdrawing, check for redeeming TODO remove/rework

    uint256 ownerSharesBefore = balanceOf(owner);
    uint256 receiverAssetsBefore = userAssets(receiver);

    callReclaimingMethods(e, f, assets, shares, receiver, owner);

    uint256 ownerSharesAfter = balanceOf(owner);
    uint256 receiverAssetsAfter = userAssets(receiver);

    assert ownerSharesBefore > ownerSharesAfter <=> receiverAssetsBefore < receiverAssetsAfter,
        "an owner's shares must decrease if and only if the receiver's assets increase";
}

////////////////////////////////////////////////////////////////////////////////
//// # variable change properties //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// TODO already partially present w reclaiming and contributing rules
// decide if needed
// FAILING on IO methods
rule gainingLosingSharesInvChangesUserAssets(method f)
filtered {
    f -> f.selector != transfer(address,uint256).selector
      && f.selector != transferFrom(address,address,uint256).selector
}
{
    env e;
    require currentContract != e.msg.sender; // TODO safeAssumptions refactor
    address user;
    uint256 userSharesBefore = balanceOf(user);
    uint256 userAssetsBefore = userAssets(user);

    calldataarg args;
    f(e, args);

    uint256 userSharesAfter = balanceOf(user);
    uint256 userAssetsAfter = userAssets(user);

    assert userSharesBefore < userSharesAfter <=> userAssetsBefore > userAssetsAfter,
        "if a user's shares increase outside of transfers, the user's assets must decrease";
    assert userSharesBefore > userSharesAfter <=> userAssetsBefore < userAssetsAfter,
        "if a user's shares decrease outside of transfers, the user's assets must increase";
}

rule underlyingCannotChange() { // DONE?
    address originalAsset = asset();

    method f; env e; calldataarg args;
    f(e, args);

    address newAsset = asset();

    assert originalAsset == newAsset,
        "the underlying asset of a contract must not change";
}

////////////////////////////////////////////////////////////////////////////////
//// # variable relationships properties ///////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
//// # state change properties /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
//// # unit test properties ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

rule vaultMustAllowReclaiming() { // TODO
    assert false,
        "TODO calls to withdraw and redeem must not revert improperly";
}

// TODO check logic
rule contributionMethodWeakEquivalence() { // TODO FAILING due to violation of expected rounding behavior
    env e; storage before = lastStorage;
    address contractAddress = currentContract; address assetAddress = asset();
    address receiver; uint256 receiverPriorBalance = balanceOf(receiver);
    uint256 senderPriorAssets = userAssets(e.msg.sender);
    require contractAddress != e.msg.sender
         && contractAddress != receiver
         && contractAddress != assetAddress;

    requireInvariant sumOfBalancePairsBounded(e.msg.sender, receiver); // TODO needs safeAssumptions refactor
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

// TODO same tasks as contributionMethodWeakEquivalence
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

//// # convertTo_____ previewFunction //////////////////////////////////////////

/// relationship between convertToShares and previewDeposit

/// relationship between convertToAssets and previewMint

/// relationship between convertToShares and previewWithdraw

/// relationship between convertToAssets and previewRedeem

////////////////////////////////////////////////////////////////////////////////
//// # helpers and miscelanious ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// This rule should always fail.
rule sanity {
    method f; env e; calldataarg args;

    f(e, args);

    assert false, 
        "This rule should always fail";
}

function safeAssumptions(env e, address receiver, address owner) { // DONE
    require currentContract != asset(); // Although this is not disallowed, we assume the contract's underlying asset is not the contract itself
    requireInvariant totalSupplyIsSumOfBalances();
    requireInvariant sumOfBalancePairsBounded(receiver, owner);
    requireInvariant singleBalanceBounded(receiver);
}

function updateChangeMarker(env e, uint256 oldLevel, uint256 newLevel) returns uint256 { // TODO when time, generalize this function to use elsewhere
    if (oldLevel <= newLevel) {
        return to_uint256(newLevel - oldLevel);
    } else {
        return to_uint256(oldLevel - newLevel);
    }
}

// TODO clean up
function callContributionMethods(env e, method f, uint256 assets, uint256 shares, address receiver) {
    if (f.selector == deposit(uint256,address).selector) {
        deposit(e, assets, receiver);
        // return;
    }
    if (f.selector == mint(uint256,address).selector) {
        mint(e, shares, receiver);
        // return;
    }
} // TODO file bug report on weird java error when returns are present, works when returns commented out

function callReclaimingMethods(env e, method f, uint256 assets, uint256 shares, address receiver, address owner) { // DONE
    if (f.selector == withdraw(uint256,address,address).selector) {
        withdraw(e, assets, receiver, owner);
    }
    if (f.selector == redeem(uint256,address,address).selector) {
        redeem(e, shares, receiver, owner);
    }
}












// TODO remove
// invariant assetIsNotVaultToken() // violated init state
//     asset() != currentContract // Armen interesting idea. Bug? Def weird
//     // in report specify...






// ++++++++++++++++++



rule contractCannotCallIoMethods(method f) 
filtered {
    f -> f.selector == deposit(uint256,address).selector
      || f.selector == mint(uint256,address).selector
      || f.selector == withdraw(uint256,address,address).selector
      || f.selector == redeem(uint256,address,address).selector
}
{
    env e; calldataarg args;
    f(e, args);
    assert currentContract != e.msg.sender,
        "the vault must not be able to call its own contribution and reclaiming functions";
} // TODO doesn't probably do what I want it to: remove it


// rounding direction in transactions should always favor vault

// Only I/approved should be able to remove any of the assets/shares I have in the vault // --> distinct permissions section?

// No one should be able to take out more than they have in the vault // --> like solvency but personal

















/*



*/