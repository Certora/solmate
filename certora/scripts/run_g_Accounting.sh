if [[ "$1" ]]
then
    RULE="--rule $1"
fi

if [[ "$2" ]]
then
    MSG="$2"
fi

certoraRun \
    certora/harnesses/mixins/ERC4626AccountingHarness.sol \
    certora/helpers/DummyERC20A.sol \
    --verify ERC4626AccountingHarness:certora/specs/gadi.spec \
    --link ERC4626AccountingHarness:asset=DummyERC20A \
    --solc solc8.0 \
    --optimistic_loop \
    --loop_iter 1 \
    --send_only \
    --staging master \
    --settings -mediumTimeout=2000 \
    $RULE \
    --msg "ERC4626 accounting: $RULE - $MSG"