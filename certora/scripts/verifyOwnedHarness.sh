if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun \
    certora/harnesses/auth/OwnedHarness.sol \
    --verify OwnedHarness:certora/specs/OwnedHarness.spec \
    --solc solc8.0 \
    --optimistic_loop \
    --loop_iter 3 \
    --send_only \
    --cloud \
    $RULE \
    --msg "OwnedHarness verification: $1"