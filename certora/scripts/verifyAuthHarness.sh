if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun \
    certora/harnesses/auth/AuthHarness.sol \
    --verify AuthHarness:certora/specs/AuthHarness.spec \
    --solc solc8.0 \
    --optimistic_loop \
    --loop_iter 3 \
    --send_only \
    --cloud \
    $RULE \
    --msg "AuthHarness verification: $1"