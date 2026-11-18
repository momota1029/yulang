#!/bin/sh
set -eu
export LEAN_PATH=lean/.lake/cycle263-normalized-review
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/GeneralRebaseFiniteStates263.olean" lean/Yulang/GeneralRebaseFiniteStates263.lean
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle263FiniteStates.lean > notes/verification/cycle263-normalized/finite-states/audit.txt
sha256sum lean/Yulang/GeneralRebaseFiniteStates263.lean > notes/verification/cycle263-normalized/finite-states/source-hashes.txt
printf 'PASS FiniteStates263 and focused audit\n'
