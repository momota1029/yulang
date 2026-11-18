#!/bin/sh
set -eu
export LEAN_PATH=lean/.lake/cycle264-projection
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/GeneralRebaseMergeRegression264.olean" lean/Yulang/GeneralRebaseMergeRegression264.lean
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle264MergeRegression.lean > notes/verification/cycle264-projection/merge-regression-audit.txt
sha256sum lean/Yulang/GeneralRebaseMergeRegression264.lean > notes/verification/cycle264-projection/merge-regression-source-hashes.txt
printf 'PASS actual guarded mixed merge with strict projection growth\n'
