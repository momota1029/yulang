#!/bin/sh
set -eu
export LEAN_PATH=lean/.lake/cycle264-projection
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/GeneralRebaseMergeRequests264.olean" lean/Yulang/GeneralRebaseMergeRequests264.lean
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle264MergeRequests.lean > notes/verification/cycle264-projection/merge-audit.txt
sha256sum lean/Yulang/GeneralRebaseMergeRequests264.lean > notes/verification/cycle264-projection/merge-source-hashes.txt
printf 'PASS MergeRequests264\n'
