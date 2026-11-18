#!/bin/sh
set -eu
export LEAN_PATH=lean/.lake/cycle264-projection
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/GeneralRebaseSourceRequests264.olean" lean/Yulang/GeneralRebaseSourceRequests264.lean
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle264SourceRequests.lean > notes/verification/cycle264-projection/requests-audit.txt
sha256sum lean/Yulang/GeneralRebaseSourceRequests264.lean > notes/verification/cycle264-projection/requests-source-hashes.txt
printf 'PASS SourceRequests264 production and audit\n'
