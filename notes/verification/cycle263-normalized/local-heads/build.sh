#!/bin/sh
set -eu
export LEAN_PATH=lean/.lake/cycle263-normalized-review
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/GeneralRebaseSourceLocalHeads263.olean" lean/Yulang/GeneralRebaseSourceLocalHeads263.lean
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle263LocalHeads.lean > notes/verification/cycle263-normalized/local-heads/audit.txt
sha256sum lean/Yulang/GeneralRebaseSourceLocalHeads263.lean > notes/verification/cycle263-normalized/local-heads/source-hashes.txt
printf 'PASS SourceLocalHeads263 and focused audit\n'
