#!/bin/sh
set -eu
export LEAN_PATH=lean/.lake/cycle263-normalized-review
path=/tmp/yulang263-normalized-review/lean/Yulang/GeneralRebaseSourceLocalMeaning263.lean
git show ce8255291:lean/Yulang/GeneralRebaseSourceLocalMeaning263.lean > "$path"
../toolchain244/bin/lean --root=/tmp/yulang263-normalized-review/lean --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/GeneralRebaseSourceLocalMeaning263.olean" "$path"
sha256sum "$path" > notes/verification/cycle263-normalized/local-meaning-review/source-hashes.txt
../toolchain244/bin/lean --trust=0 -DwarningAsError=true notes/verification/cycle263-normalized/local-meaning-review/Probe.lean > notes/verification/cycle263-normalized/local-meaning-review/audit.txt
printf 'PASS SourceLocalMeaning263 strict independent review\n'
