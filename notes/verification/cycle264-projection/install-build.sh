#!/bin/sh
set -eu
export LEAN_PATH=lean/.lake/cycle264-projection
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/GeneralRebaseSourceInstallProjection264.olean" lean/Yulang/GeneralRebaseSourceInstallProjection264.lean
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle264SourceInstallProjection.lean > notes/verification/cycle264-projection/install-audit.txt
sha256sum lean/Yulang/GeneralRebaseSourceInstallProjection264.lean lean/Yulang/GeneralRebaseLiveProjection264.lean > notes/verification/cycle264-projection/install-source-hashes.txt
printf 'PASS SourceInstallProjection264 and actual source example\n'
