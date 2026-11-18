#!/bin/sh
set -eu
export LEAN_PATH=lean/.lake/cycle263-normalized-review
for module in GeneralRebaseSourceRepresentatives263 GeneralRebaseRepresentativesExample263; do
  ../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/$module.olean" "lean/Yulang/$module.lean"
  echo "PASS $module"
done
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle263Representatives.lean > notes/verification/cycle263-normalized/representatives/audit.txt
sha256sum lean/Yulang/GeneralRebaseSourceRepresentatives263.lean lean/Yulang/GeneralRebaseRepresentativesExample263.lean lean/Yulang/GeneralRebaseRegisteredOwners263.lean lean/Yulang/GeneralDictionaryCompoundStep238.lean > notes/verification/cycle263-normalized/representatives/source-hashes.txt
