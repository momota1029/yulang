#!/usr/bin/env bash
set -euo pipefail
export LEAN_PATH=lean/.lake/cycle247-clean
while read -r module; do
 echo "BUILD $module"
 ../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o "lean/.lake/cycle247-clean/Yulang/$module.olean" "lean/Yulang/$module.lean"
done < notes/verification/cycle252/CompleteAudit-modules.txt
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle252CompleteAudit.lean
../toolchain244/bin/lean --trust=0 -DwarningAsError=true lean/Audit/Cycle252Full.lean
echo 'EXIT 0'
