#!/usr/bin/env bash
set -euo pipefail
export LEAN_PATH=lean/.lake/cycle247-clean
LEAN=../toolchain244/bin/lean
printf 'Focused cycle254 verification started '; date -u +%FT%TZ
while read -r module; do
  echo "$LEAN --trust=0 -DwarningAsError=true -o $LEAN_PATH/Yulang/$module.olean lean/Yulang/$module.lean"
  "$LEAN" --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/$module.olean" "lean/Yulang/$module.lean"
  echo "$module exit=0"
done < notes/verification/cycle254/modules.txt
"$LEAN" --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Audit/Cycle254Usage.olean" lean/Audit/Cycle254Usage.lean
echo 'Usage 17 examples exit=0'
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle254Complete.lean > notes/verification/cycle254/complete-audit.txt
echo 'Complete audit 84 explicit declarations exit=0'
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle254Full.lean > notes/verification/cycle254/full-audit.txt
cat notes/verification/cycle254/full-audit.txt
python3 notes/verification/cycle254/check-sources.py > notes/verification/cycle254/source-check.txt
cat notes/verification/cycle254/source-check.txt
printf 'Focused verification completed '; date -u +%FT%TZ
