#!/usr/bin/env bash
set -euo pipefail
export LEAN_PATH=lean/.lake/cycle255-focused
LEAN=../toolchain244/bin/lean
printf 'Focused cycle255 fresh-module verification started '; date -u +%FT%TZ
while read -r module; do
  echo "$LEAN --trust=0 -DwarningAsError=true -o $LEAN_PATH/Yulang/$module.olean lean/Yulang/$module.lean"
  "$LEAN" --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/$module.olean" "lean/Yulang/$module.lean"
  echo "$module exit=0"
done < notes/verification/cycle255/modules.txt
"$LEAN" --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Audit/Cycle255Usage.olean" lean/Audit/Cycle255Usage.lean > notes/verification/cycle255/usage.txt
echo 'Usage 20 examples exit=0'
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle255Complete.lean > notes/verification/cycle255/complete-audit.txt
echo 'Complete explicit-declaration audit exit=0'
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle255Full.lean > notes/verification/cycle255/full-audit.txt
cat notes/verification/cycle255/full-audit.txt
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle255Reach.lean > notes/verification/cycle255/reach.txt
tail -1 notes/verification/cycle255/reach.txt
python3 notes/verification/cycle255/check-sources.py > notes/verification/cycle255/source-check.txt
cat notes/verification/cycle255/source-check.txt
printf 'Focused verification completed '; date -u +%FT%TZ
