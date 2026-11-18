#!/usr/bin/env bash
set -euo pipefail
export LEAN_PATH=lean/.lake/cycle256-focused
LEAN=../toolchain244/bin/lean
printf 'Focused cycle256 fresh-module verification started '; date -u +%FT%TZ
while read -r module; do
  echo "$LEAN --trust=0 -DwarningAsError=true -o $LEAN_PATH/Yulang/$module.olean lean/Yulang/$module.lean"
  "$LEAN" --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/$module.olean" "lean/Yulang/$module.lean"
  echo "$module exit=0"
done < notes/verification/cycle256/modules.txt
"$LEAN" --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Audit/Cycle256Usage.olean" lean/Audit/Cycle256Usage.lean > notes/verification/cycle256/usage.txt
echo 'Usage 19 examples exit=0'
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle256Complete.lean > notes/verification/cycle256/complete-audit.txt
echo 'Complete explicit-declaration audit exit=0'
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle256Full.lean > notes/verification/cycle256/full-audit.txt
cat notes/verification/cycle256/full-audit.txt
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle256Reach.lean > notes/verification/cycle256/reach.txt
tail -1 notes/verification/cycle256/reach.txt
"$LEAN" --trust=0 -DwarningAsError=true lean/Audit/Cycle256Types.lean > notes/verification/cycle256/critical-types.txt
python3 notes/verification/cycle256/check-sources.py > notes/verification/cycle256/source-check.txt
cat notes/verification/cycle256/source-check.txt
printf 'Focused verification completed '; date -u +%FT%TZ
