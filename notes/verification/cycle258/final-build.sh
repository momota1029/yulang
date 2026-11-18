#!/usr/bin/env bash
set -euo pipefail
export LEAN_PATH=lean/.lake/cycle258-final
LEAN=../toolchain244/bin/lean
V=notes/verification/cycle258
printf 'Final fresh focused build start '; date -u +%FT%TZ
while read -r module; do
 printf 'BUILD %s ' "$module"; date -u +%FT%TZ
 "$LEAN" --trust=0 -DwarningAsError=true -o "$LEAN_PATH/Yulang/$module.olean" "lean/Yulang/$module.lean"
done < "$V/modules.txt"
for kind in Complete Full Usage Reach Types AllTypes; do
 "$LEAN" --trust=0 -DwarningAsError=true "lean/Audit/Cycle258$kind.lean" > "$V/${kind,,}-final.txt" 2>&1
done
python "$V/check-sources.py"
printf 'FINAL-FOCUSED-PASS '; date -u +%FT%TZ
