#!/usr/bin/env bash
set -euo pipefail
export LEAN_PATH=lean/.lake/cycle247-clean
LEAN=../toolchain244/bin/lean
for m in GeneralPatternAdditiveDepth253 GeneralNominalExprDepth253 GeneralNominalOutputNames253 GeneralNominalRawFinite253 GeneralNominalPublicPorts253 GeneralDictionaryCompoundPool253 GeneralDictionaryCompoundPoolRepair253 GeneralPatternDependencyDepth253 GeneralDictionaryOutputDepthRepair253 GeneralDeclarationProducerRank253 GeneralDeclarationOutputDepth253 GeneralNominalPublicBasis253 GeneralNominalAllHeadReadback253; do
 echo "BUILD $m"
 "$LEAN" --trust=0 -DwarningAsError=true -o "lean/.lake/cycle247-clean/Yulang/$m.olean" "lean/Yulang/$m.lean"
 echo "EXIT 0 $m"
done
for a in CompleteAudit Full Usage; do
 echo "AUDIT Cycle253$a"
 "$LEAN" --trust=0 -DwarningAsError=true "lean/Audit/Cycle253$a.lean"
 echo "EXIT 0 Cycle253$a"
done
python notes/verification/cycle253/check-sources.py
