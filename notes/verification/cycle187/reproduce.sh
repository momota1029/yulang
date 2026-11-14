#!/usr/bin/env bash
set -euo pipefail
python notes/verification/cycle187/preservation.py
cd lean
lake build --wfail Yulang.GeneralNominalHeadBranchFrame187 Yulang.GeneralNominalHeadDeclaredBounds187
lake env lean --trust=0 -DwarningAsError=true Audit/Cycle187FrameGate.lean
lake env lean --trust=0 -DwarningAsError=true Audit/Cycle187FrameTypes.lean
for source in Yulang/*187.lean; do
  echo "SOURCE $source"
  lake env lean --trust=0 -DwarningAsError=true "$source"
done
