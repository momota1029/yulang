#!/usr/bin/env bash
set -euo pipefail
export LEAN_PATH=lean/.lake/cycle247-clean
echo BUILD Yulang.GeneralNominalVersionedHeadMass237
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o lean/.lake/cycle247-clean/Yulang/GeneralNominalVersionedHeadMass237.olean lean/Yulang/GeneralNominalVersionedHeadMass237.lean
echo BUILD Yulang.GeneralNominalVersionedWeightedHead237
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o lean/.lake/cycle247-clean/Yulang/GeneralNominalVersionedWeightedHead237.olean lean/Yulang/GeneralNominalVersionedWeightedHead237.lean
echo BUILD Yulang.GeneralNominalVersionedHeadReadback237
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o lean/.lake/cycle247-clean/Yulang/GeneralNominalVersionedHeadReadback237.olean lean/Yulang/GeneralNominalVersionedHeadReadback237.lean
echo BUILD Yulang.GeneralNominalVersionedChildLabels237
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o lean/.lake/cycle247-clean/Yulang/GeneralNominalVersionedChildLabels237.olean lean/Yulang/GeneralNominalVersionedChildLabels237.lean
echo BUILD Yulang.GeneralNominalVersionedMixedAncestry237
../toolchain244/bin/lean --trust=0 -DwarningAsError=true -o lean/.lake/cycle247-clean/Yulang/GeneralNominalVersionedMixedAncestry237.olean lean/Yulang/GeneralNominalVersionedMixedAncestry237.lean
echo EXIT 0
