#!/usr/bin/env bash
# Run from repository root with the pinned Lean toolchain available.
set -euo pipefail
python notes/verification/cycle185/preservation.py
(
 cd lean
 lake build --wfail Yulang.GeneralNominalHeadRootExtension185 Yulang.GeneralNominalHeadHistoricalExtension185 Yulang.GeneralNominalCenteredHeadWFJoinCounterexample Yulang.GeneralNominalHeadSemanticTransport185
 lake env lean --trust=0 -DwarningAsError=true Audit/Cycle185ReleaseGate.lean
 lake env lean --trust=0 -DwarningAsError=true Audit/Cycle185PublicTypes.lean
 lake env lean --trust=0 -DwarningAsError=true Audit/Cycle185SemanticTypes.lean
 for source in Yulang/*185.lean; do
   lake env lean --trust=0 -DwarningAsError=true "$source"
 done
 YULANG_REACH_ROOTS=../notes/verification/cycle185/general-roots.txt YULANG_REACH_OUTPUT=/tmp/cycle185-general-reach.tsv lake env lean ../tools/ReachCycle185Release.lean
 YULANG_REACH_ROOTS=../notes/verification/cycle185/release-local-roots.txt YULANG_REACH_OUTPUT=/tmp/cycle185-local-reach.tsv lake env lean ../tools/ReachCycle185Release.lean
)
