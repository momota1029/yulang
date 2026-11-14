#!/usr/bin/env bash
# Run from repository root, Lean4.35.0 on PATH. Focused targets only.
set -euo pipefail
python notes/verification/cycle186/preservation.py
(
 cd lean
 lake build --wfail Yulang.GeneralNominalHeadRevisitExtension186 Yulang.GeneralNominalHeadCandidateExtension186
 lake env lean --trust=0 -DwarningAsError=true Audit/Cycle186ReleaseGate.lean
 lake env lean --trust=0 -DwarningAsError=true Audit/Cycle186PublicTypes.lean
 for source in Yulang/*186.lean; do
   echo "SOURCE $source"
   lake env lean --trust=0 -DwarningAsError=true "$source"
 done
 YULANG_REACH_ROOTS=../notes/verification/cycle186/general-roots.txt YULANG_REACH_OUTPUT=/tmp/cycle186-general-reach.tsv lake env lean ../tools/ReachCycle186.lean
 YULANG_REACH_ROOTS=../notes/verification/cycle186/local-roots.txt YULANG_REACH_OUTPUT=/tmp/cycle186-local-reach.tsv lake env lean ../tools/ReachCycle186.lean
)
