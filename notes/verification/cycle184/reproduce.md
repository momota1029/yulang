# Cycle184 verification reproduction

Toolchain: repository Lean4.35.0. Start from the final work/dots-main tree.
No full lake build or tools/verify-lean.sh was run by dot.

From lean/:
```
lake build --wfail Yulang.GeneralNominalRootExtension184 Yulang.GeneralNominalCandidateCoverage184
lake env lean --trust=0 -DwarningAsError=true Audit/Cycle184FourthGate.lean
lake env lean --trust=0 -DwarningAsError=true Audit/Cycle184PublicTypes.lean
lake build --wfail Yulang.GeneralNominalCenteredHeadWFTransfer
lake env lean --trust=0 -DwarningAsError=true Audit/Cycle184MigrationTypes.lean
```
Also each of the17 Yulang/*184.lean was individually recompiled with
`lake env lean --trust=0 -DwarningAsError=true` after latest integration;
all-source-strict.txt records every path/exit. verified-source-hashes.tsv
records those exact source bytes. Each module is imported exactly once in
Yulang.lean; the root file itself was not used to trigger a whole build.

Dependency reach from lean/ (ROOT is absolute repository path):
```
YULANG_REACH_ROOTS=$ROOT/notes/verification/cycle184/general-roots.txt \
YULANG_REACH_OUTPUT=/tmp/general184.tsv lake env lean --trust=0 ../tools/ReachCycle184.lean
YULANG_REACH_ROOTS=$ROOT/notes/verification/cycle184/local-roots.txt \
YULANG_REACH_OUTPUT=/tmp/local184.tsv lake env lean --trust=0 ../tools/ReachCycle184.lean
```
Only loaded184 defining modules are counted; standard/private/generated
constants contribute to155, while public theorem statements count92.
Syntactic dependency reach is not a semantic/specification adequacy proof.

From repo root: `python notes/verification/cycle184/preservation-upstream.py`
compares against integration0b2a6b482: all5245 paths retained, existing Lean
sources exact except append-only root, frozen Audit/README exact, INDEX
prefix preserved, no forbidden proof token in17 new modules. The earlier
preservation.py comparison targets startup work4d6 and is intentionally a
pre-late-merge historical audit. It need not pass after adopting supervisor
whitespace/import corrections; do not mistake that for our proof rewrites.

Failures during development were repaired namespace/import/implicit argument/
binder-shadowing compilation errors. No failed compile is reported as PASS.
One transport tree failed expected hash comparison due UTF8 chunking, was
not installed; ASCII-escaped JSON retry matched the full expected tree.
No permission block, no runtimeYulang2 rerun, no whole-CI certification,
no usage-budget information. No old proof source pruning or theorem weakening.
