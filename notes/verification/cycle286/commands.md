# Cycle 286 focused verification

Run from the repository root on the pinned cycle tree with the repository's
Lean 4.35.0 toolchain. Keep existing dependency objects; this is not a clean
full-repository build. The cycle baseline is the tree of cycle 285, whose
remote commit is `e5057c2b5bbb16af2d7e835e2225286f5fa3dd18`. For routine
reproduction on the pinned snapshot, these file patterns select only 286.

```bash
set -eu
cd lean
for mod in $(sed -n 's/^import Yulang\.\(.*286\)$/\1/p' Yulang.lean); do
  lake env lean --trust=0 -M 3200 -DwarningAsError=true -R . \
    -o ".lake/build/lib/lean/Yulang/$mod.olean" "Yulang/$mod.lean"
done
for part in Audit/Cycle286*.lean; do
  lake env lean --trust=0 -M 3200 -DwarningAsError=true "$part"
done
for part in Cycle206DefaultGap Cycle233Final Cycle239First Cycle240Independent \
    Cycle271InstalledReadback Cycle271SourceTraces Cycle276EvidenceAt \
    Cycle284Driver Cycle284JointLimit Cycle285Path Cycle285Complete \
    Cycle285Evidence Cycle285Tower; do
  lake env lean --trust=0 -M 3200 -DwarningAsError=true "Audit/$part.lean"
done
```

The toolchain is printed at the start of `focused-recheck.txt`; the
standalone audit exit statuses and complete (including wrapped) axiom
reports are in that file. The axiom allowlist was verified over entire
bracketed lists, even when Lean wrapped them across lines. The named older
regression exit statuses are in `reused-regressions.txt`.

```bash
# From repository root, test only static preservation/registration.
bash tools/verify-lean.sh . e5057c2b5bbb16af2d7e835e2225286f5fa3dd18 --no-build
bash tools/verify-lean.sh . b9bb2a19d271447d6f03f8b99e8ec97c9ee50363 --no-build
git diff --check e5057c2b5bbb16af2d7e835e2225286f5fa3dd18 HEAD
```

`diff-scope.txt` uses the local commit matching the same cycle-285 tree.
It records the static-only checks and excludes repetitive confirmations for
unchanged audit parts. Full `lake build`, whole Audit, and full CI have not
been run by this cycle.
