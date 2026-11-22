# C338 verification

Lean version 4.35.0, official Linux release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Official release archive verified SHA-256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.

From the fixed report commit's `lean/` directory, with the specified toolchain:
```bash
set -eu
set --
for file in Yulang/GeneralDeclarative*338.lean; do
  set -- "$@" "Yulang.$(basename "$file" .lean)"
done
lake build "$@" --wfail
for file in Yulang/GeneralDeclarative*338.lean Audit/Cycle338*.lean; do
  lake env lean --trust=0 -DwarningAsError=true "$file"
done
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle338/dependency-boundary.lean
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle338/scoped-gate.lean
```

- [Focused scope build](scoped-final.txt), [direct source/standalone audit replay](all-direct-final.txt), [exact detached-pin replay](pinned-direct-final.txt), [source and immutable Git blob verification](git-exact-final.txt), [official diff-only summary](diff-official-summary.txt).
- [Dependency boundary](dependency-boundary-final.txt), [scoped gate](scoped-gate-final.txt). These are not whole-repository results.
- Standalone theorem audits: [initial](standalone-initial.txt), [recursive source](standalone-source.txt), [compiler/dictionary](standalone-compiler.txt), [original positive candidate and exact routed fixture](standalone-positive.txt), [selected fixture](standalone-fixture-final.txt), [open prefix and exact value naming](standalone-open-prefix.txt), [genuinely unclosed tail fixture](standalone-open-fixture.txt).
- Standard axioms only: `propext`, `Classical.choice`, `Quot.sound` (some proofs use fewer or none).
- C337 start object `cdfca81e37ee0b502b4b7bdf00a56720dbc2ba5b`. Before documentation commit, all proof bytes were read back from fixed pin `ac9fb5040adf67ec68fd3460741f4816363a2b33`. No changes to `lean/Audit.lean` or `lean/README.md`; existing `lean/Yulang.lean` bytes retained in full, with 18 exact appended imports.
