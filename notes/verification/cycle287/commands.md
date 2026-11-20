# Cycle 287: narrow reproducible verification

Run on the pinned cycle snapshot from this repository, with Lean 4.35.0
and the existing dependency objects. The new modules are selected from the
barrel in dependency order. This is not a fresh full-library build.

```sh
set -eu
cd lean
for mod in $(sed -n 's/^import Yulang\.\(.*287\)$/\1/p' Yulang.lean); do
  lake env lean --trust=0 -M 3200 -DwarningAsError=true -R . \
    -o ".lake/build/lib/lean/Yulang/$mod.olean" "Yulang/$mod.lean"
done
for part in Audit/Cycle287*.lean; do
  lake env lean --trust=0 -M 3200 -DwarningAsError=true "$part"
done
```

`focused.txt` records each focused module and standalone audit result.
The complete bracketed axiom dependency lists (including wrapped lines)
were checked against `propext`, `Classical.choice`, `Quot.sound`.
`Audit/Cycle287Driver.lean` runs both executable fixture cases and
checks the exact tree shapes. These are Lean fixture computations, not
new Yulang2 compiled binaries or surface-language tests.

Old regression commands use the same lean flags for each of:
`Cycle206DefaultGap`, `Cycle233Final`, `Cycle239First`,
`Cycle240Independent`, `Cycle271InstalledReadback`, `Cycle271SourceTraces`,
`Cycle276EvidenceAt`, `Cycle284Driver`, `Cycle284JointLimit`,
`Cycle285Evidence`, `Cycle285Tower`, `Cycle286Trace`, `Cycle286Schedule`,
`Cycle286Projection`, and `Cycle286Semantic` (see `legacy.txt`).

```sh
# From repository root; static registration, freeze and diff only:
bash tools/verify-lean.sh . dfbb9f68dc03bf095e9091be84f0584ddfced2cf --no-build
bash tools/verify-lean.sh . b9bb2a19d271447d6f03f8b99e8ec97c9ee50363 --no-build
git diff --check dfbb9f68dc03bf095e9091be84f0584ddfced2cf HEAD
```

The local 286 commit used in the static log has the same whole tree as
the remote 286 pin above. Repetitive confirmations of the unchanged
audit files are abbreviated in `static.txt`. No full lake build, full
Audit, or repository CI was run.
