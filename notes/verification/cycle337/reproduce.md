# C337 verification

Verifier: official Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Authenticated release archive SHA-256: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.

From the `lean/` directory at the fixed report commit, with the project's matching toolchain:

```sh
set -eu
set --
for f in Yulang/GeneralDeclarative*337.lean; do
  set -- "$@" "Yulang.$(basename "$f" .lean)"
done
lake build "$@" --wfail
for f in Yulang/GeneralDeclarative*337.lean Audit/Cycle337*.lean; do
  lake env lean --trust=0 -DwarningAsError=true "$f"
done
```

- [Scoped Lake build](scoped-all.txt), [direct source/audit replay status](all-direct.txt), and [declarative transitive dependency boundary](dependency-boundary.txt).
- Separate per-theorem axiom logs: [core](standalone-core.txt), [composition](standalone-compose.txt), [authorship](standalone-authorized.txt), [dictionary](standalone-dictionary.txt), [nested](standalone-nested.txt), [clash](standalone-clash.txt), [compatibility](standalone-compatibility.txt). Only the standard `propext`, `Classical.choice`, and `Quot.sound` occur; not every result uses all.
- C336 base: `3c878eabd74db107b7db9d7f74c6d0a254de0c1b`. Logic-only replay pin before the dependency-audit source: `a4dc88479763de5131e5c2eac1a274b754beec45`.
- To verify I-52/I-57, compare fixed-commit path/blob deltas against the C336 base. Read the entire current and original `lean/Yulang.lean` blobs and check the exact append-only list of 13 C337 imports. The two frozen paths `lean/Audit.lean` and `lean/README.md` remain Git blobs `97dd1cfaded3e3abc3fd8caa98a64843d6f7a3d9` and `9fd6842bcc00c5bc5c00a196d9ccb328c6b0c94a`, respectively.
- No whole-repository Lake or Rust build/execution. The finite sample counts in the contemporaneous [design note](../../design/dots-cycle-337-exact-deletion.md) predate restoration of the Lean toolchain and are not kernel results.
- [Fixed-commit exact source replay](pinned-direct.txt), [Git object and byte readback](git-direct-readback.txt), [official diff-only checker summary](verify-diff-summary.txt), and [scoped gate log](scoped-gate.txt). Re-run `lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle337/dependency-boundary.lean` to check the transitive declarative boundary.
