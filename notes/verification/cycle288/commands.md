# Cycle 288 verification commands

Lean 4.35.0 (Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`)
was already available. Run from repository root, with the Lean 4.35.0
binaries first on PATH. The local predecessor tree was
`d1b1494efa0481b196f6c0623a11ccf37fab82b8`, the matching remote predecessor
`14ecc280dc7c28982a02c6d9b56879c172d77a63`; integration ancestor
`b9bb2a19d271447d6f03f8b99e8ec97c9ee50363`. Local and remote commits are
different objects, but whole tree hashes were checked on publication.

## Focused modules and standalone audit

The script took the added modules against the predecessor and used the
append-only barrel as topological order. Each module and audit invocation
was individually bounded, with a 330-second second-pass aggregate limit.
This was **not** `lake build` of the barrel nor the old monolithic audit.

```bash
BASE=d1b1494efa0481b196f6c0623a11ccf37fab82b8
modules=$(git diff --diff-filter=A --name-only "$BASE" HEAD -- lean/Yulang |
  sed -e 's,^.*/,,' -e 's/\.lean$//')
while IFS= read -r name; do
  if grep -qx "$name" <<< "$modules"; then
    (cd lean && timeout 160s lake env lean --trust=0 -M 3200 \
      -DwarningAsError=true -R . -o ".lake/build/lib/lean/Yulang/$name.olean" "Yulang/$name.lean") || exit
  fi
done < <(sed -n 's/^import Yulang\.//p' lean/Yulang.lean)
for part in $(git diff --diff-filter=A --name-only "$BASE" HEAD -- lean/Audit); do
  ! grep -q '^import Audit\.' "$part" || exit 1
  (cd lean && timeout 160s lake env lean --trust=0 -M 3200 \
    -DwarningAsError=true "${part#lean/}") || exit
done
```

Parsed every full axiom list, including multiline lists, against
`{propext, Classical.choice, Quot.sound}`, and matched the complete
set of module/audit names to the diff. See [focused.txt](focused.txt).
The finite phase table is checked by the kernel as a closed `example`,
not by executing a noncomputable journal or by a new Yulang2 run.

## Static checks

```bash
bash tools/verify-lean.sh . "$BASE" --no-build
bash tools/verify-lean.sh . b9bb2a19d271447d6f03f8b99e8ec97c9ee50363 --no-build
git diff --check "$BASE" HEAD
git merge-base --is-ancestor b9bb2a19d271447d6f03f8b99e8ec97c9ee50363 HEAD
git diff --exit-code "$BASE" HEAD -- lean/Audit.lean lean/README.md \
  lean/lakefile.lean lean/lean-toolchain notes/plan spec crates Cargo.toml Cargo.lock
```

Also checked byte-for-byte barrel prefix, one append per new module,
no modified existing module/audit, audit imports only `Yulang.*`, and no
forbidden tokens in any added Lean file, including comments. Full check
output is [static.txt](static.txt). The integration comparison reports
two preexisting REVIEW lines for the two Cycle 287 fixture evaluations;
this cycle has no new `#eval` or metaprogramming.

## Reused regressions

Each .lean was run by the same standalone command with a 100-second part
limit (350 seconds for the rerun), selecting 24 prior audit parts.
The first pass found missing cached `.olean` dependencies specifically for
199/202, not a theorem failure. A focused traversal of those two audit
import trees compiled only seven absent dependencies using the module
command above; both parts passed on retry. A fresh pass over all 24
succeeded. See [legacy.txt](legacy.txt) for exact targets and statuses.
