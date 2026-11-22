# Reproduce C336

Proof pin: `9ef7cc13aeeeeef30fc25dadb6dff111d00e214a`. Starting work pin: `bf7c80faefdce4b832e92b1cfa154a15247acf70`. All proofs use Lean 4.35.0. No Rust run or full repository Lean build was performed.

From `lean/`:

```bash
mapfile -t src < ../notes/verification/cycle336/modules.txt
mods=("${src[@]%.lean}")
lake build "${mods[@]//\//.}" --wfail
for f in "${src[@]}" Audit/Cycle336*.lean; do
  lake env lean --trust=0 -DwarningAsError=true "$f" || exit
done
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle336/axiom-index.lean
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle336/statement-index.lean
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle336/exact-source-readback.lean
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle336/dependency-boundary.lean
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle336/no-center.lean
```

The first two commands have their shell substitution written in Bash syntax and select only the new proof modules. The individual theorem axiom and statement outputs are partitioned in axiom/statements files. The separate scoped supervisor gate uses the ordinary gate predicate with exactly the listed explicit modules in place of the enormous top-level imports.

`github-exact-replay.txt` verifies each fixed source and independent audit path byte-for-byte against its GitHub proof blob before checking that source directly. Files unchanged since the slightly earlier verified proof pin were checked against the last pin's exact blob IDs. `shadow-build.txt` compiles those same bytes in topological order with a separate Lean path, reusing older imports but no new C336 objects. `proof-tree.json` compares the exact base and proof trees, including the two I-57 frozen blobs. `proof-source-sha256.txt` lists the proof and audit source checksums, including the append-only barrel.

`dependency-boundary.txt` audits transitive types and values of the new declarative constants for forbidden raw solver/state/resolver references. `no-center.txt` rechecks with the fresh C336 objects that the selected two-node compiler fixture still has no supported literal input-center row and retains its exact fixed writes.

`diff-NN.txt` is the complete diff-only verifier output under I-57 (Audit.lean and README.md untouched, standalone audit files allowed); its scoped full-build option was not used. Exit codes are stored alongside logs.
