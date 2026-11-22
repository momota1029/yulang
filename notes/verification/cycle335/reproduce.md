# Reproducing C335 verification

Proof source pin: `293360074691286b8398007782d3292d5f0ea7d0`. Starting work pin: `8c712916a4a7cb86398a3e6ece943585bb25fa99`. Use Lean 4.35.0. The commands below are scoped to the declaration and ordinary readout proofs; they are not a complete repository build.

From `lean/`:

```bash
mapfile -t src < ../notes/verification/cycle335/modules.txt
mods=("${src[@]%.lean}")
lake build "${mods[@]//\//.}" --wfail
for f in "${src[@]}" Audit/Cycle335*.lean; do
  lake env lean --trust=0 -DwarningAsError=true "$f" || exit
done
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle335/statement-index.lean
lake env lean --trust=0 -DwarningAsError=true ../notes/verification/cycle335/exact-source-readback.lean
```

`build.txt`, `source-status.txt`, `audit-status.txt`, and `Cycle335*.txt` record the outputs. The ordered independent audit logs and SHA checksum list describe exactly this proof pin. `github-exact-replay.txt` records the fixed GitHub paths byte-for-byte verified and replayed. `shadow-build.txt` records an additional independent Lean replay: none of the new C335 compiled objects was reused. We fetched the same 31 exact source and audit files, compiled the new source modules in topological order with direct `lean --trust=0 -DwarningAsError=true --root=<shadow source> -o <fresh library>/Yulang/<module>.olean`, and checked the eight audits against those fresh objects. Prior imports used the retained checkout's objects; this was not a cold rebuild of prior work.

`diff-NN.txt` together contain the complete I-57-compatible diff-only checks; `diff-status.txt` is the exit. Its full-build mode was intentionally not invoked. `proof-tree.json` compares the GitHub starting and proof trees' full path scope and blob hashes, including separately confirming the frozen Audit and README. `axioms-NN.txt` contains all individually indexed theorem axiom checks. `scoped-gate.txt` records the supervisor's gate with the 23 explicit C335 imports in place of the all-repository barrel. `declarative-dependencies.txt` checks the isolated ordinary literal compiler/witness transitive type and value dependencies against the forbidden physical solver/state/whole-resolver boundary. The actual projection modules intentionally import the raw source machine. No compiled files, credential material or changes to tooling were published.
