# Shadow identity crosswalk — round 15

Baseline: latest pushed `origin/research/simple-sub-intrusion` at
`b6e566936308aeac78d30cf497a6e617c2a7d0e9`.

The existing `my id x = x; pub public_alias = id` shadow fixture now follows a
single retained construction path across the current solver:

```text
HIR parameter identity and exact source position
  → captured historical startup row
  → target scheme's unique origin binder
  → incoming use's fresh row for that scheme-qualified binder
  → receiving public-alias scheme's unique origin binder
```

The test checks the startup row differs from the incoming fresh row, repeated
observations preserve row identity, independent solves have distinct brands,
and the receiving binder belongs to the alias's distinct scheme owner. The
ordinary and shadow solver diagnostics and counters remain compared in the
existing fixture. The `pub` marker is retained metadata only; the test makes no
export-eligibility or semantic-incidence claim. Successor eligibility,
source-to-scheme correspondence, and recursive principal-view premises remain
unresolved.

Compiler-referee review and delta review passed. The targeted integration file
passed all three tests with `shadow-f5` and `shadow-scc-observer` enabled. No
production solver path changed and no DAG node status changed.
