# R215 — Capture predecessor Effect-row readback

Status: bounded test-only observation complete. Independent review is not claimed.

## Observation

At the first Capture visit to canonical `Effect(31)` on the R187 local relay route,
the raw solver `effect_bounds[31].direct_lower_rows` snapshot was:

```text
CaptureEffectFrontierObservation {
  graph_row: 2,
  requested: Effect(31),
  representative: Effect(31),
  direct_lower_rows: [28],
  direct_upper_rows: [],
  truncated: false
}
contains_effect10=false
```

The row was visited and the bounded snapshot was complete. `Effect(10)` was not
in the raw lower-row adjacency at Capture entry. This locates the observed gap
before Capture traversal or route serialization: the source relation `Effect(10)
<= Effect(31)` recorded in R213 was not present in this candidate solver bound
adjacency at the queried point. It does not yet identify which earlier
accumulation step lost or redirected the relation.

## Verification

`RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate local_source_observation`
passed: 1 passed, 731 filtered out. A first compile attempt had failed because
two test-only `Graph` literals needed the newly added field. Cargo's passing
output captured the diagnostic line, so the same target was run with
`--nocapture`; that passed too, but the tool truncated its output. Running the
compiled test binary with the same test filter and `--nocapture` then printed the
complete R215 record above and exited 0.

Instrumentation is under `#[cfg(test)]`, bounded to 256 lower and upper row IDs
per visited effect row, and included in test graph byte accounting. No solver
decision or production behavior changed.

## Limits and next owner

This is evidence about the candidate implementation only. The original
computation-forwarding preservation theorem, source/native correspondence,
semantic approval, and production gates remain OPEN. Next inspect the path from
completed source relation 71 through source drain/relation accumulation to
`effect_bounds[31]`; do not treat this readback as theorem closure or a
production counterexample.
