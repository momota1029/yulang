# R202 — Capture fiber lineage readback

Status: query implementation written in test-only code, but no test execution result. The targeted compile failed before the test body ran. No candidate lineage claim is made.

## Scope and changes

The readback adds a `#[cfg(test)]` accessor that follows an existing relation's source-set ID to the stored event IDs, plus one test-only R187 relay fixture query. It allocates no new solver state and adds no production API. The query would compare exact Capture snapshot `(BoundKey, relation)` keys with retained admissions and emissions, then resolve relation source-event IDs through the existing checking-occurrence index.

## Execution receipt

One invocation was made:

```text
RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --lib relay_capture_snapshots_join_existing_bound_emissions_and_source_sets -- --nocapture
```

Cargo exited 101 during compilation, before the new test ran. The blocking diagnostic is in the pre-existing `candidate_extrusion.rs:327` test-only format path: private `Key` is formatted with `{:?}` but does not implement `Debug`. Driver output SHA-256: `abc245e226daf3a5c518210bd36be89716fb95ea0dfa4f86c013a3ef0c6a014c`. The contract prohibited a retry, so there was no second invocation. `target/r202-capture-lineage/` was removed. The new accessor/test source remains unverified until the compile blocker is repaired and a fresh bounded validation is authorized.

No relation-specific source event, admission, emission or Capture result is claimed. R183 and all parent/A/B/source-native/production gates remain OPEN. R202 closed after this pre-test compile failure; no carryover.
