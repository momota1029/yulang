# R203 — Capture-fiber lineage readback

R203 repaired the test-build failure in the R202 test query by deriving `Debug` for the private `candidate_extrusion::Key` used at an existing test diagnostic. This changes no inference behavior.

## Validation

One targeted invocation completed successfully:

```text
RUSTC_WRAPPER= CARGO_TARGET_DIR=target/r203-capture-lineage cargo test -q -p yu-solver --features shadow-apply-candidate --lib relay_capture_snapshots_join_existing_bound_emissions_and_source_sets -- --nocapture
exit: 0
1 passed; 0 failed; 0 ignored; 731 filtered out
```

Captured output hashes:

- stdout: `1ea73295dca2687d045623a5ec6b4891befbef873714c5b32d0dc099a6b389b7`
- stderr: `1f97b3d3e80b42218786e48198dc4a535de6065b00d050cc494b2a1f967b9efe`

## Readback

Each listed Capture snapshot joined to a retained bound admission and a physical bound emission whose readback matched the bound key and physical slot:

| Relation | Captured bound | Source events | Checking occurrences | Admission / emission | Coverage bits |
|---:|---|---|---|---|---:|
| 53 | Effect(29) −≤ Effect(9) | none | none | admission 48 / emission 45; physical slot read back | 120 |
| 56 | Effect(23) −≤ Effect(12) | none | none | admission 51 / emission 48; physical slot read back | 56 |
| 57 | Effect(12) −≤ Effect(23) | none | none | admission 52 / emission 49; physical slot read back | 56 |
| 62 | Effect(12) −≤ Effect(29) | event 1 | occurrence 13, local slot 0 | admission 55 / emission 52; physical slot read back | 56 |

The records establish a fixture-specific join from Capture snapshots through admission and physical emission. They do not authenticate complete construction coverage: all four coverage masks are nonzero. Only relation 62 carries a source event in this readback; relations 53, 56 and 57 have no event IDs. This is the concrete remaining source-lineage gap for applying the fixture to R183. It does not establish a universal negative for other routes or fixtures.

The test passed with existing dead-code and private-interface compiler warnings. The `Debug` derive is the only `candidate_extrusion.rs` change. No production inference path changed.
