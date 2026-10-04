# Intrusion transport test gate follow-up

Date: 2026-10-05
Status: reviewed focused test-only differential expansion; no production routing
Governing design: [experimental SCC-intrusion transport](../design/2026-10-04-intrusion-experimental-transport.md)

## Added checks

`crates/yu-solver/src/tests/intrusion_transport.rs` now checks malformed
caller-supplied partitions for incompleteness, overlap between member locals
and anchors, and unknown identities. It also rejects duplicate identities in
a receiving namespace before returning use overlays.

The allocation-failure test walks `FaultInjection::fail_after` through every
explicit check point in parent construction and two-use construction for the
Identity, Terms, Bounds, Evidence, and UseViews lanes. Each injected failure
returns only `AllocationFailed`; source and parent inputs remain equal to
snapshots. A dedicated case fails after the first use overlay has been
constructed locally and while the second is being prepared, checking that no
partial vector escapes. This covers explicit simulated failure points, not
every actual allocator `try_reserve` site.

The first focused run found a test expectation error: it assumed six Identity
fault checks per overlay, but the current constructor has three (`public_map`,
identity list, and `Graph::renamed`). `fail_after(Identities, 6)` therefore
completed both overlays. The test now uses `skip=3` to fail at the first
Identity check for the second overlay. The invariant and expected `Err` result
did not change. Independent spec_auditor review confirmed this is an
incidental injection count correction and found no remaining issue.

## Verification and limits

```text
rustfmt --check crates/yu-solver/src/tests/intrusion_transport.rs
  pass
RUSTC_WRAPPER= cargo test -p yu-solver intrusion_transport
  8 passed; 429 filtered out
```

The workspace-wide `cargo fmt --check` was also attempted and reported
pre-existing formatting diffs in unrelated workspace files. No files from
those diffs were changed. No workspace tests, builds, or performance
measurements were run. This remains the authorized `cfg(test)` graph-transport
model with caller-supplied identity partitions; it proves neither source
partition adequacy nor permission for production inference routing.
