# Shadow SCC use to target scheme and F5 freshening join

Date: 2026-10-06
Baseline: `30b98e390087c57c7578822b2b8a81b266b13114`
Status: implemented, focused checks passed, compiler-referee reviewed
Authority: user's default-off shadow/experimental implementation authorization; no semantic authority
Mode: M2, default-off cross-module identity plumbing

## Change

`SccTopology::use_closed_scheme` now follows a retained
`SccUseRef` through its exact collection-owned definition-use record to the
exact target `DefinitionOrderId`, then delegates to the existing
definition-to-current-closed-scheme join. It validates the topology, use and
solved result's collection brands first. The API returns a borrowed current
scheme and does not infer source ownership, a call-view relation, or a
successor generalized interface.

A focused test composes the existing private, test-only F5 freshening capture
with the SCC use and exact target scheme from the same inference session. For
both repeated quantified uses and repeated uses of mutually recursive current
members, it checks exact use/target/root identity, Q/R kind and ordinal
inventory, session-local fresh rows and unchanged observation counters. Other
tests cover foreign collections, missing use/target identities, and internal
recursive-use target lookup while the unsupported shadow skeleton remains
absent.

Fresh-row capture remains private test instrumentation. A current SCC use can
map to a current target scheme without implying that every use has an F5
freshening route; only successfully captured incoming routes are compared.
No `beta/Slots(beta)`, source profile, receiver, receipt, or semantic
discharge is produced.

## Review and verification

An independent compiler referee found no blocking, major or minor issue in the
three changed paths. Review covered collection/use/target/root identity,
same-session capture provenance, Q/R inventory matching, row assertions,
feature gates and claim boundaries. It did not certify successor semantics,
generalization correctness, productive recursive correspondence, or
principality.

Checks passed sequentially:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-f5,shadow-scc-observer fresh_capture_routes_join_exact_scc_use_target_scheme_in_same_session -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-f5,shadow-scc-observer closed_scheme_join -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --no-default-features
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-scc-observer
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-f5
```

The composition test passed once; the `closed_scheme_join` filter passed 3
tests. Scoped rustfmt and `git diff --check` passed. Each Cargo command used one
build job and ran sequentially. No broad suite, Oracle, benchmark, or
production inference check was run.

## Remaining gates

This joins identities observed by today's collector and solver. It does not
prove the target-use edge or Q/R identity corresponds to successor source
semantics, source `beta/Slots(beta)`, or a generalized SCC interface. Current
generalization equality, recursive discharge, soundness, principality, source
adequacy and production cutover remain open.
