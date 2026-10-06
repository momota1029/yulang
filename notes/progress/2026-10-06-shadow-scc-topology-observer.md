# Shadow observer for existing SCC topology

Date: 2026-10-06
Baseline: `ae9ff327285a625b02a99fe85a5cae14579de250`
Status: default-off experimental observation; spec and regression review complete
Claim class: borrowed view of existing current F0–F2 topology
Implementation authority: shadow identity/evidence plumbing only

## Result

`yu-solver/shadow-scc-observer` exposes an opt-in borrowed `SccTopology` view
over the immutable `SccPlan` already frozen by `ConstraintBatch::collect`.
The view reports dependency-first components, branded definition handles,
member sets, and existing internal/incoming resolved-use handles. Its queries
borrow the plan directly and leave the observable `ProductionCounters`
unchanged. Foreign definition handles are rejected by the existing collection
artifact check.

This is current F0–F2 topology observation. It does not connect solver IDs to
the independently branded HIR shadow IDs, create a successor component, or
provide a generalized interface. Q/R, recursive identity, use-time
freshening, solving, and production inference remain untouched. The source
correspondence and generalized-interface fields remain explicit open gates.

## Review and focused verification

Independent spec review found no conformance findings. Independent regression
review requested order and handle coverage; the repaired test now checks
dependency-first component/member order, the `definitions()` plan order,
canonical/member identity, successful and foreign `component_of`, distinct
internal-use identities, occurrence ordinals, and counter neutrality. Delta
review found no further required issue.

Passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-scc-observer shadow_scc_observer -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver
rustfmt --edition 2024 --check crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
git diff --check -- crates/yu-solver/Cargo.toml crates/yu-solver/src/lib.rs crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
```

The focused observer tests passed 2/2. The ordinary feature-off package check
passed. An initial formatter check also included the existing large
`lib.rs`; it reported repository-wide formatting differences in unrelated
pre-existing code. No formatter wrote `lib.rs`; checks were narrowed to the
two new files and passed. No full `yu-solver` suite, broad workspace check,
Oracle run, or performance sample was used.

## Next gates

The observer can support inspection of the existing static dependency graph.
Before joining it to successor HIR, establish a source-occurrence
correspondence without using spelling, range, or collection ordinal as
cross-artifact identity. The generalized interface schema, original Q/R
identity/freshening, and all soundness, principality, source-adequacy, and
production-conformance gates remain open. This slice does not certify any of
them.
