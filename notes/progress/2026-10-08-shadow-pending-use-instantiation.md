# Shadow SCC pending use-instantiation carrier

Date: 2026-10-08
Baseline: `2569c0182e2c562d176c837b4d60e0ee693d8c02`
Status: compiler-referee reviewed M1 structural slice; no findings
Authority: user-approved default-off shadow lane; no semantic or production authority
Review: compiler_referee PASS on the following frozen content hashes:

- `crates/yu-solver/src/shadow_scc.rs`: `b9f14fa8f6e7301014b39496f6992f99fa15ec5587ee497ef9e37bcee1d37d57`
- `crates/yu-solver/src/tests/shadow_scc_observer.rs`: `6b05bdfb5d438dd08189b2ea7912dcaa5a8e627858f9bb33ccd9aec91b6b6afe`
- `crates/yu-solver/src/tests/shadow_f5.rs`: `07f3b5fd3cf8bcf64e977f2bb4b8ee2db1a3a60c256c0a2ff63de5c7b8693bff`

## Change

Added a borrowed `PendingUseInstantiationRef` that joins one existing SCC use
to its retained parent and target definitions, the target component, the
finalized current scheme, and the existing pending generalization carrier.
The view is compiled only with `shadow-f5` and `shadow-scc-observer`.

It carries three unconditional unresolved premises: successor generalization,
current-to-successor Q/R correspondence, and use-time shared-contract
transport. Internal recursive uses, absent source skeletons, and empty current
Q/R inventories leave these premises pending. The carrier does not create a
generalized interface, manufacture a lexical dependency edge, or change
solver behavior.

## Evidence

Tests distinguish multiple UseIds that share a target/component/current
scheme; retain empty Q/R inventories and absent skeleton metadata; exercise
internal recursive uses; reject foreign or missing identities; and verify
observer counters remain unchanged. The existing test-only same-session
fresh-capture trace is joined through the carrier to Q/R kind/ordinal and
fresh-row evidence, without treating it as successor instantiation evidence.

Checks run at the frozen implementation:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5,shadow-scc-observer --lib shadow_ -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver
rustfmt --edition 2024 --check --config skip_children=true crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs crates/yu-solver/src/tests/shadow_f5.rs
git diff --check -- crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs crates/yu-solver/src/tests/shadow_f5.rs
```

The focused feature-on run passed 29 tests (444 filtered); the feature-off
solver check, targeted formatting and whitespace check passed. Verification
used one Cargo process at a time, two build jobs, and one test thread. No
benchmark or broad suite was run. Performance measurements were not taken;
the API exposes borrowed handles through existing lookups and adds no solver
traversal or allocation by design, subject to future usage-path review.

## Review boundary and next step

The independent compiler-referee review passed the three implementation/test
files. It checked collection branding, endpoint joins and failure paths,
premise persistence, same-session evidence limits, test nonvacuity and
unchanged production routing.

Current SCC identity, member scheme and observed fresh rows remain historical
evidence for the existing solver. Successor generalized-interface ownership,
Q/R mapping, use-time contract transport, source-profile lifecycle and
production inference correspondence remain unresolved. The next shadow slice
must replace only premises whose corresponding theorem/rule has been
adjudicated; no production inference path is enabled here.
