# Shadow SCC to closed-scheme identity join

Date: 2026-10-06
Baseline: `5104e1f34567adc874a981679a96b6ef49b6a319`
Status: implemented, focused checks passed, compiler-referee reviewed
Authority: user's default-off shadow/experimental implementation authorization; no new semantic authority
Mode: M2, default-off cross-module identity plumbing

## Change

The shadow SCC observer can now join a collection-branded
`SccDefinitionRef` to its exact already-finalized current `ClosedSchemeRef`.
Under the joint `shadow-f5` and `shadow-scc-observer` feature gate,
`SolvedModule` retains the existing collection artifact token. The lookup
checks that the topology batch, definition and solved module carry that same
token, resolves the retained definition root from the batch index, and then
uses `ClosedSchemes::for_root`. Foreign collection, missing identity and
foreign root have distinct errors.

This is identity/provenance observation only. Q/R remain local to the exact
current closed scheme; no successor generalized-interface identity,
`beta/Slots(beta)`, source licensing, call-view judgment, or production
inference behavior is introduced. If a source member has no shadow skeleton,
the existing structural crosswalk still reports absence.

## Review and verification

An independent compiler referee found no blocking, major or minor issue in the
three changed paths. The review checked collection-brand soundness, exact root
ownership, feature guards, side effects/counters, and claim boundaries. It did
not certify successor semantics, productive recursive-R correspondence, or a
broader compiler property.

Checks passed sequentially:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-scc-observer
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-f5
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-f5,shadow-scc-observer shadow_scc_observer -- --test-threads=1
```

The focused test run passed 11 tests; 449 unit and 2 integration tests were
filtered. Scoped `rustfmt --check` on the shadow files and `git diff --check`
passed. A `lib.rs` formatting check encounters existing unrelated formatting
drift; this change's four lines are cfg field/initializer entries, and no
workspace formatting was applied. The initial Cargo wrapper attempt was denied
before compilation; the clean-wrapper retry passed. Final compile time was
2.51 seconds, one Cargo process, one build job and one test thread. No
benchmark, broad suite, Oracle execution, semantic comparison or production
test was run.

The tests cover the unary Lambda to current scheme/Q identity join, cloned
collection identity, rejection of independent collections over equal HIR
roots, missing identity, mutual-recursive SCC scheme lookup while preserving
absent skeleton correspondence, and unchanged observer counters. This is not a
differential inference comparison.

## Remaining gates

The existing tests do not establish productive recursive R/use-time
freshening identity correspondence for successor schemes. They also do not
prove that current generalization, Q/R selection, recursive discharge, source
profiles, soundness, principality or source adequacy match the successor
theory. Production inference remains untouched. Those gates stay open.
