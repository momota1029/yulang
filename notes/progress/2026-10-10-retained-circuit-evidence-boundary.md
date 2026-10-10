# Retained circuit evidence boundary

Date: 2026-10-10
Status: reviewed inert-evidence implementation sub-slice; the full Packet 1
input/readiness gate remains open
Baseline: `9d4392ef4a4ef309c6c9c9194840deca3cbf6de6`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–7; no new semantic decision

## Result

`yu-solver` now exposes a borrowed `CircuitEvidence` view rooted at retained
relation IDs. Its closure follows endpoint views including `Support`, weights,
registered filter obligations, shared context children, bound incidences,
ordered replay inputs, and transport provenance. Missing references, invalid
annotation-member ordinals, mismatched relation/key incidences, and
unavailable transport authentication are reported as explicit incomplete
evidence. Fresh-use transport remains provenance-only and creates no solver
edge. The view does not execute nonidentity operations, recognize approved
cycles, mint certificates, or authorize recursive admission.

This is an implementation sub-slice, not completion of the complete retained
input contract. In particular, no readiness producer exists in this slice;
readiness and lifecycle authentication continue to prevent `Complete`.

The initial independent compiler-referee review found omitted `Support` view
closure, incomplete retained-reference validation, and private-interface
warnings. One batched repair added the missing closure and validation,
regressions for malformed and valid references, and crate-private type
visibility. A fresh compiler-referee delta review passed the exact repaired
six-file snapshot with no further finding. The final primary-only delta made
the intentionally Packet-2 `bounds` accessor warning allowance apply in test
builds too; it changes no behavior.

## Verification

Focused command:

```sh
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_context -- --test-threads=1
```

Result: 71 passed, 539 filtered; compile 17.13 seconds, tests 0.20 seconds.
`git diff --check` passed for all six changed files. The final warning-only
attribute was applied after that run; no test was repeated for this
non-semantic annotation. No broad suite, benchmark, or lifecycle check ran.

Changed paths:

- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_context_tests.rs`
- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/candidate_extrusion.rs`
- `crates/yu-solver/src/candidate_intrusion.rs`
- `crates/yu-solver/src/candidate_scheme.rs`

The complete-component recognizer, readiness production, dependent-observation
withdrawal, private publication deferral, atomic certificate rollback, source
operation execution, contravariant concrete-row admission, and production
cutover remain open.
