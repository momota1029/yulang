# Shadow lexical capture-use incidence

Date: 2026-10-06
Baseline: `2667a46b0`
Status: M2 shadow implementation slice; independently spec-audited with no findings
Scope: exact `my apply f = { my step x = f x; step }` candidate

## Result

The default-off `yu-hir/shadow` skeleton now exposes a read-only
`CaptureUseIncidence` for the selected nested function. It links the local
Lambda expression, the captured outer `f` binder, the exact callee `UseId`,
and the retained `IdentifierExpression` position. Validation checks that the
links agree with the existing lexical capture and `f x` application, rejects
missing or inconsistent incidences, and preserves the artifact-branded IDs.
The `yu-core/shadow` facade exposes this structural record.

This records lexical source incidence only. It does not attach a typed receipt
or evidence environment, form `beta`/`Slots(beta)`, create a typed path or
`Flow`, identify a provider or receiver, or discharge call semantics. The
closure correspondence and callable-role, Function-membership, and call-view
premises remain pending. Production HIR, solver, and inference routing are
unchanged.

Authority is the [Authoritative nested-block source interpretation](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3 and the user's shadow-lane authorization recorded in
[`tasks/current.md`](../../tasks/current.md). Frozen Oracle evidence is not an
authority for this structure.

## Review and verification

An independent `spec_auditor` inspected the frozen three-file delta, its direct
projection/validation paths and feature facade against the approved candidate
scope. The review found no blocking, major, or minor issues. It confirmed that
semantic transport and activation remain pending and that the narrow source
recognizer and production routing are unchanged.

Focused checks passed:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-hir --features shadow --lib shadow -- --test-threads=1` — 27 passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-core --features shadow --test shadow_feature -- --test-threads=1` — 3 passed.
- Scoped `rustfmt --edition 2024 --check` and `git diff --check` — passed.

No broad workspace check, runtime closure validation, inference parity,
performance measurement, source-adequacy proof, principality proof, or
soundness proof was run. The source producer must still derive the typed
evidence-environment attachment and captured-name lookup correspondence from
the original Q-independent contract; later receiver realization remains a
separate obligation.
