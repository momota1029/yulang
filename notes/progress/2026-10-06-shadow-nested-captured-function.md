# Opt-in shadow structure for the selected captured function

Date: 2026-10-06
Baseline: `90eee6c2a686394e669d0361d825977f82a74f8a`
Status: M2 shadow implementation slice; independently spec-audited after one batched repair; production inference unchanged
Scope: exact `my apply f = { my step x = f x; step }` structural correspondence

## Authority and result

The source interpretation is the [Authoritative nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. The user's 2026-10-06 direction permits settled source structure and
identity plumbing in the default-off shadow lane while theory continues; it
does not permit production inference replacement before soundness,
principality, and source adequacy close.

The `yu-hir/shadow` projector now represents this one source shape as an outer
`Lambda`, sequential `Bind`, local `Lambda`, ordinary `Apply(f,x)`, and final
`Use(step)`. Binder and use identities are artifact-branded; the local closure
records the same outer `f` binder as a lexical capture. Validation checks
sequential visibility, captured-scope membership, and parameter non-escape.
The recognizer requires the named `apply` / `f` / `step` / `x` roles and `my`
visibility on both binding headers. Formatting trivia may vary. Renamed roles,
`our`/`pub` bindings, and adjacent block forms remain unsupported.

The call still carries pending callable-role, full Function-membership, and
call-view-realization premises. Closure correspondence remains pending for
typed capture transport, provider/receiver realization, and semantic/source
discharge. The shadow structure does not invoke the returned `step` function.
`yu-core/shadow` re-exports the pending correspondence so an opt-in consumer
can inspect it. Production HIR, solver, and inference routing are untouched.

## Review and verification

The first frozen review round found two scope leaks: renamed identifiers were
accepted and binding visibility keyword tokens were ignored. Both findings
were accepted and repaired in one producer pass. The repaired recognizer pins
the approved names and `MyKw` token at both headers, with negative cases for
renames and `our`/`pub`. A fresh spec auditor found no remaining BLOCKING,
major, or minor issues in the exact-candidate delta, including the public
shadow facade. The new variants were also confirmed to remain unavailable to
the existing source-core differential consumer.

Checks passed:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-hir --features shadow --lib shadow -- --test-threads=1` — 26 passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo check -p yu-core --features shadow` — passed.
- `rustfmt --edition 2024 --check crates/yu-hir/src/shadow.rs crates/yu-hir/src/tests/shadow_source_core.rs crates/yu-core/src/shadow.rs` — passed.
- `git diff --check` — passed.

No performance measurements or broad/workspace checks were run. This slice
does not establish exact production-program acceptance, typed call-view
formation, capture/evidence transport, receiver activation, a solved scheme,
soundness, principality, source adequacy, or production inference behavior.
The next proof target remains the missing typed capture-attachment judgment
under an independently supplied original Q-independent contract/receipt.
