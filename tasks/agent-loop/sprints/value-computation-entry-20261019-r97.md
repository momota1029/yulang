# R97: finite §21 Value/Computation entry contrast

Status: ACTIVE; six-cell candidate source/runtime evidence matrix.
Primary: Luna `/root`. This does not adopt implementation behavior as language semantics.

## Fixed experiment and falsifiers

Add one uniquely named test to `tools/inference-playground/tests/runtime_control.rs`, using existing helpers and no production change. Compare these three source formal shapes:

- `ignore x = 9` — implicit Value(A);
- `ignore (x:int) = 9` — explicit Value(Int);
- `ignore (x:[] int) = 9` — explicit Computation(empty, Int).

For each shape, test both arguments:

1. Effectful request: `signal::ping()` under the existing `DECL`. Candidate prediction for the first two is an unhandled ping with Unit payload. Candidate prediction for the computation formal is completion with `9`, if candidate preparation accepts the source.
2. Pure recursive computation: `loop x = loop x` and `loop ()`. Candidate prediction for the first two is finite-fuel exhaustion; for the computation formal, completion with `9`.

The six outcomes are falsifiable predictions, not language rules. A CandidateError/conflict for the `[] int` plus `signal::ping()` cell is a recorded source-type compatibility observation and fails the whole matrix as contracted; do not remove or rewrite that cell. Any flipped role, eager execution before receiver entry, missing outward request, unexpected completion/exhaustion, parser/runtime preparation failure or dependency drift stops R97. No repair/retry.

## Proof obligation

For the six exact sources, derive the source-owned role from the outer formal annotation, original binder and annotation identity, whole inert argument construction, and consumer path to ValueEntry or Computation binding. Bind independent source and runtime consumers: parser/LocalSource and candidate source formation; RuntimeProgram role/schema; Machine invocation and entry. State all unobserved paths until Luna's one run. This contributes only a finite ordinary-entry lemma that may support the method/role work when an authentic executable binder is preserved. It does not establish method-member production, typing, lookup, dispatch, role-call compatibility, full §21 theorem, divergence, effects soundness, original A/B, or semantic/production approval.

Proof note: `notes/theory/2026-10-19-r97-value-computation-entry.md`; proof handoff: `tasks/agent-loop/inbox/20261019-r97-proof.md`.

## Leases and review

- Luna primary: this contract, `tasks/agent-loop/current.json`, R97 review inboxes and closeout.
- Implementation lane only: add one new matrix test in `tools/inference-playground/tests/runtime_control.rs` and its handoff. Preserve every existing test and helper; no other files or execution.
- Proof lane only: the two proof artifacts above; no source edits, build/test/CLI or Git.
- Fresh spec reviewer before edits; after source/proof freeze, spec delta review and fresh compiler/source review. Reviewers report read-only; Luna preserves receipts.

## One verification command

After source/proof freeze and CLEAN spec delta, Luna runs exactly once:

`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_control section21_outer_annotation_selects_entry_for_ignored_arguments -- --exact --nocapture`

The one test must execute all six cells. No retry under R97.

## Budget and boundaries

Total cap 1,800 seconds: proof 600; implementation 360; spec review 180; one test command 120; compiler/source review 240; integration/closeout 300; Astra 0. No renewal/reset. Unknown inherited identities and board quarantine remain untouched; concurrency stays within six live identities.

Open hygiene fronts remain independent: ordered handler priority; wrong/sibling permission; unmatched outward request plus suspended suffix; continuation capture/resumption; static-to-runtime projection. R95 method/role source correspondence and R96 permission-owner evidence remain bounded candidates. R92 runnable effectful source remains verified to stdout `23`. Preserve all parent theorem quantifiers and adoption gates.
