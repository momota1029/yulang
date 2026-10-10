# Dormant source-owned context PUSH seed checkpoint

Status: reviewed M1 preparation; no live operation execution or source admission
Baseline: `6727c69a4`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–4/6; reviewed source correspondence for nonempty covariant written return
rows

## Change

An existing admitted written covariant attachment set with nonempty resolved
concrete members now retains an inline dormant unit-PUSH marker in its existing
`AttachmentSet`. The marker owns no second family or identity. A private
adapter uses the existing `LocalWeightId` as the attachment instance and the
already retained resolved members as the finite PUSH family, with count one,
zero POPs, `All` filter, and empty right word.

The adapter only constructs a detached evaluator input. It does not create a
live `ContextExpr`, relation, bound, registration, memo entry, filter result,
or source task. `candidate_context_source`, `candidate_context_execute`, and
preflight/admission do not read the marker. Closed filter eligibility and
`LocalWeight.left_word`/`right_pops` remain unchanged. No POP/output recipe or
negative formal row was added.

Existing source-weight copy/remap reconstruction preserves owner, exact source
position, composed polarity, lexical scope, and member ordinals. Each fresh
copy receives a fresh source-weight/attachment identity; one per-use remap
still shares the copy within that use. Empty, omitted, symbolic-only,
operation-declaration, inert negative-empty, and rejected concrete formal
rows gain no unit-PUSH marker.

## Review and verification

Selected mode: M1. One independent compiler-referee review passed for
eligibility, source identity, copy/remap behavior, detached-only materialization,
accounting, rollback isolation, and unchanged live dispatch.

Focused verification passed:

- `RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --lib source_unit_push --offline --jobs=1 -- --test-threads=1` — 3 passed.
- `RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --lib detached_ --offline --jobs=1 -- --test-threads=1` — 8 passed.
- `git diff --check -- crates/yu-solver/src/candidate_context.rs crates/yu-solver/src/candidate_context_tests.rs` — passed.

The inline marker adds no separate heap buffer; existing `LocalWeight` capacity
accounting includes it. Detached materialization performs fallible allocation
for the copied atom vector, entry vector, and exact count limb. No broad or
non-test build, allocation-failure injection, benchmark, or timing sample ran.

## Remaining gates

The source seed is not consumed by live relations. Relation-sensitive
completion, Function-port transforms, checked filter ownership/discharge,
context transport and per-use freshening, residual/gamma consumers, and exact
two-cycle certificate invalidation/withdrawal/rollback/retry remain required
before recursive nonempty contexts can be admitted. General mixed-component
termination, complete Call, full effect hygiene, soundness/principality,
ordinary/default/public inference, and F5 retirement remain open.
