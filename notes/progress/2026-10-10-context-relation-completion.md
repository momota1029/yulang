# Relation-sensitive contextual completion checkpoint

Status: reviewed M2 implementation slice; nonempty source operations remain
disconnected
Baseline: `f2e0031cd`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–6, especially the exact relation identity, task admission, SCC generation,
and rollback requirements in §§4–5

## Change

Candidate completion is now recorded by the admitted `RelationId` and SCC
generation, rather than by endpoint pair and generation. Distinct contextual
relations over the same component/endpoints therefore have independent
completion, while the existing typed-pair diagnostic memo continues to own
pair diagnostics. Exact duplicate relations may still be suppressed within the
current generation. Context execution remains before completion suppression
and endpoint equality handling.

Raw aliases retain their own diagnostic memo without completing the canonical
relation. A canonical work item completes that relation only when it performs
the canonical semantic step. Relation completion and its undo journal use the
smaller relation key and retain capacity accounting. SCC generation changes
invalidate the relation completion; route rollback restores both the generation
and completion entries.

The first review found a raw-alias case that could mark a canonical relation
complete after SCC invalidation, before canonical replay. The batched repair
kept raw diagnostic admission separate from semantic completion. A fresh
regression-auditor delta review passed the repair. The old closed-filter path
and dormant source unit-PUSH marker remain unchanged; no source-derived
nonempty operation or formal-row admission was enabled.

## Verification and resource notes

Selected mode: M2, one compiler-referee review and one fresh regression-auditor
delta review after repair. No timing samples were taken.

Focused checks passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests --offline --jobs=1 -- --test-threads=1` — 45 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests --offline --jobs=1 -- --test-threads=1` — 7 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests --offline --jobs=1 -- --test-threads=1` — 27 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests::raw_alias_diagnostic_admission_cannot_complete_invalidated_canonical_relation --offline --jobs=1 -- --test-threads=1` — 1 passed.
- `RUSTC_WRAPPER= cargo check -q -p yu-solver --features shadow-apply-candidate --offline --jobs=1` — passed without warnings after making the test-only identity lookup test-only.
- `git diff --check` — passed for the scoped implementation and record changes.

No broad solver/workspace test suite, allocation-failure injection, non-candidate
build, or benchmark ran. Completion storage and undo storage scale with exact
relation count; the key is smaller than the former typed-pair key.

## Remaining gates

Contextual transport and per-use freshening remain open across operation DAGs,
payloads, capture, extrusion, and qualifying intrusion. Function argument
`swap`, result preservation, source-certified inferred-entry `both`, checked
filter discharge, residual/gamma feedback, and complete two-cycle certificate
invalidation/withdrawal/rollback/retry are still required before recursive
nonempty contexts can be admitted. General mixed-component termination,
complete Call, full effect hygiene, soundness/principality, ordinary/default/
public inference, and F5 retirement remain open.
