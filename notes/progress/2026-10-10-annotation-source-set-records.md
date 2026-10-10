# Annotation source-set records checkpoint

Status: partial implementation checkpoint for the Authoritative contextual
attachment gate; source admission and executable filter behavior are unchanged
Baseline: `9ccc99fc0`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–4, 6; approved attachment grouping in §3.1

## Change

Written closed covariant annotation views retain source attachment-set
metadata: exact owner and occurrence, ordered resolved members, stable member
ordinals, composed polarity, and lexical scope. Admitted covariant mixed-tail
views now retain the same source record independently of `closed_weight`,
which remains absent for those rows. Thus source identity survives a symbolic
tail without making a mixed row executable as a closed filter. Operation views
still receive no attachment record. Omitted rows retain the existing closed
filter behavior without a written attachment record.

Copying creates fresh payload identities while preserving source metadata and
resolved member order. Existing per-use remapping shares a copied view within
one freshening operation. Payload and ordinal capacities participate in the
retained-byte meter and rollback. No endpoint, filter, or source-admission
behavior changed; no negative concrete row or nonempty operation was admitted.

Explicit negative empty rows remain outside this checkpoint: the existing
constructor returns their leaf before creating a view. Retaining a detached
empty-set record without creating an executable view needs a separate source
record owner. This is the next bounded attachment-record task.

## Review and verification

Selected mode: M3, because the attachment identity and effect-authority
boundary cross source construction, copying, filter eligibility, accounting,
and rollback. The closed-view foundation received three full reviews, then the
mixed-row repair received three independent delta reviews:

- compiler-referee: PASS for mixed source-record retention and unchanged
  executable filter behavior;
- spec-auditor: PASS for the repaired mixed-tail omission; negative explicit
  empty-row retention remains a stated residual;
- performance-auditor: PASS, with O(k) member/ordinal work and storage per
  constructed or copied view with k concrete members.

Focused verification passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests --offline --jobs=1 -- --test-threads=1` — 27 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests::union_tail_preserves_flow_and_cached_effect_and_function_roots_replay_future_conflicts --offline --jobs=1 -- --test-threads=1` — 1 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation --offline --jobs=1 -- --test-threads=1` — 17 passed.
- `git diff --check` — passed.

No broad suite or benchmark ran. Static complexity and accounting review did
not require timing evidence; measurement budget consumed was zero processes and
zero samples.

## Remaining gate

Next, retain source identity for explicit negative empty rows without creating
an executable view or changing endpoints. Then continue the coupled operation
carrier, exact relation lifecycle, and two-cycle certificate invalidation,
withdrawal, rollback, and retry work. Keep recursive nonempty contexts
unreachable until that lifecycle gate closes. General mixed-component
termination, complete Call, full effect hygiene, soundness/principality,
ordinary/default/public inference, and F5 retirement remain open.
