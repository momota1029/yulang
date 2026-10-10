# Negative empty attachment provenance checkpoint

Status: inert provenance checkpoint within the Authoritative contextual
attachment gate; annotation endpoints, filter behavior, and source admission
are unchanged
Baseline: `3db789357`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–4, 6; approved attachment grouping in §3.1

## Change

Admitted whole and local annotations now retain an inert bundle for written
negative `[]` rows. Each set records its owner, exact row position, composed
polarity, and lexical scope. One bundle is shared across the annotation's
paired signature construction and is associated with both source checks and
the slot-41 publication origin. The existing empty-effect leaves remain the
result; the bundle creates no view, bound, context expression, filter, or
executable attachment. Omitted rows, operation signatures, and rejected
negative formal rows remain outside this registration.

Captured graphs retain bundle provenance on reachable relation fibers, with a
per-use map that shares copied identity within one reconstruction and separates
independent uses. Fresh-use transports carry the copied bundle without
back-propagating it into the template. Bundle identities remain outside
relation keys and endpoint equality.

The first implementation review found global edge/incidence scans with
quadratic worst-case work. One batched repair replaced them with relation-local
incidence chains, existing diagnostic successors, and a lazy index for eligible
zero-use transports. Captured graphs store sparse relation spans so capture
and reconstruction visit only relevant bundles. A session that never uses
bundle provenance allocates no transport index.

Rollback covers bundle records, source links, incidence heads, lazy index
activation and additions, and captured graph data. Retained capacity is
accounted. The indexed implementation does not traverse behind existing
nongeneric capture boundaries.

## Review and verification

Selected mode: M2, a private provenance and capture representation with no
change to inference behavior. After the indexed repair:

- compiler-referee: PASS for source ownership, relation propagation, capture
  boundaries, fresh-use isolation, and rollback;
- performance-auditor: PASS. The former global O(E·I), O(B·I), and O(B·J)
  scans are closed. Propagation now visits actual successors/incidences after
  one O(D) dependency-index activation scan on first use; capture is O(B+J),
  and reconstruction is O(B+L) after per-use remapping, where L is the number
  of applicable bundle references.

Focused verification passed:

- `RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests --offline --jobs=1 -- --test-threads=1` — 34 passed.
- `RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation --offline --jobs=1 -- --test-threads=1` — 17 passed.
- `git diff --check` — passed.

No broad suite or benchmark ran. Static complexity and structural visit-count
tests resolved the performance question, so measurement budget consumed was
zero processes and zero samples. Actual workload incidence distributions and
peak allocation remain unmeasured.

## Remaining gate

This metadata checkpoint does not execute nonempty operations or close the
contextual relation lifecycle. Next, implement the private finite operation
evaluator while keeping nonempty contexts disconnected from source-derived
tasks; then integrate source construction, relation-sensitive completion,
transport/freshening, and the approved two-cycle certificate invalidation,
withdrawal, rollback, and retry gate before any recursive nonempty context can
be admitted. General mixed-component termination, complete Call, full effect
hygiene, soundness/principality, ordinary/default/public inference, and F5
retirement remain open.
