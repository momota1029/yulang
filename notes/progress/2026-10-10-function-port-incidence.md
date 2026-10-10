# Function-port operation incidence checkpoint

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `980b9633a576ecfb93c2601364b404862754b1c7`
Status: reviewed inert source provenance; executable nonidentity Function
contexts and cycle certification remain open

## Authority and scope

This slice follows the Authoritative
[contextual attachment/admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
§4 Function-port contract and §§3–6. The bounded source characterization is
recorded in the [Function-port context falsifiers](2026-10-10-function-port-context-falsifiers.md).
It retains construction facts without changing current context execution,
formal-row admission, diagnostics, or language semantics.

## Retained incidence

At Function decomposition, each generated child records the exact processing
parent relation, admitted child relation, Function field, and operation kind.
Argument Value and ordinary argument Effect record `Swap`; result Effect and
Value record `Preserve`. The child still receives the existing child-local
context reconstructed by `candidate_context_admit`; this slice does not create
`Swap(I)`, execute nonidentity transforms, or authorize `BothFromRight`.

At the source Lambda owner, the exact `InferredEntryOriginId` for slot 3 now
travels directly into initial relation admission and is retained on that
relation's origin record. Slot 4 and all other source seeds pass no handle.
Written Function annotations therefore cannot acquire inferred-entry
provenance through endpoint shape or occurrence scanning.

## Review, repair, and verification

The initial M2 semantic review found no issue. A focused performance review
found a quadratic worst case in reverse-searching all retained Lambda origins
for unrelated slot-3 source constraints. The repair passed the handle directly
from the owning Lambda constructor. Fresh semantic and performance delta
reviews passed. The repair adds no index or heap allocation; source-seed
association is O(1), with no `inferred_entries` traversal in seed admission.

Focused checks:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib inferred_entry_origin -- --test-threads=1` (3 passed).
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib function_port -- --test-threads=1` (2 passed).
- `git diff --check -- crates/yu-solver/src/lib.rs crates/yu-solver/src/candidate_context.rs crates/yu-solver/src/candidate_context_tests.rs` passed.

No benchmark was run; source inspection closed the asymptotic finding. The
scoped rustfmt check reports pre-existing formatting drift in the touched
modules; only new fragments were formatted. Broad suites and other feature
combinations remain unverified.

## Limits and next gate

This is metadata/provenance only. It does not implement executable Function
context inheritance, concrete contravariant attachment construction, current
and future subtraction checks, source/legacy effect-hygiene correspondence,
`BothFromRight` authorization, exact recursive-cycle recognition, late-edge
invalidation/withdrawal, private deferral, certificate rollback, complete
Call, principality, or F5 replacement.

Next, construct the approved source-owned operations and live consumers across
Function endpoints, bounds, extrusion, freshening, and intrusion. Keep
recursive nonempty admission behind the exact two-cycle lifecycle gate. The
conditional contravariant hygiene derivation remains conditional on authentic
source attachments and their consuming checks.
