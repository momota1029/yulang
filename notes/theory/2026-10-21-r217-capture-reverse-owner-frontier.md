# R217 Capture reverse-owner frontier result

## Claim class

Bounded candidate implementation observation. This is not a theorem proof,
native correspondence, semantic approval, independent review, or production
authorization.

## Result

The local same-use Capture route now indexes eligible incoming effect owners
once per Capture. The index canonicalizes both endpoints, includes only local
upper rows whose direct negative-bound edge has a completed Lambda slot-4
source Origin, and is consulted only for effect rows already reached from a
positive-boundary captured type shape. Incoming edges are fed through the
existing `Capture::bound` path. Bound-discovered owners do not recursively
expand the reverse frontier. Index, origin, and shape-row capacities are
included in Capture evidence/scratch accounting.

The R187 same-use relay assertion observes the source bound
`Effect(10), Negative, Effect(31)` in the provider Capture graph. Its derived
relation lineage reaches the retained Lambda slot-4 source Origin; Effect(10)
is local and has a fresh-use image. The test uses canonical bound keys instead
of allocation-order-sensitive relation IDs for sibling Capture observations.

## Verification

- `RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate local_source_observation` — passed, 1 matching test.
- `RUSTC_WRAPPER= cargo test -q -p yu-playground` — passed all package test binaries, including ordinary Yulang2 playground samples.
- `python3 tools/agent_sprint.py check` — passed static state/contract checks; this is not independent review.
- `git diff --check` — passed.
- Full candidate-enabled `yu-solver` package tests could not compile unrelated research examples against current APIs, as recorded in the R217 contract.
- Sequential full `yu-solver` library tests reported three `candidate_context` failures by test 77/732, then stopped making progress under continuous CPU use for over 90 seconds. The run was interrupted. No full-library pass or baseline attribution is claimed.

## Boundaries and next work

The original Simple-sub A/B claims, quantifiers, source/native correspondence,
semantic approval, expected-output protection, and independent review remain
open. This result repairs the observed candidate Capture path only. It does
not close the Lambda source-owner proof or authorize promotion.

The sprint ended without an end-of-sprint dispatcher consultation because the
user's standing instruction forbids subagents. This note creates no next
sprint or expanded lease.
