# Structured-recovery extent-validation addendum

Status: Authoritative

Date: 2026-09-07

Drafted-by: primary after compiler/recovery finding

Reviewed-by: M3 compiler/recovery, specification, and performance delta review
on 2026-09-07

Approved-by: user

Approved-at: 2026-09-07

Scope: the `RewriteOutput` structured-reservation completion check used by the
first O3a polymorphic-variant tag-name caller; this addendum does not authorize
that caller or any public cutover.

Depends-on:

- `2026-09-07-successor-structured-recovery-reservation-amendment.md`;
- `2026-09-06-successor-typed-output-recovery-amendment.md`.

Supersedes: §§3, 5, and 8 of
`2026-09-07-successor-structured-recovery-reservation-amendment.md` only where
they leave the structured Error range supplied by a grammar caller without an
independent emitted-extent check.

## 1. Finding

The approved reservation amendment requires a complete structured Error record
after a total nested body, but its conceptual helper accepts caller-supplied
`start` and an exact returned end. That form allows a faulty grammar caller to
commit a nonempty range that is not the range of the tokens emitted inside its
Error node. Rowan construction alone cannot validate this correspondence.

The defect is concrete: a nonzero coordinate error, pre-emitted payload, or
fragmented UTF-8/CRLF token boundary could make a syntactically valid CST and
an invalid recovery record agree only by caller assertion. The compiler/recovery
review therefore rejects completion until an independent extent check exists.

## 2. Decision

`RewriteOutput` gains one monotonic `usize` byte counter. Its sole token
forwarder performs one checked `text.len()` increment before forwarding every
token to the existing Rowan builder. This is builder metadata, not retained
source: it stores no root source, Item range, fragment coordinate, event log,
buffered token, or replay state.

A structured reservation snapshots that counter at begin. Completion requires
the nonempty explicit recovery range length to equal the checked delta between
the current counter and that snapshot. A nested reservation snapshots later,
so its delta is a subset of the enclosing reservation's inclusive delta.
Ordinary Missing nodes emit no token and add zero bytes. Overflow or mismatch
invalidates the current output under the existing panic/rollback boundary.

The private grammar-facing helper accepts the moved primary `Item` and the
threaded successor origin rather than an unsealed raw start. It derives the
start from that Item's checked `ItemExtent` and rejects a primary Item that
still has physical leading parts. Thus caller-owned direct leading must be
emitted before the Error opens, while its byte count is excluded from the
reservation snapshot. The total nested body still returns the exact end using
the existing successor-coordinate handoff; that end must satisfy the counter
delta check before the reserved slot becomes complete.

The affine reservation token, slots, and helper remain private to output code.
No source/range state is added to `Item`; no second builder, CST walk,
insertion, sorting, source replay, or diagnostic transaction is introduced.

## 3. Cost and bounds

Valid input still has no recovery slot allocation, recovery extraction, new
traversal, or second builder. It now has exactly one checked byte-length update
per emitted token in the already-inline token forwarder. Recovered input keeps
the approved `O(R)` slot storage and consuming final extraction, and adds only
constant state per active reservation; begin and completion stay `O(1)` apart
from existing evidence comparison.

Static performance review found no allocation, clone, scan, lookup, dynamic
dispatch, or asymptotic change. Its timing budget is zero samples because no
material runtime uncertainty remains.

## 4. Evidence and boundary

The output-infrastructure tests must cover nonzero origins, pre-emitted bytes,
fragmented UTF-8 and CRLF/Yumark token sequences, nested reservations,
zero-byte Missing nodes, fresh and frozen endpoint mismatches, remaining
physical leading rejection, LIFO completion, overflow, and final extraction.

This addendum authorizes only the extent-validation prerequisite after user
approval. It does not authorize the O3a PV wrong-kind caller, broader Type/PV
migration, public dispatch, or legacy-parser removal.

## 5. Rejected alternatives and approval record

Rejected alternatives are trusting a raw caller `start`, deriving range by a
post-hoc CST walk, retaining source/ranges in `Item`, buffering/replaying
tokens, using a second builder, or skipping validation for nested recoveries.

User approved the counter, Item-derived start seal, and exact emitted-byte-delta
validation described above on 2026-09-07, limited to structured reservations.
