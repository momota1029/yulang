# Authoritative: G4b E5 index-call control correction

Status: Authoritative

Scope: the successor rewrite's isolated G4b E5 index witness only.  This
corrects neither production dispatch nor unrelated Yumark adoption rows.

Approved-by: user

Approved-at: 2026-09-03

Supersedes: only the successor-rewrite application of the E5
`x[a b]` `IndexSeparator` Missing witness in
`2026-09-02-yumark-gate3b-recovery-adoption-matrix.md`.

## Decision

The E5 index-call control is `x[a(b)]`.  Its bracket content is one
`IndexItem` whose `a(b)` is an ordinary nested `CallTail`; it does not publish
an `IndexSeparator` recovery.  The older `x[a b]` row is not a successor
rewrite separator contract and must not be retained merely to preserve a
matrix spelling that contradicts the direct expression-item grammar.

This correction preserves the existing direct Item handoff: accepted `(` is a
tail of `a`, its nested call owns its own `)`, and the surrounding index owner
then owns the same `]` boundary.  It adds no parser-local state, delimiter
stack, cache, or legacy-parser bridge.

## Verification boundary

Focused G4b evidence asserts one `IndexTail` containing one direct
`OperatorChain` item with an inner `CallTail`, lossless CST, no
`IndexSeparator` recovery, and exact `]` ownership.  Existing E5 leading-item
and missing-bracket controls remain separate.
