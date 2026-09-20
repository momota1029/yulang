# BracketRow close-error CST topology supersession

Status: Authoritative; construction complete (2026-09-20)

Scope: BracketRow Item/Close raw-`Error` topology only.

Approved by: user, 2026-09-20.

## Supersession

This record supersedes only the P/E-only and BracketRow-exclusion clauses of
[`2026-09-12-successor-type-delimited-foreign-close-topology.md`](2026-09-12-successor-type-delimited-foreign-close-topology.md), and the direct raw
`Error` placement rule only for the error emitted by
`retry_bracket_row_close_normalized`.

It changes no accepted grammar, P/E or Call topology, BracketRow Item error,
Missing/Separator topology, diagnostic schema, or diagnostic wording.

## Decision

```text
BracketRowItemError  := BracketRow > Error+
BracketRowCloseError := BracketRow > TypeDelimitedForeignClose > Error+
```

Reuse the existing `SyntaxKind::TypeDelimitedForeignClose`; do not add a kind
or move a discriminant. Open and finish that wrapper only around the existing
nonempty raw-Error emission in `retry_bracket_row_close_normalized`, after the
close item's leading is emitted and before successor acquisition.

Each locally consumed mismatched close owns one sibling wrapper. The wrapper
contains only that close item's unchanged `Error` leaves: no leading or retry
trivia, `Missing`, accepted `]`, returned Item, nested type, caller/outer
close, fence boundary, or successor acquisition. The wrapper itself creates no
diagnostic; its Error group is the generic CST-derived Close occurrence.

## Invariants

- Item errors remain direct BracketRow children.
- Matching `]`, protected caller/outer closes, and fences retain priority and
  remain outside wrappers.
- Close-only retry, non-close pending-Item handoff, current-Item ownership,
  UTF-8/CRLF ranges, and lossless source remain unchanged.
- Adjacent mismatched closes produce separate wrappers and separate generic
  occurrences in source order.
- No parser-private metadata, Error-text inspection, `Invalid`, or schema/API
  refinement is introduced. Generic identity/path already distinguishes the
  two roles.

## Required proof

The collision pair must become structurally distinct; repeated close,
boundary/fence, accepted-input, source-flattening, and generic projection path
tests must retain their existing contracts. Roll back if any Item error gains a
wrapper, any protected source is consumed/wrapped, adjacent closes merge, or
the two roles remain indistinguishable.

## Construction and verification

`retry_bracket_row_close_normalized` now opens the existing wrapper only around
the local close Error emission and closes it before successor acquisition.
Focused BracketRow, structural-diagnostic, and P/E topology tests pass; the
warning-free syntax test compile, full syntax library suite, and HIR suite pass
as recorded in the daily progress record.
