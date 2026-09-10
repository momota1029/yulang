# RecordPattern foreign-close CST slot draft

Status: Draft; no implementation authorization

Date: 2026-09-10

Drafted-by: primary from the CST-only diagnostic construction investigation

Scope: one proposed Rowan topology distinction for raw foreign-close recovery
inside `RecordPattern`. This draft neither changes accepted syntax, recovery
continuation, source ownership, public diagnostics, temporary recovery records,
nor the existing `RecordPatternSeparator` structured-Invalid discriminator. It
does not authorize code, fixture, API, SyntaxKind, documentation, or ledger
changes.

Governing authority: the Authoritative CST-derived diagnostics amendment and
Error/Invalid topology-ordering addendum; the Authoritative RecordPattern
separator-slot amendment; the Authoritative Pattern sequence current-Item and
delimited-slot-publication records. This draft identifies a missing owner-schema
decision exposed while cataloging their already-existing raw Error leaves.

## Problem

The CST-derived diagnostics amendment requires each raw Error-token group to
have a distinguishable grammar slot. Current RecordPattern source recovery
does not always preserve that slot in the tree:

```text
{)1}  -> RecordPattern(LBrace, Error, Invalid(Pattern(1)), RBrace)
{@1}  -> RecordPattern(LBrace, Error, Invalid(Pattern(1)), RBrace)
```

The first Error is a foreign-close recovery and has
`ClosingDelimiter(RecordPattern, Brace)` as its current temporary-record
expectation. The second is an Item recovery and has `Identifier`. The tree
cannot select either expectation without reading Error spelling or retaining
parser provenance, both prohibited by the CST-only decision. Mixed inputs can
also place close- and item-role Error leaves adjacently before the same nested
Pattern, so combining such leaves into one generic group is not sound.

This is a schema gap, not a failure of existing recovery behavior. The current
temporary records remain the compatibility evidence until the complete schema
and migration gate retire them.

## Candidate decision requiring user approval

Introduce one transparent grammar-slot node, with its durable spelling still
subject to approval:

```text
RecordPatternCloseRecovery := Error+
RecordPattern := ... RecordPatternCloseRecovery ...
                 | ... Error+ ...
                 | ... Invalid(Pattern(...)) ...
                 | ... RecordPatternSeparator(Invalid(Pattern(...))) ...
```

Only `pattern::delimited` selects this node. It wraps the raw Error emission
for exactly one consumed foreign close while a RecordPattern sequence remains
open. It identifies an interrupted close slot, not a successful close or a
new diagnostic kind.

The wrapper's range is exactly its Error-token children's combined UTF-8
range. It owns the consumed foreign close and any leading currently emitted as
part of that raw recovery, in source order. It excludes already-emitted source,
accepted local close, final Missing, retry leading, returned/protected Item,
accepted field, nested Pattern, `Invalid`, and `RecordPatternSeparator`.

Its Error-token group would derive singleton
`ClosingDelimiter(RecordPattern, Brace)`, primary alternative zero. The wrapper
itself would project nothing. A direct raw Error group remains Item recovery;
the existing structured separator wrapper continues to distinguish its own
Invalid occurrence. No Error spelling, record ID, unexpected category,
expectation-source flag, parser range, attribute, AST, side tree, or ledger
would participate.

Each consumed foreign-close occurrence would get one wrapper. Thus repeated
foreign closes are separate slot occurrences; one lexical sequence run remains
one direct Error-token group. This cardinality is a proposed semantic rule,
not an emitter-call accident.

## Alternatives not selected by this draft

- `Invalid(Error+)` would expand the existing structured-wrong-slot meaning of
  Invalid and introduce an outer Invalid diagnostic.
- A universal Error wrapper adds topology where direct owner/ordered children
  already distinguish the slot, while an untyped universal wrapper cannot
  identify close versus Item ownership.
- Extending `RecordPatternSeparator` to raw Error changes its deliberately
  bounded structured-Invalid scope and still does not identify Item-phase
  foreign-close recovery.
- Error spelling, parser-side metadata, and a generic expected payload all
  retain forbidden parallel state or discard the documented expected slot.

## Required approval and construction gate

Before any construction, the user must approve all of the following:

1. the transparent foreign-close slot mechanism;
2. its durable SyntaxKind/node name;
3. one wrapper per consumed foreign-close occurrence and its diagnostic
   grouping consequence; and
4. the narrow supersession of direct raw Error placement for this owner only.

After approval, use M2: independent specification and compiler/recovery
pre-write review, one implementation/repair bundle, and one scoped closure
review. Append the new SyntaxKind without changing existing raw values.
Required proof includes collision, repeated and mixed close/raw inputs, both
sequence phases, comma/layout/EOF, UTF-8/CRLF/comment leading, caller/fence
handoff, nested recovery, source flattening, wrapper ranges and preorder, and
unchanged temporary records/frozen replay/accepted controls. No benchmark
samples/processes are planned unless construction exposes material uncertainty.

Stop construction if any same-CST/different-slot witness remains, source or
handoff ownership changes, grouping relies on hidden parser history, or the
new node reaches a sibling owner outside this scope.
