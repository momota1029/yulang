# RecordPattern foreign-close CST slot draft

Status: Authoritative; private construction complete

Date: 2026-09-10

Approved-by: user

Approved-at: 2026-09-10

Drafted-by: primary from the CST-only diagnostic construction investigation

Reviewed-by: specification and compiler/recovery pre-write audits

Scope: one proposed Rowan topology distinction for raw foreign-close recovery
inside `RecordPattern`. This draft neither changes accepted syntax, recovery
continuation, source ownership, public diagnostics, temporary recovery records,
nor the existing `RecordPatternSeparator` structured-Invalid discriminator.
It authorizes only this bounded CST/SyntaxKind/test construction; full
schema publication and parser-ledger retirement remain separate gates.

Supersedes: the Error/Invalid topology-ordering addendum's direct raw-placement
rule only for raw Error emitted by a consumed foreign close in RecordPattern.
Every other raw malformed fragment remains a direct Error token under its
existing owner slot.

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

## Decision

Introduce one transparent grammar-slot node:

```text
RecordPatternForeignClose := Error+
RecordPattern := ... RecordPatternForeignClose ...
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

Its Error-token group derives the slot
`ClosingDelimiter(RecordPattern, Brace)` and singleton expected punctuation
`Close(Brace)`, primary alternative zero. The wrapper itself projects nothing.
Direct raw Error groups retain their existing Item-or-Separator slot according
to the ordered RecordPattern sequence context; the wrapper distinguishes only
the foreign-close slot. The existing structured separator wrapper continues to
distinguish its own Invalid occurrence. No Error spelling, record ID,
unexpected category, expectation-source flag, parser range, attribute, AST,
side tree, or ledger participates.

Each consumed foreign-close occurrence would get one wrapper. Thus repeated
foreign closes are separate slot occurrences; one lexical sequence run remains
one direct Error-token group. This cardinality is a proposed semantic rule,
not an emitter-call accident.

The XML-like CST notation for one consumed parenthesis close is:

```xml
<RecordPattern>
  <LBrace text="{"/>
  <RecordPatternForeignClose>
    <Error text=")"/>
  </RecordPatternForeignClose>
  <Invalid><Pattern>...</Pattern></Invalid>
  <RBrace text="}"/>
</RecordPattern>
```

`RecordPatternForeignClose` has no attributes and no diagnostic of its own.
The `Error` token remains the sole spelling-bearing leaf. For `{@1}`, the
corresponding Item Error remains a direct `RecordPattern` child; for `{a@1}`
the direct Error remains the existing Separator occurrence. The node does not
encode either of those phase facts.

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

## Construction gate

The user approved the transparent foreign-close slot mechanism,
`RecordPatternForeignClose` name, one-wrapper-per-consumed-close cardinality,
and this narrow raw-placement supersession on 2026-09-10. The two independent
pre-write reviews found the corrected direct Item-or-Separator distinction and
no implementation blocker.

Use M2: one implementation/repair bundle and one scoped closure review. Append
the new SyntaxKind without changing existing raw values.
Required proof includes collision, repeated and mixed close/raw inputs, both
sequence phases, comma/layout/EOF, UTF-8/CRLF/comment leading, caller/fence
handoff, nested recovery, source flattening, wrapper ranges and preorder, and
unchanged temporary records/frozen replay/accepted controls. No benchmark
samples/processes are planned unless construction exposes material uncertainty.

Stop construction if any same-CST/different-slot witness remains, source or
handoff ownership changes, grouping relies on hidden parser history, or the
new node reaches a sibling owner outside this scope.

## Implementation status

Private construction completed on 2026-09-10. `RecordPatternForeignClose` is
append-only SyntaxKind `275`; only the Record-owned `emit_wrong_close` path
opens it immediately around the existing one-Item Error emission. Each consumed
foreign close therefore has one Error-only wrapper. Parenthesized/List owners,
generic emitters, direct lexical Item/Separator Error groups, structured
Invalid topology, parser state and temporary recovery records remain unchanged.

Focused Pattern recovery controls passed 33/33; SyntaxKind controls passed
3/3; `cargo check -p yu-syntax`, scoped rustfmt and diff checks passed.
Independent closure review found no issue. Benchmark use: zero samples and
zero processes. The complete RecordPattern schema, CST diagnostic interpreter,
parser ledger retirement and API migration remain open.
