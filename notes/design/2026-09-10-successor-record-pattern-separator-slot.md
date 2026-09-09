# RecordPattern structured separator-slot discriminator

Status: Authoritative; private construction complete

Approved-by: user

Approved-at: 2026-09-10

Date: 2026-09-10

Scope: the existing structured `Invalid` recovery which admits a Pattern in a
RecordPattern sequence while that sequence expects a separator. This amendment
adds one local Rowan grammar-slot node, `RecordPatternSeparator`, around that
existing `Invalid`. It does not alter accepted RecordPattern spelling, raw
`Error` leaves, the `Invalid` kind, Pattern parsing, parser-record compatibility,
or any other RecordPattern sequence phase.

## Problem and selected representation

The CST-derived diagnostics amendment requires every diagnostic expectation to
be recoverable from a CST occurrence and its documented grammar context. The
existing RecordPattern structured owner cannot meet that requirement for its
two sequence phases. In particular, the malformed sources `{a)1}` and `{a@1}`
can produce the same visible sequence of direct children:

```text
RecordPattern(LBrace RecordPatternField("a") Error Invalid(Pattern("1")) RBrace)
```

The former reaches the structured recovery while a separator is required; the
latter reaches it after raw sequence recovery reset the phase to an item. Their
expected alternatives are respectively `DelimitedSequenceSeparator` and
`Identifier`. Opaque Error spelling is not a permitted discriminator, and a
parser ledger cannot survive the CST-derived diagnostic migration.

The selected minimal repair is asymmetric grammar structure:

```text
RecordPattern item phase      := Invalid(Pattern(...))
RecordPattern separator phase := RecordPatternSeparator(Invalid(Pattern(...)))
```

`RecordPatternSeparator` denotes the separator grammar slot only. It has no
diagnostic of its own and adds no expectation metadata. Its only child in this
scope is the existing `Invalid`, which retains its current range, preorder
diagnostic, nested Pattern child and nested recovery traversal. The item phase
remains the direct existing `Invalid` child. This is not a new structured
recovery owner and does not create a specialized Invalid kind.

## Required construction boundary

`pattern::delimited` owns the Record sequence phase and therefore opens the
node only on the existing separator-phase structured-recovery path. It must
not wrap ordinary raw Error leaves, accepted separators, accepted items,
item-phase structured Invalid recovery, local close recovery, or any nested
Pattern output. Leading already emitted by RecordPattern stays outside the
node. The wrapper contains the existing Invalid intact; it neither consumes
nor emits source independently.

The selected wrapper resolves the Item-versus-Separator expectation collision
only. It does not certify the preceding raw Error group, the complete Record
sequence schema, other delimiter owners, or parser-ledger retirement.

## CST and diagnostic contract

For separator-phase structured recovery, the required direct topology is:

```text
RecordPattern(... RecordPatternSeparator(Invalid(Pattern(...))) ...)
```

The wrapper identifies the semantic slot as `(RecordPattern, separator phase,
RecordPattern sequence context)`. The existing `Invalid` emits the one
structured diagnostic over `Invalid.text_range()` before recursively visiting
its Pattern child; the wrapper is transparent to source range and diagnostic
order. Its expected alternative is `DelimitedSequenceSeparator`, primary zero.
For the direct item-phase Invalid, the semantic slot remains
`(RecordPattern, item phase, RecordPattern sequence context)` and expects
`Identifier`, primary zero.

Matching local close priority, comma consumption, retry without an invented
separator Missing, protected caller/fence handoff, UTF-8 ranges and nested
Pattern ownership remain governed by the existing RecordPattern recovery
authority. A returned comma or close remains outside `Invalid` and the new
wrapper. The wrapper must not move an Invalid extent to an inspected boundary
coordinate.

## Construction and proof

This is an M2 local CST-shape/diagnostic-contract repair. Before code,
specification and compiler/recovery review confirm the exact insertion path,
phase transport, direct-child topology and no-source-change rule. Implement
one append-only `SyntaxKind::RecordPatternSeparator`, open it only in the
approved separator structured path, and extend direct Rowan tests.

Evidence must cover the collision witnesses `{a)1}` and `{a@1}`, both direct
item/separator structured controls, repeated wrong closes and raw runs, nested
Missing/Error under Invalid, commas/layout, UTF-8/CRLF, caller/fence handoff,
source conservation, pending Item/origin/line and unchanged Invalid range and
preorder. Accepted RecordPattern input and item-phase structure remain
unchanged. Verify focused Pattern controls, package check, format and diff.

Benchmark budget is zero samples/processes: the repair adds at most one Rowan
node for the already-structured separator occurrence and adds no scan, replay
or parser state.

Stop this local construction if the separator phase cannot be selected at the
owning path, the wrapper changes source/leading/continuation/range, a raw Error
group would need wrapping, or another collision remains in this structured
Item/Separator discrimination. Return such a case to design; do not retain
hidden phase provenance or a parser ledger. Unrelated incomplete RecordPattern
schema rows remain outside this bounded completion.

## Implementation status

Private construction completed on 2026-09-10. `RecordPatternSeparator` is
append-only SyntaxKind `274` and wraps only the existing separator-phase
structured Invalid path in `pattern::delimited`; the item phase stays direct.
Focused Pattern recovery controls (30), SyntaxKind controls (3), package check,
format and diff checks passed. Independent specification and compiler/recovery
reviews found no remaining delta finding. No benchmark sample/process was used.
