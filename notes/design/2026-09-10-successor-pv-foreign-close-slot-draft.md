# PolymorphicVariantType foreign-close CST slot draft

Status: Draft; no implementation authorization

Date: 2026-09-10

Drafted-by: primary from the PolymorphicVariantType collision investigation

Scope: a proposed transparent CST distinction for one locally consumed foreign
close inside `PolymorphicVariantType`. It does not change accepted type grammar,
TagPosition transitions, tag/payload recovery, structured Invalid ownership,
current-Item continuation, parser records, frozen reconciliation, public
diagnostics, API migration or recovery-ledger retirement.

Governing authority: the Authoritative CST-derived diagnostics amendment,
Error/Invalid topology-ordering addendum and polymorphic-variant current-Item
recovery authority. This Draft records a proven owner-schema gap; it adds no
implementation authority.

## Proven collision

The focused current-contract test fixes two fully consumed malformed/recovered
type inputs:

```text
:{;} -> PolymorphicVariantTagSeparator / DelimitedSequenceSeparator
:{]} -> ClosingDelimiter(PolymorphicVariantType, Brace) / Close(Brace)
```

Both have the same direct lossless Rowan shape and Error range:

```text
PolymorphicVariantType(Colon@0..1, LBrace@1..2, Error-token@2..3, RBrace@3..4)
```

There is no Missing, Invalid or admitted tag. The future CST walker must not
inspect `;` versus `]` spelling or retain parser phase, so the distinct existing
slot expectations cannot be derived from this tree.

## Candidate decision requiring user approval

Add one transparent node:

```text
PolymorphicVariantForeignClose := Error+
```

It is admitted only as a direct child of `PolymorphicVariantType`, once for
each locally consumed unclaimed `RParen` or `RBracket`. The wrapper contains
exactly the existing nonempty physical Error-token group for that Item, no
native trivia, Missing, Invalid, accepted tag/payload/punctuation, returned
Item or retry leading. Its range is exactly the combined UTF-8 range of its
Error children. It produces no independent diagnostic.

The exact ordered grammar skeleton is:

```text
PolymorphicVariantType := Colon LBrace
  (NativeTrivia | Comma | PolymorphicVariantTag | Missing(Tag)
   | Error+(Separator) | PolymorphicVariantForeignClose)*
  (RBrace | Missing(Close) | Missing(Tag) Missing(Close))
```

The XML-like notation for its optional/repeated foreign-close alternative is:

```xml
<PolymorphicVariantType>
  <Colon text=":"/><LBrace text="{"/>
  <!-- the following direct children may repeat and interleave in existing phase order -->
  <NativeTrivia text="..."/> | <Comma text=","/> | <PolymorphicVariantTag>...</PolymorphicVariantTag>
  | <Missing/> <!-- existing comma-associated Tag vacancy -->
  | <Error text="..."/> <!-- existing Separator occurrence -->
  | <PolymorphicVariantForeignClose><Error text="..."/>+</PolymorphicVariantForeignClose>
  <!-- existing terminal RBrace or ordered existing Missing(Tag)/Missing(Close) remains direct -->
</PolymorphicVariantType>
```

Direct raw `Error` groups remain the existing
`PolymorphicVariantTagSeparator` occurrence. The Error group inside
`PolymorphicVariantForeignClose` is the existing
`ClosingDelimiter(PolymorphicVariantType, Brace)` occurrence. Existing
`PolymorphicVariantTag`, `PolymorphicVariantPayload` and tag-name `Invalid`
owners distinguish all other raw/structured recovery and remain unchanged.

No wrapper is emitted for accepted `RBrace`, terminal Missing, protected outer
close, semicolon, tag/payload error, or nested recovery. Consecutive foreign
closes produce distinct wrappers. Existing adjacent semicolon Error groups
retain their established maximal-group rule; temporary individual parser
records remain compatibility evidence until ledger retirement.

## Source, phase and handoff contract

All existing `TagPosition` states (`Open`, `AfterTag`, `Unfilled`, `Filled`)
remain unchanged. The wrapper is selected only by the existing locally consumed
foreign-close branch after its current leading emission; it finishes immediately
after unchanged Error emission. The branch preserves the current state and
reads/retries the existing successor under unchanged stops, line/fence and
ambient context. It does not reconstruct a phase from Error spelling.

Leading emitted before the foreign-close classification remains direct
PolymorphicVariantType content. Error-internal leading remains Error content.
Following leading, returned Items, protected caller/fence boundaries and
outer-owned source remain outside. Matching local `RBrace`, comma, ordinary
EOF, Missing(Tag)/Missing(Close), qualifying newline and Type-tail continuation
retain their existing ownership and propagation.

## Alternatives not selected by this draft

- A Separator wrapper is unnecessary: once foreign close is explicit, every
  remaining direct raw Error group in this owner is Separator-owned.
- Reusing tag/payload nodes creates false grammar ownership; `Invalid` expands
  structured recovery beyond its approved scope.
- A uniform terminal-close node changes accepted ancestry without repairing an
  additional demonstrated ambiguity.
- Error spelling/provenance inspection, an expected payload, parser state, a
  generic recovery facility, record merging or another family's wrapper violate
  governing authority or exceed this repair.

## Required approval and construction gate

Before implementation, independent specification and compiler/recovery reviews
must validate this Draft. The user must then approve the node name, all and only
locally consumed foreign closes, one-wrapper cardinality, leading/handoff
contract and narrow supersession of direct raw Error placement on this path.

After approval, use M2: append one SyntaxKind without changing existing values;
one implementation/repair bundle; focused tests for all positions, repeated and
mixed errors, source/leading/CRLF/UTF-8/fence/caller handoff, accepted/type-tail
controls and unchanged records/frozen replay; one scoped closure review; one
package check, format and diff. No benchmark samples/processes are planned
unless material cost uncertainty appears.

The topology/name assertions in
`pv_separator_and_foreign_close_errors_currently_collide_as_raw_cst_leaves`
are current-contract evidence, not stale tests. This approval narrowly
authorizes changing only its foreign-close ancestry and its identical-shape
claim to the new wrapper shape; source, record role/range/category,
fresh/frozen and direct separator controls remain unchanged.

Stop if a direct PV Error cause is not Separator-owned, an accepted tree changes,
records/ranges/current Item/leading/continuation change, a wrapper gains a
successor-owned child, an existing SyntaxKind is renumbered, or another owner
would need the node.
