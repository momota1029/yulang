# Successor retry-leading diagnostic-extent amendment

Status: Reviewed

Date: 2026-09-07

Drafted-by: primary after T2a implementation-review finding

Reviewed-by: M3 compiler/recovery, specification, and performance review;
one batched repair and clean delta review on 2026-09-07

Scope: one recovery-only exception for a mapped malformed Error whose legacy
diagnostic extent includes same-line leading trivia owned by the valid retry
Item. The first intended consumer is O3a T2 ArrowRhs. This proposal does not
authorize its implementation, any other owner migration, public dispatch, or
legacy-parser removal.

Depends-on:

- `2026-09-06-successor-typed-output-recovery-amendment.md`;
- `2026-09-05-item-emission-ownership-frontier-amendment.md`;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` T2 and RB-T.

Supersedes: typed-output amendment §4 only where its Error-run range and
per-emitted-Item unexpected convention conflict with the retained ArrowRhs
legacy whole-run record below. The exception applies only to a sealed,
contiguous trailing same-line retry-leading suffix. Every other Error range and
unexpected-fact rule continues to derive from emitted Error-node segments
exactly as before.

## 1. Finding

The Gate3b T2 witness `A ->@ B` has an established direct recovery record:

```text
Type(ArrowRhs), Error, 4..6, TypeExpression
```

The Error CST node contains only `@` at `4..5`. The byte `5..6` is ordinary
same-line leading trivia owned by the valid retry Item `B`; the RHS itself is
`6..7`. The legacy parser deliberately reports the contiguous `@ ` recovery
extent while preserving that space as the retry's leading trivia in the CST and
in the pending Item.

The completed O2 `ErrorRunOutput` has exactly four grammar-visible operations:
lexical acquisition, Item emission, literal-segment emission, and unexpected
evidence append. Its one accumulated extent is both the emitted Error-node
extent and the committed record extent. Its normal Error-run form also records
one explicit unexpected fact per emitted malformed Item. ArrowRhs instead has
one legacy `UnexpectedSyntax::Token { range: 4..6, category: OtherCharacter }`
fact covering the whole diagnostic run. Consequently an ArrowRhs migration can
either publish `4..5`, violating T2, emit/move `B`'s leading into Error,
violating the Item-emission frontier and legacy CST topology, or retain the
per-Item `4..5` fact, violating exact frozen reconciliation. A synthetic raw
range would violate the same source-free emitted-segment proof.

This is an output-capability mismatch, not a reason to weaken the matrix
witness or to make a second parse/source replay.

## 2. Proposed decision

`ErrorRunOutput` gains one fifth sealed recovery-only terminal operation,
conceptually:

```rust
seal_record_through_retry_leading(&Item, successor_origin, UnexpectedCategory)
```

It may be called only after the Error body has emitted a nonempty contiguous
malformed prefix, has not appended ordinary per-Item unexpected evidence, and
has lexically acquired a valid retry Item. The operation borrows that Item; it
does not emit, mutate, split, consume, retag, or retain it. It derives the
candidate suffix solely from the Item's existing successor coordinate and
un-emitted physical leading through one private Item query. It retains no
source, raw Item range, fragment coordinate, replay buffer, second builder,
event list, or new Item field.

The private Item query and the output operation jointly enforce this complete
eligibility formula; caller convention is insufficient. With `retry_extent`
derived from the unchanged retry Item:

```text
suffix = retry_extent.remaining
suffix is nonempty
suffix.start == error_node_extent.end
suffix.end == retry_extent.payload.start
record_extent = error_node_extent.start .. suffix.end
```

The Item query additionally rejects unless all physical leading parts in
`suffix` are still un-emitted, ordinary, same-line, and carrier-free; its
frontier is the exact untouched retry-leading frontier expected by this helper.
It rejects every `YmQuotePrefix`/foreign carrier, CR/LF-bearing part, boundary,
EOF, missing payload, emitted-leading state, noncontiguous range, and payload
inclusion. The grammar caller separately proves its retry payload is valid for
the owning continuation; the output helper never infers a grammar role.

Sealing is one-shot and terminal. It rejects a second seal and then rejects
every further lexical acquisition, Item/literal emission, or unexpected-evidence
append through that Error-run capability. The enclosing helper may only close
the one Error node, construct the record, and return the unchanged retry Item.
This makes the borrowed suffix structurally trailing rather than merely a
convention about where a closure happens to return.

`ErrorRunOutput` then retains two private extents:

- `error_node_extent`: the union of bytes actually emitted while its one
  `SyntaxKind::Error` node is open;
- `record_extent`: initially the same range, optionally extended once through
  the permitted retry-leading suffix.

The helper continues to close exactly one Error node and to publish exactly one
record atomically on normal return. Its record draft receives `record_extent`;
the CST node remains exactly `error_node_extent`. For this terminal form,
sealing requires an empty ordinary unexpected vector and installs exactly one
`UnexpectedSyntax::Token` with `range: record_extent` and the explicit supplied
category. ArrowRhs supplies `OtherCharacter`, preserving its legacy whole-run
fact. No per-Item unexpected fact is retained for this one exception. The
ordinary four-operation Error-run keeps its existing per-emitted-Item evidence
unchanged.

For `A ->@ B`, the body emits `@` (`4..5`), borrows but leaves `B` unchanged,
seals the record through `B`'s same-line leading (`5..6`) with one
`OtherCharacter` fact at `4..6`, then returns the unchanged Item. The final
observations are therefore all simultaneous:

- Error CST text is `@` and has extent `4..5`;
- retry Item remains `B` with its leading space and later produces RHS `6..7`;
- committed ArrowRhs Error record is `4..6`;
- no payload byte, newline, boundary, or caller-owned byte joins the record.

The fifth operation is a closed capability addition, not a general arbitrary
range setter. It accepts no caller-supplied range/text and exposes no builder,
node, diagnostic, record, source, or generic output access. It may not be used
to extend before the emitted prefix, across a gap, through more than the one
immediate retry Item's permitted leading, or after the Error record commits.

## 3. Scope and staging

After user approval, this amendment authorizes:

1. output-infrastructure construction and tests for the one sealed operation;
2. only the T2a ArrowRhs migration: its two typed Missing sites and its
   contiguous malformed Error run; and
3. the exact T2 ArrowRhs fresh/frozen, CST, Item, boundary, and rollback
   evidence below.

It does not authorize PathSegment (T2b), bracket-row arrow (T4h), any other
T3--T7/PV/P/D owner, caller-owned Missing migration, public dispatch, or
legacy cutover. The separately observed legacy primary `@ A` range is a
sibling inventory fact only; it remains unchanged until a later mapped owner
slice explicitly adopts this approved capability.

The existing PendingBoundary rule is not changed: ArrowRhs Missing at an
abstract boundary derives its zero-width anchor from
`PendingBoundary::coordinate()`, never from an Item/CST extent. That
read-only coordinate path needs no new output decision.

## 4. Required evidence

Before T2a is complete, prove all of the following.

- Fresh and frozen `A ->@ B` records are exactly
  `Type(ArrowRhs)`, Error, `4..6`, `TypeExpression`, committed-rule source,
  primary expectation zero, with one `OtherCharacter` unexpected fact at
  `4..6`. Error CST remains `@`; the space remains owned by `B`; and RHS is
  `6..7`.
- Adjacent `A ->@B` stays `4..5` with its one whole-run unexpected fact;
  multi-item ArrowRhs controls prove the retained legacy whole-run fact and
  exact Error CST/order. Ordinary nonterminal Error-run owners retain their
  existing per-emitted-Item evidence rules.
- Same-line horizontal/comment retry-leading controls establish exactly the
  permitted suffix. Newline, CRLF, fenced/foreign-prefix leading, EOF,
  abstract boundary, caller close, outer boundary, and invalid retry controls
  prove no suffix extension and preserve the pending Item unchanged.
- ArrowRhs Missing controls cover both branches, including post-emission anchor
  after owner-emitted leading and this exact fenced source:

  ````text
  > > A ->
  > > ```
  outer
  ````

  Its unchanged pending boundary has coordinate and ArrowRhs Missing record
  `9..9`.
- The required embedded witness is `R({type T = A ->@ B})`. It asserts ordered
  AST/direct primary equality at `Type(ArrowRhs)`, Error, `19..21`,
  `TypeExpression` (the T2 local range shifted by `+15`), exact whole-record
  evidence, lossless prefix, precise remainder, and balanced enclosing
  successor output/frame boundary.
- Frozen equality/mismatch, diagnostic order/ID reuse, and RB-T use the
  successor-native rollback vector: independent finished Rowan output,
  records/recovery slots, diagnostic cursor and next ID/frozen cursor, input
  remainder, pending Item payload/leading, successor coordinate, line entry,
  shared operator-table reference, and `Recoverable::Mark = ()`. The successor
  has no legacy `ParseLocal`, latest sink, cut, or persistent recovery log;
  requiring those removed carriers is forbidden by the typed-output authority
  and the prerequisite-ordering successor rollback decision.
- Output tests pin the fifth and only fifth grammar-visible Error-run operation
  and prove it cannot expose builder, node, diagnostics, recoveries, source,
  replay, or mutation of the borrowed retry Item. Direct negative capability
  tests reject newline and CRLF leading, foreign/carrier leading, boundary/EOF,
  payload inclusion, noncontiguity, double seal, and every post-seal
  lexical/emission/evidence operation.
- Focused output/Type tests, `cargo check -p yu-syntax`, formatting, and diff
  checks pass. Broad suites remain at the O4/O7 barrier.

## 5. Cost, rejected alternatives, and approval record

The fifth operation runs only after a malformed Error has already acquired a
valid retry Item. It performs one `O(L)` Item-leading metadata traversal to
derive and validate the retry suffix, where `L` is that retry Item's remaining
physical leading-part count. If the owning grammar cannot reuse a prior
same-line classification, its independent predicate check is a second `O(L)`
leading traversal and must be counted explicitly; implementation should reuse
the classification when the existing control flow permits it. The operation
allocates nothing and adds no valid-input work, clone, source/CST/AST traversal,
lookup, rescan of source, dynamic dispatch, or asymptotic change. Across a
recovery episode eligible retry Items are handled once, so the additional
leading work is linear in their leading parts and does not make the malformed
scan quadratic. Performance review determines whether this static proof leaves
any material timing uncertainty.

Rejected alternatives are a synthetic caller range, moving the retry leading
into Error CST, consuming/splitting the retry Item, a raw source/range field,
source replay, a second builder, a buffered token/event protocol, and changing
the Gate3b range witness. Each either breaks the Item/CST ownership invariant
or violates source-free committed-output authority.

No user approval has been recorded. No implementation under this reviewed
proposal may begin until it has explicit user approval.
