# Fenced block-comment lexical capability amendment

Status: Authoritative

Scope: This amendment fixes only the immediate, private construction API for
the first fence-aware multiline lexical owner: a block-comment scanner in the
direct rewrite. It implements neither a production code-cell parser nor
Yumark dispatch. Ordinary lexer call sites, legacy/public parsers, session
state, Rowan ownership, AST/HIR, operator state, strings, rule literals, and
all grammar/recovery certification remain outside this scope.

User decision: 2026-09-05 — use a dedicated fenced block-comment scanner;
leave the ordinary scanner unchanged; treat the comment bytes before a fence
boundary as accepted `BlockComment` trivia and leave the boundary line
untouched.

Reviewed-by: independent compiler/recovery review and specification review,
2026-09-05

Approved-by: user, 2026-09-05

Implementation: isolated construction completed 2026-09-05; this does not
claim Gate 4 lexical/Expression closure or production reachability.

Authority: `2026-09-05-yumark-parsed-yulang-fence-addendum.md` §§3, 5, 7–8
requires every multiline lexical owner to judge a physical line before
consuming it, keep its current-item fragment carrier move-only, and return
fence boundaries unchanged. That addendum deliberately does not prescribe the
immediate scanner API; this amendment supplies only that missing shape.

Supersedes: none. It clarifies no grammar, CST, recovery identity, or
production-routing decision outside the scoped construction entry.

## 1. Private immediate capability

The ordinary `scan_block_comment` remains exactly the ordinary scanner. The
fence construction path adds a separate private function, available only to
the isolated direct test/construction entry:

```rust
fn scan_block_comment_fenced(
    i: LexIn,
    part_origin: usize,
    fence: &FenceBoundary,
    foreign: &mut Option<Vec<ForeignSplit>>,
) -> Option<FencedBlockComment>;

enum FencedBlockComment {
    Complete(Trivia),
    Boundary { accepted: Trivia, pending: PendingBoundary },
}
```

The exact spelling of the private result enum may vary, but its two outcomes
may not. `None` means the input did not begin `/*` and must leave `foreign`
unchanged. Once `/*` has been accepted, the scanner is total: it returns one
complete or boundary outcome rather than failing a committed lexical item.
The scanner is invoked only as the immediate `i.token` lexical transaction.
It either probes `/*` before changing `foreign`, or its `None` path restores
both input and the pre-existing accumulator byte-for-byte. After opener
acceptance, it and its containing current-item constructor are total through
the complete Item/carrier outcome: neither may be wrapped in a later
transaction that returns `None`. Coordinate or `PendingFragments::record`
failure after opener acceptance is an explicit invariant failure or a
non-backtracking outcome, never `None`.

The current-item builder owns `foreign`, combines every split from all leading
trivia and payload parts into its one `PendingFragments`, and calls
`PendingFragments::finish` exactly once. Before scanning its first text part,
it captures a checked `item_origin`. Before each part it derives that part's
checked `part_origin` from `item_origin + accepted_item_text_length`, with the
same suffix-pointer agreement as the entry check. The sole `finish` call uses
`item_origin` and the final total length of every accepted Item constituent;
it never uses a comment-part origin. Thus ordinary trivia before a segmented
comment remains in the same physical envelope. The scanner does not create an
Item, finalize a carrier, emit Rowan, or retain the accumulator after its
call.

This is direct argument threading, not a context/frame or parser state. In
particular, `FenceBoundary`, the coordinate, and the accumulator do not enter
`Recover`, Rowan `S`, `Item` metadata, `ParseLocal`, a cursor wrapper, or a
custom input type. The normal scanner has no fence branch and no fragment
allocation.

## 2. Coordinates and line transition

`part_origin` is the common-root byte coordinate of the current live
`&str` suffix at function entry. The caller derives it immediately from a
checked root/suffix relation: `root.len() - suffix.len()` is valid only when
the corresponding pointer position agrees. The root slice is discarded after
that check; no source/root value is retained in parser state or output.

Within the scanner, the current physical-line coordinate is derived from the
entry length and current suffix length with checked arithmetic. On every
physical newline transition, before consuming any byte of the next line, it
calls:

```rust
judge_fence_line(current_suffix, current_line_coordinate, fence)
```

It also makes that call at physical EOF. A `Body` result without a prefix
continues ordinary block-comment scanning. A `Body` result with an accepted
prefix first records exactly one `ForeignSplit::quote_prefix` for the
prefix's common-root extent, then consumes exactly that accepted prefix and
continues. The strict-close test precedes this record and consumption.

The fenced scanner preserves the ordinary nested block-comment algorithm
exactly: `/*` increments depth, `*/` decrements it, and only depth zero
completes the trivia. Fence judging is an additional physical-line transition
before the next-line byte is read; it neither resets nor completes nesting.
LF and CRLF are each consumed as one completed physical-line terminator before
the judge observes the next-line suffix.

For `BorrowedClose`, `Stop(YumarkFence(_))`, or `EofAfterTrivia`, the scanner
returns `Boundary { accepted, pending }`. `accepted` contains only bytes up to
the preceding physical line; the close/transition line has not been consumed,
recorded as a split, or emitted. At EOF, `accepted` contains the unterminated
comment exactly as the ordinary scanner already accepts an EOF-terminated
block comment, while the typed EOF boundary carries the end coordinate.

## 3. Ownership, recovery, and construction boundary

The isolated current-item builder creates an `Item` from the completed leading
trivia/payload and attaches the single item-wide carrier only after acceptance.
If `FencedBlockComment::Boundary` occurs, it places the unchanged
`PendingBoundary` in `Payload::Boundary` and returns that same Item to the
cell adapter. No ordinary statement, Pratt, token-kind, or emitter predicate
may inspect the boundary first. No fragment is emitted speculatively; accepted
fragments use the same one builder only after acceptance.

This gate proves only a block-comment lexical construction control. It does
not implement strings or rule literals, full expression recovery, the root
statement/declaration cone, the immutable host operator-table proof, a
production Yumark adapter, or a public parser. Those retain the gate order of
the parsed-fence addendum: lexical/Expression and Gates 4–7 first, Yumark
convergence at Gate 8, atomic production cutover at Gate 9.

## 4. Required controls and stop conditions

Focused controls must cover ordinary unsplit comments; equivalent-prefix body
continuation; legal close before prefix consumption; reduced, greater,
non-prefix, and explicit transitions; EOF; CRLF and UTF-8 common-root ranges;
one split per accepted prefix; physical-order reconstruction; and exact
unchanged boundary handoff. They must include ordinary leading trivia before a
segmented comment, proving one item-wide finish/reconstruction envelope; a
nested open/close sequence spanning accepted-prefix continuation and a fence
boundary, proving only depth zero completes; and a `/x` non-match with a
nonempty sentinel accumulator, proving both input and accumulator stay
unchanged. An accepted-prefix boundary control proves its accumulator is
committed with the partial trivia while the exact boundary suffix is untouched.
The isolated harness must prove the live suffix is unchanged at a close or
transition.

Return to design rather than implement if this requires retained source/root
state, an ambient fence stack, a dequoted/body buffer, source replay, a second
builder, a custom discontinuous input, Item-local carrier finalization per
trivia part, consumption of a boundary line, or non-linear byte work. Static
cost is `O(comment bytes + accepted prefixes)` with the already-authorized
lazy split vector; timing remains unnecessary unless review identifies a new
material resource uncertainty.

## 5. Review and verification

This is M2 under the parsed-fence addendum. Before code, specification review
must confirm the exact line/boundary contract; compiler/recovery review must
confirm no-consumption and item-wide ownership. After implementation, repeat
those two focused closure reviews. Verification is focused lexical/fence tests
and one `cargo check -p yu-syntax`; no workspace suite is implied.
