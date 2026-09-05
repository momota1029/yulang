# Yumark active-prefix trailing-whitespace amendment

Status: **Authoritative, implemented**

Approved by the user on 2026-09-06. This amendment resolves only the ownership
of horizontal bytes after the final `>` of an accepted active-prefix body row.
It supersedes the conflicting full-prefix wording in
`2026-09-05-yumark-parsed-yulang-fence-addendum.md` and makes the
post-prefix-indentation requirement in
`2026-09-05-fenced-current-item-normalization-addendum.md` exact. All other
quote equivalence, transition, current-Item, fragment, CST, and recovery rules
remain unchanged.

## Decision

The shared Yumark line judge computes two extents for an equivalent active
prefix:

1. The **close-probe extent** contains the line's initial indentation, every
   `>` marker, all horizontal bytes between markers, and the complete run of
   ASCII horizontal bytes after the final `>`. A provisional strict fence-close
   probe starts after this full extent, exactly as before.
2. If the close probe fails and the row is accepted as body, the
   **body-prefix extent** contains the initial indentation, every `>` marker,
   all horizontal bytes between markers, and at most one ASCII horizontal byte
   immediately after the final `>`. Only this extent becomes `YmQuotePrefix`.
   Any remaining horizontal bytes are ordinary Yulang whitespace and begin the
   logical body input.

Thus `> >   Pair` is segmented as `YmQuotePrefix("> > ")`,
`Whitespace("  ")`, `Pair`. The same rule is byte-based for a tab: one tab
immediately after the final marker may belong to the prefix, while later
horizontal bytes remain Yulang whitespace.

An equivalent close line with extra horizontal bytes between its final `>` and
the recorded fence marker still receives the full trailing-byte close probe.
When it is a legal close, the complete line remains unconsumed boundary input
and emits neither `YmQuotePrefix` nor Yulang whitespace.

## Ownership and implementation constraints

- Quote equivalence continues to use the existing depth/base facts and permits
  variation in indentation, inter-marker horizontal bytes, and trailing
  horizontal spelling.
- `QuotePrefixFacts` continues to describe the full observed marker form used
  by the quote judge and close probe. The accepted body result separately gives
  the logical body coordinate; current-Item and segmented lexical consumers use
  that coordinate as the end of the foreign split.
- No parser state, cursor, copied/dequoted buffer, replay, row token storage, or
  second traversal is introduced.
- `YmQuotePrefix` remains grammar-inert. The residual ordinary whitespace owns
  indentation, adjacency, ML-application, operator-site, and recovery effects
  through the existing Yulang trivia path.

## Focused evidence

The implementation slice must cover:

- an accepted same-depth body row with two or more trailing spaces, proving the
  prefix/ordinary-whitespace split and resulting indentation;
- the corresponding tab/space spelling boundary;
- an equivalent legal close with extra trailing horizontal bytes, proving that
  the close line remains wholly unconsumed and emits no body prefix; and
- at least one segmented multiline lexical Item, proving that its foreign split
  ends at the body-prefix extent while the remaining whitespace stays ordinary
  input in physical order.

## Implementation status

Implemented on 2026-09-06 in the shared Yumark judge and every direct accepted-
prefix consumer. Focused Yumark, lexical/current-Item, literal, rule, and
normalized controls passed, as did `cargo check -p yu-syntax`, formatting, and
diff checks. Independent specification and regression audits found no code
defect. No parser state, allocation, replay, or additional traversal was added,
so no performance measurement was consumed.
