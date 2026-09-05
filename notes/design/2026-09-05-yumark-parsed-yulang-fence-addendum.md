# Authoritative: parsed Yulang code fences in Yumark

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-05

Drafted-by: primary agent from architecture investigation

Reviewed-by: independent compiler/recovery, specification, regression, and
performance reviewers on 2026-09-05; all blocking findings closed by scoped
delta review. The performance review accepted the current-item fragment bound
without a benchmark because the required construction is linear by contract.

Scope: parsed `yulang` fence selection, one-forward streaming ownership,
direct CST/AST topology, recovery, and migration gates. This is a successor
addendum. Gate 1 is complete on this approval; it authorizes only the inert
Gate 2 construction. Every later gate retains its stated prerequisite.

User direction: a Yumark `yulang` fence is syntax-recognized Yulang code,
not merely raw text. It supports syntax coloring and is the later doctest
input. Each fence is an independent code cell: it may refer to the externally
supplied environment, but never to bindings or execution state made by another
cell. Its syntax entry is root-style `Statement*`, so root-level declarations
including `our` are permitted. Syntax parsing performs no evaluation.

Authority basis: `notes/design/2026-09-01-doc-comment-yumark-addendum.md`
(especially §§4, 6.1, 7--9, and 11),
`notes/design/2026-09-01-yumark-frame-transaction-storage-addendum.md`,
`notes/design/2026-09-01-yumark-gate3-embedded-yulang-allocation-amendment.md`,
`notes/design/2026-09-02-yumark-gate3b-canonical-recovery-episode-amendment.md`,
and `notes/design/2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`
(especially §§2--3 and Gates 6, 8, and 9). The written Yumark specification
remains the surface oracle; Yulang2 is operational evidence only.

## 1. Exact supersession and retained contracts

When Authoritative, this document supersedes only the following contracts, and
only for a fence selected by §2 as a Yulang cell:

- original Yumark §1: parsed-Yulang fences move from excluded scope into the
  syntax product, and `yulang` is no longer restricted to command/apply
  argument positions;
- original Yumark §7: the selected body is no longer one opaque
  `YmCodeFenceText` range in which only close/EOF are active; it is consumed by
  the one-forward root-style cell owner under the fence boundary in §3;
- original Yumark §8: the selected direct-CST row becomes the structured
  `YmYulangCodeCell` row in §4, its AST changes from a raw `text` member to the
  selected `body` sum in §4, and canonical Yulang CST is additionally allowed
  below `YmYulangCodeCell`; the former closed adapter-home list and its
  “never appears in raw fences” exclusion remain exact for every other adapter
  and every non-selected fence;
- original Yumark §11: the byte-work and storage ledger gains the selected-cell
  canonical parser and current-item fragment bound in §5, and the implementation
  schedule is replaced by §7 only for this successor-cell integration; and
- rewrite-plan Gate 8: the sentence that every `yulang` fence remains raw is
  replaced by the selected-cell integration contract in §7.

All other fences retain their exact existing raw CST bytes, recovery, and
close behavior. Their opening marker, info, opening newline, single
`YmCodeFenceText`, recovered close marker, remainder, and source order are
unchanged. For every fence, including a selected cell, the recovered close-line
marker remains under `YmCodeFence`, while its horizontal suffix and physical
newline remain children of the parent `YmDoc`. In particular, no
Yumark command/apply argument changes, no public `parse_file` recursion, no
opaque-body pre-scan, no replay, no copied/dequoted body, no second Rowan
builder, and no legacy/new production crossing is permitted. The existing
embedded-Yulang delimiter bridge remains a different adapter: it lends a
paired delimiter to an expression/pattern/use-tree parser, whereas a fence
lends a streamed end-of-cell boundary to a root-style statement sequence.

The selected AST intentionally changes from a `text` field to
`body: Raw { text } | Yulang { cell }`; this is not a source-compatible shell.
Every raw AST consumer migrates with the atomic successor cutover in §7, and
no production consumer sees an intermediate or dual representation.

The live input remains `I = &str`; `with_str`, common-root range derivation,
and direct source-backed Rowan emission retain the rewrite plan's approved
contracts. This addendum neither adds a custom discontinuous `Input` nor puts
a cursor, a quote depth, a fence state, a token row, or a source buffer into
`Recover`/`S`/ambient parser state.

It narrowly extends the rewrite plan §3.3 and §6 item algebra only at the
outer-to-inner seam. All existing boundary variants and meanings remain. The
exact extension is:

```text
Boundary ::= Close(Delimiter)
           | BorrowedClose(BorrowedTarget)
           | Dedent(LayoutEvidence)
           | Stop(StopKind)
           | EofAfterTrivia

BorrowedTarget ::= Delimiter(Delimiter)
                 | YumarkFence(FenceCloseFacts)
StopKind        ::= <every existing StopKind variant>
                 | YumarkFence(YumarkFenceTransition)
```

This document abbreviates the new stop case as
`Stop(YumarkFenceTransition)`. `YumarkFence` is deliberately not a
`Delimiter`: it is a non-paired borrowed target whose close is recognized by
line facts rather than by canonical delimiter nesting. Every such pending
`Item` preserves the source coordinate, leading trivia, and exact marker,
prefix, indentation, and transition facts inspected to classify it. Existing
`BorrowedClose(Delimiter)` values migrate mechanically to
`BorrowedClose(BorrowedTarget::Delimiter(...))`; no owner or recovery meaning
changes.

## 2. Fence selection

The proposed selector is deliberately small and extensible:

```text
FenceInfo ::= raw bytes after the opening ``` up to but excluding its
              physical newline
FirstInfoAtom ::= after skipping leading ASCII space/tab bytes, the maximal
                  byte run ending at ASCII space/tab or FenceInfo end

YulangCellFence ::= opening fence whose FirstInfoAtom is exactly `yulang`
RawFence         ::= every other fence
```

Comparison is case-sensitive. Later info atoms are inert, source-preserved
metadata; they neither select aliases nor alter Yulang syntax. Thus
`yulang`, `  yulang`, `yulang test`, and `<TAB>yulang anything` are cells, while
`Yulang`, `yulang2`, `tag yulang`, an empty/ASCII-horizontal-only info line,
and every other language remain raw. A future
language gets an explicit selector and addendum. Its structured body must use
the same §3 borrowed fence-boundary protocol; the outer driver remains one
streaming static `match` over selected payload modes. This preserves a single
multi-language stream without creating a registry or speculative adapter trait.

## 3. Outer/inner ownership and physical stream

Yumark is the sole owner of fence opener/info, opener column, prefix-quote
decoration classification, legal closing-fence recognition, Missing close,
close-line suffix, and return to its enclosing quote/document frame. The
Yulang cell owner sees only the body stream and returns every fence boundary
unconsumed. It never opens a public `Root`, calls a public parser, or decides
whether a physical line is a quote or a fence close.

For every selected fence--unquoted, inside an explicit quote body, or under a
prefix quote--the outer frame constructs one immutable immediate value after
accepting the opener:

```text
FenceBoundary {
  opener: marker range/width and physical source coordinate,
  prefix_policy: None | ActivePrefixQuote(depth, base),
  close_column: opener column after that prefix,
}

FenceCloseFacts {
  line source coordinate,
  exact prefix range/facts if present,
  exact indentation range/column,
  exact marker range/width,
  inspected horizontal suffix and newline/EOF facts,
}

YumarkFenceTransition {
  line source coordinate,
  expected and observed prefix/indent facts,
  exact unconsumed inspected extent,
}
```

`FenceBoundary` is an argument, not a new parser frame, recoverable field,
global cursor, or retained item annotation. `prefix_policy` is `None` for an
unquoted fence and for a fence in the unprefixed physical body of an explicit
quote; both still use this same judge and strict opener-column close rule. It
is `ActivePrefixQuote` only when the selected opener is in an active prefix
quote, and records that quote's active depth and base.

At every new physical line under `ActivePrefixQuote(active_depth,
active_base)`, the shared fence-aware lexical boundary judge uses the exact
existing Yumark §5.3/current quote-judge predicate:

```text
indent = length of the line's leading horizontal bytes
line = source[indent..]
facts = quote_marker_facts(line, indent, active_base)

equivalent active prefix iff
  facts is present
  and facts.explicit is false
  and facts.depth == active_depth
```

Equivalence does not require the opener line's leading indentation,
inter-`>` horizontal bytes, trailing horizontal bytes, or tab/space spelling
to be repeated. Under `ActivePrefixQuote`, an equivalent prefix is provisional
until close recognition finishes: the judge first treats the line's `indent +
facts.marker_len` bytes as a prospective foreign prefix and tests the remaining
physical line for the strict recorded-`close_column` fence close. A successful
test returns
`BorrowedClose(BorrowedTarget::YumarkFence(FenceCloseFacts))` before accepting
or emitting any body `YmQuotePrefix`. If that close test fails, those
prospective bytes become outer Yumark foreign decoration tokens and the
remaining bytes begin the logical body line. Greater depth, reduced depth, no
prefix facts, and explicit facts all fail the equivalence predicate; they never
receive this stripped-prefix close test and instead follow the transition/EOF
rules below. Under `prefix_policy: None`, the judge tests the unmodified
physical line for the same strict recorded-`close_column` close before ordinary
Yulang lexing.

At each physical-line transition, the judge applies the following outcomes in
this exact precedence order:

1. at physical EOF, returns `EofAfterTrivia` without consuming caller-owned
   input;
2. under `ActivePrefixQuote`, for equivalent non-explicit facts, provisionally
   skips `indent + facts.marker_len`, tests the remaining physical line for the
   strict recorded-`close_column` close, and on success returns
   `BorrowedClose(BorrowedTarget::YumarkFence(FenceCloseFacts))` without
   consuming its prefix, indentation, marker, suffix, or newline;
3. if that provisional stripped-prefix close test fails, accepts the equivalent
   active quote decoration as `YmQuotePrefix` foreign trivia and continues the
   logical Yulang body; no body prefix is emitted before this point;
4. under `ActivePrefixQuote`, detects greater-depth, reduced-depth, non-prefix,
   or explicit-quote facts as `Stop(YumarkFenceTransition)` without a
   stripped-prefix close test and without consuming the following outer line;
5. under `prefix_policy: None`, tests the unmodified physical line for the
   strict recorded-`close_column` close and, on success, returns the same
   `BorrowedClose` without consuming its indentation, marker, suffix, or
   newline; or
6. leaves ordinary body bytes to the normal Yulang lexer.

The body-line prefix is source-preserved foreign trivia. It is not a Yulang
operator, whitespace normalization, or hidden input deletion. Its grammar
classification and recovery authority stay Yumark's even when source order
requires the token to appear below an open Yulang CST node.

Foreign decoration splits a trivia or lexical token at its physical position
instead of coloring the `>` bytes as Yulang source. Thus a multiline comment,
string, or later rule literal has ordinary Yulang token segments around an
interleaved `YmQuotePrefix` token. An interrupted lexical-token or trivia item
owns one current-item-local ordered fragment carrier:

```text
PendingFragments {
  foreign: Box<[ForeignSplit { offset, length, kind: YmQuotePrefix }]>,
}
```

The current `Item` retains its one existing contiguous physical token/trivia
text. It gains `Option<PendingFragments>`; an unsplit item has `None` and no
fragment carrier. While completing one lexical item, the scanner creates one
scanner-local `Vec<ForeignSplit>` only when it accepts that item's first
foreign prefix. It immediately pushes one record for that prefix and exactly
one record for each later accepted prefix in that same item. When the lexical
item completes, the scanner converts that vector exactly once with
`into_boxed_slice`; this may perform one final shrink/reallocation. The
resulting ordered box contains only common-root split offsets/lengths and the
exact foreign kind.

One builder derives the intervening Yulang segments from the item's existing
physical text and emits all segments in order only after the lexical item is
accepted. After completion the box moves with that same `Item` through owner
handoff or rejection: it is never cloned, rescanned, or appended. It is not an
event stream, body/row buffer, duplicated text, parser-state field, or
suspended row parser. No fragment is emitted speculatively and no rejected
item must rewind Rowan.

Every scanner that can cross a physical newline must ask this exact judge
before consuming the next logical body line. This includes block comments and
every later multiline lexical owner such as string/rule literals. It prevents
a lexical region from swallowing a close marker or a quote transition.

The outer Yumark owner constructs `FenceBoundary`. The fence-aware
current-item builder alone constructs `FenceCloseFacts` or
`YumarkFenceTransition` from the current physical line and common-root
coordinates. At physical EOF it constructs the existing `EofAfterTrivia`
with the same common-root source coordinate and exact leading trivia.
Canonical statement/Pratt owners may reject and return the exact
pending `Item`, including leading trivia and `PendingFragments`, but may not
reclassify it. The cell adapter transfers it unchanged to Yumark. Yumark alone
consumes/emits an accepted close or handles the transition; no ordinary Yulang
owner constructs or consumes either new boundary.

At a quote transition before a legal close, Yumark emits exactly one
`Missing(CodeFence, ClosingDelimiter)` at the unconsumed line, finishes the
cell, and returns that line to the quote owner. At EOF it emits the same
fence Missing, then existing enclosing explicit-frame Missings inner-to-outer.
An equivalent active quote prefix followed by a legal close is not body trivia:
the final body newline belongs to the cell, while the close-line prefix and
marker belong to `YmCodeFence` after the cell. This preserves the outer
frame's next-document decision and avoids consuming a caller-owned close.

The selected cell accepts only prefix facts equivalent under the recorded
active depth/base predicate above; spacing and tab/space variation at the same
depth remain ordinary continuation under Yumark §5.3. A greater-depth,
reduced-depth, non-prefix, or explicit-quote line ends that cell with one fence
Missing and returns the entire line untouched. Normal outer Yumark quote
handling then closes frames for a reduced/non-prefix line, diagnoses or
handles an explicit form under its existing rules, or opens/continues deeper
nesting for a greater prefix. This rule changes only the selected cell's
continuation; it does not supersede ordinary Yumark's approved greater-depth
prefix-quote nesting outside a selected cell. Explicit quote blocks already
give their body an unprefixed physical region. Nested prefix quotes use the
outer streaming frame stack and have no language-defined depth limit.

## 4. Cell syntax, syntax environment, and CST/AST products

A selected cell uses one root-style canonical statement loop:

```text
YulangCodeCell ::= Statement* FenceBoundary
```

It uses the containing file's already immutable operator table. A cell-local
operator declaration may be syntactically parsed according to ordinary root
rules, but does not change syntax selection for later text in that cell or in
another cell. Incremental cell-local header construction would require a
separate approved syntax-environment design; it is not implicit here.

The proposed direct CST topology is:

```text
YmCodeFence
  YmFenceMarker
  YmCodeFenceInfo
  Newline
  YmYulangCodeCell
    Statement*
    Yulang tokens
    YmQuotePrefix tokens where physical source order requires them
  [close-line YmQuotePrefix / indentation]
  Recovered YmFenceMarker
```

`YmYulangCodeCell` is a new structural node. It is not a nested public Root
or a separately built/spliced green tree. An interleaved body-line
`YmQuotePrefix` cannot always be a sibling outside the cell: a multiline
Yulang node may still be open at its physical position. Therefore *outer
ownership* here means outer classification, terminator, recovery, and return
authority--not a promise that every such token has `YmCodeFence` as its
immediate Rowan parent. The close-line prefix is outside the cell and directly
under `YmCodeFence`.

Raw fences keep this exact existing topology:

```text
YmCodeFence(open marker, info, opening newline, YmCodeFenceText, recovered close)
```

The AST mirrors the selected form rather than hiding a parsed cell behind a
raw range:

```text
YumarkCodeFence {
  open, info, opening_newline,
  body: YumarkFenceBody,
  close, range,
}

YumarkFenceBody ::= Raw { text }
                  | Yulang { cell: YumarkYulangCodeCell }
YumarkYulangCodeCell { statements: Vec<Recovered<Statement>>, range }
```

`range` is a physical source envelope and can include interleaved quote-prefix
bytes; it is never a reconstructed logical source. AST and direct CST use one
cell driver with thin materializers. They make no independent grammar or
recovery decision, and neither is made by walking/reparsing the other.

## 5. Recovery and byte-work invariants

The cell's canonical statement recovery retains its ordinary typed owner/slot
and the exact active root-style stop policy. The fence adapter adds a Yumark
`ClosingDelimiter` Missing only when its boundary is reached before an exact
close; it adds no duplicate canonical close or statement recovery. The pending
boundary and all of its leading trivia return unconsumed to Yumark.

One physical source byte has one forward owner:

- opener/info/opening newline, close-line prefix/indentation/marker, and
  close-line suffix/newline: outer Yumark;
- ordinary body code and its ordinary trivia: Yulang cell;
- interleaved active body quote prefix: Yumark-classified foreign trivia,
  emitted by the cell at its physical position;
- a pending segmented lexical item's ranges: its one current `Item` until
  acceptance, then the same Yulang/foreign owners above through one builder.

No full-body scanner may discover a close before the cell parser runs. The
outer judge may inspect only the current physical line boundary. No cell path
copies/dequotes a body, captures/reparses it, retains a per-row token vector,
suspends a parser between rows, or uses an event buffer/tree splice. Static
time is `O(body bytes + structural work)` and retained parser storage is
`O(structural nesting + largest pending segmented lexical item)`, excluding
ordinary committed CST/AST products. A single unclosed multiline lexical or
trivia item may span the remaining cell, so its ordered foreign-split list may
be linear in that item's size. Its scanner-local vector is created only at the
first accepted prefix, grows with exactly one metadata record per accepted
prefix, and is converted once to the item's boxed carrier at completion (with
at most one possible final shrink/reallocation). Metadata construction is
amortized `O(prefixes in that item)`; peak metadata storage is bounded by the
largest pending segmented item. Completed carriers move without clone,
rescan, or append, and no raw source byte is duplicated. Gate 2 accounts for
this nontrivial allocation and requires performance review of the static
progress/allocation bound. Timing is required only if static analysis cannot
resolve a material risk.

## 6. Doctest and coloring boundary

The syntax product makes selected cells discoverable and colored through their
ordinary nested Yulang CST. Syntax receives no runtime environment and runs no
cell. A later, separately approved doctest-runner design must enumerate
`YumarkFenceBody::Yulang` cells in source order and, for each one, create a
fresh cell scope over the supplied external environment. It permits the normal
root declaration surface (including `our`), observes no prior cell's bindings
or execution state, and discards the cell's owned state afterward. This
addendum authorizes neither runner APIs nor evaluation.

## 7. Migration gates and prerequisites

This is M3 language/architecture work. It does not reprioritize or authorize
the currently incomplete rewrite closure. In particular, no legacy Yumark
driver is extended: the final integration occurs only in the successor
Yumark owner and only through rewrite Gates 8--9.

1. **Authority closure (complete on this approval).** Record the approved selector, quote/dequote rule,
   AST/CST topology, syntax-table policy, exact supersession, and coverage
   table. No Rust change.
2. **Inert direct vocabulary and boundary judges.** Add
   `YmYulangCodeCell`, the pure selector, `FenceBoundary`, the typed pending
   fence/quote boundaries, and the current-item-local physical-text plus
   foreign-split fragment carrier. No body parser or dispatch edge. This is
   the only implementation
   point that adds the §1 boundary cases and §3 fragment representation. Its
   nontrivial largest-pending-item allocation receives performance review and
   a static progress/storage bound before acceptance; timing is added only if
   that analysis leaves a material risk unresolved.
3. **Isolated cell construction witness.** Use the then-available direct
   canonical-statement closure to prove one-builder root-style `Statement*`
   composition and the foreign-trivia/borrowed-close contract. It is not a
   production parser and cannot claim grammar closure before the prerequisites
   in the next row.
4. **Full cell closure.** First close rewrite Gate 4's expression and
   multiline lexical-owner cone, Gate 5's Pattern/TypeExpression owners where
   reachable from root statements, and Gate 6's root statement/declaration
   cone. Connect the containing file's immutable host operator table only
   after rewrite Gate 7 has constructed and reconciled it. Then prove every
   accepted/recovered cell uses that complete direct closure; an isolated
   fixture table before Gate 7 is not production host-table evidence.
5. **Yumark convergence.** Replace only the raw-fence branch of the successor
   Yumark owner with the §2 selector and its raw/Yulang adapters. Preserve
   non-Yulang raw fences byte-identically. This is part of rewrite Gate 8;
   the old Gate-8 all-raw sentence is superseded only here.
6. **Atomic production cutover.** Promote with rewrite Gate 9, delete old
   callers, and prove one production authority. No temporary legacy bridge or
   dual parse is permitted.
7. **Later semantic product.** Design doctest enumeration/evaluation and any
   public highlighting API separately; no syntax gate smuggles it in.

## 8. Required evidence, reviews, and stop conditions

The focused table before Gate 5 is exact rather than representative:

| area | required rows and assertions |
| --- | --- |
| selector | positive exact `yulang`, leading-horizontal `  yulang`, and later inert atoms `yulang test`; negative empty/horizontal-only, case change, `yulang2`, and first atom other than `yulang`, including `  rust yulang`; exact info bytes exclude LF/CRLF |
| cell surface | empty, single, and multiple statements; root-level `our`; host-defined operator use after Gate 7; syntax-only/no execution |
| adjacent modes | one document containing raw → selected `yulang` → raw/unknown fences followed immediately by a heading, paragraph, command, quote, or other next document construct; each body kind, remainder, and following owner stays exact |
| close/source order | exact opener-column close, close-like body text, close marker under `YmCodeFence`, horizontal suffix/newline under parent `YmDoc`, and exact remainder/source order for LF, CRLF, and EOF/missing-close variants |
| quote streaming | prefix quote depths 1, 2, and 3; same-depth prefix equivalence under the existing §5.3 judge across changed leading indent, inter-`>` horizontal bytes, trailing horizontal bytes, and tab/space spelling; reduced, greater, non-prefix, and explicit facts each return the untouched line for ordinary outer handling; explicit-quote and unquoted controls |
| segmented lexical items | multiline block comment, string, and rule literal each with an equivalent-prefix close row and a failing-prefix transition row; fragment order/ranges, scanner-local vector creation only at the first prefix, exactly one record per accepted prefix, one `into_boxed_slice` at completion, no carrier for unsplit items, one-builder post-acceptance emission, and move-only pending-item handoff are exact |
| bytes/color | UTF-8 content and CRLF across segmented items; lossless common-root ranges; no `YmQuotePrefix` byte receives a Yulang lexical color |
| recovery | selected-cell syntax recovery followed by exact close; missing fence at dequote/greater-prefix/EOF; enclosing explicit frames recover inner-before-outer with exact typed owner/slot, range, record order, and untouched remainder |
| products/invariants | exact CST hierarchy, AST body variant/ranges, raw-control byte identity, no nested Root/public invocation/opaque scan/replay/dequoted body/body buffer/row suspension/second builder/tree splice, and the §5 byte/storage ledger |

Gate 2 uses the smallest implementation/recovery review allowed by its inert
scope plus the mandatory performance review of the fragment allocation and
static bound. Gates 3--4 use M2 compiler/recovery plus specification review.
Gate 5 and public cutover are M3 compiler/recovery, specification, and
regression review; the latter must audit raw non-Yulang controls and
nested-quote siblings. Performance timing is omitted only when Gate 2's static
analysis resolves progress and the largest-pending-item bound. A rescan,
material source clone, or uncertain retained-state bound requires measurement
within the active performance budget and may return the gate to design.

Return to design before implementation if it requires a dequoted buffer,
body replay, a public-parser call, a second builder/tree splice, row-wise
parser suspension, a custom discontinuous input, mutable cell-local operator
activation, hidden quote/fence state, a caller-boundary consumption, or a
nonlinear byte-work path.

## 9. Approved decisions

The user approved the following decisions on 2026-09-05:

1. first exact info atom `yulang` selects a cell; later atoms are inert;
2. rewrite §3.3/§6 is extended exactly with
   `BorrowedTarget::{Delimiter, YumarkFence(FenceCloseFacts)}` and
   `StopKind::YumarkFence(YumarkFenceTransition)`; `YumarkFence` is never a
   paired `Delimiter`, and the exact pending Item/fact transfer follows §3;
3. an active prefix cell continues exactly when the existing Yumark §5.3 quote
   judge returns non-explicit facts at the recorded active depth/base; leading
   indent, inter-`>`/trailing horizontal bytes, and tab/space spelling may
   vary, while reduced, greater, non-prefix, or explicit facts emit one fence
   Missing and return the entire line untouched to normal outer quote
   handling; ordinary greater-depth quote nesting outside the cell is
   unchanged;
4. body-line foreign `YmQuotePrefix` may be physically nested under an open
   Yulang node while its classification/recovery authority stays Yumark;
5. interrupted multiline lexical-token/trivia items reuse the current item's
   existing physical text; only after the first foreign prefix does one
   scanner-local vector collect exactly one split record per accepted prefix,
   then convert once with `into_boxed_slice` at item completion and move with
   the item without clone/rescan/append under the §5 storage bound; unsplit
   items have no carrier;
6. cells use only the host immutable operator table after rewrite Gate 7; and
7. the fence AST changes to
   `body: Raw { text } | Yulang { cell: YumarkYulangCodeCell }` with the cell's
   `statements` and physical `range`, not a raw-range-only compatibility shell.
