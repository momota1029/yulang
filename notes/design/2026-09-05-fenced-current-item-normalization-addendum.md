# Fenced current-Item normalization addendum

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-05

Scope: private direct-rewrite lexical/current-Item construction, fence-aware
source-only observation, and the staged adoption needed to complete the parsed
Yulang fence rewrite gates. This does not change surface grammar, public API,
operator declarations/table contents, legacy parsing, production dispatch,
Yumark ownership, CST hierarchy, or recovery roles.

User direction: the user selected the normalized current-Item route on
2026-09-05: one generic current-Item constructor with an owner-supplied raw
payload recognizer, rather than continuing the owner-local `L5a -> L6a ->
L5b` fenced-entry migration. After review exposed the ordinary/fenced sharing
choice, the user selected one direct normalized grammar body with an immediate
`Option<&FenceBoundary>` capability over duplicated bodies or type-level
dispatch.

Drafted-by: primary after the L5 successor-acquisition representation
contradiction.

Reviewed-by: independent architecture, compiler/recovery, and specification
review; all blocking findings closed by scoped delta review.

## 1. Exact supersession and retained authority

When Authoritative, this addendum supersedes only these parts of
`2026-09-05-direct-expression-successor-acquisition-addendum.md`:

- §3's owner-local fenced entry protocol;
- §4's `L5a`, `L6a`, and `L5b` construction mechanism and ordering, except
  the `Complete(TailExit) | Deferred(Item)` result algebra and its exact
  zero-effect propagation rule retained below; and
- the matching owner-local portions of §6--§7.

It retains that document's `TailExit` meanings, unchanged pending-Item
handoff, recovery ordering, no-replay/no-persistent-state prohibitions, and
the fact that the uncommitted L5 work is not a completed gate.

It supersedes only the parsed-fence addendum §3 sentences which require foreign
decoration to split an already-existing trivia/token part and say that the
Item retains only its pre-existing token/trivia parts. The retained semantic
contract is narrower and exact: `ForeignSplit` remains the sole foreign
range/segmented-emission classification carrier, while its covered bytes remain
one real physical Item part. The `TriviaKind` variant in §2 is that byte
carrier, not a second fragment classification or range record.

`2026-09-05-direct-literal-cone-addendum.md` remains the grammar, CST, and
recovery authority for literal work. Dedicated multiline lexical owners keep
their ownership; this addendum only gives them the shared current-Item and
source-observation seam described below. It supersedes only that addendum's
private Item-transport spellings with these transient equivalents:

```text
LiteralPiece = Complete(CurrentItem)
             | Boundary {
                   accepted: Option<CurrentItem>,
                   pending: CurrentItem,
               }

StringLiteralExit = Complete(LineEntry) | Boundary(CurrentItem)
NonInterpolatingStringExit = Complete(LineEntry)
                            | Boundary(CurrentItem)
                            | DeferredInterpolation(CurrentItem)
RuleLiteralExit = Complete(LineEntry)
                | Boundary(CurrentItem)
                | DeferredInterpolation(CurrentItem)
```

Every other multiline/literal exit crossing back to a normalized grammar owner
has the same rule: successful completion carries `LineEntry`, while a pending
or deferred Item is `CurrentItem`. A narrower internal helper may use an Item
alone only when its enclosing literal owner restores the fact before returning.
Accepted-first emission, unchanged pending-Item identity, and all literal
grammar/recovery/CST rules remain unchanged.

## 2. One physical foreign Item part

Add one private Item physical part:

```text
TriviaKind::YmQuotePrefix
```

It holds the accepted equivalent-prefix bytes that physically precede a
logical Yulang token or a pending boundary. It is neither Yulang whitespace
nor a Yulang token. It exists because `PendingFragments` validates each
`ForeignSplit` against the Item's real contiguous physical parts: a range-only
split cannot own prefix bytes before an ordinary identifier, operator, or
EOF-after-trivia boundary.

For every accepted `YmQuotePrefix` part, the same current Item has exactly one
ordered, nonempty, UTF-8-aligned `ForeignSplit::YmQuotePrefix` covering that
part. The part supplies the source bytes; the split preserves the foreign
classification, source order, and segmented-emission boundary. A prefix
inside an existing block-comment or lexical-token part remains in that part
and is covered by its split; it does not gain a duplicate standalone part.

The constructor creates no prefix part for a legal close or transition line:
those lines remain unconsumed boundary input. An accepted prefix followed by
physical EOF is instead a leading-only Item whose payload is
`Boundary(EofAfterTrivia)`.

`YmQuotePrefix` is grammar-inert. `LeadingTrivia` exposes semantic operations
instead of new grammar code inspecting its physical storage directly:

- ordinary-leading-trivia presence / grammar emptiness / adjacency;
- ordinary newline presence and indentation after it; and
- physical-part iteration for validation and emission.

The foreign part does not create a Yulang gap, alter line-start state, add
indentation, count as a newline, or alter operator site, ML application,
call/index adjacency, chain continuation, implicit-newline, separator, or
payload-boundary decisions. Ordinary horizontal whitespace after it still has
its ordinary meaning. Normal scanners never construct this variant.

Emission maps a standalone part to the existing `SyntaxKind::YmQuotePrefix`.
Every accepted-Item emitter is fragment-aware: it emits standalone prefix
parts and prefix splits inside comment/token parts exactly once and in physical
order. No new public syntax kind, source root, range-only envelope, copied
body, or second fragment-text storage is added.

## 3. Normalized current-Item constructor

The direct lexical owner receives one static, direct function rather than a
parser trait, request enum, stored callback, cursor, custom input, or ambient
context. Its implementation spelling may vary, but its semantic interface is:

```rust
enum LineEntry {
    PhysicalStart,
    InLine,
}

enum CurrentPayload {
    Token(Token),
    Operator(OperatorToken),
}

struct AcceptedPayload {
    payload: CurrentPayload,
    next_line_entry: LineEntry,
}

struct CurrentItem {
    item: Item,
    next_line_entry: LineEntry,
}

fn current_item<P>(
    i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    payload: P,
) -> Option<CurrentItem>
where
    P: FnOnce(
        LexIn,
        bool,   // ordinary leading trivia is present
        usize,  // common-root origin of the payload
        Option<&FenceBoundary>,
        &mut Option<Vec<ForeignSplit>>,
    ) -> Option<AcceptedPayload>;
```

The owner supplies only its raw payload vocabulary. Expression, statement,
Pattern, Type, declaration-header, and path ownership stay with their existing
grammar functions. The callback is direct and statically dispatched for this
one call; nothing stores or forwards it. There is one normalized grammar body:
ordinary callers pass `None`, fenced callers pass `Some(&FenceBoundary)`, and
only current-Item/source-observation code branches on that immediate value.
There is no duplicate owner grammar/recovery body, parser trait, stored
callback, runtime context object, or owner-local fenced wrapper.

The sole staged exception is the recorded unmigrated-owner frontier in §6:
there, `None` enters the existing ordinary direct-rewrite child while `Some(_)`
returns the same Item as zero-effect `Deferred`. It exists only until that
child's transitive cone is normalized and does not create a permanent grammar
mode branch.

`LineEntry` is a call-local fact, not retained parser state. The outer cell
passes `PhysicalStart` for its first body Item. A successor directly after an
accepted non-multiline payload passes `InLine`; while scanning leading trivia,
the constructor changes its local fact to `PhysicalStart` only after it
consumes an LF/CRLF. Thus it judges the first cell body line and every later
physical line, but never mistakes a mid-line `>` for quote decoration. A
payload owner which crosses a physical line performs the same immediate
judgment before observing its next line and reports the actual successor fact
in `AcceptedPayload`. Physical newlines remain leading-trivia or dedicated-
multiline-owner responsibility.

`CurrentItem` is similarly a transient lexical result, immediately
destructured by its caller; it is not Item metadata or a retained row/token
state. A non-multiline token/operator reports `InLine`. A multiline payload
reports `PhysicalStart` exactly when it consumed its final LF/CRLF and leaves
the next physical line as its live suffix. A close/transition boundary reports
`PhysicalStart`, preserving the unconsumed line for its parent; an
`EofAfterTrivia` result reports `InLine` because it has no live next line.
Every `Complete` and `Deferred` grammar return transports that same immediate
fact, so a child which ended just before an unconsumed structural starter on a
new physical line cannot lose its required first-byte fence judgment.

Every normalized grammar owner directly receives and forwards its immediate
`item_origin`, `LineEntry`, and `Option<&FenceBoundary>` to the next normalized
owner. These are function arguments only: no owner stores them in `Recover`,
Rowan, Item metadata, a frame, or a context object, and no acquisition callback
is forwarded. The ordinary entry supplies `None`; it shares the direct grammar
body and observes no fence/prefix behavior. The predictable `None` branch is
confined to current-Item/source-observation helpers and changes neither
ordinary Item/CST/recovery/suffix behavior nor its allocation/asymptotic bound.

The outer cell establishes the initial common-root coordinate. Thereafter each
owner snapshots the child entry suffix pointer/length and advances its
caller-owned coordinate only by the observed consumed-byte delta on return.
`current_item` receives this already synchronized immediate coordinate and
uses its live entry suffix only for its local part/payload deltas; it never
derives or verifies an absolute coordinate from a root source.

The fenced constructor owns exactly one current Item's:

- physical leading parts;
- immediate fence decision after every physical newline while it owns trivia;
- fenced block-comment leading-trivia scan;
- call-local lazy `Option<Vec<ForeignSplit>>`; and
- one `PendingFragments::finish` when that Item is complete.

It never emits Rowan, invokes grammar recovery, reads a future logical Item,
or retains any of its arguments. It does not turn an already-consumed fenced
attempt into the ordinary entry.

`None` is permitted only inside the existing `i.token(...)` lexical
transaction. Leading trivia/prefix parts and the constructor-local fragment
vector are tentative until either a boundary is materialized or `payload`
returns `Some`. If an optional payload candidate returns `None`, the lexical
transaction restores input and recoverable state and the local parts/carrier
are dropped. It has no Rowan effect. A payload candidate must make no effect
outside that transaction before returning `None`; in particular it may not
touch a Rowan sink, recovery state by another route, or a caller-owned
fragment accumulator. `CurrentPayload` deliberately excludes `Boundary` and
EOF: only the constructor materializes a fenced boundary or ordinary physical
EOF. Required payload classifiers use their existing unknown/EOF fallback
rather than returning `None` after accepting a token opener. The payload
callback reports only the immediate `next_line_entry` resulting from its
accepted physical consumption; it cannot construct a future Item or boundary.

The constructor algorithm is fixed:

1. receive the caller-synchronized immediate coordinate, call-local line-entry
   fact, and optional fence capability;
2. under `Some(fence)`, if the fact is `PhysicalStart`, classify the entry line
   before consuming any of it; under `None`, scan ordinary trivia unchanged;
3. under `Some(fence)`, after each consumed LF or CRLF, classify the next
   physical line before any byte of that line is consumed;
4. on an accepted body prefix, append one `YmQuotePrefix` physical part and one matching
   split only after strict close recognition has failed;
5. under `Some(fence)`, on close, transition, or physical EOF (the last
   independent of line-entry state), complete the leading-only pending boundary
   Item without calling `payload`; under `None`, construct the existing
   ordinary EOF payload when appropriate;
6. otherwise call `payload` once, attach the carrier exactly once, and return
   the completed Item.

In ordinary mode physical EOF remains ordinary `Payload::Eof`; in fenced mode
physical EOF is `Boundary(EofAfterTrivia)`, including an immediate empty
boundary Item.

## 4. Source-only observation before a payload decision

Dynamic operator role selection and the existing raw follower/layout probes
must not inspect outer Yumark input. They use a pure, non-materializing
fence-aware observer with immediate arguments:

```text
observe_fenced_trivia(
  source suffix, common-root coordinate, LineEntry, Option<&FenceBoundary>,
)
  -> Visible { ordinary trivia facts, next logical source suffix }
   | Boundary
```

The observer is a scanner-local read-only walker, not a custom `Input`, source
wrapper, retained source lifetime, cache, or grammar-wide context. With
`None`, it is the existing ordinary observation. With `Some(fence)`, given
`PhysicalStart`, it judges the entry suffix before observation; given `InLine`,
it does not. It checks each later LF/CRLF before looking at its next line; it
logically skips accepted quote prefixes without classifying them as whitespace
and without recording a split; and it returns `Boundary` without observing a
value starter, comment body, or other outer-line byte past a
close/transition/EOF. It constructs neither an `Item` nor `PendingBoundary`,
`PendingFragments`, or `ForeignSplit`.

A source-only probe beginning at the live current cursor receives that cursor's
`LineEntry`. A probe beginning after any accepted non-newline spelling (an
operator, contextual word, colon, or declaration introducer) starts from
`InLine` even if its enclosing Item began at `PhysicalStart`; only an LF/CRLF
seen by that probe changes its local fact to `PhysicalStart`. Thus a mid-line
`>` after an operator spelling never becomes fence syntax.

For an operator spelling ending at `payload_origin + end`, the observer feeds
the existing raw-trivia facts into role selection. At `Boundary`, role
selection uses cell-EOF facts: post-whitespace is true, value-start is false,
and the dangling operator probe treats the boundary as EOF/an active local
stop. It may accept the current operator only; the next real `current_item`
call, at the untouched suffix, materializes the exact boundary Item.

The same observation rule supplies fenced forms of existing source-only
contextual-word, colon, body-indentation, and declaration-admission probes.
These probes may select or reject an owner branch, but never consume, emit,
record a split, materialize a boundary, or inspect beyond it.

Multiline payload owners (normal/heredoc string, Rule literal, and any future
multiline raw suffix) remain dedicated lexical owners. When they are the
payload portion of `current_item`, they inherit its already-judged entry
position and receive the constructor-owned mutable split accumulator shown in
§3, not an independent vector. They append only accepted splits for that same
Item; the constructor alone finalizes/attaches the one carrier. A dedicated
owner which cannot use this payload seam instead owns the whole Item—leading
parts, payload, one accumulator, and one finalization—from its entry; that
whole-Item owner receives the direct `LineEntry` argument. In both forms it
receives live lexical input, immediate payload origin, and the same immediate
`Option<&FenceBoundary>` capability, and it calls the same line classification
before every next physical body line. A balanced/multiline suffix cannot be
silently treated as a one-line callback. A whole-Item owner returns the same
transient `CurrentItem` result algebra, including its actual successor fact,
unless it encounters a boundary after accepted text. That existing one-forward
case returns its dedicated algebra instead:

```text
MultilineItem = Complete(CurrentItem)
              | Boundary {
                    accepted: Option<CurrentItem>,
                    pending: CurrentItem,
                }
```

`pending` is the exact unchanged close/transition/EOF Item. The lexical owner
returns this algebra without Rowan effect. Its receiving grammar owner emits
`accepted` first when present according to the retained literal CST/recovery
contract, then hands `pending` upward unchanged with its own line-entry fact.
It neither merges two Items nor rejudges/reconstructs the boundary. Literal
owners use the equivalent retained `LiteralPiece` result described in §1.

## 5. Exact boundary and recovery contract

Fenced `current_item` constructs exactly one unchanged pending Item:

```text
BorrowedClose(YumarkFence)
Stop(YumarkFenceTransition)
EofAfterTrivia
```

The boundary line itself is unconsumed and appears in neither Item physical
text nor fragment carrier. Only already accepted prior leading trivia/prefix
parts remain on that same Item. Lookahead never caches a future Item, boolean
replacement, range replacement, or boundary reconstruction recipe.

Before token kind, contextual word, operator, or retry handling, direct
grammar code handles `Payload::Boundary`. A tail returns it through existing
`TailExit`; a required owner first emits only its own zero-width Missing;
recovery stops before the boundary; callers hand the same Item upward without
rescanning, retagging, splitting, emitting, or taking its leading/fragments.
Ordinary `Payload::Eof` recovery remains a distinct path. This preserves
inner-recovery, caller-recovery, then Yumark-fence-recovery order.

## 6. Staged migration

### N0 — physical representation and emission kernel

Add `TriviaKind::YmQuotePrefix`, semantic `LeadingTrivia` operations,
fragment-aware accepted-Item emission, and focused physical-order/noninterference
controls. No scanner, grammar, production reachability, or public surface
changes in this gate.

### N1 — isolated normalized lexical kernel

Add the one mode-parameterized current-Item constructor, pure line
classification and source-only observer, fenced operator/follower evidence,
and isolated lexical/operator controls. Ordinary behavior remains
byte-identical and does not allocate a prefix carrier.

### N2 — grammar-owner migration

Migrate owners incrementally, each supplying its raw payload function:

1. Pratt core, tails, and delimited expressions;
2. Pattern and TypeExpression;
3. canonical statement sequence; then
4. each declaration family and its raw probe loops.

An unmigrated owner may remain behind the retained private effect-free result
algebra only:

```text
NormalizedExit = Complete(TailExit, LineEntry)
               | Deferred(Item, LineEntry)
```

`Deferred(Item, LineEntry)` is not `TailExit::Left(Item)`. It marks an
unentered distinct owner. Each propagating parent closes only its already-open
node, emits no Error/Missing, does not feed the Item to tail/ML/list retry,
creates no child CST/recovery effect, and returns the same Item and call-local
fact unchanged. `Complete` carries the fact produced by its completed child.
At each frontier ledger row only, `None` enters the existing ordinary
direct-rewrite child while `Some(_)` returns that `Deferred` result before
entering it. This temporary capability branch preserves ordinary byte-identical
CST/recovery and prevents the fenced route from consuming beyond its exact
boundary. It is deleted atomically with that child's transitive normalization;
the permanent normalized grammar has no branch outside current-Item/source
observation. No
`CompleteItemSite`-style request enum, generic parser trait, or owner-local
fenced wrapper is added.

Before introducing any such branch, N2 records one finite frontier-ledger row
in `tasks/current.md`: the direct normalized owner and exact call site, its
ordinary direct-rewrite child (never a legacy parser), the exact `Deferred`
propagation path, focused controls for both capability arms, and the named
normalization gate that deletes the row. N3 may not begin or close while any
row remains open; completed rows move into the gate's durable progress record.

### N3 — L5 completion

Only after every Rule `ExpressionList`-reachable owner is normalized may L5
claim full ordinary Expression support, fence handoff after a successful
simple/compound child, braced statement/declaration routes, Pattern/Type
descendants, prefix coloring, and established recovery order.

## 7. Required evidence and stop conditions

Each gate supplies focused controls for its changed cone. Across N0--N3 the
evidence includes:

- prefix physical order, exactly-once fragmented emission, grammar inertness,
  and post-prefix indentation;
- lexical nonmatch rollback, one carrier finalization, one split per prefix,
  no payload callback at a boundary, and no external callback effect on
  lexical `None`;
- initial cell-body `PhysicalStart`, an LF/CRLF-started body line, and an
  in-line `>` control proving the line-entry fact is neither omitted nor
  over-applied;
- a multiline accepted payload ending at an LF/CRLF before an unconsumed
  structural starter, proving its returned fact reaches the next acquisition;
- close/transition/EOF after trivia, operator, line comment, nested block
  comment, NUD/LED, infix RHS, ML argument, call/index, and nested delimiter;
- paired ordinary/fenced dynamic prefix/infix/suffix/nullfix and word-operator
  matrices, including call/path-sensitive `(`/`:` behavior;
- source observers with no fragment/boundary materialization and no
  outer-boundary inspection; the next acquisition returns the exact pending
  Item and suffix pointer;
- byte-identical ordinary CST/recovery/suffix behavior for each migrated
  owner; and
- each ledgered temporary frontier's ordinary-child and fenced-`Deferred`
  branches, plus exact zero-effect deferral at every such frontier;
- accepted multiline text followed by close/transition/EOF before its
  terminator, proving accepted-first emission and unchanged pending-Item
  handoff with both transient line-entry facts.

The static fenced bound remains linear in consumed bytes plus existing
source-only operator probing, with at most one carrier box per fragmented
current Item. The ordinary path has no new allocation or asymptotic work.
Timing measurement is not required unless the concrete implementation changes
that bound.

Return to design rather than creating an exception if a gate requires a
request enum, parser trait, ambient fence state, a retained `LineEntry` or
`CurrentItem`, `Recover`/Rowan/Item stored fence or cursor, custom
input/source wrapper, retained root/source lifetime, source/body replay,
copied physical envelope, fragment text buffer, boundary materialization
during lookahead, inspection past a boundary, per-trivia carrier finalization,
ordinary-path allocation/regression, or an unledgered/permanent grammar-level
fence branch.
