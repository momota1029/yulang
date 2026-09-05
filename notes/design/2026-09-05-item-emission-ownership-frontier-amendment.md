# Item emission-ownership frontier amendment

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-05

Scope: private direct-rewrite `Item` physical ownership, accepted-Item
emission, leading-trivia transfer, and the parsed-fence normalization N0 gate.
It changes no surface grammar, public API, Yumark fence judgment, lexical
input, operator table, recovery role, legacy parser, production dispatch, or
CST topology.

User direction: after review established that physical `Item` ownership and
destructive leading-trivia transfer cannot coexist, the user approved one
strictly limited Item-local emission-ownership frontier on 2026-09-05. It is
not a source, fence, lexical, lookahead, or parser-progress cursor.

Drafted-by: primary after N0 specification/regression review found the
cross-owner carrier contradiction.

Reviewed-by: independent architecture, compiler/recovery, and specification
review; initial findings and two scoped delta rounds closed all blockers.

## 1. Exact supersession and retained authority

When Authoritative, this amendment supersedes only these portions of
`2026-09-05-fenced-current-item-normalization-addendum.md`:

- §7's prohibition on every Item-stored cursor, narrowed to permit exactly the
  emission-ownership frontier in §2; and
- §6's single N0 gate, replaced by N0a--N0c in §6.

It also narrowly supersedes parsed-Yulang-fence addendum §3's sentence that a
closed cell adapter transfers the exact pending Item unchanged to Yumark. The
Yulang grammar still hands that exact zero-frontier Item unchanged to its
terminal adapter; only after that handoff does the terminal adapter consume the
accepted body-leading and return the same pending-boundary facts to Yumark, as
§5 fixes below. No Yulang grammar owner consumes a fence close or transition.

The normalized current-Item addendum named above is already Authoritative and
its INDEX entry remains the authority for all retained construction,
`CurrentItem`, line-fact, and fence-observation clauses. This amendment is the
later, narrower authority only for the two clauses named here; no simultaneous
promotion or imported duplicate of the normalized construction contract is
needed.

It retains every prohibition on stored source/fence/lexical/lookahead cursor,
`Recover`/Rowan state, source root, custom input, body/event buffer, replay,
fragment-text storage, carrier cloning, reconstruction, and lexical Rowan
emission. Its `CurrentItem` line fact remains a transient return value and is
unrelated to this Item-local index.

It also retains the parsed-fence, literal, tail-handoff, and no-`IsCut`
contracts: a pending boundary stays one exact unchanged Item through every
Yulang grammar handoff before the terminal exception above; an accepted Item
has one contiguous physical ownership unit and one carrier; accepted-first
literal ordering remains; and an owner may not create a substitute Item after
handoff. This amendment makes those retained rules implementable across the
existing direct CST topology; it does not authorize physical Item splitting or
leading-trivia reconstruction.

## 2. Sealed physical Item and the one allowed frontier

A completed Item has exactly this conceptual shape:

```text
Item {
  physical_leading: Box<[Trivia]>,
  payload: Payload,
  fragments: Option<PendingFragments>,
  first_unemitted_leading: usize,
}
```

`physical_leading`, payload text, carrier physical interval, and the complete
carrier split slice are private and immutable to grammar code. The one mutable
field is
`first_unemitted_leading`, always in `0..=physical_leading.len()` and monotone.
It means only that the earlier leading physical parts have already been emitted
by an accepting grammar owner. It holds no input coordinate, source reference,
fence fact, token row, continuation, or recovery state.

Lexical construction returns an Item with frontier zero. A leading view used by
grammar predicates observes only the uncommitted suffix. It exposes ordinary
trivia presence, grammar emptiness/adjacency, newline/indentation facts, and
physical-part cut positions; it never exposes mutable boxes, carrier offsets,
or split entries. A read-only `PayloadView` exposes the grammar-relevant
payload classification and, where the existing grammar already needs it, a
borrowed immutable logical spelling (`spelling() -> Option<&str>` or equivalent
borrowed token/operator view). It exposes no source range, physical-part
traversal, part ownership, carrier state, or destructive extraction.
The spelling is borrowed from the existing payload-owned lexical spelling; it
is never carrier-stripped or reconstructed text.
`YmQuotePrefix` remains physical but grammar-inert.

Every standalone `TriviaKind::YmQuotePrefix` physical part always has exactly
one matching `ForeignSplit::YmQuotePrefix` covering its full part. The split
remains the foreign range/classification carrier; the TriviaKind holds only the
Item's physical bytes. “Active” below means eligible for a future emission,
not physical existence: after its physical prefix part is emitted, its matching
split remains in the carrier but is inactive. Embedded prefix splits in a
comment/token remain valid without a standalone part. A completed Item with a
prefix part but no matching carrier is rejected before it becomes observable or
emit-able.

## 3. Atomic construction and carrier window

Fragmented construction is atomic:

```text
Item::finish(physical_leading, payload, pending_splits, item_origin)
  -> Result<Item, FragmentError>
```

It validates the complete physical interval, ordered/non-overlapping UTF-8
split ranges, part boundaries, and standalone-prefix invariant, attaches the
single carrier once, and returns a frontier-zero Item. A recognizer calls it
inside its existing `i.token` lexical transaction. `FragmentError` is an
internal construction-invariant failure after acceptance: a production scanner
must fail internally (`expect`/panic, or an equivalent non-parser internal
error channel) rather than return `None`, syntax recovery, Rowan output, or a
committed suffix without an Item. `None` remains only the existing optional
pre-acceptance payload nonmatch, which restores input and `R` and drops its
local values. Direct negative construction controls may observe `Err` without
making an Item observable.

The ordinary no-split path has sealed prefix-free construction provenance:
ordinary scanners alone create its `LeadingTrivia`, through a private ordinary
constructor that cannot manufacture `YmQuotePrefix`. The only authorized
prefix constructors are the shared fenced `current_item` constructor (including
its fenced block-comment leading-trivia path) and the dedicated whole-Item
fence-aware multiline owners retained by normalization §4: normal/heredoc
string, Rule literal, and a future multiline raw suffix. Each must use
`Item::finish`. `Item::plain` relies on the ordinary module invariant (a debug
assertion is allowed), so the ordinary path does no release prefix traversal or
allocation beyond the existing Item parts. N0a removes `with_fragments` and
every post-construction carrier attachment, including all of those constructors
and test helpers.

The carrier retains one immutable boxed split slice. A central emission
operation derives eligibility from `first_unemitted_leading` and physical-part
boundaries while it performs its permitted bounded metadata traversal; it
stores no split-window start. Already emitted entries remain retained but
inactive backing storage until the Item drops. No split box is cloned,
partitioned, rebuilt, appended, or represented by a per-owner cursor. Each
active split is within one active physical part, and each inactive split has
already been emitted exactly once.

## 4. Consuming emission boundary

All physical traversal belongs to central accepted-Item emission. Grammar code
uses the read-only semantic views to choose the CST node and, for a payload, its
ordinary `SyntaxKind`; it does not walk parts, retag foreign ranges, move
leading trivia or payload, or manipulate carrier state.

The required direct operations are semantically:

```text
item.leading_view() -> LeadingView
item.payload_view() -> PayloadView
item.emit_all_remaining_leading(builder)
item.emit_leading_prefix_with(builder, end_part, before_part)
item.emit_all_remaining_ordinary_leading_compat(builder) // N0b only
item.emit_payload(builder, payload_kind)          // requires no leading remains
item.emit_remaining(builder, payload_kind)        // leading then payload
item.emit_eof_leading(builder)
item.emit_terminal_boundary(builder) -> PendingBoundary
```

They are consuming/mutating Item transitions, not borrowing production
emitters. Each part/token segment is emitted through the one fragment-aware
kernel: normal pieces keep their original trivia/token kind and every currently
active foreign split emits existing `SyntaxKind::YmQuotePrefix` once in physical
order. Retagged keywords/operators/literals supply only `payload_kind` to that
kernel.

`emit_leading_prefix_with` cuts only between whole leading physical parts. Its
immediate non-retainable `before_part` hook is called exactly once, in physical
order, immediately before each part in the committed interval. It receives only
that part's semantic kind (including whether it is a newline) and the current
builder; it cannot inspect source/raw text/ranges, retain Item state, change the
cut, or emit the Item itself. It may update only the calling owner's local
separator flags and emit the pre-part zero-width recovery required by existing
CST topology. It returns no parser outcome and cannot change input, `R`, a cut,
or recovery ownership. Rule uses this hook before every newline, including
repeated newlines, to preserve its existing Missing/Newline sequence. Common
owners use `emit_all_remaining_leading`.

After all leading parts are committed, payload emission uses the original
physical carrier and derived active eligibility; it never needs a reconstructed
payload Item. An Item wholly consumed as a normal/retagged/error/literal token
uses `emit_remaining` once.

N0a makes Item physical fields private. It mechanically converts every raw
leading and payload read/move/assignment to `LeadingView`, `PayloadView`, or a
permanent phased emission operation. The one named temporary
`emit_all_remaining_ordinary_leading_compat` operation accepts only a
prefix-free Item with no carrier, rejects fragmented and pending-boundary Items
before a Rowan effect, and has no Item field escape. It exists only to preserve
ordinary whole-leading owner control flow while each N0b batch moves to the
phased operations above; its callers and the assertion that
fragmented/boundary Items cannot reach them are recorded in the N0b ledger. An
Item site that is carrier-reachable, `Payload::Boundary`-reachable, performs a
partial leading commit, or needs payload ownership is migrated directly to its
permanent view/emission/terminal operation in N0a. That executable partition
includes Rule's partial-separator owner. The temporary operation is deleted by
N0c.

## 5. Boundary and recovery ownership

A `Payload::Boundary` Item always has frontier zero while it is owned by
Yulang grammar. Every grammar-owned leading/payload emission transition rejects
it before a Rowan effect. Required Yulang recovery emits only its owned
zero-width Missing and hands the bitwise same Item to the terminal adapter; it
may not advance the frontier, extract leading, or alter the carrier.

After Yulang returns a boundary, its terminal adapter runs while
`YmYulangCodeCell` is still open. It alone calls `emit_terminal_boundary`,
which emits only that retained accepted body-leading (including any
`YmQuotePrefix`) through the central kernel below the cell and returns the
unchanged `PendingBoundary` facts. This is the sole post-handoff terminal
exception: it consumes the Item completely and leaves no Item to hand onward.
The outer Yumark owner then emits only its owned close/transition line and any
required Missing. It never reparents body leading, reconstructs a boundary
Item, or changes the pending facts before consuming them.

Ordinary `Payload::Eof` is distinct. Its accepting owner may commit ordinary
leading before creating `End`, preserving existing CST/recovery order. A
malformed nonboundary Item consumed as Error is emitted as one whole Item. If a
nonboundary recovery must emit leading, then Missing, then hand the payload to
another owner, it uses `emit_leading_prefix_with` and hands that same
carrier-normalized Item onward.

## 6. N0 replacement gates

### N0a — emission-ownership kernel

Add sealed atomic Item construction, the one frontier, `LeadingView`, the
immutable carrier with derived eligibility, and central phased emission APIs.
Migrate every carrier-bearing constructor (literal, Rule, block-comment
witness, and test helper) to `Item::finish`; delete `with_fragments` and every
post-construction carrier attachment. Make physical Item fields private and
perform the one mechanical compile-only conversion of all raw Item-leading and
payload accesses to `LeadingView`, `PayloadView`, the permanent phased
operations, or the named checked `emit_all_remaining_ordinary_leading_compat`
operation. Migrate every carrier/boundary-reachable site, every partial-leading
site (including Rule), and every payload-owning site directly to its permanent
operation in this gate; only proven ordinary prefix-free whole-leading sites
may use compatibility. Prefix scanning remains unreachable. N0a stops only at
zero production/test `with_fragments`, zero post-construction carrier
attachment, zero direct physical Item-field access, a checked exhaustive site
partition, and an explicit caller/reachability list for the temporary
operation. Focused Item-level ordinary/fragmented controls establish these
invariants without changing parser reachability.

### N0b — finite owner migration

Migrate the temporary ordinary-only compatibility callers and detached
Item-leading emissions in finite batches:

1. expression, tails, and delimited owners;
2. Pattern and Type owners;
3. statement, binding, `if`, and case owners;
4. remaining declaration owners.

Before each batch, `tasks/current.md` records the files, former
leading/payload mutation/emission patterns, focused CST/recovery controls,
temporary-operation callers removed, and deletion condition. The temporary
operation may never touch a fragmented or pending-boundary Item. N0b ends only
after static checks find zero temporary-operation callers, zero detached
Item-owned leading or payload emitter, and zero manual fragment walker.

### N0c — physical-prefix certification

Enable/certify the physical prefix/carrier emission contract after N0b. Every
accepted-Item emitter uses the central API; every Yulang grammar pending
boundary path retains frontier zero, and only the specified terminal adapter
consumes it after handoff. Only then can N1 current-Item construction begin.

## 7. Required evidence, cost, and stop conditions

N0a controls cover ordinary whole emission; leading outside a payload node;
leading then Missing then payload handoff; partial leading through the last
newline; every-newline Rule callback order with repeated newlines and its local
separator flags; a standalone prefix; splits inside a leading block comment and
inside payload text; attempted invalid construction/foreign emission; and the
optional pre-acceptance transaction rollback separate from an invalid direct
construction `Err`. It also proves an accepted production scanner cannot map a
construction invariant failure to lexical nonmatch. N0b adds close, transition,
and EOF terminal-adapter controls proving body-leading emits below the
still-open cell before Yumark emits its owned line, with exact source order,
frontier-zero Yulang handoff identity, and unchanged returned pending facts.

N0b adds representative CST parity controls for binding `=`, `if`/case
recovery, braced/indented statement separators, Pattern alias/alternation,
Type arrow/record/forall, and declaration keyword routing. Rule multiline
separator controls belong to N0a. Boundary controls cover close, transition,
and EOF with exact frontier-zero Yulang-handoff Item identity. Each batch runs
focused checks; one full
`cargo test -p yu-syntax` belongs only to N0c/final coherent certification.

The static cost is one `usize` per live Item, one bounds check on leading
access/emission, and at most a second metadata-only traversal of the leading
parts after a partial commit to derive carrier eligibility. There is no added
ordinary allocation, ordinary prefix scan, text copy, source traversal, or
asymptotic work. Record `size_of::<Item>()` and
`size_of::<LeadingTrivia>()` before/after N0a. Timing measurement is not needed
unless implementation exceeds this layout/traversal bound.

Return to design rather than creating an exception for a source/fence/lexical
cursor, retained callback/context, source root, copied/rebuilt carrier,
per-owner split state, event/body buffer, replay, lexical Rowan effect, direct
physical Item mutation, a boundary frontier above zero, an unbounded owner
migration, more than the bounded second metadata traversal, or an
ordinary-path allocation.
