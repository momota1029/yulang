# Draft: canonical AST/direct-CST materialization seam

Status: Draft; not implementation authority

Date: 2026-09-09

Scope: the missing representation and committed-output boundary needed for the
canonical successor grammar to produce its already-specified AST products as
an alternative to direct CST. This is the prerequisite to the selected Yumark
cell's `Vec<Recovered<Statement>>`; it neither changes accepted syntax nor
selects any new recovery policy, Yumark form, public API, or parser entrypoint.

Authority considered: the chasa architecture's `Recovered<T>` and incremental
surface-product sections; minimal token-transaction amendment §§1--3;
typed-output amendment §§1--6; structured recovery reservation and extent
addenda; public-cutover priority amendment; doc-comment Yumark §§4/8/11; and
parsed-Yulang-fence addendum §§3--5/§7--9.

## Problem and boundary

The selected fence contract requires one cell decision driver with thin,
alternate AST and direct-CST materializers:

```text
YumarkYulangCodeCell {
  statements: Vec<Recovered<Statement>>,
  range,
}
```

The current successor has only `CstOutput`: `SyntaxIn` fixes every canonical
call to it, grammar procedures construct Rowan directly, and their exits carry
only completion or an unread successor Item. No semantic `Statement`,
`Recovered<T>`, or Yumark structural product exists in source. Consequently a
cell-only adapter would either invent range placeholders, walk the resulting
CST, replay source, or add a second grammar; all are forbidden.

This draft does not restore a legacy parser or an adapter retained only by a
superseded cutover order. It supplies the missing output representation for
the one canonical grammar.

## Retained invariants

1. Lexical scanning, candidate selection, mandatory-slot recovery, grammar
   admission, current-Item ownership, and boundary handoff are shared and run
   once. A materializer cannot scan source, select an alternative, consume a
   boundary, allocate diagnostics, or inspect CST/recovery history.
2. Direct CST streams one Rowan tree and does not allocate or replay an AST.
   AST mode creates no Rowan tree, token-event tape, source/body copy, or
   second parse. Neither mode is derived from the other.
3. `NormalizedExit::Complete(Err(Item))` remains successful completion with
   an unread successor. Product completion is independent from that handoff;
   rejected/deferred optional entry creates neither product nor output effect.
4. `Recovered<T>::Incomplete` means an owner committed its CST/recovery but
   has no mandatory semantic fact. It is a total continuation, not an abort,
   a whole-parent Error, or permission to drop later siblings. A complete
   parent may contain incomplete children.
5. The existing recovery ID sequence, frozen-header reconciliation scope,
   structured-reservation order, LIFO completion, exact draft comparison,
   diagnostic order, and panic-invalidates-output rule remain single and
   mode-independent. A materializer receives only a completed recovery
   identity when its documented product needs it.
6. Structured Error extent validation remains physical: every consumed token
   and trivia fragment, including operator-header split tokens, advances one
   common checked byte account. Reservation completion still requires that
   emitted-account delta equals the Error's physical source extent.
7. Product leaves own their semantic spelling or source-coordinate facts.
   They cannot borrow a consumed `Item`, short `PayloadView`, mutable output,
   or recursive-call reborrow. A range is structural metadata only; it never
   replaces the move-only Item/leading/suffix handoff.

## Candidate representation; not yet a selected API

The candidate seam is private and statically selected, not a public parser
framework, dynamic registry, trait-object sink, or generic `parser/` module.
This records a candidate responsibility split, not a selected Rust API. The
product inventory below must first establish that every returned shape is
authoritatively specified.

```text
mode-independent committed output
  RecoveryLedger = diagnostic sequence + ordered slots + reservations
  PhysicalEmissionAccount = checked source-byte accounting

direct-CST materializer
  Rowan builder + node/token publication

AST materializer
  documented owned structural products only

canonical owner continuation
  one admission/recovery/boundary decision
  + selected materializer operation(s)
  -> owned product, independently of NormalizedExit
```

`RecoveryLedger` owns fresh/reconcile publication, shared-header scope,
reservation/finish validation, and final records. `PhysicalEmissionAccount`
is shared by both modes and is updated for every physical fragment the direct
mode would emit. Rowan-specific checkpoints and node/token construction stay
with the direct-CST materializer.

The candidate canonical construction closure receives a private static
materialization parameter only at construction boundaries. Its associated
products are owner-specific and owned; it cannot choose grammar or recovery.
The direct specialization has no retained semantic product. AST specialization
constructs only an already-authoritative child shape from accepted lexical
facts, child products, and owner-supplied physical coordinates.

The minimum conceptual result contract is:

```text
Entry<P> ::= Rejected
           | Deferred { item, line }
           | Committed { product: P, exit: CompleteExit }
```

`Rejected` is the existing effect-free optional non-match. `Committed` is
entered only after the owner accepts its branch; `CompleteExit` may carry an
unread successor Item independently of `product`. `Deferred` transports the
existing zero-effect deferred Item/line outcome and creates no product. A
required missing slot contributes `Recovered::Incomplete` to its documented
parent field, whereas a malformed root item contributes the documented root
sequence entry. This is not `Result<P, Item>` and must not interpret
`Complete(Err(Item))` as failure.

One sealed common publication surface accepts an actual physical fragment,
advances `PhysicalEmissionAccount` from that fragment's byte length, and then
immediately invokes the selected materializer operation. Grammar callers may
not advance an account from an asserted range. Reservation identities, their
account snapshots, and LIFO completion remain private to `RecoveryLedger`.
The header reconciliation scope is an RAII reborrow of the whole selected
output, so nested grammar can publish fragments and records while restoration
remains unconditional. This is synchronous forwarding, not a retained event
buffer.

The shared recovery product is exactly the established conceptual form:

```text
Recovered<T> ::= Complete(T) | Incomplete
```

It carries neither a borrowed input nor an inferred diagnostic. Mandatory
slots, recovered delimiters, malformed root items, and retryable children map
to an actual owner product or the relevant `Incomplete` slot according to the
latest owner-specific AST contract. A whole `Statement` is not made
incomplete merely because one of its children recovered.

## Candidate source-backed syntax-coordinate leaves

The candidate common leaf representation is source-backed coordinates, not a
copied/dequoted literal string and not an AST borrow of a consumed Item:

```text
TextSyntax {
  physical: Range,
  logical: Contiguous(Range) | Fragmented(Box<[Range]>),
}
```

`WordSyntax` and `IntegerSyntax` reuse this representation with only their
documented syntax facts. Delimiters use their ordinary physical ranges. An
empty logical spelling uses a zero-width contiguous range. `physical` includes
accepted foreign quote prefixes; `logical` selects only the accepted language
text, preserving original UTF-8, CRLF and ordinary whitespace without decode
or normalization.

A completed AST package, rather than `SyntaxIn`, `Recover`, or a materializer,
owns exactly one immutable `Arc<SourceText>` and revision. It resolves a leaf
only through package-derived traversal views that yield its logical source
slices. A detached `TextSyntax` has no resolver; the package does not expose a
`resolve(&leaf, source)` operation. The view borrows the owning package and
returns a zero-allocation iterator of its `&str` logical segments. Therefore a
leaf from another equal-text package cannot be supplied as an argument or
silently resolved. The grammar/materializer never looks up source text through
that package.

At consumption, the sealed common publication operation receives the accepted
physical fragments once. It advances the common physical account for every
fragment and, in AST mode only, records the leaf's already-classified logical
coordinates. An unfragmented leaf stores its range inline. A fragmented leaf
creates a temporary vector only when a second non-adjacent logical range is
actually discovered, coalesces adjacent logical ranges as each one arrives,
and commits one boxed range slice. A prefix before a sole logical range remains
`Contiguous` and allocates nothing. The existing move-only
pending fragment carrier is not cloned or retained. This is committed AST
storage, not a parser event/body buffer; direct-CST specialization retains no
leaf accumulator or coordinate vector.

The proposed cost is O(published fragments) construction work, no additional
text traversal, O(logical segments) deferred accessor traversal, and retained
O(logical segments) coordinate metadata only in AST products. It is excluded
from the parser-storage bound as an ordinary committed product. Repeated views
repeat only their bounded segment traversal; they build no cache or index. For
`B` source bytes and `F` accepted foreign prefixes, `F <= B`, and each split
adds at most one committed logical segment. Thus total committed segments are
O(B); peak temporary memory is the current Item's boxed split carrier plus its
eventual boxed ranges, O(F_item). It needs static performance review before
approval.

### Required sealed coordinate publication

The later amendment must give the common publication surface an explicit
coordinate-bearing physical fragment, not infer a source coordinate from
emitted-byte count:

```text
PublishedFragment { text, physical: Range, logical: language-text | foreign-prefix }
```

The consuming Item/leading owner derives these ranges once from its explicit
origin, extent, physical leading parts, and one emission-local monotone cursor.
The cursor validates carrier structure once at Item construction/finalization,
then advances leading index, split index and physical offset exactly once per
fragment. It checks `physical.end - physical.start == text.len()` and partition
progression during that one traversal; it never restarts a split search or
calls `extent()`/`fragment_cursor()` per fragment. This makes unfragmented
payloads and partially emitted leading explicit at a nonzero origin, while a
split's lexical coordinate is a checked input rather than an independently
rediscovered AST fact. The common surface advances physical accounting from
`text` exactly once and passes the classified coordinate to the AST materializer
immediately.

`PublishedFragment` is also the only route for a verified source subslice that
is not an Item part. Its owner supplies borrowed text with checked physical and
logical ranges; the surface verifies `physical.end - physical.start ==
text.len()` before advancing the account and forwarding the selected
token/leaf. This covers source-preserving partition output such as an operator
spelling emitted as parenthesis/name/parenthesis, binding-power components and
dots, header opaque tails, and raw opaque/Error segments. A partition may
change token kinds but must cover the accepted source extent exactly once in
source order. No raw `token(text)` emission, synthetic/unranged token, or
after-the-fact asserted range bypasses the account. Recovery-only Error
segments use this surface before entering their extent in a reservation.

### Candidate root/cell coordinate entry invariant; not yet selected

Every full-root or selected-cell construction entry must carry an explicit
physical input region in the owning document's coordinate space. The convenient
calculation `absolute_end - remaining.len()` is permitted only while
`remaining` is a suffix ending at that same explicit `absolute_end`; a shifted
slice may not substitute its own length or a zero-based origin. Any entry that
cannot maintain that invariant carries/updates its explicit absolute frontier
instead. The candidate surface obtains fragment coordinates only from this
entry frontier plus the consuming Item/subslice owner's monotone traversal.

For a selected cell, terminal body-leading is published through the cell while
it remains open. Its resulting frontier is recorded as the candidate cell-range
end, but boundary facts, boundary-line text and suffix stay pending for the
outer document owner. No equality between that frontier and a pending close or
transition coordinate is assumed without controls for every terminal path.
This is a durable coordinate convention requiring M3 review and user approval;
it names no Rust API and authorizes no shared-output extraction.

The direct-CST specialization replaces the current token-counter increment
with this common call; it may not wrap it with a second counter, branch,
dynamic dispatch, `Option<Vec<Range>>`, or AST accumulator on its per-fragment
path. AST owner vectors grow only after their grammar owner has committed;
rejected/deferred entry allocates neither parent nor child.

### Candidate static construction boundary

The candidate has exactly two private static materializers:

```text
CommittedOutput<M> { ledger: RecoveryLedger, account: PhysicalEmissionAccount,
                     sink: M::Sink }
M ::= DirectCst | SyntaxAst
```

Only committed construction owners are generic in `M`; they return
`Committed { product, exit }`. Direct products and list accumulators are
erased rather than `Vec<()>`; AST products are the selected owned structures.
Lexing, operator/stop judgment, coordinate cursor, recovery draft validation,
reservation, frozen reconciliation and physical accounting remain non-generic
narrow operations. A materializer has neither parser cursor nor ledger access.

Two product modes necessarily create bounded construction specialization; this
Draft does not promise impossible zero code duplication. The design instead
forbids duplicate heavy lexical/recovery algorithms, dynamic dispatch and an
event interpreter. Before widening the generic closure, the pilot must inspect
optimized code size/symbols under matching settings and distinguish intentional
two-mode owner code from duplicated shared algorithms.

The existing single-frontier API may allow multiple partial emission operations
per Item. A one-cursor-per-operation proof is therefore insufficient until a
caller audit proves operations are bounded or batches newline-sensitive emission
through the existing immediate hook. If that audit finds unbounded resumptions,
stop: a persistent/resumable coordinate capability would need its own narrow
frontier amendment, not an accidental cache.

The audit has one concrete unbounded-resumption site:
`rule/mod.rs` repeatedly emits one ordinary-newline prefix of the same Item.
The candidate repair is to consume through the last eligible newline in one
emission-local cursor traversal and perform the existing Rule finish/start
sequence from that traversal's immediate per-part callback. It must preserve
the exact token/node order and line handoff for LF, CRLF, comments and foreign
prefixes. Because the callback runs before its part, its local `open_next`
state finishes the current `RuleSequence` immediately before each newline
fragment, opens the next only immediately before the following physical
fragment, and opens it after traversal before payload/boundary handling when
the newline was final. Thus no newline token enters the next RuleSequence. No
persistent cursor is selected by this Draft. If this batching cannot preserve
the Rule contract, return to design for a narrowly approved frontier capability
rather than retaining repeated cursor restarts.

## Product inventory prerequisite

The seam is not certified by a literal-only or range-only cell control. The
following is a dependency map, **not a completed authority inventory**:

```text
Expression(OperatorChain), Binding, Use, Mod, Struct, Type, Impl, Cast,
Role, Act, Enum, Error, For, and DocCommentDeclaration.
```

It reaches flat source-order operator chains and their fixed tails; Patterns;
Type expressions including records, forall, effect rows and polymorphic
variants; braced/indented statement blocks; If/Case/Catch forms; declaration
payloads and their recursive statement bodies. Each product and field needs an
owner/field-to-authority locator, approval-status adjudication, recovery-slot
mapping, and explicit leaf ownership rule. Earlier proposal/review-pending
appendices are evidence, not automatic authority; a later approval signature
or narrow supersession must be checked at the exact field.

Literal syntax is an explicit unresolved dependency: String and Rule literals
are admitted through canonical expression dispatch, while the literal-cone
addendum excludes its own AST/HIR interpretation. The inventory must determine
whether another latest Authoritative source defines their syntax products. If
none does, a separate literal syntax-product decision is required before a
canonical selected cell can claim actual `Vec<Recovered<Statement>>`. It is
not valid to use an opaque range, CST handle, placeholder Statement, or
`Recovered::Incomplete` merely to bypass that gap.

That audit is now concrete: no later Authoritative source supplies such a
product. `2026-09-05-direct-literal-cone-addendum.md` explicitly excludes
AST/HIR interpretation, and the later StringLiteral, RuleLiteral, and Rule
ExpressionList records are recovery-only. A companion M3 literal
syntax-product amendment must define owned String/interpolation and
RuleExpression/RuleLiteral fields, every recovered delimiter/escape/
interpolation slot, and their child `Recovered` mapping before the canonical
inventory can close.

Until this finite inventory is completed and independently reviewed, this
Draft cannot become Reviewed or authorize a shared-output or materialization
pilot.

### Inventory outcome (2026-09-09)

The inventory established a larger authority gap than a field locator alone.
The Yumark/doc-comment addenda authoritatively define the outer document and
selected-fence products, including `YumarkYulangCodeCell`'s actual
`Vec<Recovered<Statement>>`. They do not define canonical `Statement` fields.
The current successor source has no semantic product types at all.

For canonical expressions, Patterns, Types, blocks, controls, and declarations,
the detailed candidate shapes are primarily evidence in the historical chasa
architecture Proposal. Later Authoritative current-Item records select recovery
roles, expectations, extents, and handoff; they do not adopt a product field or
map a record to `Recovered::Complete` versus `Incomplete`. A product amendment
must therefore expressly select a closed Statement sum and every
statement-reachable field/recovery mapping, with the literal companion schema,
rather than silently treating historical prose as approved output authority.

The inventory also retains these product invariants for that amendment:

- an admitted statement with a recovered child remains a complete statement;
  only a failed required Statement sequence position is an incomplete sequence
  entry;
- an unread `Complete(Err(Item))` successor never changes product success;
- separator records remain recovery-ledger facts unless the selected product
  explicitly retains their syntax; and
- root malformed entries, virtual interpolation sequences, braced/indented
  blocks, and ExpressionList need their own explicit product homes.

This is a scope expansion from a materialization seam to a canonical syntax
product design. No code pilot or outer Yumark production construction is
authorized by this Draft.

## Required supersession ledger

Any successor amendment adopting this candidate must explicitly supersede only
the representation clauses below, and must restate every retained invariant:

| current authority | clause to supersede narrowly | retained rule |
| --- | --- | --- |
| minimal token-transaction amendment §1 | successor results are only handoff/recovery facts and no structural product; source-free output restriction where it precludes owned structural coordinates | `I = &str`, operator-only `Recover`, move-only Item handoff, no root source/cursor/cache, and effect-free entry |
| typed-output amendment §2 | one output is necessarily a Rowan-owner in every mode | one mode-independent recovery authority; direct mode owns exactly one Rowan builder; AST mode owns none |
| structured extent-validation addendum §2 | byte counter is builder metadata updated only by the Rowan token forwarder | one sealed common fragment-forwarding account, reservation snapshots, physical-delta assertion, and no caller-supplied extent assertion |

No supersession may weaken typed-output optional-entry preservation, fresh and
frozen record reconciliation, structured reservation order, sealed lexical
Error scanning, or the parsed-fence one-driver/no-replay contract. The final
amendment must name exact paragraph ranges rather than relying on this table's
summary.

## Rejected routes

- Attach an AST accumulator to `CstOutput` or always build AST beside CST:
  violates the no-AST-mirror direct-CST contract and adds ordinary allocations.
- Make `CstOutput` an enum/no-op facade: it discards CST events, creates no
  AST, and loses the current recovery/extent owner.
- CST walk, source replay, retained source/body buffer, event tape, tree
  splice, or separate AST grammar: violates the selected-cell contract.
- Cell-only statement ranges/CST handles: does not provide actual recovered
  canonical statements.
- Store source/root state, a materializer, diagnostics, or parser frames in
  `Recover`: violates the source-free/operator-only recovery boundary.

## Construction and evidence gates

1. **Inventory closure:** provide the authority/field/recovery/leaf map,
   literal-product adjudication, and exact supersession paragraphs. This Draft
   deliberately leaves that work open. No Rust change.
2. **Reviewed amendment:** resolve the concrete private API and product shapes,
   have compiler/recovery and specification reviewers test the inventory and
   rollback conditions, and obtain recorded user approval. No Rust change.
3. **Shared-output pilot:** factor `RecoveryLedger` and
   `PhysicalEmissionAccount` behind the existing non-generic direct output,
   with unchanged CST/fresh/frozen/structured tests. This may not add AST mode
   or change parser signatures.
4. **Private materialization pilot:** one fully inventoried canonical
   statement-reachable closure, including nested Missing/Error, an unread
   same-Item successor, rejected optional entry, and owned leaves after Item
   drop. CST and AST modes prove identical recovery identities/order and input
   progression; direct mode proves no AST allocation and AST mode no Rowan.
5. **Canonical closure:** migrate every included owner before a selected cell
   claims `Vec<Recovered<Statement>>`. Unsupported admitted families cannot be
   silently discarded or published as incomplete public statements.
6. **Yumark integration:** the future `yumark/` document/frame owner selects
   raw versus `yulang`, owns the fence envelope/close/suffix/continuation, and
   invokes the completed canonical cell materializer with the immutable host
   table. It remains private until the existing outer grammar gate is closed.

Pilot evidence includes fresh and frozen records, structured nested recovery,
nonzero origin, UTF-8/CRLF/foreign prefixes, protected terminal leading,
exact terminal Item/origin/line return, and no source replay/event buffer.
The direct-output pilot must prove every emitted source byte, including
operator-header partitions and raw opaque/Error segments, crosses exactly one
checked publication/account operation. Its Rule controls include a fragmented
multi-newline CRLF/quote-prefix Item, preserving the existing sequence order
and proving one cursor traversal through the final newline. Before generic
widening, compare optimized symbols/code size against the matching direct-only
baseline and show that lexical scanning, recovery reconciliation and coordinate
traversal have one shared implementation. AST mode may retain only committed
products/range slices and one shared `Arc<SourceText>`; direct mode may retain
none. Timing remains conditional: only if that static inspection leaves a
direct-mode constant-factor uncertainty, use one warm-up and three paired
samples on a synthetic long fragmented multiline Rule input.
Any need for materializer-selected recovery, a CST-derived AST, an AST direct
mirror, a borrow beyond Item consumption, or a different recovery sequence
returns the affected gate to design.

## Required review and approval

This is a new durable representation decision. Before implementation it needs
the still-open exact inventory, compiler/recovery and specification review of
an exact API/product inventory, then user approval in a successor amendment.
The existing Yumark AST/direct requirement is retained; only this missing
canonical seam and any independently unspecified literal product require
approval.
