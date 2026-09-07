# Successor T2b PathSegment recovery amendment

Status: Reviewed

Date: 2026-09-07

Drafted-by: primary from architecture preflight after T2a completion

Reviewed-by: M3 compiler/recovery, specification, and performance review; two
batched Draft repairs followed by clean compiler/specification/performance
delta review on 2026-09-07

Scope: one TypeExpression `Type(PathSegment)` successor owner migration for
the accepted `TypePathTail` after `::`.  It proposes the exact Missing/Error
records, legacy continuation preservation, one narrow partial-leading
Error-run capability, and the associated local/O6 evidence timing.  It does
not authorize any other T2 owner, T3--T7/PV owner, caller-owned Missing,
legacy production change, Yumark/session transport change, public dispatch, or
cutover.

Depends-on:

- `2026-08-20-yu-syntax-chasa-architecture.md` Type primary/path recovery
  table;
- `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`;
- `2026-09-02-yumark-gate3b-canonical-recovery-episode-amendment.md`;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` T2 and RB-T;
- `2026-09-05-item-emission-ownership-frontier-amendment.md`;
- `2026-09-06-successor-typed-output-recovery-amendment.md`;
- `2026-09-07-successor-retry-leading-diagnostic-extent-amendment.md`;
- `2026-09-07-successor-t2a-yumark-evidence-timing-correction.md`; and
- `2026-09-07-successor-t2a-embedded-cst-topology-amendment.md`.

Supersedes if approved, and only for every direct child actually emitted by the
Type(PathSegment) Error run under the bounded owner rule in §2.4:

- typed-output amendment §4's whole-Item/literal-only ErrorRunOutput surface
  and its architecture-return sentence, to authorize the sixth sealed
  PathSegment-only partial-leading terminal capability with the exact
  finalization contract in §2.3;
- typed-output amendment §1's unchanged-CST sentence, rewrite-plan §2(1)'s
  exact green-tree rule and §5's full-CST acceptance bullet, and the
  Item-frontier amendment Scope's no-CST-topology clause, to authorize only
  the explicitly named direct-child tokenization delta in §2.4.

It does not supersede Item-frontier central emission, Item ownership, or any
T2a exclusion, and it does not make the T2a retry-leading diagnostic-extent
operation available to T2b.

## 1. Established contract and contradiction

The Type architecture already fixes the legacy owner contract:

- `GrammarRole::Type(TypeRole::PathSegment)` has primary expectation
  `ExpectedSyntax::TypePathSegment`;
- EOF, an active owner boundary, or a next fixed-tail boundary after `::`
  emits a zero-width Missing in the accepted `TypePathTail` and consumes no
  boundary byte;
- a nonempty invalid run is Error, and a valid identifier or sigil identifier
  may retry at the same slot; and
- an integer is never a valid path segment.  Caller punctuation, newline, and
  closes remain outside the Error run.

The existing direct records establish, locally, `A::` Missing `3..3`, `A::@`
Error `3..4`, and `A::123` Error `3..6`.  The Gate3b T2 embedded shell is
`\ref({type T = <type>})`, whose local Type range shifts by `+15`; therefore
the `A::@` primary direct fact is Type(PathSegment), Error, `18..19`,
TypePathSegment.

The successor's current raw PathSegment owner cannot be migrated as-is:

1. Its raw `emit_missing` sites and raw Error loop publish no committed
   recovery record.
2. It currently retries `A::@ B` into the same `TypePathTail`, whereas legacy
   direct parsing ends the incomplete path at the ordinary same-line space and
   lets `B` become an outer TypeApply argument.  This changes the path/apply
   AST and CST hierarchy.
3. Legacy `A::@/*x*/ B` Error owns `@/*x*/` at `3..9` but leaves the subsequent
   space and `B` outside the path.  The successor's next Item owns the block
   comment, space, and payload together.  Existing `ErrorRunOutput` can either
   leave them all untouched or emit the whole Item; neither action preserves
   the legacy continuation.
4. Legacy direct Error coalesces an entire malformed run into one `Unknown`
   token, for example `A::@@B` has `Unknown("@@")` and `A::@/*x*/ B` has
   `Unknown("@/*x*/")`.  Source-free Item emission preserves the same Error
   node text/range only as its physical Item-native pieces, such as two
   `Unknown("@")` children or `Unknown("@")` followed by
   `BlockComment("/*x*/")`.  Source slicing, copied recovery text, replay, an
   event buffer, a substitute Item, and Item splitting are all forbidden by
   the governing authority.

The legacy embedded AST adapter currently has no PathSegment fact publication.
The legacy direct record exists, but actual embedded AST/direct equality cannot
be manufactured from it during O3a.

## 2. Proposed T2b owner contract

### 2.1 Typed recovery identity and anchors

The only migrated raw sites are the three Missing branches in
`type_path_tail_normalized` and the Error body in
`retry_type_path_segment_normalized`.

Each Missing publishes exactly one committed-rule record with role
Type(PathSegment), expected TypePathSegment, primary index zero, no unexpected
facts, and the following existing anchors:

| condition | range source | required result |
| --- | --- | --- |
| abstract pending boundary | `PendingBoundary::coordinate()` | Missing at that coordinate |
| un-emitted caller/outer boundary | current Item remaining-start | Missing before the still-owned Item |
| leading emitted before a close/EOF/path boundary | post-emission Item extent start | Missing at that post-leading coordinate |

Each nonempty Error publishes exactly one Type(PathSegment) record with one
whole-run `UnexpectedSyntax::Token` in category `OtherCharacter`, one
committed-rule TypePathSegment expectation over the record range, and primary
index zero.  Normal no-prefix Error records use the emitted Error-node extent;
this proposal does **not** extend a diagnostic span through ordinary retry
whitespace.  It does not use the T2a fifth operation.

### 2.2 Continuation and ownership

The successor must reproduce the following legacy continuation table.

| input | Error range / continuation |
| --- | --- |
| `A::@B` | Error `3..4`; retry `B` in the same TypePathTail |
| `A::@\n  B` / `A::@\r\n  B` | Error `3..4`; either physical newline retries `B` only when it is continuation-qualified at a deeper indent |
| `A::@ B` | Error `3..4`; leave the space and `B` unchanged, close the incomplete TypePathTail, then permit outer TypeApply ownership |
| `A::@@B` | Error `3..5`; retry `B` in the same TypePathTail |
| `A::@/*x*/B` | Error `3..9`; consume the complete adjacent block-comment leading prefix, then retry `B` in the same TypePathTail |
| `A::@/*x*/ B` | Error `3..9`; consume only the adjacent block-comment prefix, leave the space and `B` on the same Item, close the incomplete TypePathTail, then permit outer TypeApply ownership |
| `A::@/*x*/@B` | Error `3..10`; retry `B` in the same TypePathTail |
| `A::123` | Error `3..6`; do not accept the number as a segment |

EOF, abstract/fenced boundaries, caller stops, outer boundaries, closes,
shallow LF/CRLF, line comments, carriers, repeated `::`, and any invalid retry
retain their current owner boundary and never become Error bytes.  Valid
`A::B`, `A:: B`, and `A::'b` retain their ordinary CST and publish no record.

### 2.3 Sixth sealed Error-run terminal operation

`ErrorRunOutput` gains exactly one new terminal, recovery-only operation for
this owner: it may consume a nonempty contiguous prefix of one immediate retry
Item's un-emitted leading into the still-open Error node, then seal the one
record and return that same Item with only its existing frontier advanced.

Eligibility is deliberately narrow:

- an Error body has already emitted a nonempty contiguous malformed prefix;
- before the operation is attempted, the owning retry loop has established
  that the candidate is not a caller/outer/path boundary or close and therefore
  cannot outrank PathSegment retry.  In particular `A::@/*x*/ with` under
  `WITH` and `A::@/*x*/)` retain Error `@` alone and return their complete
  comment-leading Item unchanged;
- the retry Item has a lexical payload and no pending boundary, foreign
  carrier, prior emitted leading, or payload inclusion;
- the emitted retry-leading prefix consists only of one or more complete,
  contiguous `BlockComment` parts beginning at the Item frontier;
- the first remaining leading part is either absent or ordinary horizontal
  whitespace.  It is never emitted by this operation; and
- no emitted/remaining part contains CR or LF, and no newline, line comment,
  quote prefix, gap, noncontiguity, second use, or post-seal operation is
  accepted.

The capability returns exactly one of two outcomes over the same borrowed Item:
`Ineligible`, which leaves Item frontier, Error node extent, record extent,
unexpected evidence, and sealing state byte-identical and leaves the run open;
or `Sealed`, which has emitted the complete validated prefix and advanced only
that Item's existing frontier.  Every eligibility, contiguity, boundary, and
cut validation completes before the first Rowan/frontier effect.  Ineligibility
is ordinary control flow, never a panic or partial emission.

The capability itself derives and validates the leading-part cut through an
Item-local read-only query.  Grammar code receives no physical trivia storage,
source text, raw range, builder, diagnostic, recovery-vector, or arbitrary
Item mutation.  Central Item emission performs the actual prefix emission and
the only permitted frontier advance.  `Sealed` forms the whole-run
`OtherCharacter` evidence itself and is terminal: no later lexical, emission,
evidence, builder, or diagnostic action can occur through that Error run.

This is a sixth operation, distinct from the fifth T2a operation.  The fifth
borrows an Item without changing its CST frontier and widens only a record;
this sixth operation emits an approved physical leading prefix into the Error
node and gives the same frontier-advanced Item back to the ordinary caller.
It uses a distinct sealed completion mode, not the fifth operation's
record-beyond-Error mode: sixth success requires `record_extent ==
error_node_extent` and supplies the one whole-run fact at that equal range,
while sharing the same terminal gate.

### 2.4 T2b Error-run direct-child tokenization delta

For every Item or eligible Item-leading part actually emitted by the T2b
PathSegment Error run, successor Error node text/range and all outer topology
must remain byte-exact with legacy, but direct children preserve their native
physical token/part boundaries rather than coalescing into legacy `Unknown`.
The finite owner contract includes:

```text
input         legacy Error child             successor Error children
A::123        Unknown("123")                 Integer("123")
A::@@B        Unknown("@@")                  Unknown("@"), Unknown("@")
A::@/*x*/ B  Unknown("@/*x*/")               Unknown("@"), BlockComment("/*x*/")
A::@/*x*/@B  Unknown("@/*x*/@")              Unknown("@"), BlockComment("/*x*/"), Unknown("@")
```

No Error node outside this T2b owner, no un-emitted Item part, and no parent or
sibling hierarchy receives a topology exception.  In particular, ordinary
space remains outside Error and with the returned Item.  AST shape, recovery
role/range, unexpected fact, expectation, diagnostic order, losslessness,
remainder, and continuation remain exact.  This owner-local direct-child delta
is necessary to retain one-forward source-free Item ownership; it does not
authorize source retention, text coalescing, or a broader CST-compatibility
exception.

### 2.5 Embedded evidence timing

The T2a timing correction is intentionally not reused by implication.  This
proposal explicitly applies the same placement rule only to T2b:

- O3a proves local successor records, CST/Item ownership, continuation,
  fresh/frozen reconciliation, RB-T, and `+15` arithmetic.
- O4 may close only the local T2b direct/CST/Item/frozen/RB-T subproof.  The
  aggregate T2 matrix row remains Open and earns no common-template or full
  certification credit.
- O6, after real successor Yumark adoption, must compare actual embedded AST
  facts with successor records for all three named T2b controls below, then
  prove frame pop and a clean following `\ref(C)` through the real successor
  route.  It may not fabricate an AST fact, reuse a copied direct record,
  shadow parse, replay source, or restart legacy owner adoption.

The three real O6 controls are:

| embedded source | equality tuple and required successor topology |
| --- | --- |
| `\ref({type T = A::@})` | Type(PathSegment), Error, `18..19`, TypePathSegment; Error child `Unknown("@")` |
| `\ref({type T = A::@@B})` | Type(PathSegment), Error, `18..20`, TypePathSegment; Error children `Unknown("@")` at `18..19`, `Unknown("@")` at `19..20`, then retry `B` at `20..21` in TypePathTail |
| `\ref({type T = A::@/*x*/ B})` | Type(PathSegment), Error, `18..24`, TypePathSegment; Error children `Unknown("@")` at `18..19`, `BlockComment("/*x*/")` at `19..24`; whitespace `24..25` outside Error and `B` `25..26` in outer TypeApply |

The first is the matrix's named primary witness.  The second and third are
additional T2b continuation/topology controls; each still compares the actual
embedded fact to the successor committed record in source order.

Before successor expectations are added, distinct legacy embedded direct
baselines for all three sources above must pin their direct record tuple,
losslessness, precise remainder, enclosing frame balance, AST continuation,
and Error child sequence.  They remain O3 local structural controls only and
make no nonexistent legacy AST-fact claim.

## 3. Required evidence and exclusions

Before local T2b construction can close, focused tests must prove:

- fresh and frozen exact Missing records for `A::`, `A:: `, the fenced
  `> > A::` coordinate `7`, and caller/outer boundary cases;
- execution-pin the direct legacy baselines before successor topology
  expectations: `A::@`, `A::123`, `A::@@B`, `A::@/*x*/B`, `A::@/*x*/ B`, and
  `A::@/*x*/@B` must assert Error text/range, exact legacy single-Unknown
  child, direct record/evidence, AST continuation, losslessness, and remainder;
- fresh and frozen exact Error records, evidence, native-child CST, and
  continuation for `A::@`, `A::123`, `A::@B`, `A::@ B`, `A::@\n  B`,
  `A::@\r\n  B`, `A::@@B`, `A::@/*x*/B`, `A::@/*x*/ B`, and
  `A::@/*x*/@B`;
- exact Item frontier/parentage after partial comment emission: comment inside
  Error, subsequent horizontal space outside Error, and the returned payload
  in either the retry PathSegment or outer TypeApply according to §2.2;
- negative capability controls for every rejected leading form, including
  newline/CRLF, line comment, carrier, boundary/EOF, payload crossing,
  horizontal-whitespace-first, noncontiguity, double seal, and every
  post-seal operation.  Each ineligible attempt must preserve Item/frontier,
  Error extent, record/evidence state, and open-run state exactly;
- raw and space-prefixed deeper LF/CRLF and shallow LF/CRLF controls; closes,
  `WITH`, `EQUALS`, `PIPE`, `STRUCT_BODY`, `VARIANT_BODY`, and repeated `::`
  ownership; and comment-bearing `WITH`/close controls proving the sixth
  operation never outranks a caller/outer/path boundary;
- shifted-local origin `15` controls with local/global Error/record pairs
  `3..4`/`18..19`, `3..5`/`18..20`, and `3..9`/`18..24`; plus the distinct
  legacy direct embedded baselines above, with no fabricated AST equality;
- frozen mismatch preservation of record order/IDs, recovery slots, diagnostic
  cursor, input, Item leading/payload, successor origin, line entry, shared
  operator reference, and `Recoverable::Mark = ()`; and
- successor-native RB-T vectors for `A::@ with` and `A::@/*x*/ with`, each
  proving one Error record and an untouched pending `with` Item (including
  comment leading in the latter) against an independent accepted control.

Focused PathSegment/output/legacy-baseline tests, `cargo check -p yu-syntax`,
formatting, and diff checks are required.  O4/O7 broad suites remain deferred.
T2a, every later Type/PV owner, caller-owned Missing, Yumark transport,
legacy grammar production, public dispatch, and cutover remain out of scope.

## 4. Cost, review, approval, and rollback

The sixth operation runs only after a malformed PathSegment Error has found an
immediate retry Item.  Let `L` be that Item's total leading source bytes plus
its leading-part count.  Its Item-local classification and extent derivation
make a constant number of `O(L)` scans plus one prefix-emission pass; the Item
frontier makes each accepted part emit at most once.  It allocates no source
buffer, event stream, replay state, second builder, Item clone, or valid-input
work.  Static review must establish that no path makes this recovery-only work
quadratic.  The proposed timing budget is zero unless that review identifies a
material unresolved cost.

Return to architecture without implementation if execution-pinned legacy
controls contradict §2.2 or §2.4, or if preserving them requires Item splitting,
source/range retention, byte copying, replay, a secondary builder, nested Error
recovery, caller-boundary consumption, or a topology exception outside §2.4.

M3 review must cover compiler/recovery ownership, exact specification and
Gate3b conformance, and recovery-path resource bounds.  This Draft makes
durable continuation, output-capability, CST-topology, and evidence-timing
decisions.  It must become Reviewed, receive user approval, and become
Authoritative before any T2b code, expected-output, or production-test change.
