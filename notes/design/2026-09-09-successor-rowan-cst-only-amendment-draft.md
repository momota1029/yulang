# Rowan CST-only successor amendment

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-09

Drafted-by: primary from the user's CST-only direction

Reviewed-by: compiler-recovery, specification and regression reviewers;
direct-Rowan architecture review

Date: 2026-09-09

Scope: successor parser output, recovery-node CST shape, direct Rowan
construction, the replacement of `CstOutput`, and the public
`syntax-reference` direction. This amendment does not alter accepted syntax,
selected recovery ownership, current-Item/fence handoff, public diagnostics, or
the public parser entrypoint except through its approved construction gates.

User direction: the parser produces no AST, semantic syntax product,
materializer, event tape, second tree, or CST-derived reconstruction. Rowan is
the sole syntax-tree representation. `CstOutput` is not retained as a wrapper:
grammar construction uses `rowan::GreenNodeBuilder` directly. No new parallel
output/account/ledger state is introduced. Existing individual expected and
recovery diagnostic information remains required.

## Decision boundary

The three 2026-09-09 canonical materialization/product Drafts were preparation
for an AST/direct-CST dual representation. They are incompatible with the user
direction and receive no further construction work. On approval, this amendment
supersedes them in full. It also narrowly supersedes the AST/materializer or
alternate-output obligations in the parsed-Yulang-fence, doc-comment Yumark,
recursive-descent rewrite-plan and expression-tail-handoff documents.

For direct Rowan construction, this amendment narrowly supersedes
`2026-09-06-successor-typed-output-recovery-amendment.md` §2's required output
wrapper and operator-only `Recover` restriction, and §4 only where generic
recovery must emit the former structural Error wrapper. It narrowly supersedes
`2026-09-07-successor-structured-recovery-reservation-amendment.md` §§2--4
only for reservation storage/output topology, and
`2026-09-07-successor-structured-recovery-extent-validation-addendum.md`
§§2--5 only for the global emitted-token counter and its completion assertion.
It retains Item-derived starts, nonempty Error extents, one committed recovery
occurrence, outer-before-inner order, LIFO completion, exact frozen comparison,
final unfinished-reservation rejection, source-coordinate recovery facts and
all current-Item/fence contracts.

The user has selected a direct Rowan tree, not a runtime XML representation.
The XML-like notation below is the normative notation for the Rowan node schema
and the basis for the rewritten `syntax-reference`.

## Output and diagnostic responsibility

One parse produces one `GreenNode` tree plus the existing public syntax
diagnostics. The diagnostic result is not an AST or a second syntax tree. It
retains individual occurrences, expected unions, unexpected facts, source
ranges, source flags, frozen-header reconciliation and ordering required by
current public behavior.

`GreenNodeBuilder` owns only Rowan construction. Parser recovery owns recovery
publication and reconciliation. The working candidate is to place the existing
diagnostic sequence, frozen cursor and structured reservation within the
already-existing `Recover` parser state, with all mutation private to committed
`SyntaxIn` recovery emitters. Lexical/probe `LexIn` has no diagnostic mutation
capability. This is a migration detail still requiring review: optional
rejection must remain effect-free despite `Recoverable::Mark = ()`, and header
reconciliation restoration must remain scoped.

The global emitted-token byte counter is removed with `CstOutput`. It is not a
source-coordinate authority: recovery sites remain derived from Item/source
coordinates. The runtime structured Error counter check is replaced by focused
source/CST/diagnostic controls for each structured recovery shape; no Rowan
walk, counter beside direct builder calls, source replay, or new runtime account
is introduced. A review must prove retained coverage for nested ordering,
frozen records, UTF-8/CRLF, retry-leading spans and protected boundaries.

## Rowan node notation

The notation is XML-like documentation only:

```xml
<OperatorChain>
  <PrefixOperator text="!" />
  <Missing />
</OperatorChain>
```

Paired tags denote Rowan nodes. Self-closing tags with `text` denote token
leaves. Every source-bearing leaf has its source spelling in a `text`
attribute; structural nodes never contain bare character data. The reference
specifies exact reversible escaping and UTF-8 byte coordinate conventions.
Ordinary trivia outside a malformed run is represented by its own
source-bearing leaves. Trivia absorbed by a raw malformed run is instead
spelled by its Error leaf or leaves. `Missing` is a zero-width structural node
in a documented grammar slot and has no `text`.

`Error` is always a token, never a node. Raw lexical malformed source is
emitted as one or more adjacent opaque Error tokens in its owning grammar slot:

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

Each leaf corresponds to an already emitted physical source fragment, so the
direct builder needs no retained run buffer, source replay or source slice
rediscovery. An Item emitted by the raw-recovery mode maps *every* one of its
remaining physical fragments to an Error token, including interior trivia and
Yumark quote-prefix fragments. It does not take leading trivia already emitted
by the owning production, or retry/boundary leading that remains with the next
owner. Together the leaves represent one ordinary contiguous invalid run and
deliberately expose no invented grammar inside it. The raw Error leaves replace
the current Error wrapper when that wrapper's children are only source tokens.

`Invalid` is always a node. It is emitted only when recovery actually retains
nested grammar, Missing, or nested Error children:

```xml
<Invalid>
  <Error text="@" />
  <ParenthesizedTypeGroup>
    <Missing />
  </ParenthesizedTypeGroup>
</Invalid>
```

It is not emitted around an ordinary raw Error token. This split is a deliberate
CST-shape migration: current `SyntaxKind::Error` is a structural container and
there is no `Invalid` kind. The current structured owners are the
polymorphic-variant tag-name recovery and record-pattern wrong-kind
item/separator recovery. They emit `Invalid` because each may retain grammar
children; ordinary sealed Error runs cannot. No other owner may acquire
`Invalid` by analogy without a schema amendment.

Expected syntax is specified by the containing production and documented slot,
not encoded as synthetic Expected nodes. The parser retains the selected
diagnostic facts until the node-schema projection proves each relevant mapping.
The schema must cover multiple expectations at one Missing, same-offset
occurrences, and recovery spans that differ from a raw Error token's source
range. A diagnostic occurrence is not presumed to have a one-to-one Error
leaf or range: retry-leading and prefix-consuming recovery intentionally break
that equivalence. It must not claim that immediate parent alone uniquely
determines every current diagnostic.

## Reference reconstruction

`syntax-reference` becomes a bilingual language/CST reference, not an
implementation chronicle. Its target structure is:

1. notation: XML-like node vocabulary, token/trivia encoding, byte offsets,
   Missing/Error/Invalid;
2. source root and trivia;
3. expressions, patterns, types, declarations, literals/rules and Yumark;
4. recovery: slot-derived expected syntax and individual diagnostic placement;
5. coverage: authoritative construct status and deferred forms.

Every construct page presents accepted surface spelling, source-order Rowan
schema, punctuation/trivia ownership and recovery placement. It excludes
function paths, parser judges, rollback/session lifecycle, fixtures, commits,
gate history and AST/direct parity. Historical implementation evidence remains
in design/progress records. EN/JA pages remain semantically paired. The first
reference vertical slice is notation, Root and recovery nodes; no broad page
rewrite is performed before that schema is reviewed.

## Construction gates

1. Review this direct-Rowan/recovery ownership and Error/Invalid schema against
   current typed-output, structured reservation, header and fence contracts.
2. Approve the narrow supersession list and XML-like node notation.
3. Mechanically migrate to a direct `GreenNodeBuilder`: delete `CstOutput`,
   move recovery publication without exposing it to lexical probes, and retain
   the old tree shape only for this bounded migration check.
4. Apply the documented Error-token/Invalid-node topology with the raw Item
   emission mode; add `Invalid` without renumbering existing syntax kinds.
5. Prove unchanged accepted source and selected recovery behavior with direct
   Rowan controls: nested structured recovery order, frozen header records,
   optional rejection, UTF-8/CRLF, retry leading, root/fence current-Item
   handoff, and public diagnostics.
6. Publish the reviewed notation/Root/recovery reference slice, then convert
   the remaining reference in authoritative construct batches.
7. Resume production Yumark document/frame construction using the direct CST
   owner; no AST/product/materialization prerequisite remains.

Rollback conditions: any second output representation, AST/product retention,
unbounded runtime accounting state, CST walk/replay, source-byte loss or
duplication, synthetic Expected node, optional-probe diagnostic mutation,
changed accepted input, changed recovery fact/order, or consumed outer boundary
returns the affected gate to design.
