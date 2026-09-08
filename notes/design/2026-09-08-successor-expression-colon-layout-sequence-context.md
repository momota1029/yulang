# Expression Colon current-depth layout-sequence context

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-by: primary from independent architecture, ingress-map and
specification audits

Scope: source-free current-depth sequence ownership for successor Expression
and canonical Statement paths, and ColonApplication inline argument boundary
selection. This includes expression delimiters, Colon's local sequence,
root/braced/indented Statement sequences, Case/Catch arm sequences, active If
lifetime, VirtualStatementBlock, RecordPattern default-Expression and Rule
ordinary ExpressionList interiors while they route an Expression. Virtual is
included only as the already-authoritative root-style separator owner; its raw
recovery, ambient policy and aggregate certification remain open. RecordPattern
and Rule inclusion is limited to their direct ordinary-Expression bridges, not
their wider recovery migration. Independent Type, other Pattern and Yumark
sequence loops and their context ingress remain excluded; those owners do not
become implicitly covered.
It does not alter typed recovery role vocabulary, colon immediate body-layout
classification, accepted lexical Item scanning, literal grammar, public parser
dispatch or O4--O7.

Authority: the architecture's Unified Yulang3 rule, Shared session contract and
ColonApplicationTail outer-ownership sections; the ambient-claim prerequisite
amendment's active-If outer-owner rule; recovery-authority amendment §§1--3;
and the expression-tail handoff addendum. The prior Colon/With inline and
indented Statement transport designs explicitly defer this correction.

## Context and ownership

Introduce a private, `Copy`, source-free current-depth context separate from
`AmbientClaimContext`. Its finite value is either `None` or a typed
`SequenceOwner`; the owner is sufficient for Colon's binary query and must not
be inferred from `Stops`, `StatementLineHandoff`, indentation, or ambient
claims. It has no mutable session stack, allocation or replay state. Rust call
scope retains an incoming value, a fresh delimiter/sequence replaces it for
children, and ordinary return restores the retained caller value.

`SequenceOwner` is finite:

| entry / lifetime | owner effect on a nested Colon inline argument |
| --- | --- |
| direct standalone Expression | `None`: Colon owns comma and qualifying layout-newline boundaries |
| root canonical Statement sequence | outer-owned: Colon parses exactly one argument |
| VirtualStatementBlock | replace with its explicit virtual Statement owner: Colon parses exactly one argument; its existing comma/semicolon/newline and borrowed-close policy stay unchanged |
| RecordPattern default after `=` | replace with RecordPattern owner: Colon parses exactly one argument and returns the record comma/qualifying newline/close |
| Rule bracket atom, call or index ordinary ExpressionList | replace with Rule ExpressionList owner: Colon parses exactly one argument and returns the list comma/newline/close |
| Parenthesized, Call, Index, ProjectionTuple, ProjectionRecord | replace with local delimiter owner: Colon parses exactly one argument |
| Colon after its first inline argument when no outer owner was visible | replace with local Colon owner: nested Colon parses exactly one argument; this Colon owns its own comma/newline sequence |
| Indented or Braced Statement block | replace with local Statement owner: Colon parses exactly one argument |
| CaseInline, CaseIndented, CatchInline, CatchIndented, CatchBraced arm body | replace with its explicit arm owner: Colon parses exactly one argument without deriving policy from a comma stop |
| active If expression body / companion lifetime | replace with local If owner: Colon parses exactly one argument and leaves companion boundaries visible |
| ordinary prefix/infix operands, ML children and expression-tail continuation at the same depth | forward unchanged |
| Binding/Cast inline body and retry; For iterable and inline body; Case scrutinee | forward unchanged: these introduce no delimiter or sequence of their own |
| If condition / Case guard | retain their active If/arm owner and local introducer/arrow token stops |
| fresh nested delimiter or sequence owner | replace incoming owner for its nested contents; return restores it |

The context answers only whether an outer current-depth owner claims the full
Colon inline sequence. Existing owner parsers retain their distinct concrete
separator rules: a CatchInline owner need not itself own a comma merely because
it makes Colon parse one argument. Matching/inherited closes and active stops
remain token capabilities, not context substitutes. `AmbientClaimContext`
continues to govern strict dedent and If companion claims across ordinary
delimiters; it cannot represent this context because it intentionally crosses
them.

## Colon branch and boundary rule

After accepting `:`, retain the existing immediate physical-newline
classification before consulting sequence ownership: deeper indentation enters
an indented Statement block; equal/shallower newline emits the existing RHS
Missing and leaves the newline/Item with its outer owner. In particular,
`f:\n, x` does not enter a comma-first inline path.

For an inline first argument, snapshot the current context once.

- With an outer owner, parse exactly one argument under the unchanged
  threshold/ML/stops/baseline/line/fence/ambient contracts. Return comma or a
  qualifying layout-newline Item whole, including its leading, for that owner.
- With `None`, install Colon's local owner and parse one-or-more arguments.
  A literal comma or a qualifying physical newline whose following indent is
  `<=` the captured incoming base opens the next mandatory argument. A deeper
  newline is continuation, not a separator. A comma plus surrounding
  qualifying newline is one logical boundary episode: preserve its source
  trivia once, make no empty argument and emit no synthetic separator or
  Missing comma. A final qualifying implicit newline before End is a valid
  terminal boundary: emit its trivia once and return End without opening a
  Missing argument. Repeated or trailing literal comma retains the existing
  mandatory-item recovery behavior.

After a malformed initial/local argument, preserve the existing sealed
current-Item recovery and apply the same context-owned boundary rule before a
retry. Protected outer comma/newline/close/fence/stops remain pending and do
not create a second same-slot Missing. The three normalized exits, retained
Item/origin/line state, source ownership and effect-free optional rejection do
not change.

## Required propagation and exclusions

The implementation must thread the context explicitly through every Expression
and canonical Statement normalized entry that can recur at the same lexical
depth. It establishes/replaces at the finite entries listed above and forwards
through ordinary expression and inline Statement composition. It must cover
all direct expression-delimiter owners (`Parenthesized`, `Call`, `Index`,
`ProjectionTuple`, `ProjectionRecord`), root/braced/indented Statement loops,
VirtualStatementBlock, Case/Catch arm body modes and If body/companion lifetime.
Virtual establishes its owner for every admitted/retried child Statement;
nested delimiter/virtual entry replaces it and ordinary return restores it by
call scope. Its baseline zero, original separators, borrowed `}` and
`ambient.unavailable()` policy remain unchanged. Each accepted owner's normal,
Missing, Error, boundary and return exits restore its caller value by ordinary
call scope; no global depth counter is introduced. Binding/Cast/For inline
routes forward their incoming owner; If inline body replaces it with If, and
Case/Catch arm body replaces it with the selected arm owner. RecordPattern's
default-Expression and Rule's bracket/call/index ExpressionList replace the
incoming owner with their distinct local owner. Projection-record spread RHS
forwards the already-established ProjectionRecord owner. The cfg(test)
Yumark-cell wrapper passes an explicit ownerless test carrier solely to compile
the shared signature; it establishes no public Yumark bridge or certification.

Type delimiter/record/effect paths, Pattern paths other than RecordPattern
defaults, and Yumark embedded ingress and their public/header/full evidence
stay outside this construction. Do not give them a default context or claim
their nested Colon behavior is certified; a later owner inventory decides their
explicit bridge. Virtual's sequence owner here does not certify its raw
recovery or Yumark ambient policy.

## Required evidence

Preserve the accepted contracts `f: a, b` and standalone `f: a\nb` as two
Colon arguments, while `(f: a\nb)` has two outer elements and one Colon
argument. Cover braced/indented Statement, every Case/Catch arm mode and active
If companion as outer owners; nested delimiter suspension/restoration and
nested Colon; immediate `f:\n, x`, equal/shallow/deeper post-colon newline,
comma/newline clusters, repeated comma and trailing implicit boundary.

For recovery, verify Error before each owned/protected boundary, fresh/frozen
records, UTF-8/CRLF/fence coordinates, complete pending Items and leading,
threshold/ML preservation and effect-free rejected entry. Test actual context
entry and returned ownership, not CST shape alone. Retain existing accepted
normalized and grammar controls; do not update an expectation to accommodate
the prior `STOP_COMMA` behavior.

For actual normal and heredoc virtual interpolation, cover `f: a, b`,
`f: a\nb`, semicolon and borrowed-close controls, nested interpolation/delimiter
replacement/restoration, and malformed Colon operands before comma/newline,
borrowed close, EOF and fence. Preserve ambient unavailability and all existing
virtual separator/close/following-text controls. This evidence concerns Colon
ownership only, not Virtual's raw recovery migration.

For RecordPattern defaults, retain `{x = f: a, y}` and qualifying-newline
record-boundary ownership. For Rule bracket/call/index ordinary lists, retain
their comma/newline/close ownership across nested delimiters. These bridges
must replace, not forward, an enclosing owner.

## Execution boundary

This is M2: one implementation pass, at most one batched repair, then
specification/recovery and regression review. The existing lexical path adds a
bounded by-value context branch; no traversal, cache, retained Item vector or
allocation is permitted. Benchmark budget is zero samples/processes unless a
concrete new cost uncertainty arises. Synchronize task/index/ledger/daily
before commit. Stop this gate if an omitted ingress needs a new ownership
priority, a context leaks through a delimiter, or accepted grouping outside the
recorded authority changes.

## Construction result

Completed 2026-09-08. `SequenceContext` is a private, source-free `Copy`
carrier passed independently of ambient claims. Its finite owners are installed
at the recorded Expression/Statement, Virtual, RecordPattern-default and Rule
bridges; ordinary same-depth recursion forwards it. Colon now snapshots the
outer owner: it owns comma and qualifying layout-newline arguments only with
no outer owner, otherwise returns the entire boundary to the actual owner.
Immediate post-colon layout selection still precedes that query.

The initial implementation incorrectly treated a final implicit LF/CRLF as a
mandatory argument. One batched repair restored the accepted terminal boundary:
it emits trivia and returns End with no Missing, while literal trailing/repeated
comma remains mandatory-slot recovery. Focused Colon tests passed 12; the Rule
owner test passed; four named threshold/ML/effect-free controls passed; literal,
Yumark and Yumark-cell regression filters passed 35/14/5. The related
dependency cone passed 511 tests with one pre-existing, non-Colon operator
assertion reproduced identically on baseline `ac372aad`. Package check, scoped
format and diff checks passed. Specification/recovery and regression delta
audits found no remaining scoped defect. Benchmarks: zero samples/processes.
Type, other Pattern, Yumark production ingress, Virtual raw recovery, aggregate
certification and public cutover remain open.
