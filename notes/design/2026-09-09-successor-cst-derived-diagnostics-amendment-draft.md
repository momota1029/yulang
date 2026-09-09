# CST-derived syntax diagnostics successor amendment

Status: Reviewed

Drafted-by: primary from the user's CST-derived diagnostic direction

Reviewed-by: specification and compiler/recovery reviewers

Date: 2026-09-09

Scope: the ownership, representation and publication of malformed-syntax and
syntax-environment diagnostics after direct Rowan construction. This amendment
supersedes no accepted grammar, recovery continuation, current-Item ownership,
fence handoff or lossless-source contract. It defines the next direct-Rowan
gate only; it neither adds an AST nor implements type inference or an
incremental cache.

User direction: the parser produces only Rowan CST. Structural recovery is
represented by that CST and diagnosed while a frontend traverses it. The future
type-inference traversal performs that interpretation as part of its ordinary
CST walk. Environment-dependent invalidity is diagnosed from the selected
environment at the relevant CST occurrence, rather than being written into the
CST as `Invalid`.

## Decision

### One syntax tree; no parser diagnostic ledger

Parsing returns a lossless `GreenNode` plus the syntax inputs required to
interpret that particular tree. It does not return recovery records, diagnostic
IDs, reservations, a frozen-record cursor, an event sequence, an output
counter, a side tree or a `ParsedFile::diagnostics()` array. `scan_header`
likewise retains only the source identity, coverage, imports and complete local
operator facts needed to select parsing syntax; it does not publish header
recovery diagnostics or reconcile them with a later full parse.

`Missing`, `Error`, and `Invalid` are the structural recovery facts. The
documented grammar slot containing one of them determines its expected syntax
and recovery category. A syntax-schema interpreter derives diagnostics from
the red-tree occurrence and that slot:

* entering `Missing` emits its slot's missing diagnostic at the node's
  zero-width UTF-8 byte range;
* a maximal adjacent sequence of `Error` tokens in one slot and immediate
  parent emits one malformed-input diagnostic over the sequence's combined
  range. Ordinary trivia, `Missing`, a nested node, or a slot boundary ends
  the sequence;
* entering `Invalid` emits one wrong-slot/structured-recovery diagnostic over
  `Invalid.text_range()`, then visits its children. `Invalid` is not
  transparent: it can retain a valid nested subtree and still represent a
  required outer error.

The interpreter visits source order. Equal ranges are ordered by documented
slot order and occurrence ordinal. An occurrence identity is local to one
snapshot: `(tree occurrence path, grammar slot, diagnostic kind, ordinal)`.
The contract does not promise diagnostic IDs stable across source revisions.
Raw source ranges remain UTF-8 byte ranges. A `Missing` range is zero-width.

The public diagnostic result is an ordered sequence emitted by that one
analysis walk, not a field of `ParsedFile`. Each occurrence contains its
snapshot-local identity, UTF-8 byte range, grammar slot, diagnostic kind and
the schema-derived expected alternatives and primary alternative where they
apply. The kinds are `Missing`, raw `Error` group, structured `Invalid`, and
environment `ConflictingOperatorFixity`. Conflict occurrences additionally
retain the winning spelling, fixity, origin and range required to explain the
environment fact. Consumers obtain raw malformed spelling from the referenced
CST token group/source range; it is not copied into a second diagnostic ledger.

All four kinds share one preorder walk. An `OperatorHeader` conflict is emitted
on entry to its complete header occurrence, before diagnostics in its child
slots; ordinary node/slot traversal then continues in source order. This
explicitly replaces the former global `all recovery before construction`
ordering. A complete conflicting header which also contains a child Error is
therefore ordered as its enclosing conflict followed by that child diagnostic.

Every recovery-bearing slot must be specified by ordered child grammar,
including optional and repeated children, punctuation and trivia ownership,
consecutive zero-width `Missing` children, and any required ancestor context.
A parent node kind alone is not a slot identity. A required diagnostic that is
not distinguishable from the CST plus this grammar context blocks removal of
the old representation: repair the CST schema at its owner, rather than
retaining a hidden recovery fact or silently collapsing the diagnostic.

The earlier retry-leading diagnostic range is deliberately not retained. The
new malformed-input diagnostic covers its documented `Error` token group; no
parser-owned range may extend it with retry leading that belongs to the next
owner. Expected alternatives, primary choice and presentation wording are
schema constants, not parser-emitted facts or synthetic CST nodes.

Parser-issued `UnexpectedSyntax` categories, per-Item unexpected ranges and
expectation-source flags are retired. Their native lexical classifications and
construction provenance are not faithfully represented by opaque Error tokens,
and no compatibility field may recreate them as parallel parser state. The
successor exposes the raw Error group/Invalid subtree through the CST and the
schema-derived category described above. This is an intentional public
diagnostic payload change, not a lossless-CST change.

### Syntax environments and operator conflicts

The parser still needs a selected effective operator table before it can parse
the source. The full-parse planner merges imported capabilities followed by
source-header declarations in source order, retaining the existing
first-capability-wins rule. It returns the one immutable effective table used
by the parser; that exact table is retained with `ParsedFile` for frontend
analysis. This is syntax input required to interpret the tree, not a second
tree, recovery state or diagnostic ledger.

`ParsedFile` retains `source`, `revision`, `header`, `green`, the selected
`Arc<SyntaxEnvironment>`, and the effective operator table. It exposes the
environment key as a shorthand and exposes the selected environment and table
for analysis. It no longer exposes a diagnostic array. The existing
source/header allocation-identity validation remains.

During the same CST analysis, each complete local header operator occurrence
is compared with the accepted capability site in that retained table. If a
different site already won the same spelling/fixity, analysis emits a
conflicting-operator diagnostic at the local CST occurrence and uses the
winning site's stored provenance. This covers equal declarations too; it does
not compare binding powers alone. The comparison does not recompile operators
or retain a parser-produced rejected-conflict vector.

An environment diagnostic never writes an `Invalid` node. Its environment may
change provenance or duplicate-conflict facts while the selected effective
table remains the same, in which case the existing CST can be reused and only
analysis reruns. Conversely, a changed effective table can change recognition
or binding thresholds, so identical source text may require reparsing and is
not promised an identical CST. The actual reuse key is at least source revision
and effective syntax-table identity; provenance-only analysis dependencies are
tracked separately.

Header discovery remains a prerequisite for selecting imported syntax, but its
temporary tree has opaque bodies and is not diagnostic authority. Full-CST
analysis is the sole syntax-diagnostic publication path. Header/full streams
are not reconciled or compared as equal streams.

### Frontend integration and incremental boundary

`yu-syntax` owns the documented slot interpreter because it owns the CST
schema. It provides a local, callback-based interpretation operation for a
visited CST occurrence and a convenience whole-tree collector for tests and
tools. The operation has no parser mutation capability. A future frontend/type
walk invokes it while visiting the same slots and appends its results to that
walk's normal diagnostic sink. Until a real frontend traversal exists, the
collector is the sole executable integration and must walk every syntax child;
semantic failure or skipping a child must never suppress structural diagnosis.

No incremental cache is introduced by this gate. The initial safe unit is a
whole source revision with its effective syntax-table identity. A later
subtree cache must include its ancestor slot context and semantic/environment
dependencies, retain owner-relative ranges, and rebase those ranges at the
current occurrence. Green-node identity or an absolute range alone cannot
identify a diagnostic: repeated green subtrees and several zero-width Missing
nodes are both valid.

## Narrow supersession

On approval this amendment replaces only diagnostic-output obligations that
conflict with CST-derived publication:

1. `2026-09-09-successor-rowan-cst-only-amendment-draft.md`, **Output and
   diagnostic responsibility**, the retained-record portions of
   **Cursor-capability clarification**, the diagnostic-retention portions of
   **Rowan node notation**, Construction gates 3 and 5, and the conflicting
   rollback clauses. Its direct builder, lossless CST, `Error` token and
   `Invalid` node decisions remain in force.
2. `2026-09-06-successor-typed-output-recovery-amendment.md` only where it
   requires parser-published typed recovery records, record IDs, expectation
   facts, expectation-source flags, unexpected evidence, or node-plus-record
   atomic publication and finalization.
3. `2026-09-07-successor-structured-recovery-reservation-amendment.md` and
   `2026-09-07-successor-structured-recovery-extent-validation-addendum.md`
   only where they require reservations, emitted-token counters, record order,
   frozen reconciliation, or their parser-output verification.
4. `2026-09-07-successor-retry-leading-diagnostic-extent-amendment.md` only
   for its parser diagnostic range extension.
5. Earlier owner-specific/header/public exact-record commitments only insofar
   as they require those replaced diagnostic fields. Their accepted grammar,
   recovery ownership, source preservation, and continuation contracts remain
   authoritative.

The successor schema must list every affected slot before implementation; this
general rule is not permission to discard an unmapped required diagnostic.

## Construction and proof gates

1. Complete and independently audit the XML-like Rowan schema for every
   `Missing`, `Error`, and `Invalid` slot, including same-offset and structured
   cases. Publish the notation/Root/recovery slice of `syntax-reference` from
   that schema.
2. Specify and test CST-derived structural diagnostic order, range, grouping,
   expectations and Invalid preorder against representative malformed trees:
   adjacent Error fragments, separate adjacent slots, nested Invalid plus
   Missing/Error, valid nested syntax inside Invalid, UTF-8, CRLF and Yumark
   quote-prefix input. Include a complete conflicting OperatorHeader containing
   a child recovery and prove the specified enclosing-conflict-before-child
   order.
3. Change the full-parse operator planner into one reusable, non-diagnostic
   effective-table result; prove parse and analysis consult the same accepted
   site. Cover imported/local and local/local duplicates, equal binding powers,
   mixed fixities, malformed headers, header cutoff, and later valid facts.
4. In one API migration, remove parser recovery-record state, reservations,
   frozen reconciliation, diagnostic IDs and `ParsedFile` diagnostic storage;
   install the CST interpreter and environment-conflict analysis. Preserve
   accepted input, source losslessness and recovery continuation.
5. Connect the local interpreter to the actual frontend/type CST walk when
   that owner exists. Design cache units and invalidation separately; do not
   infer them from Rowan sharing alone.

Stop the affected gate if a selected header fact cannot be mapped uniquely to
its full-CST occurrence, a required structural diagnostic cannot be assigned a
slot, analysis could suppress a syntax child because semantic work stopped, or
an environment-only change would require an `Invalid` mutation. Resolve the
schema or ownership at the source; do not restore a parallel parser ledger.

## Verification and cost

This is an M2 cross-layer/public-contract migration. Before code, one
specification review checks the schema and changed observable diagnostics, and
one compiler/recovery review checks parser/planner/analyzer agreement and
continuation. The implementation uses one producer and one batched repair
round unless a new design contradiction appears. No benchmark process is
budgeted: the parser removes diagnostic allocation, and the only new work is a
linear CST interpretation that the future semantic traversal already requires.
Measure only if a concrete integration produces material uncertainty.
