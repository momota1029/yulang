# R77 member receiver and declared-role source correspondence

Status: candidate constructive source-correspondence proof, independent review pending.
Author: `/root/r76_proof`, reused live identity for the R77 proof assignment;
no descendants or coauthors. Source implementation owner: Luna `/root`.
Contract: R77 revision 1, SHA-256
`26735a4d825ecd783856675dadb91b9d97df5f8b71e8f62d1fde06b92d8ce3b1`.
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`.
Activation is Luna's current-session receipt in `tasks/agent-loop/current.json`.

## Parent application and exact domain

The R76 result gives retained source positions, raw receiver prefix and
unresolved declaration inventory. R77's contribution is the missing identity
join to authentic association/parser products. It establishes no member
typing, dispatch, semantic RoleId, impl eligibility, selected candidate,
generated constraint, evaluator correspondence or production authority.
Original inference/evaluator and Simple-sub A/B parents retain their original
quantifiers and remain OPEN 0→0; R50 remains NOT_ADOPTED.

Fix one successfully published ShadowArtifact S and its own ParsedFile Q.
For member joins, fix an associated OperatorChain root and its nested
association closure, or pairwise disjoint outermost roots selected by stopping
the syntax walk whenever an OperatorChain is encountered. The selected source
domain consists of complete parser-produced FieldTail nodes in that closure.
A field tail is exactly direct Dot and Identifier tokens; its raw syntax
target is outside the tail. Role joins cover actual RoleDeclaration and
standalone ImplDeclaration nodes enumerated by R76, including nested nodes
when such nodes occur in the retained syntax. An impl-tail embedded in another
declaration without an ImplDeclaration node, a field named `role`, a PathTail,
and semantic role/impl instances are outside this fixed constructor domain.
Malformed syntax refused by S, and ambiguous synthetic source identity, are
not repaired into this domain.

R76's retention/brand proof is reused only for exact Position descriptors,
ordered raw children, checked lookup and lexical parent chains. It does not
prove an associated receiver: a raw preceding prefix is not that receiver.
No R74/R75 effect observer or historical conditional theorem is reused.

## Authentic source keys and partial bijection

In `yu-syntax/src/full_parse.rs`, only `ParsedFile::source_root` and
`SourceNode::children` mint SourceNodes. Each descent preserves Q's Arc parse
brand. `SourceNode::key` retains that brand, the exact green allocation and
start offset. Equality/hash inspect those identity components, not spelling,
textual equality or range equality. A ParsedFile clone preserves its brand;
a distinct parse with identical source text does not.

Walk Q's SourceNodes once and retain their authentic keys. For any selected
node n, the join to S is `S.source_position(n.key())`. This checks the parse
brand, then the artifact's retained source-key map. The map marks repeated
keys ambiguous; `AmbiguousSource` is a refusal, never a tie breaker. Conversely
a PositionId from S carries S's separate artifact Arc and checked vector
index. `S.position` refuses foreign artifact IDs even if their parses are
clones of Q. The parse brand and artifact brand serve different obligations.

For reverse lookup, inserting a second occurrence for an already present key
must mark ambiguity or fail immediately. The actual owner doing this is S's
`retain_source_position`, whose repeated-key map entry becomes None.
`source_keys`' ordinary SyntaxNode→key convenience map alone does not establish
reverse uniqueness; its overwrite behavior is not a proof that synthetic
equal zero-width nodes have one occurrence. Every relevant actual API lookup
uses `source_position` after that convenience lookup, so ambiguity is refused
at its retained owner. Successful unique source-key joins therefore form a
partial bijection between actual parse occurrences and S positions. Refusing
an ambiguous key preserves this statement without silently narrowing the
accepted ordinary parser-constructor domain.

## Paired expression/provenance invariant from actual producers

Define a paired tree relation B(h,p) on HirExpr and AssociationProvenance.
Every h child/operand is paired with the provenance child at the same index;
the two child lists have equal length. Node provenance retains the actual
source SyntaxNode used by its producer. Synthetic provenance records grouping
introduced by association and does not invent a source node. Token provenance
retains an actual error token and has no children. HirExpr ranges need not
equal source-node ranges: a structural continuation spans its receiver too.

**Producer lemma.** Every successful result of
`associate_chain_owned_with_sources(Q, root)` satisfies B, with no independent
reconstruction of source/provenance from output labels.

Proof by induction over the actual producer operations:

1. `value` and `invalid_expression` collect AssociatedExpr children, then
   `split_associated` consumes each child once and appends its HIR and
   provenance halves at matching indices. Their Node provenance copies the
   actual source node. `error` constructs matching empty child lists for
   Node/Token or empty Synthetic recovery provenance.
2. `structural_continuation(left,t)` obtains paired nested tail children from
   `value(t)`, prepends the exact moved `left.hir` and `left.provenance` to
   their respective lists, then appends the original corresponding tail
   children. Hence its HIR child zero is exactly the actual receiver `left`
   chosen by ChainParser, and its provenance is Node(source=t), with the same
   paired receiver at provenance child zero. A complete FieldTail has no
   nested OperatorChain, so this constructor produces one receiver child.
3. `apply_one`, `apply_two` and `apply` consume actual operands and split their
   halves together, producing Apply and Synthetic with identical index order.
   Prefix/infix/suffix binding powers are read from Q's retained operator
   environment by `definition`/`operator`. No new environment or raw-prefix
   association is substituted. `recovery_sequence` likewise moves both input
   halves together into a paired Synthetic grouping.
4. `collect_nested_items` recurses through wrappers, stops at each encountered
   nested OperatorChain to invoke its actual association producer, and appends
   the resulting pair exactly once. `ChainParser::take` advances one cursor;
   successful chain association requires complete cursor consumption. Combining
   the producer cases preserves B at each reduction and at the final result.

All fallible constructor errors propagate; the lemma is about successful
producer results and does not turn an association error into an accepted join.
This proves the pairing used by traversal rather than assuming two matching
trees from tests. It makes no separate linear-time claim about association.

## Receiver join, coverage and reconstruction

Traverse each association expression and provenance together, requiring B at
every visited pair. A selected FieldTail hit must be a Value of kind FieldTail
paired with Node provenance whose actual source kind is FieldTail, and must
have its receiver child zero. Authenticate that source node through Q's
source-key index and S's checked source-position map; validate the R76 exact
tail/member occurrence before indexing the hit by its authentic key/position.
Reject duplicate hits and mismatched/foreign/ambiguous source references.

**Receiver correctness.** For every such successful hit, its returned receiver
is a borrowed reference to the exact HIR child zero constructed by
`structural_continuation`, by the producer lemma. Traversal never re-associates
the raw prefix, guesses the immediately preceding sibling, or clones a
receiver subtree. Nested `.first.second` therefore joins `.second` to the
already constructed `.first` expression, and `.first` to its own actual left
input. Grouped and operator-sensitive input retains precisely Q's constructor
result; no assertion equates a raw prefix or source range with that result.

**Exact multiplicity.** Every selected FieldTail belongs to one direct chain.
The chain cursor consumes it once. The fixed-postfix branch calls
`structural_continuation` once for that occurrence; later reductions move the
result without duplicating it. Nested-chain collection visits each nested
chain once. Selecting disjoint outermost roots prevents the same nested chain
being associated again as an independent root. Thus every selected field
produces exactly one source-labelled pair, and no other constructor creates
that selected tail provenance. A paired traversal visits each resulting pair
once, so indexing yields one hit per selected tail. Independent two-sided
inventory checks must reject any missing or surplus/duplicate join before
publishing a complete inventory.

**Source order.** Association preorder is not source order: in `a.b.c` the
outer `.c` is visited before inner `.b`. Therefore a hash index of paired hits
is consumed using the retained parser-order field inventory, rather than
publishing traversal order. This yields source-order output without sorting
or repeated whole-tree searches. The same checked key fixes the original
member token, spelling/range and lexical occurrence; R76 reconstruction
recovers these independently from S.

The reverse of a successful join is lookup of its actual source key/position
and the paired actual association node. It reconstructs retained occurrence
and constructor correspondence only. A HIR kind, equal span, spelling or
successful solver result cannot create this reverse identity.

## Declared-role and standalone-impl join

Use the single authenticated Q node index above. Consume the R76 declaration
inventory in its retained preorder. For each `(position, kind)`, checked
lookup in S and the unique same-Q node index must establish the actual source
node's key maps to that exact position and its constructor kind equals kind.
Refuse missing/duplicate/ambiguous entries or either foreign brand.

**Declaration theorem.** Each selected declaration returns its original Q
SyntaxNode authenticated by its source key, with one join per retained position, in retained source order and
with constructor kind, range and lexical parents preserved. Proof: the unique
source-key partial bijection supplies existence/uniqueness on accepted joins;
R76's inventory supplies exact occurrence/order; source kind is validated
against the actual node and cannot be inferred from a display label. Two
declarations with the same spelling remain separate original occurrences
unless an actual key ambiguity is detected, in which case the API refuses
instead of identifying them. Their role/impl semantic identity stays unresolved.

## Complexity, missing premise and integration seam

Let P be raw parser nodes visited by the indexing/root walk, A the total
association/provenance pairs visited over disjoint chosen roots, F selected
field occurrences and R selected declarations. Under expected constant-time
hash indexing, one node walk, one paired traversal and one inventory join
cost O(P+A+F+R). Additional indexes and constant-size borrowed handles occupy
O(P+A+F+R) storage (a tighter implementation may retain fewer association
entries). The receiver subtree itself and root-to-occurrence paths are not
copied. SourceNode/SourceNodeKey green/Arc handle clones retain identity and
are constant-size; their child vectors are not cloned by correspondence.
Explicit traversal of a returned subtree is charged to its consumer. This
bound excludes the pre-existing association producer and does not certify its
operator scanning, recursion or nested collection as linear.

P counts raw parser elements (tree nodes including token leaves) processed
by retained inventory/index construction; self.positions-sized tables are
therefore O(P). It is not just the number of matching declarations or chains.
The separate method and declaration calls each build their own index a
constant number of times; this does not multiply the bound by F or R.

## Actual API construction and checked publication

`ShadowArtifact::visit_associated_member_receivers` uses the following actual
consumer path, in the source snapshot pinned below:

- R76 field enumeration selects every retained FieldTail once and creates a
  source-order `fields` vector. `selected[PositionId.index]` identifies exactly
  its inventory slot, with duplicate insertion refused.
- One `source_keys(&self.parsed)` walk authenticates Node provenance. A root
  walk pushes children in reverse order and stops descending at each selected
  outermost OperatorChain, giving disjoint roots in source order.
- Each root is associated exactly once with the existing producer and the
  same `self.parsed`. `into_projection_parts` moves expression/provenance
  into the retained result vector; it does not clone them or their receivers.
- `visit_pair` uses an explicit stack of borrowed pairs. Each pair's child
  counts/variant shape is checked before zipped descent. Node provenance also
  checks actual source kind, authentic source key, S-owned position and kind.
  A FieldTail hit writes its borrowed first child into the selected inventory
  slot; replacing an occupied slot fails. A field with no selected slot fails.
- After all roots have been traversed, every slot must contain one receiver
  and every field's retained prefix must pass its original checked lookup.
  Only then are callbacks invoked in `fields` order. Consequently an internal
  missing/duplicate/foreign/ambiguous/shape error delivers no callback. Callback
  panics or external side effects are outside the API's correspondence theorem.

`ShadowArtifact::visit_role_impl_nodes` builds one same-Q key index and walks
actual syntax nodes in preorder. For each RoleDeclaration/ImplDeclaration it
checks its authentic key/position against the next retained declaration, kind
and an unvisited source-position slot. It collects `(declaration reference,
SyntaxNode handle)` without cloning a syntax subtree. The final cursor must
equal the inventory length before any callback. Thus missing, duplicate,
wrong-order, kind or ambiguous-identity errors deliver no callback; success
delivers exactly the original nodes in source order. The returned raw Rowan
node is authenticated by this construction, not itself a new semantic brand.

There is no public foreign root or arbitrary caller-supplied provenance input
to either callback API. Every producer root comes from S's own ParsedFile.
Foreign-artifact PositionIds remain refused by the retained checked lookup,
and foreign parse keys cannot pass `source_position`. These facts supply
ownership at their constructors instead of inferring it from callback labels.

The explicit traversal stack uses O(A) worst-case borrowed entries and does
not assume that the parser's raw depth bound also bounds associated depth.
The existing association producer/result destruction is outside the new
correspondence complexity and stack-safety claim. Pre-existing producer error
or resource limits remain errors; this proof does not broaden its support.

The semantic boundary remains the first approved source selection/evidence
judgment connecting lexical member/role/impl occurrences and receiver types
to licensed candidates and generated constraints. No such rule follows from
the joins. Owner: Luna/later method-role semantic gate. This independent
correspondence result reduces the source-provenance prerequisite, while
inference/evaluator/A-B remain open with unchanged quantifiers.

## Dependency binding and handoff boundary

All fixed R77 activation pins were checked against live bytes. The relevant
constructor source is the source snapshot below; the ordinary association
producers remain unchanged from the activation input. This argument is about
these bytes, not an unpinned later implementation.

| Input | SHA-256 |
| --- | --- |
| R77 contract rev1 | `26735a4d825ecd783856675dadb91b9d97df5f8b71e8f62d1fde06b92d8ce3b1` |
| R77 `crates/yu-hir/src/shadow.rs` observed implementation | `9bf3e046a55206607527d2df3dde42b32afa814bc8d8b82c814583923aefc856` |
| R77 `crates/yu-hir/src/lib.rs` observed implementation | `afd9b382d95e2a8d22635eaf6b9bd8f134b80f5ebd35789265e236884b0fa58e` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/operator_table.rs` | `369ce0a3a8f5ac39da9da572cfe4fab6f61dd4ca07c554848cfcc44aa7051643` |
| OperatorChain reference | `56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842` |
| FieldTail reference | `0fbbe46d52328b0438c4acc5e2e958380efa45e74ef0020c4762383804d3c253` |
| Redesign charter | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| R76 contract | `38142e65fa9a73e9efa073208ec5456da5e9fec22f984baf83b65e3e28b84ff8` |
| R76 proof (retention only reused) | `04b36001d9ccaaace8930d6304745928b03906f9e4e0a2d041f47223f543b275` |
| R76 implementation receipt | `680e9b17922a4b46cab9f62a7a5c455fba084754e0356daea868395dc2561029` |
| `crates/yu-hir/Cargo.toml` | `a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1` |

Source-freeze receipt remains pending from Luna at proof submission. The
candidate's implementation binding is conditional on Luna freezing exactly
the two observed source hashes above; this packet does not claim an immutable
implementation snapshot before that receipt. Changed source bytes invalidate
the implementation binding until explicitly checked.
Tests are not proof dependencies; this worker executes no compiler/test/probe
command and makes no claim about the primary's forthcoming verification.

Mutual TODO `R77-METHOD-ROLE-SEMANTIC-LAW-1`: Luna owns the first missing
approved source rule described above; required inputs are actual lexical
occurrences and receiver types, accepted source envelope and candidate/evidence
law. Proposed next semantic output is source-licensed constraint generation;
falsifiers are omitted licensed candidates, semantic identity created from a
label, or solving used to establish its own eligibility prerequisite. No new
semantics, lease or production permission follows from this request.

Requested model/effort Sol/high; observed model/effort UNKNOWN. R77 proof grant
600 seconds with no carryover or renewal; exact elapsed/remaining time UNKNOWN.
Only source reads, manual derivation and static SHA checks were used. No
descendants, Git, compiler execution or scratch/new paths beyond the exact
leased note and its inbox. Fresh compiler/spec review and primary adjudication
remain required; this producer cannot certify its own result.

Writer-stop receipt: `/root/r76_proof` stops writing both R77 leased outputs
after the coherent handoff. There are no descendant or scratch leases. This
is a stopped candidate awaiting primary source freeze/review, not a worker
still computing or an independently reviewed parent closure.
