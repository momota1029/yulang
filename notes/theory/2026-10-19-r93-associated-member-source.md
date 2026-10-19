# R93 paired association and exact member/declaration source bridge

Status: candidate constructive source-correspondence proof; fresh review pending.
Author: `/root/r93_proof_r1`; no descendants or coauthors.
Contract: R93 revision 2, `tasks/agent-loop/sprints/associated-member-source-correspondence-20261019-r93-rev2.md`, SHA-256 `dbdaf587eef269631060ce6e00fa0be620c25c57419b4b9b3e10a7cbe851aa3a`.
Baseline: `d34568a7ca062c8004122bf4a9ac8d7fa9434bb0`.

## Claim, hypotheses and application

Fix one successfully published `ShadowArtifact` A and its own immutable
`ParsedFile` P. Quantify over every complete accepted FieldTail in the entire
inventory returned by `A.pending_field_tail_sources()`, and every retained
RoleDeclaration or standalone ImplDeclaration in
`A.pending_role_impl_sources()`. An error is a refusal of the complete bridge,
not a successful empty or truncated inventory. The source domain, including
nested and repeated same-spelled occurrences, is the R93 contract's domain.

The constructor theorem below establishes that successful association creates
an ordered HIR/provenance pair and that a FieldTail continuation's child-zero
pair is exactly the previously accumulated associated receiver. The checked
join theorem establishes which finite identity/coverage checks suffice to
connect that pair to A's original tail and member. The declaration theorem
establishes the analogous same-parse occurrence join without association.
These theorems apply directly to R93's source prerequisite: there is no need
to reconstruct the receiver from R76's raw prefix. The remaining R93 premise
is that the final frozen bridge implements the checks, borrowing and complete
publication described below. This note does not certify the concurrent code.

Hypotheses are (H1) successful artifact construction and the R76 retained-tree
invariant; (H2) association on an actual OperatorChain node obtained from P,
with P's own operator table, returning `Ok`; and (H3) for the checked bridge
the explicit unique-key, complete-inventory and prepublication checks below.
H1 does not imply every association succeeds. H3 is a code correspondence
obligation, not an assumed language typing rule.

The original Simple-sub A/B parents stay OPEN 0→0, R50 NOT_ADOPTED and R85
AWAITING_USER_ADOPTION. No constraint generation, accumulation, propagation,
level, extrusion, qualifying intrusion, generalization or evaluator judgment
is changed or proved. No F1/FK1, foreign-continuation, provider, residual or
witness quantifier is discharged by this local source result.

## Ordered paired constructor invariant

For HIR h let C(h) be Value/Error children or Apply operands. For provenance p
let C(p) be Node/Synthetic children or the empty list for Token. Define Pair(h,p)
recursively: these lists have equal length and their corresponding entries
satisfy Pair. A Node additionally carries the actual source SyntaxNode and
agrees with h's Value/Error kind; Token is paired with a childless Error of
that token kind. Synthetic is used for Apply, recovery grouping and the
childless synthetic Missing result of an empty expression. No equality of HIR
range and source-node range is required: a continuation spans its receiver.

**Lemma 1.** Every successful `associate_chain_owned_with_sources(P,n)`
constructs Pair(expression, provenance), with provenance children in exactly
the HIR child order. Each retained source handle comes from that constructor's
input tree, not an independently parsed string.

Proof is mutual induction on the finite actual constructor evaluation, counting
recursive nested chains and decreasing expression cursor work. The complete
constructor cases in `lib.rs` are:

1. `item_expression` makes childless errors with childless Node or Token
   provenance; empty `expression` makes childless Missing/Synthetic. The
   operator-use error cases verify their actual operator definition first.
2. `value` and `invalid_expression` call `collect_nested_items` and then
   `split_associated`. The latter moves each input's hir and provenance into
   corresponding vectors in one loop. The former preserves discovery order,
   recurses into nested OperatorChains through the same association seam,
   retains recovery nodes/tokens, and descends through other syntax wrappers.
   Induction therefore gives the same ordered children on both sides.
3. `apply_one` and `apply_two` supply respectively [operand] and [left,right]
   to `apply`. `apply` splits this vector once and builds Apply/Synthetic with
   that same order. Its accepted binding powers are read from P's exact table
   by `operator`/`definition`; the proof assumes no alternative precedence.
4. `recovery_sequence` moves [left.hir,item.hir] and
   [left.provenance,item.provenance] into Value(OperatorChain)/Synthetic.
   Thus synthetic grouping also preserves Pair; it is not a source-node
   certificate and must not be treated as one.
5. `structural_continuation(left,t)` calls `value(t)`, checks its Value/Node
   shapes, and builds exactly

   ```text
   h = Value(kind(t), span(left.hir,t), [left.hir] ++ tail_hir_children)
   p = Node(t, [left.provenance] ++ tail_source_children).
   ```

   Both vectors prepend the same prior associated pair, then preserve the
   already paired tail items. Checked capacity arithmetic/reservations either
   fail or permit the full construction. No success returns half a pair.

The `expression` loop only combines these cases. Cursor exhaustion is checked
by `associate_chain_expression`; `into_associated` and
`into_projection_parts` move the existing pair without reassociation. This
exhausts the constructors; the Rust source, rather than a test transition
model, supplies the induction steps.

**Lemma 2 (receiver).** When that evaluation consumes an accepted FieldTail t
as a fixed postfix, its actual h child zero and p child zero are the exact
previous `left` pair from that evaluation.

`is_fixed_postfix` includes FieldTail. The fixed-postfix branch consumes its
actual node and calls `structural_continuation`; Lemma 1 case 5 proves the
claim by the two explicit moves. Its Node source is t itself, whereas its HIR
range spans left and t. A complete FieldTail's raw children are Dot and
Identifier, so it contributes no nested associated operand of its own.
The receiver therefore has the existing associated range, including any
constructor-owned leading trivia. No range trimming is licensed.

For `a.first.second`, the first construction has receiver a; the second has
the entire first continuation as receiver. The first remains a descendant of
the second, with its own source node and child zero. For a tail inside a call,
group or other nested chain, `collect_nested_items` embeds that chain's whole
pair; the same induction applies at its actual position. For a receiver that
contains dynamic Apply or synthetic grouping, paired descent traverses the
matching Synthetic children. It must not skip such subtrees or fabricate a
Node source for the synthetic parent. The input syntax reference requires an
initial operand: an arbitrary synthetic tree with FieldTail in operand slot
is outside the accepted claim and must fail the bridge's child-zero checks.

## Unique occurrence join and complete publication

R76 supplies the retained preorder bijection x ↔ PositionId_A(x), including
parent, ordinal, kind, exact raw range and ordered raw children. IDs compare
artifact Arc identity and index. `pending_field_tail_sources` checks the tail's
actual OperatorChain parent/ordinal, nonempty raw prefix, and exactly token
Dot/Identifier children. R76's raw prefix is reused only for these retained
syntax facts; it was never an associated receiver theorem.

`ParsedFile::source_root` and `SourceNode::children` are the minting path for
SourceNodeKey. Equality uses parse Arc identity, green allocation identity and
start offset. A spelling or equal range does not mint a key. In particular,
`AssociationProvenance::Node.source` is a SyntaxNode, not a SourceNode: obtain
its key from a same-P node/key traversal such as `source_identity::source_keys`
and check uniqueness; do not invent a `.key()` operation on the raw node.
The SourceNodeKey→position map marks repeated keys ambiguous. Reject missing,
foreign or ambiguous joins even if printed text matches. This is deliberately
a partial occurrence lookup for synthetic shared zero-width keys.

**Lemma 3 (checked field join).** Build one same-P source node/key index and
selected-tail key→inventory-slot index with duplicate rejection. Associate
disjoint outermost containing OperatorChain roots once; nested chains are
included by the authentic recursive constructor. Traverse each result as
paired `(h,p)` entries, checking child lengths before zipping. At a Node whose
source is a selected FieldTail, resolve its same-P key back to its exact A
position, check kind and nonempty paired children, and record the borrowed
child-zero pair in that tail's unique slot. Require exactly one match for
every selected slot and reject duplicate matches. Then every published field
record refers to its actual constructor-owned receiver and original member.

Proof: the key round trip supplies the unique original tail, H1 supplies its
member/parent facts, Lemma 1 supplies paired traversal, and Lemma 2 identifies
the receiver. Slot coverage supplies totality; duplicate rejection supplies
injectivity. Iterating slots in retained inventory order restores source
order even if paired-tree visitation order differs. An unexpected selected
occurrence cannot be silently dropped. An unmatched FieldTail encountered in
the selected root must also be refused or shown outside the selected domain;
complete inventory and H1 rule out the latter for an authentic selected root.

Validate all fields, role joins and all fallible staging before calling any
callback. A final single infallible callback over borrowed completed slices
then has all-or-nothing validation publication: a later join failure cannot
follow an earlier callback. This says nothing about arbitrary callback side
effects or panic recovery. Borrow the pair from the retained associated
roots for the callback's lifetime; do not return a dangling reference or
clone receiver subtrees. A second constant-number paired traversal is sound
if the same immutable roots and identity checks are used. It is not necessary
to retain root-to-occurrence paths or reassociate a prefix for each field.

**Lemma 4 (declarations).** For each retained RoleDeclaration or standalone
ImplDeclaration position, obtain its retained node key, check that P owns it
and that the key uniquely maps back to that same A position, and look it up
in the unique same-P source-node index. Check actual node kind against the
retained kind, with no duplicate selected position. Publishing these borrowed
nodes in retained order preserves occurrence, full raw range, lexical parent,
ordinal and kind. This follows directly from the same key and retention
invariants; equal text at two distinct positions remains two occurrences.
R76's constructor scope excludes a role-body impl tail that is not a standalone
ImplDeclaration. The result constructs no semantic RoleId, global membership,
implementation compatibility or selection priority.

## Source consumers, errors, cost and exact remaining premise

The source route is P's actual nodes → R76 `ShadowArtifact::retain` and pending
inventories → `associate_chain_owned_with_sources` → `ChainParser::expression`
and `structural_continuation` → same-parse checked paired bridge → borrowed
source views. `module::lower_ordinary_admission` already consumes the same
association seam and checks paired Value/Node children, but intentionally
admits a narrower ordinary projection; it is not a method/role consumer.
No route from these source views to generated method/role constraints,
propagation or native execution has been established.

The first missing semantic premise is an approved source judgment connecting
this exact lexical member/declaration occurrence and receiver type to the
complete eligible candidate/evidence set and constraints. Luna owns adoption;
the future method/role constraint-generation consumer owns its implementation.
The charter's later gate still applies. No choice of identity map proves that
judgment. This is the same semantic obstruction as R76, with the receiver
association prerequisite now constructively resolved, not a renamed theorem.

`AssociationError::{ExactOperatorEnvironment,StructuralInvariant,Allocation}`
are distinct in `lib.rs`. Missing operator role/table membership is the first;
wrong constructor/paired/join shapes are the second; checked allocation and
capacity failure are the third. Preserve errors from actual association at
the bridge seam; only the bridge's own checked shape failures belong in
StructuralInvariant. `lower_ordinary_admission` exemplifies distinct mappings
to ExactOperatorEnvironment, StructuralProjection and IdentityExhausted.
Any enumeration allocation error also needs an allocation-preserving mapping,
rather than a blanket structural map. This proof is a successful-result
argument, not a proof that every Rust allocation in the final overlay is
fallible or that resource exhaustion is recovered.

With N retained/source nodes, F selected tails, D selected declarations and M
associated nodes in the disjoint chosen roots, a once-built index and a
constant number of paired walks use O(N+F+D+M) expected hash work, plus ordered
map costs and any explicit ancestor-root discovery. Root discovery by climbing
each tail's ancestors costs O(F·H) in the worst case at depth H; this note does
not hide that term. The join must not add a whole-tree search per tail.
Auxiliary storage is O(N+F+D+M), with borrowed receiver views and no copied
receiver subtrees or retained root-to-occurrence paths. Existing preflight
limits and successful constructor termination bound the claim; this is not a
new depth limit or a native stack/peak-memory measurement.

## Reuse, falsifiers and omitted cases

Reuse R76 only for authentic syntax constructor scope, raw retention, lexical
occurrence identity and complete pending inventories. It does not prove an
associated receiver. Reuse `lib.rs`'s actual paired constructors independently
of historical test outcomes. R77 rev1's failed test (2 passed, 1 failed;
expected `b`, observed ` b`) is preserved as contract-recorded evidence that
constructor ranges include trivia; it is not success evidence. R77 rev2 was
never activated. No R77 overlay or unreviewed semantic candidate is imported.

Falsifiers for fresh review: either tail in `.first.second` receives the wrong
child; operator/grouping-sensitive association changes under the join; an
unvisited nested/Synthetic subtree loses a selected tail; source text/range
creates an identity; foreign/duplicate/missing keys are accepted; role/impl
order or kind changes; a callback precedes complete validation; receiver
subtrees are cloned; per-tail whole-tree searches appear; allocation/operator
errors collapse into structural errors. Each falsifies the stated bridge
premise rather than licensing a narrowed source domain.

Omitted: malformed/recovered/synthetic inputs as accepted programs; duplicate
zero-width key resolution; semantic RoleIds, member typing/lookup/dispatch,
impl eligibility/compatibility, constraint generation/solving, soundness,
principality, F1/FK1 and foreign continuations, evaluator/native execution,
callback panic handling and quantified native resource guarantees. Refusing
these joins is not silent successful omission of an accepted selected item.

## Frozen dependencies and writer receipt

The following direct immutable bytes were read and SHA-256 checked. The R93
implementation's concurrent `shadow.rs` overlay is not a frozen proof binding;
the final source correspondence, compilation and fresh independent reviews
remain Luna's pending integration premise. Rev2's partial shadow baseline is
`25150d99f8603bde46b62f0cef030351ae5a721ef32a32b11b06eb3d00730b78`;
R76's historical original shadow binding was `7fce00d94303e83b08d1dbd132b278489a0af85224f751d3e2a00de4b9804593`.

| Input | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/operator_table.rs` | `369ce0a3a8f5ac39da9da572cfe4fab6f61dd4ca07c554848cfcc44aa7051643` |
| syntax `operator-chain.md` (English) | `56cd8495ad0b14cddb4da9fa8088e43647ce4d522ffcab19a08857d2dda1c842` |
| syntax `call-field-path-tails.md` (English) | `0fbbe46d52328b0438c4acc5e2e958380efa45e74ef0020c4762383804d3c253` |
| redesign charter | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| R76 rev2 projection contract | `38142e65fa9a73e9efa073208ec5456da5e9fec22f984baf83b65e3e28b84ff8` |
| R76 source proof, author `/root/r76_proof` | `04b36001d9ccaaace8930d6304745928b03906f9e4e0a2d041f47223f543b275` |
| `notes/progress/2026-10-19-r76-method-role-implementation.md`, primary receipt | `680e9b17922a4b46cab9f62a7a5c455fba084754e0356daea868395dc2561029` |

R77 historical pins are carried by the frozen R93 contract; their underlying
preserved objects were not independently opened by this worker. An initially
read R76 inbox path was not the pinned progress receipt and is excluded as a
proof dependency. Rev1 stopped before writes on the operator hash typo; Luna
issued rev2. Read-only inspection and SHA checks only; no tests, builds,
probes, Git, source/test edits or descendants. Requested model/effort:
gpt-6.1-sol/high; observed model/effort: UNKNOWN/UNKNOWN. Original proof grant:
600 seconds cumulative, with rev1 elapsed UNKNOWN and charged, no renewal.
Exact total elapsed/remaining is UNKNOWN; no measured duration is invented.
Only this note and the assigned proof inbox are written; no scratch paths.
Freeze ends this assignment. The author cannot independently certify it.
