# R76 constructor correspondence for unresolved method/role source input

Status: candidate constructive source-correspondence argument; independent review pending.
Author: `/root/r76_proof`; no contributing descendants.
Contract: `tasks/agent-loop/sprints/method-role-source-projection-20261019-r76-rev2.md`.
Scope: its fixed parser-produced FieldTail, direct RoleDeclaration and standalone
ImplDeclaration cases in one caller-selected ShadowArtifact. No source typing,
dispatch, candidate selection, semantic RoleId, solver or evaluator conclusion.

## Parent application and first missing premise

The immediate parent is the R76 source-input prerequisite, not Simple-sub A/B,
computation-forwarding preservation or evaluator correspondence. Those original
parents and all their quantifiers remain OPEN 0→0; R50 remains NOT_ADOPTED.
The contribution is a faithful, still unresolved source carrier that a later
approved method/role rule can consume without reconstructing occurrence or
lexical provenance from strings or successful solving.

The first missing premise for a typing/selection constraint is an approved
source judgment that, at the retained lexical source occurrence and receiver
type, relates the member spelling or declared role/implementation syntax to
the complete eligible candidate/evidence set and the constraints to generate.
Its owner is the later method/declared-role selection design and its eventual
constraint-generation consumer. Architecture §6.6 supplies index keys
`(RoleId, nominal head / structural shape class)` and `(method name, receiver
head)`; it supplies no eligibility, resolution, ambiguity, evidence or typing
judgment. The charter's later gate remains open. The October 5 Function
Pure/Handler call views concern a different source judgment. Consequently the
selection result here is `NO_SAFE_ROLE_SOLVER_SLICE`. Stop selection at that
premise; the independent source proof below does not assume it.

## Retention model and invariant

Let T be the finite ordered raw Rowan tree actually supplied by a successful
`ShadowArtifact::from_parsed`, including nodes, tokens, punctuation and trivia.
The entrypoint first checks `preflight` depth/element bounds and syntax
diagnostics; failure publishes no artifact. The claim is about successful
published artifacts, not every hypothetical malformed tree or scanner behavior.

For each raw occurrence x of T, define i(x) by the actual preorder traversal in
`ShadowArtifact::retain`. Define I(x) as the PositionId consisting of the freshly
allocated artifact Arc brand and index i(x). `RawElement::range`, `raw_children`
and `range_of`/`range_of_token` are the source owners of range/child extraction.
The retained descriptor is exactly

`(I(x), kind(x), range(x), is_node(x), I(parent(x))?, ordinal(x), [I(c) | c child of x])`.

**Retention lemma.** Every raw occurrence has exactly one descriptor with that
tuple, in preorder; every retained descriptor comes from exactly one occurrence.

Proof by the explicit traversal invariant. Initially the stack contains only
the root and the position vector is empty. Each pop assigns the current vector
length, appends exactly one Position and appends its new ID to its already
retained parent's children. Raw children are pushed in reverse enumeration
order, so successive pops visit them in increasing raw ordinal and complete
each earlier sibling subtree before the next sibling. The children arise from
`children_with_tokens`, so no punctuation/trivia child is discarded. Every
nonroot occurrence has one raw parent and is pushed once by that parent; no
other branch pushes it. Finite preflight and the finite tree imply termination.
The tuple fields are copied at this pop; no later step changes kind, range,
parent, ordinal or node/token status. The only later mutation is appending
children, whose induction establishes the exact ordered list. This proves both
coverage and uniqueness without using a spelling, range or output label to
manufacture ownership.

**Identity lemma.** I(x)=I(y) iff x=y within T; IDs from separately built
artifacts are unequal even for identical input bytes. `LocalId::eq` requires
both `Arc::ptr_eq` and equal index, and `position` first rejects a foreign Arc
then performs checked vector lookup. Cloning an ID preserves that same pair.
Raw `SourceNodeKey` lookup is a separate partial map: repeated keys become
`None` and return `AmbiguousSource`; they never merge PositionIds. Therefore a
claim about retained occurrences does not assert unique source-key lookup for
synthetic equal zero-width nodes.

**Lexical reconstruction lemma.** Starting at I(x), checked Position lookup and
its ordered child IDs reconstruct exactly the retained descriptor subtree of
x; repeated checked parent lookup reconstructs exactly its lexical ancestors
to the artifact root. Proof is induction on subtree height for children and
on finite source depth for parents. Parent indices are strictly smaller than
their children's indices, so ancestor traversal cannot cycle. The recovered
scope is this syntax chain, with no resolved namespace or semantic owner.
Reconstruction retains identity, range and structure; it is not source text
regeneration or a theorem about typing/evaluation.

## FieldTail source constructors

The syntax reference's direct CST states `FieldTail := "." Identifier`, with
Dot and Identifier directly in the tail; its target is a preceding sibling in
OperatorChain. Continuing trivia belongs to OperatorChain, outside the tail.
The actual `field_tail_normalized` starts FieldTail, emits the accepted dot,
then only accepts a nonboundary Identifier with empty grammar leading before
finishing the tail. Recovery instead emits Missing or a raw Error run and
finishes that tail; a later item is returned to the outer tail machinery, not
used to replace its failed member slot. Projection tuple/record tails and path
tails have distinct constructor kinds and are not FieldTail cases.

For an accepted tail t at raw child ordinal k of enclosing chain e, define its
raw preceding structure P(t)=children(e)[0..k]. Preserve P(t), including every
trivia element and prior continuation, rather than equating its last element
with an associated receiver expression. For example the raw prefix before
`.c` in `a.b.c` contains both `a` and `.b`; the tail `.b` alone is not an
associated receiver proof. The retained raw prefix is sufficient for a later
approved association consumer to recover its own input without loss.

The member spelling is the source slice at the exact retained Identifier token
range; tail range is the retained FieldTail range, distinct from any span
covering its preceding receiver. No identifier normalization is performed.

## Source declarations

`role_declaration_normalized` starts one RoleDeclaration before its visibility
or RoleKw token and finishes it after the parsed head/body path.
`impl_declaration_normalized` similarly owns one standalone ImplDeclaration,
its visibility/ImplKw and delegated impl-tail subtree. The claim follows these
node constructors, not identifiers that happen to spell `role` or `impl`, nor a
role-body impl-tail which is not a standalone ImplDeclaration node.

By the retention lemma, selecting exactly these actual node kinds yields each
occurrence once in retained preorder, preserving its PositionId, full range,
raw parent and child ordinal. Equal declaration text or equal names do not
collapse two occurrences. A nested declaration keeps its authentic lexical
parent chain; enumeration does not assert global membership or selection
priority. Header/body subtrees remain unresolved retained syntax accessible
through checked lookup and lexical reconstruction.

## Boundary and reusable evidence

Recovery refusals have two owners: `from_parsed` rejects a parse with syntax
diagnostics before publication; a projection may also reject an unsupported
retained shape. Neither failure is an accepted empty result or an accepted
repaired occurrence. Unsupported structural skeleton/ordinary lowering does
not make a well-formed raw source occurrence disappear from the artifact.

Only the actual parser-constructor and retention invariants above are reused.
No R74/R75 observer result, Debug label, effect preservation claim or historical
conditional theorem supplies a missing projection premise. R75's failed test
does not establish any result here. No F1/FK1 or provider/witness lineage is
identified or discharged by these source identities.

## Implementation binding and frozen evidence

The implementation source is `crates/yu-hir/src/shadow.rs`:
`PendingFieldTailSource`, `PendingRoleImplSource`,
`ShadowArtifact::pending_field_tail_sources`,
`ShadowArtifact::pending_role_impl_sources`, and
`PendingFieldTailSource::receiver_prefix`.

**Field enumeration theorem.** On successful enumeration, the output is in
bijection, in retained preorder, with all FieldTail nodes in this artifact.
Every output carries its actual tail ID, actual OperatorChain parent ID, exact
raw prefix length and actual Identifier child ID. The accepted structural
checks require a nonempty raw prefix, a node OperatorChain parent and exactly
two direct children which are token Dot and token Identifier. If any selected
tail fails a check, enumeration returns an error for the whole call; it does
not return the accepted prefix as a complete inventory.

Proof. The outer loop visits every retained position exactly once. Non-node or
non-FieldTail positions cannot append an output. For every selected node its
ID is regenerated from its actual vector index and artifact brand. Checked
parent lookup and the raw child-incidence check identify the exact parent and
tail ordinal; uniqueness follows from the retention lemma. The two-child
destructuring forbids extra trivia, Error/Missing children, non-Identifier
members and inserted recovery. The member ID is cloned from child one, not
derived from text or range. A successful selected iteration appends exactly
one record, and no other iteration has that tail ID. An early `?`/`Err` returns
no result Vec. Thus success has neither omission nor duplication and error is
not silently interpreted as a smaller inventory. Finite-allocation success is
the ordinary prerequisite of obtaining a Vec result, not evidence of typing.

**Prefix access theorem.** For an output generated from artifact A, calling
`receiver_prefix(A)` returns exactly P(t), as a borrowed slice of the original
parent's retained child list. It checks both IDs through A's `position`, checks
the tail's actual parent, the parent kind and the exact child at the retained
prefix length. A foreign artifact fails checked ID lookup before access.
Successful indexing of the tail at k ensures k is within the original child
list, making the returned prefix slice safe. There is no independent copied
receiver tree that could drift. Applying lexical reconstruction to every ID
in that slice recovers all preceding raw structure, with order and multiplicity.
No association precedence, resolved receiver type or method classification is
claimed by this raw-prefix theorem.

**Field reconstruction theorem.** Given A and any enumerated field record,
checked lookup recovers the original tail and enclosing chain, the precise
member token and their ranges, and the prefix theorem recovers P(t). The
tail's children recover its original Dot token as child zero. Reading A's
immutable source at the member token's retained range recovers the parser's
member spelling. Parent traversal recovers the original lexical ancestor
chain. Conversely, enumerating any supported parser-created FieldTail with
these retained facts reproduces this record, by the loop construction above.
Equality of tail IDs implies equality of the source occurrence, and all its
remaining fields are then fixed by its retained parent/children. This is a
two-sided reconstruction of retained syntax facts, not a complete source-text
round trip and not an inverse typing rule.

**Declaration enumeration/reconstruction theorem.** The declaration iterator
enumerates exactly retained RoleDeclaration or ImplDeclaration kinds, makes
one record `(actual PositionId, actual kind)` per selected vector entry and
preserves preorder. Parser construction gives these kinds to the direct role
and standalone impl nodes above; no other parser token has either node kind.
Consequently the retention lemma supplies exact occurrence coverage and
identity. Checked position lookup recovers full range, parent, ordinal and
children. The lexical reconstruction lemma supplies the entire syntax parent
chain and retained declaration subtree. Re-enumeration at that position gives
the identical record. The kind field is copied corroboration, not the source
of ownership. Semantic RoleId or implementation eligibility cannot be inferred
from this pair.

**Unresolved/refusal preservation.** These two APIs only inspect positions,
copy branded IDs/kinds and publish immutable source records. They invoke no
resolver, typing rule, constraint generator, solver, generalizer or evaluator.
There is therefore no transition that discharges unresolved declaration,
receiver or member meaning. In supported parser-produced inputs the exact
FieldTail constructor matches the structural checks. An unsupported receiver
representation outside the raw nonempty OperatorChain prefix, or a malformed
retained tail shape, is refused. Parser recovery reported by syntax diagnostics
is refused earlier by `from_parsed`; any retained recovery child in a selected
tail is refused by the two-child/kind checks. This argument does not assert
that arbitrary synthetic trees are validated as source programs, nor that
raw-prefix retention resolves their expression association.

Tests are the primary's separately authorized evidence, not a premise of any
lemma above. No test/build/probe was executed by this proof worker. The worker
used source reads and static byte hashing only. Independent compiler/spec
review, compilation and primary adjudication remain pending.

**Cost invariant.** Let N be retained raw positions, F selected field tails and
D selected declarations. Each enumeration scans N positions once and appends
constant-size records, so its successful time is O(N) and output storage is
O(F) or O(D). The field parent slot is checked using `tail.ordinal`, not a
linear sibling search. A field stores prefix length rather than copying its
prefix; checked prefix access borrows an existing slice in O(1) time/storage.
Traversing a returned prefix costs its actual length at the caller. The proof
does not promise constant total work for a caller that explicitly traverses
every prefix of a long chain.

Frozen binding received from Luna: the source API is stable at the hashes
below. Luna still owns final code-snapshot freeze and review assignment. A
different source hash invalidates this implementation binding until checked;
it does not silently inherit this argument.

| Input | SHA-256 |
| --- | --- |
| R76 rev2 contract | `38142e65fa9a73e9efa073208ec5456da5e9fec22f984baf83b65e3e28b84ff8` |
| `crates/yu-hir/src/shadow.rs` | `7fce00d94303e83b08d1dbd132b278489a0af85224f751d3e2a00de4b9804593` |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `crates/yu-hir/src/module/local_source.rs` (unchanged; no inference extension) | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/module.rs` (unchanged) | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| Field parser | `9e88d7ce18d8bd2d3c3bfa6fbdd6cac7e37032a21fedc35774c71597ff7a21bd` |
| Role parser | `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634` |
| Standalone impl parser | `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066` |
| Call/field/path syntax reference | `0fbbe46d52328b0438c4acc5e2e958380efa45e74ef0020c4762383804d3c253` |
| Architecture | `76b59a473c84a0654a40b7598c9a2d4ce54eeb512c6aa3f5213e95aa8fab44a5` |
| Redesign charter | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| October 5 Function views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

The new test file is outside the mathematical dependency set; Luna supplied
its snapshot hash `0b1e570845b62237ac8e19b94b29facc42b40b5bcb943676078b8e5c33eed53a`.
This worker makes no execution/pass claim about it.

Mutual TODO `R76-ROLE-SELECTION-LAW-1`: Luna owns the missing approved judgment
named above. Inputs must be authentic lexical declaration/member occurrences,
receiver types, supported source envelope and an independently approved
selection/evidence rule. The proposed future output is a source-to-generated
constraints correspondence preserving the complete licensed candidate set;
falsifier: an eligible source candidate is omitted, a label invents role
identity, a successful solve creates its own eligibility premise, or unrelated
ordinary Simple-sub constraints/lineages change. This TODO grants no new lease.

Worker cessation: `/root/r76_proof` has no descendants, compiler execution,
temporary/scratch files or other writes. Only this note and the exact assigned
inbox are outputs. Requested model/effort: Sol/high; observed runtime
model/effort: UNKNOWN. Grant: at most 600 seconds; exact elapsed/remaining
runtime is UNKNOWN (not reclaimed or renewed). The coherent candidate now
stops for fresh independent review and primary adjudication. No parent theorem
or production gate is closed by this submission.
