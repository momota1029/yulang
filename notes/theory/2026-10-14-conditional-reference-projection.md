# Conditional reference fragments: exact projection and unchanged qualification

Status: independently reviewed bounded theorem and source correspondence;
primary acceptance recorded in §8. Global inference claims remain open.
Baseline: `c34723114aee241a7dc1237b78b01a3b3e918d3e`.
Branch: `research/simple-sub-intrusion`.
Exclusive output lease: this file; leaf only, no delegation.
Method: source-constructor induction and path contraction, no executable probe.
Verification/review owner: primary.

## 1. Frozen statement and authority

Authority is `notes/design/2026-10-14-conditional-value-references.md`,
“Already determined”, “Choice A: condition and every branch (selected)”,
“Current graph consequence”, and “Verification and scope”. The primary
recorded the user's direct `Aですね．` approval. This extends the earlier
parent-copy SCC design's “Apply-result source-fragment ownership” and “Nested
Apply membership” only to the named Name/Apply/If fragment constructors.
“Definition-root Value ownership” and the association design's “Approved
extrusion-event qualification” / “Definition-root origin” remain unchanged.
Top-level inference principles §§1.1–3 govern the mathematical operation,
cost accounting and implementation correspondence.

Quantify over every finite successfully authenticated LocalSource tree in the
existing private carrier envelope at the baseline: Unit, Operation, Integer,
Boolean, String, Name, Apply, If, Group, Ascription, Lambda and Block; If has
one or more condition/body arms and an explicit else. Retain its exact
DefinitionRootId, artifact, HirOccurrenceIds, Module DefIds, Local IDs,
Parameter IDs, scopes, resolved identities and nested initializer ownership.
The claim also applies when such trees are retained into one successfully
collected and sealed finite batch. Each tree's helpers are fresh and disjoint;
its semantic named Values use the existing identity interner.

Let N denote the tagged Module/Local/Parameter Values and X the tagged
Expression(HirOccurrenceId) Values. V = N disjoint-union X contains every
semantic Value interned by either compared construction. For comparison,
adjoin any newly interned If Expressions as isolated vertices to the old
graph. They are existing source identities, not new aliases. Helpers H are
disjoint from V and have no Value descriptor.

Define eligible forms P = {Name, Apply, If}. For an occurrence x, define the
finite set Sel(x) of resolved Name **occurrences** by structural recursion:

- Name x: {x} when its resolution is ModuleDef, Local or Parameter; otherwise
  empty. Targets are its retained tagged resolution, never its spelling.
- Apply x: Sel(callee) union Sel(argument), but recurse into a child only when
  that child's immediate form is in P.
- If x: union Sel(condition) and Sel(body) for every arm, plus Sel(else), with
  the same immediate-form test. No condition evaluation chooses a subset.
- Every other form: empty for this fragment selection.

Group, Ascription, Lambda and Block are thus fragment boundaries. They remain
transparent only to their already distinct definition-owner traversal where
that traversal already descends them. A Block initializer changes the
definition owner to that binding's original Local ID; other structural children
keep their enclosing owner. Lexical resolution and graph reference ownership
are separate retained facts.

The approved construction G_A allocates one helper F(x) for every eligible
occurrence. F(Name) points to its resolved named Value, if any. F(Apply) points
to each eligible immediate callee/argument helper; F(If) points to every
eligible immediate condition/body/else helper. Every Apply or If result
Expression points to its own helper. The existing owner-to-resolved-Name edges
are retained directly. No edge targets a nested result Expression, and no edge
enters any Expression Value. Only Apply occurrences produce the existing call
associations, with their original definition owner and callee receiver.

Required conclusions, fixed before derivation:

1. First semantic endpoints reachable from F(x) with only helpers in the
   interior are exactly the retained resolutions of Sel(x). Every selected
   occurrence has its corresponding path; duplicate target identities may
   coincide without replacing the original occurrence facts.
2. Contracting helper paths preserves reachability and SCC equivalence on V
   against the direct selected graph D_A defined below.
3. Compared with the baseline constructor G_0 on the same source trees,
   semantic Value SCC membership and each original call-event qualification
   are unchanged. Numeric component/vertex labels are not compared.
4. Retained helper vertices/edges and constructor incidence work/storage are
   linear in source incidences, without materializing every Sel(x).

The statement excludes forged arenas, cross-artifact/cross-session IDs,
arbitrary graph mutations after seal, failed partially retained private
collections, constructors outside this envelope, omitted else, additional
incoming Expression edges and definition/result identity aliases. These are
the assigned route's existing boundaries, not restrictions invented for this
proof. It does not claim whole-source semantics, complete Call, native typing
preservation, effect hygiene, principality, termination of inference or F5
cutover. Those original gates remain separate.

## 2. Actual source premises at the pinned baseline

`crates/yu-hir/src/module/local_source.rs` supplies the source premise rather
than an assumed transition checker. `form` dispatches each pending formation
responsibility and rejects uncompleted slots before returning. `slot` (line
464) reserves a fresh increasing ordinal with the original root brand; `set`
(line 480) mints the occurrence and retains the original source key, range,
scope and form. Existing non-If slot/schedule uniqueness is the flat-formation
proof §§3–5, rechecked at these current owners.

The If extension's actual owner is `Builder::conditional` (line 730). For each
IfArm it reserves two distinct fresh slots and stores exactly those two indices
in arms; for the unique ElseArm it reserves one fresh slot. It rejects a second
else, arms after else, absent else and absent preceding arms. It stores the
parent once, then schedules each distinct child once with the parent
Expression scope and a lexical Restore boundary. Each index is allocated
after the parent. Parsed arm children are distinct proper CST descendants;
no transition schedules an ancestor. Thus this new case preserves both the
single-owner pending-slot invariant and the acyclic structural tree. Each
condition/body starts in the original enclosing lexical environment. A nested
Block still introduces only its own retained local IDs. No name is re-resolved
by graph construction.

At baseline `candidate_value_graph.rs`, `resolved` admits only ModuleDef,
Local and Parameter targets. `intern` retains the tagged Value identity;
helpers are allocated separately in adjacency arrays. `retain_source`'s first
work loop already visits **all** If conditions, bodies and else with the
enclosing definition owner. Its Block arm switches only each initializer to
its own Local ID. The proposed extension leaves this loop unchanged.

The baseline second pass allocates Name/Apply fragments, emits Name-target and
Apply-result/helper-child edges, and records each Apply event. The new If
fragment and direct-If-child membership are the precise changed premise;
baseline code alone does not establish that the new edges are emitted.
Section 6 bridges the primary-frozen actual extension at those constructors.

`candidate_source.rs:190` retains this very LocalSource graph before its
constraint emission. Its Apply check at line 452 and the graph event use
`ConstraintOccurrenceId::new(apply.occurrence, 0)` to join by original
occurrence identity. `lib.rs:1001` registers actual module roots;
`:1413` and `:10122` seal the retained graph before the corresponding solver
route. The present derivation uses those actual collection/session owners;
it is not valid for arbitrary later edge edits that leave vertex counts equal.

## 3. Exact fragment endpoints and semantic projection

Induct on the structural size of x. For a Name, its only possible outgoing
helper edge is the actual resolved named Value, matching Sel(x); an unresolved
or ambiguous Name has no such edge. For an Apply or If, every first edge from
F(x) goes to exactly one eligible immediate child's helper. Such a child is a
proper descendant, so the induction applies. There are no other outgoing
edges from that helper. Taking the union over exactly those children gives
the first conclusion in both directions. Each selected Name occurrence yields
its actual descendant chain, including every elsif condition and body. Literal
conditions are leaves with no Name edge; their truth value cannot select or
discard another child's path.

The helper-only subgraph is a DAG: every helper-to-helper edge goes to a later
allocated structural descendant. Paths terminate either at a Name's named
Value or at a helper leaf with no outgoing edge. This argument uses the source
constructors above, not an invariant merely asserted in a code comment.

Define D_A on V by the unchanged definition-owner edges and, for every Apply
or If x and n in Sel(x), the direct edge X(x) -> resolution(n). It has no
helper vertices. An interior-helper path between semantic Values in G_A must
start with an Expression-to-own-helper edge, descend that exact fragment, and
end at a Name resolution. Conclusion 1 contracts it to an edge of D_A.
Conversely every selected edge in D_A expands to its corresponding path in
G_A. Direct owner edges are common to both constructions.

Decompose any path between u,v in V at successive semantic Values. Every
piece contracts to a direct D_A edge, so G_A reachability implies D_A
reachability. Expanding each edge gives the converse. Empty paths are common,
so this holds also for u=v. Mutual reachability and the SCC partition on V
are therefore identical. This establishes the exact selected-reference
projection without flattening duplicated incidence lists.

The “first semantic endpoint” qualifier is essential: unrestricted reachability
from a fragment can continue through the selected named Value's own definition
references. For example a selected f that references g permits the path on to
g. The claim does not wrongly identify that entire transitive reachable set
with Sel(x). The direct graph D_A retains this continuation exactly.

## 4. SCC and original association qualification are unchanged

Every edge in either G_0 or G_A has one of the following forms:

| Edge source | Edge target | Owner |
| --- | --- | --- |
| Named Value | Named Value | Definition-owner resolved Name incidence |
| Expression Value | Helper | Apply/If result's own fragment |
| Helper | Proper descendant helper | Eligible structural child |
| Helper | Named Value | Resolved Name fragment |

In particular a path starting in N never leaves N. The induced graph on N is
identical before and after the extension, since the existing definition-owner
loop already follows every If child and keeps initializer ownership. Therefore
every pair of named Values has unchanged mutual reachability. An Expression
Value has no incoming edge and cannot be on a nonempty returning path; each
Expression remains a singleton SCC, including newly interned If results.
It cannot share an SCC with a named Value or a distinct Expression. Hence the
whole semantic Value partition is preserved under the identity comparison in
§1. New helpers may alter DFS/component labels without altering that fact.

Events arise only from Apply occurrences. Their origin is the retained
definition Module/Local owner, hence in N. Their receiver is the original
callee Value selected by `expression_value`: resolved Name gives its N
identity, Group/Ascription unwrap to the same callee identity, and other forms
give their original Expression identity. This receiver operation does not
unwrap fragment boundaries or identify a result with its enclosing root.

For a named receiver, qualification is unchanged because its named SCC relation
with the origin is unchanged. For an Expression receiver, it is false both
before and after because N cannot reach X. The extension creates no If event
and changes no original Apply occurrence, owner or receiver. Thus every
original event has the same qualification boolean, including If-valued callees
and calls nested in If children. This is a proof for the exact current edge
construction, not a general promise for a future graph with incoming X edges.

Reuse the independently reviewed activation mechanism result
`2026-10-14-value-intrusion-activation-correspondence.md` §§4–6 at its actual
consumer: `retain_extrusion_parent` tests a complete immutable source-event set;
`finish_candidate_extrusion` and `recapture_candidate_extrusion` use the same
qualification predicate; settlement consumes actual pending pairs. For any
fixed actual retained source set S, each event's preserved boolean gives the
same Q(S), and hence the same activation decision for the same actual
extrusion/reuse records. No separate origin/receiver witness is selected.
The changed graph introduces no parent/copy, witness, attachment, provider or
residual identity and changes none of their lineage fields.

This applies the reviewed graph/activation interface lemma only. Its historical
source envelope did not contain If, so that review is not treated as a review
of this new source case. Inference histories on two different source programs,
or global applicability of propagated event sets to all new source operations,
are not equated. No new equality-preservation or hygiene conclusion follows
just from unchanged qualification.

## 5. Linear construction and retained storage

Let n count retained expression occurrences, b retained Block bindings, a
Apply occurrences, i If occurrences, m Name occurrences, and c structural
child incidences (including Block initializer links). For authenticated trees,
c is O(n+b); summing over finite batches retains the same bound. An If with k
arms contributes exactly 2k+1 child incidences, not a fixed arity assumption.

There are m+a+i helpers, at most m helper-to-named edges, at most a+i
Expression-to-helper edges, at most c helper-to-child edges, and at most m
definition-owner edges. Reverse adjacency retains one entry per forward edge.
At most one event/checking entry is retained per Apply. Each eligible child
helper is allocated once and reused by its parent, and its own Expression
points to that same helper. An ancestor never copies a descendant's selected
Name list. This rules out quadratic expansion on long nested Apply/If chains.

The owner traversal visits each structural occurrence once with its unique
owner. Fragment allocation and emission make constant passes over expressions
and their child incidences. Owners/fragments/work, adjacency headers,
semantic interning entries, edges, events/checking and iterative SCC scratch
are O(n+b+c) structural entries, plus registered external identities. Iterative
Kosaraju is O(vertices+edges) adjacency steps as in the existing projection
theorem. If qualification reuses the sealed components, it adds no traversal.

This is a structural entry/work bound, not a universal allocator/RSS or
worst-case HashMap runtime guarantee. Tagged Module identities have retained
payload bytes and hashing/equality cost; include their actual payload measure
separately. Amortized vector growth and expected hash operations give the
usual linear incidence cost. `expression_value` can separately walk an existing
Group/Ascription callee chain; the extension adds no such walk and does not
claim that all unrelated name-resolution/emission work is linear. No benchmark
or runtime sample was taken.

## 6. Frozen implementation bridge

The primary supplied final `candidate_value_graph.rs` hash
`a9c75499d2da1d0f52568db1ce3ed1d5465501e7952bc160e81cdaf9d84d19a6`;
the leaf rehashed that exact snapshot and rechecked its production diff.
Production construction is identical to the initially inspected snapshot
`82501be79da6e9edf64939dcc2b130bc9f11cc92641bd8ad16c5065cc3ab4b8a`.
The final delta repairs only private source-test fixture syntax/diagnostic
context. Neither a test result nor that fixture repair is a proof premise.

Actual correspondence, at this snapshot's line numbers:

| Original construction premise | Actual emitted action |
| --- | --- |
| Exact eligible set | Lines 112–118 allocate exactly one fresh helper for Name, Apply or If and None for every other form. Helpers are absent from the Value interner. |
| Name termination | Lines 121–125 emit exactly the helper-to-original-resolved-Value edge; `resolved` at 54–57 admits only N. |
| Each If result's own fragment | Lines 127–130 intern its original tagged occurrence and emit its own helper edge. |
| Every condition/body/else | Lines 131–136 iterate every arm, both fields, and the explicit else once, consulting only fragments[child]; no Boolean value or branch outcome is read. |
| Direct If children of Apply | Lines 138–144 retain the existing Apply edge loop; the eligible fragment table now supplies Some for a direct If as well. |
| No wrapper expansion or result-containment edge | None entries skip Group/Ascription/Lambda/Block; every selected child target is its helper ordinal, never its Expression Value. |
| Original owners and call events | Lines 66–105 are unchanged; only Apply reaches lines 145–149, retaining the same occurrence/check slot, owner, and `expression_value` receiver. If falls through the non-Apply continue and creates no event. |
| Reverse edges and SCC consumer | `edge` at 47–52 still inserts forward/reverse entries together on success; `seal` 159–183 and `qualifies` 184–186 are unchanged. |

All edge-emitting sites in production retain exactly the four forms of §4.
All helpers are allocated before child links are emitted, so ordinal use does
not depend on which child is processed first. The authenticated index and
single-write premises make each fragment unwrap/child lookup valid. Checked
allocation failures still abort collection via the existing owning `?` route;
this theorem asserts no partially collected graph's publication or activation.
The diff against the pinned baseline changes only eligible-helper allocation,
the If edge loop, its explanatory comment, and private tests. No graph event,
owner, interner, receiver, sealing, intrusion or solver consumer is changed.

Thus the derivation's transitions are traced to actual source constructors,
not supplied by a checker. At producer handoff this was an unreviewed bounded
derivation; subsequent independent review is recorded in §8. Tests authored/run in the implementation lane are
not premises. No claim about all inference histories is added by this bridge.

Only one direct proof method was attempted. No two materially different failed
routes left the same premise untouched. The remaining action is independent
review, rather than another semantic relation or
reconstruction layer.

## 7. Producer handoff: dependencies, checks and commit packet

| Dependency | SHA-256 |
| --- | --- |
| Baseline `crates/yu-solver/src/candidate_value_graph.rs` | `449b223d11a7b3c5286fd8c1277ff1d2c48ced52927622d98dbef173f0459346` |
| Final frozen `crates/yu-solver/src/candidate_value_graph.rs` | `a9c75499d2da1d0f52568db1ce3ed1d5465501e7952bc160e81cdaf9d84d19a6` |
| Approved conditional-reference design, primary's recorded A | `4c37fdef212b59ef686f10da5ba0ce35dc71b59589ebb502376fa7ba03ea3b2a` |
| Existing activation correspondence | `72ac1d304a556fc1af1bfe8757aaac8b920338168553149e87def671b60ef4a1` |
| `crates/yu-hir/src/module/local_source.rs` | `fab5436a6f37b795c7fb6553c320e2ed942d2ab850d3a446c1fa3e2e3c6ceeaa` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e` |
| `crates/yu-solver/src/candidate_source.rs` | `4060efb4177b26d5afc395a138fb24c7ef2a641a64f547755775b2c9bd801fd7` |
| `crates/yu-solver/src/lib.rs` | `91938447f78b6ca6b252a67641f30c2e20f05193d112aa7f0019a87caf6f93e3` |
| Flat LocalSource formation proof | `4f9c43ece1127baf29d3b5737a96abd41f9baeb16115b654b73d2f03bec74424` |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Parent-copy SCC design | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| Intrusion association design | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |

Commands used: bounded `cat`, `sed -n`, `rg -n`, `nl -ba`, read-only `git show` /
HEAD/status/diff, and `sha256sum`; `apply_patch` writes only this leased note.
No tests, builds, semantic probes, benchmark samples, heavyweight processes,
child workers or Git mutations. Static process concurrency never exceeded
three shell reads; verification remains primary-owned. Budget: one leaf,
ten-minute initial derivation allocation, plus the primary-requested narrow
frozen-constructor bridge; no wall-time/RSS measurement was taken.
Requested routing: normal `gpt-6.1-sol` / high. Configuration registers prover
with absent model/effort pins and those normal defaults; observed live
model/effort metadata are unknown. No Astra escalation or routing change.

The local_source, candidate_intrusion, candidate_source and lib dependency
hashes were individually checked equal to the pinned baseline. Final HEAD
remained the baseline and the approved A design hash was unchanged. Concurrent
primary-owned navigation/task edits are outside the proof's premise set and
were not modified by this leaf. Unverified: independent review and all excluded
global inference/semantic claims. One next action: primary assigns fresh
independent review of this frozen note and dependency combination.

Commit packet: exact leased path
`notes/theory/2026-10-14-conditional-reference-projection.md`; baseline
`c34723114aee241a7dc1237b78b01a3b3e918d3e`; changed direct dependencies are the
approved A design hash and constructor snapshot recorded above.
Claim/review status: Draft/unreviewed bounded construction derivation with
inspected source correspondence,
no producer certification. Checks: static source/authority/hash inspection
only. Proposed checkpoint message:
`research: derive conditional reference fragment projection`.
Shared-record deltas left to primary/curator: link the exact projection/SCC
candidate, record its pending independent review honestly, preserve source-global
intrusion applicability, typing preservation, complete Call, effect hygiene,
principality and F5 gates OPEN. No shared record changed by this leaf.

## 8. Independent review and primary acceptance, 2026-10-14

A fresh `compiler_referee` reviewed the original frozen derivation
`e2680680b919788dfda550dc3dbf6556deb8b4b1b0655b467d70959623dd34ce`,
the approved design and code hashes in §7, and the actual source/collection/
sealing/qualification owners. No blocking or major finding was identified.
The primary accepts the exact first-endpoint projection, contracted direct
reachability/SCC equivalence, unchanged semantic SCC/event qualification,
actual constructor correspondence and structural linear incidence bounds.
These conclusions discharge this bounded Choice A obligation only.

One minor verification gap concerned conditional callee and Lambda fixtures.
A subsequent test-only addition exercises `(if p: f else: g) x`, the original
If receiver after Group unwrapping, its named origin, false qualification and
the enclosing Apply fragment's Group boundary. Seven graph tests pass. The
final file hash is
`0a0bbf4cbdfddedfc1c5658df12569cd60d8b943cd726b68b42c68d3622092ed`;
the primary inspected the addition and unchanged production section. The
Lambda boundary is statically covered by the eligible-set proof: current
LocalSource creates Lambdas only for definition parameters (`local_source.rs`
325, 368), with no expression constructor for a direct Lambda child. No
synthetic source fixture or broader syntax is invented. A direct ungrouped
If callee fixture remains absent; the symmetric Apply child loop is covered
by the proof and direct If argument fixture. The primary closes this minor
item with those explicit verification limits, without another review round.

The design's subsequent metadata marks implementation completion; its selected
edge rules and scope are unchanged from the recorded review snapshot. Earlier
hashes and producer-handoff status in §§6–7 remain historical evidence, not
claims that later metadata have identical bytes. Tests are regression evidence,
not premises of the theorem. Source-global applicability, typing preservation,
complete Call, hygiene, principality, inference termination and F5 remain OPEN.
