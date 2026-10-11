# Generalize source emission: retained source edges and missing frame consumers

Date: 2026-10-11
Status: frozen research-only constructive source trace and exact missing law;
independent review pending. No semantic counterexample or parent closure.
Baseline: `4361e3b59df6995a756639ad948a99681dd5c02e`.
Branch: `research/simple-sub-intrusion`.
Exclusive lease: this file. Normal Sol/high leaf, no further delegation.

## 1. Frozen question, quantifiers and method

Determine whether actual source construction and consumers establish P from
[the previous frozen note](2026-10-11-value-generalize-level-correspondence-proof.md#5-first-unprovided-source-law):
complete free dependent fields and original binder incidence for
Mono/Established, Executed/OneShot and Shared contracts, with their correct
preservation through incoming frames. Investigate the supplied discarded-peer
construction at its actual owning points, rather than assuming those fields
are numerical row dependencies.

The unchanged parent is the implementation correspondence to
[selected Generalize §§2–4](../design/2026-10-08-source-generalize-definition.md)
and [construction §§3–6, especially §§5.1–5.3](2026-10-08-source-generalize-definition-and-proof.md).
For every original finite resolved source/rule graph S, original binder tree T,
genuine local L1–L5 laws, actual source anchor and publication p in its validating
component C, the implementation must represent

```text
Generalize_source(S,b)
  = ScopedClosure(p,C,T,anchors_b,templates_b,N_b,R_b).
```

It must retain the complete simultaneous source relation and every original
constraint; fix exactly the typed dependent fields required by §§3.3/5.1; keep
eligible ordinary Desc coordinates at their original scopes; and preserve
shared, description-frame and actual-event binder incidences. Lawful-use scope
remains `forall finite independent joint d_U and well-scoped W; exists finite
allocation m_d before assignments/challenges/histories`, with the same joint
solution-and-observation fiber and original scoped strategies. The whole Call,
provider, world, attachment, protection and residual contracts are unchanged.
The original L1–L5 source laws are not compiler-emission assumptions.

Method: trace a resolved source constructor through HIR, collection, static
component registration, source action execution, publication, recapture and
the actual incoming mapping. Separate source information retained in the batch
from source clauses activated in an incoming frame. Inspect typed evidence
consumers for the remaining fixed/event fields. No source form, annotation
requirement, semantic alternative, proof-only reconstruction or code change is
introduced. No numeric rank proof is repeated.

## 2. The first source edge is not the final Value endpoint

The supplied [falsification note](../progress/2026-10-11-value-generalize-level-falsification.md)
constructs

```text
my f x = { my u = g; x }; my g y = f
```

Under the original source constructor inventory, f's body is a sequential
Bind: evaluate/rebind the actual Name g to u, then return x in that same source
context. Build §4 conjoins both premise programs and the local Bind clause.
Returning x does not remove the Name, its rebind or its original invocation
scope. This is not the operation of projecting a final Value row.

The first source reference demanding the peer relation is the resolved
recursive **Name g in u's initializer**, under f's body event. Construction
§3.3 assigns the recursive Name `Live(C,g)` / `Internal(C,g)`, pointing to the
complete simultaneous relation. The enclosing Bind retains that rule clause
and its original telescope. The other recursive Name f is in g's body.
These are source relations, not an equality between Function ports.

At publication, §5.1(1) already seeds retain with the **whole component C**
before traversing an endpoint. Rule 3 also requires the Internal edge above
to visit the whole relation. Thus there are two compatible requirements:
registration identifies the component-wide relation; the retained Name clause
links to it at its own scope. Neither depends on f returning g. §5.2 opens
one whole component frame for an incoming f description, including background
and peer conjuncts; §5.3's selected-root/member distinction does not authorize
separate member-only clause closures.

The source-to-compiler matching of complete MemberEntry/world validity still
requires its genuine L4 evidence. This trace does not prove that law for all
recursive programs. It identifies the exact source rule that a correspondence
must represent, with the original validating C unchanged; it does not define
semantic C by a row SCC or declare the source lawful from solver success.

## 3. Actual source construction retains the syntactic edge

The source metadata needed to locate this edge has not been globally discarded.
The following is a direct owner trace, subject to normal fallible construction
and resource limits; exact source-string acceptance was not executed.

1. `local_source.rs:288–320` introduces the top-level Lambda and original formal
   identity x. The Block builder at `:698–829` retains u as a
   `LocalSourceBinding`, its initializer node, and the distinct final expression.
   u has no formal parameters. Its initializer scope is
   `LocalInitializer(u)`, while its binding records the containing Block scope.
   The original tree still places the Block inside f's Lambda.
2. `local_source.rs:637–660` resolves g through the module namespace after
   lexical lookup, and similarly resolves f in g's body. `Work::Publish` installs
   u only after its initializer. These records do not depend on a printed
   Function endpoint. The final Name x resolves to the authentic formal.
3. `lib.rs:1124–1138` obtains f's actual LocalSource from the HIR and invokes
   `emit_candidate_source`. At `candidate_source.rs:367–388`, ModuleDef(g)
   produces `PendingDefinitionUse(parent=f,target=g,occurrence=Name_g)` and
   `Action::Module(Name_g)`. The opposite Name produces parent=g,target=f.
   The Bind's initializer is visited even though u is unused.
4. `lib.rs:1278–1339` validates each pending target against the definition map,
   freezes its authentic parent/target, occurrence/cause, use component and
   target-root component in DefinitionUse, and retains its use-position map.
   `scc.rs:276–306,416–437` builds the opposing definition arcs and stores both
   use identities in the same component's `internal_uses`. This is a concrete
   source dependency SCC, distinct from the intrusion row graph.
5. `ConstraintBatch` retains `hir: Arc<HirModule>`, the SCC plan, definition/use
   maps, original parameter identities, Lambda recipes and source schedules
   (`lib.rs:828–887`). `GraphState` stores the separate graphs for f and g.
   Their source trees, component membership and original lexical ownership can
   therefore still be located. Literal absence of y in one graph is not proof
   that the whole compiler has forgotten y.

This establishes authentic syntactic occurrence, component incidence and
lexical-tree retention. It does not elevate those records to a complete
Mono/Established or Executed/Shared semantic certificate. SourceNodeKey,
HirOccurrenceId, HirLocalId and HirParameterId locate constructors; their IDs
do not themselves supply contracts or witness dependency laws.

## 4. Actual emission and publication do not connect that relation to the frame

`candidate_source.rs:251–326` traverses all initializer and final-expression
nodes in order. For u, `Work::Install` emits its initializer Effect into the
Block computation and produces `Action::Install`. `step_candidate_source`
retains only `Stage::PublishLocal {slot,exposed,boundary}` before calling
`install_candidate_local_term`; that call stores `LocalScheme {id,root,boundary}`
(`candidate_source.rs:627–653`; `candidate_scheme.rs:1319–1336`). It creates no
source execution witness by evaluating user code: these are compiler inference
actions. One emitted Effect constraint is not the complete source Bind's
return/world/provider/rebind telescope.

The Block's Value recipe uses only its final x endpoint
(`candidate_source.rs:461–474`). The Lambda Value recipe uses that Block Value.
`shadow_apply.rs:1327–1330,1409–1423` confirms that Group/Block admission links
the final child Value and its Effect; it introduces no enclosing source-Bind
clause or peer-member Value seed.
The source initializer and its effect were genuinely visited; there is simply
no Value-return edge from this discarded initializer into the final Value.
That omission is correct as a scalar Value dataflow observation. It is not
permission to remove the initializer's complete source rule clause.

The component orchestrator supplies every active root and internal use before
running either source schedule, and finishes both schedules before capture.
It then stages **one graph per member**, calling
`capture_candidate_graph(root_of_member,0)` (`candidate_scheme.rs:842–918`).
The complete member list is available at this owning point. It is not installed
as a shared component-relation seed in those graphs. After publication, active
root/use sets are cleared; the retained SCC/HIR metadata remains in the batch.

For the discarded-peer family, the supplied scalar reachability finding can
be checked directly against these owners. Let N_g denote g's discarded Name
and N_f denote f's Name in g's body. f's positive Function uses x and its final
Block Value; g's positive Function uses y and N_f. The native row storage puts
the live g→N_g bound on N_g. Other generated Value constraints contain no
negative Function demand or inverse child-to-enclosing-Function rule. Positive
lower-bound replay forwards f's Function to N_f and g's Function to N_g; it
does not add g's enclosing Function to a Value child of f. Capture beginning
at R_f therefore does not seed R_g,N_g,g's Function or y. This uses the supplied
source mutation's actual emission orientation, not another general level proof.
The f-root graph lacks the peer seed even though its source component contains g.

Capture's extra dependency traversal reaches captured bound relations, their
context payload Effect tails, attachment bundles and physical evidence
snapshots (`candidate_scheme.rs:722–804`). No one of these owners enqueues the
static SCC's other Value member roots. Value/effect separation is respected;
an Effect tail is not a proxy for g's Value description or its source binders.

## 5. The incoming consumer supplies no deferred component reconstruction

`route_candidate_graph` reads the selected target's stored live root/boundary,
recaptures that root and calls `instantiate_candidate_graph`
(`candidate_scheme.rs:947–962`). It does not inspect peer graph slots, SCC
member lists, internal-use clauses or HIR source trees. Fresh preparation maps
only the captured `graph.rows`; it reconstructs captured structural nodes and
contexts and imports the captured evidence. Freshening restores only
`graph.bounds`, then routes the remapped selected root to its occurrence
(`:967–1021,1118–1175,1222–1314`). The ordinary route records the same use/fact
and invokes native propagation; it does not add a component source frame
(`lib.rs:16842–16907`).

Appending `my first=f; my second=f` supplies two authentic incoming occurrence
routes through these consumers. Neither route allocates a y coordinate or
peer-source clause in its graph mapping. There is no later source traversal
in these consumers translating the omitted peer into an `(incoming i, source q)`
description/event frame. The only `scc_component_members` read in
`candidate_scheme.rs` is component scheduling; the graph use path reads only
the selected graph. The source Call observer in `candidate_call.rs:282–322`
can consult retained HIR for a different purpose; it does not serve as a
Generalize frame allocator.

The native entry branch is decisive: `route_incoming_inner` immediately returns
through `route_candidate_graph` when the candidate graph exists
(`lib.rs:16681–16689`). It cannot subsequently use the legacy closed-scheme
branch as a whole-component supplier. The wrapper owns transaction/accounting,
not source clause allocation. The global intrusion scan can canonicalize real
parent/copy rows; it does not allocate a peer's source clause/event frame from
the retained definition SCC.

The three layers and their relationship are therefore:

| Layer | Established owner fact | Missing connection |
| --- | --- | --- |
| 1. Original source Generalize | §5.1 seeds whole C at f publication; §5.2 opens whole C at every independent incoming frame | No source rule authorizes replacing that seed with final-Value reachability |
| 2. Retained source evidence | `batch.hir` retains Name g under Bind/f's Lambda; DefinitionUse(f,g), its occurrence/cause and the opposing use remain in the retained SCC plan | These data are available but do not themselves allocate their semantic clause/binder incidences |
| 3. Actual graph/fresh consumer | f publication and recapture start only at R_f; its graph lacks g/y; preparation maps captured rows only | No operative transition from the layer-2 internal source edge to the missing layer-3 component/frame seed occurs |

The absence of that layer-2-to-layer-3 operation is established by the actual
native publication and incoming branches above. No extant owner on those paths
supplies the same whole source relation in an additional incoming frame. The
peer graph, HIR and source schedules are retained independently; the inspected
incoming consumer neither reads them for this purpose nor activates their
clauses at the incoming description's binder incidences.

Consequently, the proposed graph-only law “capturing a member root and mapping
its rows emits the whole source component frame” fails on this static
constructor trace. This is a **representation/consumer coverage finding**,
not a refutation of source GS/GC or of every possible interpretation of the
complete retained compiler state. An effective, scope-preserving alternative
representation is not logically impossible merely because these consumers
do not currently construct it.

This omission refutes the concrete **construction-preserving correspondence
claim for these owners**: their graph/frame construction is not the whole-C
ScopedClosure construction required at this seam. It alone does not refute
semantic observational adequacy of every interpretation of the complete
compiler state. A different extant operative supplier or a valid source-scoped
elimination/representation theorem would need to be exhibited; none is supplied
by the inspected native consumers. The original full implementation theorem
therefore remains OPEN, and this finding is not a lawful-use semantic
counterexample or a theorem that no implementation can satisfy the contract.

No independently legal distinguishing client/proof grammar and its changed
fiber has been derived. In particular, y is unused by g's return and f returns
x. Choosing an arbitrary predicate on an unmapped hidden y without proving
its lawful source/client incidence does not supply a semantic counterexample.
Nor can its apparent unobservability justify elimination: §5.1 retains the
whole relation and §5.2 retains original binders and all conjuncts. No lawful
elimination or existing source-scoped reconstruction certificate was found.

## 6. Fixed dependencies and event binders remain a distinct missing law

The precise first missing consumer law at this concrete publication is:

> From the retained source component and its authentic Internal incidences,
> publication and incoming allocation construct one complete component source
> frame, with all member/source clauses, original Desc scope incidences, and
> nested Bind/event records. The selected final root chooses a member without
> dropping the other source clauses. Original fixed fields/binders stay shared,
> and event-local fields remain under their original actual source event.

Its source origin is construction §§3.3/4; its publication/allocation duties
are §§5.1(1,3) and §5.2. Its actual compiler owner is
`execute_candidate_graph_plan` → capture → `instantiate_candidate_graph` /
`prepare_candidate_fresh_use`, using the already retained batch's source/SCC
owners. It is a concrete portion of P's construction/consumer bridge, not an
added semantic restriction or an assumed opaque adequacy theorem.

Before this can yield the full original P, source Mono/Established and
Executed/OneShot/Shared fields must also have independently grounded complete
contract/telescope records. The current local Install state exposes a root and
boundary, not their complete free semantic dependencies. Physical bound
`EvidenceSnapshot` carries source_bound/relation/admission/emission incidence
and coverage gaps; fresh import preserves that snapshot. Its consumers do not
interpret it as the same source world/provider/evidence tuple or original
Shared/Event binder strategy (`candidate_context.rs:337–381,508–545,1535–1540`).
`candidate_call.rs:86–149` explicitly retains the missing whole-interface,
formal-introduction, original Gen-Call-0, carrier and complete result/future
suppliers. Scalar NativeInterface ports are not those supplied source laws.

The local u formation is nested under f's invocation. Its future RHS evaluation
and rebind cannot be relocated to f's outer initialization or treated as a
top-level OneShot choice once across every call. Conversely an actual external
Mono/Shared dependency may not be copied once per incoming description. HIR
retains the syntactic nesting needed to locate these responsibilities, but the
examined graph consumers produce no original actual-event keys or complete
dependent witness allocation proving this distinction. Exact classification
of u's retained contract and y's fix/eligible status is therefore left open;
retention of the whole component is required in either case.

## 7. Result, economy audit and next owner

Result class: constructive syntactic source-to-registration trace plus bounded
representation/consumer coverage finding. P is neither established for its
original scope nor semantically refuted. The full Generalize parent remains
OPEN with unchanged quantifiers and local source laws.

This assignment advances from the previous abstract gap to its owning source
edge and consumer seam: the recursive Name/Bind edge is actually retained in
HIR and the static component plan, while publication and fresh-use consumers
do not open its complete source relation. A further conditional numerical
lemma would leave that seam untouched. Under the proof-obligation-economy rule,
the fixed/event preservation obligation remains A/B. Rebuilding the component
or original binder incidence from solved Value shapes would create D debt;
the construction already retains the source/SCC information. This audit changes
no gate status or semantic contract and chooses no production representation.

Next owner: the primary's source/component-frame correspondence lane at
`candidate_scheme` publication/allocation, using the existing HIR, SCC and
source Bind owners. Establish the quoted frame law, or return a lawful
distinguishing client/refutation, before another equivalent proof attempt.
Full Mono/Executed/Shared dependent-field suppliers remain explicit subsequent
premises; this single edge's coverage cannot close them.

## 8. Checks, dependency snapshot and resources

Only bounded source/section reads, symbol/caller searches, read-only Git
HEAD/branch/status/diff inspection, SHA-256 capture and lease-only Markdown
construction were performed. The note is not an executable probe. Zero
build/test/Oracle/checker/benchmark processes, zero samples, zero child launches
and zero Git mutations. One lightweight shell command at a time; verification
owner remains the primary. Assigned wall bound: 45 minutes; exact cumulative
wall, CPU time and peak RAM were not measured. Requested model/effort:
`gpt-6.1-sol` / `high`; observed runtime metadata unknown. No Astra routing.

All named dependencies matched baseline before derivation. Production and
governing source bytes also matched the preceding assignment. The final named
dependency diff remained empty at live HEAD
`eb9308dac6f8790519ea3e9d46a686a2e53c2876`. SHA-256 snapshot:

```text
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8  crates/yu-solver/src/scc.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
4b63cc39c0d1dab2809e7f7948bf323857fd7461618a5350687897280f6c3325  notes/theory/2026-10-11-value-generalize-level-correspondence-proof.md
e0e5518a04d55850979e71170fa3b776499495a40314f88c519bede374390b7a  notes/progress/2026-10-11-value-generalize-level-falsification.md
```

Unverified: exact parsing/execution of the mutation; resource-abort and abnormal
reuse paths; complete MemberEntry/world and other L1–L5 law instances; legal
client distinguishability; full binder/contract field transport; complete Call,
effect/attachment hygiene, source soundness/principality and production cutover.
No owning source law is inferred from a stored constraint or producer note.

## Commit packet

- Exact leased path:
  `notes/theory/2026-10-11-value-generalize-source-emission-law-proof.md`.
- Baseline: `4361e3b59df6995a756639ad948a99681dd5c02e`.
- Changed dependency hashes: none at freeze; primary rechecks before integration.
- Review: unreviewed research-only producer artifact; parent OPEN.
- Checks: static source/SCC/Bind/publication/incoming consumer trace, exact
  dependency comparison and hashes, lease-only whitespace/fence validation.
  No executable source or test verification.
- Proposed message:
  `research: locate missing Generalize component-frame consumer law`.
- Shared-record deltas left to primary/curator: attach the exact Name/Bind →
  component → incoming-frame gap to P; record existing HIR/SCC retention separately
  from absent consumer construction; keep original Generalize/Call/fixed-field/
  soundness/principality gates OPEN and require independent review. No shared
  records were edited.
