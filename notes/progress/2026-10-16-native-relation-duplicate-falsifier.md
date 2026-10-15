# Native relation duplicate suppression: ordinary diagnostic-child reuse seam

Date: 2026-10-16
Status: historical static falsification/source audit with accepted causal
adjudication and verified local repair. Concrete pre-repair production
branch and missing relation-fiber route identified; no missing-required-
consequence counterexample or duplicate-preservation theorem established.
Baseline supplied by primary: `87ac89419`; native owners unchanged.
Lease: this new note only; 25-minute static leaf. No Git, compiler edits,
tests, builds, executable probes, children or shared-record writes.

Primary adjudication at producer
`6e34becbc760257edb28fd0f099737bc3c7e20520109d8df74b9376455b4607d`:
independent `checked_result_semantics` confirms an uncertified semantic-rewrite
shortcut under contextual attachment §4, sufficient for the bounded causal
repair. This audit's authentic missing-bound-fiber trace is not an observable
counterexample; some Derived provenance and scalar compensation remain.
The primary accepts the responsibility finding without promoting the whole
duplicate-preservation parent. [Repair gate](2026-10-16-native-value-rewrite-provenance.md).

Later receipt: the unchanged authentic source regression fails at the original
bound association on baseline `8d2699197` and passes after repair. The separate
[actual native invariant](../theory/2026-10-16-native-retained-value-rewrite-invariant.md)
now has independent semantic acceptance for operational obligation retention.
That post-repair theorem closes only the local native subgate; this audit
still establishes no observable source-semantic counterexample.

## 1. Original obligation and method

Attack whether `pair_is_current` suppression preserves every required native
consequence of the actual contextual relation, including retained extrusion
rewrites, ordered replay, Function-port context, residual discharge and evidence.
After a stamp, later mutation must change its identity, invalidate its
generation, or incrementally own its new consequences. An early processing
stamp is not a drain-completion certificate.

Authority: inference top-level principles §§1,1.1,3–5 and contextual attachment
§4. The reviewed initialization-replay and capture-completion results supply
their stated admission/drain boundaries. They do not establish semantic
redundancy of every suppressed duplicate. Their already excluded queue-before-
publication attack is not repeated. The independent producer's live duplicate
proof was not read. The primary supplied one concrete candidate to inspect;
that shared lead is not independent review or independent discovery.

## 2. Memo identity and mutations actually covered

At `lib.rs:11585–11597`, candidate-mode currentness requires an existing raw
typed diagnostic pair and the actual processing RelationId stamped at the
current **intrusion** generation. RelationKey is
`(pair,context,sources,scoped)` (`candidate_context.rs:223–230,2569–2600`).
Contexts, source sets and scoped flows are interned, rather than mutated in
place. Transport/Context precede Dispatch (`lib.rs:12390–12406`); context
checks are not bypassed by the later pair memo test.

`mark_candidate_pair` stamps only a canonical raw key at its actual processing
relation (`candidate_intrusion.rs:352–384`). A raw alias cannot stamp the queued
canonical task complete. Nontrivial row merging transfers both sides/origins,
canonicalizes bounds, increments intrusion generation and replays
(`:518–612`). The retained child must be compared with the existing transformed
copy graph; blindly rerunning extrusion would allocate another graph and is
not a valid reference operation.

Dependency-only mutation does not generally increment intrusion generation.
`dependency()` increments the separate source-support `lifecycle_generation`
only for FunctionPort additions and invalidates their watched certificates
(`candidate_context.rs:2660–2715`). That is a different certificate from the
relation processing stamp. The following positive incremental owners were
found:

| Mutation | Existing owner / bounded exclusion |
| --- | --- |
| New Derived/FunctionPort/Replay dependency | `dependency` installs actual diagnostic edges before publishing the dependency. It retains both ordered Replay parents and BoundKeys. Dispatch does not choose its four Function fields by reading the dependency list. |
| Bundle attached after an edge already exists | `bundle_link:2365–2389` traverses existing diagnostic successors and eligible sparse transport chains. |
| Edge attached after a bundle already exists | `edge:2718–2750` calls `bundle_edge`, which propagates already linked parent bundles. Eligible transport publication also updates this route when active. |
| Late opposite bound/fiber | `candidate_apply_value/effect` inserts then invokes ordinary replay; `candidate_context_begin_replay:3391–3456` accounts for new/new and old/new attached-fiber quadrants and retains exact ordered recipes. |
| Discharged context | Context execution precedes memo checking; discharge publishes only after checking/registering executable Allowance bounds. Later lowers meet those retained bounds through ordinary replay. A fixed context's checked weight is not widened by appending a dependency. |
| Function stamp before children | FunctionDispatch retains its next/pending child, and the existing drain proof owns descendants before source return. This does not settle the distinct rewrite branch below. |
| SCC qualification/levels | Value-reference graph is sealed before session source-level initialization (`lib.rs:10174`); no late production reference-graph mutation was found. Nontrivial intrusion representative/level changes increment intrusion generation. |

This is not exhaustive negative coverage of every mutable field or rollback/
restoration path. In particular, it does not assume evidence snapshots become
live views of later admissions, or that late incoming capture incidence is
handled by constructing a second extrusion graph.

## 3. Concrete ordinary-row branch reached by authentic source constructors

Use the primary's candidate source, retaining its source identities:

```text
my apply (f: 'a -> int) (x: int) = { my first = f x; f x }
```

This is a static constructor trace, not an executed fixture or an accepted
source-failure report. The ordinary source constraints have a compatible
typing (for example alpha=int and a pure supplied callable); no altered
semantic rule is needed to form the source.

Let p be x's parameter row and a the annotation's original scoped `'a` row.
The relevant authentic source owners establish the following route:

1. `candidate_source.rs:618–625` maps every Parameter Name directly to its
   shared `CandidateEndpoint::Parameter`. The two x uses have the same p;
   they are not two local FreshUse roots. Formal parameter levels are
   installed from their source level (`:1210–1212`), and the annotation a
   is allocated at that formal level. Here both are level1.
2. `candidate_formal_annotation:1191–1231` installs x's paired Int contract
   before body actions. Thus Int+ is a stored positive lower of p, and p
   also has Int- as an upper. f's paired Function has argument a.
3. Each Apply owns a distinct source checking event
   (`candidate_value_graph.rs:170–179`). Annotation lower Function plus that
   Apply's demand yields an Argument child with raw pair `p <= a`.
   Its inherited source set contains that Call's distinct event. The source
   registration and Function-port constructors therefore distinguish r1
   and r2 even when their endpoint pair/context is identical.
4. The first r1 has no prior raw-pair memo. `candidate_apply_value(p<=a)`
   (`candidate_extrusion.rs:844–873`) chooses p's negative bound a at equal
   levels, inserts that bound/fiber, and replays its existing Int lower.
5. `candidate_replay_bound:799–840` calls
   `record_diagnostic_edge(parent=p<=a, child=Int<=a, field=None)`.
   This is **ordinary row propagation**, not an extrusion rewrite. Its child
   is nevertheless stored in the raw pair's `TypedPairMemo::Value.children`.
   `record_diagnostic_edge:13115 onward` is a shared diagnostic writer.
6. The first source action drains before the later source action. No
   qualifying source SCC or representative merge is needed for this trace.
   On r2, pair_is_current is false because r2 has not been stamped, although
   the shared raw pair memo already has that child.

The decisive branch is `lib.rs:12494–12509`. For a non-Function/Function raw
pair it treats **any** nonempty Value diagnostic children as retained
structural extrusion children. It stamps the new relation, iterates the old
children, invokes recapture/value_rewrite and queues them, then returns.
There is no check that a child originated in extrusion or even that the
original pair had a structural endpoint.

For this row/row pair, recapture finds no actual extrusion group for this
ordinary Int child. `candidate_context_value_rewrite` does accept the parent
pair and creates `Int<=a` at r2's source/context, with a Derived edge.
The branch does **not** call candidate_apply_value on `p<=a` and does not
attach r2 to `BoundKey(p,Negative,a)`. Identity context execution before it
also performs no such attachment. The first bound's r1 fiber remains.

Consequently an argument that every newly stamped relation first installs
its own original row bound/fiber cannot cover this branch. Later exact r2
duplicates may use its stamp, whose initial processing was this diagnostic-
child rewrite. That observation identifies the missing proof case; it does
not yet establish a lost semantic consequence on an actual later duplicate.

## 4. Why this is not a certified compiler counterexample

The annotation gives both `Int<=p` and `p<=Int`. Thus the rewritten
`Int<=a` plus the retained `p<=Int` may already imply the required **value
inclusion** `p<=a`. A later incompatible lower of p conflicts with x's fixed
Int upper independently. This audit does not discard that compensation or
use an ill-typed later lower as an accepted-program counterexample.

Nor does an absent second physical fiber by itself establish an observable
diagnostic, source-qualification, context or evidence failure. The new
relation retains a Derived edge to its child; existing dependencies/bundle
propagation may supply the necessary consequence by a different route.
Top-level principles do not require exact diagnostic identity.

To complete a falsifier requires an authentic production/source sequence
where this branch's reused ordinary children fail to represent a genuinely
required later consequence of the original relation. A decisive instance
could use a shared row with earlier positive lowers but no compensating upper,
or demonstrate a particular required context/evidence disposition absent
from both the original live graph and the rewritten child route. No such
complete source-qualified late sequence was derived in this packet.

The first uncovered owner is therefore **the semantic/evidence sufficiency
of reusing ordinary replay diagnostic children as a new relation's extrusion
rewrite**, at `dispatch_live_item:12494–12509`. Its actual child writer is
`candidate_replay_bound:817`, not only the structural-rewrite writer at
`lib.rs:12586`. This is more precise than another generic dependency-only
mutation concern. Replaying old children does not automatically justify
omitting the new original bound/fiber, and allocating a fresh copy graph is
not the correct comparison for genuine extrusion children.

No implementation fix is selected here. One next action: have the constructive
duplicate-preservation argument handle this exact ordinary-child writer and
new-source-relation branch, including late-bound/context/evidence compensation,
or source-qualify the missing compensating route. Do not return to the already
settled owned-drain early-publication attack.

## 5. Checks, resource use and frozen inputs

Static source reads/searches and hashes only; no candidate/reference program,
oracle, test/build/probe, mutation, random seed or numerical enumeration ran.
The source trace is derived from inspected production constructors; its full
late-counterexample extension remains incomplete. CPU/RAM unmeasured;
sequential short shell processes, no heavyweight process, within 25 minutes.
The producer supplies no independent review. Original duplicate-preservation,
H2/U, contextual semantics, soundness/principality and production/F5 gates
remain OPEN; no dependency on opaque L1 or source ResultBind is introduced.

Direct dependency SHA-256 snapshot, unchanged on final recheck:

```text
199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070  crates/yu-solver/src/lib.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6  crates/yu-solver/src/candidate_context.rs
2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c  crates/yu-solver/src/candidate_intrusion.rs
44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9  crates/yu-solver/src/candidate_effect.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38  crates/yu-solver/src/candidate_source.rs
d08f6c5fb9ae4c5f005b6cb40aa3462f4f58b350cd6842b76a15d2dfdb520bec  crates/yu-solver/src/candidate_value_graph.rs
cb1ffafb226d1b8443c6d6f3206b5205fc2ec760137e58e16b964f659d67797c  notes/theory/2026-10-15-extrusion-initialization-replay-invariant.md
f286eb3d0280b614caf2a870aa36204ff766241033c9dc49b75f01cde9d87fd7  notes/theory/2026-10-16-extrusion-replay-capture-completion.md
622873c766f9f3a5ae8bf7bc6bd7469216715d79f85b760a9335285fd818cac9  notes/progress/2026-10-16-extrusion-replay-publication-falsifier.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

Commit packet: exact sole leased path
`notes/progress/2026-10-16-native-relation-duplicate-falsifier.md`;
baseline `87ac89419`, native owners as above; no dependency edits/digest
changes. Frozen unreviewed production-branch characterization, not a certified
semantic counterexample. Checks: static production/source trace, 12 dependency
rechecks, whitespace/fences/local artifact links; no executable verification.
Proposed checkpoint: `research: isolate ordinary-child reuse in relation duplicate dispatch`.
Shared-record delta left to primary/curator: retain original OPEN parent and
add the concrete diagnostic-child writer/dispatch sufficiency obligation;
do not record source rejection or a proved compiler defect.
