# R170 source/Capture incidence: the ignored-input fixture and exact remaining join

Date: 2026-10-21 repository session. Status: **UNREVIEWED SOURCE/NATIVE EVIDENCE; incidence OPEN**.
Author: `/root/r170_provider_proof`; no coauthors or descendants.
Assignment: `R170-SOURCE-CAPTURE-INCIDENCE`, result revision 1.
Contract revision 6: `tasks/agent-loop/sprints/provider-capture-incidence-20261021-r170.md`,
SHA-256 `f099fe9e5d10420413a20ffae5916a7961767e5ed76f592240c19d89e643f74b`.
Activation baseline supplied by Luna: `5837ec19220cc6f0c7e0d8f106dee59e3bbad9a`.
The contract's historical R169 baseline is not asserted as the activation HEAD.

## 1. Parent application and result

Parent: computation-forwarding preservation §§1,6–7. Preserve its one shared satisfying
assignment `xi=(nu,K,D)`, original resolved declarations, formal/provider/witness identities,
arbitrary finite forwarding chains, repeated calls, simultaneous receiving entries and every
typed finite interaction prefix. Incoming E remains open; the finite local permission set does
not cap E. Independent Simple-sub/evaluator A/B, F1/FK1 and foreign-continuation obligations remain
unchanged. No native/runtime, soundness, principality or production gate closes here.

The pinned fixture is a member of §1's **ignored Computation input / ground-return case**, under
that section's explicit base typing contracts. It is outside §6's **direct formal-Name body
subcase**. Its original source suppliers are the `ignore` Lambda's slot 2 positive Function and
slot 4 ground-body effect bound. There is no source Name of `ignore`'s parameter, hence no
same-construction Name slots 1/2 or e_n for that Lambda. This is a source-constructor exclusion,
not evidence that the solver lost a required Name witness.

Applied to the parent immediately: the later single candidate-solver observation may provide
one ordinary provider/Capture/AE-RE case for this fixture. It cannot establish §6's premise
`mu(e_t)<=mu(e_n)<=mu(e_R)` and `mu(e_n)<=mu(e_t)` for a direct-Name provider, even if all its
printed Capture/map rows match. The source local theorem already permits an unused delayed
input to remain inert. Requiring this fixture's incoming argument effect to reach RE would add
a conclusion that the parent does not require. The original direct-Name and forwarding native
admission premise stays OPEN.

**Actual incidence outcome:** no full authentic source FactId/Terms → same provider Capture/map
→ same consumer q tuple is established. The precise remaining association is
`R169-SOURCE-FACT-CAPTURE-INCIDENCE-1` in §4, with source owners and a falsifier. This packet
supplies neither a source-qualified mismatch nor another theorem assuming that association.
Luna's later borrowed observation/probe is an unconsumed TODO input here, not claimed evidence.

## 2. Fixture membership and actual source suppliers

Read-only fixture `tools/inference-playground/examples/entry-computation-argument.yu`, SHA-256
`a81a52d582067e9d76ca41bfb946cd539cd98cc369b9b2c2a01fb0b3e0e239fd`:

```text
act signal:
    our ping: () -> int
my ignore (x:[] int) = 9
my main = ignore (signal::ping())
```

`ignore` has one explicitly annotated formal with finite resolved concrete permission set
S=empty and outer Computation(E,Int) role. `9` is an ordinary ground return; `signal::ping()`
is an operation declared with monomorphic Unit input and Int response; the outer expression
is an ordinary call. There are zero forwarding edges and no handlers or raw resumptions in
this fixture. Zero edges and an ignored formal are allowed by the parent. The argument does
not have to be a formal Name at this initial ordinary call: §1 imposes that condition on
forwarding edges. These are source-fragment and base-typing checks, not a claim that a candidate
solve, evaluator execution, or full source-admission theorem has occurred. Future operation
responses retain the parent's declared-type hypothesis. The fixture does not exhaust §1.

Constructor specialization, at the frozen baseline:

1. `candidate_source.rs:869–884` registers the explicit effect annotation as Computation with
   its original source owner, Lambda position and parameter identity.
   `initialize_candidate_source_levels:1585–1620` allocates its actual e_t at the formal's level.
2. The literal branch `candidate_source:1168–1190` emits its own exact Value component V_9 with
   `Int+<=V_9<=Int-` and effect component e_9 with `bottom<=e_9<=empty`, at that literal's slots
   0/1 and 2/3 respectively. V_9 is not replaced by an Int leaf.
3. `candidate_source:1482–1498` records the actual Lambda recipe/body components and original
   registration. `lib::admit_lambda_fact:11322–11495` selects registered e_t as AE, allocates e_R,
   omits Value-entry slot 3 for Computation, admits Lambda slot 4 `e_9<=e_R`, and admits Lambda
   slot 2 `P+<=Lambda_root`. P+ is the actual positive Function with the owner's actual formal
   domain Term, e_t, e_R and V_9, in their prescribed polarities. No `e_t<=e_R` edge is inferred.
4. `candidate_source:1294–1305,1736–1740` generates `FormalNameEffect` only for a resolved
   parameter Name and its same registration. The body `9` has no such constructor. `ignore`
   in `main` is a declaration Name, and `signal::ping` is an operation; neither is Name(x).
   Thus the direct-Name equality supplier is inapplicable by the actual source syntax/action
   branches, rather than absent because of an optional `FormalConstruction`/`ScopedDemand`.

R169's supplier applies to each actual successful admission above:
`ConstraintStore::admit_and_record_provenance:3671–3718` consumes this occurrence's receipt,
retains CauseId/ProvenanceEdge/FactId and exact Term pair, and the direct typed drain uses this
same occurrence/task. `FactKey::eq:3933–3936` compares both Term handles; duplicate facts may
share FactId while retaining their own successful source-cause edges. Numeric FactIds, Term
handles and a concrete source-drain RelationId are **not observed in this packet**. Symbolic
names P+, V_9, e_t/e_9/e_R above identify constructor outputs, not fabricated native IDs.
The displayed inequalities abbreviate constructor endpoints. The literal's retained source
Component Terms and their live-variable translations remain distinct handles, related by the
owning live-component translation; no Term equality between those forms is assumed.

## 3. Capture, provider maps and consumer slice on frozen source

The following successful-constructor facts identify how an authentic tuple would be checked;
they do not assert that a selected fixture tuple has been observed.

`candidate_scheme::Capture::bound:1008–1053` computes the supplied owner's actual raw
`source_bound=(owner,side,stored_item)` and obtains its exact bound cursor **before** structural
endpoint interning. It enumerates each attached relation, retaining a Bound with that raw key
and an EvidenceSnapshot. Structural interning uses canonical endpoints; bound deduplication
uses kind/side/structural-node indices/optional relation. This does not establish a converse
from a canonical structural match to a particular raw witness. An empty cursor's None Bound
is not an authenticated source fiber. `expand_row:1055–1161` skips nonlocal/shared anchors;
their actual unchanged-session path needs its own proof rather than a fictitious capture row.

`prepare_candidate_fresh_use:1557–1861` creates one context_use and its own canonical row map,
terms, effect operands, context/scoped/bundle remaps and imported snapshot map. Actual generic
local rows can freshen; nongeneric/older coordinates can remain shared. All four Function
children use those same maps. `begin_candidate_fresh_bound:1863–1910` consumes that Bound through
this use's maps and imported evidence, retaining exact FreshUse transport/source key/use_origin
and its mapped relation when present. Module restoration finishes graph bounds before returning
the root (`1536–1556`); `instantiate_candidate_graph:1911–1966` retains that graph and its maps
as its own FreshRoute. The Local route has its own occurrence/use/maps; it is not a sibling-map
substitute for this module provider. These facts apply R165 only **after** identifying a required
source witness with the captured fiber or an independently justified shared-anchor route.

For an actual consumer q, `lib::dispatch_live_item:12648–12720` obtains the exact positive P and
negative D children and forms AE=`D.AE<=P.AE`, RE=`P.RE<=D.RE`. The typed drain installs Transport,
Context and Dispatch for its actual saved item. `candidate_function_port_admit:3415–3480`
retains the exact q/field/child, swaps AE, preserves RE, uses q's post-check residual and prefixes
the child-local wrapper in source order. It preserves q's source set; any actual scoped demand
is authenticated/transformed/cleared by this owner. Ordinary admission needs no optional demand.

Backward traversal must keep every justified retained route. For each Replay retain
`(child,lower,upper,lower_input,upper_input)` with lower/provider and upper/demand orientation.
`candidate_context_begin_replay:3807–3895` uses the exact key-indexed fiber lists, two ordered
old/new quadrants and cutoffs, immutable parent contexts, source union and scoped composition.
For Transport retain parent, child, use_origin, full from/to keys and reason; retain each Derived
parent as well. Relation interning includes pair/context/sources/scoped; exact dependency
deduplication does not justify picking one producer merely from q or an endpoint match.
Repeated constructor invocations can share a structural dependency; no unique ReplayOperation
or historical event is inferred from it.

Residual correspondence remains separate: FreshUse's relation_context and FunctionPort use
post-check contexts; Replay constructs from its immutable selected-parent contexts and can
check new opposite products. Neither inspection establishes their semantic equality or a bug.
No local frame action discharges F1/FK1 or foreign-continuation quantifiers.

## 4. Exact obstruction, owners and discriminating evidence

**R169-SOURCE-FACT-CAPTURE-INCIDENCE-1 remains OPEN.** Starting at an actual ordinary q/AE or q/RE
FunctionPort, identify every justified provider alternative and its positive admission; connect
it to the authentic original Lambda slot-2 CauseId/FactId/exact Terms; identify each required
same-construction body witness and, when actually present in the source case, formal-Name
witness. Show that witness's actual surviving lineage is captured at the provider's exact raw
key/snapshot by **its own** graph/context_use/maps, remains at an unchanged shared anchor with a
justified consumer path, or follows another proved factorization to **this same q**, preserving
ordered dependencies, current residual and scoped payload. No frozen input to this packet
supplies that full association for the selected fixture.

The source-fact supplier exists. The missing item is its demonstrated incidence with the
actual compared provider/use and consumer, not a new existential premise silently assumed
true. `BoundAdmissionCause::OwnerEmission` retains processing information, not a source FactId
certificate. `BoundEvidence::admit:730–780` explicitly records missing ordinary-seed/processing
antecedents. An Origin is not a unique original constructor certificate: direct source and
Replay-child drains can seed using the enclosing occurrence, and interning can retain multiple
routes. These limits do not prove that a richer source-constructor induction or actual retained
inventory could never recover the join. Missing observation is not a source counterexample.

Owning symbols:

- Source: `lib::{admit_lambda_fact,ConstraintStore::admit_and_record_provenance,start_typed_drain}`;
  `candidate_source::{initialize_candidate_source_levels,FormalNameEffect}` and the literal/Lambda
  action constructors; `candidate_effect::candidate_formal_effect_equal` where a Name exists.
- Capture/map: `candidate_scheme::{Capture::bound,Capture::expand_row,prepare_candidate_fresh_use,
  begin_candidate_fresh_bound,instantiate_candidate_graph}` and the provider's own retained route.
- Propagation/consumer: `candidate_context::{candidate_context_bound_for,candidate_context_begin_replay,
  candidate_function_port_admit}`; actual extrusion and qualifying intrusion/recapture owners.

Mutual TODO, same stable ID, to Luna: consume the separately frozen R170 observation if available.
For this fixture require its real Lambda slot 2/4 source facts, q/port pair, positive BoundAdmission
and physical readback, exact captured raw Bound/EvidenceSnapshot, provider-owned use/maps and all
retained transport/ordered Replay alternatives with current residual/scoped payload. Label any
unjoined or truncated record explicitly. For the parent §6 direct-Name case, this fixture is not
the required input; a suitable original-domain source input and any new observation/code lease
need Luna's authorization before writing or running anything. This leaf grants neither.

Minimal provisional code-evidence TODO, only if those frozen records cannot discriminate the join:
borrow the existing source cause/fact/Term records and their provider-side association at the named
owners, alongside the existing own-route Capture/maps; report absent association without creating
persistent semantic state or an endpoint/count-based certificate. Luna must approve any work
outside the frozen R170 implementation boundary. This is a requested evidence packet, not an edit.

Exact falsifier for an asserted incidence: an accepted original history, authentic same provider
and use, required original source witness/cause/Terms, and actual q whose raw captured fibers,
unchanged-anchor path and every other justified retained route fail to deliver that witness's
required lineage/residual/scoped payload. An observer association is falsified if its reported
source cause/fact/Terms, raw snapshot, own context_use/map or q attribution disagrees with its
owning retained constructor. A missing formal-Name witness in this ignored-body fixture, optional
handle absence, fiber count, endpoint equality, sibling map or hand-built state is insufficient.

## 5. Reuse, frozen inputs, checks and cessation

Reused within actual premises: original reviewed source local preservation and separate native
template/conditional implication; R169 source-fact supplier; R165 identified-captured-fiber
restoration; R70 successful operation only under ENTRY-WF; R71 forward raw-to-canonical transport
only. R166's ordinary-consumer/selector-domain audit explains why an omitted-formal selector is
inapplicable. Historical authors: R169 `/root/r169_provider_proof`; R165/R166
`/root/r165_native_admission_proof`; R70 `/root/r70_ordinary_extrusion_proof` with complementary
`/root/r70_extrusion_countertrace`; R71 `/root/r71_raw_canonical_proof`. Their producer records do
not independently certify this artifact. Original-parent author identity beyond its recorded
historical role is UNKNOWN. R169 observation author is Luna primary; this leaf is a complementary
source/proof producer and cannot independently certify the combined result.

Rejected: original/copy endpoint identification, a demand-owned sibling map, unique-origin/event
inference, raw/canonical converse, count-based witness recovery, forcing an ignored Computation
formal, or treating a probe of retained records as source-constructor induction. Simple-sub
generation, accumulation, propagation, levels, extrusion, Value-SCC-qualified intrusion and
generalization retain their existing operations. No withdrawn bypass is restored.

The contract dependency pins matched; the additional authority hashes below identify the read
documents. The observer-owner sources were read into immutable tool-memory snapshots between
two matching checks of their baseline pins.
Later Luna edits were detected by a locator search only; no moving diff or new implementation
semantics are used. Luna explicitly confirmed continued static work and treating later observation
as TODO input. No filesystem snapshot/scratch path was created.

```text
contract            f099fe9e5d10420413a20ffae5916a7961767e5ed76f592240c19d89e643f74b
parent              d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79
fixture             a81a52d582067e9d76ca41bfb946cd539cd98cc369b9b2c2a01fb0b3e0e239fd
R169 source result  80e637bb64af9cb6247ff4ccb8d1241ef1d721e2d99fa17c52a121bb21e6bb68
R169 observation    77b909829c7b5188e673aa11eabb7413a87a1a041a2e14ec3a39146c6982fdac
R70 result          648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7
R71 result          620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e
R165 result         ac8f211679cb8c44d7834069d821e0a774f83fdc379845ca9ad110eb3b14b9aa
R165 closeout       7c522f0b4f4851ca620f75889c08e78cbe6d63752fb8140492fd66b022506f82
R166 result         2e0548ca9fb7ad69504648061c879fa1b69af54ed507f4d65e7e221ce5ffa9c9
R166 handoff        84cdff552cbd3d6409d4c06c958dc32320c2031a1147be0fc53f23757020f0fc
candidate_context   d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb
candidate_scheme    2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
shadow_apply        b9d5a1a1ddb013045723f258161d647a0dc1fe8cf39b772b89b6eadd2be15622
solver lib          c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985
candidate_source    cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
candidate_effect    c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1
candidate_extrusion 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332
candidate_intrusion 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
inference authority 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
sprint decision     2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e
sprint rule         e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a
handoff protocol    1379059577f4469ed930c0fc130e5cd169401cf9188dfcbbc482b92b43daebbf
```

Checks: static source/authority inspection, fixture syntax/base-contract membership reasoning,
constructor specialization and exact byte hashes. No tests, builds, probes, compiler/sample/runtime
execution, code edits, Git, network, user/external contact, descendants or background processes.
A whole-file static `lib.rs` read exceeded the tool output cap and was discarded; exact scoped
excerpts were used instead. Requested Sol/high; observed effective model/effort UNKNOWN/UNKNOWN.
Grant 1500 seconds fully charged, no carryover/reclaim or extension. Actual activation-to-stop
elapsed time is UNKNOWN; timestamp observations are reported in the handoff without substituting
them for activation metadata. Only this note and `tasks/agent-loop/inbox/20261021-r170-proof.md`
are written. Omitted: concrete native IDs/tuple/probe, direct-Name and forwarding instances,
arbitrary histories, raw/canonical converse, shared-anchor coverage and replay residual law.

Stop condition reached: exact unsupported source-to-same-provider association returned to Luna;
fresh independent review and any subsequent input/lease decision belong to Luna.
**Writes stop with the frozen handoff. No descendants, unresolved child leases or active worker
work are claimed after submission.**
