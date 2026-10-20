# R165 native forwarding admission: exact capture boundary

Date: 2026-10-20. Status: **UNREVIEWED SOURCE/NATIVE EVIDENCE; original mapped admission OPEN**.
Author: `/root/r165_native_admission_proof`; no coauthors or descendants.
Contract: `tasks/agent-loop/sprints/native-admission-20261020-r165-rev2.md`, revision 2,
SHA-256 `5ae2524975b209d8e15cc737740ab35f46729755364f47562ccaec3e75e2e955`.
Baseline supplied by Luna: `e2c1908575c45743b6311dbf195681d9f8f182dc`.
All contract, parent, R70/R71 result and five live source pins matched. No Git operation by this leaf.

## 1. Parent application and actual result

The parent is computation-forwarding preservation §§1, 6–7, with its shared satisfying assignment
`xi=(nu,K,D)`, original resolved formal/provider/witness identities, ordered dependencies, arbitrary
finite chains, repeated calls, simultaneous entries and original accepted source domain unchanged.
Its native implication needs the actual compared provider's authentic instance map `mu` and admission of

```text
mu(e_t) <= mu(e_n) <= mu(e_R), and mu(e_n) <= mu(e_t).
```

R165 establishes the inspected constructor fact in §2: an actually captured bound fiber has a
concrete supplier through that FreshUse's shared maps, exact FreshUse dependency and physical
restoration before the use exposes its root. This is source/native evidence for successful named
constructors, not an independently reviewed theorem. Applied to the original parent: a required
original witness identified with such an actual captured bound has this restoration supplier.
Endpoints, physical slots and completed-restoration counts alone cannot supply that identification.

The first unproved induction step is **occurrence-specific original-witness coverage at
`Capture::bound`**, followed by the exact compared-provider/consumer lineage join (§3). Structural
endpoints are canonicalized separately from the retained raw-key fiber lookup. R71's forward
transport proves neither the required converse nor an alternative lineage-preserving factorization
for this actual occurrence. This is neither a source-qualified counterexample nor proof of
universally absent fibers. Original mapped admission, Simple-sub/evaluator A/B, F1/FK1, foreign
continuations, soundness, principality, native/runtime correspondence and production remain OPEN.

## 2. Actual constructor-to-consumer facts

These facts concern successful executions on actual retained records. They neither assert arbitrary
native states are source-reachable nor establish global R70 ENTRY-WF or successful completion after
every suspension/error.

**Capture.** `candidate_scheme::Capture::intern:745–755` canonicalizes a signed endpoint before
interning its structural node. `row:757–790` selects a canonical row and its generic/local status;
`expand_node:903–1007` reconstructs Function children with Value/Effect/Effect/Value kinds and
opposite/opposite/same/same variance. `expand_row:1055–1161` stops at shared nonlocal anchors,
whose mutable bounds remain in the session; local rows enumerate both physical sides and the
specified Effect capture incidence.

`Capture::bound:1008–1053` computes the raw `source_bound` from the supplied owner, side and stored
item, then enumerates exactly `bound_cursor(source_bound)`. Each observed relation gets a Bound and
an evidence snapshot. Deduplication includes kind, side, canonical structural indices and optional
relation: different relations are not equated by endpoints. Empty lookup creates one `relation: None`
Bound; that placeholder does not establish an original executable witness. The capture closure
(`capture_candidate_graph_inner:1217–1360`) also follows relation contexts and deferred demand roots.
Its `relation_context` lookup delegates to `post_check_context`
(`candidate_context:1641–1644,3195–3200`), retaining the discharged relation's current residual or
IDENTITY when none remains. FreshUse does not blindly copy the immutable pre-discharge context.

**One authentic use.** `prepare_candidate_fresh_use:1557–1861` allocates one `context_use`, with a
single canonical row map and terms map. Rows sharing a current source representative share their
image within this use. Still-generic local rows get fresh identities at the actual use level;
other coordinates remain anchors. All four Function children use that same reconstruction.
This does not identify original/copy coordinates or sibling uses. The same preparation remaps
context views/tails, captured current contexts, attachment bundles and evidence snapshots. Scoped
mode remaps transformers, output scopes, inputs and captured negative demand roots, changing a
demand's use instance only under its actual local-input rule. These maps are not runtime receiver
identities.

For a captured Bound with `relation=Some(r)`, `begin_candidate_fresh_bound:1863–1910` derives both
endpoints from this FreshUse, preserves owner orientation and obtains the prepared image of the
current `relation_context(r)`. `candidate_context_fresh_transport_scoped:4079–4096` retains/attaches
the mapped child with the parent's source set, supplied scoped flow and exact dependency:

```text
Dependency::Transport { child, parent: r, use_origin: this_use,
  witness: Some(TransportWitness { from: source_bound,
                                  to: destination, reason: FreshUse }) }
```

Scoped destinations are canonicalized at that constructor. The restoration receives the same source
bound/use identity, imported evidence antecedent and mapped relation.
`candidate_context_reuse_fresh_relation:4060–4078` verifies the antecedent's parent/source and that
exact retained dependency when its reuse path is taken. This does not assert every mode takes that
path, or that an optional-None bound gains the desired original fiber from physical bootstrap.

**Restoration before root exposure.** `candidate_extrusion::candidate_begin_bound_restoration:765–785`
requires an idle typed worklist, inserts the mapped bound, snapshots opposite count and retains its
restoration handle. `candidate_insert_bound_with_evidence:501–674` canonicalizes the actual insertion
key, admits its evidence, appends the correct kind/lane, reads the addressed slot back, checks the
complete key and emits its physical receipt. Successful insertion proves storage of that actual
bound; storage alone does not prove its full executable lineage.

`candidate_step_bound_restoration_child:803–867` preserves saved count/index and the active replay.
It drives each retained nonempty ReplayOperation to completion before advancing, then retires after
the saved opposite positions. It re-reads the live canonical owner/item at the saved index. This does
not enumerate arbitrary future appends beyond the saved count or establish later propagation.

The module route `freshen_candidate_graph_core:1536–1556` restores every captured Bound in order
before returning the root; `instantiate_candidate_graph:1911–1966` invokes the root route afterward
and retains that graph/map combination. The Local route constructs graph/maps once
(`route_candidate_local_run:2038–2047`); `step_candidate_local_use:2168–2187` advances `next_bound`
only when current restoration reports completion, and exposes the root link after all captured
bounds. `commit_local_use:662–692` retains that exact use and maps. The module and Local mechanisms
are FreshUse restoration, distinct from production extrusion's one-sided copies and source links.

**Relation-local consumption.** `lib::step_typed_drain:12344–12449` installs the actual item's task and
relation, then runs Transport, Context and Dispatch before diagnostics/terminal acknowledgements.
The Function comparison (`dispatch_live_item:12653–12720`) constructs variance-correct child pairs;
`candidate_step_function_dispatch:12800–12829` admits/enqueues each through
`candidate_function_port_admit`. ArgumentEffect compares actual demand AE with this positive
Function's AE; ResultEffect compares its RE with demand RE. Endpoint matches without the original
provider/witness route do not establish the parent's required instance joins. A drain return or
acknowledgment proves its owner protocol, not missing original-witness coverage.

## 3. Exact first unproved constructor/consumer premise

Let `k=(o,p,q)` be a selected physical slot's retained raw key, `C(k)` its current canonical key and
`F(k)` its actual bound-cursor relation list. The inspected constructors give two routes:

```text
physical slot (o,p,q) -> Capture::bound exact F(k)
                      -> intern structural C(o),C(q)
                      -> one authentic FreshUse and exact parent r in F(k)
                      -> restoration / Replay / FunctionPort consumer

r in F(k) -> EqualityCanonicalization witness -> c in F(C(k))
```

The second route is `candidate_context_canonicalize_bounds:4031–4052`: each observed raw fiber
remains and gets a canonical child. `merge_candidate_rows:599–707` copies both sides/transfers fibers,
changes representatives, performs that sweep and replays retained-parent lowers. Third-owner raw
physical items remain. `recapture_candidate_extrusion:388–421` retains source reuse and qualifying
activation for the actual reused output group; it does not rewrite every raw physical slot or add
reverse fiber transport. `settle_candidate_intrusion:568–597` processes the actual occurrence's
parent/copy pairs selected by qualifying source Value SCC events, not type-endpoint SCCs.

These facts do not show that a particular canonical descendant `c`, or another required witness at
`C(k)`, is among the raw relations captured from `F(k)`. Nor may an ancestor `r` silently substitute:
their ordered Transport/Replay dependencies and residual/scoped contexts need a justified
occurrence-specific factorization through the actual consumer. This packet establishes neither that
every such canonical descendant is required by the parent nor that it is universally absent.
The obstruction is missing proof of the actual required lineage, not a proposed reverse-saturation
algorithm or a blanket claim that raw/canonical lookup is incorrect.

**R165-CAPTURE-CONSUMER-1.** For the actual compared positive provider instance, identify each original
Name/body witness and ordered forwarding join at its production source admission; prove its required
lineage is either (a) a concrete `Some(r)` Bound observed at this exact Capture raw lookup and restored
by this use, (b) retained at an unchanged shared anchor with its actual consumer route, or (c)
transported through a separately justified factorization preserving provider, witness, dependency
order and current residual/scoped state. Identify that route at the actual AE/RE consumer, through
all intervening extrusion, qualifying merge/recapture and replay. These are proof cases, not new
source restrictions or compiler rules.

Constructor owners: `candidate_scheme::{Capture::bound,Capture::expand_row,begin_candidate_fresh_bound}`.
Transport owners: `candidate_intrusion::{merge_candidate_rows,recapture_candidate_extrusion}` and
`candidate_context_canonicalize_bounds`. Consumers: `candidate_context_begin_replay` and
`lib::{step_typed_drain,candidate_step_function_dispatch}`. Luna owns assignment/adjudication.

This is the exact stop condition. A falsifier needs an accepted original source history, its
authentic compared provider/use, a specific original required witness with current residual/scoped
lineage, and evidence that the selected raw lookup and every admissible retained route fail to
deliver it to the actual consumer. An endpoint-only example, sibling use, missing count or hand-built
forest is insufficient. Conversely complete constructor induction establishing the exact preserving
route for every original-scope history discharges this premise; one fixture does not.

## 4. Reuse and separate replay residual obligation

R70 is used only as its reviewed successful-operation simulation under ENTRY-WF.
`candidate_extrusion::Work::Bound:325–342` copies the selected bound and transfers actual fibers from
the exact raw source with its Extrusion witness. R70 does not establish global ENTRY-WF or the
original-witness/Capture association. R71 supplies forward raw-to-canonical preservation and exact
raw-fiber transfer; it supplies no converse. Its production extrusion scope is preserved; Capture's
separate raw lookup was inspected directly. The parent's historical template lemma and conditional
instance-relative implication retain their actual hypotheses. Old source hashes are not asserted
as current source coverage. No R50 bypass, equality of buckets/endpoints or counts is used as proof.

Replay residual handling remains **separately OPEN**. Ordinary transports and FreshUse's
`relation_context` use `post_check_context`; this rules out a suspected unconditional stale-context
claim against FreshUse. `candidate_context_begin_replay:3810–3855`, however, constructs an ordered
Replay context from each selected parent's immutable `key.context`, retains ordered dependencies
and composes scoped flows. Original receiver filters may need checking on the new opposite product.
The correspondence law relating that rechecking and retained residual to the parent's current
constraint at this consumer is not proved here. This packet neither changes that operation nor
labels it a bug/counterexample or discharged residual law.

## 5. Next evidence and receipts

No equivalent conditional theorem is proposed as the successor. The minimum future provisional
source-evidence TODO is R165-CAPTURE-CONSUMER-1: select an authentic required provider witness; retain
its source admission, exact raw/canonical keys, Capture Bound, common FreshUse maps, intervening
transport dependencies and actual AE/RE consumer relation, with ordered lineage and residual/scoped
payload at every step. The falsifier is §3's missing required authentic consumer lineage. Luna must
grant that packet; this note authorizes no instrumentation, execution, code or semantics change.

Checks: exact byte hashes, source/authority reads, constructor-to-consumer inspection and claim audit.
No tests, builds, probes, benchmarks, compiler/sample/runtime execution, temporary Y2 activity, Git,
network, external/user contact or descendants. One unavailable `python` writer invocation failed
before writing any file; the supported patch writer created the exact leased artifact. No scratch or
generated paths were created. Only this file and the leased inbox are outputs.

Assignment cap 900 seconds, no carryover, no resource/model extension. Requested model/effort
metadata absent from the grant: UNKNOWN/UNKNOWN. Observed model/effort UNKNOWN/UNKNOWN; configured
role policy is not execution metadata. The primary retains the whole charged grant; no unused-time
reclaim is requested from unobserved timing.

```text
parent              d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79
R70 result          648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7
R71 result          620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e
candidate_scheme    2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
candidate_extrusion 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332
candidate_intrusion 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
candidate_context   93ff11f005c9e29e007d2a21479779dd14ff462a41da9c937a0e6a48fc1603be
solver lib          c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985
```

Frozen for fresh independent review; the author cannot certify it. No parent theorem or production
promotion is claimed. Writes stop with the exact handoff; no descendants, background process,
unconsumed child result or additional output lease exists.
